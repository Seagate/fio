/*
 * Copyright (C) 2018 Western Digital Corporation or its affiliates.
 *
 * This file is released under the GPL.
 */

#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <dirent.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <unistd.h>
#include <linux/blkzoned.h>
#include "file.h"
#include "fio.h"
#include "lib/pow2.h"
#include "log.h"
#include "smalloc.h"
#include "verify.h"
#include "zbd.h"

/**
 * zbd_zone_idx - convert an offset into a zone number
 * @f: file pointer.
 * @offset: offset in bytes. If this offset is in the first zone_size bytes
 *	    past the disk size then the index of the sentinel is returned.
 */
static uint32_t zbd_zone_idx(const struct fio_file *f, uint64_t offset)
{
	uint32_t zone_idx;

	if (f->zbd_info->zone_size_log2)
		zone_idx = offset >> f->zbd_info->zone_size_log2;
	else
		zone_idx = (offset >> 9) / f->zbd_info->zone_size;

	return min(zone_idx, f->zbd_info->nr_zones);
}

/**
 * zbd_zone_full - verify whether a minimum number of bytes remain in a zone
 * @f: file pointer.
 * @z: zone info pointer.
 * @required: minimum number of bytes that must remain in a zone.
 *
 * The caller must hold z->mutex.
 */
static bool zbd_zone_full(const struct fio_file *f, struct fio_zone_info *z,
			  uint64_t required)
{
	assert(z->type == BLK_ZONE_TYPE_SEQWRITE_REQ);
	assert((required & 511) == 0);

	return z->wp + (required >> 9) > z->start + f->zbd_info->zone_size;
}

static bool is_valid_offset(const struct fio_file *f, uint64_t offset)
{
	return (uint64_t)(offset - f->file_offset) < f->io_size;
}

/* Verify whether direct I/O is used for all ZBD drives. */
static bool zbd_using_direct_io(void)
{
	struct thread_data *td;
	struct fio_file *f;
	int i, j;

	for_each_td(td, i) {
		if (td->o.odirect || !(td->o.td_ddir & TD_DDIR_WRITE))
			continue;
		for_each_file(td, f, j) {
			if (f->zbd_info)
				return false;
		}
	}

	return true;
}

/* Whether or not the I/O range for f includes one or more sequential zones */
static bool zbd_is_seq_job(struct fio_file *f)
{
	uint32_t zone_idx, zone_idx_b, zone_idx_e;

	assert(f->zbd_info);
	zone_idx_b = zbd_zone_idx(f, f->file_offset);
	zone_idx_e = zbd_zone_idx(f, f->file_offset + f->io_size);
	for (zone_idx = zone_idx_b; zone_idx <= zone_idx_e; zone_idx++)
		if (f->zbd_info->zone_info[zone_idx].type ==
		    BLK_ZONE_TYPE_SEQWRITE_REQ)
			return true;

	return false;
}

static bool zbd_verify_sizes(void)
{
	const struct fio_zone_info *z;
	struct thread_data *td;
	struct fio_file *f;
	uint64_t new_offset, new_end;
	uint32_t zone_idx;
	int i, j;

	for_each_td(td, i) {
		for_each_file(td, f, j) {
			if (!f->zbd_info)
				continue;
			if (f->file_offset >= f->real_file_size)
				continue;
			if (!zbd_is_seq_job(f))
				continue;
			zone_idx = zbd_zone_idx(f, f->file_offset);
			z = &f->zbd_info->zone_info[zone_idx];
			if (f->file_offset != (z->start << 9)) {
				new_offset = (z+1)->start << 9;
				if (new_offset >= f->file_offset + f->io_size) {
					log_info("%s: io_size must be at least one zone\n",
						 f->file_name);
					return false;
				}
				log_info("%s: rounded up offset from %lu to %lu\n",
					 f->file_name, f->file_offset,
					 new_offset);
				f->io_size -= (new_offset - f->file_offset);
				f->file_offset = new_offset;
			}
			zone_idx = zbd_zone_idx(f, f->file_offset + f->io_size);
			z = &f->zbd_info->zone_info[zone_idx];
			new_end = z->start << 9;
			if (f->file_offset + f->io_size != new_end) {
				if (new_end <= f->file_offset) {
					log_info("%s: io_size must be at least one zone\n",
						 f->file_name);
					return false;
				}
				log_info("%s: rounded down io_size from %lu to %lu\n",
					 f->file_name, f->io_size,
					 new_end - f->file_offset);
				f->io_size = new_end - f->file_offset;
			}
		}
	}

	return true;
}

static bool zbd_verify_bs(void)
{
	struct thread_data *td;
	struct fio_file *f;
	uint32_t zone_size;
	int i, j, k;

	for_each_td(td, i) {
		for_each_file(td, f, j) {
			if (!f->zbd_info)
				continue;
			zone_size = f->zbd_info->zone_size;
			for (k = 0; k < ARRAY_SIZE(td->o.bs); k++) {
				if (td->o.verify != VERIFY_NONE &&
				    (zone_size << 9) % td->o.bs[k] != 0) {
					log_info("%s: block size %d is not a divisor of the zone size %d\n",
						 f->file_name, td->o.bs[k],
						 zone_size << 9);
					return false;
				}
			}
		}
	}
	return true;
}

/*
 * Read zone information into @buf starting from sector @start_sector.
 * @fd is a file descriptor that refers to a block device and @bufsz is the
 * size of @buf.
 *
 * Returns 0 upon success and a negative error code upon failure.
 */
static int read_zone_info(int fd, uint64_t start_sector,
			  void *buf, unsigned int bufsz)
{
	struct blk_zone_report *hdr = buf;

	if (bufsz < sizeof(*hdr))
		return -EINVAL;

	memset(hdr, 0, sizeof(*hdr));

	hdr->nr_zones = (bufsz - sizeof(*hdr)) / sizeof(struct blk_zone);
	hdr->sector = start_sector;
	return ioctl(fd, BLKREPORTZONE, hdr) >= 0 ? 0 : -errno;
}

/*
 * Read up to 255 characters from the first line of a file. Strip the trailing
 * newline.
 */
static char *read_file(const char *path)
{
	char line[256], *p = line;
	FILE *f;

	f = fopen(path, "rb");
	if (!f)
		return NULL;
	if (!fgets(line, sizeof(line), f))
		line[0] = '\0';
	strsep(&p, "\n");
	fclose(f);

	return strdup(line);
}

static enum blk_zoned_model get_zbd_model(const char *file_name)
{
	enum blk_zoned_model model = ZBD_DM_NONE;
	char *zoned_attr_path = NULL;
	char *model_str = NULL;
	struct stat statbuf;

	if (stat(file_name, &statbuf) < 0)
		goto out;
	if (asprintf(&zoned_attr_path, "/sys/dev/block/%d:%d/queue/zoned",
		     major(statbuf.st_rdev), minor(statbuf.st_rdev)) < 0)
		goto out;
	model_str = read_file(zoned_attr_path);
	if (!model_str)
		goto out;
	dprint(FD_ZBD, "%s: zbd model string: %s\n", file_name, model_str);
	if (strcmp(model_str, "host-aware") == 0)
		model = ZBD_DM_HOST_AWARE;
	else if (strcmp(model_str, "host-managed") == 0)
		model = ZBD_DM_HOST_MANAGED;

out:
	free(model_str);
	free(zoned_attr_path);
	return model;
}

static int ilog2(uint64_t i)
{
	int log = -1;

	while (i) {
		i >>= 1;
		log++;
	}
	return log;
}

/*
 * Allocate zone information and assign it to f->zbd_info.
 *
 * Returns 0 upon success and a negative error code upon failure.
 */
int zbd_create_zone_info(struct fio_file *f)
{
	const unsigned int bufsz = sizeof(struct blk_zone_report) +
		4096 * sizeof(struct blk_zone);
	uint32_t nr_zones;
	struct blk_zone_report *hdr;
	const struct blk_zone *z;
	struct fio_zone_info *p;
	uint64_t zone_size, start_sector;
	struct zoned_block_device_info *zbd_info = NULL;
	enum blk_zoned_model zbd_model;
	pthread_mutexattr_t attr;
	void *buf;
	int fd, i, j, ret = 0;

	pthread_mutexattr_init(&attr);
	pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
	pthread_mutexattr_setpshared(&attr, true);

	zbd_model = get_zbd_model(f->file_name);
	if (zbd_model != ZBD_DM_HOST_MANAGED)
		goto out;

	buf = malloc(bufsz);
	if (!buf)
		goto out;

	fd = open(f->file_name, O_RDONLY | O_LARGEFILE);
	if (fd < 0) {
		ret = -errno;
		goto free;
	}

	ret = read_zone_info(fd, 0, buf, bufsz);
	if (ret < 0) {
		log_info("fio: BLKREPORTZONE(%lu) failed for %s (%d).\n",
			 0UL, f->file_name, -ret);
		goto close;
	}
	hdr = buf;
	if (hdr->nr_zones < 1) {
		log_info("fio: %s has invalid zone information.\n",
			 f->file_name);
		goto close;
	}
	z = (void *)(hdr + 1);
	zone_size = z->len;
	nr_zones = ((f->real_file_size >> 9) + zone_size - 1) / zone_size;

	dprint(FD_ZBD, "Device %s has %d zones of size %lu KB\n", f->file_name,
	       nr_zones, zone_size / 2);

	zbd_info = scalloc(1, sizeof(*zbd_info) +
			   (nr_zones + 1) * sizeof(zbd_info->zone_info[0]));
	ret = -ENOMEM;
	if (!zbd_info)
		goto close;
	pthread_mutex_init(&zbd_info->mutex, &attr);
	zbd_info->refcount = 1;
	p = &zbd_info->zone_info[0];
	for (start_sector = 0, j = 0; j < nr_zones;) {
		z = (void *)(hdr + 1);
		for (i = 0; i < hdr->nr_zones; i++, j++, z++, p++) {
			pthread_mutex_init(&p->mutex, &attr);
			p->start = z->start;
			switch (z->cond) {
			case BLK_ZONE_COND_NOT_WP:
				p->wp = z->start;
				break;
			case BLK_ZONE_COND_FULL:
				p->wp = z->start + zone_size;
				break;
			default:
				assert(z->start <= z->wp);
				assert(z->wp <= z->start + zone_size);
				p->wp = z->wp;
				break;
			}
			p->type = z->type;
			if (j > 0 && p->start != p[-1].start + zone_size) {
				log_info("%s: invalid zone data\n",
					 f->file_name);
				ret = -EINVAL;
				goto close;
			}
		}
		z--;
		start_sector = z->start + z->len;
		if (j >= nr_zones)
			break;
		ret = read_zone_info(fd, start_sector, buf, bufsz);
		if (ret < 0) {
			log_info("fio: BLKREPORTZONE(%lu) failed for %s (%d).\n",
				 start_sector, f->file_name, -ret);
			goto close;
		}
	}
	/* a sentinel */
	zbd_info->zone_info[nr_zones].start = start_sector;

	f->zbd_info = zbd_info;
	f->zbd_info->zone_size = zone_size;
	f->zbd_info->zone_size_log2 = is_power_of_2(zone_size) ?
		ilog2(zone_size) + 9 : -1;
	f->zbd_info->nr_zones = nr_zones;
	zbd_info = NULL;
	ret = 0;

close:
	sfree(zbd_info);
	close(fd);
free:
	free(buf);
out:
	pthread_mutexattr_destroy(&attr);
	return ret;
}

void zbd_free_zone_info(struct fio_file *f)
{
	uint32_t refcount;

	if (!f->zbd_info)
		return;

	pthread_mutex_lock(&f->zbd_info->mutex);
	refcount = --f->zbd_info->refcount;
	pthread_mutex_unlock(&f->zbd_info->mutex);

	assert((int32_t)refcount >= 0);
	if (refcount == 0)
		sfree(f->zbd_info);
	f->zbd_info = NULL;
}

/*
 * Initialize f->zbd_info.
 *
 * Returns 0 upon success and a negative error code upon failure.
 *
 * Note: this function can only work correctly if it is called before the first
 * fio fork() call.
 */
static int zbd_init_zone_info(struct thread_data *td, struct fio_file *file)
{
	struct thread_data *td2;
	struct fio_file *f2;
	int i, j, ret;

	for_each_td(td2, i) {
		for_each_file(td2, f2, j) {
			if (td2 == td && f2 == file)
				continue;
			if (!f2->zbd_info ||
			    strcmp(f2->file_name, file->file_name) != 0)
				continue;
			file->zbd_info = f2->zbd_info;
			file->zbd_info->refcount++;
			return 0;
		}
	}

	ret = zbd_create_zone_info(file);
	if (ret < 0)
		td_verror(td, -ret, "BLKREPORTZONE failed");
	return ret;
}

int zbd_init(struct thread_data *td)
{
	struct fio_file *f;
	int i;

	for_each_file(td, f, i) {
		if (f->filetype == FIO_TYPE_BLOCK)
			zbd_init_zone_info(td, f);
	}

	if (!zbd_using_direct_io()) {
		log_err("Using direct I/O is mandatory for writing to ZBD drives\n\n");
		return 1;
	}

	if (!zbd_verify_sizes())
		return 1;

	if (!zbd_verify_bs())
		return 1;

	return 0;
}

/**
 * zbd_reset_range - reset zones for a range of sectors
 * @td: FIO thread data.
 * @f: Fio file for which to reset zones
 * @sector: Starting sector in units of 512 bytes
 * @nr_sectors: Number of sectors in units of 512 bytes
 *
 * Returns 0 upon success and a negative error code upon failure.
 */
static int zbd_reset_range(struct thread_data *td, const struct fio_file *f,
			   uint64_t sector, uint64_t nr_sectors)
{
	struct blk_zone_range zr = {
		.sector         = sector,
		.nr_sectors     = nr_sectors,
	};
	uint32_t zone_idx_b, zone_idx_e;
	struct fio_zone_info *zb, *ze, *z;
	int ret;

	assert(f->fd != -1);
	assert(is_valid_offset(f, ((sector + nr_sectors) << 9) - 1));
	ret = ioctl(f->fd, BLKRESETZONE, &zr);
	if (ret < 0) {
		td_verror(td, errno, "resetting wp failed");
		log_err("%s: resetting wp for %llu sectors at sector %llu failed (%d).\n",
			f->file_name, zr.nr_sectors, zr.sector, errno);
		return ret;
	}

	zone_idx_b = zbd_zone_idx(f, sector << 9);
	zb = &f->zbd_info->zone_info[zone_idx_b];
	zone_idx_e = zbd_zone_idx(f, (sector + nr_sectors) << 9);
	ze = &f->zbd_info->zone_info[zone_idx_e];
	for (z = zb; z < ze; z++) {
		pthread_mutex_lock(&z->mutex);
		z->wp = z->start;
		z->verify_block = 0;
		pthread_mutex_unlock(&z->mutex);
	}

	td->ts.nr_zone_resets += ze - zb;

	return ret;
}

/**
 * zbd_reset_zone - reset the write pointer of a single zone
 * @td: FIO thread data.
 * @f: FIO file associated with the disk for which to reset a write pointer.
 * @z: Zone to reset.
 *
 * Returns 0 upon success and a negative error code upon failure.
 */
static int zbd_reset_zone(struct thread_data *td, const struct fio_file *f,
			  struct fio_zone_info *z)
{
	int ret;

	dprint(FD_ZBD, "%s: resetting wp of zone %lu.\n", f->file_name,
	       z - f->zbd_info->zone_info);
	ret = zbd_reset_range(td, f, z->start, (z+1)->start - z->start);
	return ret;
}

/*
 * Reset a range of zones. Returns 0 upon success and 1 upon failure.
 * @td: fio thread data.
 * @f: fio file for which to reset zones
 * @zb: first zone to reset.
 * @ze: first zone not to reset.
 * @all_zones: whether to reset all zones or only those zones for which the
 *	write pointer is not a multiple of td->o.min_bs[DDIR_WRITE].
 */
static int zbd_reset_zones(struct thread_data *td, struct fio_file *f,
			   struct fio_zone_info *const zb,
			   struct fio_zone_info *const ze, bool all_zones)
{
	struct fio_zone_info *z, *start_z = ze;
	uint32_t min_bs = td->o.min_bs[DDIR_WRITE] >> 9;
	bool reset_wp;
	int res = 0;

	dprint(FD_ZBD, "%s: resetting zones\n", f->file_name);
	assert(f->fd != -1);
	for (z = zb; z < ze; z++) {
		pthread_mutex_lock(&z->mutex);
		switch (z->type) {
		case BLK_ZONE_TYPE_SEQWRITE_REQ:
			reset_wp = all_zones ? z->wp != z->start :
					(td->o.td_ddir & TD_DDIR_WRITE) &&
					z->wp % min_bs != 0;
			if (start_z == ze && reset_wp) {
				start_z = z;
			} else if (start_z < ze && !reset_wp) {
				dprint(FD_ZBD,
				       "%s: resetting zones %lu .. %lu\n",
				       f->file_name,
				       start_z - f->zbd_info->zone_info,
				       z - f->zbd_info->zone_info);
				if (zbd_reset_range(td, f, start_z->start,
						z->start - start_z->start) < 0)
					res = 1;
				start_z = ze;
			}
			break;
		default:
			if (start_z == ze)
				break;
			dprint(FD_ZBD, "%s: resetting zones %lu .. %lu\n",
			       f->file_name, start_z - f->zbd_info->zone_info,
			       z - f->zbd_info->zone_info);
			if (zbd_reset_range(td, f, start_z->start,
					    z->start - start_z->start) < 0)
				res = 1;
			start_z = ze;
			break;
		}
	}
	dprint(FD_ZBD, "%s: resetting zones %lu .. %lu\n", f->file_name,
	       start_z - f->zbd_info->zone_info, z - f->zbd_info->zone_info);
	if (start_z < ze && zbd_reset_range(td, f, start_z->start,
					    z->start - start_z->start) < 0)
		res = 1;
	for (z = zb; z < ze; z++)
		pthread_mutex_unlock(&z->mutex);

	return res;
}

void zbd_file_reset(struct thread_data *td, struct fio_file *f)
{
	struct fio_zone_info *zb, *ze;
	uint32_t zone_idx_e;

	if (!f->zbd_info)
		return;

	zb = &f->zbd_info->zone_info[zbd_zone_idx(f, f->file_offset)];
	zone_idx_e = zbd_zone_idx(f, f->file_offset + f->io_size);
	ze = &f->zbd_info->zone_info[zone_idx_e];
	/*
	 * If data verification is enabled reset the affected zones before
	 * writing any data to avoid that a zone reset has to be issued while
	 * writing data, which causes data loss.
	 */
	zbd_reset_zones(td, f, zb, ze, td->o.verify != VERIFY_NONE &&
			(td->o.td_ddir & TD_DDIR_WRITE) &&
			td->runstate != TD_VERIFYING);
}

/* The caller must hold f->zbd_info->mutex. */
static bool is_zone_open(const struct thread_data *td, const struct fio_file *f,
			 unsigned int zone_idx)
{
	struct zoned_block_device_info *zbdi = f->zbd_info;
	int i;

	assert(td->o.max_open_zones <= ARRAY_SIZE(zbdi->open_zones));
	assert(zbdi->num_open_zones <= td->o.max_open_zones);

	for (i = 0; i < zbdi->num_open_zones; i++)
		if (zbdi->open_zones[i] == zone_idx)
			return true;

	return false;
}

/*
 * Open a ZBD zone if it was not yet open. Returns true if either the zone was
 * already open or if opening a new zone is allowed. Returns false if the zone
 * was not yet open and opening a new zone would cause the zone limit to be
 * exceeded.
 */
static bool zbd_open_zone(struct thread_data *td, const struct fio_file *f,
			  uint32_t zone_idx)
{
	bool res = true;

	pthread_mutex_lock(&f->zbd_info->mutex);
	/* Zero means no limit */
	if (!td->o.max_open_zones)
		goto out;
	if (is_zone_open(td, f, zone_idx))
		goto out;
	res = false;
	if (f->zbd_info->num_open_zones >= td->o.max_open_zones)
		goto out;
	dprint(FD_ZBD, "%s: opening zone %d\n", f->file_name, zone_idx);
	f->zbd_info->open_zones[f->zbd_info->num_open_zones++] = zone_idx;
	f->zbd_info->zone_info[zone_idx].open = 1;
	res = true;

out:
	pthread_mutex_unlock(&f->zbd_info->mutex);
	return res;
}

/* The caller must hold f->zbd_info->mutex */
static void zbd_close_zone(struct thread_data *td, const struct fio_file *f,
			   unsigned int open_zone_idx)
{
	uint32_t zone_idx;

	assert(open_zone_idx < f->zbd_info->num_open_zones);
	zone_idx = f->zbd_info->open_zones[open_zone_idx];
	memmove(f->zbd_info->open_zones + open_zone_idx,
		f->zbd_info->open_zones + open_zone_idx + 1,
		(FIO_MAX_OPEN_ZBD_ZONES - (open_zone_idx + 1)) *
		sizeof(f->zbd_info->open_zones[0]));
	f->zbd_info->num_open_zones--;
	f->zbd_info->zone_info[zone_idx].open = 0;
}

/*
 * Modify the offset of an I/O unit that does not refer to an open zone such
 * that it refers to an open zone. Close an open zone and open a new zone if
 * necessary. This algorithm can only work correctly if all write pointers are
 * a multiple of the fio block size. The caller must neither hold z->mutex
 * nor f->zbd_info->mutex. Returns with z->mutex held upon success.
 */
struct fio_zone_info *zbd_convert_to_open_zone(struct thread_data *td,
					       struct io_u *io_u)
{
	const struct fio_file *f = io_u->file;
	struct fio_zone_info *z;
	unsigned int open_zone_idx;
	uint32_t zone_idx, new_zone_idx;
	int i;

	assert(is_valid_offset(f, io_u->offset));

	/*
	 * This statement accesses f->zbd_info->open_zones[] on purpose
	 * without locking.
	 */
	zone_idx = f->zbd_info->open_zones[(io_u->offset - f->file_offset) *
			f->zbd_info->num_open_zones / f->io_size];

	/*
	 * Since z->mutex is the outer lock and f->zbd_info->mutex the inner
	 * lock it can happen that the state of the zone with index zone_idx
	 * has changed after 'z' has been assigned and before f->zbd_info->mutex
	 * has been obtained. Hence the loop.
	 */
	for (;;) {
		z = &f->zbd_info->zone_info[zone_idx];

		pthread_mutex_lock(&z->mutex);
		pthread_mutex_lock(&f->zbd_info->mutex);
		if (f->zbd_info->num_open_zones == 0) {
			pthread_mutex_unlock(&f->zbd_info->mutex);
			pthread_mutex_unlock(&z->mutex);
			return NULL;
		}
		open_zone_idx = (io_u->offset - f->file_offset) *
			f->zbd_info->num_open_zones / f->io_size;
		assert(open_zone_idx < f->zbd_info->num_open_zones);
		new_zone_idx = f->zbd_info->open_zones[open_zone_idx];
		if (new_zone_idx == zone_idx)
			break;
		zone_idx = new_zone_idx;
		pthread_mutex_unlock(&f->zbd_info->mutex);
		pthread_mutex_unlock(&z->mutex);
	}

	/* Both z->mutex and f->zbd_info->mutex are held. */

	if ((z->wp << 9) + io_u->buflen <= ((z+1)->start << 9)) {
		pthread_mutex_unlock(&f->zbd_info->mutex);
		goto out;
	}
	dprint(FD_ZBD, "%s: closing zone %d\n", f->file_name, zone_idx);
	zbd_close_zone(td, f, open_zone_idx);
	pthread_mutex_unlock(&f->zbd_info->mutex);

	/* Only z->mutex is held. */

	/* Zone 'z' is full, so try to open a new zone. */
	for (i = f->io_size / f->zbd_info->zone_size; i > 0; i--) {
		zone_idx++;
		pthread_mutex_unlock(&z->mutex);
		z++;
		if (!is_valid_offset(f, z->start << 9)) {
			/* Wrap-around. */
			zone_idx = zbd_zone_idx(f, f->file_offset);
			z = &f->zbd_info->zone_info[zone_idx];
		}
		assert(is_valid_offset(f, z->start << 9));
		pthread_mutex_lock(&z->mutex);
		/*
		 * Skip full zones with data verification enabled because
		 * resetting a zone causes data loss and hence causes
		 * verification to fail.
		 */
		if (z->open || (td->o.verify != VERIFY_NONE &&
				zbd_zone_full(f, z, io_u->buflen)))
			continue;
		if (zbd_open_zone(td, f, zone_idx))
			goto out;
	}

	/* Only z->mutex is held. */

	/* Check whether the write fits in any of the already opened zones. */
	pthread_mutex_lock(&f->zbd_info->mutex);
	for (i = 0; i < f->zbd_info->num_open_zones; i++) {
		zone_idx = f->zbd_info->open_zones[i];
		pthread_mutex_unlock(&f->zbd_info->mutex);
		pthread_mutex_unlock(&z->mutex);

		z = &f->zbd_info->zone_info[zone_idx];

		pthread_mutex_lock(&z->mutex);
		if ((z->wp << 9) + io_u->buflen <= ((z+1)->start << 9))
			goto out;
		pthread_mutex_lock(&f->zbd_info->mutex);
	}
	pthread_mutex_unlock(&f->zbd_info->mutex);
	pthread_mutex_unlock(&z->mutex);
	return NULL;

out:
	io_u->offset = z->start << 9;
	return z;
}

/* The caller must hold z->mutex. */
static struct fio_zone_info *zbd_replay_write_order(struct thread_data *td,
						    struct io_u *io_u,
						    struct fio_zone_info *z)
{
	const struct fio_file *f = io_u->file;
	uint32_t ba = td->o.ba[io_u->ddir];

	if (!zbd_open_zone(td, f, z - f->zbd_info->zone_info)) {
		pthread_mutex_unlock(&z->mutex);
		z = zbd_convert_to_open_zone(td, io_u);
		assert(z);
	}

	if (z->verify_block * ba >= f->zbd_info->zone_size)
		log_err("%s: %d * %d >= %ld\n", f->file_name, z->verify_block,
			ba, f->zbd_info->zone_size);
	io_u->offset = (z->start << 9) + z->verify_block++ * ba;
	return z;
}

/*
 * Find another zone for which @io_u fits below the write pointer. Start
 * searching in zones @zb + 1 .. @zl and continue searching in zones
 * @zf .. @zb - 1.
 *
 * Either returns NULL or returns a zone pointer and holds the mutex for that
 * zone.
 */
static struct fio_zone_info *
zbd_find_zone(struct thread_data *td, struct io_u *io_u,
	      struct fio_zone_info *zb, struct fio_zone_info *zl)
{
	const struct fio_file *f = io_u->file;
	struct fio_zone_info *z1, *z2;
	const struct fio_zone_info *const zf =
		&f->zbd_info->zone_info[zbd_zone_idx(f, f->file_offset)];

	/*
	 * Skip to the next non-empty zone in case of sequential I/O and to
	 * the nearest non-empty zone in case of random I/O.
	 */
	for (z1 = zb + 1, z2 = zb - 1; z1 < zl || z2 >= zf; z1++, z2--) {
		if (z1 < zl) {
			pthread_mutex_lock(&z1->mutex);
			if (z1->start + (io_u->buflen >> 9) <= z1->wp)
				return z1;
			pthread_mutex_unlock(&z1->mutex);
		} else if (!td_random(td)) {
			break;
		}
		if (td_random(td) && z2 >= zf) {
			pthread_mutex_lock(&z2->mutex);
			if (z2->start + (io_u->buflen >> 9) <= z2->wp)
				return z2;
			pthread_mutex_unlock(&z2->mutex);
		}
	}
	dprint(FD_ZBD, "%s: adjusting random read offset failed\n",
	       f->file_name);
	return NULL;
}


/**
 * zbd_post_submit - update the write pointer and unlock the zone lock
 * @io_u: I/O unit
 * @success: Whether or not the I/O unit has been executed successfully
 *
 * For write and trim operations, update the write pointer of all affected
 * zones.
 */
static void zbd_post_submit(const struct io_u *io_u, bool success)
{
	struct zoned_block_device_info *zbd_info;
	struct fio_zone_info *z;
	uint32_t zone_idx;
	uint64_t end, zone_end;

	zbd_info = io_u->file->zbd_info;
	if (!zbd_info)
		return;

	zone_idx = zbd_zone_idx(io_u->file, io_u->offset);
	end = (io_u->offset + io_u->buflen) >> 9;
	z = &zbd_info->zone_info[zone_idx];
	assert(zone_idx < zbd_info->nr_zones);
	if (z->type != BLK_ZONE_TYPE_SEQWRITE_REQ)
		return;
	if (!success)
		goto unlock;
	switch (io_u->ddir) {
	case DDIR_WRITE:
		zone_end = min(end, (z + 1)->start);
		z->wp = zone_end;
		break;
	case DDIR_TRIM:
		assert(z->wp == z->start);
		break;
	default:
		break;
	}
unlock:
	pthread_mutex_unlock(&z->mutex);
}

/**
 * zbd_adjust_block - adjust the offset and length as necessary for ZBD drives
 * @td: FIO thread data.
 * @io_u: FIO I/O unit.
 *
 * Locking strategy: returns with z->mutex locked if and only if z refers
 * to a sequential zone and if io_u_accept is returned. z is the zone that
 * corresponds to io_u->offset at the end of this function.
 */
enum io_u_action zbd_adjust_block(struct thread_data *td, struct io_u *io_u)
{
	const struct fio_file *f = io_u->file;
	uint32_t zone_idx_b;
	struct fio_zone_info *zb, *zl;
	uint32_t orig_len = io_u->buflen;
	uint32_t min_bs = td->o.min_bs[io_u->ddir];
	uint64_t new_len;
	int64_t range;

	if (!f->zbd_info)
		return io_u_accept;

	assert(is_valid_offset(f, io_u->offset));
	assert(io_u->buflen);
	zone_idx_b = zbd_zone_idx(f, io_u->offset);
	zb = &f->zbd_info->zone_info[zone_idx_b];

	if (zb->type != BLK_ZONE_TYPE_SEQWRITE_REQ)
		return io_u_accept;

	if (io_u->ddir == DDIR_READ && td->o.read_beyond_wp)
		return io_u_accept;

	pthread_mutex_lock(&zb->mutex);
	switch (io_u->ddir) {
	case DDIR_READ:
		if (td->runstate == TD_VERIFYING) {
			zb = zbd_replay_write_order(td, io_u, zb);
			goto accept;
		}
		/*
		 * Avoid reads past the write pointer because such reads do not
		 * hit the medium.
		 */
		range = ((zb->wp - zb->start) << 9) - io_u->buflen;
		if (td_random(td) && range >= 0) {
			io_u->offset = (zb->start << 9) +
				((io_u->offset - (zb->start << 9)) %
				 (range + 1)) / min_bs * min_bs;
			assert(zb->start << 9 <= io_u->offset);
			assert(io_u->offset + io_u->buflen <= zb->wp << 9);
			goto accept;
		}
		if ((io_u->offset + io_u->buflen) >> 9 > zb->wp) {
			pthread_mutex_unlock(&zb->mutex);
			zl = &f->zbd_info->zone_info[zbd_zone_idx(f,
						f->file_offset + f->io_size)];
			zb = zbd_find_zone(td, io_u, zb, zl);
			if (!zb) {
				dprint(FD_ZBD,
				       "%s: zbd_find_zone(%lld, %ld) failed\n",
				       f->file_name, io_u->offset,
				       io_u->buflen);
				goto eof;
			}
			io_u->offset = zb->start << 9;
		}
		if ((io_u->offset + io_u->buflen) >> 9 > zb->wp) {
			dprint(FD_ZBD, "%s: %lld + %ld > %ld\n",
			       f->file_name, io_u->offset, io_u->buflen,
			       zb->wp);
			goto eof;
		}
		goto accept;
	case DDIR_WRITE:
		if (io_u->buflen > (f->zbd_info->zone_size << 9))
			goto eof;
		if (!zbd_open_zone(td, f, zone_idx_b)) {
			pthread_mutex_unlock(&zb->mutex);
			zb = zbd_convert_to_open_zone(td, io_u);
			if (!zb)
				goto eof;
			zone_idx_b = zb - f->zbd_info->zone_info;
		}
		/* Reset the zone pointer if necessary */
		if (zb->reset_zone || zbd_zone_full(f, zb, io_u->buflen)) {
			assert(td->o.verify == VERIFY_NONE);
			/*
			 * Since previous write requests may have been submitted
			 * asynchronously and since we will submit the zone
			 * reset synchronously, wait until previously submitted
			 * write requests have completed before issuing a
			 * zone reset.
			 */
			io_u_quiesce(td);
			zb->reset_zone = 0;
			if (zbd_reset_zone(td, f, zb) < 0)
				goto eof;
		}
		/* Make writes occur at the write pointer */
		assert(!zbd_zone_full(f, zb, io_u->buflen));
		io_u->offset = zb->wp << 9;
		if (!is_valid_offset(f, io_u->offset)) {
			dprint(FD_IO, "Dropped request with offset %llu\n",
			       io_u->offset);
			goto eof;
		}
		/*
		 * Make sure that the buflen is a multiple of the minimal
		 * block size. Give up if shrinking would make the request too
		 * small.
		 */
		new_len = min((unsigned long long)io_u->buflen,
			      ((zb + 1)->start << 9) - io_u->offset);
		new_len = new_len / min_bs * min_bs;
		if (new_len == io_u->buflen)
			goto accept;
		if (new_len >= min_bs) {
			io_u->buflen = new_len;
			dprint(FD_IO, "Changed length from %u into %lu\n",
			       orig_len, io_u->buflen);
			goto accept;
		}
		log_err("Zone remainder %lld smaller than minimum block size %d\n",
			(((zb + 1)->start << 9) - io_u->offset),
			min_bs);
		goto eof;
	case DDIR_TRIM:
		/* fall-through */
	case DDIR_SYNC:
	case DDIR_DATASYNC:
	case DDIR_SYNC_FILE_RANGE:
	case DDIR_WAIT:
	case DDIR_LAST:
	case DDIR_INVAL:
		goto accept;
	}

	assert(false);

accept:
	assert(!io_u->post_submit);
	io_u->post_submit = zbd_post_submit;
	return io_u_accept;

eof:
	if (zb)
		pthread_mutex_unlock(&zb->mutex);
	return io_u_eof;
}

/*
 * Reset all zones that fit in their entirety in the I/O unit.
 *
 * Returns 0 if io_u->file refers to a ZBD disk and 1 otherwise.
 */
int zbd_do_trim(struct thread_data *td, const struct io_u *io_u)
{
	const struct fio_file *f = io_u->file;
	uint32_t zone_idx_b, zone_idx_e;
	uint32_t zone_size;
	struct fio_zone_info *zb, *ze;

	if (!f->zbd_info)
		return 1;

	zone_size = f->zbd_info->zone_size;
	zone_idx_b = zbd_zone_idx(f, io_u->offset + zone_size - 1);
	zb = &f->zbd_info->zone_info[zone_idx_b];
	zone_idx_e = zbd_zone_idx(f, io_u->offset + io_u->buflen);
	ze = &f->zbd_info->zone_info[zone_idx_e];

	if (zb->start < ze->start)
		zbd_reset_range(td, f, zb->start, ze->start - zb->start);

	return 0;
}

/* Return a string with ZBD statistics */
char *zbd_write_status(const struct thread_stat *ts)
{
	char *res;

	if (asprintf(&res, "; %ld zone resets", ts->nr_zone_resets) < 0)
		return NULL;
	return res;
}
