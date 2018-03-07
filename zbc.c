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
#include "zbc.h"

/**
 * zbc_zone_idx - convert an offset into a zone number
 * @f: file pointer.
 * @offset: offset in bytes. If this offset is in the first zone_size bytes
 *	    past the disk size then the index of the sentinel is returned.
 */
static uint32_t zbc_zone_idx(const struct fio_file *f, uint64_t offset)
{
	uint32_t zone_idx;

	if (f->zbd_info->zone_size_log2)
		zone_idx = offset >> f->zbd_info->zone_size_log2;
	else
		zone_idx = (offset >> 9) / f->zbd_info->zone_size;

	return min(zone_idx, f->zbd_info->nr_zones);
}

/* The caller must hold z->mutex. */
static bool zbc_zone_full(const struct fio_file *f, struct fio_zone_info *z)
{
	assert(z->type == BLK_ZONE_TYPE_SEQWRITE_REQ);

	return z->wp >= z->start + f->zbd_info->zone_size;
}

static bool is_valid_offset(const struct fio_file *f, uint64_t offset)
{
	return (uint64_t)(offset - f->file_offset) < f->io_size;
}

/* Verify whether direct I/O is used for all ZBC drives. */
static bool zbc_using_direct_io(void)
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

static bool zbc_verify_sizes(void)
{
	const struct fio_zone_info *z;
	struct thread_data *td;
	struct fio_file *f;
	uint64_t new_offset, new_start;
	uint32_t zone_idx;
	int i, j;

	for_each_td(td, i) {
		for_each_file(td, f, j) {
			if (!f->zbd_info)
				continue;
			if (f->file_offset >= f->real_file_size)
				continue;
			zone_idx = zbc_zone_idx(f, f->file_offset);
			z = &f->zbd_info->zone_info[zone_idx];
			if (z->type == BLK_ZONE_TYPE_SEQWRITE_REQ &&
			    f->file_offset != (z->start << 9)) {
				new_offset = (z+1)->start << 9;
				log_info("%s: rounded up offset from %lu to %lu\n",
					 f->file_name, f->file_offset,
					 new_offset);
				f->io_size -= (new_offset - f->file_offset);
				f->file_offset = new_offset;
			}
			zone_idx = zbc_zone_idx(f, f->file_offset + f->io_size);
			z = &f->zbd_info->zone_info[zone_idx];
			new_start = z->start << 9;
			if (z->type == BLK_ZONE_TYPE_SEQWRITE_REQ &&
			    f->file_offset + f->io_size != new_start) {
				if (new_start == f->file_offset) {
					log_info("%s: io_size must be at least one zone\n",
						 f->file_name);
					return false;
				}
				log_info("%s: rounded down io_size from %lu to %lu\n",
					 f->file_name, f->io_size, new_start);
				f->io_size = new_start;
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
	return ioctl(fd, BLKREPORTZONE, hdr);
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
	enum blk_zoned_model model = ZBC_DM_NONE;
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
	dprint(FD_ZBC, "%s: zbd model string: %s\n", file_name, model_str);
	if (strcmp(model_str, "host-aware") == 0)
		model = ZBC_DM_HOST_AWARE;
	else if (strcmp(model_str, "host-managed") == 0)
		model = ZBC_DM_HOST_MANAGED;

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
int zbc_create_zone_info(struct fio_file *f)
{
	const unsigned int bufsz = sizeof(struct blk_zone_report) +
		32768 * sizeof(struct blk_zone);
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
	if (zbd_model != ZBC_DM_HOST_MANAGED)
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
			 0UL, f->file_name, errno);
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

	dprint(FD_ZBC, "Device %s has %d zones of size %lu KB\n", f->file_name,
	       nr_zones, zone_size / 2);

	zbd_info = scalloc(1, sizeof(*zbd_info) +
			   (nr_zones + 1) * sizeof(zbd_info->zone_info[0]));
	ret = -ENOMEM;
	if (!zbd_info)
		goto close;
	zbd_info->refcount = 1;
	p = &zbd_info->zone_info[0];
	for (start_sector = 0, j = 0; j < nr_zones;) {
		z = (void *)(hdr + 1);
		for (i = 0; i < hdr->nr_zones; i++, j++, z++, p++) {
			pthread_mutex_init(&p->mutex, &attr);
			p->start = z->start;
			p->wp = z->wp;
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
				 start_sector, f->file_name, errno);
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

void zbc_free_zone_info(struct fio_file *f)
{
	if (!f->zbd_info)
		return;
	if (--f->zbd_info->refcount == 0)
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
static int zbc_init_zone_info(struct thread_data *td, struct fio_file *file)
{
	struct thread_data *td2;
	struct fio_file *f2;
	int i, j;

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

	return zbc_create_zone_info(file);
}

int zbc_init(struct thread_data *td)
{
	struct fio_file *f;
	int i;

	for_each_file(td, f, i) {
		if (f->filetype == FIO_TYPE_BLOCK)
			zbc_init_zone_info(td, f);
	}

	if (!zbc_using_direct_io()) {
		log_err("Using direct I/O is mandatory for writing to ZBC drives\n\n");
		return 1;
	}

	if (!zbc_verify_sizes())
		return 1;

	return 0;
}

/**
 * zbc_reset_range - reset zones for a range of sectors
 * @td: FIO thread data.
 * @f: Fio file for which to reset zones
 * @sector: Starting sector in units of 512 bytes
 * @nr_sectors: Number of sectors in units of 512 bytes
 *
 * Returns 0 upon success and a negative error code upon failure.
 */
static int zbc_reset_range(struct thread_data *td, const struct fio_file *f,
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

	zone_idx_b = zbc_zone_idx(f, sector << 9);
	zb = &f->zbd_info->zone_info[zone_idx_b];
	zone_idx_e = zbc_zone_idx(f, (sector + nr_sectors) << 9);
	ze = &f->zbd_info->zone_info[zone_idx_e];
	for (z = zb; z < ze; z++) {
		pthread_mutex_lock(&z->mutex);
		z->wp = z->start;
		z->verify_block = 0;
		pthread_mutex_unlock(&z->mutex);
	}

	return ret;
}

/**
 * zbc_reset_zone - reset the write pointer of a single zone
 * @td: FIO thread data.
 * @f: FIO file associated with the disk for which to reset a write pointer.
 * @z: Zone to reset.
 *
 * Returns 0 upon success and a negative error code upon failure.
 */
static int zbc_reset_zone(struct thread_data *td, const struct fio_file *f,
			  struct fio_zone_info *z)
{
	int ret;

	dprint(FD_ZBC, "%s: resetting wp of zone %lu.\n", f->file_name,
	       z - f->zbd_info->zone_info);
	ret = zbc_reset_range(td, f, z->start, (z+1)->start - z->start);
	return ret;
}

/* Reset a range of zones. Returns 0 upon success and 1 upon failure. */
static int zbc_reset_zones(struct thread_data *td, struct fio_file *f,
			   struct fio_zone_info *zb, struct fio_zone_info *ze)
{
	struct fio_zone_info *z, *start_z = ze;
	int res = 0;

	dprint(FD_ZBC, "%s: resetting zones\n", f->file_name);
	assert(f->fd != -1);
	for (z = zb; z < ze; z++) {
		pthread_mutex_lock(&z->mutex);
		switch (z->type) {
		case BLK_ZONE_TYPE_SEQWRITE_REQ:
			if (start_z == ze && z->wp != z->start) {
				start_z = z;
			} else if (start_z < ze && z->wp == z->start) {
				if (zbc_reset_range(td, f, start_z->start,
						z->start - start_z->start) < 0)
					res = 1;
				start_z = ze;
			}
			break;
		default:
			if (start_z == ze)
				break;
			if (zbc_reset_range(td, f, start_z->start,
					    z->start - start_z->start) < 0)
				res = 1;
			start_z = ze;
			break;
		}
	}
	if (start_z < ze && zbc_reset_range(td, f, start_z->start,
					    z->start - start_z->start) < 0)
		res = 1;
	for (z = zb; z < ze; z++)
		pthread_mutex_unlock(&z->mutex);

	return res;
}

void zbc_file_reset(struct thread_data *td, struct fio_file *f)
{
	struct fio_zone_info *zb, *ze;
	uint32_t zone_idx_e;

	if (!f->zbd_info)
		return;

	zb = &f->zbd_info->zone_info[zbc_zone_idx(f, f->file_offset)];
	zone_idx_e = zbc_zone_idx(f, f->file_offset + f->io_size);
	ze = &f->zbd_info->zone_info[zone_idx_e];
	/*
	 * If data verification is enabled reset the affected zones before
	 * writing any data to avoid that a zone reset has to be issued while
	 * writing data, which causes data loss.
	 */
	if (td->o.verify != VERIFY_NONE && (td->o.td_ddir & TD_DDIR_WRITE) &&
	    td->runstate != TD_VERIFYING)
		zbc_reset_zones(td, f, zb, ze);
}

/* The caller must hold z->mutex. */
static void zbc_replay_write_order(struct thread_data *td, struct io_u *io_u,
				   struct fio_zone_info *z)
{
	const struct fio_file *f = io_u->file;
	uint32_t ba = td->o.ba[io_u->ddir];

	if (z->verify_block * ba >= f->zbd_info->zone_size)
		log_err("%s: %d * %d >= %ld\n", f->file_name, z->verify_block,
			ba, f->zbd_info->zone_size);
	io_u->offset = (z->start << 9) + z->verify_block++ * ba;
}

static int zbc_drain_queue(struct thread_data *td)
{
#if 0
	dprint(FD_ZBC, "number of pending I/O requests: %d\n",
	       td->io_u_in_flight);
	io_u_quiesce(td);
#endif
	return 0;
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
zbc_find_zone(struct thread_data *td, struct io_u *io_u,
	      struct fio_zone_info *zb, struct fio_zone_info *zl)
{
	const struct fio_file *f = io_u->file;
	struct fio_zone_info *z1, *z2;
	const struct fio_zone_info *const zf =
		&f->zbd_info->zone_info[zbc_zone_idx(f, f->file_offset)];

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
	dprint(FD_ZBC, "%s: adjusting random read offset failed\n",
	       f->file_name);
	return NULL;
}


/**
 * zbc_post_submit - update the write pointer and unlock the zone lock
 * @io_u: I/O unit
 * @submit_result: a FIO_Q_* status code
 *
 * For write and trim operations, update the write pointer of all affected
 * zones.
 */
static void zbc_post_submit(const struct io_u *io_u,
			    enum fio_q_status submit_result)
{
	struct zoned_block_device_info *zbd_info;
	struct fio_zone_info *z;
	uint32_t zone_idx;
	uint64_t end, zone_end;

	zbd_info = io_u->file->zbd_info;
	if (!zbd_info)
		return;

	zone_idx = zbc_zone_idx(io_u->file, io_u->offset);
	end = (io_u->offset + io_u->buflen) >> 9;
	for (z = &zbd_info->zone_info[zone_idx]; z->start < end;
	     z++, zone_idx++) {
		assert(zone_idx < zbd_info->nr_zones);
		if (z->type != BLK_ZONE_TYPE_SEQWRITE_REQ)
			continue;
		if (submit_result < FIO_Q_BUSY) {
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
		}
		pthread_mutex_unlock(&z->mutex);
	}
}

/**
 * zbc_adjust_block - adjust the offset and length as necessary for ZBC drives
 * @td: FIO thread data.
 * @io_u: FIO I/O unit.
 *
 * Locking strategy: returns with z->mutex locked if and only if z refers
 * to a sequential zone and if io_u_accept is returned. z is the zone that
 * corresponds to io_u->offset at the end of this function.
 */
enum io_u_action zbc_adjust_block(struct thread_data *td, struct io_u *io_u)
{
	const struct fio_file *f = io_u->file;
	uint32_t zone_idx_b, zone_idx_e;
	struct fio_zone_info *zb, *zl;
	uint32_t orig_len = io_u->buflen, new_len;
	uint32_t min_bs = td->o.min_bs[io_u->ddir];
	int64_t range;

	if (!f->zbd_info)
		return io_u_accept;

	assert(is_valid_offset(f, io_u->offset));
	assert(io_u->buflen);
	zone_idx_b = zbc_zone_idx(f, io_u->offset);
	zb = &f->zbd_info->zone_info[zone_idx_b];

	if (zb->type != BLK_ZONE_TYPE_SEQWRITE_REQ)
		return io_u_accept;

	if (io_u->ddir == DDIR_READ && td->o.read_beyond_wp)
		return io_u_accept;

	pthread_mutex_lock(&zb->mutex);
	switch (io_u->ddir) {
	case DDIR_READ:
		if (td->runstate == TD_VERIFYING) {
			zbc_replay_write_order(td, io_u, zb);
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
			zl = &f->zbd_info->zone_info[zbc_zone_idx(f,
						f->file_offset + f->io_size)];
			zb = zbc_find_zone(td, io_u, zb, zl);
			if (!zb) {
				dprint(FD_ZBC,
				       "%s: zbc_find_zone(%lld, %ld) failed\n",
				       f->file_name, io_u->offset,
				       io_u->buflen);
				goto eof;
			}
			io_u->offset = zb->start << 9;
		}
		if ((io_u->offset + io_u->buflen) >> 9 > zb->wp) {
			dprint(FD_ZBC, "%s: %lld + %ld > %ld\n",
			       f->file_name, io_u->offset, io_u->buflen,
			       zb->wp);
			goto eof;
		}
		goto accept;
	case DDIR_WRITE:
		zone_idx_e = zbc_zone_idx(f, (zb->wp << 9) + io_u->buflen - 1);
		/* Reset the zone pointer if necessary */
		if (zb->reset_zone || zbc_zone_full(f, zb)) {
			zb->reset_zone = 0;
			assert(td->o.verify == VERIFY_NONE);
			if (zbc_drain_queue(td) < 0)
				goto eof;
			if (zbc_reset_zone(td, f, zb) < 0)
				goto eof;
			zone_idx_e = zbc_zone_idx(f, (zb->wp << 9) +
						  io_u->buflen - 1);
			assert(zone_idx_b <= zone_idx_e);
		}
		/* Make writes occur at the write pointer */
		assert(!zbc_zone_full(f, zb));
		io_u->offset = zb->wp << 9;
		if (!is_valid_offset(f, io_u->offset)) {
			dprint(FD_IO, "Dropped request with offset %llu\n",
			       io_u->offset);
			goto eof;
		}
		/*
		 * Shrink write requests that exceed the zone size and make
		 * sure that the new size is a multiple of the minimal block
		 * size. Give up if the minimal block size exceeds the zone
		 * size.
		 */
		if (zone_idx_b != zone_idx_e) {
			new_len = (((zb + 1)->start << 9) - io_u->offset) /
				min_bs * min_bs;
			if (new_len >= min_bs) {
				io_u->buflen = new_len;
				dprint(FD_IO,
				       "Changed length from %u into %lu\n",
				       orig_len, io_u->buflen);
				goto accept;
			}
			log_err("Zone remainder %lld smaller than minimum block size %d\n",
				(((zb + 1)->start << 9) - io_u->offset),
				min_bs);
			goto eof;
		}
		goto accept;
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
	io_u->post_submit = zbc_post_submit;
	return io_u_accept;

eof:
	if (zb)
		pthread_mutex_unlock(&zb->mutex);
	return io_u_eof;
}

/*
 * Reset all zones that fit in their entirety in the I/O unit.
 *
 * Returns 0 if io_u->file refers to a ZBC disk and 1 otherwise.
 */
int zbc_do_trim(struct thread_data *td, const struct io_u *io_u)
{
	const struct fio_file *f = io_u->file;
	uint32_t zone_idx_b, zone_idx_e;
	uint32_t zone_size;
	struct fio_zone_info *zb, *ze;

	if (!f->zbd_info)
		return 1;

	zone_size = f->zbd_info->zone_size;
	zone_idx_b = zbc_zone_idx(f, io_u->offset + zone_size - 1);
	zb = &f->zbd_info->zone_info[zone_idx_b];
	zone_idx_e = zbc_zone_idx(f, io_u->offset + io_u->buflen);
	ze = &f->zbd_info->zone_info[zone_idx_e];

	if (zb->start < ze->start)
		zbc_reset_range(td, f, zb->start, ze->start - zb->start);

	return 0;
}
