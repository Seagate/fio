/*
 * Copyright (C) 2020 Western Digital Corporation or its affiliates.
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
#include <math.h>

#include "file.h"
#include "fio.h"
#include "lib/pow2.h"
#include "log.h"
#include "oslib/asprintf.h"
#include "smalloc.h"
#include "verify.h"
#include "zbd_types.h"
#include "sg_zone_domains.h"
#include "zbd.h"

#include <linux/blkzoned.h>
#ifndef BLKFINISHZONE
#define BLKFINISHZONE _IOW(0x12, 136, struct blk_zone_range)
#endif


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

/*
 * Get the value of a sysfs attribute for a block device.
 *
 * Returns NULL on failure.
 * Returns a pointer to a string on success.
 * The caller is responsible for freeing the memory.
 */
static char *blkzoned_get_sysfs_attr(const char *file_name, const char *attr)
{
	char *attr_path = NULL;
	struct stat statbuf;
	char *sys_devno_path = NULL;
	char *part_attr_path = NULL;
	char *part_str = NULL;
	char sys_path[PATH_MAX];
	ssize_t sz;
	char *delim = NULL;
	char *attr_str = NULL;

	if (stat(file_name, &statbuf) < 0)
		goto out;

	if (asprintf(&sys_devno_path, "/sys/dev/block/%d:%d",
		     major(statbuf.st_rdev), minor(statbuf.st_rdev)) < 0)
		goto out;

	sz = readlink(sys_devno_path, sys_path, sizeof(sys_path) - 1);
	if (sz < 0)
		goto out;
	sys_path[sz] = '\0';

	/*
	 * If the device is a partition device, cut the device name in the
	 * canonical sysfs path to obtain the sysfs path of the holder device.
	 *   e.g.:  /sys/devices/.../sda/sda1 -> /sys/devices/.../sda
	 */
	if (asprintf(&part_attr_path, "/sys/dev/block/%s/partition",
		     sys_path) < 0)
		goto out;
	part_str = read_file(part_attr_path);
	if (part_str && *part_str == '1') {
		delim = strrchr(sys_path, '/');
		if (!delim)
			goto out;
		*delim = '\0';
	}

	if (asprintf(&attr_path,
		     "/sys/dev/block/%s/%s", sys_path, attr) < 0)
		goto out;

	attr_str = read_file(attr_path);
out:
	free(attr_path);
	free(part_str);
	free(part_attr_path);
	free(sys_devno_path);

	return attr_str;
}

int blkzoned_get_zoned_model(struct thread_data *td, struct fio_file *f,
			     enum zbd_zoned_model *model)
{
	char *model_str = NULL;

	if (f->filetype != FIO_TYPE_BLOCK)
		return -EINVAL;

	*model = ZBD_NONE;

	model_str = blkzoned_get_sysfs_attr(f->file_name, "queue/zoned");
	if (!model_str)
		return 0;

	dprint(FD_ZBD, "%s: zbd model string: %s\n", f->file_name, model_str);
	if (strcmp(model_str, "host-aware") == 0)
		*model = ZBD_HOST_AWARE;
	else if (strcmp(model_str, "host-managed") == 0)
		*model = ZBD_HOST_MANAGED;
	else {
		bool flex_drive = false;
		int fd = -1;
		// Check whether drive is FLEX/zone domains drive
		fd = open(f->file_name, O_RDONLY | O_LARGEFILE);
		// This may not succeed, but if it doesn't it's definitely not a FLEX drive
		sg_get_flex_zd(fd, &flex_drive);
		if (flex_drive)
			*model = ZBD_ZONE_DOMAINS;
		close(fd);
	}

	free(model_str);

	return 0;
}

int blkzoned_get_max_open_zones(struct thread_data *td, struct fio_file *f,
				unsigned int *max_open_zones)
{
	char *max_open_str;

	if (f->filetype != FIO_TYPE_BLOCK)
		return -EIO;

	max_open_str = blkzoned_get_sysfs_attr(f->file_name, "queue/max_open_zones");
	if (!max_open_str) {
		*max_open_zones = 0;
		return 0;
	}

	dprint(FD_ZBD, "%s: max open zones supported by device: %s\n",
	       f->file_name, max_open_str);
	*max_open_zones = atoll(max_open_str);

	free(max_open_str);

	return 0;
}

int blkzoned_get_max_active_zones(struct thread_data *td, struct fio_file *f,
				  unsigned int *max_active_zones)
{
	char *max_active_str;

	if (f->filetype != FIO_TYPE_BLOCK)
		return -EIO;

	max_active_str = blkzoned_get_sysfs_attr(f->file_name, "queue/max_active_zones");
	if (!max_active_str) {
		*max_active_zones = 0;
		return 0;
	}

	dprint(FD_ZBD, "%s: max active zones supported by device: %s\n",
	       f->file_name, max_active_str);
	*max_active_zones = atoll(max_active_str);

	free(max_active_str);

	return 0;
}

static uint64_t zone_capacity(struct blk_zone_report *hdr,
			      struct blk_zone *blkz)
{
	if (hdr->flags & BLK_ZONE_REP_CAPACITY)
		return blkz->capacity << 9;
	return blkz->len << 9;
}

int _blkzoned_report_zones(struct thread_data *td, struct fio_file *f,
			  uint64_t offset, struct zbd_zone *zones,
			  unsigned int nr_zones, int *use_sg_rz, uint32_t *block_size)
{
	struct blk_zone_report *hdr = NULL;
	struct blk_zone *blkz;
	struct zbd_zone *z;
	unsigned int i;
	int fd = -1, ret;
	unsigned int bufsz;
	int lba_power = 9;

	fd = open(f->file_name, O_RDONLY | O_LARGEFILE);
	if (fd < 0)
		return -errno;

	bufsz = sizeof(struct blk_zone_report) + nr_zones * sizeof(struct blk_zone);
	hdr = calloc(1, bufsz);
	if (!hdr) {
		ret = -ENOMEM;
		goto out;
	}

	if (*use_sg_rz <= sg_zd_uninitialized) {
		hdr->nr_zones = nr_zones;
		hdr->sector = offset >> lba_power;
		ret = ioctl(fd, BLKREPORTZONE, hdr);
		dprint(FD_ZBD, "%s: BLKREPORTZONE ioctl failed, ret=%d, err=%d.\n",
			f->file_name, ret, -errno);
	}
	// Get zones using sg_report_zones
	// TODO: Check this failed for the right reason
	if (*use_sg_rz > sg_zd_uninitialized || (ret < 0 && *use_sg_rz > sg_zd_do_not_use)) {
		bool guessed_block_size = false;
		// sg_report_zones uses 64 bytes for the header and 64 bytes for each zone
		bufsz = 64 + nr_zones * 64;
		// sg_report_zones can only return full blocks, so round up to the nearest block, resulting
		// in more than the requested number of zones, unless this would overrun our buffer
		// Assume block size of 512 if unknown
		if (*block_size == 0) {
			guessed_block_size = true;
			*block_size = 512;
		}

		if (bufsz % *block_size != 0)
			bufsz += *block_size - (bufsz % *block_size);
		if ((bufsz - 64) / 64 > ZBD_REPORT_MAX_ZONES )
			bufsz -= *block_size;
		if (guessed_block_size)
			*block_size = 0;
		hdr = realloc(hdr, bufsz);
		if (!hdr) {
			dprint(FD_ZBD, "%s: Realloc returned NULL in blkzoned_report_zones after trying to "
				"allocate %d bytes\n", f->file_name, bufsz);
			ret = -ENOMEM;
			goto out;
		}
		ret = sg_read_zone_info(fd, offset, use_sg_rz, block_size, hdr, bufsz);
		if (ret) {
			dprint(FD_ZBD, "%s: sg_read_zone_info failed, ret=%d, err=%d.\n",
				f->file_name, ret, -errno);
		}
	}
	if (ret) {
		ret = -errno;
		goto out;
	}

	if (*block_size != 0)
		lba_power = log2(*block_size);
	nr_zones = hdr->nr_zones;
	blkz = (void *) hdr + sizeof(*hdr);
	z = &zones[0];
	for (i = 0; i < nr_zones; i++, z++, blkz++) {
		z->start = blkz->start << lba_power;
		z->wp = blkz->wp << lba_power;
		z->len = blkz->len << lba_power;
		z->capacity = zone_capacity(hdr, blkz);

		switch (blkz->type) {
		case BLK_ZONE_TYPE_CONVENTIONAL:
			z->type = ZBD_ZONE_TYPE_CNV;
			break;
		case BLK_ZONE_TYPE_SEQWRITE_REQ:
			z->type = ZBD_ZONE_TYPE_SWR;
			break;
		case BLK_ZONE_TYPE_SEQWRITE_PREF:
			z->type = ZBD_ZONE_TYPE_SWP;
			break;
		case ZBD_ZONE_TYPE_FLEX:
			z->type = ZBD_ZONE_TYPE_FLEX;
			break;
		default:
			dprint(FD_ZBD, "Encountered unknown zone type %d\n", blkz->type);
			td_verror(td, errno, "invalid zone type");
			log_err("%s: invalid type for zone at sector %llu.\n",
				f->file_name, (unsigned long long)offset >> 9);
			ret = -EIO;
			goto out;
		}

		switch (blkz->cond) {
		case BLK_ZONE_COND_NOT_WP:
			z->cond = ZBD_ZONE_COND_NOT_WP;
			break;
		case BLK_ZONE_COND_EMPTY:
			z->cond = ZBD_ZONE_COND_EMPTY;
			break;
		case BLK_ZONE_COND_IMP_OPEN:
			z->cond = ZBD_ZONE_COND_IMP_OPEN;
			break;
		case BLK_ZONE_COND_EXP_OPEN:
			z->cond = ZBD_ZONE_COND_EXP_OPEN;
			break;
		case BLK_ZONE_COND_CLOSED:
		// case BLK_ZONE_COND_INACTIVE:
			z->cond = ZBD_ZONE_COND_CLOSED;
			break;
		case BLK_ZONE_COND_FULL:
			z->cond = ZBD_ZONE_COND_FULL;
			break;
		case BLK_ZONE_COND_READONLY:
		case BLK_ZONE_COND_OFFLINE:
		default:
			/* Treat all these conditions as offline (don't use!) */
			z->cond = ZBD_ZONE_COND_OFFLINE;
			z->wp = z->start;
		}
	}

	ret = nr_zones;
out:
	free(hdr);
	close(fd);
	return ret;
}


unsigned int practical_max_report_zones = ZBD_REPORT_MAX_ZONES;


int blkzoned_report_zones(struct thread_data *td, struct fio_file *f,
			  uint64_t offset, struct zbd_zone *zones,
			  unsigned int nr_zones, int *use_sg_rz, uint32_t *block_size) {
	int ret, i;
	if (nr_zones > practical_max_report_zones) {
		nr_zones = practical_max_report_zones;
	}
	// Try up to 4 times on a report zones on EINVAL, reducing nr_zones to a minimum of 2048
	for (i = 0; i < 4; i++) {
		ret = _blkzoned_report_zones(td, f, offset, zones, nr_zones, use_sg_rz, block_size);
		if (ret == -EINVAL && nr_zones > 2048) {
			// Might want to only set this based on repeated failures
			practical_max_report_zones = nr_zones / 2;
			if (practical_max_report_zones < 2048) {
				practical_max_report_zones = 2048;
			}
			dprint(
				FD_ZBD, "%s: EINVAL received from report zones, retrying with nr_zones changed from %u to %u\n",
				f->file_name, nr_zones, practical_max_report_zones);
			nr_zones = practical_max_report_zones;
		} else {
			break;
		}
	}
	return ret;
}


int blkzoned_reset_wp(struct thread_data *td, struct fio_file *f,
		      uint64_t offset, uint64_t length)
{
	int lba_power = 9;
	struct blk_zone_range zr = {
		.sector         = offset >> lba_power,
		.nr_sectors     = length >> lba_power,
	};
	int fd, ret = 0;

	/* If the file is not yet opened, open it for this function. */
	fd = f->fd;
	if (fd < 0) {
		fd = open(f->file_name, O_RDWR | O_LARGEFILE);
		if (fd < 0)
			return -errno;
	}

	ret = ioctl(fd, BLKRESETZONE, &zr);
	if (ret < 0) {
		lba_power = log2(f->zbd_info->block_size);
		zr.sector = offset >> lba_power;
		zr.nr_sectors = length >> lba_power;
		ret = sg_reset_zones(fd, &zr, f->zbd_info->zone_size >> lba_power, f->zbd_info->use_sg == sg_zd_use_scsi);
	}
	if (ret < 0)
		ret = -errno;

	if (f->fd < 0)
		close(fd);

	return ret;
}

int blkzoned_finish_zone(struct thread_data *td, struct fio_file *f,
			 uint64_t offset, uint64_t length)
{
	struct blk_zone_range zr = {
		.sector         = offset >> 9,
		.nr_sectors     = length >> 9,
	};
	int fd, ret = 0;

	/* If the file is not yet opened, open it for this function. */
	fd = f->fd;
	if (fd < 0) {
		fd = open(f->file_name, O_RDWR | O_LARGEFILE);
		if (fd < 0)
			return -errno;
	}

	if (ioctl(fd, BLKFINISHZONE, &zr) < 0) {
		ret = -errno;
		/*
		 * Kernel versions older than 5.5 do not support BLKFINISHZONE
		 * and return the ENOTTY error code. These old kernels only
		 * support block devices that close zones automatically.
		 */
		if (ret == ENOTTY)
			ret = 0;
	}

	if (f->fd < 0)
		close(fd);

	return ret;
}
