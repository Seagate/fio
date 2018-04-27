/*
 * Copyright (C) 2018 Western Digital Corporation or its affiliates.
 *
 * This file is released under the GPL.
 */

#ifndef FIO_ZBC_H
#define FIO_ZBC_H

#include <inttypes.h>

struct fio_file;

/*
 * Zoned block device models.
 */
enum blk_zoned_model {
	ZBC_DM_NONE,	/* Regular block device */
	ZBC_DM_HOST_AWARE,	/* Host-aware zoned block device */
	ZBC_DM_HOST_MANAGED,	/* Host-managed zoned block device */
};

enum io_u_action {
	io_u_accept	= 0,
	io_u_eof	= 1,
};

/**
 * struct fio_zone_info - information about a single ZBC zone
 * @start: zone start in 512 byte units
 * @wp: zone write pointer location in 512 byte units
 * @verify_block: number of blocks that have been verified for this zone
 * @mutex: protects the modifiable members in this structure
 * @type: zone type as defined by enum blk_zone_type
 * @open: whether or not this zone is currently open. Only relevant if
 *		max_open_zones > 0.
 * @reset_zone: whether or not this zone should be reset before writing to it
 */
struct fio_zone_info {
	pthread_mutex_t	mutex;
	uint64_t	start;
	uint64_t	wp;
	uint32_t	verify_block;
	uint8_t		type;
	unsigned int	open:1;
	unsigned int	reset_zone:1;
};

/**
 * zoned_block_device_info - zoned block device characteristics
 * @zone_size: size of a single zone in units of 512 bytes
 * @zone_size_log2: log2 of the zone size in bytes if it is a power of 2 or 0
 *		if the zone size is not a power of 2.
 * @nr_zones: number of zones
 * @refcount: number of fio files that share this structure
 * @zone_info: description of the individual zones
 *
 * Only devices for which all zones have the same size are supported.
 * Note: if the capacity is not a multiple of the zone size then the last zone
 * will be smaller than 'zone_size'.
 */
struct zoned_block_device_info {
	uint64_t		zone_size;
	uint32_t		zone_size_log2;
	uint32_t		nr_zones;
	uint32_t		refcount;
	struct fio_zone_info	zone_info[0];
};

#ifdef CONFIG_LINUX_BLKZONED
void zbc_free_zone_info(struct fio_file *f);
int zbc_init(struct thread_data *td);
void zbc_file_reset(struct thread_data *td, struct fio_file *f);
enum io_u_action zbc_adjust_block(struct thread_data *td, struct io_u *io_u);
int zbc_do_trim(struct thread_data *td, const struct io_u *io_u);
void zbc_update_wp(struct thread_data *td, const struct io_u *io_u);
char *zbc_write_status(const struct group_run_stats *rs);
#else
static inline void zbc_free_zone_info(struct fio_file *f)
{
}

static inline int zbc_init(struct thread_data *td)
{
	return 0;
}

static inline void zbc_file_reset(struct thread_data *td, struct fio_file *f)
{
}

static inline enum io_u_action
zbc_adjust_block(struct thread_data *td, struct io_u *io_u)
{
	return io_u_accept;
}

static inline int zbc_do_trim(struct thread_data *td, const struct io_u *io_u)
{
	return 1;
}

static inline void zbc_update_wp(struct thread_data *td,
				 const struct io_u *io_u)
{
}

static inline char *zbc_write_status(const struct group_run_stats *rs)
{
	return NULL;
}
#endif

#endif /* FIO_ZBC_H */
