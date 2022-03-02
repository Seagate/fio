#include <stdbool.h>
#include <linux/blkzoned.h>
#include "zbd_types.h"
#ifndef FIO_SG_ZD_H
#define FIO_SG_ZD_H
/*
 * If the uapi headers installed on the system lacks zone capacity support,
 * use our local versions. If the installed headers are recent enough to
 * support zone capacity, do not redefine any structs.
 */
#ifndef CONFIG_HAVE_REP_CAPACITY
#define BLK_ZONE_REP_CAPACITY   (1 << 0)

struct blk_zone_v2 {
    __u64   start;          /* Zone start sector */
    __u64   len;            /* Zone length in number of sectors */
    __u64   wp;             /* Zone write pointer position */
    __u8    type;           /* Zone type */
    __u8    cond;           /* Zone condition */
    __u8    non_seq;        /* Non-sequential write resources active */
    __u8    reset;          /* Reset write pointer recommended */
    __u8    resv[4];
    __u64   capacity;       /* Zone capacity in number of sectors */
    __u8    reserved[24];
};
#define blk_zone blk_zone_v2

struct blk_zone_report_v2 {
    __u64   sector;
    __u32   nr_zones;
    __u32   flags;
struct blk_zone zones[0];
};
#define blk_zone_report blk_zone_report_v2
#endif /* CONFIG_HAVE_REP_CAPACITY */

enum use_sg_flags {
    sg_zd_do_not_use    = -2,
    sg_zd_uninitialized = -1,
    sg_zd_use_sata      = 0,
    sg_zd_use_scsi      = 1,
};

int sg_get_flex_zd(int fd, bool* is_flex);
int sg_read_zone_info(int fd, uint64_t start_sector, int* use_sg_rz, uint32_t* block_size,
              struct blk_zone_report *hdr, unsigned int bufsz);
int sg_reset_zones(int fd, struct blk_zone_range* zr, uint64_t zone_size, bool use_scsi);
#endif /* FIO_SG_ZD_H */
