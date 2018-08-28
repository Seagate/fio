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
#include <unistd.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <scsi/sg.h> /* take care: fetches glibc's /usr/include/scsi/sg.h */
#include "file.h"
#include "fio.h"
#include "lib/pow2.h"
#include "log.h"
#include "smalloc.h"
#include "verify.h"
#include "zbd.h"

#define INQ_CMD_CODE 0x12
#define INQ_LEN 6
#define RZ_CMD_CODE 0x4A
#define SCSI_RZ_CMD_CODE 0x95
#define REZ_CMD_CODE 0x9F
#define SCSI_REZ_CMD_CODE 0x94
#define RC16_CMD_CODE 0x9E
#define PT_PROTOCOL_DMA 0x0D	// DMA protocol and Extend bit
#define PT_PROTOCOL_ND 0x07	// Non-data and Extend bit
// 0 second timeout, TDIR_IN, BYT_BLOCK set, T_LENGTH set to 2 to use sector count
#define MISC_BYTE 0x0E
#define PT_CMD_CODE 0x85
#define PT_CMD_LEN 16
#define HDR_SIZE 64
#define ZONE_INFO_SIZE 64

// Function declarations
static int zbd_reset_zone(struct thread_data *td, const struct fio_file *f,
			  struct fio_zone_info *z);

/**
 * os_is_little_endian - check OS endianess for a
 * uint32_t, assumes same endianess for other
 * unsigned integers
 */
static bool os_is_little_endian() {
	uint32_t test_int = 0x0A0B0C0D;
	unsigned char* byte_pointer;
	byte_pointer = (unsigned char*) &test_int;
	if (byte_pointer[0] == 0x0A)
		return false;
	else if (byte_pointer[0] == 0x0D)
		return true;
	else
		log_err("Environment seems to be neither big or little endian\n");
	return true;
}

/**
 * unpack_bytes - unpack unsigned integers of arbitrary
 * length from byte buffers
 */
static void unpack_bytes(unsigned char* byte_buf, unsigned int num_bytes,
					bool little_endian, void* ret_var) {
	int ind;
	unsigned char* ret_bytes;
	static bool need_init = true;
	static bool os_little_endian = false;
	if (need_init) {
		os_little_endian = os_is_little_endian();
		need_init = false;
	}
	ret_bytes = ret_var;
	for (ind = 0; ind < num_bytes; ind++) {
		if (little_endian == os_little_endian)
			ret_bytes[ind] = byte_buf[ind];
		else
			ret_bytes[ind] = byte_buf[num_bytes - 1 - ind];
	}
}

/**
 * sg_send_cdb - send generic CDBs
 * @fd: file descriptor
 * @cdb_buf: command descriptor block buffer
 * @cdb_len: length of cdb buffer
 * @data_buf: buffer to hold outgoing or incoming data
 * @bufsz: size of data_buf
 * @io_hdr_pt: pointer to io_hdr. Can be set to NULL or checked
 *			after running command for various information
 */
static int sg_send_cdb(int fd, unsigned char* cdb_buf, unsigned char cdb_len,
				void *data_buf, unsigned int bufsz, sg_io_hdr_t* io_hdr_pt) {
	sg_io_hdr_t io_hdr;
	unsigned char sense_buffer[64];

	if (io_hdr_pt == NULL)
		io_hdr_pt = &io_hdr;
	/* Prepare SCSI command */
	memset(&io_hdr, 0, sizeof(sg_io_hdr_t));
	io_hdr_pt->interface_id = 'S';
	io_hdr_pt->cmd_len = cdb_len;
	/* io_hdr_pt->iovec_count = 0; */  /* memset takes care of this */
	io_hdr_pt->mx_sb_len = sizeof(sense_buffer);
	io_hdr_pt->dxfer_direction = SG_DXFER_FROM_DEV;
	io_hdr_pt->dxfer_len = bufsz;
	io_hdr_pt->dxferp = data_buf;
	io_hdr_pt->cmdp = cdb_buf;
	io_hdr_pt->sbp = sense_buffer;
	// Maybe should let users set these themselves somehow
	io_hdr_pt->timeout = 30000;     /* 30000 millisecs == 30 seconds */
	/* io_hdr_pt->flags = 0; */     /* take defaults: indirect IO, etc */
	/* io_hdr_pt->pack_id = 0; */
	/* io_hdr_pt->usr_ptr = NULL; */

	if (ioctl(fd, SG_IO, io_hdr_pt) < 0) {
		return -errno;
	}

	/* now for the error processing */
	if ((io_hdr_pt->info & SG_INFO_OK_MASK) != SG_INFO_OK) {
		dprint(FD_ZBD, "Error sending following CDB:\n");
		if (1 << FD_ZBD & fio_debug) {
			for (int k = 0; k < cdb_len; k++)
				log_info("%02X ", cdb_buf[k]);
			log_info("\nCommand returned with following sense buffer:\n");
			for (int k = 0; k < 64; k++)
				log_info("%02X ", sense_buffer[k]);
			log_info("\n");
		}
		return -EBADE;
	}
	return 0;
}

/**
 * sg_get_protocol - Get first 36 bytes of inquiry
 * and parse the vendor string to see if device is ATA
 * @fd: file descriptor
 * @is_sas: True if not SATA
 */
int sg_get_protocol(int fd, bool* is_sas)
{
	unsigned char inq_cmd_blk[6];
	unsigned char ret_buf[36];
	int ret;

	inq_cmd_blk[0] = INQ_CMD_CODE;
	inq_cmd_blk[1] = 0;  // EVPD
	inq_cmd_blk[2] = 0;  // Page Code
	inq_cmd_blk[3] = 0;  // Allocation bytes - MSB
	inq_cmd_blk[4] = 36;  // allocation bytes - LSB
	inq_cmd_blk[5] = 0;

	ret = sg_send_cdb(fd, inq_cmd_blk, INQ_LEN, ret_buf, 36, NULL);
	if (ret < 0)
		return ret;

	ret_buf[16] = '\0';
	*is_sas = strcmp((char*) &ret_buf[8], "ATA     ") != 0;
	return 0;
}

/**
 * sg_read_capacity - issue a read capacity command to
 * get the block size of the device
 * @fd: file descriptor
 * @block_size: returned block size
 */
int sg_read_capacity(int fd, uint32_t* block_size)
{
	unsigned char rcCmdBlk[16];
	unsigned char retBuf[4096];
	int ret;

	rcCmdBlk[0] = RC16_CMD_CODE;
	rcCmdBlk[1] = 0x10;  // Service action (like a subfunction code)
	rcCmdBlk[2] = 0;  // Obsolete LBA field
	rcCmdBlk[3] = 0;
	rcCmdBlk[4] = 0;
	rcCmdBlk[5] = 0;
	rcCmdBlk[6] = 0;
	rcCmdBlk[7] = 0;
	rcCmdBlk[8] = 0;
	rcCmdBlk[9] = 0;
	rcCmdBlk[10] = 0;  // Allocation length (return 4k bytes)
	rcCmdBlk[11] = 0;
	rcCmdBlk[12] = 1;
	rcCmdBlk[13] = 0;
	rcCmdBlk[14] = 0;  // Obsolete PMI byte
	rcCmdBlk[15] = 0;  // Control byte

	ret = sg_send_cdb(fd, rcCmdBlk, 16, retBuf, 4096, NULL);
	if (ret < 0)
		return ret;

	unpack_bytes(&retBuf[8], 4, false, block_size);
	return 0;
}

/**
 * sg_report_zones - get zones by issuing the report zones CDB directly
 * @fd: file descriptor
 * @start_sector: first sector to report zones from
 * @buf: buffer to hold return data in
 * @bufsz: size of buf
 * @use_scsi: whether to use SCSI report zones or pass through ATA command
 *				SCSI command might be usable for both, depending on sat4
 *				layer
 */
static int sg_report_zones(int fd, uint64_t start_lba, void *buf,
							unsigned int bufsz, bool use_scsi) {
	uint8_t reporting_options = 0;
	uint16_t sector_count;
	unsigned char rzCmdBlk[PT_CMD_LEN];

	if (use_scsi) {
		rzCmdBlk[0] = SCSI_RZ_CMD_CODE;
		rzCmdBlk[1] = 0;
		rzCmdBlk[2] = (start_lba >> 56) & 0xFF;
		rzCmdBlk[3] = (start_lba >> 48) & 0xFF;
		rzCmdBlk[4] = (start_lba >> 40) & 0xFF;
		rzCmdBlk[5] = (start_lba >> 32) & 0xFF;
		rzCmdBlk[6] = (start_lba >> 24) & 0xFF;
		rzCmdBlk[7] = (start_lba >> 16) & 0xFF;
		rzCmdBlk[8] = (start_lba >> 8) & 0xFF;
		rzCmdBlk[9] = start_lba & 0xFF;
		rzCmdBlk[10] = (bufsz >> 24) & 0xFF;
		rzCmdBlk[11] = (bufsz >> 16) & 0xFF;
		rzCmdBlk[12] = (bufsz >> 8) & 0xFF;
		rzCmdBlk[13] = bufsz & 0xFF;
		rzCmdBlk[14] = reporting_options;
		rzCmdBlk[15] = 0;
	}
	else {
		sector_count = bufsz / 512;  // This count is always in 512 blocks as per specification

		rzCmdBlk[0] = PT_CMD_CODE;
		rzCmdBlk[1] = PT_PROTOCOL_DMA;
		rzCmdBlk[2] = MISC_BYTE;
		rzCmdBlk[3] = (unsigned char) reporting_options;
		rzCmdBlk[4] = 0;
		rzCmdBlk[5] = (unsigned char) (sector_count >> 8) & 0xFF;
		rzCmdBlk[6] = (unsigned char) sector_count & 0xFF;
		rzCmdBlk[7] = (unsigned char) (start_lba >> 24) & 0xFF;
		rzCmdBlk[8] = (unsigned char) start_lba & 0xFF;
		rzCmdBlk[9] = (unsigned char) (start_lba >> 32) & 0xFF;
		rzCmdBlk[10] = (unsigned char) (start_lba >> 8) & 0xFF;
		rzCmdBlk[11] = (unsigned char) (start_lba >> 40) & 0xFF;
		rzCmdBlk[12] = (unsigned char) (start_lba >> 16) & 0xFF;
		rzCmdBlk[13] = 0;
		rzCmdBlk[14] = RZ_CMD_CODE;
		rzCmdBlk[15] = 0;
	}

	return sg_send_cdb(fd, rzCmdBlk, PT_CMD_LEN, buf, bufsz, NULL);
}

/**
 * sg_reset_zones - reset all zones specified by zr parameter
 * @fd: file descriptor
 * @zr: start and number of zones to reset
 * @block_size: logical block size of device in bytes -- used to convert
 *				sectors from zr into LBAs
 * @zone_size: sectors per zone
 * @use_scsi: whether to use the SCSI or the ATA command
 */
static int sg_reset_zones(int fd, struct blk_zone_range* zr, uint32_t block_size,
		uint64_t zone_size, bool use_scsi) {
	uint8_t sub_cmd = 4;
	unsigned char rez_cmd_blk[PT_CMD_LEN];
	uint16_t sec_per_lba = block_size / 512;
	uint64_t cur_lba, last_lba;
	int ret;

	zone_size = zone_size / sec_per_lba;
	cur_lba = zr->sector / sec_per_lba;
	last_lba = cur_lba + (zr->nr_sectors / sec_per_lba);

	if (use_scsi) {
		rez_cmd_blk[0] = SCSI_REZ_CMD_CODE;
		// Service action
		rez_cmd_blk[1] = 0x4;
		// Reserved
		rez_cmd_blk[10] = 0;
		rez_cmd_blk[11] = 0;
		// Sector size -- for now this seems to abort if 0 is not sent
		rez_cmd_blk[12] = 0;
		rez_cmd_blk[13] = 0;
		// Reset all can be set here
		rez_cmd_blk[14] = 0;
		rez_cmd_blk[15] = 0;
		while (cur_lba < last_lba) {
			// Set LBAs
			rez_cmd_blk[2] = (unsigned char) (cur_lba >> 56) & 0xFF;
			rez_cmd_blk[3] = (unsigned char) (cur_lba >> 48) & 0xFF;
			rez_cmd_blk[4] = (unsigned char) (cur_lba >> 40) & 0xFF;
			rez_cmd_blk[5] = (unsigned char) (cur_lba >> 32) & 0xFF;
			rez_cmd_blk[6] = (unsigned char) (cur_lba >> 24) & 0xFF;
			rez_cmd_blk[7] = (unsigned char) (cur_lba >> 16) & 0xFF;
			rez_cmd_blk[8] = (unsigned char) (cur_lba >> 8) & 0xFF;
			rez_cmd_blk[9] = (unsigned char) cur_lba & 0xFF;
			ret = sg_send_cdb(fd, rez_cmd_blk, PT_CMD_LEN, NULL, 0, NULL);
			if (ret != 0)
				return ret;
			cur_lba += zone_size;
		}
	}
	else {
		rez_cmd_blk[0] = PT_CMD_CODE;
		rez_cmd_blk[1] = PT_PROTOCOL_ND;
		// Non-data command doesn't need to use this byte
		rez_cmd_blk[2] = 0;
		// Features high used for resetting all zones
		rez_cmd_blk[3] = 0;
		// Features low used for sub command
		rez_cmd_blk[4] = sub_cmd;
		// This might be usable for multiple sectors, but can't count on it
		// for now
		rez_cmd_blk[5] = 0;
		rez_cmd_blk[6] = 0;
		// Unused device byte
		rez_cmd_blk[13] = 0;
		rez_cmd_blk[14] = REZ_CMD_CODE;
		rez_cmd_blk[15] = 0;
		while (cur_lba < last_lba) {
			// Set LBAs
			rez_cmd_blk[7] = (unsigned char) (cur_lba >> 24) & 0xFF;
			rez_cmd_blk[8] = (unsigned char) cur_lba & 0xFF;
			rez_cmd_blk[9] = (unsigned char) (cur_lba >> 32) & 0xFF;
			rez_cmd_blk[10] = (unsigned char) (cur_lba >> 8) & 0xFF;
			rez_cmd_blk[11] = (unsigned char) (cur_lba >> 40) & 0xFF;
			rez_cmd_blk[12] = (unsigned char) (cur_lba >> 16) & 0xFF;
			ret = sg_send_cdb(fd, rez_cmd_blk, PT_CMD_LEN, NULL, 0, NULL);
			if (ret != 0)
				return ret;
			cur_lba += zone_size;
		}
	}

	return ret;
}

/**
 * parse_to_structs - parse return from sg_report_zones
 * into a format similar to that returned by
 * ioctl(fd, BLKREPORTZONE, buf)
 * @buf: buffer written into by sg_report_zones
 * @bufsz: size of buffer written into by sg_report_zones
 * @secPerLba: number of linux 512 sectors per reported LBA
 */
static int parse_to_structs(unsigned char* buf, unsigned int bufsz,
	                        unsigned int secPerLba, bool use_scsi) {
	uint32_t num_zones;
	uint8_t zone_type;
	uint8_t zone_cond;
	uint64_t zone_size;
	uint64_t zone_start;
	uint64_t write_pointer;
	struct blk_zone_report *hdr;
	struct blk_zone *zone_struct;
	unsigned int struct_offset;
	unsigned int data_offset;
	unsigned char* cur_zone;
	if (sizeof(struct blk_zone_report) > HDR_SIZE) {
		log_err("Cannot parse zone information in place if blk_zone_report "
				"structure is bigger than the raw data\n");
		return 1;
	}
	else if (sizeof(struct blk_zone) > ZONE_INFO_SIZE) {
		log_err("Cannot parse zone information in place if blk_zone "
			   "structure is bigger than the raw data\n");
		return 1;
	}
	// Parse the header first
	unpack_bytes(buf, 4, !use_scsi, &num_zones);
	num_zones = num_zones / ZONE_INFO_SIZE;


	// Zero out the space needed by the structure
	memset(buf, 0, sizeof(struct blk_zone_report));
	hdr = (struct blk_zone_report*) buf;
	hdr->nr_zones = num_zones;

	num_zones = 0;
	data_offset = HDR_SIZE;
	struct_offset = sizeof(struct blk_zone_report);
	while (data_offset < bufsz && num_zones < hdr->nr_zones) {
		// If there isn't enough data for another zone, break out
		if (bufsz - data_offset < ZONE_INFO_SIZE) {
			break;
		}
		cur_zone = &buf[data_offset];
		zone_type = cur_zone[0] & 0xF;
		zone_cond = cur_zone[1] >> 4;
		unpack_bytes(&cur_zone[8], 8, !use_scsi, &zone_size);
		unpack_bytes(&cur_zone[16], 8, !use_scsi, &zone_start);
		unpack_bytes(&cur_zone[24], 8, !use_scsi, &write_pointer);
		// If too many zones are requested, command will zero pad
		if (zone_size == 0) {
			break;
		}
		// Convert large marker wp to start + zone_size
		if (write_pointer > zone_start + zone_size)
			write_pointer = zone_start + zone_size;
		// Convert LBAs to sectors
		zone_size *= secPerLba;
		zone_start *= secPerLba;
		write_pointer *= secPerLba;
		// Zero out the space needed by the structure
		zone_struct = (struct blk_zone*) &buf[struct_offset];
		memset(zone_struct, 0, sizeof(struct blk_zone));
		zone_struct->start = zone_start;
		zone_struct->len = zone_size;
		zone_struct->wp = write_pointer;
		zone_struct->type = zone_type;
		zone_struct->cond = zone_cond;
		data_offset += ZONE_INFO_SIZE;
		struct_offset += sizeof(struct blk_zone);
		num_zones++;
	}
	// Set the header start to the first zone start
	zone_struct = (struct blk_zone*) &buf[sizeof(struct blk_zone_report)];
	hdr->sector = zone_struct->start;
	// Modify header to represent the number of zones in the buffer
	hdr->nr_zones = num_zones;
	return 0;
}

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

/* The caller must hold z->mutex. */
static bool zbd_zone_full(const struct fio_file *f, struct fio_zone_info *z)
{
	assert(wp_zone(z));

	return z->wp >= z->start + f->zbd_info->zone_size;
}

static bool is_valid_offset(const struct fio_file *f, uint64_t offset,
							struct thread_data* td, enum fio_ddir ddir)
{
	int iter;
	struct thread_options* o = &td->o;
	uint64_t cur_size;
	uint64_t lastb = last_block(td, f, ddir);
	if (td_random(td) && ((o->random_distribution == FIO_RAND_DIST_ZONED_ABS) ||
		(o->random_distribution == FIO_RAND_DIST_ZONED)))
	{
		for (iter = 0; iter < o->zone_split_nr[ddir]; iter++)
		{
			if (o->random_distribution == FIO_RAND_DIST_ZONED_ABS)
				cur_size = o->zone_split[ddir][iter].size;
			else
				cur_size = (lastb * o->zone_split[ddir][iter].size_perc) / 100ULL;
			if (o->zone_split[ddir][iter].access_perc > 0 &&
				offset < cur_size)
				return true;
			offset -= cur_size;
		}
	}
	else
	{
		return (uint64_t)(offset - f->file_offset) < f->io_size;
	}
	return false;
}

static void get_valid_offset(const struct fio_file *f, uint64_t* offset,
							struct thread_data *td, enum fio_ddir ddir, bool forward)
{
	uint64_t valid_offset, wrap_offset, cur_offset, cur_size;
	bool offset_found = false;
	uint64_t lastb = last_block(td, f, ddir);
	struct thread_options* o = &td->o;
	int iter;
	if (td_random(td) && ((o->random_distribution == FIO_RAND_DIST_ZONED_ABS) ||
		(o->random_distribution == FIO_RAND_DIST_ZONED)))
	{
		cur_offset = 0;
		valid_offset = 0;
		if (forward)
			wrap_offset = f->real_file_size;
		else
			wrap_offset = 0;
		for (iter = 0; iter < o->zone_split_nr[ddir]; iter++)
		{
			if (o->random_distribution == FIO_RAND_DIST_ZONED_ABS)
				cur_size = o->zone_split[ddir][iter].size;
			else
				cur_size = (lastb * o->zone_split[ddir][iter].size_perc) / 100ULL;
			if (o->zone_split[ddir][iter].access_perc > 0)
			{
				// If the input offset is valid, we can just return
				if (*offset >= cur_offset && *offset < cur_offset + cur_size)
					return;
				else if (cur_offset < *offset)
				{
					if (!forward)
					{
						offset_found = true;
						valid_offset = cur_offset + cur_size - 1;
					}
					// Record the first valid offset in case we need to wrap
					// forwards
					else if (wrap_offset > cur_offset)
						wrap_offset = cur_offset;
				}
				else if (cur_offset + cur_size >= *offset)
				{
					if (forward)
					{
						offset_found = true;
						valid_offset = cur_offset;
						break;
					}
					// Record the last valid offset in case we need to wrap
					// backwards
					else if (wrap_offset < cur_offset + cur_size - 1)
						wrap_offset = cur_offset + cur_size - 1;
				}
			}
			cur_offset += cur_size;
			if (!forward && (cur_offset > *offset) && offset_found)
				break;
		}
		// Use the wrap_offset if needed
		if (offset_found)
			*offset = valid_offset;
		else
			*offset = wrap_offset;
	}
	else if ((*offset < f->file_offset) ||
		(*offset >= f->file_offset + f->io_size))
	{
		if (forward)
			*offset = f->file_offset;
		else
			*offset = f->file_offset + f->io_size - 1;
	}
}

static bool is_valid_zone_ptr(const struct fio_file *f,
		const struct fio_zone_info *z)
{
	return f->zbd_info->zone_info <= z &&
		z < f->zbd_info->zone_info + f->zbd_info->nr_zones;
}

/* Verify whether direct I/O is used for all ZBD drives. */
static bool zbd_using_direct_io(void)
{
	struct thread_data *td;
	struct fio_file *f;
	int i, j;

	for_each_td(td, i) {
		if (td->o.odirect || !(td->o.td_ddir & TD_DDIR_WRITE) || !strcmp(td->o.ioengine, "sg"))
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
	struct fio_zone_info *z;

	assert(f->zbd_info);
	zone_idx_b = zbd_zone_idx(f, f->file_offset);
	zone_idx_e = zbd_zone_idx(f, f->file_offset + f->io_size);
	for (zone_idx = zone_idx_b; zone_idx <= zone_idx_e; zone_idx++) {
		z = &f->zbd_info->zone_info[zone_idx];
		if (wp_zone(z) ||
		    z->type == OFFLINE_ZONE_TYPE)
			return true;
	}

	return false;
}

static bool zbd_verify_sizes(void)
{
	struct fio_zone_info *z;
	struct thread_data *td;
	struct fio_file *f;
	uint64_t new_offset, new_end;
	uint32_t zone_idx, zones_checked;
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
			// If the starting offset zone is offline, scan forward to an
			// online zone, wrapping if needed
			if (z->type == OFFLINE_ZONE_TYPE) {
				for (zones_checked = 1; zones_checked < f->zbd_info->nr_zones; zones_checked++)
				{
					zone_idx = zbd_zone_idx(f, f->file_offset);
					z = &f->zbd_info->zone_info[(zone_idx + zones_checked) % f->zbd_info->nr_zones];
					if (z->type != OFFLINE_ZONE_TYPE)
						break;
				}
				if (z->type == OFFLINE_ZONE_TYPE)
					log_err("%s: No online zones found\n", f->file_name);
				f->file_offset = (z->start) << 9;
			}
			// If the user defined start isn't equal to the write pointer,
			// and we're sequentially writing, need to reset the zone
			if (z->type == BLK_ZONE_TYPE_SEQWRITE_REQ &&
				f->file_offset != (z->wp << 9) &&
				td_write(td) && !td_random(td)) {
				// If fd is invalid, set the write pointer to an impossible value
				// so that zbd_file_reset knows to reset the starting zone
				if (f->fd == -1)
					z->wp = z->start + f->zbd_info->zone_size + 1;
				else
					zbd_reset_zone(td, f, z);
			}
			if (f->file_offset != (z->start << 9)) {
				new_offset = z->start << 9;
				dprint(FD_ZBD, "%s: rounded down offset from %lu to %lu\n",
					f->file_name, f->file_offset, new_offset);
				// Set the sequential starting offset to the original offset
				// Increase the file io_size -- this shouldn't affect the amount of
				// io actually completed
				f->io_size += (f->file_offset - new_offset);
				f->file_offset = new_offset;
			}
			zone_idx = zbd_zone_idx(f, f->file_offset + f->io_size);
			z = &f->zbd_info->zone_info[zone_idx];
			new_end = z->start << 9;
			if (f->file_offset + f->io_size != new_end) {
				// Try to round up to next zone if possible
				zone_idx = zbd_zone_idx(f, f->file_offset + f->io_size +
					(f->zbd_info->zone_size << 9));
				z = &f->zbd_info->zone_info[zone_idx];
				new_end = z->start << 9;
				dprint(FD_ZBD, "%s: rounded io_size from %lu to %lu\n",
					f->file_name, f->io_size, new_end - f->file_offset);
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
static int read_zone_info(int fd, int* use_sg_rz, uint32_t* block_size,
			uint64_t start_sector, void *buf, unsigned int bufsz)
{
	struct blk_zone_report *hdr = buf;
	int ret = -1;
	uint64_t start_lba;
	int retry;
	bool use_scsi;

	if (bufsz < sizeof(*hdr))
		return -ENOMEM;

	if (*use_sg_rz <= 0) {
		memset(hdr, 0, sizeof(*hdr));
		hdr->nr_zones = (bufsz - sizeof(*hdr)) / sizeof(struct blk_zone);
		hdr->sector = start_sector;
		for (retry = 0; retry < 10; retry++) {
			ret = ioctl(fd, BLKREPORTZONE, hdr) >= 0 ? 0 : -errno;;
			// Doublecheck the returned header returned a non-zero number of zones
			if (ret == 0 && hdr->nr_zones == 0)
				ret = -42;
			if (ret == 0) {
				*use_sg_rz = 0;
				break;
			}
		}
	}

	// Try issuing the sg_report_zones instead
	if (ret != 0 || *use_sg_rz != 0) {
		if (*block_size < 512) {
			ret = sg_read_capacity(fd, block_size);
			if (ret != 0) {
				log_info("failed to read capacity with return %d\n", ret);
				*block_size = 0;
				return ret;
			}
		}
		// Round the bufsz to an even multiple of the block size
		bufsz = (bufsz / *block_size) * (*block_size);
		start_lba = (start_sector * 512) / (*block_size);
		// Get whether the device is SAS or SATA
		if (*use_sg_rz == -1) {
			ret = sg_get_protocol(fd, &use_scsi);
			if (ret != 0) {
				log_info("failed to issue inquiry with return %d\n", ret);
				return ret;
			}
			*use_sg_rz = use_scsi ? 2: 1;
		} else
			use_scsi = *use_sg_rz == 2;
		for (retry = 0; retry < 10; retry++) {
			ret = sg_report_zones(fd, start_lba, buf, bufsz, use_scsi);
			if (ret != -EINVAL && ret != -EBADE) {
				break;
			}
		}
		if (ret != 0)
			return ret;

		ret = parse_to_structs(buf, bufsz, *block_size / 512, use_scsi);
		if (ret != 0) {
			log_info("failed to parse to structs with return %d\n", ret);
		}
	}

	return ret;
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
	uint32_t nr_zones, block_size, j;
	struct blk_zone_report *hdr;
	const struct blk_zone *z;
	struct fio_zone_info *p;
	uint64_t zone_size, start_sector = 0;
	struct zoned_block_device_info *zbd_info = NULL;
	enum blk_zoned_model zbd_model;
	pthread_mutexattr_t attr;
	void *buf;
	int fd, i, use_sg, ret = 0;
	void* aligned_ptr;

	pthread_mutexattr_init(&attr);
	pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);
	pthread_mutexattr_setpshared(&attr, true);

	buf = malloc(bufsz + page_mask);
	if (!buf)
	{
		log_err("fio: Could not allocate memory for %s's zone table\n", f->file_name);
		goto out;
	}

	fd = open(f->file_name, O_RDONLY | O_LARGEFILE);
	if (fd < 0) {
		ret = -errno;
		log_err("fio: Could not open %s\n", f->file_name);
		goto free;
	}

	// Need to align the input buffer to the page size
	aligned_ptr = PTR_ALIGN(buf, page_mask);
	use_sg = -1;
	block_size = 0;
	memset(aligned_ptr, 0x77, 16);
	ret = read_zone_info(fd, &use_sg, &block_size, 0, aligned_ptr, bufsz);
	if (ret != 0)
		goto check_ret;
	hdr = aligned_ptr;
	z = (void *)(hdr + 1);
	zone_size = z->len;
	nr_zones = ((f->real_file_size >> 9) + zone_size - 1) / zone_size;
	if (hdr->nr_zones < 1) {
		log_info("fio: %s has invalid zone information.\n",
			 f->file_name);
		goto close;
	}

	dprint(FD_ZBD, "Device %s has %d zones of size %lu KB\n", f->file_name,
			nr_zones, zone_size / 2);
	zbd_info = scalloc(1, sizeof(*zbd_info) +
				(nr_zones + 1) * sizeof(zbd_info->zone_info[0]));
	ret = -ENOMEM;
	if (!zbd_info)
		goto close;
	pthread_mutex_init(&zbd_info->mutex, &attr);
	zbd_info->refcount = 1;
	zbd_info->use_sg = use_sg;
	zbd_info->block_size = block_size;
	p = &zbd_info->zone_info[0];

	for (start_sector = 0, j = 0; j < nr_zones;) {
		z = (void *)(hdr + 1);
		for (i = 0; i < hdr->nr_zones; i++, j++, z++, p++) {
			pthread_mutex_init(&p->mutex, &attr);
			p->start = z->start;
			p->wp = z->wp;
			// Treat full FLEX zones as conventional zones
			if (z->type == FLEX_ZONE_TYPE && z->cond == 0xE) {
				p->type = 1;
			}
			// Add offline zones with type 0xFF
			else if (z->cond == 0xF) {
				p->type = OFFLINE_ZONE_TYPE;
			}
			else {
				p->type = z->type;
			}
			if (j > 0 && p->start != p[-1].start + zone_size) {
				log_info("%s: invalid zone data\n",
					 f->file_name);
				ret = -EINVAL;
				goto close;
			}
			if (nr_zones - j == 0) {
				// For reasons completely opaque to me, if we exit this loop
				// normally on the last try, the postred marker will get
				// set to 0, causing a valid but apparently harmless
				// warning that I'd still rather avoid -- likely
				// to be system dependent
				break;
			}
		}
		z--;
		start_sector = z->start + z->len;
		if (j >= nr_zones)
			break;
		ret = read_zone_info(fd, &zbd_info->use_sg, &zbd_info->block_size,
							start_sector, aligned_ptr, bufsz);
		if (ret < 0) {
			goto check_ret;
		}
	}
	/* a sentinel */
	zbd_info->zone_info[nr_zones].start = start_sector;
	zbd_info->zone_info[nr_zones].type = OFFLINE_ZONE_TYPE;

	// Set all the offline zone's wp to the next valid zone start, or 0
	start_sector = 0;
	j = nr_zones;
	while (j != 0) {
		j--;
		p = &zbd_info->zone_info[j];
		if (p->type == OFFLINE_ZONE_TYPE)
			p->wp = start_sector;
		else
			start_sector = p->start;
	}

	f->zbd_info = zbd_info;
	f->zbd_info->zone_size = zone_size;
	f->zbd_info->zone_size_log2 = is_power_of_2(zone_size) ?
		ilog2(zone_size) + 9 : -1;
	f->zbd_info->nr_zones = nr_zones;
	zbd_info = NULL;
	ret = 0;
check_ret:
	if (ret != 0) {
		// If we can't get get BLKREPORTZONE on a host managed drive,
		// this is an issue
		zbd_model = get_zbd_model(f->file_name);
		if (zbd_model == ZBD_DM_HOST_MANAGED)
			log_err("fio: read_zone_info (%lu) failed for %s (%d).\n",
				 start_sector, f->file_name, errno);
		else
		{
			dprint(FD_ZBD, "read_zone_info (%lu) failed for %s (%d).\n",
				start_sector, f->file_name, errno);
			ret = 0;
		}
	}
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

	if (td->o.zbd_ignore)
		return 0;
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
	assert(is_valid_offset(f, ((sector + nr_sectors) << 9) - 1, td, DDIR_WRITE));
	if (f->zbd_info->use_sg)
		ret = sg_reset_zones(f->fd, &zr, f->zbd_info->block_size,
			f->zbd_info->zone_size, f->zbd_info->use_sg == 2);
	else {
		ret = ioctl(f->fd, BLKRESETZONE, &zr);
		if (ret < 0) {
			bool use_scsi;
			dprint(FD_ZBD, "%s: resetting wp with ioctl at sector %llu for %llu "
				"sectors failed (%d), trying sg_driver instead\n",
				f->file_name, zr.nr_sectors, zr.sector, errno);
			ret = sg_get_protocol(f->fd, &use_scsi);
			if (ret != 0) {
				log_info("failed to issue inquiry with return %d\n", ret);
				return ret;
			}
			f->zbd_info->use_sg = use_scsi ? 2: 1;
		}
	}
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
		pthread_mutex_lock(&f->zbd_info->mutex);
		f->zbd_info->sectors_with_data -= z->wp - z->start;
		pthread_mutex_unlock(&f->zbd_info->mutex);
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

	dprint(FD_ZBD, "%s: checking for zones to reset\n", f->file_name);
	assert(f->fd != -1);
	for (z = zb; z < ze; z++) {
		pthread_mutex_lock(&z->mutex);
		if (wp_zone(z)) {
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
		}
		else if (start_z != ze) {
			dprint(FD_ZBD, "%s: resetting zones %lu .. %lu\n",
			       f->file_name, start_z - f->zbd_info->zone_info,
			       z - f->zbd_info->zone_info);
			if (zbd_reset_range(td, f, start_z->start,
					    z->start - start_z->start) < 0)
				res = 1;
			start_z = ze;
		}
	}
	if (start_z < ze) {
		dprint(FD_ZBD, "%s: resetting zones %lu .. %lu\n", f->file_name,
		       start_z - f->zbd_info->zone_info, z - f->zbd_info->zone_info);
		if (zbd_reset_range(td, f, start_z->start,
			z->start - start_z->start) < 0)
			res = 1;
	}
	for (z = zb; z < ze; z++)
		pthread_mutex_unlock(&z->mutex);

	return res;
}

/*
 * Reset zbd_info.write_cnt, the counter that counts down towards the next
 * zone reset.
 */
static void zbd_reset_write_cnt(const struct thread_data *td,
				const struct fio_file *f)
{
	assert(0 <= td->o.zrf.u.f && td->o.zrf.u.f <= 1);

	pthread_mutex_lock(&f->zbd_info->mutex);
	f->zbd_info->write_cnt = td->o.zrf.u.f ?
		min(1.0 / td->o.zrf.u.f, 0.0 + UINT_MAX) : UINT_MAX;
	pthread_mutex_unlock(&f->zbd_info->mutex);
}

static bool zbd_dec_and_reset_write_cnt(const struct thread_data *td,
					const struct fio_file *f)
{
	uint32_t write_cnt = 0;

	pthread_mutex_lock(&f->zbd_info->mutex);
	assert(f->zbd_info->write_cnt);
	if (f->zbd_info->write_cnt)
		write_cnt = --f->zbd_info->write_cnt;
	if (write_cnt == 0)
		zbd_reset_write_cnt(td, f);
	pthread_mutex_unlock(&f->zbd_info->mutex);

	return write_cnt == 0;
}

/* Check whether the value of zbd_info.sectors_with_data is correct. */
static void check_swd(const struct thread_data *td, const struct fio_file *f)
{
#if 0
	struct fio_zone_info *zb, *ze, *z;
	uint64_t swd;

	zb = &f->zbd_info->zone_info[zbd_zone_idx(f, f->file_offset)];
	ze = &f->zbd_info->zone_info[zbd_zone_idx(f, f->file_offset +
						  f->io_size)];
	swd = 0;
	for (z = zb; z < ze; z++) {
		pthread_mutex_lock(&z->mutex);
		swd += z->wp - z->start;
	}
	pthread_mutex_lock(&f->zbd_info->mutex);
	assert(f->zbd_info->sectors_with_data == swd);
	pthread_mutex_unlock(&f->zbd_info->mutex);
	for (z = zb; z < ze; z++)
		pthread_mutex_unlock(&z->mutex);
#endif
}

void zbd_file_reset(struct thread_data *td, struct fio_file *f)
{
	struct fio_zone_info *zb, *ze, *z;
	uint32_t zone_idx_e;
	uint64_t swd = 0;

	if (!f->zbd_info)
		return;

	zb = &f->zbd_info->zone_info[zbd_zone_idx(f, f->file_offset)];
	zone_idx_e = zbd_zone_idx(f, f->file_offset + f->io_size);
	ze = &f->zbd_info->zone_info[zone_idx_e];
	pthread_mutex_lock(&f->zbd_info->mutex);
	for (z = zb ; z < ze; z++) {
		pthread_mutex_lock(&z->mutex);
		swd += z->wp - z->start;
	}
	for (z = zb ; z < ze; z++)
		pthread_mutex_unlock(&z->mutex);
	f->zbd_info->sectors_with_data = swd;
	pthread_mutex_unlock(&f->zbd_info->mutex);

	/*
	 * If the write pointer is set to this impossible flag value, it means
	 * zbd_verify_sizes flagged the first zone to be reset, but couldn't
	 * reset it before the real file was opened, so we'll reset it now
	 */
	if (zb->wp == zb->start + f->zbd_info->zone_size + 1) {
		dprint(FD_ZBD, "%s: Resetting starting zone\n", f->file_name);
		zbd_reset_zone(td, f, zb);
	}

	/*
	 * If data verification is enabled reset the affected zones before
	 * writing any data to avoid that a zone reset has to be issued while
	 * writing data, which causes data loss.
	 */
	zbd_reset_zones(td, f, zb, ze, td->o.verify != VERIFY_NONE &&
			(td->o.td_ddir & TD_DDIR_WRITE) &&
			td->runstate != TD_VERIFYING);
	zbd_reset_write_cnt(td, f);

	/*
	 * Set the first write position to the write pointer in case the user
	 * specified to start writing at the write pointer in an open zone
	 * but we rounded the file offset to the start of the zone in
	 * zbd_verify_sizes
	 */

	if (wp_zone(zb) && ((zb->wp << 9) != f->last_pos[DDIR_WRITE]) &&
		(f->last_pos[DDIR_WRITE] < zb->start + f->zbd_info->zone_size)
		)
		f->last_pos[DDIR_WRITE] = zb->wp << 9;
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
	uint64_t next_offset;


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
		next_offset = z->start << 9;
		if (!is_valid_offset(f, next_offset, td, io_u->ddir)) {
			/* Wrap around */
			get_valid_offset(f, &next_offset, td, io_u->ddir, true);
			zone_idx = zbd_zone_idx(f, f->file_offset);
			z = &f->zbd_info->zone_info[zone_idx];
		}
		assert(is_valid_offset(f, z->start << 9, td, io_u->ddir));
		pthread_mutex_lock(&z->mutex);
		/*
		 * Skip full zones with data verification enabled because
		 * resetting a zone causes data loss and hence causes
		 * verification to fail.
		 */
		if (z->open || (td->o.verify != VERIFY_NONE &&
				zbd_zone_full(f, z)) ||
			!wp_zone(z))
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

	// if (z->verify_block * ba >= f->zbd_info->zone_size)
	// 	log_err("%s: %d * %d >= %ld\n", f->file_name, z->verify_block,
	// 		ba, f->zbd_info->zone_size);
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
	struct fio_zone_info* zf =
		&f->zbd_info->zone_info[zbd_zone_idx(f, f->file_offset)];
	uint64_t new_offset;

	/*
	 * Shouldn't call this for non random IO
	 */
	if(!td_random(td)) {
		dprint(FD_ZBD, "%s: issued zbd_find_zone on non-random IO, exiting\n",
				f->file_name);
	}

	/*
	 * Skip to the nearest non-empty zone in case of random I/O.
	 */
	for (z1 = zb + 1, z2 = zb - 1; z1 < zl || z2 >= zf; z1++, z2--) {
		// Move to the last offline zone (so that it increments
		// into the next online zone) which should be held in
		// the wp from when the zone table was initialized
		if (z1->type == OFFLINE_ZONE_TYPE) {
			// If the wp is 0, then there is no online zone after this
			if (z1->wp == 0)
				z1 = zl;
			else {
				z1 = &f->zbd_info->zone_info[zbd_zone_idx(f, z1->wp - 1)];
			}
		}
		if (!is_valid_offset(f, z1->start << 9, td, io_u->ddir))
		{
			new_offset = z1->start;
			get_valid_offset(f, &new_offset, td, io_u->ddir, true);
			// If we wrap, there are no valid offsets past this one,
			// so give up
			if (new_offset < z1->start)
				z1 = zl;
			else
				z1 = &f->zbd_info->zone_info[zbd_zone_idx(f, new_offset)];
		}
		if (z1 < zl) {
			assert(is_valid_zone_ptr(f, z1));
			pthread_mutex_lock(&z1->mutex);
			if (z1->start + (io_u->buflen >> 9) <= z1->wp)
				return z1;
			pthread_mutex_unlock(&z1->mutex);
		}
		if (!is_valid_offset(f, z2->start << 9, td, io_u->ddir))
		{
			new_offset = z2->start;
			get_valid_offset(f, &new_offset, td, io_u->ddir, false);
			// If we wrap, there are no valid offsets past this one,
			// so give up
			if (new_offset > z2->start)
			{
				z2 = zf;
				z2--;
			}
			else
				z2 = &f->zbd_info->zone_info[zbd_zone_idx(f, new_offset)];
		}
		if (z2 >= zf) {
			assert(is_valid_zone_ptr(f, z2));
			// No easy way to skip backwards, so just loop
			// through all the offline zones for now
			if (z2->type == OFFLINE_ZONE_TYPE) {
				continue;
			}
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
	if (!wp_zone(z))
		return;
	if (!success)
		goto unlock;
	switch (io_u->ddir) {
	case DDIR_WRITE:
		zone_end = min(end, (z + 1)->start);
		pthread_mutex_lock(&zbd_info->mutex);
		/*
		 * z->wp > zone_end means that one or more I/O errors
		 * have occurred.
		 */
		if (z->wp <= zone_end)
			zbd_info->sectors_with_data += zone_end - z->wp;
		pthread_mutex_unlock(&zbd_info->mutex);
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
	struct fio_file *f = io_u->file;
	uint32_t zone_idx_b;
	struct fio_zone_info *zb, *zl;
	uint32_t orig_len = io_u->buflen;
	uint32_t min_bs = td->o.min_bs[io_u->ddir];
	uint64_t new_len;
	int64_t range;

	if (!f->zbd_info)
		return io_u_accept;

	assert(is_valid_offset(f, io_u->offset, td, io_u->ddir));
	assert(io_u->buflen);
	zone_idx_b = zbd_zone_idx(f, io_u->offset);
	zb = &f->zbd_info->zone_info[zone_idx_b];

	if (zb->type == OFFLINE_ZONE_TYPE) {
		// Allow sequential jobs to skip this zone
		if (zb->wp == 0)
			f->last_pos[io_u->ddir] = f->file_offset;
		else
			f->last_pos[io_u->ddir] = zb->wp;
		return io_u_retry;
	}
	else if (!wp_zone(zb))
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
		/* Check whether the zone reset threshold has been exceeded */
		if (td->o.zrf.u.f && !td->o.skip_zone_resets) {
			check_swd(td, f);
			if ((f->zbd_info->sectors_with_data << 9) >=
				f->io_size * td->o.zrt.u.f &&
				zbd_dec_and_reset_write_cnt(td, f)) {
				dprint(FD_ZBD, "Reset threshold %f exceeded (reset frequency = %f)\n",
					td->o.zrt.u.f, td->o.zrf.u.f);
				zb->reset_zone = 1;
			}
		}

		/* If this is a filled FLEX zone, treat it like
		 * a conventional zone from here on
		 */
		if (zb->type == FLEX_ZONE_TYPE && zb->wp >= zb->start + f->zbd_info->zone_size) {
			zb->type = BLK_ZONE_TYPE_CONVENTIONAL;
			goto accept;
		}
		/* Reset the zone pointer if necessary */
		if (zb->reset_zone || zbd_zone_full(f, zb)) {
			assert(td->o.verify == VERIFY_NONE);
			if (td->o.skip_zone_resets) {
				if (zb) {
					// Allow sequential jobs to skip this zone
					f->last_pos[io_u->ddir] = zb->start + f->zbd_info->zone_size;
					pthread_mutex_unlock(&zb->mutex);
				}
				return io_u_retry;
			}
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
			check_swd(td, f);
		}
		/* Make writes occur at the write pointer */
		assert(!zbd_zone_full(f, zb));
		io_u->offset = zb->wp << 9;
		if (!is_valid_offset(f, io_u->offset, td, io_u->ddir)) {
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
