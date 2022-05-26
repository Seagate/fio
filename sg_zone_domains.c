#include <stdlib.h>

#include "sg_zone_domains.h"
#include "file.h"
#include "fio.h"
#include "log.h"
#include "smalloc.h"

#define INQ_CMD_CODE 0x12
#define INQ_LEN 6
#define RZ_CMD_CODE 0x4A
#define SCSI_RZ_CMD_CODE 0x95
#define REZ_CMD_CODE 0x9F
#define SCSI_REZ_CMD_CODE 0x94
#define RC16_CMD_CODE 0x9E
#define PT_PROTOCOL_DMA 0x0D    // DMA protocol and Extend bit
#define PT_PROTOCOL_ND 0x07 // Non-data and Extend bit
// 0 second timeout, TDIR_IN, BYT_BLOCK set, T_LENGTH set to 2 to use sector count
#define MISC_BYTE 0x0E
#define PT_CMD_CODE 0x85
#define PT_CMD_LEN 16
#define HDR_SIZE 64
#define ZONE_INFO_SIZE 64


/**
 * sg_send_cdb - send generic CDBs
 * @fd: file descriptor
 * @cdb_buf: command descriptor block buffer
 * @cdb_len: length of cdb buffer
 * @data_buf: buffer to hold outgoing or incoming data
 * @bufsz: size of data_buf
 * @io_hdr_pt: pointer to io_hdr. Can be set to NULL or checked
 *          after running command for various information
 */
int sg_send_cdb(int fd, unsigned char* cdb_buf, unsigned char cdb_len,
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
 * sg_reset_zones - reset all zones specified by zr parameter
 * @fd: file descriptor
 * @zr: start and number of zones to reset
 * @block_size: logical block size of device in bytes -- used to convert
 *              sectors from zr into LBAs
 * @zone_size: bytes per zone
 * @use_scsi: whether to use the SCSI or the ATA command
 */
int sg_reset_zones(int fd, struct blk_zone_range* zr,
        uint64_t zone_size, bool use_scsi) {
    uint8_t sub_cmd = 4;
    unsigned char rez_cmd_blk[PT_CMD_LEN];
    uint64_t cur_lba, last_lba;
    int ret = 0;

    cur_lba = zr->sector;
    last_lba = cur_lba + zr->nr_sectors;

    if (use_scsi) {
        dprint(FD_ZBD, "Entered SCSI portion of sg_reset_zones\n");
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
        dprint(FD_ZBD, "Entered SATA portion of sg_reset_zones\n");
        rez_cmd_blk[0] = PT_CMD_CODE;
        rez_cmd_blk[1] = PT_PROTOCOL_ND;
        // Non-data command doesn't need to use this byte
        rez_cmd_blk[2] = 0;
        // Features high used for resetting all zones
        rez_cmd_blk[3] = 0;
        // Features low used for sub command
        rez_cmd_blk[4] = sub_cmd;
        // This count field might be usable for multiple sectors, but can't rely on it
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
            dprint(FD_ZBD, "Resetting zone at LBA 0x%lX\n", cur_lba);
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
            dprint(FD_ZBD, "No further data to parse, exiting\n");
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
            dprint(FD_ZBD, "Encountered zero padded data after %d zones, exiting\n", num_zones);
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
 *              SCSI command might be usable for both, depending on sat4
 *              layer
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
 * sg_read_log_ext - send read log extended CDBs
 * @fd: file descriptor
 * @log_address: address of the log to fetch
 * @subpage: subpage to fetch (usually 0)
 * @ret_buf: buffer to store the output in
 * @buf_len: length of the buffer--this will
 *  control how many pages (512 blocks) are fetched as well
*/
static int sg_read_log_ext(int fd, uint16_t log_address, uint16_t subpage,
        unsigned char* ret_buf, int buf_len) {
    unsigned char rle_cmd_blk[16];
    uint16_t page_count = buf_len / 512;

    rle_cmd_blk[0] = 0x85;
    rle_cmd_blk[1] = 0x09;
    rle_cmd_blk[2] = 0x0E;
    // Features
    rle_cmd_blk[3] = 0x00;
    rle_cmd_blk[4] = 0x00;
    // Upper and lower page count
    rle_cmd_blk[5] = (page_count >> 8) & 0xFF;
    rle_cmd_blk[6] = page_count & 0xFF;
    // Reserved
    rle_cmd_blk[7] = 0x00;
    // Log address
    rle_cmd_blk[8] = 0x30;
    // Upper and lower page number
    rle_cmd_blk[9] = (subpage >> 8) & 0xFF;
    rle_cmd_blk[10] = subpage & 0xFF;
    // Reserved
    rle_cmd_blk[11] = 0x00;
    rle_cmd_blk[12] = 0x00;
    // Device byte
    rle_cmd_blk[13] = 0x00;
    // Read Log Extended op code
    rle_cmd_blk[14] = 0x2F;
    // Control byte
    rle_cmd_blk[15] = 0x00;

    return sg_send_cdb(fd, rle_cmd_blk, 16, ret_buf, 512, NULL);
}
int sg_get_flex_zd(int fd, bool* is_flex) {
    unsigned char ret_buf[512];
    int ret;

    // This may not succeed, but if it doesn't we want
    // to check zone domains anyway, so ignore
    // command failures here
    ret = sg_read_log_ext(fd, 0x30, 3, ret_buf, 512);
    if (ret == 0)
        *is_flex = (bool) (ret_buf[105] & 1);

    if (*is_flex) {
        return 0;
    }
    ret = sg_read_log_ext(fd, 0x30, 9, ret_buf, 512);
    if (ret) {
        return ret;
    }
    *is_flex = (bool) (ret_buf[56] & 1);
    return 0;
}


/*
 * Read zone information into @buf starting from sector @start_sector.
 * @fd is a file descriptor that refers to a block device and @bufsz is the
 * size of @buf.
 *
 * Returns 0 upon success and a negative error code upon failure.
 * If the zone report is empty, always assume an error (device problem) and
 * return -EIO.
 */
int sg_read_zone_info(int fd, uint64_t start_offset, int* use_sg_rz, uint32_t* block_size,
              struct blk_zone_report *hdr, unsigned int bufsz)
{
    void *buf = (void*) hdr;
    int ret = -1;
    uint64_t start_lba;
    int retry;
    bool use_scsi;
    // void* aligned_ptr;


    if (bufsz < sizeof(*hdr))
        return -ENOMEM;

    if (*block_size < 512) {
        ret = sg_read_capacity(fd, block_size);
        if (ret != 0) {
            log_info("failed to read capacity with return %d\n", ret);
            *block_size = 0;
            return ret;
        }
    }
    // Round the bufsz to an even multiple of the block size -- not sure if this is necessary or if
    // we can use 512 regardless of block size
    bufsz = (bufsz / *block_size) * (*block_size);
    start_lba = start_offset / *block_size;
    // Get whether the device is SAS or SATA
    if (*use_sg_rz == sg_zd_uninitialized) {
        ret = sg_get_protocol(fd, &use_scsi);
        if (ret != 0) {
            log_info("failed to issue inquiry with return %d\n", ret);
            return ret;
        }
        *use_sg_rz = use_scsi ? sg_zd_use_scsi: sg_zd_use_sata;
    } else
        use_scsi = *use_sg_rz == sg_zd_use_scsi;
    // aligned_ptr = PTR_ALIGN(buf, page_mask);
    // memset(aligned_ptr, 0x77, 16);
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
    return ret;
}
