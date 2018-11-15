#ifndef __RSDT__
#define __RSDT__

#include <stdint.h>

struct ACPISDTHeader {
    char signature[4];
    uint32_t length;
    uint8_t revision;
    uint8_t checksum;
    char oemID[6];
    char oemTableID[8];
    uint32_t oemRevision;
    uint32_t creatorId;
    uint32_t creatorRevision;
} __attribute__ ((packed));

struct RSDT {
    struct ACPISDTHeader h;
    uint32_t *tables; /* Fixed amount of pointers to tables */
};

#endif
