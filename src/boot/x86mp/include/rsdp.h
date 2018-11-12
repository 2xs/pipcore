#ifndef __RSDP__
#define __RSDP__

#include <stdint.h>

/* ACPI 1.0 RSDP Descriptor */
struct RSDPDescriptor {
    char signature[8];
    uint8_t checksum;
    char oemID[6];
    uint8_t revision;
    uint32_t rsdtAddress;
} __attribute__ ((packed));

/* RSDP descriptor since ACPI 2.0 */
struct RSDPDescriptorACPI2 {
    struct RSDPDescriptor desc;
    uint32_t length;
    uint32_t xsdtAddress;
    uint8_t extendedChecksum;
    uint8_t reserved[3];
} __attribute__ ((packed));

#endif
