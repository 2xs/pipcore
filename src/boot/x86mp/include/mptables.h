#ifndef __MPTABLES__
#define __MPTABLES__

#include <stdint.h>

struct mp_floating_pointer_structure {
    char signature[4];
    uint32_t configuration_table;
    uint8_t length; 
    uint8_t mp_specification_revision;
    uint8_t checksum; 
    uint8_t default_configuration; 
    uint32_t features; 
} __attribute__ ((packed));

struct mp_configuration_table {
    char signature[4]; // "PCMP"
    uint16_t length;
    uint8_t mp_specification_revision;
    uint8_t checksum; 
    char oem_id[8];
    char product_id[12];
    uint32_t oem_table;
    uint16_t oem_table_size;
    uint16_t entry_count; 
    uint32_t lapic_address; 
    uint16_t extended_table_length;
    uint8_t extended_table_checksum;
    uint8_t reserved;
} __attribute__ ((packed));

struct entry_processor {
    uint8_t type; // Always 0
    uint8_t local_apic_id;
    uint8_t local_apic_version;
    uint8_t flags; // If bit 0 is clear then the processor must be ignored
                   // If bit 1 is set then the processor is the bootstrap processor
    uint32_t signature;
    uint32_t feature_flags;
    uint64_t reserved;
} __attribute__ ((packed));

struct entry_io_apic {
    uint8_t type; // Always 2
    uint8_t id;
    uint8_t version;
    uint8_t flags; // If bit 0 is set then the entry should be ignored
    uint32_t address; // The memory mapped address of the IO APIC is memory
} __attribute__ ((packed));

#endif
