#include "mp.h"
#include "rsdp.h"
#include "rsdt.h"
#include "libc.h"
#include "mptables.h"
#include <stdint.h>

#include "debug.h"

struct RSDPDescriptor   *rsdp     = 0x0;
struct ACPISDTHeader    *rsdtTbl   = 0x0;
struct ACPISDTHeader    *madt = 0x0;
#define RSDP_OFFSET     16

struct mp_floating_pointer_structure *mpt = 0x0;
struct mp_configuration_table *mpconf = 0x0;

uint32_t* io_apic = 0x0;

void find_mpt()
{
    static const char mpt_sig[4] = "_MP_"; /* MP table signature to find */
    uintptr_t* ebda = (uintptr_t*)0x000E0000; /* Extended BIOS Data Area */
    size_t offset;
    for(offset = 0x0; ((offset + sizeof(uintptr_t)) < 0x20000); offset += RSDP_OFFSET)
    {
        mpt = (struct mp_floating_pointer_structure*)((uint32_t)ebda + offset);
        if(memcmp(mpt->signature, mpt_sig, sizeof(mpt_sig)) == 0x0)
        {
            DEBUG(CRITICAL, "Found MP table descriptor at %x!\n", mpt);
            mpconf = (struct mp_configuration_table*)mpt->configuration_table;
            return;
        }
    }
    
    DEBUG(CRITICAL, "Couldn't find MP Table. MP is unavailable. Please use x86_multiboot instead.\n");
    for(;;);
}

void parse_mpconf()
{
    static const char mpc_sig[4] = "PCMP";
    if(memcmp(mpconf->signature, mpc_sig, sizeof(mpc_sig)) != 0x0)
    {
        DEBUG(CRITICAL, "Invalid MP configuration table signature. This shouldn't happen...\n");
        for(;;);
    } else {
        DEBUG(CRITICAL, "MP configuration table signature is valid. Continuing.\n");
        DEBUG(CRITICAL, "%d entries found in MP configuration table.\n", mpconf->entry_count);

        struct entry_processor* entry = (struct entry_processor*)((uint32_t)mpconf + sizeof(struct mp_configuration_table));

        for(int i = 0; i < mpconf->entry_count; i++)
        {
            // DEBUG(CRITICAL, "Parsing entry at %x.\n", entry);
            if(entry->type == 0x0)
            {
                // DEBUG(CRITICAL, "Found a processor entry at %d.\n", i);
                DEBUG(CRITICAL, "CPU%d: LocalAPIC ID : %x, LocalAPIC Version : %x, Flags : %x (%s)\n", entry->local_apic_id, entry->local_apic_id, entry->local_apic_version, entry->flags, entry->flags & 0x2 ? "BP" :  "AP");
                entry = (struct entry_processor*)((uint32_t)entry + 20);
            } else {
                if(entry->type == 0x2)
                {
                    struct entry_io_apic* apic = (struct entry_io_apic*)entry;
                    DEBUG(CRITICAL, "Found IO APIC, address %x, flags %x\n", apic->address, apic->flags);
                } else {
                    // DEBUG(CRITICAL, "Ignoring entry type %d.\n", entry->type);
                }
                entry = (struct entry_processor*)((uint32_t)entry + 8);
            }
        }
    }
}

void find_rsdp()
{
    static const char rsdp_sig[8] = "RSD PTR "; /* RSDP signature to find */
    uintptr_t* ebda = (uintptr_t*)0x000E0000; /* Extended BIOS Data Area */
    size_t offset;
    for(offset = 0x0; ((offset + sizeof(uintptr_t)) < 0x20000); offset += RSDP_OFFSET)
    {
        rsdp = (struct RSDPDescriptor*)((uint32_t)ebda + offset);
        if(memcmp(rsdp->signature, rsdp_sig, sizeof(rsdp_sig)) == 0x0)
        {
            DEBUG(CRITICAL, "Found RSDP descriptor at %x!\n", rsdp);
            return;
        }
    }
    
    DEBUG(CRITICAL, "Couldn't find RSDP descriptor. MP is unavailable. Please use x86_multiboot instead.\n");
    for(;;);
}

void dump_rsdp()
{
    if(rsdp->revision == 0x0)
    {
        DEBUG(CRITICAL, "ACPI version 1.0.\n");
    } else {
        DEBUG(CRITICAL, "ACPI version 2.0 to 6.1.\n");
    }

    DEBUG(CRITICAL, "RSDT address at %x.\n", rsdp->rsdtAddress);
    rsdtTbl = (struct ACPISDTHeader*)rsdp->rsdtAddress;
}

uint8_t parse_rsdt()
{
    struct RSDT *rsdt = (struct RSDT*)rsdtTbl;
    struct ACPISDTHeader* h = (struct ACPISDTHeader*)rsdtTbl;
    int entries = (rsdtTbl->length - sizeof(struct ACPISDTHeader)) / 4;
    
    DEBUG(CRITICAL, "%d System Description Tables present.\n", entries);
    /* Parse each RSDT table */
    for(int i = 0; i < entries; i++)
    {
        DEBUG(CRITICAL, "Found RSDT table at %x : %c%c%c%c\n", h, h->signature[0], h->signature[1], h->signature[2], h->signature[3]);
        h = (struct ACPISDTHeader*)(rsdt->tables + i * sizeof(uint32_t));
        if(strncmp(h->signature, "MADT", 4) == 0x0) {
            DEBUG(CRITICAL, "Found MADT.\n");
            madt = h;
            return 1;
        }
    }
    DEBUG(CRITICAL, "Couldn't find MADT.\n");
    return 0;
}

void init_mp()
{
    /* Find RSDP (Root System Description Pointer) */
    find_rsdp();

    /* Dump some info about RSDP */
    dump_rsdp();

    /* Find ACPI table in RSDT */
    if(parse_rsdt())
    {
        /* Initialize through MADT */
    } else {
        /* Fallback : initialize through MP Table */
        DEBUG(CRITICAL, "Couldn't initialize SMP through RSDT. Using MP tables.\n");
        find_mpt();
        parse_mpconf();
    }
}
