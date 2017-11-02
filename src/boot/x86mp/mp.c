#include "mp.h"
#include "rsdp.h"
#include "libc.h"
#include <stdint.h>

#include "debug.h"

struct RSDPDescriptor *rsdp = 0x0;

#define RSDP_OFFSET     16

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

void init_mp()
{
    /* Find RSDP (Root System Description Pointer) */
    find_rsdp();
}
