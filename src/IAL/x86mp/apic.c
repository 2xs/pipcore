#include <stdint.h>

#include "lapic.h"
#include "ial.h"
#include "mal.h"

extern uint32_t *lapic_base;
extern uint32_t mmuEnabled;

/* Write a value to LAPIC, disabling MMU during the operation if required */
void write_lapic(uint32_t reg, uint32_t value)
{
    if(mmuEnabled) disable_paging();    
    *(uint32_t*)(((uint32_t)lapic_base) + reg) = value;
    if(mmuEnabled) enable_paging();
}

/* Reads a value to LAPIC, disabling MMU during the operation if required */
uint32_t read_lapic(uint32_t reg)
{
    uint32_t ret;
    if(mmuEnabled) disable_paging();
    ret = *(uint32_t*)((uint32_t)lapic_base + reg);
    if(mmuEnabled) enable_paging();

    return ret;
}
