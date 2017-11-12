#include <stdint.h>

#include "lapic.h"
#include "ial.h"

extern uint32_t *lapic_base;

void write_lapic(uint32_t reg, uint32_t value)
{
    *(uint32_t*)(((uint32_t)lapic_base) + reg) = value;
}

uint32_t read_lapic(uint32_t reg)
{
    return *(uint32_t*)((uint32_t)lapic_base + reg);
}
