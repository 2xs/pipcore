#include <stdint.h>
#include "cmos.h"
#include "port.h"

void write_cmos(uint32_t reg, uint8_t data)
{
    /* Select CMOS register disabling NMI */
    outb(CMOS_REG, (1 << 7) | reg);

    /* Write value */
    outb(CMOS_DATA, data);
}

uint8_t read_cmos(uint32_t reg)
{
    /* Select CMOS register disabling NMI */
    outb(CMOS_REG, (1 << 7) | reg);

    /* Read and return value */
    return inb(CMOS_DATA);
}

uint32_t read_msr_low(uint32_t msr)
{
    uint32_t edx, eax;
    __asm volatile("MOV %1, %%ECX; \
                    RDMSR; \
                    MOV %%EAX, %0"
                    : "=r"(eax)
                    : "r" (msr)
                    : "eax", "ecx");
    return eax;
}
