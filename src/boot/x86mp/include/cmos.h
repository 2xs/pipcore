#ifndef __CMOS__
#define __CMOS__

#define CMOS_REG    0x70
#define CMOS_DATA   0x71

void write_cmos(uint32_t reg, uint8_t data);
uint8_t read_cmos(uint32_t reg);
uint32_t read_msr_low(uint32_t msr);
void delay(uint32_t ms);

#endif
