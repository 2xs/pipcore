#ifndef __MP__
#define __MP__

#include <stdint.h>

/* Multiprocessor extensions for Pip */
void init_mp();
void boot_core();

uint8_t hasBooted(uint32_t n);
void setBooted(uint32_t n);

uint32_t coreId();
uint32_t coreCount();

#endif
