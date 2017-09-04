#ifndef __HDEF__
#define __HDEF__

#include <stdint.h>
#include "ial.h"

#define HSPEC_COUNT 1

struct hardware_def pshw[HSPEC_COUNT] = {
    { "VGAController", 0xb8000, 0xc00b8000, 0x8000 }, 
}; 

#endif
