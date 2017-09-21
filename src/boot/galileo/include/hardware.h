#ifndef __HARDWARE__
#define __HARDWARE__


typedef signed char int8_t;
typedef unsigned char uint8_t;
typedef signed short int16_t;
typedef unsigned short uint16_t;
//typedef signed long int32_t;
//typedef unsigned long uint32_t;


typedef signed long long int64_t;
typedef unsigned long long uint64_t;
typedef uint32_t uintn_t;

#define USHRT_MAX	((uint16_t)(~0U))



void calibrateLVTimer( void );
void setupHardware();


#endif
