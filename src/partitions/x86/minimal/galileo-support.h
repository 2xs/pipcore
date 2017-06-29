



#ifndef __GALILEO_SUPPORT__
#define __GALILEO_SUPPORT__
#include "pip/io.h"

#define CLIENT_SERIAL_PORT 0
#define DEBUG_SERIAL_PORT 1


#ifndef NULL
	#define NULL (void *)0
#endif

#define configASSERT( x ) if( ( x ) == 0 ) for(;;);
#define configISR_STACK_SIZE					350
#define configCPU_CLOCK_HZ						( 400000000UL )
#define configTICK_RATE_HZ						( ( TickType_t ) 1000 )
#define portBYTE_ALIGNMENT_MASK ( 0x001f )



typedef uint32_t uintn_t;


void initializeGalileoUART(uint32_t portnumber);

void initGalileoSerialPort(uint32_t portnumber);




#ifndef TRUE
	#define TRUE ( 1 )
#endif

#ifndef FALSE
	#define FALSE ( 0 )
#endif

#ifndef true
	#define true  TRUE
#endif

#ifndef false
	#define false FALSE
#endif

#ifndef OK
	#define OK TRUE
#endif


//---------------------------------------------------------------------
// Serial port support definitions
//---------------------------------------------------------------------


#define CLIENT_SERIAL_PORT 				0
#define DEBUG_SERIAL_PORT 				1

#define R_UART_THR                      0
#define R_UART_IER                      0x04
#define R_UART_BAUD_THR                 R_UART_THR
#define R_UART_BAUD_LOW                 R_UART_BAUD_THR
#define R_UART_BAUD_HIGH                R_UART_IER
#define R_UART_FCR                      0x08
#define B_UARY_FCR_TRFIFIE              BIT0
#define B_UARY_FCR_RESETRF              BIT1
#define B_UARY_FCR_RESETTF              BIT2
#define R_UART_LCR                      0x0C
#define B_UARY_LCR_DLAB                 BIT7
#define R_UART_MCR                      0x10
#define R_UART_LSR                      0x14
#define B_UART_LSR_RXRDY                BIT0
#define B_UART_LSR_OE                   BIT1
#define B_UART_LSR_PE                   BIT2
#define B_UART_LSR_FE                   BIT3
#define B_UART_LSR_BI                   BIT4
#define B_UART_LSR_TXRDY                BIT5
#define B_UART_LSR_TEMT                 BIT6
#define R_UART_MSR                      0x18
#define R_UART_SCR                      0x1C


//---------------------------------------------------------------------
// General bit pattern definitions
//---------------------------------------------------------------------
#define BIT0  0x00000001U
#define BIT1  0x00000002U
#define BIT2  0x00000004U
#define BIT3  0x00000008U
#define BIT4  0x00000010U
#define BIT5  0x00000020U
#define BIT6  0x00000040U
#define BIT7  0x00000080U
#define BIT8  0x00000100U
#define BIT9  0x00000200U

//---------------------------------------------------------------------
// MMIO support definitions
//---------------------------------------------------------------------
#define EC_BASE			0xE0000000	/* Base of MMConfig space */
#define MMCONFIG_BASE	EC_BASE
#define MMIO_PCI_ADDRESS(bus,dev,fn,reg) ( \
        (EC_BASE) + \
		((bus) << 20) + \
		((dev) << 15) + \
		((fn)  << 12) + \
		(reg))

//---------------------------------------------------------------------
// MMIO read/write/set/clear/modify macros
//---------------------------------------------------------------------
#define mem_read(base, offset, size)({\
        volatile uint64_t r;\
        r = mmioRead(base,offset,size);\
        r;\
        })
// No cache bypass necessary -- MTRRs should handle this
#define mem_write(base, offset, size, value) mmioWrite(base,offset,size,value);

#define mem_set(base, offset, size, smask) mmioSet(base,offset,size,smask);
#define mem_clear(base, offset, size, cmask) mmioClear(base,offset,size,cmask);
#define mem_modify(base, offset, size, cmask, smask) mmioModify(base,offset,size,cmask,smask);

//---------------------------------------------------------------------
// 82C54 PIT (programmable interval timer) definitions
//---------------------------------------------------------------------
#define GATE_CONTROL	0x61
#define CHANNEL2_DATA	0x42
#define	MODE_REGISTER	0x43
#define ONESHOT_MODE	0xB2
#define	CLKBASE			0x40
#define	CLKCNTL			MODE_REGISTER


void vGalileoPrintc(char c);
uint8_t ucGalileoGetchar();
void vGalileoPuts(const char *string);
void initializeGalileoPort(uint32_t portnumber);
void initializeGalileoUART(uint32_t portnumber);



#endif
