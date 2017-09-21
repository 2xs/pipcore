#include <stdint.h>
#include <pip/fpinfo.h>
#include <pip/api.h>
#include <pip/vidt.h>
#include "galileo-support.h"

/**
 * Page fault irq handler
 */
INTERRUPT_HANDLER(pfAsm, pfHandler)
	vcli();
	vGalileoPuts("Page Fault\r\n");
	for(;;);
END_OF_INTERRUPT

/**
 * General protection failure irq handler
 */
INTERRUPT_HANDLER(gpfAsm, gpfHandler)
	vGalileoPuts("GPF\r\n");
	for(;;);
END_OF_INTERRUPT

INTERRUPT_HANDLER(timerAsm, timerHandler)
	vGalileoPuts("Timer interrupts... Continue \r\n");
	vsti();
END_OF_INTERRUPT

/*
 * Prepares the fake interrupt vector to receive new interrupts
 */
void initInterrupts()
{
	registerInterrupt(33, &timerAsm, (uint32_t*)0x2020000); /* We can use the same stack for both interrupts, or choose different stacks, let's play a bit */
	registerInterrupt(14, &gpfAsm, (uint32_t*)0x2030000); /* General Protection Fault */
	registerInterrupt(15, &pfAsm, (uint32_t*)0x2040000); /* Page Fault */
	return;
}

void main(pip_fpinfo* bootinfo)
{

	initGalileoSerialPort(DEBUG_SERIAL_PORT);
	initInterrupts();
	vGalileoPuts("Hello from Userland\r\n");
	vsti();
   	for(;;);
}
