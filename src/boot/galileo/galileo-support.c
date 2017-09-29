/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2017)                 */
/*                                                                             */
/*  This software is a computer program whose purpose is to run a minimal,     */
/*  hypervisor relying on proven properties such as memory isolation.          */
/*                                                                             */
/*  This software is governed by the CeCILL license under French law and       */
/*  abiding by the rules of distribution of free software.  You can  use,      */
/*  modify and/ or redistribute the software under the terms of the CeCILL     */
/*  license as circulated by CEA, CNRS and INRIA at the following URL          */
/*  "http://www.cecill.info".                                                  */
/*                                                                             */
/*  As a counterpart to the access to the source code and  rights to copy,     */
/*  modify and redistribute granted by the license, users are provided only    */
/*  with a limited warranty  and the software's author,  the holder of the     */
/*  economic rights,  and the successive licensors  have only  limited         */
/*  liability.                                                                 */
/*                                                                             */
/*  In this respect, the user's attention is drawn to the risks associated     */
/*  with loading,  using,  modifying and/or developing or reproducing the      */
/*  software by the user in light of its specific status of free software,     */
/*  that may mean  that it is complicated to manipulate,  and  that  also      */
/*  therefore means  that it is reserved for developers  and  experienced      */
/*  professionals having in-depth computer knowledge. Users are therefore      */
/*  encouraged to load and test the software's suitability as regards their    */
/*  requirements in conditions enabling the security of their systems and/or   */
/*  data to be ensured and,  more generally, to use and operate it in the      */
/*  same conditions as regards security.                                       */
/*                                                                             */
/*  The fact that you are presently reading this means that you have had       */
/*  knowledge of the CeCILL license and that you accept its terms.             */
/*******************************************************************************/

/**
 * \file mmu.c
 * \brief MMU early-boot configuration
 */
#include <stdint.h>
#include "debug.h"
#include <libc.h>
#include "galileo-support.h"
#include "port.h"

volatile uint16_t usIRQMask = 0xfffb;
volatile uint32_t UART_PCI_Base = 0UL;
volatile uint32_t UART_MMIO_Base = 0UL;


void initGalileoSerial(uint32_t portnumber)
{
    if(galileoSerialPortInitialized == 0){
        initGalileoUART(portnumber);
        galileoSerialPortInitialized = 1;
    }
}



void initGalileoUART(uint32_t portnumber)
 {
	volatile uint8_t divisor = 24;
	volatile uint8_t output_data = 0x3 & 0xFB & 0xF7;
	volatile uint8_t input_data = 0;
	volatile uint8_t lcr = 0;

	if (portnumber == DEBUG_SERIAL)
		UART_PCI_Base = MMIO_PCI_ADDRESS(0, 20, 5, 0);
	else
		UART_PCI_Base = MMIO_PCI_ADDRESS(0, 20, 1, 0);

	uint32_t base = MMIO_read(UART_PCI_Base, 0x10, 4);
	UART_MMIO_Base = base;

	MMIO_write(base, R_UART_SCR, 1, 0xAB);

	MMIO_write(base, R_UART_LCR, 1, output_data | B_UARY_LCR_DLAB);

	MMIO_write(base, R_UART_BAUD_HIGH, 1, (uint8_t)(divisor >> 8));
	MMIO_write(base, R_UART_BAUD_LOW, 1, (uint8_t)(divisor & 0xff));

	MMIO_write(base, R_UART_LCR, 1, output_data);

	MMIO_write(base, R_UART_FCR, 1, (uint8_t)(B_UARY_FCR_TRFIFIE |
		B_UARY_FCR_RESETRF | B_UARY_FCR_RESETTF | 0x30));

	input_data = MMIO_read(base, R_UART_MCR, 1);
	input_data |= BIT1;
	input_data &= ~BIT5;
	MMIO_write(base, R_UART_MCR, 1, input_data);

	lcr = MMIO_read(base, R_UART_LCR, 1);
	MMIO_write(base, R_UART_LCR, 1, (uint8_t) (lcr & ~B_UARY_LCR_DLAB));

	MMIO_write(base, R_UART_IER, 1, 0);
 }

 /*-----------------------------------------------------------------------
  * Serial port support functions
  *------------------------------------------------------------------------
  */
 void galileoSerialPrintc(char c)
 {
	if (galileoSerialPortInitialized)
	{
		while((MMIO_read(UART_MMIO_Base, R_UART_LSR, 1) & B_UART_LSR_TXRDY) == 0);
	 	MMIO_write(UART_MMIO_Base, R_UART_BAUD_THR, 1, c);
	}
 }
 /*-----------------------------------------------------------*/

 uint8_t galileoSerialGetc()
 {
	uint8_t c = 0;
	if (galileoSerialPortInitialized)
	{
		if((MMIO_read(UART_MMIO_Base, R_UART_LSR, 1) & B_UART_LSR_RXRDY) != 0)
		 	c  = MMIO_read(UART_MMIO_Base, R_UART_BAUD_THR, 1);
	}
	  return c;
 }
 /*-----------------------------------------------------------*/

 void galileoSerialPrints(const char *string)
 {
	if (galileoSerialPortInitialized)
	{
	    while(*string)
	    	galileoSerialPrintc(*string++);
	}


 }
 /*-----------------------------------------------------------*/
