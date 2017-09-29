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
