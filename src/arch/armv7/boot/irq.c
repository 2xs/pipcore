/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2021)                */
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

#include "debug.h"
#include "periph.h"

/* See QA7_rev3.4.pdf */

#define CPU_FREQ 900000000
#define TIMER_HZ 160
#define TIMER_RELOAD (CPU_FREQ / TIMER_HZ)

/* Defines for bcm2836  */
#define LOCAL_TIMER_INT_EN       (1<<29)
#define LOCAL_TIMER_EN           (1<<28)
#define	LOCAL_TIMER_RELOAD_MASK  ((1<<28)-1)

void irq_init_2836(void)
{
	int i;
	DEBUG(ERROR, "%s: %p\n", __FUNCTION__, PERIPH_CONTROL);

	/* 4.2 Control register:
	 * source = ABP clock ( clocked at half the ARM clock)
	 * increment = 2 */
	IRQ2836REG(CONTROL) = 3<<8;
	/* Set the prescaler 1/1. (timer_freq = (2^31/prescaler)*source_freq)*/
	IRQ2836REG(TIMER_PRESCALER) = 1<<31;

	/* 4.4 GPU interrupts routing: route all to core 0 */
	IRQ2836REG(GPU_ROUTING) = 0;

	/* 4.5 Performance monitors: disabled */
	IRQ2836REG(PMU_ROUTING_CLR) = 0xf;

	/* 4.6 Core timer interrupts: Enable all timer IRQs */
	IRQ2836REG(TIMER_CTL) = 0xf;

	/* 4.7 Core mailbox interrupts: FIXME Disable all */
	IRQ2836REG(MAILBOX_CTL) = 0;

	/* 4.9 Axi outstanding: Disable irq */
	IRQ2836REG(AXI_OUTSTD_CTL) = 0;

	/* 4.10 Core interrupt sources: Enable all on core 0, disable others */
	IRQ2836REG(IRQ_SOURCE) = 0xffffffff;
	DEBUG(ERROR, "irq_source read: %08x\n", IRQ2836REG(IRQ_SOURCE));
	for (i=1;i<4;i++)
		IRQ2836REG(IRQ_SOURCE+4*i) = 0;

	/* 4.11 Local timer: give timer to core 0 */
	IRQ2836REG(LOCAL_INT_ROUTING) = 0;
	IRQ2836REG(LOCAL_TIMER_CTL) = LOCAL_TIMER_INT_EN | LOCAL_TIMER_EN | TIMER_RELOAD;
	IRQ2836REG(LOCAL_TIMER_CLR_RLD) = 3<<30;
}

void irq_init(void)
{
	irq_init_2836();
}
