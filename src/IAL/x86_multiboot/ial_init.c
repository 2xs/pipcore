/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2018)                 */
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
 * \file ial_init.c
 * \brief x86 interrupt abstraction layer initialization.
 */

#include "debug.h"
#include "port.h"
#include "pic8259.h"
#include "fpinfo.h"
#include "ial_defines.h"
#include "x86int.h"
#include "ial.h"
#include "libc.h"
#include "idt.h"

uint32_t timer_ticks = 0;


uint32_t pcid_enabled = 0;

/**
 * \fn remapIrq
 * \brief Remaps IRQ from int. 0-15 to int. 33-48
 */
void
remapIrq (void)
{
#define PIC1_OFFSET	0x20
#define PIC2_OFFSET	0x28
	
#ifdef KEEP_PIC_MASK
	uint8_t a1, a2;
	/* save masks */
	a1 = inb (PIC1_DATA);
	a2 = inb (PIC2_DATA);
#endif
	
	/* starts the initialization sequence (in cascade mode) */
	outb (PIC1_COMMAND, ICW1_INIT | ICW1_ICW4);
	outb (PIC2_COMMAND, ICW1_INIT | ICW1_ICW4);
	outb (PIC1_DATA, PIC1_OFFSET);
	outb (PIC2_DATA, PIC2_OFFSET);
	outb (PIC1_DATA, 0x04);	/* there is a slave PIC at IRQ2 */
	outb (PIC2_DATA, 0x02);	/* Slave PIC its cascade identity */
	outb (PIC1_DATA, ICW4_8086);
	outb (PIC2_DATA, ICW4_8086);
	
	/* masks */
#ifdef KEEP_PIC_MASK
	outb (PIC1_DATA, a1);
	outb (PIC2_DATA, a2);
#else
	outb (PIC1_DATA, 0);
	outb (PIC2_DATA, 0);
#endif
}

/**
 * \fn timerPhase
 * \brief Set timer frequency
 * \param Frequency to set
 *
 */
void
timerPhase (uint32_t hz)
{
	//  int divisor = 1193180 / hz;	/* Calculate our divisor */
	uint32_t divisor = 2600000 / hz;
	if (divisor > 0xffff) divisor = 0xffff;
	if (divisor < 1) divisor = 1;
	
	outb (0x43, 0x36);			/* Set our command byte 0x36 */
	outb (0x40, divisor & 0xFF);	/* Set low byte of divisor */
	outb (0x40, divisor >> 8);	/* Set high byte of divisor */
	
	IAL_DEBUG (INFO, "Timer phase changed to %d hz\n", hz);
}

/**
 * \fn void initCpu()
 * \brief Initializes CPU-specific features
 */
void initCpu()
{
	IAL_DEBUG(CRITICAL, "Identifying CPU model and features...\n");
	
	/* Display CPU vendor string */
	uint32_t cpu_string[4];
	cpuid_string(CPUID_GETVENDORSTRING, cpu_string); /* Vendor string will be 12 characters in EBX, EDX, ECX */
	char cpuident[17];
	char cpubrand[49];
	
	/* Build string */
	memcpy(cpuident, &(cpu_string[1]), 4 * sizeof(char));
	memcpy(&(cpuident[4]), &(cpu_string[3]), 4 * sizeof(char));
	memcpy(&(cpuident[8]), &(cpu_string[2]), 4 * sizeof(char));
	cpuident[12] = '\0';
	
	IAL_DEBUG(CRITICAL, "CPU identification: %s\n", cpuident);
	
	/* Processor brand */
	cpuid_string(CPUID_INTELBRANDSTRING, (uint32_t*)cpubrand);
	cpuid_string(CPUID_INTELBRANDSTRINGMORE, (uint32_t*)&cpubrand[16]);
	cpuid_string(CPUID_INTELBRANDSTRINGEND, (uint32_t*)&cpubrand[32]);
	cpubrand[48] = '\n';
	IAL_DEBUG(CRITICAL, "CPU brand: %s\n", cpubrand);
	
	/* Check whether PCID is supported as well as PGE */
	uint32_t ecx, edx;
	cpuid(CPUID_GETFEATURES, &ecx, &edx);
	uint32_t cr4;
	
	/* PGE check */
	if(edx & CPUID_FEAT_EDX_PGE)
	{
		IAL_DEBUG(CRITICAL, "PGE supported, enabling CR4.PGE\n");
		__asm volatile("MOV %%CR4, %0" : "=r"(cr4));
		cr4 |= (1 << 7); /* Enable Page Global as well */
		__asm volatile("MOV %0, %%CR4" :: "r"(cr4));
	} else {
		IAL_DEBUG(CRITICAL, "PGE unsupported, Global Page feature will be unavailable\n");
	}
	
	/* PCID check */
	if(ecx & CPUID_FEAT_ECX_PCID)
	{
		IAL_DEBUG(CRITICAL, "PCID supported, enabling CR4.PCIDE\n");
		pcid_enabled = 1;
		
		/* Enable PCID */
		__asm volatile("MOV %%CR4, %0" : "=r"(cr4));
		cr4 |= (1 << 17);
		__asm volatile("MOV %0, %%CR4" :: "r"(cr4));
	} else {
		IAL_DEBUG(CRITICAL, "PCID unsupported, Process Context Identifiers feature will be unavailable\n");
	}
}

extern void initIDT();

/**
 * \fn initInterrupts
 * \brief Initializes the IAL
 */
void
initInterrupts (void)
{
	IAL_DEBUG (INFO, "Initializing interrupts, IAL %s \"On Steroids\" version %s\n", IAL_PREFIX, IAL_VERSION);
	initIDT();
	remapIrq ();
	timerPhase (100);
	timer_ticks = 0;
	initCpu();
	IAL_DEBUG (INFO, "Init CPU done.\n");
	asm("int $0x1");
	IAL_DEBUG(INFO, "Returned from interrupt 0x1\n");
}

