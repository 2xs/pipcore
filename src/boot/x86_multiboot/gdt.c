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
 * \file gdt.c
 * \brief GDT configuration
 */
#include "gdt.h"
#include "libc.h"
#include "debug.h"

struct tss_descriptor tss; //!< Generic TSS for userland-to-kernel switch
extern void tssFlush(); //!< ASM method to flush the TSS entry

extern void *cg_outbGlue;
extern void *cg_inbGlue;
extern void *cg_outwGlue;
extern void *cg_inwGlue;
extern void *cg_outlGlue;
extern void *cg_inlGlue;
extern void *cg_outaddrlGlue;
extern void *cg_createPartition;
extern void *cg_countToMap;
extern void *cg_prepare;
extern void *cg_addVAddr;
extern void *cg_dispatchGlue;
extern void *cg_timerGlue;
extern void *cg_resume;
extern void *cg_removeVAddr;
extern void *cg_mappedInChild;
extern void *cg_deletePartition;
extern void *cg_collect;
extern void *cg_yieldGlue;

/**
 * \struct gdt_entry_s
 * \brief Global Descriptor Table callgate entry structure
 */
struct gdt_entry_s {
	void *handler;
	unsigned nargs;
	unsigned rpl;
	unsigned segment;
};

struct gdt_entry_s gdtEntries[] = {
	{&cg_outbGlue, 		2, 0x3, 0x08}, /* 0x30 */
	{&cg_inbGlue, 		1, 0x3, 0x08}, /* 0x38 */
	{&cg_outwGlue, 		2, 0x3, 0x08}, /* 0x40 */
	{&cg_inwGlue, 		1, 0x3, 0x08}, /* 0x48 */
	{&cg_outlGlue, 		2, 0x3, 0x08}, /* 0x50 */
	{&cg_inlGlue, 		1, 0x3, 0x08}, /* 0x58 */

	{&cg_createPartition, 	5, 0x3, 0x08}, /* 0x60 */
	{&cg_countToMap, 	2, 0x3, 0x08}, /* 0x68 */
	{&cg_prepare, 		4, 0x3, 0x08}, /* 0x70 */
	{&cg_addVAddr, 		6, 0x3, 0x08}, /* 0x78 */
	{&cg_dispatchGlue, 	5, 0x3, 0x08}, /* 0x80 */

	{&cg_outaddrlGlue, 	2, 0x3, 0x08}, /* 0x88 */
	{&cg_timerGlue, 	0, 0x3, 0x08}, /* 0x90 */
	{&cg_resume, 		2, 0x3, 0x08}, /* 0x98 */
	{&cg_removeVAddr, 	2, 0x3, 0x08}, /* 0xA0 */
	{&cg_mappedInChild,	1, 0x3, 0x08}, /* 0xA8 */
	{&cg_deletePartition,	1, 0x3, 0x08}, /* 0xB0 */
	{&cg_collect,		1, 0x3, 0x08}, /* 0xB8 */
	{&cg_yieldGlue,		5, 0x3, 0x08}, /* 0xC0 */
};

#define CG_COUNT (sizeof(gdtEntries)/sizeof(struct gdt_entry_s))

#define gdtEntriesCount (6 + CG_COUNT)

gdt_entry_t gdt[gdtEntriesCount]; //!< Our GDT
struct gdt_ptr gp; //!< Pointer to our GDT

/**
 * \fn void gdtSetGate(int num, unsigned long base, unsigned long limit, unsigned char access, unsigned char gran)
 * \brief Installs a segment selector into the GDT
 * \param num The index of the segment into the GDT
 * \param base The base address for the segment
 * \param limit The maximal value of an address, given this segment is selected
 * \param access Access byte for this segment
 * \param gran Granularity. I never understood what this is supposed to mean. TODO: find out.
 */
void gdtSetGate(int num, unsigned long base, unsigned long limit, unsigned char access, unsigned char gran)
{
    gdt[num].segment.present = 0;
    gdt[num].segment.base_low = (base & 0xFFFF);
    gdt[num].segment.base_middle = (base >> 16) & 0xFF;
    gdt[num].segment.base_high = (base >> 24) & 0xFF;

    gdt[num].segment.limit_low = (limit & 0xFFFF);
    gdt[num].segment.granularity = ((limit >> 16) & 0x0F);

    gdt[num].segment.granularity |= (gran & 0xF0);
    gdt[num].segment.access = access;
    gdt[num].segment.present = 1;
}

/**
 * \fn void buildCallgate(int num, void* handler, uint8_t args, uint8_t rpl, uint16_t segment)
 * \brief Installs a call gate entry into the GDT
 * \param num The index of the segment into the GDT
 * \param handler The function pointer
 * \param args Argument count
 * \param rpl Requested Privilege Level
 * \param segment The segment to switch to
 */
void buildCallgate(int num, void* handler, uint8_t args, uint8_t rpl, uint16_t segment)
{
	gdt[num].callgate.present = 0; /* Make sure the entry is not valid until the end */
	gdt[num].callgate.dpl = rpl; /* Caller ring privilege level */
	gdt[num].callgate.zero = 0;
	gdt[num].callgate.type = 0xC; /* Call-gate type */
	gdt[num].callgate.selector = segment; /* Segment selector for ring-level 1 */
	gdt[num].callgate.reserved = 0;
	gdt[num].callgate.args = args;
	uint32_t addr = (uint32_t)(handler);
	gdt[num].callgate.offset_low = (uint16_t)(addr & 0xFFFF);
	gdt[num].callgate.offset_high = (uint16_t)((addr >> 16) & 0xFFFF);
	gdt[num].callgate.present = 1; /* Validate callgate entry */
	return;
}

/**
 * \fn void writeTss(int32_t num, uint16_t ss0, uint32_t esp0)
 * \brief Writes the TSS entry into the given GDT segment
 * \param num The GDT entry
 * \param ss0 The stack selector for kernel mode
 * \param esp0 The stack pointer for kernel mode
 */
void writeTss(int32_t num, uint16_t ss0, uint32_t esp0)
{
	uint32_t base = (uint32_t) &tss;
	uint32_t limit = sizeof(tss);

	gdtSetGate(num, base, limit, 0xE9, 0x00);

	memset(&tss, 0, sizeof(tss));

	tss.ss0 = ss0;
	tss.esp0 = esp0;

	tss.cs = 0x0B;
	tss.ss = tss.ds = tss.es = tss.fs = tss.gs = 0x13;
}

/**
 * \fn void setKernelStack (uint32_t stack)
 * \brief Updates the kernel stack address into the TSS
 * \param stack The stack address
 */
void setKernelStack (uint32_t stack)
{
	tss.esp0 = stack;
}

/**
 * \fn void gdtInstall()
 * \brief Installs the GDT into the CPU
 */
void gdtInstall(void)
{
	unsigned i;
	struct gdt_entry_s *e;

	gp.limit = (sizeof(gdt_entry_t) * (gdtEntriesCount)) - 1;
	gp.base = (uint32_t)&gdt;

	gdtSetGate(0, 0, 0, 0, 0);

	/* segment selectors */
	/* User code segment  */
	gdtSetGate(1, 0, 0xFFFFF, 0x9A, 0xC0);
	/* User data segment  */
	gdtSetGate(2, 0, 0xFFFFF, 0x92, 0xC0);
	/* Kernel code segment */
	gdtSetGate(3, 0, 0xFFFFF, 0xFA, 0xC0);
	/* Kernel data segment */
	gdtSetGate(4, 0, 0xFFFFF, 0xF2, 0xC0);

	writeTss(5, 0x10, 0x0);
	for (i=0;i<CG_COUNT; i++)
	{
		e = &gdtEntries[i];
		buildCallgate(6+i, e->handler, e->nargs, e->rpl, e->segment);
	}
	
	DEBUG(INFO, "Callgate set-up\n");

	gdtFlush();
	tssFlush();
}

