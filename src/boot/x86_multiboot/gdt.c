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

/* FIXME FIXME */
#define USER_RING   0b11
#define KERNEL_RING 0b00

tss_segment_t tss; //!< Generic TSS for userland-to-kernel switch
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
struct gdt_callgate_entry_s {
	void *handler;
	unsigned nargs;
};

struct gdt_callgate_entry_s callgateEntries[] = {
	{&cg_outbGlue, 		2}, /* 0x30 */
	{&cg_inbGlue, 		1}, /* 0x38 */
	{&cg_outwGlue, 		2}, /* 0x40 */
	{&cg_inwGlue, 		1}, /* 0x48 */
	{&cg_outlGlue, 		2}, /* 0x50 */
	{&cg_inlGlue, 		1}, /* 0x58 */

	{&cg_createPartition, 	5}, /* 0x60 */
	{&cg_countToMap, 	2}, /* 0x68 */
	{&cg_prepare, 		4}, /* 0x70 */
	{&cg_addVAddr, 		6}, /* 0x78 */
	{&cg_dispatchGlue, 	5}, /* 0x80 */

	{&cg_outaddrlGlue, 	2}, /* 0x88 */
	{&cg_timerGlue, 	0}, /* 0x90 */
	{&cg_resume, 		2}, /* 0x98 */
	{&cg_removeVAddr, 	2}, /* 0xA0 */
	{&cg_mappedInChild,	1}, /* 0xA8 */
	{&cg_deletePartition,	1}, /* 0xB0 */
	{&cg_collect,		1}, /* 0xB8 */
	{&cg_yieldGlue,		5}, /* 0xC0 */
};

#define CG_COUNT (sizeof(callgateEntries)/sizeof(struct gdt_callgate_entry_s))

#define gdtEntriesCount (6 + CG_COUNT)

gdt_entry_t gdt[gdtEntriesCount]; //!< Our GDT
struct gdt_ptr gp; //!< Pointer to our GDT

void set_segment_descriptor(uint32_t num, uint32_t base, uint32_t limit, unsigned char type, unsigned char dpl, unsigned char granularity) {
    gdt[num].segment_desc.present     = 0; // invalidate entry until its completion
    gdt[num].segment_desc.base_low    = (base & 0xFFFF);     // bits 15..0  of base
    gdt[num].segment_desc.base_middle = (base >> 16) & 0xFF; // bits 23..16 of base
    gdt[num].segment_desc.base_high   = (base >> 24) & 0xFF; // bits 31..24 of base
    gdt[num].segment_desc.limit_low   = (limit & 0xFFFF);    // bits 15..0  of limit
    gdt[num].segment_desc.limit_high  = (limit >> 16) & 0xF; // bits 19..16 of limit
    gdt[num].segment_desc.type        = type; // MUST be one of the macros defined in gdt.h
    gdt[num].segment_desc.dpl         = dpl;  // descriptor privilege level
    gdt[num].segment_desc.granularity = granularity; // limit inc. steps of 4kB instead of 1B
    gdt[num].segment_desc.s           = 1; // system flag, segment descriptors require 1
    gdt[num].segment_desc.avl         = 0; // Available for use by system software
    gdt[num].segment_desc.l           = 0; // we operate in 32 bits not 64
    gdt[num].segment_desc.d_b         = 1; // we operate in 32 bits not 16
    gdt[num].segment_desc.present     = 1; // validate entry now that it is full
}

/**
 * \fn void set_callgate_descriptor(int num, void* handler, uint8_t args, uint8_t dpl, uint16_t segment)
 * \brief Installs a call gate entry into the GDT
 * \param num The index of the segment into the GDT
 * \param handler The function pointer
 * \param args Argument count
 * \param dpl Descriptor Privilege Level (Caller Privilege Level must be numerically less or equal to DPL)
 * \param segment The segment to switch to
 */
void set_callgate_descriptor(int num, void* handler, uint8_t args, uint8_t dpl, uint16_t segment)
{
	gdt[num].callgate_desc.present = 0; // Make sure the entry is not valid until the end
	gdt[num].callgate_desc.dpl = dpl; // Caller ring privilege level
	gdt[num].callgate_desc.zero = 0;
	gdt[num].callgate_desc.type = GDT_CALLGATE_TYPE; // Call-gate type
	gdt[num].callgate_desc.segment = segment; // Segment selector (entry offset in GDT)
	gdt[num].callgate_desc.reserved = 0;
	gdt[num].callgate_desc.args = args; //number of params to be copied in case of a task switch
	uint32_t addr = (uint32_t)(handler);
	gdt[num].callgate_desc.offset_low = (uint16_t)(addr & 0xFFFF);
	gdt[num].callgate_desc.offset_high = (uint16_t)((addr >> 16) & 0xFFFF);
	gdt[num].callgate_desc.present = 1; /* Validate callgate entry */
	return;
}

void set_tss_descriptor(uint32_t num, uint32_t base, uint32_t limit, unsigned char type, unsigned char dpl, unsigned char granularity) {
	gdt[num].tss_desc.present     = 0; // ensures the entry is not valid until completion
	gdt[num].tss_desc.base_low    = base & 0xFFFF;
	gdt[num].tss_desc.base_middle = (base >> 16) & 0xFF;
	gdt[num].tss_desc.base_high   = (base >> 24) & 0xFF;
	gdt[num].tss_desc.limit_low   = limit & 0xFFFF;
	gdt[num].tss_desc.limit_high  = (limit >> 16) & 0xF;
	gdt[num].tss_desc.type        = type; // either GDT_TSS_INACTIVE_TYPE
                                              // or     GDT_TSS_BUSY_TYPE
	gdt[num].tss_desc.dpl         = dpl; // Descriptor Privilege Level
	gdt[num].tss_desc.granularity = granularity; // A TSS struct is 104 bytes
	gdt[num].tss_desc.zero        = 0;
	gdt[num].tss_desc.zero2       = 0;
	gdt[num].tss_desc.avl         = 0; // Available for use by system software TODO wth
	gdt[num].tss_desc.present     = 1; // Validate the entry
}


void init_tss_segment(uint16_t kernel_stack_segment, uint32_t kernel_esp) {
        memset(&tss, 0, sizeof(tss)); // Sets all tss fields to 0

	tss.ss0 = kernel_stack_segment;
	tss.esp0 = kernel_esp;

	/* TODO RPL USER_RING is it correct ? TODO */
	tss.cs = 0x08 | USER_RING; // Kernel code segment (+ GDT) + USER_RING (RPL)
	tss.ss = tss.ds = tss.es = tss.fs = tss.gs = 0x10 | USER_RING; // Kernel data segment + USER_RING (RPL)
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
	struct gdt_callgate_entry_s *e;

	gp.limit = (sizeof(gdt_entry_t) * (gdtEntriesCount)) - 1;
	gp.base = (uint32_t)&gdt;

	/* Intel 64 and IA-32 Architecture Software Developer Manual, Volume 3A - Sec. 3.5.1
	 * The first descriptor is not used by the GDT is not used by the processor.
	 * A segment selector to this "null descriptor" does not generate an exception when
	 * loaded into a data segment register, but it always generates a general-protection
	 * fault when an attempt is made to access memory using this descriptor */

	/* initialize a null GDT descriptor */
	memset(&gdt[0], 0, sizeof(gdt_entry_t));

	/* segment selectors */
	/* Kernel code segment  */
	set_segment_descriptor(1, 0, 0xFFFFF, SEG_CODE_EXECONLY_NONCONFORMING_TYPE, KERNEL_RING, 1);
	/* Kernel data segment (stack) */
	set_segment_descriptor(2, 0, 0xFFFFF, SEG_DATA_READWRITE_EXPANDUP_TYPE, KERNEL_RING, 1);
	/* User code segment */
	set_segment_descriptor(3, 0, 0xFFFFF, SEG_CODE_EXECONLY_NONCONFORMING_TYPE, USER_RING, 1);
	/* User data segment (stack) */
	set_segment_descriptor(4, 0, 0xFFFFF, SEG_DATA_READWRITE_EXPANDUP_TYPE, USER_RING, 1);

	/* Intel 64 and IA-32 Architectures Software Developer's Manual - Vol. 3a - Sec. 2.1.2
	 * If the call requires a change in privilege level, the processor
	 * also switches to the stack for the targeted privilege level. The
	 * segment selector for the new stack is obtained from the TSS for the
	 * currently running task.
	 */
	init_tss_segment(0x10, 0x0); // kernel data segment and offset 0
        set_tss_descriptor(5, (uint32_t) &tss, sizeof(tss_segment_t) - 1, GDT_TSS_INACTIVE_TYPE, KERNEL_RING /* FIXME DPL of task switch in user ring ??????? FIXME */, 0);

	/* Intel 64 and IA-32 Architecture Software Developer Manual, Volume 3A - Sec. 7.2.2
	 * In most systems, the DPLs of TSS descriptors are to values less than 3 (USER_RING),
	 * so that only privileged code can perform task switching. However, in multitasking
	 * applications, DPLs for some TSS descriptors may be set to 3 (USER_RING) to allow
	 * task switching at the application (or user) privilege level.
	 */

	/**
	 * Callgate setup (Syscalls)
	 */
	for (i=0;i<CG_COUNT; i++)
	{
		e = &callgateEntries[i];
		set_callgate_descriptor(6+i, e->handler, e->nargs, USER_RING, 0x08);
	}
	
	DEBUG(INFO, "Callgate set-up\n");

	gdtFlush();
	tssFlush();
}

