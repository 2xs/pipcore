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
#include "pipcall.h"
#include "segment_selectors.h"

#define GDT_N_ENTRY (LAST_PIPCALL + 1)

gdt_entry_t gdt[GDT_N_ENTRY]; //!< Our GDT
tss_t tss; //!< Generic TSS for userland-to-kernel switch

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
//extern void *cg_dispatchGlue;
extern void *cg_timerGlue;
//extern void *cg_resume;
extern void *cg_removeVAddr;
extern void *cg_mappedInChild;
extern void *cg_deletePartition;
extern void *cg_collect;
//extern void *cg_yieldGlue;

/* TODO refactor to new structure fill
 * see below */
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
/*
void set_callgate_descriptor(int num, void* handler, uint8_t args, uint8_t dpl, uint16_t segment)
{
	uint32_t addr = (uint32_t)(handler);
	gdt[num] = (gdt_entry_t) {
		.callgate_desc = {
			.dpl         = dpl,
			.zero        = 0,
			.type        = GDT_CALLGATE_TYPE,
			.segment     = segment,
			.reserved    = 0,
			.args        = args,
			.offset_low  = (uint16_t)(addr & 0xFFFF),
			.offset_high = (uint16_t)((addr >> 16) & 0xFFFF),
			.present     = 1
		}
	};
}
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

void set_tss_descriptor(uint32_t num, tss_t *tss_ptr, uint32_t limit, unsigned char type, unsigned char dpl, unsigned char granularity) {
	uint32_t base = (uint32_t) tss_ptr;
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
	gdt[num].tss_desc.avl         = 0; // Available for use by system software
	gdt[num].tss_desc.present     = 1; // Validate the entry
}


void set_tss(uint16_t kernel_code_segment, uint16_t kernel_data_segment, uint16_t kernel_stack_segment) {
	tss.prev_tss   = 0; //!< Pointer to the previous TSS entry (updated on a task switch)
	tss.reserved0  = 0;
	tss.esp0       = 0; //!< Kernel-mode ESP           (static)
	tss.ss0        = kernel_stack_segment; //!< Kernel-mode stack segment (static)
	tss.reserved1  = 0;
	tss.esp1       = 0; //!< Ring-1 ESP                (static)
	tss.ss1        = 0; //!< Ring-1 stack segment      (static)
	tss.reserved2  = 0;
	tss.esp2       = 0; //!< Ring-2 ESP                (static)
	tss.ss2        = 0; //!< Ring-2 stack segment      (static)
	tss.reserved3  = 0;
	tss.cr3        = 0; //!< Page directory address    (static)
	tss.eip        = 0; //!< Execution pointer    (prior to task switch)
	tss.eflags     = 0; //!< CPU flags            (prior to task switch)
	tss.eax        = 0; //!< General register EAX (prior to task switch)
	tss.ecx        = 0; //!< General register ECX (prior to task switch)
	tss.edx        = 0; //!< General register EDX (prior to task switch)
	tss.ebx        = 0; //!< General register EBX (prior to task switch)
	tss.esp        = 0; //!< User-mode ESP        (prior to task switch)
	tss.ebp        = 0; //!< User-mode EBP        (prior to task switch)
	tss.esi        = 0; //!< General register ESI (prior to task switch)
	tss.edi        = 0; //!< General register EDI (prior to task switch)
	tss.es         = 0; //!< Segment selector ES  (prior to task switch)
	tss.reserved4  = 0;
	tss.cs         = kernel_code_segment; //!< Segment selector CS  (prior to task switch)
	tss.reserved5  = 0;
	tss.ss         = kernel_data_segment; //!< Segment selector SS  (prior to task switch)
	tss.reserved6  = 0;
	tss.ds         = kernel_data_segment; //!< Segment selector DS  (prior to task switch)
	tss.reserved7  = 0;
	tss.fs         = kernel_data_segment; //!< Segment selector FS  (prior to task switch)
	tss.reserved8  = 0;
	tss.gs         = kernel_data_segment; //!< Segment selector GS  (prior to task switch)
	tss.reserved9  = 0;
	tss.ldt        = 0; //!< Pointer to the LDT (static)
	tss.reserved10 = 0;
	tss.trap       = 0; //!< Flag to raise an exception when a task switch to this task occurs (static)
	tss.reserved11 = 0;
	tss.iomap_base = 0; //!< IOMMU base
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

/* Effectively loads the GDT, and changes the code segment selector to
 * KERNEL_CODE_SEGMENT, and the data segment selectors to KERNEL_DATA_SEGMENT.
 * /!\ This function defines a label ! Multiple calls to this function
 * may prevent the code from compiling ! */
void load_gdt(void *base, uint16_t limit) {

	struct gdt_ptr gp = {.limit = limit, .base = (uint32_t) base}; //!< Pointer to our GDT
	asm(/* load the GDT, but our current segment selectors remain the same
	     * we have to change them manually */
	    "lgdt (%0);" // gp

	    /* we can't load ss with a mov instruction
	     * we jump through the GDT to the next instruction to change cs
	     * (we jump to a label defined in the next assembly line) */
	    "ljmp %1, $set_kernel_data_segment_selectors;"

	    /* label declaration before the next instruction */
	    "set_kernel_data_segment_selectors:;"
	    /* store KERNEL_DATA_SEGMENT_SELECTOR in ax */
	    "mov %2, %%ax;"
	    /* move the value from ax to the segment registers */
	    "mov %%ax, %%ds;"
	    "mov %%ax, %%es;"
	    "mov %%ax, %%fs;"
	    "mov %%ax, %%gs;"
	    "mov %%ax, %%ss;"

	    /* output operands */
	    :
	    /* input operands */
	    : "r"(&gp), "i"(KERNEL_CODE_SEGMENT_SELECTOR), "i"(KERNEL_DATA_SEGMENT_SELECTOR)
	    /* registers we changed during that inline assembly */
	    : "%eax"
	);
}

/* Loads the TSS register with the TSS selector */
void load_tss() {
	asm(
	    "mov %0, %%ax;"
	    "ltr %%ax;"

	    /* output operands */
	    :
	    /* input operands */
	    : "i"(TSS_SELECTOR | USER_RING) /* TODO Correct ? */
	    /* cloberred registers */
	    : "%eax"
	);
}


/**
 * \fn void gdt_init()
 * \brief Installs the GDT into the CPU
 */
void gdt_init(void)
{
	/* Intel 64 and IA-32 Architecture Software Developer Manual, Volume 3A - Sec. 3.5.1
	 * The first descriptor is not used by the GDT is not used by the processor.
	 * A segment selector to this "null descriptor" does not generate an exception when
	 * loaded into a data segment register, but it always generates a general-protection
	 * fault when an attempt is made to access memory using this descriptor */

	/* initialize a null GDT descriptor */
	gdt[0].null_desc = 0;

	/* segment descriptors */
	/* TODO maybe we could use a single segment data segment */
	/* Kernel code segment  */
	set_segment_descriptor(1, 0, 0xFFFFF, SEG_CODE_EXECONLY_NONCONFORMING_TYPE, KERNEL_RING, GRANULARITY_4096);
	/* Kernel data segment (stack) */
	set_segment_descriptor(2, 0, 0xFFFFF, SEG_DATA_READWRITE_EXPANDUP_TYPE, KERNEL_RING, GRANULARITY_4096);
	/* User code segment */
	set_segment_descriptor(3, 0, 0xFFFFF, SEG_CODE_EXECONLY_NONCONFORMING_TYPE, USER_RING, GRANULARITY_4096);
	/* User data segment (stack) */
	set_segment_descriptor(4, 0, 0xFFFFF, SEG_DATA_READWRITE_EXPANDUP_TYPE, USER_RING, GRANULARITY_4096);
	DEBUG(INFO, "Segments initialized\n");

	/* Intel 64 and IA-32 Architectures Software Developer's Manual - Vol. 3a - Sec. 2.1.2
	 * If the call requires a change in privilege level, the processor
	 * also switches to the stack for the targeted privilege level. The
	 * segment selector for the new stack is obtained from the TSS for the
	 * currently running task.
	 */
	/* TODO check RPL for the following segments once we get into userland*/
	set_tss(KERNEL_CODE_SEGMENT_SELECTOR | USER_RING, KERNEL_DATA_SEGMENT_SELECTOR | USER_RING, KERNEL_DATA_SEGMENT_SELECTOR);
        set_tss_descriptor(5, &tss, sizeof(tss_t) - 1, GDT_TSS_INACTIVE_TYPE, KERNEL_RING, GRANULARITY_1);
	DEBUG(INFO, "TSS and its descriptor initialized\n");

	/* Intel 64 and IA-32 Architecture Software Developer Manual, Volume 3A - Sec. 7.2.2
	 * In most systems, the DPLs of TSS descriptors are to values less than 3 (USER_RING),
	 * so that only privileged code can perform task switching. However, in multitasking
	 * applications, DPLs for some TSS descriptors may be set to 3 (USER_RING) to allow
	 * task switching at the application (or user) privilege level.
	 */

	/**
	 * Callgate setup (Syscalls)
	 */ 
	set_callgate_descriptor(PIPCALL_OUTB,            &cg_outbGlue, 		PIPCALL_NARGS_OUTB,              USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_INB,             &cg_inbGlue, 		PIPCALL_NARGS_INB,               USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_OUTW,            &cg_outwGlue, 		PIPCALL_NARGS_OUTW,              USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_INW,             &cg_inwGlue, 		PIPCALL_NARGS_INW,               USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_OUTL,            &cg_outlGlue, 		PIPCALL_NARGS_OUTL,              USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_INL,             &cg_inlGlue, 		PIPCALL_NARGS_INL,               USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_CREATEPARTITION, &cg_createPartition, 	PIPCALL_NARGS_CREATEPARTITION,   USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_COUNTTOMAP,      &cg_countToMap, 	PIPCALL_NARGS_COUNTTOMAP,        USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_PREPARE,         &cg_prepare, 		PIPCALL_NARGS_PREPARE,           USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_ADDVADDR,        &cg_addVAddr, 		PIPCALL_NARGS_ADDVADDR,          USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	//set_callgate_descriptor(PIPCALL_DISPATCH,        &cg_dispatchGlue, 	PIPCALL_NARGS_DISPATCH,          USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_OUTADDRL,        &cg_outaddrlGlue, 	PIPCALL_NARGS_OUTADDRL,          USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_TIMER,           &cg_timerGlue, 	PIPCALL_NARGS_TIMER,             USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	//set_callgate_descriptor(PIPCALL_RESUME,          &cg_resume, 		PIPCALL_NARGS_RESUME,            USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_REMOVEVADDR,     &cg_removeVAddr, 	PIPCALL_NARGS_REMOVEVADDR,       USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_MAPPEDINCHILD,   &cg_mappedInChild,	PIPCALL_NARGS_MAPPEDINCHILD,     USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_DELETEPARTITION, &cg_deletePartition,	PIPCALL_NARGS_DELETEPARTITION,   USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	set_callgate_descriptor(PIPCALL_COLLECT,         &cg_collect,		PIPCALL_NARGS_COLLECT,           USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	//set_callgate_descriptor(PIPCALL_YIELD,           &cg_yieldGlue,		PIPCALL_NARGS_YIELD,             USER_RING, KERNEL_CODE_SEGMENT_SELECTOR);
	DEBUG(INFO, "Callgate descriptors initialized\n");

	load_gdt(&gdt, (sizeof(gdt_entry_t) * GDT_N_ENTRY) - 1);
	DEBUG(INFO, "GDT loaded and current segments updated\n");

	load_tss();
	DEBUG(INFO, "TSS loaded\n");
}
