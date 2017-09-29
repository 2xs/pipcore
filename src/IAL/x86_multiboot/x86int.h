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
 * \file x86int.h
 * \brief x86 interrupts include file for x86 IAL
 */

#ifndef IAL_STRUCT_H
#define IAL_STRUCT_H

#include <stdint.h>

/**
 * \struct idt_entry_struct
 * \brief Interrupt Descriptor Table entry
 */
struct idt_entry_struct
{
    uint16_t base_lo; //!< Lower bytes of handler address
    uint16_t sel; //!< Selector
    uint8_t  always0; //!< ?
    uint8_t  flags; //!< Interrupt handler flags (Required Privilege Level etc)
    uint16_t base_hi; //!< Higher bytes of handler address
} __attribute__((packed));

typedef struct idt_entry_struct idt_entry_t;

/**
 * \struct idt_ptr_struct
 * \brief IDT pointer structure
 */
struct idt_ptr_struct
{
    uint16_t limit; //!< Address limit
    uint32_t base; //!< IDT pointer base
} __attribute__((packed));

typedef struct idt_ptr_struct idt_ptr_t;

extern void irq0(); //!< IRQ 0
extern void irq1(); //!< IRQ 1
extern void irq2(); //!< IRQ 2
extern void irq3(); //!< IRQ 3
extern void irq4(); //!< IRQ 4
extern void irq5(); //!< IRQ 5
extern void irq6(); //!< IRQ 6
extern void irq7(); //!< IRQ 7
extern void irq8(); //!< IRQ 8
extern void irq9(); //!< IRQ 9
extern void irq10(); //!< IRQ 10
extern void irq11(); //!< IRQ 11
extern void irq12(); //!< IRQ 12
extern void irq13(); //!< IRQ 13
extern void irq14(); //!< IRQ 14
extern void irq15(); //!< IRQ 15

/**
 * \struct registers
 * \brief Registers structure for x86
 */
typedef struct pushad_regs_s
{
    uint32_t edi; //!< General register EDI
    uint32_t esi; //!< General register ESI
    uint32_t ebp; //!< EBP
    uint32_t esp; //!< Stack pointer
    uint32_t ebx; //!< General register EBX
    uint32_t edx; //!< General register EDX
    uint32_t ecx; //!< General register ECX
    uint32_t eax; //!< General register EAX
} pushad_regs_t;

/**
 * \struct int_stack_s
 * \brief Stack context from interrupt/exception
 */
typedef const struct int_stack_s
{
    pushad_regs_t regs;//!< Interrupt handler saved regs
    uint32_t int_no; //!< Interrupt number
    uint32_t err_code; //!< Interrupt error code
    uint32_t eip; //!< Execution pointer
    uint32_t cs; //!< Code segment
    uint32_t eflags; //!< CPU flags
    /* only present when we're coming from userland */
    uint32_t useresp; //!< User-mode ESP
    uint32_t ss; //!< Stack segment
} int_ctx_t ;

/** 
 * \struct gate_stack_s
 * \brief Stack context from callgate
 */
typedef const struct gate_stack_s
{
	pushad_regs_t regs;
	uint32_t eip;
} gate_ctx_t;

/**
 * \struct user_ctx_s
 * \brief User saved context
 */
typedef struct user_ctx_s
{
	uint32_t eip;
	uint32_t pipflags;
	uint32_t eflags;
	pushad_regs_t regs;
	uint32_t valid;
	uint32_t nfu[4];
} user_ctx_t;

enum cpuid_features {
	CPUID_FEAT_ECX_SSE3         = 1 << 0,
	CPUID_FEAT_ECX_PCLMUL       = 1 << 1,
	CPUID_FEAT_ECX_DTES64       = 1 << 2,
	CPUID_FEAT_ECX_MONITOR      = 1 << 3,
	CPUID_FEAT_ECX_DS_CPL       = 1 << 4,
	CPUID_FEAT_ECX_VMX          = 1 << 5,
	CPUID_FEAT_ECX_SMX          = 1 << 6,
	CPUID_FEAT_ECX_EST          = 1 << 7,
	CPUID_FEAT_ECX_TM2          = 1 << 8,
	CPUID_FEAT_ECX_SSSE3        = 1 << 9,
	CPUID_FEAT_ECX_CID          = 1 << 10,
	CPUID_FEAT_ECX_FMA          = 1 << 12,
	CPUID_FEAT_ECX_CX16         = 1 << 13,
	CPUID_FEAT_ECX_ETPRD        = 1 << 14,
	CPUID_FEAT_ECX_PDCM         = 1 << 15,
	CPUID_FEAT_ECX_PCID			= 1 << 17,
	CPUID_FEAT_ECX_DCA          = 1 << 18,
	CPUID_FEAT_ECX_SSE4_1       = 1 << 19,
	CPUID_FEAT_ECX_SSE4_2       = 1 << 20,
	CPUID_FEAT_ECX_x2APIC       = 1 << 21,
	CPUID_FEAT_ECX_MOVBE        = 1 << 22,
	CPUID_FEAT_ECX_POPCNT       = 1 << 23,
	CPUID_FEAT_ECX_AES          = 1 << 25,
	CPUID_FEAT_ECX_XSAVE        = 1 << 26,
	CPUID_FEAT_ECX_OSXSAVE      = 1 << 27,
	CPUID_FEAT_ECX_AVX          = 1 << 28,
 
	CPUID_FEAT_EDX_FPU          = 1 << 0,
	CPUID_FEAT_EDX_VME          = 1 << 1,
	CPUID_FEAT_EDX_DE           = 1 << 2,
	CPUID_FEAT_EDX_PSE          = 1 << 3,
	CPUID_FEAT_EDX_TSC          = 1 << 4,
	CPUID_FEAT_EDX_MSR          = 1 << 5,
	CPUID_FEAT_EDX_PAE          = 1 << 6,
	CPUID_FEAT_EDX_MCE          = 1 << 7,
	CPUID_FEAT_EDX_CX8          = 1 << 8,
	CPUID_FEAT_EDX_APIC         = 1 << 9,
	CPUID_FEAT_EDX_SEP          = 1 << 11,
	CPUID_FEAT_EDX_MTRR         = 1 << 12,
	CPUID_FEAT_EDX_PGE          = 1 << 13,
	CPUID_FEAT_EDX_MCA          = 1 << 14,
	CPUID_FEAT_EDX_CMOV         = 1 << 15,
	CPUID_FEAT_EDX_PAT          = 1 << 16,
	CPUID_FEAT_EDX_PSE36        = 1 << 17,
	CPUID_FEAT_EDX_PSN          = 1 << 18,
	CPUID_FEAT_EDX_CLF          = 1 << 19,
	CPUID_FEAT_EDX_DTES         = 1 << 21,
	CPUID_FEAT_EDX_ACPI         = 1 << 22,
	CPUID_FEAT_EDX_MMX          = 1 << 23,
	CPUID_FEAT_EDX_FXSR         = 1 << 24,
	CPUID_FEAT_EDX_SSE          = 1 << 25,
	CPUID_FEAT_EDX_SSE2         = 1 << 26,
	CPUID_FEAT_EDX_SS           = 1 << 27,
	CPUID_FEAT_EDX_HTT          = 1 << 28,
	CPUID_FEAT_EDX_TM1          = 1 << 29,
	CPUID_FEAT_EDX_IA64         = 1 << 30,
	CPUID_FEAT_EDX_PBE          = 1 << 31
};

enum cpuid_requests {
	CPUID_GETVENDORSTRING,
	CPUID_GETFEATURES,
	CPUID_GETTLB,
	CPUID_GETSERIAL,
 
	CPUID_INTELEXTENDED=0x80000000,
	CPUID_INTELFEATURES,
	CPUID_INTELBRANDSTRING,
	CPUID_INTELBRANDSTRINGMORE,
	CPUID_INTELBRANDSTRINGEND,
};

/** issue a single request to CPUID. Fits 'intel features', for instance
 *  note that even if only "eax" and "edx" are of interest, other registers
 *  will be modified by the operation, so we need to tell the compiler about it.
 */
static inline void cpuid(int code, uint32_t *a, uint32_t *d) {
	asm volatile("cpuid":"=a"(*a),"=d"(*d):"a"(code):"ecx","ebx");
}

/** issue a complete request, storing general registers output as a string
 */
static inline int cpuid_string(int code, uint32_t where[4]) {
	asm volatile("cpuid":"=a"(*where),"=b"(*(where+1)),
				 "=c"(*(where+2)),"=d"(*(where+3)):"a"(code));
	return (int)where[0];
}

#endif
