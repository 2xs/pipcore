/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2024)                */
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

#ifndef COPROC_H_
#define COPROC_H_

/* Definitions for ARMv7-A/R */

#define CPSR_NEGATIVE	(1<<31)
#define CPSR_ZERO		(1<<30)
#define CPSR_CARRY		(1<<29)
#define CPSR_OVERFLOW	(1<<28)
#define CPSR_UNDERFLOW	(1<<27)
#define CPSR_JAZELLE	(1<<24)
#define CPSR_E			(1<<9)
#define CPSR_A			(1<<8)
#define CPSR_IRQ		(1<<7)
#define CPSR_FIQ		(1<<6)
#define CPSR_THUMB		(1<<5)

#define ARM_MODE_USER	(0x10)
#define ARM_MODE_FIQ	(0x11)
#define ARM_MODE_IRQ	(0x12)
#define ARM_MODE_SVC	(0x13)
#define ARM_MODE_MON	(0x16)
#define ARM_MODE_ABORT	(0x17)
#define ARM_MODE_HYP	(0x1A)
#define ARM_MODE_UNDEF	(0x1B)
#define ARM_MODE_SYSTEM	(0x1F)

/* B4.1.130: SCTLR */
#define SCTLR_MMU			(1)
#define SCTLR_ALIGH			(1<<1)
#define SCTLR_DCACHE		(1<<2)
#define SCTLR_CP15BEN		(1<<5)
#define SCTLR_ENDIAN		(1<<7)
#define SCTLR_SWP			(1<<10)
#define SCTLR_BRANCH_PRED	(1<<11)
#define SCTLR_ICACHE		(1<<12)
#define SCTLR_VECTOR		(1<<13)
#define SCTLR_ROUNDROBIN	(1<<14)
#define SCTLR_HWACCESS		(1<<17)
#define SCTLR_WXN			(1<<19)
#define SCTLR_UWXN			(1<<20)
#define SCTLR_FASTINT		(1<<21)
#define SCTLR_U				(1<<22)
#define SCTLR_VE			(1<<24)
#define SCTLR_EE			(1<<25)
#define SCTLR_NMFI			(1<<27)
#define SCTLR_TRE			(1<<28)
#define SCTLR_AFE			(1<<29)
#define SCTLR_THUMBEXC		(1<<30)

/* B3.17.1: CP15 register summary by coprocessor register number */
#define ID_MIDR		p15, c0, 0, c0, 0
#define ID_CTR		p15, c0, 0, c0, 1
#define ID_TCMTR	p15, c0, 0, c0, 2
#define ID_TLBTR	p15, c0, 0, c0, 3
#define ID_MPIDR	p15, c0, 0, c0, 5
#define ID_REVIDR	p15, c0, 0, c0, 6

#define ID_PFR0		p15, c0, 0, c1, 0
#define ID_PFR1		p15, c0, 0, c1, 1
#define ID_DFR0		p15, c0, 0, c1, 2
#define ID_AFR0		p15, c0, 0, c1, 3
#define ID_MMFR0	p15, c0, 0, c1, 4
#define ID_MMFR1	p15, c0, 0, c1, 5
#define ID_MMFR2	p15, c0, 0, c1, 6
#define ID_MMFR3	p15, c0, 0, c1, 7

#define ID_ISAR0	p15, c0, 0, c2, 0
#define ID_ISAR1	p15, c0, 0, c2, 1
#define ID_ISAR2	p15, c0, 0, c2, 2
#define ID_ISAR3	p15, c0, 0, c2, 3
#define ID_ISAR4	p15, c0, 0, c2, 4
#define ID_ISAR5	p15, c0, 0, c2, 5

#define ID_CCSIDR	p15, c0, 1, c0, 0
#define ID_CLIDR	p15, c0, 1, c0, 1
#define ID_AIDR		p15, c0, 1, c0, 7

#define ID_CCSELR	p15, c0, 2, c0, 0
#define ID_VPIDR	p15, c0, 4, c0, 0
#define ID_VMPIDR	p15, c0, 4, c0, 5

#define ID_SCTLR	p15, c1, 0, c0, 0
#define ID_ACTLR	p15, c1, 0, c0, 1
#define ID_CPACR	p15, c1, 0, c0, 2

#define ID_SCR		p15, c1, 0, c1, 0
#define ID_SDER		p15, c1, 0, c1, 1
#define ID_NSACR	p15, c1, 0, c1, 2

#define ID_HSCTLR	p15, c1, 4, c0, 0
#define ID_HACTLR	p15, c1, 4, c0, 1

#define ID_HCR		p15, c1, 4, c1, 0
#define ID_HDCR		p15, c1, 4, c1, 1
#define ID_HCPTR	p15, c1, 4, c1, 2
#define ID_HSTR		p15, c1, 4, c1, 3
#define ID_HACR		p15, c1, 4, c1, 7

#define ID_TTBR0	p15, c2, 0, c0, 0
#define ID_TTBR1	p15, c2, 0, c0, 1
#define ID_TTBCR	p15, c2, 0, c0, 2
#define ID_HTCR		p15, c2, 4, c0, 2
#define ID_VTCR		p15, c2, 4, c1, 2

#define ID_DACR		p15, c3, 0, c0, 0

#define ID_DFSR		p15, c5, 0, c0, 0
#define ID_IFSR		p15, c5, 0, c0, 1
#define ID_ADFSR	p15, c5, 0, c1, 0
#define ID_AIFSR	p15, c5, 0, c1, 1
#define ID_DFAR		p15, c6, 0, c0, 0
#define ID_IFAR		p15, c6, 0, c0, 2

#define ID_ICIALLUIS	p15, c7, 0, c1, 0
#define ID_BPIALLUIS	p15, c7, 0, c1, 6
#define ID_PAR			p15, c7, 0, c4, 0
#define ID_ICIALLU		p15, c7, 0, c5, 0
#define ID_ICIMVAU		p15, c7, 0, c5, 1
#define ID_CP15ISB		p15, c7, 0, c5, 4
#define ID_BPIALL		p15, c7, 0, c5, 6
#define ID_BPIMVA		p15, c7, 0, c5, 7
#define ID_DCIMVAC		p15, c7, 0, c6, 1
#define ID_DCISW		p15, c7, 0, c6, 2
#define ID_ATS1CPR		p15, c7, 0, c8, 0
#define ID_ATS1CPW		p15, c7, 0, c8, 1
#define ID_ATS1CUR		p15, c7, 0, c8, 2
#define ID_ATS1CUW		p15, c7, 0, c8, 3
#define ID_ATS12NSOPR	p15, c7, 0, c8, 4
#define ID_ATS12NSOPW	p15, c7, 0, c8, 5
#define ID_ATS12NSOUR	p15, c7, 0, c8, 6
#define ID_ATS12NSOUW	p15, c7, 0, c8, 7
#define ID_DCCMVAC		p15, c7, 0, c10, 1
#define ID_DCCSW		p15, c7, 0, c10, 2
#define ID_CP15DSB		p15, c7, 0, c10, 4
#define ID_CP15DMB		p15, c7, 0, c10, 5
#define ID_DCCMVAU		p15, c7, 0, c11, 1
#define ID_DCCIMVAC		p15, c7, 0, c14, 1
#define ID_DCCISW		p15, c7, 0, c14, 2
#define ID_ATS1HR		p15, c7, 4, c8, 0
#define ID_ATS1HW		p15, c7, 4, c8, 1

#define ID_TLBIALL		p15, c8, 0, c7, 0
#define ID_TLBIMVA		p15, c8, 0, c7, 1
#define ID_TLBIASID		p15, c8, 0, c7, 2
#define ID_TLBIMVAA		p15, c8, 0, c7, 3

#define ID_VBAR			p15, c12, 0, c0, 0
#define ID_MVBAR		p15, c12, 0, c0, 1
#define ID_ISR			p15, c12, 0, c1, 0
#define ID_HVBAR		p15, c12, 4, c0, 0

#define ID_FCSEIDR		p15, c13, 0, c0, 0
#define ID_CONTEXTIDR	p15, c13, 0, c0, 1

#define CP_READ_ASM(reg, pn, n,opc1,m,opc2)		\
	mrc pn, opc1, reg, n, m, opc2
#define CP_WRITE_ASM(reg, pn, n,opc1,m,opc2)	\
	mcr pn, opc1, reg, n, m, opc2

#define CP_READ(reg, pn, n,opc1,m,opc2)		\
	asm("mrc " #pn ", " #opc1 ", %0, " #n ", " #m ", " #opc2	\
		: "=r"(reg));
#define CP_WRITE(reg, pn, n,opc1,m,opc2)		\
	asm("mcr " #pn ", #" #opc1 ", %0, " #n ", " #m ", #" #opc2	\
		:: "r"(reg));

#define READ_CP_ASM(dst,id)		CP_READ_ASM(dst,id)
#define WRITE_CP_ASM(src,id)	CP_WRITE_ASM(src,id)
#define READ_CP(dst,id)			CP_READ(dst,id)
#define WRITE_CP(src,id)		CP_WRITE(src,id)

#define DMB() asm("dmb")

#define READ_CPSR(reg)	asm("mrs %0, cpsr ":"=r"(reg))
#define WRITE_CPSR(reg)	asm("msr cpsr_fc, %0"::"r"(reg))

/* ============================================= */

#define DSB()                               \
	asm volatile (                      \
		"dsb"                       \
		:                           \
		:                           \
		: "memory"                  \
	)

#define ISB()                               \
	asm volatile (                      \
		"isb"                       \
		:                           \
		:                           \
		: "memory"                  \
	)

#define WRITE_TLBIASID(val)                 \
	asm volatile (                      \
		"mcr p15, 0, %0, c8, c7, 2" \
		:                           \
		: "r" (val)                 \
		: "memory"                  \
	)

#define WRITE_TTBR0(val)                    \
	asm volatile (                      \
		"mcr p15, 0, %0, c2, c0, 0" \
		:                           \
		: "r" (val)                 \
		: "memory"                  \
	)

#endif
