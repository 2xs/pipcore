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

#include "idt.h"
#include "port.h"
#include "pic8259.h"
#include "debug.h"
#include "libc.h"
#include "Internal.h"

/* declaration of the int_ctx_t type */
#include "x86int.h"

/* declaration of the assembly interrupt counterparts */
#include "asm_int.h"

#include "segment_selectors.h"
#include "gdt.h"

/* TODO remove me once the new service is written in Coq */
//#include "yield_c.h"

/* TODO possibly rewrite me in Coq too */
#include "pip_interrupt_calls.h"

#define DOUBLE_FAULT_LEVEL 8

/* C handler called when interrupt linked to the PIC are triggered
 * i.e. hardware related interrupts like alarms)
 * (see calling code in irq.s - macro HARDWARE_INT) */
void hardwareInterruptHandler(int_ctx_t *ctx)
{
	DEBUG(TRACE, "Received hardware int n°%d\n", ctx->int_no);
	outb (PIC1_COMMAND, PIC_EOI); // PIC interrupt acknowledgment
	outb (PIC2_COMMAND, PIC_EOI); // PIC interrupt acknowledgment

	/* We need to convert the int_ctx_t ctx
	 * into a generic user_ctx_t */
	user_ctx_t uctx;
	uctx.eip = ctx->eip;
	uctx.regs = ctx->regs;
	uctx.regs.esp = ctx->useresp;
	uctx.eflags = ctx->eflags;
	uctx.valid = 1;

	//TODO The next few lines of code could be written in Coq

	page rootPartDesc = getRootPartition();
	//DEBUG(TRACE, "Hardware interrupt handler - Got root partition : %x\n", rootPartDesc);
	page intPartitionPartDesc = getCurPartition();
	//DEBUG(TRACE, "Hardware interrupt handler - Got interrupted partition : %x\n", intPartitionPartDesc);
	interruptMask intPartitionIntState = get_self_int_state();
	unsigned saveIndex;
	if (intPartitionIntState == 0) {
		//DEBUG(TRACE, "Hardware interrupt handler - Partition is VCLI'd, saving its context in index %x\n", CLI_INDEX_SAVE);
		saveIndex = CLI_SAVE_INDEX;
	}
	else {
		//DEBUG(TRACE, "Hardware interrupt handler - Partition is VSTI'd, saving its context in index %x\n", STI_INDEX_SAVE);
		saveIndex = STI_SAVE_INDEX;
	}
	//DEBUG(TRACE, "Hardware interrupt handler - Retrieved interrupt state from interrupted partition : %d\n", intPartitionIntState);
	page intPartitionPageDir  = getPd(intPartitionPartDesc);
	//DEBUG(TRACE, "Hardware interrupt handler - Retrieved interrupted partition page dir : %x\n", intPartitionPageDir);
	yield_checks rc = getSourcePartVidtCont(rootPartDesc, intPartitionPageDir, ctx->int_no, saveIndex, getNbLevel(), intPartitionIntState, intPartitionIntState, &uctx);
	switch(rc) {
		case coq_FAIL_UNAVAILABLE_CALLER_VIDT:
		case coq_FAIL_CALLER_CONTEXT_SAVE:
			if (rc == coq_FAIL_UNAVAILABLE_CALLER_VIDT) {
				DEBUG(INFO, "Interrupted partition's VIDT is unavailable, can not salvage its context\n");
			}
			else {// (rc == CALLER_CONTEXT_SAVE)
				DEBUG(INFO, "Interrupted partition's context save address is not valid, can not salvage its context\n");
			}
			DEBUG(TRACE, "Skip saving the interrupted partition's context\n");
			getTargetPartVidtCont(rootPartDesc, intPartitionPageDir, getVidtVAddr(), 0, ctx->int_no, getNbLevel(), getIndexOfAddr(getVidtVAddr(), fstLevel), 0, 0, &uctx);
			break;
		default:
			DEBUG(CRITICAL, "Unrecoverable error occured during while loading the root interruption handler - guru meditation\n");
			for(;;);
	}
}


/* C handler called when software interrupts are triggered
 * i.e. explicit interrupts with `int __` instructions
 * (see calling code in irq.s - macro SOFTWARE_INT) */
void softwareInterruptHandler(int_ctx_t *ctx)
{
	DEBUG(TRACE, "Received software int n°%d\n", ctx->int_no);

	user_ctx_t uctx;
	uctx.eip = ctx->eip;
	uctx.regs = ctx->regs;
	uctx.regs.esp = ctx->useresp;
	uctx.eflags = ctx->eflags;
	uctx.valid = 1;

	// TODO The below code could be written in Coq

	page currentPartDesc = getCurPartition();
	//DEBUG(TRACE, "Software interrupt handler - Got current partition : %x\n", currentPartDesc);
	interruptMask currentPartitionIntState = get_self_int_state();
	unsigned saveIndex;
	if (currentPartitionIntState == 0) {
		//DEBUG(TRACE, "Software interrupt handler - Partition is VCLI'd, saving its context in index %x\n", CLI_INDEX_SAVE);
		saveIndex = CLI_SAVE_INDEX;
	}
	else {
		//DEBUG(TRACE, "Software interrupt handler - Partition is VSTI'd, saving its context in index %x\n", STI_INDEX_SAVE);
		saveIndex = STI_SAVE_INDEX;
	}
	//DEBUG(TRACE, "Software interrupt handler - Retrieved interrupt state from current partition : %d\n", intPartitionIntState);
	page currentPageDir  = getPd(currentPartDesc);
	//DEBUG(TRACE, "Software interrupt handler - Got current page dir : %x\n", currentPageDir);
	yield_checks rc = getParentPartDescCont(currentPartDesc, currentPageDir, ctx->int_no, saveIndex, getNbLevel(), currentPartitionIntState, currentPartitionIntState, &uctx);
	DEBUG(TRACE, "Returned from software interrupt, an error occurred : %d\n", rc);
	//Set return value
	uctx.regs.eax = rc;
}


void propagateFault(page callerPartDesc, page callerPageDir, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, interruptMask flagsOnYield, interruptMask flagsOnWake, user_ctx_t *callerInterruptedContext);

/* C handler called when faults are triggered
 * e.g when trying to divide by zero 
 * (see calling code in irq.s - macro FAULT_INT_ERRCODE/FAULT_INT_NOERRCODE) */
void faultInterruptHandler(int_ctx_t *ctx)
{
	DEBUG(TRACE, "Received fault int n°%d\n", ctx->int_no);
	DEBUG(TRACE, "Error code is : %x\n", ctx->err_code);

	user_ctx_t uctx;
	uctx.eip = ctx->eip;
	uctx.regs = ctx->regs;
	uctx.eflags = ctx->eflags;
	uctx.regs.esp = ctx->useresp;
	uctx.valid = 1;

	// TODO The below code could be written in Coq

	page currentPartDesc = getCurPartition();
	//DEBUG(TRACE, "Fault interrupt handler - Got current partition : %x\n", currentPartDesc);
	interruptMask currentPartitionIntState = get_self_int_state();
	unsigned saveIndex;
	if (currentPartitionIntState == 0) {
		//DEBUG(TRACE, "Fault interrupt handler - Partition is VCLI'd, saving its context in index %x\n", CLI_INDEX_SAVE);
		saveIndex = CLI_SAVE_INDEX;
	}
	else {
		//DEBUG(TRACE, "Fault interrupt handler - Partition is VSTI'd, saving its context in index %x\n", STI_INDEX_SAVE);
		saveIndex = STI_SAVE_INDEX;
	}
	//DEBUG(TRACE, "Fault interrupt handler - Retrieved interrupt state from current partition : %d\n", intPartitionIntState);
	page currentPageDir  = getPd(currentPartDesc);
	//DEBUG(TRACE, "Fault interrupt handler - Got current page dir : %x\n", currentPageDir);
	propagateFault(currentPartDesc, currentPageDir, ctx->int_no, saveIndex, getNbLevel(), currentPartitionIntState, currentPartitionIntState, &uctx);
}

//TODO could be written in Coq
void propagateFault(page callerPartDesc, page callerPageDir, unsigned targetInterrupt, unsigned callerContextSaveIndex, unsigned nbL, interruptMask flagsOnYield, interruptMask flagsOnWake, user_ctx_t *callerInterruptedContext)
{
	yield_checks rc = getParentPartDescCont(callerPartDesc, callerPageDir, targetInterrupt, callerContextSaveIndex, nbL, flagsOnYield, flagsOnWake, callerInterruptedContext);
	switch(rc) {
		case coq_FAIL_UNAVAILABLE_CALLER_VIDT:
		case coq_FAIL_CALLER_CONTEXT_SAVE:
			if (rc == coq_FAIL_UNAVAILABLE_CALLER_VIDT) {
				DEBUG(INFO, "Faulting partition's VIDT is unavailable, can not salvage its context\n");
			}
			else {// (rc == coq_CALLER_CONTEXT_SAVE)
				DEBUG(INFO, "Faulting partition's context save address is not valid, can not salvage its context\n");
			}
			DEBUG(TRACE, "Skip saving the interrupted partition's context\n");
			getTargetPartVidtCont(getParent(callerPartDesc), callerPageDir, getVidtVAddr(), 0, targetInterrupt, nbL, getIndexOfAddr(getVidtVAddr(), fstLevel), flagsOnYield, flagsOnWake, 0);
			break;
		case coq_FAIL_ROOT_CALLER:
			DEBUG(CRITICAL, "Root partition faulted, guru meditation.\n");
			for(;;);
			break;
		default:
			DEBUG(CRITICAL, "Error, parent partition can not handle the fault, propagating a double fault.\n");
			// Be sure to handle the root case differently, as it has no parent
			page parentPartDesc = getParent(callerPartDesc);
			// We are still trying to save the faulting partition's context, even though it is very unlikely the partition will ever wake up again
			// TODO is it worth a try ?
			propagateFault(parentPartDesc, callerPageDir, DOUBLE_FAULT_LEVEL, callerContextSaveIndex, nbL, flagsOnYield, flagsOnWake, callerInterruptedContext);
			break;
	}
}

/**
 * \struct idt_callback_conf_s
 * Holds the different parameters for each entry of the IDT
 * These will be copied as an INTERRUPT gate into the IDT
 * \seealso Intel 64 and IA-32 Architectures Software Developer's Manual - Vol. 3a - Fig 6-2.
 */
struct idt_callback_conf_s {
	callback_t callback; //<! offset to segment base address for IRQ handlers
	uint16_t    segment; //<! base address for IRQ handlers
	uint8_t         dpl; //<! descriptor privilege level
	/* only 2 bits for dpl, but the associated struct are bit fields
	 * structs and will truncate the most significant bits - hopefully */
};

#define IRQ_CODE_SEGMENT KERNEL_CODE_SEGMENT_SELECTOR //Kernel code segment in GDT (2nd entry)

/**
 * Some segment selector stuff :
 * - Faults are in kernel ring, because we won't explicitely trigger them from userland.
 * - But pipcalls may be triggered on purpose from userland (well, they should always be, in fact), so the other handlers' ring is USER (3).
*/

/**
 * \brief IRQ callbacks, privilege, and segment table
 * This table associates IRQ numbers to handlers, as well as their privilege level and their segment (configured in the GDT).
 */
static struct idt_callback_conf_s idt_callbacks[256] = {

	/* Intel reserved interrupts, triggered by CPU faults */

	[0]   = {fault_DE_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - DE : Divide Error
	[1]   = {fault_DB_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - DB : Debug Exception
	[2]   = {fault_NMI_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved -    : NMI Interrupt
	[3]   = {fault_BP_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - BP : Breakpoint
	[4]   = {fault_OF_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - OF : Overflow
	[5]   = {fault_BR_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - BR : BOUND Range Exceeded
	[6]   = {fault_UD_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - UD : Invalid Opcode
	[7]   = {fault_NM_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - NM : Device Not Available
	[8]   = {fault_DF_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - DF : Double Fault
	[9]   = {fault_CSO_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved -    : Coprocessor Segment Overrun
	[10]  = {fault_TS_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - TS : Invalid TSS
	[11]  = {fault_NP_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - NP : Segment Not Present
	[12]  = {fault_SS_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - SS : Stack-Segment Fault
	[13]  = {fault_GP_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - GP : General Protection
	[14]  = {fault_PF_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - PF : Page Fault
	[15]  = {fault_RES_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[16]  = {fault_MF_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - MF : x87 FPU Floating-Point Error
	[17]  = {fault_AC_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - AC : Alignment Check
	[18]  = {fault_MC_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - MC : Machine Check
	[19]  = {fault_XM_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - XM : SIMD Floating-Point Exception
	[20]  = {fault_VE_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - VE : Virtualization Exception
	[21]  = {fault_RES_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[22]  = {fault_RES_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[23]  = {fault_RES_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[24]  = {fault_RES_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[25]  = {fault_RES_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[26]  = {fault_RES_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[27]  = {fault_RES_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[28]  = {fault_RES_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[29]  = {fault_RES_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[30]  = {fault_RES_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[31]  = {fault_RES_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU

	/* Interrupt generated by the PIC 8259 
	 * These were remapped to this range (32-47) in remapIRQ */

	[32]  = {hardware_ALRM_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Timer Interrupt
	[33]  = {hardware_KEYB_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Keyboard Interrupt
	[34]  = {hardware_CASC_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Cascade (used internally by the two PICs. never raised)
	[35]  = {hardware_COM2_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // COM2
	[36]  = {hardware_COM1_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // COM1
	[37]  = {hardware_LPT2_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // LPT2
	[38]  = {hardware_FLPD_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Floppy Disk
	[39]  = {hardware_SPUR_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // LPT1 / "spurious" interrupt
	[40]  = {hardware_RTC_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // CMOS real-time clock
	[41]  = {hardware_PER1_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Free for peripherals / legacy SCSI / NIC
	[42]  = {hardware_PER2_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Free for peripherals / SCSI / NIC
	[43]  = {hardware_PER3_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // Free for peripherals / SCSI / NIC
	[44]  = {hardware_PS2M_asm, IRQ_CODE_SEGMENT, KERNEL_RING}, // PS2 Mouse
	[45]  = {hardware_FPU_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // FPU / Coprocessor / Inter-processor
	[46]  = {hardware_PHD_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Primary ATA Hard Disk
	[47]  = {hardware_SHD_asm,  IRQ_CODE_SEGMENT, KERNEL_RING}, // Secondary ATA Hard Disk

	/* Free to use, general purpose handlers */

	[48]  = {software_48_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[49]  = {software_49_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[50]  = {software_50_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[51]  = {software_51_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[52]  = {software_52_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[53]  = {software_53_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[54]  = {software_54_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[55]  = {software_55_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[56]  = {software_56_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[57]  = {software_57_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[58]  = {software_58_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[59]  = {software_59_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[60]  = {software_60_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[61]  = {software_61_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[62]  = {software_62_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[63]  = {software_63_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[64]  = {software_64_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[65]  = {software_65_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[66]  = {software_66_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[67]  = {software_67_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[68]  = {software_68_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[69]  = {software_69_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[70]  = {software_70_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[71]  = {software_71_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[72]  = {software_72_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[73]  = {software_73_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[74]  = {software_74_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[75]  = {software_75_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[76]  = {software_76_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[77]  = {software_77_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[78]  = {software_78_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[79]  = {software_79_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[80]  = {software_80_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[81]  = {software_81_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[82]  = {software_82_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[83]  = {software_83_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[84]  = {software_84_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[85]  = {software_85_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[86]  = {software_86_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[87]  = {software_87_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[88]  = {software_88_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[89]  = {software_89_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[90]  = {software_90_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[91]  = {software_91_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[92]  = {software_92_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[93]  = {software_93_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[94]  = {software_94_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[95]  = {software_95_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[96]  = {software_96_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[97]  = {software_97_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[98]  = {software_98_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[99]  = {software_99_asm,  IRQ_CODE_SEGMENT, USER_RING},
	[100] = {software_100_asm, IRQ_CODE_SEGMENT, USER_RING},
	[101] = {software_101_asm, IRQ_CODE_SEGMENT, USER_RING},
	[102] = {software_102_asm, IRQ_CODE_SEGMENT, USER_RING},
	[103] = {software_103_asm, IRQ_CODE_SEGMENT, USER_RING},
	[104] = {software_104_asm, IRQ_CODE_SEGMENT, USER_RING},
	[105] = {software_105_asm, IRQ_CODE_SEGMENT, USER_RING},
	[106] = {software_106_asm, IRQ_CODE_SEGMENT, USER_RING},
	[107] = {software_107_asm, IRQ_CODE_SEGMENT, USER_RING},
	[108] = {software_108_asm, IRQ_CODE_SEGMENT, USER_RING},
	[109] = {software_109_asm, IRQ_CODE_SEGMENT, USER_RING},
	[110] = {software_110_asm, IRQ_CODE_SEGMENT, USER_RING},
	[111] = {software_111_asm, IRQ_CODE_SEGMENT, USER_RING},
	[112] = {software_112_asm, IRQ_CODE_SEGMENT, USER_RING},
	[113] = {software_113_asm, IRQ_CODE_SEGMENT, USER_RING},
	[114] = {software_114_asm, IRQ_CODE_SEGMENT, USER_RING},
	[115] = {software_115_asm, IRQ_CODE_SEGMENT, USER_RING},
	[116] = {software_116_asm, IRQ_CODE_SEGMENT, USER_RING},
	[117] = {software_117_asm, IRQ_CODE_SEGMENT, USER_RING},
	[118] = {software_118_asm, IRQ_CODE_SEGMENT, USER_RING},
	[119] = {software_119_asm, IRQ_CODE_SEGMENT, USER_RING},
	[120] = {software_120_asm, IRQ_CODE_SEGMENT, USER_RING},
	[121] = {software_121_asm, IRQ_CODE_SEGMENT, USER_RING},
	[122] = {software_122_asm, IRQ_CODE_SEGMENT, USER_RING},
	[123] = {software_123_asm, IRQ_CODE_SEGMENT, USER_RING},
	[124] = {software_124_asm, IRQ_CODE_SEGMENT, USER_RING},
	[125] = {software_125_asm, IRQ_CODE_SEGMENT, USER_RING},
	[126] = {software_126_asm, IRQ_CODE_SEGMENT, USER_RING},
	[127] = {software_127_asm, IRQ_CODE_SEGMENT, USER_RING},
	[128] = {software_128_asm, IRQ_CODE_SEGMENT, USER_RING},
	[129] = {software_129_asm, IRQ_CODE_SEGMENT, USER_RING},
	[130] = {software_130_asm, IRQ_CODE_SEGMENT, USER_RING},
	[131] = {software_131_asm, IRQ_CODE_SEGMENT, USER_RING},
	[132] = {software_132_asm, IRQ_CODE_SEGMENT, USER_RING},
	[133] = {software_133_asm, IRQ_CODE_SEGMENT, USER_RING},
	[134] = {software_134_asm, IRQ_CODE_SEGMENT, USER_RING},
	[135] = {software_135_asm, IRQ_CODE_SEGMENT, USER_RING},
	[136] = {software_136_asm, IRQ_CODE_SEGMENT, USER_RING},
	[137] = {software_137_asm, IRQ_CODE_SEGMENT, USER_RING},
	[138] = {software_138_asm, IRQ_CODE_SEGMENT, USER_RING},
	[139] = {software_139_asm, IRQ_CODE_SEGMENT, USER_RING},
	[140] = {software_140_asm, IRQ_CODE_SEGMENT, USER_RING},
	[141] = {software_141_asm, IRQ_CODE_SEGMENT, USER_RING},
	[142] = {software_142_asm, IRQ_CODE_SEGMENT, USER_RING},
	[143] = {software_143_asm, IRQ_CODE_SEGMENT, USER_RING},
	[144] = {software_144_asm, IRQ_CODE_SEGMENT, USER_RING},
	[145] = {software_145_asm, IRQ_CODE_SEGMENT, USER_RING},
	[146] = {software_146_asm, IRQ_CODE_SEGMENT, USER_RING},
	[147] = {software_147_asm, IRQ_CODE_SEGMENT, USER_RING},
	[148] = {software_148_asm, IRQ_CODE_SEGMENT, USER_RING},
	[149] = {software_149_asm, IRQ_CODE_SEGMENT, USER_RING},
	[150] = {software_150_asm, IRQ_CODE_SEGMENT, USER_RING},
	[151] = {software_151_asm, IRQ_CODE_SEGMENT, USER_RING},
	[152] = {software_152_asm, IRQ_CODE_SEGMENT, USER_RING},
	[153] = {software_153_asm, IRQ_CODE_SEGMENT, USER_RING},
	[154] = {software_154_asm, IRQ_CODE_SEGMENT, USER_RING},
	[155] = {software_155_asm, IRQ_CODE_SEGMENT, USER_RING},
	[156] = {software_156_asm, IRQ_CODE_SEGMENT, USER_RING},
	[157] = {software_157_asm, IRQ_CODE_SEGMENT, USER_RING},
	[158] = {software_158_asm, IRQ_CODE_SEGMENT, USER_RING},
	[159] = {software_159_asm, IRQ_CODE_SEGMENT, USER_RING},
	[160] = {software_160_asm, IRQ_CODE_SEGMENT, USER_RING},
	[161] = {software_161_asm, IRQ_CODE_SEGMENT, USER_RING},
	[162] = {software_162_asm, IRQ_CODE_SEGMENT, USER_RING},
	[163] = {software_163_asm, IRQ_CODE_SEGMENT, USER_RING},
	[164] = {software_164_asm, IRQ_CODE_SEGMENT, USER_RING},
	[165] = {software_165_asm, IRQ_CODE_SEGMENT, USER_RING},
	[166] = {software_166_asm, IRQ_CODE_SEGMENT, USER_RING},
	[167] = {software_167_asm, IRQ_CODE_SEGMENT, USER_RING},
	[168] = {software_168_asm, IRQ_CODE_SEGMENT, USER_RING},
	[169] = {software_169_asm, IRQ_CODE_SEGMENT, USER_RING},
	[170] = {software_170_asm, IRQ_CODE_SEGMENT, USER_RING},
	[171] = {software_171_asm, IRQ_CODE_SEGMENT, USER_RING},
	[172] = {software_172_asm, IRQ_CODE_SEGMENT, USER_RING},
	[173] = {software_173_asm, IRQ_CODE_SEGMENT, USER_RING},
	[174] = {software_174_asm, IRQ_CODE_SEGMENT, USER_RING},
	[175] = {software_175_asm, IRQ_CODE_SEGMENT, USER_RING},
	[176] = {software_176_asm, IRQ_CODE_SEGMENT, USER_RING},
	[177] = {software_177_asm, IRQ_CODE_SEGMENT, USER_RING},
	[178] = {software_178_asm, IRQ_CODE_SEGMENT, USER_RING},
	[179] = {software_179_asm, IRQ_CODE_SEGMENT, USER_RING},
	[180] = {software_180_asm, IRQ_CODE_SEGMENT, USER_RING},
	[181] = {software_181_asm, IRQ_CODE_SEGMENT, USER_RING},
	[182] = {software_182_asm, IRQ_CODE_SEGMENT, USER_RING},
	[183] = {software_183_asm, IRQ_CODE_SEGMENT, USER_RING},
	[184] = {software_184_asm, IRQ_CODE_SEGMENT, USER_RING},
	[185] = {software_185_asm, IRQ_CODE_SEGMENT, USER_RING},
	[186] = {software_186_asm, IRQ_CODE_SEGMENT, USER_RING},
	[187] = {software_187_asm, IRQ_CODE_SEGMENT, USER_RING},
	[188] = {software_188_asm, IRQ_CODE_SEGMENT, USER_RING},
	[189] = {software_189_asm, IRQ_CODE_SEGMENT, USER_RING},
	[190] = {software_190_asm, IRQ_CODE_SEGMENT, USER_RING},
	[191] = {software_191_asm, IRQ_CODE_SEGMENT, USER_RING},
	[192] = {software_192_asm, IRQ_CODE_SEGMENT, USER_RING},
	[193] = {software_193_asm, IRQ_CODE_SEGMENT, USER_RING},
	[194] = {software_194_asm, IRQ_CODE_SEGMENT, USER_RING},
	[195] = {software_195_asm, IRQ_CODE_SEGMENT, USER_RING},
	[196] = {software_196_asm, IRQ_CODE_SEGMENT, USER_RING},
	[197] = {software_197_asm, IRQ_CODE_SEGMENT, USER_RING},
	[198] = {software_198_asm, IRQ_CODE_SEGMENT, USER_RING},
	[199] = {software_199_asm, IRQ_CODE_SEGMENT, USER_RING},
	[200] = {software_200_asm, IRQ_CODE_SEGMENT, USER_RING},
	[201] = {software_201_asm, IRQ_CODE_SEGMENT, USER_RING},
	[202] = {software_202_asm, IRQ_CODE_SEGMENT, USER_RING},
	[203] = {software_203_asm, IRQ_CODE_SEGMENT, USER_RING},
	[204] = {software_204_asm, IRQ_CODE_SEGMENT, USER_RING},
	[205] = {software_205_asm, IRQ_CODE_SEGMENT, USER_RING},
	[206] = {software_206_asm, IRQ_CODE_SEGMENT, USER_RING},
	[207] = {software_207_asm, IRQ_CODE_SEGMENT, USER_RING},
	[208] = {software_208_asm, IRQ_CODE_SEGMENT, USER_RING},
	[209] = {software_209_asm, IRQ_CODE_SEGMENT, USER_RING},
	[210] = {software_210_asm, IRQ_CODE_SEGMENT, USER_RING},
	[211] = {software_211_asm, IRQ_CODE_SEGMENT, USER_RING},
	[212] = {software_212_asm, IRQ_CODE_SEGMENT, USER_RING},
	[213] = {software_213_asm, IRQ_CODE_SEGMENT, USER_RING},
	[214] = {software_214_asm, IRQ_CODE_SEGMENT, USER_RING},
	[215] = {software_215_asm, IRQ_CODE_SEGMENT, USER_RING},
	[216] = {software_216_asm, IRQ_CODE_SEGMENT, USER_RING},
	[217] = {software_217_asm, IRQ_CODE_SEGMENT, USER_RING},
	[218] = {software_218_asm, IRQ_CODE_SEGMENT, USER_RING},
	[219] = {software_219_asm, IRQ_CODE_SEGMENT, USER_RING},
	[220] = {software_220_asm, IRQ_CODE_SEGMENT, USER_RING},
	[221] = {software_221_asm, IRQ_CODE_SEGMENT, USER_RING},
	[222] = {software_222_asm, IRQ_CODE_SEGMENT, USER_RING},
	[223] = {software_223_asm, IRQ_CODE_SEGMENT, USER_RING},
	[224] = {software_224_asm, IRQ_CODE_SEGMENT, USER_RING},
	[225] = {software_225_asm, IRQ_CODE_SEGMENT, USER_RING},
	[226] = {software_226_asm, IRQ_CODE_SEGMENT, USER_RING},
	[227] = {software_227_asm, IRQ_CODE_SEGMENT, USER_RING},
	[228] = {software_228_asm, IRQ_CODE_SEGMENT, USER_RING},
	[229] = {software_229_asm, IRQ_CODE_SEGMENT, USER_RING},
	[230] = {software_230_asm, IRQ_CODE_SEGMENT, USER_RING},
	[231] = {software_231_asm, IRQ_CODE_SEGMENT, USER_RING},
	[232] = {software_232_asm, IRQ_CODE_SEGMENT, USER_RING},
	[233] = {software_233_asm, IRQ_CODE_SEGMENT, USER_RING},
	[234] = {software_234_asm, IRQ_CODE_SEGMENT, USER_RING},
	[235] = {software_235_asm, IRQ_CODE_SEGMENT, USER_RING},
	[236] = {software_236_asm, IRQ_CODE_SEGMENT, USER_RING},
	[237] = {software_237_asm, IRQ_CODE_SEGMENT, USER_RING},
	[238] = {software_238_asm, IRQ_CODE_SEGMENT, USER_RING},
	[239] = {software_239_asm, IRQ_CODE_SEGMENT, USER_RING},
	[240] = {software_240_asm, IRQ_CODE_SEGMENT, USER_RING},
	[241] = {software_241_asm, IRQ_CODE_SEGMENT, USER_RING},
	[242] = {software_242_asm, IRQ_CODE_SEGMENT, USER_RING},
	[243] = {software_243_asm, IRQ_CODE_SEGMENT, USER_RING},
	[244] = {software_244_asm, IRQ_CODE_SEGMENT, USER_RING},
	[245] = {software_245_asm, IRQ_CODE_SEGMENT, USER_RING},
	[246] = {software_246_asm, IRQ_CODE_SEGMENT, USER_RING},
	[247] = {software_247_asm, IRQ_CODE_SEGMENT, USER_RING},
	[248] = {software_248_asm, IRQ_CODE_SEGMENT, USER_RING},
	[249] = {software_249_asm, IRQ_CODE_SEGMENT, USER_RING},
	[250] = {software_250_asm, IRQ_CODE_SEGMENT, USER_RING},
	[251] = {software_251_asm, IRQ_CODE_SEGMENT, USER_RING},
	[252] = {software_252_asm, IRQ_CODE_SEGMENT, USER_RING},
	[253] = {software_253_asm, IRQ_CODE_SEGMENT, USER_RING},
	[254] = {software_254_asm, IRQ_CODE_SEGMENT, USER_RING},
	[255] = {software_255_asm, IRQ_CODE_SEGMENT, USER_RING},
};


/**
 * \brief IDT interrupt entry initializer.
 * \seealso idt_int_trap_entry_t
 * Notice that the only difference with the IDT_TRAP_ENTRY macro is the type field
 */
#define IDT_INTERRUPT_ENTRY(callback_index) (idt_entry_t) {                              \
	.interrupt = {                                                                   \
		(((uint32_t) idt_callbacks[callback_index].callback) & 0xFFFF),          \
		(idt_callbacks[callback_index].segment),                                 \
		0,                                                                       \
		0,                                                                       \
		(INTERRUPT_GATE_TYPE),                                                   \
		(idt_callbacks[callback_index].dpl),                                     \
		1,                                                                       \
		((((uint32_t) idt_callbacks[callback_index].callback) >> 16) & 0xFFFF)   \
	}                                                                                \
}

/**
 * \brief IDT trap entry initializer.
 * \seealso idt_int_trap_entry_t
 * Notice that the only difference with the IDT_INTERRUPT_ENTRY macro is the type field
 * Trap gates do not clear the interrupt flag when accessed
 */
#define IDT_TRAP_ENTRY(callback_index) (idt_entry_t) {                                 \
	.trap = {                                                                      \
		(((uint32_t) idt_callbacks[callback_index].callback) & 0xFFFF),        \
		(idt_callbacks[callback_index].segment),                               \
		0,                                                                     \
		0,                                                                     \
		TRAP_GATE_TYPE,                                                        \
		idt_callbacks[callback_index].dpl,                                     \
		1,                                                                     \
		((((uint32_t) idt_callbacks[callback_index].callback) >> 16) & 0xFFFF) \
	}                                                                              \
}

/**
 * Interrupt Descriptor Table
 * \seealso Intel 64 and IA-32 Architectures Software Developer's Manual - Volume 3a - 6.10
 */
static idt_entry_t idt_entries[256];

/**
 * Dynamic initialization of the IDT
 * could be done statically through some obscure relative address black magic
 * \seealso "https://wiki.osdev.org/IDT_problems#what_does_.22shift_operator_may_only_be_applied_to_scalar_values.22_mean.3F"
 */
void initIDT(void) {
	DEBUG(TRACE, "Initializing the IDT...\n");

	unsigned int idt_index;
	idt_ptr_t idt_ptr;		//!< Pointer to the IDT
	idt_ptr.base = idt_entries;
	idt_ptr.limit = 256 * sizeof(idt_entry_t) - 1;

	for (idt_index = 0  ; idt_index <  256 ; idt_index++) {
		idt_entries[idt_index] = IDT_INTERRUPT_ENTRY(idt_index);
	}
	DEBUG(TRACE, "Done initializing the IDT structure, now loading the IDT\n");

	asm("lidt (%0)"::"r"(&idt_ptr));
	DEBUG(TRACE, "Done loading IDT\n")
}

/**
 * \fn remapIrq
 * \brief Remaps IRQ from int. 0-15 to int. 32-47
 * \seealso Intel 64 and IA-32 Architectures Software Develeoper's Manual : Volume 3a - 6.2
 *
 * Vector numbers in the range 0 through 31 are reserved by the Intel 64 and IA-32
 * architectures for architecture-defined exceptions and interrupts. Not all of the vector
 * numbers in this range have a currently defined function. The unassigned vector numbers in
 * this range are reserved. Do not use the reserved vector numbers. See table 6-1 for details.
 */
void
remapIRQ (void)
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
	uint32_t divisor = 2600000 / hz;
	if (divisor > 0xffff) divisor = 0xffff;
	if (divisor < 1) divisor = 1;
	
	outb (0x43, 0x36);              /* Set our command byte 0x36 */
	outb (0x40, divisor & 0xFF);    /* Set low byte of divisor */
	outb (0x40, divisor >> 8);      /* Set high byte of divisor */
	
	DEBUG (INFO, "Timer phase changed to %d hz\n", hz);
}

uint32_t pcid_enabled = 0;

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

/**
 * \fn void initCpu()
 * \brief Initializes CPU-specific features
 */
void initCPU()
{
	DEBUG(CRITICAL, "Identifying CPU model and features...\n");
	
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
	
	DEBUG(CRITICAL, "CPU identification: %s\n", cpuident);
	
	/* Processor brand */
	cpuid_string(CPUID_INTELBRANDSTRING, (uint32_t*)cpubrand);
	cpuid_string(CPUID_INTELBRANDSTRINGMORE, (uint32_t*)&cpubrand[16]);
	cpuid_string(CPUID_INTELBRANDSTRINGEND, (uint32_t*)&cpubrand[32]);
	cpubrand[48] = '\n';
	DEBUG(CRITICAL, "CPU brand: %s\n", cpubrand);
	
	/* Check whether PCID is supported as well as PGE */
	uint32_t ecx, edx;
	cpuid(CPUID_GETFEATURES, &ecx, &edx);
	uint32_t cr4;
	
	/* PGE check */
	if(edx & CPUID_FEAT_EDX_PGE)
	{
		DEBUG(CRITICAL, "PGE supported, enabling CR4.PGE\n");
		asm volatile("MOV %%CR4, %0" : "=r"(cr4));
		cr4 |= (1 << 7); /* Enable Page Global as well */
		asm volatile("MOV %0, %%CR4" :: "r"(cr4));
	} else {
		DEBUG(CRITICAL, "PGE unsupported, Global Page feature will be unavailable\n");
	}
	
	/* PCID check */
	if(ecx & CPUID_FEAT_ECX_PCID)
	{
		DEBUG(CRITICAL, "PCID supported, enabling CR4.PCIDE\n");
		pcid_enabled = 1;
		
		/* Enable PCID */
		asm volatile("MOV %%CR4, %0" : "=r"(cr4));
		cr4 |= (1 << 17);
		asm volatile("MOV %0, %%CR4" :: "r"(cr4));
	} else {
		DEBUG(CRITICAL, "PCID unsupported, Process Context Identifiers feature will be unavailable\n");
	}
}

uint32_t timer_ticks = 0;

void idt_init(void) {
	DEBUG(INFO, "Initializing interrupts\n");
	initIDT();
	remapIRQ();
	timerPhase(100);
	timer_ticks = 0;
	initCPU();
	DEBUG(INFO, "Done initializing interrupts\n");
}
