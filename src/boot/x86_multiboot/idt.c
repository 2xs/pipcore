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

#include "idt.h"
#include "port.h"
#include "pic8259.h"
#include "debug.h"
#include "libc.h"

/**
 * IRQ C handlers and declaration of their assembly counterparts
 * \seealso irq.s file for assembly wrappers
 * /!\ Defining an assembly wrapper is mandatory for each handler /!\
 */
extern void irq_unsupported(void);
extern void irq_timer(void);
extern void irq_test(void);

void unsupportedHandler(void *ctx) {
	DEBUG(TRACE, "Unsupported IRQ !\n");
	while(1);
}

void timerHandler(void *ctx) {
	outb (PIC1_COMMAND, PIC_EOI); // interrupt acknowledgment
	outb (PIC2_COMMAND, PIC_EOI); // interrupt acknowledgment
	DEBUG(TRACE, "Interrupted by alarm !\n");
}

void testHandler(void *ctx) {
	outb (PIC1_COMMAND, PIC_EOI); // interrupt acknowledgment
	outb (PIC2_COMMAND, PIC_EOI); // interrupt acknowledgment
	DEBUG(TRACE, "Hello from testHandler !\n");
}

/**
 * \brief Type of callback functions (IRQ handlers)
 * No return value, and no arguments
 */
typedef void (*callback_t)(void);

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

#define IRQ_CODE_SEGMENT (0x08) //Kernel code segment in GDT (2nd entry)

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
	[0]   = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - DE : Divide Error
	[1]   = {irq_test       , IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - DB : Debug Exception
	[2]   = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved -    : NMI Interrupt
	[3]   = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - BP : Breakpoint
	[4]   = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - OF : Overflow
	[5]   = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - BR : BOUND Range Exceeded
	[6]   = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - UD : Invalid Opcode
	[7]   = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - NM : Device Not Available
	[8]   = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - DF : Double Fault
	[9]   = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved -    : Coprocessor Segment Overrun
	[10]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - TS : Invalid TSS
	[11]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - NP : Segment Not Present
	[12]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - SS : Stack-Segment Fault
	[13]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - GP : General Protection
	[14]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - PF : Page Fault
	[15]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[16]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - MF : x87 FPU Floating-Point Error
	[17]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - AC : Alignment Check
	[18]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - MC : Machine Check
	[19]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - XM : SIMD Floating-Point Exception
	[20]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved - VE : Virtualization Exception
	[21]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[22]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[23]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[24]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[25]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[26]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[27]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[28]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[29]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[30]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[31]  = {irq_unsupported, IRQ_CODE_SEGMENT, KERNEL_RING}, // Intel Reserved ------ RFU
	[32]  = {irq_timer      , IRQ_CODE_SEGMENT, USER_RING},
	[33]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[34]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[35]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[36]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[37]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[38]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[39]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[40]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[41]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[42]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[43]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[44]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[45]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[46]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[47]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[48]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[49]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[50]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[51]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[52]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[53]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[54]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[55]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[56]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[57]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[58]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[59]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[60]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[61]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[62]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[63]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[64]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[65]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[66]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[67]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[68]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[69]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[70]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[71]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[72]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[73]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[74]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[75]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[76]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[77]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[78]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[79]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[80]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[81]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[82]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[83]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[84]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[85]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[86]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[87]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[88]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[89]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[90]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[91]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[92]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[93]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[94]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[95]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[96]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[97]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[98]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[99]  = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[100] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[101] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[102] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[103] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[104] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[105] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[106] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[107] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[108] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[109] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[110] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[111] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[112] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[113] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[114] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[115] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[116] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[117] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[118] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[119] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[120] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[121] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[122] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[123] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[124] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[125] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[126] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[127] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[128] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[129] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[130] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[131] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[132] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[133] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[134] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[135] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[136] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[137] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[138] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[139] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[140] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[141] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[142] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[143] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[144] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[145] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[146] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[147] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[148] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[149] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[150] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[151] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[152] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[153] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[154] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[155] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[156] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[157] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[158] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[159] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[160] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[161] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[162] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[163] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[164] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[165] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[166] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[167] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[168] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[169] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[170] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[171] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[172] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[173] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[174] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[175] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[176] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[177] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[178] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[179] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[180] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[181] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[182] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[183] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[184] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[185] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[186] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[187] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[188] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[189] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[190] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[191] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[192] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[193] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[194] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[195] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[196] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[197] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[198] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[199] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[200] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[201] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[202] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[203] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[204] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[205] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[206] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[207] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[208] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[209] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[210] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[211] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[212] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[213] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[214] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[215] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[216] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[217] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[218] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[219] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[220] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[221] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[222] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[223] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[224] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[225] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[226] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[227] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[228] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[229] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[230] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[231] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[232] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[233] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[234] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[235] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[236] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[237] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[238] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[239] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[240] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[241] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[242] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[243] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[244] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[245] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[246] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[247] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[248] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[249] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[250] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[251] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[252] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[253] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[254] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING},
	[255] = {irq_unsupported, IRQ_CODE_SEGMENT, USER_RING}
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
	BOOT_DEBUG(TRACE, "Done initializing the IDT structure, now loading the IDT\n");

	asm("lidt (%0)"::"r"(&idt_ptr));
	BOOT_DEBUG(TRACE, "Done loading IDT\n")
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
	
	BOOT_DEBUG (INFO, "Timer phase changed to %d hz\n", hz);
}

uint32_t pcid_enabled = 0;

/**
 * \fn void initCpu()
 * \brief Initializes CPU-specific features
 */
void initCPU()
{
	BOOT_DEBUG(CRITICAL, "Identifying CPU model and features...\n");
	
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
	
	BOOT_DEBUG(CRITICAL, "CPU identification: %s\n", cpuident);
	
	/* Processor brand */
	cpuid_string(CPUID_INTELBRANDSTRING, (uint32_t*)cpubrand);
	cpuid_string(CPUID_INTELBRANDSTRINGMORE, (uint32_t*)&cpubrand[16]);
	cpuid_string(CPUID_INTELBRANDSTRINGEND, (uint32_t*)&cpubrand[32]);
	cpubrand[48] = '\n';
	BOOT_DEBUG(CRITICAL, "CPU brand: %s\n", cpubrand);
	
	/* Check whether PCID is supported as well as PGE */
	uint32_t ecx, edx;
	cpuid(CPUID_GETFEATURES, &ecx, &edx);
	uint32_t cr4;
	
	/* PGE check */
	if(edx & CPUID_FEAT_EDX_PGE)
	{
		BOOT_DEBUG(CRITICAL, "PGE supported, enabling CR4.PGE\n");
		__asm volatile("MOV %%CR4, %0" : "=r"(cr4));
		cr4 |= (1 << 7); /* Enable Page Global as well */
		__asm volatile("MOV %0, %%CR4" :: "r"(cr4));
	} else {
		BOOT_DEBUG(CRITICAL, "PGE unsupported, Global Page feature will be unavailable\n");
	}
	
	/* PCID check */
	if(ecx & CPUID_FEAT_ECX_PCID)
	{
		BOOT_DEBUG(CRITICAL, "PCID supported, enabling CR4.PCIDE\n");
		pcid_enabled = 1;
		
		/* Enable PCID */
		__asm volatile("MOV %%CR4, %0" : "=r"(cr4));
		cr4 |= (1 << 17);
		__asm volatile("MOV %0, %%CR4" :: "r"(cr4));
	} else {
		BOOT_DEBUG(CRITICAL, "PCID unsupported, Process Context Identifiers feature will be unavailable\n");
	}
}

uint32_t timer_ticks = 0;

void initInterrupts(void) {
	BOOT_DEBUG(INFO, "Initializing interrupts\n");
	initIDT();
	remapIRQ();
	timerPhase(100);
	timer_ticks = 0;
	initCPU();
	BOOT_DEBUG(INFO, "Done initializing interrupts\n");
	BOOT_DEBUG(TRACE, "Calling int 1\n");
	asm("int $0x1");
	BOOT_DEBUG(TRACE, "Returned from int 1\n");
}
