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

/**
 * \brief IDT entry initializer
 * \seealso idt_entry_t
 */
#define IDT_ENTRY(entrypoint, segment_selector, flags) {         \
	(uint16_t) (((uint32_t) (entrypoint)) & 0xFFFF),         \
	((uint16_t) (segment_selector)),                         \
	0,                                                       \
	(flags),                                                 \
	(uint16_t) ((((uint32_t) (entrypoint)) >> 16) & 0xFFFF)  \
}

/**
 * Contructs an IDT entry flag with a given ring level privilege
 * \seealso Intel Software Developer's Manual - Volume 3a Chapter 5 Figure 5-2 
 * segment present flag: 1
 * gate size: 32
 *
 * Some segment selector stuff :
 * - Faults are in kernel level, flag is then 0x8E, because we won't explicitely trigger them from userland.
 * - But pipcalls may be triggered on purpose from userland (well, they sould always be, in fact), so our flags are 0xEE.
*/
#define IDT_FLAGS(ring) (0x8E | (((ring) & 0x3) << 5))
#define IDT_KERNEL_FLAGS (IDT_FLAGS(0))
#define IDT_USER_FLAGS (IDT_FLAGS(3))

#define IRQ_CODE_SEGMENT (0x08)

extern void irq_unsupported();

/**
 * Interrupt Descriptor Table
 * \seealso Intel Software Developer's Manual - Volume 3a Chapter 5
 */
static idt_entry_t idt_entries[256] = {
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_KERNEL_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS),
       IDT_ENTRY(irq_unsupported, IRQ_CODE_SEGMENT, IDT_USER_FLAGS)
};

static idt_ptr_t idt_ptr;		//!< Pointer to the IDT
