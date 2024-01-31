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

#ifndef DEF_PERIPH_H_
#define DEF_PERIPH_H_

#include "types.h"
#include "machine.h"

#define PERIPH_RBASE (io_remapped ? PERIPH_VBASE : PERIPH_BASE)

#define CORE0_IRQ_SOURCE        ((uint32_t *) 0x40000060)
#define LOCAL_TIMER_WRITE_FLAGS ((uint32_t *) 0x40000038)

#define IRQ2836_CONTROL               0
#define IRQ2836_TIMER_PRESCALER	      0x8
#define IRQ2836_GPU_ROUTING           0xC
#define IRQ2836_PMU_ROUTING_SET	      0x10
#define IRQ2836_PMU_ROUTING_CLR	      0x14
#define IRQ2836_CORE_TIMER_LOW        0x1C
#define IRQ2836_CORE_TIMER_HIGH       0x20
#define IRQ2836_LOCAL_INT_ROUTING     0x24
#define IRQ2836_AXI_OUTSTD_CTR        0x2C
#define IRQ2836_AXI_OUTSTD_CTL        0x30
#define IRQ2836_LOCAL_TIMER_CTL       0x34
#define IRQ2836_LOCAL_TIMER_CLR_RLD   0x38
#define IRQ2836_TIMER_CTL             0x40
#define IRQ2836_MAILBOX_CTL           0x50
#define IRQ2836_IRQ_SOURCE            0x60
#define IRQ2836_FIQ_SOURCE            0x70
#define IRQ2836_MAILBOX_SET           0x80
#define IRQ2836_MAILBOX_CLR           0xC0

#define IRQ2836REG(reg)	*(unsigned int*)((IRQ2836_##reg)+PERIPH_CONTROL)

#define UART0 (PERIPH_RBASE+UART0_OFFSET)

extern bool_t io_remapped;

void periph_notify_ioremap(int v);

#endif
