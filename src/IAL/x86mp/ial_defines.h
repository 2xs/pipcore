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

#ifndef __IAL_DEFINES__
#define __IAL_DEFINES__

#define IAL_PREFIX				"みちる"
#define IAL_VERSION				"0.1"

#define SIZEOF_CTX				sizeof(int_ctx_t)
#define GENERAL_REG(a, c)		a->regs.c
#define OPTIONAL_REG(a, c)		a->c

#define PIPFLAGS				((uintptr_t*)(VIDT + 0xFFC))
#define INTLEVEL_GET			(*PIPFLAGS & 0xFFFFFF00) >> 8
#define INTLEVEL_SET(a)			*PIPFLAGS = (*PIPFLAGS & 0xFFFFFF00) | (a << 8)
#define VIDT_VCLI				*PIPFLAGS & 0x00000001


#define VIDT_CTX_BUFFER			(int_ctx_t*)(PIPFLAGS - SIZEOF_CTX)
#define INT_IRQ(a)				(a >= 32 && a <= 47)

#define PARTITION_PARENT		0
#define PARTITION_ROOT			getRootPartition()
#define PARTITION_CURRENT		getCurPartition()

#define VIDT					(IS_MPMT ? (0xFFFFF000 - 0x1000 * coreId()) : 0xFFFFF000)
#define VIDT_INT_EIP(a)			readTableVirtualNoFlags (VIDT, (2 * a))
#define VIDT_INT_ESP(a)			readTableVirtualNoFlags (VIDT, (2 * a) + 1)
#define VIDT_INT_ESP_SET(a,s)	writeTableVirtualNoFlags (VIDT, (2 * a) + 1, s)
#endif
