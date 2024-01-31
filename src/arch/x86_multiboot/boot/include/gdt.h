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

/**
 * \file gdt.h
 * \brief Include file for GDT configuration
 */

#ifndef __GDT__
#define __GDT__

#include <stdint.h>
#include "maldefines.h"

/**
 * \struct segment_descriptor_s
 * \brief Meant to be written inside the GDT. Provides the processor with the size and location of a segment, as well as access control and status information.
 *
 * 1/ Base addresses must be 16-bits aligned to maximize performance
 * 2/ Limit field's (size of segment) behaviour depends on the granularity flag :
 *    # G = 0 => range from 1 byte to 1 MByte, in byte increments.
 *    # G = 1 => range from 4 KBytes to 4 GBytes, in 4-KByte increments.
 * 3/ The "s" field should always be 1, system segments are either
 *    LDT, TSS, Callgate, Interrupt-gate, Trap-gate, or Task-gate descriptors,
 *    which have their own structs.
 *
 * \seealso Intel 64 and IA-32 Architectures Software Developer's Manual - Vol. 3a - Sec. 3.4.5 and Fig. 3-8.
 */
struct segment_descriptor_s
{
    unsigned limit_low   : 16; //!< Lower bits of the size of the segment (bits 15..0)
    unsigned base_low    : 16; //!< Lower bits of base address (bits 15..0)
    unsigned base_middle :  8; //!< Middle bits of base address (bits 23..16)
    unsigned type        :  4; //!< See below defines
    unsigned s           :  1; //!< 0 => system segment, 1 => code or data segment (see 3/)
    unsigned dpl         :  2; //!< Descriptor privilege level
    unsigned present     :  1; //!< Preset flag (validity of descriptor)
    unsigned limit_high  :  4; //!< Higher bits of the size of the segment (bits 19..16)
    unsigned avl         :  1; //!< Available for use by system software
    unsigned l           :  1; //!< Long? flag (only useful in IA-32e) 64 bits code segment.
    unsigned d_b         :  1; //!< default operation size (0 => 16-bit, 1 => 32-bit)
    unsigned granularity :  1; //!< granularity (see 2/ in above comment)
    unsigned base_high   :  8; //!< Higher bits of base address (bits 31..24)
};

#define GRANULARITY_1    0
#define GRANULARITY_4096 1

/**
 * All the different types of segments entries
 * Last bit of the type is written every time the segment is accessed, and can be cleared
 * for debug purposes and virtual memory management (according to Intel's doc).
 *
 * \seealso Intel 64 and IA-32 Architectures Software Developer's Manual - Vol. 3a - Sec. 3.5 and Fig. 3-8
 */

#define SEG_DATA_READONLY_EXPANDUP_TYPE      0b0000
#define SEG_DATA_READWRITE_EXPANDUP_TYPE     0b0010
#define SEG_DATA_READONLY_EXPANDDOWN_TYPE    0b0100
#define SEG_DATA_READWRITE_EXPANDDOWN_TYPE   0b0110

#define SEG_CODE_EXECONLY_NONCONFORMING_TYPE 0b1000
#define SEG_CODE_EXECREAD_NONCONFORMING_TYPE 0b1010
#define SEG_CODE_EXECONLY_CONFORMING_TYPE    0b1100
#define SEG_CODE_EXECREAD_CONFORMING_TYPE    0b1110

typedef struct segment_descriptor_s segment_descriptor_t;

/**
 * \brief A callgate descriptor for the GDT/LDT
 * \seealso Intel 64 and IA-32 Architectures Software Developer's Manual - Vol. 3a - Sec. 5.8.3 and Fig. 5.8.
 */
struct callgate_descriptor_s {
	unsigned offset_low  : 16; //!< Lower bits of the entrypoint offset in segment (15..0)
	unsigned segment     : 16; //!< Code segment to be accessed
	unsigned args        :  5; //!< Number of parameters to be copied between stacks if a task switch occurs
	unsigned reserved    :  3; //!< always zero smh
	unsigned type        :  4; //!< Use GDT_CALLGATE_TYPE macro
	unsigned zero        :  1; //!< always zero smh
	unsigned dpl         :  2; //!< Descriptor Privilege Level
	unsigned present     :  1; //!< Present flag (validity of the callgate)
	unsigned offset_high : 16; //!< Higher bits of the entrypoint offset in segment (31..16)
};

#define GDT_CALLGATE_TYPE 0b1100

typedef struct callgate_descriptor_s callgate_descriptor_t;

/**
 * \seealso Intel 64 and IA-32 Architectures Software Developer's Manual - Vol. 3a - Sec. 7.2.2.
 */
struct tss_descriptor_s {
	unsigned limit_low   : 16; //<! Segment limit 15..0
	unsigned base_low    : 16; //<! Segment base address 15..0
	unsigned base_middle :  8; //<! Segment base address 23..16
	unsigned type        :  4; //<! GDT_TSS_BUSY_TYPE or GDT_TSS_INACTIVE_TYPE
	unsigned zero        :  1; //<! Always zero smh
	unsigned dpl         :  2; //<! Descriptor Privilege Level
	unsigned present     :  1; //<! Present flag (validity of descriptor)
	unsigned limit_high  :  4; //<! Segment limit 19..16
	unsigned avl         :  1; //<! Available for use by system software
	unsigned zero2       :  2; //<! Also always zero smh
	unsigned granularity :  1; //<! 0 => segment limit range from 1B to 1MB, byte per byte
                                   //<! 1 => segment limit range from 4kB to 4GB, 4kB per 4kB
                                   /*   When the G flag is 0 in a TSS descriptor for a 32-bit
				    *   TSS, the limit field must have a value equal to or
                                    *   greater than 67H, one byte less than the minimum size
                                    *   of a TSS. Otherwise, TS fault is generated.
                                    */
	unsigned base_high   :  8; //<! Segment base address 31..24
};

#define GDT_TSS_INACTIVE_TYPE 0b1001 //inactive task
#define GDT_TSS_BUSY_TYPE     0b1011 //running or suspended task (interrupted state)

typedef struct tss_descriptor_s tss_descriptor_t;

union gdt_entry {
	segment_descriptor_t segment_desc;
	callgate_descriptor_t callgate_desc;
	tss_descriptor_t tss_desc;
	uint64_t null_desc;
};

typedef union gdt_entry gdt_entry_t;

/**
 * \struct gdt_ptr
 * \brief Pointer to the GDT 
 */
struct gdt_ptr
{
    unsigned short limit; //!< Address limit
    unsigned int base; //!< Base address
} __attribute__((packed));

/**
 * \struct tss_s
 * \brief Task State Segment structure
 * \seealso 
 */
struct tss_s {
	unsigned prev_tss   : 16; //!< Pointer to the previous TSS entry (updated on a task switch)
	unsigned reserved0  : 16;
	unsigned esp0       : 32; //!< Kernel-mode ESP           (static)
	unsigned ss0        : 16; //!< Kernel-mode stack segment (static)
	unsigned reserved1  : 16;
	unsigned esp1       : 32; //!< Ring-1 ESP                (static)
	unsigned ss1        : 16; //!< Ring-1 stack segment      (static)
	unsigned reserved2  : 16;
	unsigned esp2       : 32; //!< Ring-2 ESP                (static)
	unsigned ss2        : 16; //!< Ring-2 stack segment      (static)
	unsigned reserved3  : 16;
	unsigned cr3        : 32; //!< Page directory address    (static)
	unsigned eip        : 32; //!< Execution pointer    (prior to task switch)
	unsigned eflags     : 32; //!< CPU flags            (prior to task switch)
	unsigned eax        : 32; //!< General register EAX (prior to task switch)
	unsigned ecx        : 32; //!< General register ECX (prior to task switch)
	unsigned edx        : 32; //!< General register EDX (prior to task switch)
	unsigned ebx        : 32; //!< General register EBX (prior to task switch)
	unsigned esp        : 32; //!< User-mode ESP        (prior to task switch)
	unsigned ebp        : 32; //!< User-mode EBP        (prior to task switch)
	unsigned esi        : 32; //!< General register ESI (prior to task switch)
	unsigned edi        : 32; //!< General register EDI (prior to task switch)
	unsigned es         : 16; //!< Segment selector ES  (prior to task switch)
	unsigned reserved4  : 16;
	unsigned cs         : 16; //!< Segment selector CS  (prior to task switch)
	unsigned reserved5  : 16;
	unsigned ss         : 16; //!< Segment selector SS  (prior to task switch)
	unsigned reserved6  : 16;
	unsigned ds         : 16; //!< Segment selector DS  (prior to task switch)
	unsigned reserved7  : 16;
	unsigned fs         : 16; //!< Segment selector FS  (prior to task switch)
	unsigned reserved8  : 16;
	unsigned gs         : 16; //!< Segment selector GS  (prior to task switch)
	unsigned reserved9  : 16;
	unsigned ldt        : 16; //!< Pointer to the LDT (static)
	unsigned reserved10 : 16;
	unsigned trap       :  1; //!< Flag to raise an exception when a task switch to this task occurs (static)
	unsigned reserved11 : 15;
	unsigned iomap_base : 16; //!< IOMMU base
} __attribute__((packed));

typedef struct tss_s tss_t;
extern tss_t tss;

void gdt_init();

void setKernelStack(uint32_t stack);

#endif
