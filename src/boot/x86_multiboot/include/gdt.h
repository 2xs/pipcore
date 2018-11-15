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
 * \file gdt.h
 * \brief Include file for GDT configuration
 */

#ifndef __GDT__
#define __GDT__

#include <stdint.h>
#include <stdbool.h>

/**
 * \struct gdt_entry
 * \brief Global Descriptor Table entry structure
 */
struct gdt_entry
{
    unsigned short limit_low; //!< Lower bytes of address limit
    unsigned short base_low; //!< Lower bytes of base address
    unsigned char base_middle; //!< Middle bytes of base address
    unsigned char access; //!< Access flags
    unsigned char granularity; //!< Granularity (TODO: find out what this is supposed to do)
    unsigned char base_high; //!< Higher bytes of base address
} __attribute__((packed));

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
 * \struct tss_entry_struct
 * \brief Task State Segment entry structure
 */
struct tss_entry_struct {
	uint32_t prev_tss; //!< Pointer to the previous TSS entry
	uint32_t esp0; //!< Kernel-mode ESP
	uint32_t ss0; //!< Kernel-mode stack segment
	uint32_t esp1; //!< Ring-1 ESP
	uint32_t ss1; //!< Ring-1 stack segment
	uint32_t esp2; //!< Ring-2 ESP
	uint32_t ss2; //!< Ring-2 stack segment
	uint32_t cr3; //!< Page directory address
	uint32_t eip; //!< Execution pointer
	uint32_t eflags; //!< CPU flags
	uint32_t eax; //!< General register EAX
	uint32_t ecx; //!< General register ECX
	uint32_t edx; //!< General register EDX
	uint32_t ebx; //!< General register EBX
	uint32_t esp; //!< User-mode ESP
	uint32_t ebp; //!< User-mode EBP
	uint32_t esi; //!< General register ESI
	uint32_t edi; //!< General register EDI
	uint32_t es; //!< Segment selector ES
	uint32_t cs; //!< Segment selector CS
	uint32_t ss; //!< Segment selector SS
	uint32_t ds; //!< Segment selector DS
	uint32_t fs; //!< Segment selector FS
	uint32_t gs; //!< Segment selector GS
	uint32_t ldt; //!< Pointer to the LDT (unused here)
	uint16_t trap; //!< Admiral Ackbar : "It's a trap!"
	uint16_t iomap_base; //!< IOMMU base
} __attribute__((packed));

typedef struct tss_entry_struct tss_entry_t; //!< TSS entry for kernel-mode switch

struct gdt_callgate {
	unsigned short offset_low;
	unsigned short selector;
	unsigned char args : 5;
	unsigned char reserved : 3;
	unsigned char type : 4;
	unsigned char zero : 1;
	unsigned char dpl : 2;
	unsigned char present : 1;
	unsigned short offset_high;
};

typedef struct gdt_callgate callgate_t;

void gdtInstall();
void buildCallgate(int num, void* handler, uint8_t args, uint8_t rpl, uint16_t segment);

/**
 * \fn extern void gdtFlush()
 * \brief Installs the GDT into the CPU and flushes its entries.
 */
extern void gdtFlush();

void setKernelStack(uint32_t stack);

/* Farcalls to API methods */
extern bool createPartitionGlue(uint32_t ref, uint32_t pd, uint32_t sh1, uint32_t sh2, uint32_t sh3) ;

#endif
