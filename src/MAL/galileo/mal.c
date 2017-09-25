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
 * \file mal.c
 * \brief x86 memory abstraction layer
 */

#include <stdint.h>
#include "mal.h"
#include "structures.h"
#include "debug.h"

/* see "Intel® Quark SoC X1000 Core Developer’s Manual", § 4.4.1.1 (p. 47) */
#define CR0_PE (1u << 0)  /**< 1 = protected mode */
#define CR0_MP (1u << 1)  /**< 1 = monitor coprocessor (FWAIT causes an interrupt) */
#define CR0_EM (1u << 2)  /**< 1 = FPU emulation (x87 instruction cause #NM, SSE causes #UD) */
#define CR0_TS (1u << 3)  /**< 1 = task switched flag (causes #NM on x87/SSE instructions, set by CPU on hardware task switch) */
#define CR0_ET (1u << 4)  /**< 1 = 80387; 0 = 80287 */
#define CR0_NE (1u << 5)  /**< 1 = numeric error */
#define CR0_WP (1u << 16) /**< 1 = write proctected pages aren't writable in ring 0 either */
#define CR0_PCIDE (1u << 17) /** 1 = enable PCIDE */
#define CR0_AM (1u << 18) /**< 1 = alignment mask */
#define CR0_NW (1u << 29) /**< 1 = not write-through */
#define CR0_CD (1u << 30) /**< 1 = disable caching */
#define CR0_PG (1u << 31) /**< 1 = enable paging */


uint32_t current_partition; /* Current partition's CR3 */
uint32_t root_partition; /* Multiplexer's partition descriptor */
uint32_t next_pid = 0;
extern uint32_t pcid_enabled;
/*!	\fn void enable_paging()
	\brief enables paging
	\post paging mechanism is enabled
 */
void enable_paging()
{
	uint32_t cr0;
	asm volatile("mov %%cr0, %0": "=r"(cr0));

    cr0 = (CR0_PE | CR0_PG );
    cr0 &= ~(CR0_MP | CR0_EM | CR0_TS | CR0_AM | CR0_NW | CR0_CD | CR0_WP);
	asm volatile("mov %0, %%cr0":: "r"(cr0));

	//DEBUG(TRACE,"PAGING ENABLED\r\n");
}

/*!     \fn void disable_paging()
 \brief disables paging
	\post paging mechanism is disabled
 */
void disable_paging()
{
	// Get CR0 value
	uint32_t cr0;
	asm volatile("mov %%cr0, %0": "=r"(cr0));
	
	// Disable paging bit
    cr0 &= ~(CR0_PG);
    //cr0 &= ~(CR0_MP | CR0_EM | CR0_TS | CR0_AM | CR0_NW | CR0_CD);
	asm volatile("mov %0, %%cr0":: "r"(cr0));
	//DEBUG(TRACE,"PAGING DISABLED\r\n");
}

/*!
 * \fn void writePhysical(uint32_t table, uint32_t index, uint32_t addr)
 * \brief Stores the given address into the given indirection table, at the given index, with physical addresses
 * \param table The table to store into
 * \param index The index in the table
 * \param addr The address to store
 */
void writePhysical(uint32_t table, uint32_t index, uint32_t val)
{
	/* Disable paging */
	disable_paging();
	
	/* Get the destination address */
	uint32_t dest = table | (index * sizeof(uint32_t));
	*(uint32_t*)dest = val;
	
	/* Enable paging */
	enable_paging();
	
	return;
}

/*!
 * \fn uint32_t readPhysical(uint32_t table, uint32_t index)
 * \brief Reads the address stored into table Table, at index index, using physical addresses
 * \param table The table to read from
 * \param index The index in the table
 * \return The address stored in the given slot
 */
uint32_t readPhysicalNoFlags(uint32_t table, uint32_t index)
{
	/* We're in kernel : we can disable paging */
	disable_paging();
	
	/* We're page-aligned : zero the flags */
	uint32_t mask = 0xFFFFF000;
	
	/* Binary OR with the table's address, page-aligned, and the offset */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	/* Now we got a fresh, cool, nice pointer, return its value */
	uint32_t val = *(uint32_t*)dest;
	
	/* Re-enable paging */
	enable_paging();
	
	return val & 0xFFFFF000;
}

/*!
 * \fn uint32_t getTableSize()
 * \brief Gets size of indirection table
 * \return The amount of entries in a page table
 */
uint32_t getTableSize()
{
	return (uint32_t)1024; // 1024 entries per table
}


/*!
 * \fn uint32_t getIndexOfAddr(uint32_t addr, uint32_t index)
 * \brief Gets the index of this address into the given indirection table level
 * \param addr The virtual address
 * \param index The indirection level address
 * \return The desired index
 */
uint32_t getIndexOfAddr(uint32_t addr, uint32_t index)
{
	/* First check the index value */
	if (index > 1)
		return 0;

	/* Index 1 is the first indirection and 2 is the second. */
	if(index == 1)
	{
		/* First level : Page Directory */
		uint32_t pd_idx = (addr & 0xFFC00000) >> 22;
		return pd_idx;
	} else /* index == 0*/{
		/* Second level : Page Table */
		uint32_t pt_idx = (addr >> 12) & 0x000003FF;
		return pt_idx;
	}
}

/*!
 * \fn uint32_t readAccessible(uint32_t table, uint32_t index)
 * \brief Gets the Accessible flag from the given entry.
 * \param table The table to read from
 * \param index The index in the given table
 * \return 1 if the page is user-mode accessible, 0 else
 */
uint32_t readAccessible(uint32_t table, uint32_t index)
{
	disable_paging();
	
	/* Get destination */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	/* Get value */
	uint32_t val = *(uint32_t*)dest;
	
	/* Cast it into a page_table_entry_t structure */
	page_table_entry_t* entry = (page_table_entry_t*)&val;
	
	/* Now return the accessible flag */
	uint32_t ret = entry->user;
	
	enable_paging();
	
	return ret;
}

/*!
 * \fn void writeAccessible(uint32_t table, uint32_t index, uint32_t value)
 * \brief Marks a page as accessible or not.
 * \param table The indirection table
 * \param index The index into this indirection table
 * \param value 0 if the page is kernel-only, 1 else (any other value should be forbidden...)
 */
void writeAccessible(uint32_t table, uint32_t index, uint32_t value)
{
	disable_paging();
	
	/* Get destination */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	/* Cast it into a page_table_entry_t structure */
	page_table_entry_t* entry = (page_table_entry_t*)dest;
	
	/* Write the flag */
	entry->user = value;
	
	enable_paging();
	
	/* Return so we avoid the warning */
	return;
}

/*! \fn uint32_t getCurPartition()
 \brief get the current page directory
	\return the current page directory
 */
uint32_t getCurPartition(void)
{
	return current_partition;
}

/*! \fn void updateCurPartition()
 \brief Set current partition paddr
 \param partition Current partition paddr
 */
void
updateCurPartition (uint32_t descriptor)
{
	extern uint32_t pcid_enabled;
	current_partition = descriptor;
	if(readPhysical(descriptor, 12) == 0x0 && pcid_enabled)
	{
		writePhysical(descriptor, 12, next_pid);
		DEBUG(TRACE, "Registered partition descriptor %x as PID %d.\n", descriptor, next_pid);
		next_pid++;
	}
}

/*! \fn uint32_t getRootPartition()
 \brief get the root partition 
	\return the root partition 
 */
uint32_t getRootPartition(void)
{
	return root_partition;
}

/*! \fn uint32_t updateRootPartition()
 \brief Set root partition paddr
 \param partition Root partition paddr
 */
void
updateRootPartition(uint32_t partition)
{
	root_partition = partition;
}

/*!
 * \fn uint32_t readPresent(uint32_t table, uint32_t index)
 * \brief Gets the Present flag from the given entry.
 * \param table The table to read from
 * \param index The index in the given table
 * \return 1 if the page is present, 0 else
 */
uint32_t readPresent(uint32_t table, uint32_t index)
{
	disable_paging();
	
	/* Get destination */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	/* Get value */
	uint32_t val = *(uint32_t*)dest;
	
	/* Cast it into a page_table_entry_t structure */
	page_table_entry_t* entry = (page_table_entry_t*)&val;
	
	uint32_t res = entry->present;
	
	enable_paging();
	
	/* Now return the present flag */
	return res;
}

/*!
 * \fn void writePresent(uint32_t table, uint32_t index, uint32_t value)
 * \brief Marks a page as present or not.
 * \param table The indirection table
 * \param index The index into this indirection table
 * \param value 0 if the page is not present, 1 else (any other value should be forbidden...)
 */
void writePresent(uint32_t table, uint32_t index, uint32_t value)
{
	disable_paging();
	
	/* Get destination */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	/* Cast it into a page_table_entry_t structure */
	page_table_entry_t* entry = (page_table_entry_t*)dest;
	
	/* Write the flag */
	entry->present = value;
	
	enable_paging();
	
	/* Return so we avoid the warning */
	return;
}


/*!
 * \fn void writePDflag(uint32_t table, uint32_t index, uint32_t value)
 * \brief Writes the Page Directory flag into a shadow table
 * \param table The shadow page's last indirection
 * \param index The index into the shadow table
 * \param value The vamue of the PD flag
 */
void writePDflag(uint32_t table, uint32_t index, uint32_t value)
{
	disable_paging();
	
	uint32_t dest = table | (index * sizeof(uint32_t));
	uint32_t curval = *(uint32_t*)dest;
	uint32_t curAddr = (uint32_t)curval & 0xFFFFFFFE;

	if(value == 1)
		*(uint32_t*)dest = curAddr | 0x00000001;
	else
		*(uint32_t*)dest = curAddr;
	
	enable_paging();
	
	return;
}

/*!
 * \fn uint32_t readPDflag(uint32_t table, uint32_t index)
 * \brief Reads the Page Directory flag into a shadow table
 * \param table The shadow page's last indirection
 * \param index The index into the shadow table
 * \return The value of the PD flag
 */
uint32_t readPDflag(uint32_t table, uint32_t index)
{
	disable_paging();
	
	uint32_t dest = table | (index * sizeof(uint32_t));
	uint32_t curval = *(uint32_t*)dest;
	
	enable_paging();
	
	return (curval & 0x00000001);
}

uint32_t readPhysical(uint32_t table, uint32_t index)
{
	/* We're in kernel : we can disable paging */
	disable_paging();
	
	/* Binary OR with the table's address, page-aligned, and the offset */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	/* Now we got a fresh, cool, nice pointer, return its value */
	uint32_t val = *(uint32_t*)dest;
	
	/* Re-enable paging */
	enable_paging();
	
	return val;
}


void writePhysicalNoFlags(uint32_t table, uint32_t index, uint32_t addr)
{
	/* Disable paging */
	disable_paging();
	
	/* Just in case we're given bullshit, zero the potential flags. */
	uint32_t val = (uint32_t)addr & ~0xfff;
	
	/* Get the destination address */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	*(uint32_t*)dest = (*(uint32_t*)dest&0xfff)|val;
	
	/* Enable paging */
	enable_paging();
	
	return;
}


/*!	\fn uint32_t getNbIndex()
 * 	\brief Gets the amount of indirection tables
 * 	\return Amount of maximal indirection tables
 */
uint32_t getNbIndex(void)
{
	return nbLevel()-1;
}

uint32_t nbLevel(void)
{
	return 2;
}

/*!
 * \fn void writeAddr(uint32_t table, uint32_t index, uint32_t addr)
 * \brief Stores the given address into the given indirection table, at the given index
 * \param table The table to store into
 * \param index The index in the table
 * \param addr The address to store
 */
void writeTableVirtual(uint32_t table, uint32_t index, uint32_t addr)
{
	/* Just in case we're given bullshit, zero the potential flags. */
	uint32_t val = (uint32_t)addr & 0xFFFFF000;
	
	/* Get the destination address */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	/* Store this, leaving the current flags unchanged */
	uint32_t curFlags = *(uint32_t*)dest & 0x00000FFF;
	
	*(uint32_t*)dest = val | curFlags;
	
	return;
}

/*!
 * \fn uint32_t readAddr(uint32_t table, uint32_t index)
 * \brief Reads the address stored into table Table, at index index.
 * \param table The table to read from
 * \param index The index in the table
 * \return The address stored in the given slot
 */
uint32_t readTableVirtual(uint32_t table, uint32_t index)
{
	/* Binary OR with the table's address, page-aligned, and the offset */
	uint32_t dest = table | ((uint32_t)index * sizeof(uint32_t));
	
	/* Now we got a fresh, cool, nice pointer, return its value */
	uint32_t val = (uint32_t)*(uint32_t*)dest;
	
	return val & 0xFFFFF000;
}

/*!
 * \fn uint32_t checkRights(uint32_t read, uint32_t write, uint32_t execute)
 * \param read The read right
 * \param write The write right
 * \param execute The execute right
 * \brief Checks whether we can apply the given rights on the target architecture
 * \return 1 if we can, 0 if we can't
 */
uint32_t checkRights(uint32_t read, uint32_t write, uint32_t execute)
{
	// Read has to be 1 (only user/kernel in x86)
	if(read==0)
		return 0;
	
	// No XD bit on i386
	if(execute==0)
		return 0;
	
	// Well the complier will complain about a unused parameter thing so...
	if(write==0 || write == 1)
		return 1;
	else return 0;
}
