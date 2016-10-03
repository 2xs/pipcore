/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2016)                 */
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
 * \file boot_requirements.c
 * \brief x86 memory abstraction layer requirements for x86 bootstrap
 */

#include <stdint.h>
#include "structures.h"
#include "mal.h"
#include "debug.h"
#include "libc.h"

/*!	\fn void activate(uintptr_t dir)
	\brief activates the virtual space dir
	\param dir a page directory
	\post dir is the current virtual space
 */
void activate(uintptr_t dir)
{
	// Set CR3 to the address of our Page Directory
	page_directory_t* d = (page_directory_t*)dir;
	asm volatile("mov %0, %%cr3"
				 :
				 : "r"(&(d->tablesPhysical)));
	
	// Switch on paging
	enable_paging();
}

/*!
 * \fn uint32_t getOffsetOfAddr(uintptr_t addr)
 * \brief Gets the offset from an address
 * \param addr The address
 * \return The offset calculated from this address
 */
uint32_t getOffsetOfAddr(uintptr_t addr)
{
	/* Get the last 12 bytes of address */
	uint32_t off = (uint32_t)addr & 0x00000FFF;
	return off;
}

uintptr_t readArray(uintptr_t array, uint32_t index)
{
	uint32_t* tbl = (uint32_t*)array;
	return (uintptr_t)(*(tbl + index));
}

uintptr_t readTableVirtualNoFlags(uintptr_t table, uint32_t index)
{
	/* Binary OR with the table's address, page-aligned, and the offset */
	uintptr_t dest = table | ((uintptr_t)index * sizeof(uint32_t));
	
	/* Now we got a fresh, cool, nice pointer, return its value */
	uintptr_t val = (uintptr_t)*(uint32_t*)dest;
	
	return val;
}

void writeTableVirtualNoFlags(uintptr_t table, uint32_t index, uintptr_t addr)
{
	/* Just in case we're given bullshit, zero the potential flags. */
	uint32_t val = (uint32_t)addr;
	
	/* Get the destination address */
	uintptr_t dest = table | ((uintptr_t)index * sizeof(uint32_t));
	
	*(uint32_t*)dest = val;
	
	return;
}

/*!
 * \fn uint32_t derivated(uintptr_t table, uint32_t index)
 * \brief Returns 1 if the page is derivated.
 * \param table The shadow table's last indirection
 * \param index The index into this shadow table
 * \return 1 if derivated, 0 else
 */
uint32_t derivated(uintptr_t table, uint32_t index)
{
	uintptr_t dest = (uintptr_t)(table + ((uintptr_t)index * sizeof(uint32_t)));
	uint32_t curval = *(uint32_t*)dest;
	uintptr_t curAddr = (uintptr_t)curval & 0xFFFFF000;
	
	return !(curAddr == 0x00000000);
}

/*!
 * \fn void cleanPageEntry(uintptr_t table, uint32_t index);
 * \brief Cleans a page entry
 * \param table The table in which to find the entry
 * \param index The index of the entry
 */
void cleanPageEntry(uintptr_t table, uint32_t index){
	uintptr_t dest = table + (uintptr_t)(index * sizeof(uint32_t));
	*(uintptr_t*)dest = 0x00000000;
	
	return;
}

/*!
 * \fn uintptr_t readIndex(uintptr_t table, uint32_t index)
 * \brief Reads the index stored into table Table, at index index, using physical addresses
 * \param table The table to read from
 * \param index The index in the table
 * \return The index stored in the given slot
 */
uint32_t readIndex(uintptr_t table, uint32_t index)
{
	/* We're in kernel : we can disable paging */
	disable_paging();
	
	/* Binary OR with the table's address, page-aligned, and the offset */
	uintptr_t dest = table | ((uintptr_t)index * sizeof(uint32_t));
	
	/* Now we got a fresh, cool, nice pointer, return its value */
	uint32_t val = *(uint32_t*)dest;
	
	/* Re-enable paging */
	enable_paging();
	
	return val;
}

/*!
 * \fn void writeIndex(uintptr_t table, uint32_t index, uint32_t idx)
 * \brief Stores the given address into the given indirection table, at the given index, with physical addresses
 * \param table The table to store into
 * \param index The index in the table
 * \param addr The index to store
 */
void writeIndex(uintptr_t table, uint32_t index, uint32_t addr)
{
	/* Disable paging */
	disable_paging();
	
	/* Just in case we're given bullshit, zero the potential flags. */
	uint32_t val = (uint32_t)addr;
	
	/* Get the destination address */
	uintptr_t dest = table | ((uintptr_t)index * sizeof(uint32_t));
	
	*(uint32_t*)dest = val /* | curFlags */;
	
	/* Enable paging */
	enable_paging();
	
	return;
}

/**
 * \fn uintptr_t toAddr(uint32_t input)
 * \brief Dummy function to convert a given integer to an address
 * \param input The given integer
 * \return The same integer as an address
 * \note This is only for Haskell. C doesn't need this!
 */
uintptr_t toAddr(uint32_t input)
{
	return (uintptr_t)input;
}

/**
 * \fn void cleanPage(uintptr_t paddr)
 * \brief Cleans a given page, filling it with zeroes.
 * \param paddr The page's physical address
 */
void cleanPage(uintptr_t paddr)
{
	disable_paging();
	memset((uint32_t*)paddr, 0x00000000, PAGE_SIZE);
	enable_paging();
}

/**
 * \fn uint32_t applyRights(uintptr_t table, uint32_t index, uint32_t read, uint32_t write, uint32_t execute)
 * \param table The indirection table in which we find the entry
 * \param index The index in this table, targeting the specified entry
 * \param read The read right
 * \param write The write right
 * \param execute The execute right
 * \brief Applies the given rights on the given entry
 * \return 1 if the rights were applied, 0 otherwise
 */
uint32_t applyRights(uintptr_t table, uint32_t index, uint32_t read, uint32_t write, uint32_t execute)
{
	// First check is we can do this
	uint32_t checkright = checkRights(read, write, execute);
	if(checkright == 0)
		return 0;
	
	// Find the entry
	uintptr_t dest = table | ((uintptr_t)index * sizeof(uint32_t));
	page_table_entry_t* entry = (page_table_entry_t*)dest;
	
	// Change the RW bit
	entry->rw = write;
	
	return 1;
}

/**
 * \fn void writePhysicalWithLotsOfFlags(uintptr_t table, uint32_t index, uintptr_t addr, uint32_t present, uint32_t user, uint32_t read, uint32_t write, uint32_t execute)
 * \param table The indirection table in which we find the entry
 * \param index The index in this table, targeting the specified entry
 * \param addr The target address
 * \param present 1 if the page is mapped, 0 else
 * \param user 1 if the page is accessible in userland, 0 else
 * \param read The read right
 * \param write The write right
 * \param execute The execute right
 * \brief Applies the given rights on the given entry
 */
void writePhysicalWithLotsOfFlags(uintptr_t table, uint32_t index, uintptr_t addr, uint32_t present, uint32_t user, uint32_t read, uint32_t write, uint32_t execute)
{
	writePhysicalNoFlags(table, index, addr);
	applyRights(table, index, read, write, execute);
	writeAccessible(table, index, user);
	writePresent(table, index, present);
	return;
}

/**
 * \fn uint32_t dereferenceVirtual(uintptr_t addr)
 * \param addr The virtual address to dereference
 * \return The contents of the pointer
 * \warning I don't think this is still used. Anyway, it should never be. Never. Removing this soon.
 */
uint32_t dereferenceVirtual(uintptr_t addr)
{
	return *(uint32_t*)addr;
}
