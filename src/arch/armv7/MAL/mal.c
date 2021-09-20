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

/**
 * \file mal.c
 * \brief ARMv7 memory abstraction layer
 */

#include <stdint.h>

#include "structures.h"
#include "periph.h"
#include "maldefines.h"

uint32_t current_partition = 0;
uint32_t root_partition = 0;

const uint32_t nbLevel = 2;

/*!
 * \brief enables paging
 * \post paging mechanism is enabled
 */
void enable_paging()
{
	cache_and_mmu_enable();
	periph_notify_ioremap(1);
}

/*!
 * \brief disables paging
 * \post paging mechanism is disabled
 */
void disable_paging()
{
	cache_and_mmu_disable();
	periph_notify_ioremap(0);
}

/*!
 * \brief Stores the given address into the given indirection table, at the
 *        given index, with physical addresses
 * \param table The table to store into
 * \param index The index in the table
 * \param addr The address to store
 */
void writePhysical(uint32_t table, uint32_t index, uint32_t val)
{
	uint32_t *paddr;

	paddr = &((uint32_t*)table)[index];

	disable_paging();
	*paddr = val;
	enable_paging();
}

/*!
 * \brief Reads the address stored into table table, at index index, using
 *        physical addresses. This function masks the least significant bits
 *        that are used by the kernel to store various flags (see `readVirEntry`
 *        and `readPhyEntry` in model)
 * \param table The table to read from
 * \param index The index in the table
 * \return The address stored in the given slot, with its least significant bits
 *         cleared
 */
uint32_t readPhysicalNoFlags(uint32_t table, uint32_t index)
{
	uint32_t *paddr, val;

	paddr = &((uint32_t*)table)[index];

	disable_paging();
	val = *paddr & ~0xfff;
	enable_paging();

	return val;
}

/*!
 * \brief Gets size of indirection table
 * \return The amount of entries in a page table
 */
uint32_t getTableSize()
{
	return (uint32_t) MMU_L1_ENT_COUNT;
}

/*!
 * \brief Gets the index of this address into the given indirection table level
 * \param addr The virtual address
 * \param index The indirection level address
 * \return The desired index
 */
uint32_t getIndexOfAddr(uint32_t addr, uint32_t index)
{
	uint32_t idx;

	/* First check the index value */
	if (index > 1)
		return 0;

	/* Index 1 is the first indirection and 2 is the second. */
	if(index == 1)
	{
		/* First level : Page Directory */
		idx = MAL_L1_IDX(addr);
	} else /* index == 0*/{
		/* Second level : Page Table */
		idx = MAL_L2_IDX(addr);
	}

	return idx;
}

/*!
 * \brief Gets the Accessible flag from the given entry.
 * \param table The table to read from
 * \param index The index in the given table
 * \return 1 if the page is user-mode accessible, 0 else
 */
uint32_t readAccessible(uint32_t table, uint32_t index)
{
	uint32_t ret;
	page_table_t *pt = (page_table_t*) table;

	disable_paging();
	ret = pt->pages[index].AP1;
	enable_paging();

	return ret;
}

/*!
 * \brief Marks a page as accessible or not.
 * \param table The indirection table
 * \param index The index into this indirection table
 * \param value 0 if the page is kernel-only, 1 else (any other value should be
 *        forbidden...)
 */
void writeAccessible(uint32_t table, uint32_t index, uint32_t value)
{
	page_table_t *pt = (page_table_t*) table;

	disable_paging();
	pt->pages[index].AP1 = value;
	enable_paging();
}

/*!
 * \brief get the current page directory
 * \return the current page directory
 */
uint32_t getCurPartition(void)
{
	return current_partition;
}

/*!
 * \brief Set current partition paddr
 * \param partition Current partition paddr
 */
void updateCurPartition (uint32_t descriptor)
{
	current_partition = descriptor;
}

/*!
 * \brief get the root partition
 * \return the root partition
 */
uint32_t getRootPartition(void)
{
	return root_partition;
}

/*!
 * \brief Set root partition paddr
 * \param partition Root partition paddr
 */
void updateRootPartition(uint32_t partition)
{
	root_partition = partition;
}

/*!
 * \brief Gets the Present flag from the given entry.
 * \param table The table to read from
 * \param index The index in the given table
 * \return 1 if the page is present, 0 else
 */
uint32_t readPresent(uint32_t table, uint32_t index)
{
	uint32_t ret;
	uint32_t *paddr;

	paddr = &((uint32_t*)table)[index];

	disable_paging();
	/* TODO */
	ret = (*paddr & 3) != 0;
	enable_paging();

	/* Now return the present flag */
	return ret;
}

/*!
 * \brief Writes the Page Directory flag into a shadow table
 * \param table The shadow page's last indirection
 * \param index The index into the shadow table
 * \param value The vamue of the PD flag
 */
void writePDflag(uint32_t table, uint32_t index, uint32_t value)
{
	uint32_t *paddr;

	paddr = &((uint32_t*)table)[index];

	disable_paging();
	*paddr = (*paddr&~1) | (value&1);
	enable_paging();
}

/*!
 * \brief Reads the Page Directory flag into a shadow table
 * \param table The shadow page's last indirection
 * \param index The index into the shadow table
 * \return The value of the PD flag
 */
uint32_t readPDflag(uint32_t table, uint32_t index)
{
	uint32_t *paddr, curval;

	paddr = &((uint32_t*)table)[index];

	disable_paging();
	curval = *paddr;
	enable_paging();

	return (curval & 1);
}

/*!
 * \brief TODO
 * \param table The shadow page's last indirection
 * \param index The index into the shadow table
 * \return The value of the PD flag
 */
uint32_t readPhysical(uint32_t table, uint32_t index)
{
	uint32_t *paddr, val;

	paddr = &((uint32_t*)table)[index];

	disable_paging();
	val = *paddr;
	enable_paging();

	return val;
}

/*!
 * \brief TODO
 * \param table The shadow page's last indirection
 * \param index The index into the shadow table
 * \param addr The index to write
 * \return The value of the PD flag
 */
void writePhysicalNoFlags(uint32_t table, uint32_t index, uint32_t addr)
{
	uint32_t *paddr;

	paddr = &((uint32_t*)table)[index];

	disable_paging();
	*paddr = (*paddr & 0xfff) | (addr & ~0xfff);
	enable_paging();
}


/*!
 * \brief Gets the amount of indirection tables
 * \return Amount of maximal indirection tables
 */
uint32_t getNbIndex(void)
{
	return nbLevel-1;
}

/*!
 * \brief Reads the address stored into table Table, at index index
 * \param table The table to read from
 * \param index The index in the table
 * \return The address stored in the given slot
 */
uint32_t readTableVirtual(uint32_t table, uint32_t index)
{
	uint32_t *vaddr, val;

	vaddr = &((uint32_t*)table)[index];
	val = *vaddr & ~0xfff;

	return val;
}

/*!
 * \brief Checks whether we can apply the given rights on the target
 *        architecture
 * \param read The read right
 * \param write The write right
 * \param execute The execute right
 * \return 1 if we can, 0 if we can't
 */
uint32_t checkRights(uint32_t read, uint32_t write, uint32_t execute)
{
	// Read has to be 1 (only user/kernel in x86)
	if(read==0)
		return 0;

	/* FIXME: We don't support xn, but return 1.
	 * This is part of the writePhysicalWithLotsOfFlags hack */
	if(execute==0)
		return 1;

	// Well the complier will complain about a unused parameter thing so...
	if(write==0 || write == 1)
		return 1;
	else return 0;
}

/*!
 * This function is the real world version of the model's "mapKernel".
 * We use the same MMU table page for every partition that is configured at
 * boot time for the root partition. When creating a partition, that page is
 * looked up in the MMU configuration pages of the parent partition and written
 * at the same place.
 */
void writeKernelPhysicalEntry(uint32_t child_mmu_root_page, uint32_t kernel_index)
{
	uint32_t tt = readPhysical(current_partition, getPDidx() + 1);
	uint32_t kpt = readPhysical(tt, kernelIndex());
	writePhysicalWithLotsOfFlags(child_mmu_root_page, kernel_index, kpt, 0, 0, 0, 0, 0);
	return;
}

/*!
 * \brief Combines a boolean and a virtual address (boolean on the least
 *        significant bit)
 * \param b
 * \param vaddr
 */
uint32_t prepareType(int b, uint32_t vaddr)
{
	return (vaddr & ~1) | (b ? 1 : 0);
}
