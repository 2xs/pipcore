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
 * \file boot_requirements.c
 * \brief ARMv7 memory abstraction layer requirements for ARMv7 bootstrap
 */

#include <stdint.h>

#include "structures.h"
#include "mmu.h"
#include "string.h"
#include "debug.h"
#include "coproc.h"
#include "mal.h"

/*!
 * \brief updates the virtual address space root page
 * \param dir a page directory
 * \post dir is the current virtual space
 */
void updateMMURoot(page MMURoot)
{
	uint32_t ttbr0 = mmu_make_ttbr(
		(void **) MMURoot,      // Translation Table
		RGN_CACHE_WBACK_WALLOC, // Enable inner cache write-back write-alloc
		RGN_CACHE_WBACK_WALLOC, // Enable outer cache write-back write-alloc
		0, 1                    // Non shareable
	);

	disable_paging();
	DSB();

	/* ARM Architecture Reference Manual ARMv7-A and ARMv7-R edition
	 * B3.10.4  Synchronization of changes of ASID and TTBR
	 *
	 * This approach ensures that any non-global pages fetched at a
	 * time when it is uncertain whether the old or new translation
	 * tables are being accessed are associated with the unused ASID
	 * value of 0. Since the ASID value of 0 is not used for any
	 * normal operations these entries cannot cause corruption of
	 * execution.
	 */

	// Change ASID to 0
	WRITE_TLBIASID(0);
	ISB();

	// Change Translation Table Base Register
	WRITE_TTBR0(ttbr0);
	ISB();

	DSB();
	enable_paging();
}

/*!
 * \brief Reads the index stored into table Table, at index index, using
 *        physical addresses
 * \param table The table to read from
 * \param index The index in the table
 * \return The index stored in the given slot
 */
uint32_t readIndex(uint32_t table, uint32_t index)
{
	uint32_t *paddr, val;

	paddr = &((uint32_t*)table)[index];

	disable_paging();
	val = *paddr;
	enable_paging();

	return val;
}

/*!
 * \brief Stores the given address into the given indirection table, at the
 *        given index, with physical addresses
 * \param table The table to store into
 * \param index The index in the table
 * \param addr The index to store
 */
void writeIndex(uint32_t table, uint32_t index, uint32_t idx)
{
	uint32_t *paddr;

	paddr = &((uint32_t*)table)[index];

	disable_paging();
	*paddr = idx;
	enable_paging();
}

/**
 * \brief Dummy function to convert a given integer to an address
 * \param input The given integer
 * \return The same integer as an address
 * \note This is only for Haskell. C doesn't need this!
 */
uint32_t toAddr(uint32_t input)
{
	return input;
}

/**
 * \brief Cleans a given page, filling it with zeroes.
 * \param paddr The page's physical address
 */
void cleanPage(uint32_t paddr)
{
	disable_paging();
	memset((uint32_t*)paddr, 0x00000000, PAGE_SIZE);
	enable_paging();
}

/**
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
void writePhysicalWithLotsOfFlags(uint32_t table, uint32_t index, uint32_t addr,
	uint32_t present, uint32_t user, uint32_t read, uint32_t write, uint32_t execute)
{
	unsigned entry;

	/* TODO */

	if (!present && !user && !read && !write && !execute)
	{
		/* This is just a physical address, write is as it */
		entry = addr;
	}
	else if (present && user && read && write && execute)
	{
		/* Guess this is a PD entry, write a page table entry */
		entry = addr | 1;
	}
	else
	{
		/* Consider this is L2 physical entry
		 * To make this distinguishable from a PD entry, we make userland
		 * pass execute=0 (in libpip). Please forgive me because i'm a sinner.*/
		if (!present)
		{
			PANIC("WE HAVE A PROBLEM: Cannot write non-present L2 entry!\n");
			for(;;);
		}
		if (index >= MMU_L2_ENT_COUNT)
		{
			PANIC("WE HAVE A PROBLEM: index = %d in ARM PT\n", index);
		}
		entry = mmu_make_small_page((void*)addr, user, !write,
			0, /* TODO: xn */
			0  /* TODO: cache attributes */,
			!user   /* set kernel memory as global */
		).aslong;
	}

	writePhysical(table, index, entry);
}

/**
 * \param addr The virtual address to dereference
 * \return The contents of the pointer
 * \warning I don't think this is still used. Anyway, it should never be. Never.
 *          Removing this soon.
 */
uint32_t dereferenceVirtual(uint32_t addr)
{
	return *(uint32_t*) addr;
}
