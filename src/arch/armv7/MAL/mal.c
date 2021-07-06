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

const uint32_t nbLevel = 0;

/*!
 * \brief enables paging
 * \post paging mechanism is enabled
 */
void enable_paging()
{
    /* TODO */
    return;
}

/*!
 * \brief disables paging
 * \post paging mechanism is disabled
 */
void disable_paging()
{
    /* TODO */
    return;
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
    /* TODO */
    (void) table;
    (void) index;
    (void) val;
    return;
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
    /* TODO */
    (void) table;
    (void) index;
    return (uint32_t) 0;
}

/*!
 * \brief Gets size of indirection table
 * \return The amount of entries in a page table
 */
uint32_t getTableSize()
{
    /* TODO */
    return (uint32_t) 0;
}


/*!
 * \brief Gets the index of this address into the given indirection table level
 * \param addr The virtual address
 * \param index The indirection level address
 * \return The desired index
 */
uint32_t getIndexOfAddr(uint32_t addr, uint32_t index)
{
    /* TODO */
    (void) addr;
    (void) index;
    return (uint32_t) 0;
}

/*!
 * \brief Gets the Accessible flag from the given entry.
 * \param table The table to read from
 * \param index The index in the given table
 * \return 1 if the page is user-mode accessible, 0 else
 */
uint32_t readAccessible(uint32_t table, uint32_t index)
{
    /* TODO */
    (void) table;
    (void) index;
    return (uint32_t) 0;
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
    /* TODO */
    (void) table;
    (void) index;
    (void) value;
    return;
}

/*!
 * \brief get the current page directory
 * \return the current page directory
 */
uint32_t getCurPartition(void)
{
    /* TODO */
    return (uint32_t) 0;
}

/*!
 * \brief Set current partition paddr
 * \param partition Current partition paddr
 */
void updateCurPartition (uint32_t descriptor)
{
    /* TODO */
    (void) descriptor;
    return;
}

/*!
 * \brief get the root partition
 * \return the root partition
 */
uint32_t getRootPartition(void)
{
    /* TODO */
    return (uint32_t) 0;
}

/*!
 * \brief Set root partition paddr
 * \param partition Root partition paddr
 */
void updateRootPartition(uint32_t partition)
{
    /* TODO */
    (void) partition;
    return;
}

/*!
 * \brief Gets the Present flag from the given entry.
 * \param table The table to read from
 * \param index The index in the given table
 * \return 1 if the page is present, 0 else
 */
uint32_t readPresent(uint32_t table, uint32_t index)
{
    /* TODO */
    (void) table;
    (void) index;
    return (uint32_t) 0;
}

/*!
 * \brief Marks a page as present or not.
 * \param table The indirection table
 * \param index The index into this indirection table
 * \param value 0 if the page is not present, 1 else (any other value should be
 *        forbidden...)
 */
void writePresent(uint32_t table, uint32_t index, uint32_t value)
{
    /* TODO */
    (void) table;
    (void) index;
    (void) value;
    return;
}


/*!
 * \brief Writes the Page Directory flag into a shadow table
 * \param table The shadow page's last indirection
 * \param index The index into the shadow table
 * \param value The vamue of the PD flag
 */
void writePDflag(uint32_t table, uint32_t index, uint32_t value)
{
    /* TODO */
    (void) table;
    (void) index;
    (void) value;
    return;
}

/*!
 * \brief Reads the Page Directory flag into a shadow table
 * \param table The shadow page's last indirection
 * \param index The index into the shadow table
 * \return The value of the PD flag
 */
uint32_t readPDflag(uint32_t table, uint32_t index)
{
    /* TODO */
    (void) table;
    (void) index;
    return (uint32_t) 0;
}

/*!
 * \brief TODO
 * \param table The shadow page's last indirection
 * \param index The index into the shadow table
 * \return The value of the PD flag
 */
uint32_t readPhysical(uint32_t table, uint32_t index)
{
    /* TODO */
    (void) table;
    (void) index;
    return (uint32_t) 0;
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
    /* TODO */
    (void) table;
    (void) index;
    (void) addr;
    return;
}

/*!
 * \brief Gets the amount of indirection tables
 * \return Amount of maximal indirection tables
 */
uint32_t getNbIndex(void)
{
    /* TODO */
    return (uint32_t) 0;
}

/*!
 * \brief Stores the given address into the given indirection table, at the
 *        given index
 * \param table The table to store into
 * \param index The index in the table
 * \param addr The address to store
 */
void writeTableVirtual(uint32_t table, uint32_t index, uint32_t addr)
{
    /* TODO */
    (void) table;
    (void) index;
    (void) addr;
    return;
}

/*!
 * \brief Reads the address stored into table Table, at index index
 * \param table The table to read from
 * \param index The index in the table
 * \return The address stored in the given slot
 */
uint32_t readTableVirtual(uint32_t table, uint32_t index)
{
    /* TODO */
    (void) table;
    (void) index;
    return (uint32_t) 0;
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
    /* TODO */
    (void) read;
    (void) write;
    (void) execute;
    return (uint32_t) 0;
}

/*!
 * \brief TODO
 * \param addr TODO
 * \param index TODO
 */
uint32_t extractPreIndex(uint32_t addr, uint32_t index)
{
    /* TODO */
    (void) addr;
    (void) index;
    return (uint32_t) 0;
}

/*!
 * This function is the real world version of the model's "mapKernel".
 * We use the same MMU table page for every partition that is configured at
 * boot time for the root partition. When creating a partition, that page is
 * looked up in the MMU configuration pages of the parent partition and written
 * at the same place.
 */
void writeKernelPhysicalEntry(uintptr_t child_mmu_root_page,
        uint32_t kernel_index)
{
    /* TODO */
    (void) child_mmu_root_page;
    (void) kernel_index;
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
    /* TODO */
    (void) b;
    (void) vaddr;
    return (uint32_t) 0;
}
