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

/*!
 * \brief activates the virtual space dir
 * \param dir a page directory
 * \post dir is the current virtual space
 */
void activate(uintptr_t dir)
{
    /* TODO */
    (void) dir;
    return;
}

/*!
 * \brief Gets the offset from an address
 * \param addr The address
 * \return The offset calculated from this address
 */
uint32_t getOffsetOfAddr(uintptr_t addr)
{
    /* TODO */
    (void) addr;
    return (uint32_t) 0;
}

/*!
 * \brief TODO
 * \param array TODO
 * \param index TODO
 * \return TODO
 */
uintptr_t readArray(uintptr_t array, uint32_t index)
{
    /* TODO */
    (void) array;
    (void) index;
    return (uintptr_t) 0;
}

/*!
 * \brief TODO
 * \param table TODO
 * \param index TODO
 * \return TODO
 */
uintptr_t readTableVirtualNoFlags(uintptr_t table, uint32_t index)
{
    /* TODO */
    (void) table;
    (void) index;
    return (uintptr_t) 0;
}

/*!
 * \brief TODO
 * \param table TODO
 * \param index TODO
 * \param addr TODO
 */
void writeTableVirtualNoFlags(uintptr_t table, uint32_t index, uintptr_t addr)
{
    /* TODO */
    (void) table;
    (void) index;
    (void) addr;
    return;
}

/*!
 * \brief Returns 1 if the page is derivated.
 * \param table The shadow table's last indirection
 * \param index The index into this shadow table
 * \return 1 if derivated, 0 else
 */
uint32_t derivated(uintptr_t table, uint32_t index)
{
    /* TODO */
    (void) table;
    (void) index;
    return (uint32_t) 0;
}

/*!
 * \brief Cleans a page entry
 * \param table The table in which to find the entry
 * \param index The index of the entry
 */
void cleanPageEntry(uintptr_t table, uint32_t index){
    /* TODO */
    (void) table;
    (void) index;
    return;
}

/*!
 * \brief Reads the index stored into table Table, at index index, using
 *        physical addresses
 * \param table The table to read from
 * \param index The index in the table
 * \return The index stored in the given slot
 */
uint32_t readIndex(uintptr_t table, uint32_t index)
{
    /* TODO */
    (void) table;
    (void) index;
    return (uint32_t) 0;
}

/*!
 * \brief Stores the given address into the given indirection table, at the
 *        given index, with physical addresses
 * \param table The table to store into
 * \param index The index in the table
 * \param addr The index to store
 */
void writeIndex(uintptr_t table, uint32_t index, uint32_t addr)
{
    /* TODO */
    (void) table;
    (void) index;
    (void) addr;
    return;
}

/**
 * \brief Dummy function to convert a given integer to an address
 * \param input The given integer
 * \return The same integer as an address
 * \note This is only for Haskell. C doesn't need this!
 */
uintptr_t toAddr(uint32_t input)
{
    /* TODO */
    (void) input;
    return (uintptr_t) 0;
}

/**
 * \brief Cleans a given page, filling it with zeroes.
 * \param paddr The page's physical address
 */
void cleanPage(uintptr_t paddr)
{
    /* TODO */
    (void) paddr;
    return;
}

/**
 * \param table The indirection table in which we find the entry
 * \param index The index in this table, targeting the specified entry
 * \param read The read right
 * \param write The write right
 * \param execute The execute right
 * \brief Applies the given rights on the given entry
 * \return 1 if the rights were applied, 0 otherwise
 */
uint32_t applyRights(uintptr_t table, uint32_t index, uint32_t read,
        uint32_t write, uint32_t execute)
{
    /* TODO */
    (void) table;
    (void) index;
    (void) read;
    (void) write;
    (void) execute;
    return (uint32_t) 0;
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
void writePhysicalWithLotsOfFlags(uintptr_t table, uint32_t index,
        uintptr_t addr, uint32_t present, uint32_t user, uint32_t read,
        uint32_t write, uint32_t execute)
{
    /* TODO */
    (void) table;
    (void) index;
    (void) addr;
    (void) present;
    (void) user;
    (void) read;
    (void) write;
    (void) execute;
    return;
}

/**
 * \param addr The virtual address to dereference
 * \return The contents of the pointer
 * \warning I don't think this is still used. Anyway, it should never be. Never.
 *          Removing this soon.
 */
uint32_t dereferenceVirtual(uintptr_t addr)
{
    /* TODO */
    (void) addr;
    return (uint32_t) 0;
}
