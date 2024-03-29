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
 * \file mal.h
 * \brief Memory Abstraction Layer common interface
 */

#ifndef __MAL__
#define __MAL__

#include <stdint.h>

#include "maldefines.h"
#include "Constants.h"

void enable_paging();
void disable_paging();

/* Current page directory */
uint32_t getCurPartition(void); //!< Interface to get the current Page Directory
void updateCurPartition (uint32_t descriptor);

uint32_t getPageRootPartition(void); //!< Interface to get the current Page Directory
void updateRootPartition (uint32_t descriptor);

/* Address manipulation stuff */
uint32_t getNbIndex(); //!< Get amount of indirection tables
uint32_t getIndexOfAddr(uint32_t addr, uint32_t index); //!< Get index of indirection level given
uint32_t getOffsetOfAddr(uint32_t addr); //!< Get offset from address
uint32_t readTableVirtual(uint32_t table, uint32_t index); //!< FETCH address stored in indirection table
uint32_t readTableVirtualNoFlags(uint32_t table, uint32_t index); //!< FETCH address stored in indirection table
uint32_t readArray(uint32_t table, uint32_t index); //!< Read an array's contents
void writeTableVirtual(uint32_t table, uint32_t index, uint32_t addr); //!< STORE an address in an indirection table
void writeTableVirtualNoFlags(uint32_t table, uint32_t index, uint32_t addr); //!< STORE an address in an indirection table
bool readPresent(uint32_t table, uint32_t index); //!< Reads the present flag 
void writePresent(uint32_t table, uint32_t index, bool value); //!< Writes the present flag
bool readAccessible(uint32_t table, uint32_t index); //!< Reads the accessible flag
void writeAccessible(uint32_t table, uint32_t index, bool value); //!< Writes the accessible flag
page readPhysical(page table, index index); //!< FETCH address stored in indirection table, physical version
vaddr readVirtual(page table, index index);
vaddr readVirtualUser(page table, index index);
page readPhyEntry(page table, index index);
vaddr readVirEntry(page table, index index);
void writePhysical(page table, index index, page val); //!< STORE an address in an indirection table, physical version
void writeVirtual(page table, index index, vaddr val);
void writeVirEntry(page table, index index, vaddr val);
void writePhysicalNoFlags(uint32_t table, uint32_t index, uint32_t addr);
uint32_t readIndex(uint32_t table, uint32_t index); //!< FETCH index stored in indirection table, physical version
void writeIndex(uint32_t table, uint32_t index, uint32_t idx); //!< STORE an index in an indirection table, physical version
uint32_t dereferenceVirtual(uint32_t addr);
uint32_t derivated(uint32_t table, uint32_t index); //!< Returns 1 if the page is derivated, 0 else

bool readPDflag(uint32_t table, uint32_t index); //!< 
void writePDflag(uint32_t table, uint32_t index, bool value); //!< Writes the page directory flag contents
uint32_t get_pd(); //!< Returns the VIRTUAL ADDRESS of the current Page Directory

void cleanPageEntry(uint32_t table, uint32_t index); //!< Cleans a page entry, setting its contents to 0x00000000

extern uint32_t tableSize;
uint32_t getTableSize(void); //!< Table size
index maxFreeLL();
uint32_t getMaxIndex(void); //!< Table size
void cleanPage(uint32_t paddr); //!< Cleans a given page, filling it with zero

bool checkRights(bool read, bool write, bool execute); //!< Checks whether the asked rights are applicable to the architecture or not
uint32_t applyRights(uint32_t table, uint32_t index, uint32_t read, uint32_t write, uint32_t execute); //!< Apply the asked rights to the given entry

uint32_t toAddr(uint32_t input); //!< Converts a given uint32_t to an address (only for Haskell FFI purposes)
extern uint32_t nbLevel;
extern uint32_t boundNbLevel;

/* Amount of pages available, meh */
extern uint32_t nbPage;
extern uint32_t boundNbPages;

uint32_t getIdxKernel(void); //!< Index of kernel's page directory entry
void writePhyEntry(uint32_t table, uint32_t index, uint32_t addr, bool present, bool user, bool read, bool write, bool execute); //!< Write a physical entry with all the possible flags we might need
void mapKernel(uint32_t mmu_root_page, uint32_t kernel_index); //!< Writes the kernel MMU configuration page at index 'kernel_index' in the MMU root page
uint32_t extractPreIndex(uint32_t vaddr, uint32_t index);

uint32_t prepareType(bool b, uint32_t vaddr);


void updateMMURoot(page MMURoot);
interruptMask getInterruptMaskFromCtx(contextAddr context);
bool noInterruptRequest(interruptMask flagsOnWake);
bool firstVAddrGreaterThanSecond(vaddr vaddr1, vaddr vaddr2);
contextAddr vaddrToContextAddr(vaddr contextVAddr);
bool checkIndexPropertyLTB(userValue userIndex);
index userValueToIndex(userValue userIndex);
vaddr getVaddrVIDT();
vaddr getNthVAddrFrom(page base, uint32_t size);
void writeContext(contextAddr ctx, vaddr ctxSaveVAddr, interruptMask flagsOnWake);
void loadContext(contextAddr ctx, bool enforce_interrupts);

#endif
