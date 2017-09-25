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
 * \file mal.h
 * \brief Memory Abstraction Layer common interface
 */

#ifndef __MAL__
#define __MAL__

#include <stdint.h>

void enable_paging();
void disable_paging();

/* Activate : deprecated */
void activate(uint32_t dir);

/* Current page directory */
uint32_t getCurPartition(void); //!< Interface to get the current Page Directory
void updateCurPartition (uint32_t descriptor);

uint32_t getRootPartition(void); //!< Interface to get the current Page Directory
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
uint32_t readPresent(uint32_t table, uint32_t index); //!< Reads the present flag 
void writePresent(uint32_t table, uint32_t index, uint32_t value); //!< Writes the present flag
uint32_t readAccessible(uint32_t table, uint32_t index); //!< Reads the accessible flag
void writeAccessible(uint32_t table, uint32_t index, uint32_t value); //!< Writes the accessible flag
uint32_t readPhysical(uint32_t table, uint32_t index); //!< FETCH address stored in indirection table, physical version
uint32_t readPhysicalNoFlags(uint32_t table, uint32_t index);
void writePhysical(uint32_t table, uint32_t index, uint32_t addr); //!< STORE an address in an indirection table, physical version
void writePhysicalNoFlags(uint32_t table, uint32_t index, uint32_t addr);
uint32_t readIndex(uint32_t table, uint32_t index); //!< FETCH index stored in indirection table, physical version
void writeIndex(uint32_t table, uint32_t index, uint32_t idx); //!< STORE an index in an indirection table, physical version
uint32_t dereferenceVirtual(uint32_t addr);
uint32_t derivated(uint32_t table, uint32_t index); //!< Returns 1 if the page is derivated, 0 else

uint32_t readPDflag(uint32_t table, uint32_t index); //!< 
void writePDflag(uint32_t table, uint32_t index, uint32_t value); //!< Writes the page directory flag contents
uint32_t get_pd(); //!< Returns the VIRTUAL ADDRESS of the current Page Directory

void cleanPageEntry(uint32_t table, uint32_t index); //!< Cleans a page entry, setting its contents to 0x00000000

uint32_t defaultAddr(void); //!< Default address, should be 0x00000000
extern const uint32_t defaultVAddr; //!< Default address, should be 0x00000000
uint32_t getTableSize(void); //!< Table size
uint32_t getMaxIndex(void); //!< Table size
uint32_t addressEquals(uint32_t addr, uint32_t addr2); //!< Checks whether an address is equal to another.
void cleanPage(uint32_t paddr); //!< Cleans a given page, filling it with zero

uint32_t checkRights(uint32_t read, uint32_t write, uint32_t execute); //!< Checks whether the asked rights are applicable to the architecture or not
uint32_t applyRights(uint32_t table, uint32_t index, uint32_t read, uint32_t write, uint32_t execute); //!< Apply the asked rights to the given entry

uint32_t toAddr(uint32_t input); //!< Converts a given uint32_t to an address (only for Haskell FFI purposes)
extern const uint32_t nbLevel;

/* Amount of pages available, meh */
extern uint32_t maxPages;
#define nbPage maxPages

/* Coq related stuff */
int geb(const uint32_t a, const uint32_t b); //!< Greater or equal
int gtb(const uint32_t a, const uint32_t b); //!< Greater than
int leb(const uint32_t a, const uint32_t b); //!< Lower or equal
int ltb(const uint32_t a, const uint32_t b); //!< Lower than
int eqb(const uint32_t a, const uint32_t b); //!< Equals
uint32_t mul3(uint32_t v); //!< Multiply an integer with 3
uint32_t inc(uint32_t val); //!< Increment an integer
uint32_t sub(uint32_t val); //!< Decrement an integer
uint32_t zero(); //!< Zero. That's it.


uint32_t indexPR(void); //!< Partiton descriptor index into itself
uint32_t indexPD(void); //!< Page directory index within partition descriptor
uint32_t indexSh1(void); //!< Shadow 1 index within partition descriptor
uint32_t indexSh2(void); //!< Shadow 2 index within partition descriptor
uint32_t indexSh3(void); //!< Configuration tables linked list index within partition descriptor
uint32_t PPRidx(void); //!< Parent partition index within partition descriptor
uint32_t kernelIndex(void); //!< Index of kernel's page directory entry
void writePhysicalWithLotsOfFlags(uint32_t table, uint32_t index, uint32_t addr, uint32_t present, uint32_t user, uint32_t read, uint32_t write, uint32_t execute); //!< Write a physical entry with all the possible flags we might need
uint32_t extractPreIndex(uint32_t vaddr, uint32_t index);

#endif
