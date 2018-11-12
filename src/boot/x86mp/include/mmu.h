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
 * \file mmu.h
 * \brief Include file for MMU configuration.
 */

#ifndef __PAGING__
#define __PAGING__

#include "multiboot.h"
#include "structures.h"
#include <stdint.h>

/**
 * \brief Defines the size of a Page.
 */
#define PAGE_SIZE 4096

uint32_t *firstFreePage; //!< First free available page.
void initFreePageList(uintptr_t base, uintptr_t length);
uint32_t* allocPage();
void freePage(uint32_t *page);
void dumpMmap(uint32_t* mmap_ptr, uint32_t len);
uint32_t initMmu();
void fillMmu(uint32_t begin);
void coreEnableMmu();
void mapPageWrapper(page_directory_t* dir, uint32_t paddr, uint32_t vaddr, uint8_t user);
void prepareAllocatorRelease();

#endif
