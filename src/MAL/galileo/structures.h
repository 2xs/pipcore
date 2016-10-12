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
 * \file structures.h
 * \brief x86 MAL structures
 */

#ifndef STRUCT_H
#define STRUCT_H

#include <stdint.h>

#define PAGE_SIZE 4096 //!< Page size

/**
 * \struct page_table_entry
 * \brief Page Table entry structure
 */
typedef struct page_table_entry
{
	uint32_t present:1;
	uint32_t rw:1;
	uint32_t user:1;
	uint32_t write:1;
	uint32_t cache:1;
	uint32_t accessed:1;
	uint32_t dirty:1;
	uint32_t unused:1;
	uint32_t global:1;
	uint32_t avail:3;
	uint32_t frame:20;
}__attribute__((packed)) page_table_entry_t;
/**
 * \struct page_table
 * \brief Page Table structure
 */
typedef struct page_table
{
    page_table_entry_t pages[1024]; //!< Page Table Entries in this Page Table
}__attribute__((packed)) page_table_t;

/**
 * \struct page_directory
 * \brief Page Directory structure
 */
typedef struct page_directory
{
    uint32_t tablesPhysical[1024]; //!< Page Tables in this Page Directory
}__attribute__((packed)) page_directory_t;

#endif
