/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2018)                 */
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
 * \file ial.h
 * \brief Interrupt Abstraction Layer common interface
 */

#ifndef __IAL__
#define __IAL__

#include <stdint.h>

typedef enum user_ctx_role_e {
	/* saved when an interruption occurs*/
	INT_CTX = 0,
	/* saved when partition triggers fault*/
	ISR_CTX = 1,
	/* saved in parent when notifying a child */
	NOTIF_CHILD_CTX = 2,
	/* saved in child when notifying the parent */
	NOTIF_PARENT_CTX = 3,
	/* the invalid index */
	INVALID_CTX = 4,
} user_ctx_role_t;

// These are deprecated and are about to be removed
void initInterrupts(); //!< Interface for interrupt initialization
void panic(); //!< Interface for kernel panic

// The TRUE interface
void enableInterrupts(); //!< Interface for interrupt activation
void disableInterrupts(); //!< Interface for interrupt desactivation
void dispatch2 (uint32_t partition, uint32_t vint, uint32_t data1, uint32_t data2, uint32_t caller); //!< Dispatch & switch to given partition
void resume (uint32_t descriptor, uint32_t pipflags); //!< Resume interrupted partition

// FIXME: move this away
#include <x86int.h>
void
dispatchGlue (uint32_t descriptor, uint32_t vint, uint32_t notify,
			  uint32_t data1, uint32_t data2,
			  gate_ctx_t *ctx);

/**
 * \struct partition_id
 * \brief Partition-to-PartitionID structure
 */
struct partition_id {
	uint32_t partition;
	uint32_t id;
};

/**
 * \struct hardware_def
 * \brief Platform-specific hardware memory range definition
 */
struct hardware_def {
	const char*	name;
	uintptr_t	paddr_base;
	uintptr_t	vaddr_base;
	uintptr_t	limit;
};

typedef struct partition_id pip_pid;

#endif
