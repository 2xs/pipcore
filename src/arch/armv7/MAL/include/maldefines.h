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
 * \file maldefines.h
 * \brief Memory Abstraction Layer provided methods for Coq
 */

#ifndef __MAL_DEFINES__
#define __MAL_DEFINES__

#include "context.h"
#include "pip_interrupt_calls.h"
#include <stdint.h>

/* bool */
typedef _Bool bool;

#define true    1
#define false   0

/* Page */
typedef uintptr_t page;

/* VAddr */
typedef uintptr_t vaddr;

extern vaddr getVaddrVIDT(void);

/* Index */
typedef uint32_t index;

/* Level */
typedef uint32_t level;

/* Count */
typedef uint32_t count;

/* preVaddr */
typedef uint32_t preVaddr;
typedef uint32_t preIndex;
typedef uint32_t preLevel;

/* boolVAddr */
typedef uint32_t boolvaddr;

typedef uint32_t interruptMask;
typedef enum yield_checks_e {
	coq_SUCCESS=0,
	coq_FAIL_INVALID_INT_LEVEL=1,
	coq_FAIL_INVALID_CTX_SAVE_INDEX=2,
	coq_FAIL_ROOT_CALLER=3,
	coq_FAIL_INVALID_CHILD=4,
	coq_FAIL_UNAVAILABLE_TARGET_VIDT=5,
	coq_FAIL_UNAVAILABLE_CALLER_VIDT=6,
	coq_FAIL_MASKED_INTERRUPT=7,
	coq_FAIL_UNAVAILABLE_TARGET_CTX=8,
	coq_FAIL_CALLER_CONTEXT_SAVE=9
} yield_checks;

typedef user_ctx_t *contextAddr;

typedef uint32_t userValue;

#endif
