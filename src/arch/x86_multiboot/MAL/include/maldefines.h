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

#include "x86int.h"
#include "pip_interrupt_calls.h"
#include <stdint.h>

typedef _Bool bool;

#define true    1
#define false   0

/* Page */
typedef uintptr_t page;

#define getDefaultPage defaultAddr
#define Page_eqb       eqb

/* VAddr */
typedef uintptr_t vaddr;

#define getDefaultVAddr defaultAddr
#define VAddr_eqbList   addressEquals
#define beqVAddr        addressEquals

extern uint32_t getVidtVAddr(void);

/* Index */
typedef uint32_t index;

#define getSh1idx  indexSh1
#define getSh2idx  indexSh2
#define getSh3idx  indexSh3
#define getPRidx   zero
#define getPDidx   indexPD
#define getPPRidx  PPRidx

#define Index_succ inc
#define Index_pred sub
#define Index_eqb  eqb
#define Index_zero zero
#define Index_const3() 3
#define Index_geb  geb
#define Index_gtb  gtb
#define Index_leb  leb
#define Index_ltb  ltb
#define PreIndex_ltb ltb
#define PreLevel_eqb eqb
#define PreLevel_pred sub

/* Level */
typedef uint32_t level;

#define fstLevel  0
#define fstPreLevel 0

#define Level_succ inc
#define Level_pred sub
#define Level_eqb  eqb
#define Level_gtb  gtb

/* Count */
typedef uint32_t count;

#define Count_succ inc
#define Count_geb  geb
#define Count_zero zero
#define Count_mul3 mul3

/* Miscellaneous */
#define getStoreFetchIndex zero
#define fetchVirtual       readTableVirtual

/* preVaddr */
typedef uint32_t preVaddr;
typedef uint32_t preIndex;
typedef uint32_t preLevel;

/* Astucious defines */
#define preVaddrToVaddr(x) x
#define succNbLevel (nbLevel + 1)
#define maxprelevel (nbLevel - 1)
#define coq_N 1024*1024

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
#define contextAddr user_ctx_t *

#define contextSizeMinusOne (sizeof(user_ctx_t) - 1)

#define userValue uint32_t

#endif
