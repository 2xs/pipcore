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

#ifndef DEF_CACHE_H_
#define DEF_CACHE_H_

#include "coproc.h"

/* B2.2.6 About ARMv7 cache and branch predictor maintenance functionality */

/* B4.2.1 Cache and branch predictor maintenance operations, VMSA */

/* branch_pred_enable: Enable branch predictor */
static inline void branch_pred_enable(void)
{
	unsigned reg;

	READ_CP(reg, ID_SCTLR);
	/* Set branch predictor bit in SCTLR*/
	reg |= SCTLR_BRANCH_PRED;
	WRITE_CP(reg, ID_SCTLR);
}
/* branch_pred_disable: Disable branch predictor */
static inline void branch_pred_disable(void)
{
	unsigned reg;

	READ_CP(reg, ID_SCTLR);
	/* Set branch predictor bit in SCTLR*/
	reg &= ~SCTLR_BRANCH_PRED;
	WRITE_CP(reg, ID_SCTLR);
}
/* caches_enable: Enable instruction & data caches */
static inline void caches_enable(void)
{
	unsigned reg;

	ISB(); DSB();
	READ_CP(reg, ID_SCTLR);
	reg |= SCTLR_ICACHE | SCTLR_DCACHE;
	WRITE_CP(reg, ID_SCTLR);
	ISB(); DSB();
}
/* caches_disable: Enable instruction & data caches */
static inline void caches_disable(void)
{
	unsigned reg;

	ISB(); DSB();
	READ_CP(reg, ID_SCTLR);
	reg &= ~(SCTLR_ICACHE | SCTLR_DCACHE);
	WRITE_CP(reg, ID_SCTLR);
	ISB(); DSB();
}
/* dcache_enable: Enable data cache  */
static inline void dcache_enable(void)
{
	unsigned reg;

	/* Use ISB & DSB to ensure memory operations ordering */
	ISB(); DSB();
	READ_CP(reg, ID_SCTLR);
	reg |= SCTLR_DCACHE;
	WRITE_CP(reg, ID_SCTLR);
	ISB(); DSB();
}
/* dcache_disable: Disable data cache  */
static inline void dcache_disable(void)
{
	unsigned reg;

	ISB(); DSB();
	READ_CP(reg, ID_SCTLR);
	reg &= ~SCTLR_DCACHE;
	WRITE_CP(reg, ID_SCTLR);
	ISB(); DSB();
}
/* icache_enable: Enable instruction cache  */
static inline void icache_enable(void)
{
	unsigned reg;

	ISB(); DSB();
	READ_CP(reg, ID_SCTLR);
	reg |= SCTLR_ICACHE;
	WRITE_CP(reg, ID_SCTLR);
	ISB(); DSB();
}
/* icache_enable: Disable instruction cache  */
static inline void icache_disable(void)
{
	unsigned reg;

	ISB(); DSB();
	READ_CP(reg, ID_SCTLR);
	reg &= ~SCTLR_ICACHE;
	WRITE_CP(reg, ID_SCTLR);
	ISB(); DSB();
}
/* dcache_clean_range: Clean data cache of memory range */
void dcache_clean_range(void *addr_, unsigned size);

/* dcache_inval_range: Invalidate data cache of memory range */
void dcache_inval_range(void *addr_, unsigned size);

/* dcache_flush_range: Clean & invalidate data cache of memory range */
void dcache_flush_range(void *addr_, unsigned size);

/* dcache_flush_all: Clean & invalidate all data cache */
void dcache_flush_all(void);

void dcache_flush_disable(void);

#endif
