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

#include "cache.h"
#include "mmu.h"
#include "memlayout.h"
#include "string.h"
#include "irq.h"
#include "mal.h"
#include "debug.h"

/* Prototypes of control flow transfer services entrypoints */
#include "Services.h"

extern bool_t mmu_io_remapped;
extern uint32_t current_partition;

void mal_init(void);

int kernel_start(void)
{
	/* Clear bss */
	memset(kernel_bss_start, 0, (unsigned)(kernel_bss_end-kernel_bss_start));

	/* Enable D/I caches and branch predictor */
	caches_enable();
	branch_pred_enable();

	/* Configure timer & interrupts */
	irq_init();

	/* Configure the mmu */
	mmu_init();

	/* Initialize the root partition */
	mal_init();

	/* Activate and run the multiplexer */
	updateMMURoot((uint32_t) ((void **) getRootPartition())[indexPD()+1]);

	uint32_t pageDir = readPhysicalNoFlags(getRootPartition(), indexPD()+1);
	user_ctx_t *user_ctx = ((user_ctx_t **) 0x3FFFF000)[0];

	DEBUG(INFO, "Boot sequence completed - now switching to userland\n");
	switchContextCont(getRootPartition(), pageDir, 0, user_ctx);

	/* Should never be reached */
	for (;;);
}
