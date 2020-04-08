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

#include <stdint.h>

#include "maldefines.h"
#include "Internal.h"
#include "pip_interrupt_calls.h"
#include "mal.h"

// interrupt state is located at INTERRUPT_STATE_IDX in every partition descriptor
// Its semantic is the same as the CPU interrupt_enable flag :
//  - 0               => partition does not want to be interrupted
//  - any other value => partition accepts to be interrupted

// sets the interrupt state of the current partition
void set_int_state(uint32_t interrupt_state) {
	uint32_t currentPartDesc = getCurPartition();
	writePhysical(currentPartDesc, INTERRUPT_STATE_IDX, interrupt_state);
	if (currentPartDesc == getRootPartition()) {
		if (interrupt_state == 0)
			asm("cli");
		else	asm("sti");
	}
	return;
}

// gets the interrupt state of the current partition
uint32_t get_self_int_state() {
	uint32_t currentPartDesc = getCurPartition();
	return readPhysical(currentPartDesc, INTERRUPT_STATE_IDX);
}

//FIXME the function should have a reserved return code for errors
// gets the interrupt state of a child partition
uint32_t get_int_state(uint32_t child_vaddr) {
	uint32_t currentPartDesc = getCurPartition();
	uint32_t currentPageDir  = getPd(currentPartDesc);
	uint32_t nbL = getNbLevel();
	uint32_t childPartDescLastMMUPage = getTableAddr(currentPageDir, child_vaddr, nbL);
	if (childPartDescLastMMUPage == 0)
		return ~0;
	uint32_t idxChildPartDesc = getIndexOfAddr(child_vaddr, fstLevel);
	if (!(readPresent(childPartDescLastMMUPage, idxChildPartDesc)))
		return ~0;
	if (!(checkChild(currentPartDesc, nbL, child_vaddr)))
		return ~0;
	uint32_t childPartDesc = readPhyEntry(childPartDescLastMMUPage, idxChildPartDesc);
	return readPhysical(childPartDesc, INTERRUPT_STATE_IDX);
}

