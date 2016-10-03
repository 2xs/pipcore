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
 * \file maldefines.h
 * \brief Memory Abstraction Layer provided methods for Coq
 */

#ifndef __MAL_DEFINES__
#define __MAL_DEFINES__

#include "mal.h"

/* --- Defines for Coq --- */
#define readVirtual readPhysical
#define readVirEntry readPhysicalNoFlags
#define readPhyEntry readPhysicalNoFlags
#define writeVirtual writePhysical
#define writeVirEntry writePhysical
#define writePhyEntry writePhysicalWithLotsOfFlags
#define readIndex readPhysical
#define writeIndex writePhysical
#define getNbLevel getNbIndex
#define tableSize getTableSize
#define fetchVirtual readTableVirtual
#define storeVirtual writeTableVirtual
#define getDefaultVAddr defaultAddr
#define getDefaultPage defaultAddr
#define fstLevel zero
#define coq_Kidx kernelIndex
#define coq_PRidx zero
#define coq_PDidx indexPD
#define sh1idx indexSh1
#define sh2idx indexSh2
#define sh3idx indexSh3
#define coq_PRPidx PPRidx
#define getKidx kernelIndex
#define getPRidx zero
#define getPDidx indexPD
#define getSh1idx indexSh1
#define getSh2idx indexSh2
#define getSh3idx indexSh3
#define getPPRidx PPRidx
#define getStoreFetchIndex zero
#define beq_index addressEquals
#define beq_page addressEquals
#define beq_vaddr addressEquals
#define pred sub
#define succ inc
#define eqbList addressEquals
#define getMultiplexer getRootPartition

uint32_t nbPage();

#endif
