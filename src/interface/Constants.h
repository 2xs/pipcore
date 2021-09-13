/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2022)                */
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

#ifndef __CONSTANTS__
#define __CONSTANTS__

/* include mal for kernelIndex, getVidtVAddr */
#include "mal.h"

#define idxDefault 0
#define idxStoreFetch 0
/* idxKernel will be chosen by the linker */

#define idxPartDesc   0
#define idxPageDir    2
#define idxShadow1    4
#define idxShadow2    6
#define idxShadow3    8
#define idxParentDesc 10

#define vaddrDefault 0

#define pageDefault 0

#define levelMin 0
#define count0 0

#define getIdxDefault()      (idxDefault)
#define getIdx0()            (0)
#define getIdx3()            (3)
#define getIdxStoreFetch()   (idxStoreFetch)
#define getIdxKernel()       (kernelIndex())
#define getIdxPartDesc()     (idxPartDesc)
#define getIdxPageDir()      (idxPageDir)
#define getIdxShadow1()      (idxShadow1)
#define getIdxShadow2()      (idxShadow2)
#define getIdxShadow3()      (idxShadow3)
#define getIdxParentDesc()   (idxParentDesc)
#define getVaddrDefault()    (vaddrDefault)
#define getVaddrVIDT()       (getVidtVAddr())
#define getPageDefault()     (pageDefault)
#define getPageMultiplexer() (getRootPartition())
#define getLevelMin()        (levelMin)
#define getCount0()          (count0)

#endif
