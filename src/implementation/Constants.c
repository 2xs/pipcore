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

/* This file contains arch-independent constants */

#include "mal.h"
#include "Constants.h"

vaddr vaddrDefault = 0;

index getIdxStoreFetch(void) {
    return 0;
}

index getIdxPartDesc(void) {
    return 0;
}

index getIdxPageDir(void) {
    return 2;
}

index getIdx3(void) {
    return 3;
}

index getIdxShadow1(void) {
    return 4;
}

index getIdxShadow2(void) {
    return 6;
}

index getIdxShadow3(void) {
    return 8;
}

index getIdxParentDesc(void) {
    return 10;
}

vaddr getVaddrDefault(void) {
    return vaddrDefault;
}

page getPageDefault(void) {
    return 0;
}

count getCount0(void) {
    return 0;
}

size_t contextSizeMinusOne = sizeof(user_ctx_t) - 1;
