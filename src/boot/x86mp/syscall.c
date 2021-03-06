/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2017)                 */
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

#include "syscall.h"
#include "debug.h"
#include "mp.h"

#include <stdint.h>

extern void init_msr(uint32_t st);
extern uint32_t *_sysenter_stacks;

#define PIPCALL_COUNT   20
/* System calls */
extern uint32_t createPartition(uint32_t,uint32_t,uint32_t,uint32_t,uint32_t);
extern uint32_t countToMap(uint32_t,uint32_t);
extern uint32_t prepare(uint32_t, uint32_t, uint32_t, uint32_t);
extern uint32_t addVAddr(uint32_t, uint32_t, uint32_t, uint32_t, uint32_t, uint32_t);
extern uint32_t resume(uint32_t, uint32_t);
extern uint32_t removeVAddr(uint32_t, uint32_t);
extern uint32_t mappedInChild(uint32_t);
extern uint32_t deletePartition(uint32_t);
extern uint32_t collect(uint32_t,uint32_t);
extern uint32_t smpRequest(uint32_t, uint32_t);
extern uint32_t dispatchGlue(uint32_t, uint32_t, uint32_t, uint32_t, uint32_t);

extern uint32_t outbGlue(uint32_t, uint32_t);
extern uint32_t outwGlue(uint32_t, uint32_t);
extern uint32_t outlGlue(uint32_t, uint32_t);
extern uint32_t outaddrlGlue(uint32_t, uint32_t);
extern uint32_t inbGlue(uint32_t);
extern uint32_t inwGlue(uint32_t);
extern uint32_t inlGlue(uint32_t);

extern uint32_t slputs_sync(char*);

extern uint32_t timerGlue();

void *syscall_table[PIPCALL_COUNT] = 
{
    &createPartition,
    &countToMap,
    &prepare,
    &addVAddr,
    &dispatchGlue,
    &timerGlue,
    &resume,
    &removeVAddr,
    &mappedInChild,
    &deletePartition,
    &collect,
    &smpRequest,
    &outbGlue,
    &inbGlue,
    &outwGlue,
    &inwGlue,
    &outlGlue,
    &inlGlue,
    &outaddrlGlue,
    &slputs_sync,
};

void sysenter_c_ep(uint32_t syscall_id, uint32_t esp, uint32_t eip)
{
    DEBUG(CRITICAL, "Called SYSENTER! eip %x, esp %x\n", eip, esp);
    DEBUG(CRITICAL, "Attempting to call system call %x at %x...\n", syscall_id, syscall_table[syscall_id]);
    return;
}

void init_sysenter(uint32_t cid)
{
    uint32_t st = (uint32_t)&_sysenter_stacks - (cid * 131070); /* 128kb */
    DEBUG(CRITICAL, "Initializing SYSENTER with kernel stack at %x for core %d.\n", st, cid);
    
    init_msr(st);
    
    uint32_t i;
    if(coreId() == 0x0) {
        for(i=0; i<PIPCALL_COUNT; i++)
        {
            DEBUG(CRITICAL, "\tPipcall %d: %x\n", i, syscall_table[i]);
        }
}
    return;
}
