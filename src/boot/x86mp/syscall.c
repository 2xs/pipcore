#include "syscall.h"
#include "debug.h"
#include "mp.h"

#include <stdint.h>

extern void init_msr(uint32_t st);

#define PIPCALL_COUNT   19
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
};

void sysenter_c_ep(uint32_t syscall_id, uint32_t esp, uint32_t eip)
{
    DEBUG(CRITICAL, "Called SYSENTER! eip %x, esp %x\n", eip, esp);
    DEBUG(CRITICAL, "Attempting to call system call %x at %x...\n", syscall_id, syscall_table[syscall_id]);
    return;
}

void init_sysenter(uint32_t cid)
{
    uint32_t st = 0x300000 - (cid * 0x4000);
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
