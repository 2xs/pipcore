#ifndef __SPINLOCK__
#define __SPINLOCK__

#define MP_LOCK(a)     while(__sync_lock_test_and_set(&(a), 1))
#define MP_UNLOCK(a)   __sync_lock_release(&(a))
#define MP_INITLOCK(a)  do { (a) = 0; } while(0);
typedef volatile int spinlock_t;

#endif
