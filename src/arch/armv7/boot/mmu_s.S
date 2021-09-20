#include <coproc.h>

.section .text

/* Clean & invalidate full dcache */
.global dcache_flush_all
dcache_flush_all:
	stmfd sp!, {r4-r11, lr}
	bl dcache_flush_all_
	/* Invalidate Instruction & Branch predictor caches */
	mov r0, #0
	WRITE_CP_ASM(r0, ID_ICIALLU)
	ldmfd sp!, {r4-r11, lr}

.global dcache_flush_disable
dcache_flush_disable:
	stmfd sp!, {r4-r11, lr}
@	bl dcache_flush_all_				@ Flush caches
	READ_CP_ASM(r0, ID_SCTLR)			@ Disable caches
	bic r0, #0x1000						@ DCACHE
	bic r0, #0x4						@ ICACHE
	WRITE_CP_ASM(r0, ID_SCTLR)
	dsb sy
	isb sy
	mov r0, #0							@ Invalidate Instruction cache & BTB
	WRITE_CP_ASM(r0, ID_ICIALLU)
	dsb sy
	isb sy
	ldmfd sp!, {r4-r11, pc}

.global cache_and_mmu_disable
cache_and_mmu_disable:
	stmfd sp!, {lr}
	bl dcache_flush_disable				@ Flush caches
	dsb sy
	isb sy
	READ_CP_ASM(r0, ID_SCTLR)			@ Disable MMU
	bic r0, #1
	WRITE_CP_ASM(r0, ID_SCTLR)
	dsb sy
	isb sy
	mov r1, #0							@ We use ASID 0 for all tlb entries
	WRITE_CP_ASM(r1, ID_TLBIASID)		@ Clear non global tlb entries (B4.2.2)
	dsb sy
	isb sy
	ldmfd sp!, {pc}

.global cache_and_mmu_enable
cache_and_mmu_enable:
	dsb sy
	isb sy
	READ_CP_ASM(r0, ID_SCTLR)			@ Enable MMU & caches
	orr r0, #0x1000						@ ICACHE
	orr r0, #0x5						@ MMU | DCACHE
	WRITE_CP_ASM(r0, ID_SCTLR)
	dsb sy
	isb sy
	bx lr

/* Flush whole data cache by set/way (as seen in linux cache-v7.S)
 * no memory accesse there (trash r0-r6, r9-r11) */
dcache_flush_all_:
	dmb								@ synchronize memory accesses
	READ_CP_ASM(r0, ID_CLIDR)		@ r0 = CLIDR
	mov r3, r0, lsr #23
	ands r3, #0xE					@ r3 = LoC<<1
	beq .finished					@ loc is 0, nothing to clean
	mov r10, #0						@ start clean at cache level=0
.loop1:
	tst r0, #6						@ check if we have a data cache there
	beq .skip
	WRITE_CP_ASM(r10, ID_CCSELR)	@ Select cache level (r10 = level<<1)
	isb								@ flush pipeline to synchronize ccsr & csidr
	READ_CP_ASM(r1, ID_CCSIDR)		@ r1 = CCSIDR
	and r2, r1, #7					@ extract the length of the cache lines
	add r2, #4						@ r2 = log2(line size in bytes)
	ubfx r4, r1, #3, #10			@ r4 = ways count (csidr.Associativity)
	clz	r5, r4						@ r5 = bit position of way size increment
	ubfx r6, r1, #13, #15			@ r6 = clidr.num_sets
.loop2:
	mov r9, r4						@ r9 = copy of num_ways
.loop3:
	/* ARMv7 Ref B4.2.1 : Set/way */
	orr	r11, r10, r9, lsl r5		@ factor way and cache number in r11
	orr r11, r11, r6, lsl r2		@ factor set number in r11
	WRITE_CP_ASM(r11, ID_DCCISW)	@ clean & invalidate by set/way
	subs r9, #1						@ decrement the way
	bge .loop3
	subs r6, #1						@ decrement the index
	bge .loop2
.skip:
	add r10, #2						@ increment cache number
	lsl r0, #3						@ shift clidr up to next cache level
	cmp r3, r10
	bgt .loop1
.finished:
	mov r0, #0						@ switch back to cache level 0 in ccsr
	WRITE_CP_ASM(r0, ID_CCSELR)
	dsb								@ synchronize execution
	isb								@ flush pipeline
	bx lr

/* r0 = addr, r1 = size */
.global dcache_clean_range
dcache_clean_range:
	dmb
	mov	ip, #4
	sub	r1, r1, #1				@ r1 = (size-1)
	READ_CP_ASM(r3, ID_CTR)
	ubfx	r3, r3, #16, #4
	lsl	r3, ip, r3				@ r3 = dcache line_size
	add	r2, r1, r3
	sub	r1, r3, #1
	add	r2, r2, r0
	and	r2, r2, r1				@ r2 = end_addr: (addr+size+line_size-1)&(line_size -1)
	and	r0, r0, r1				@ r0 = start_addr: addr & (line_size-1)
	dsb	sy
	cmp	r0, r2					@ check if the range is empty
	bcs	2f
1:
	WRITE_CP_ASM(r0, ID_DCCMVAC)	@ clear dcache by MVA
	add	r0, r0, r3					@ addr += line_size
	cmp	r2, r0
	bhi	1b
2:
	dsb	sy
	isb sy
	bx	lr

/* r0 = addr, r1 = size */
.global dcache_inval_range
dcache_inval_range:
	dmb
	mov	ip, #4
	sub	r1, r1, #1				@ r1 = (size-1)
	READ_CP_ASM(r3, ID_CTR)
	ubfx	r3, r3, #16, #4
	lsl	r3, ip, r3				@ r3 = dcache line_size
	add	r2, r1, r3
	sub	r1, r3, #1
	add	r2, r2, r0
	and	r2, r2, r1				@ r2 = end_addr: (addr+size+line_size-1)&(line_size -1)
	and	r0, r0, r1				@ r0 = start_addr: addr & (line_size-1)
	dsb	sy
	cmp	r0, r2					@ check if the range is empty
	bcs	2f
1:
	WRITE_CP_ASM(r0, ID_DCIMVAC)	@ inval dcache by MVA
	add	r0, r0, r3					@ addr += line_size
	cmp	r2, r0
	bhi	1b
2:
	dsb	sy
	isb sy
	bx	lr

/* r0 = addr, r1 = size */
.global dcache_flush_range
dcache_flush_range:
	dmb
	mov	ip, #4
	sub	r1, r1, #1				@ r1 = (size-1)
	READ_CP_ASM(r3, ID_CTR)
	ubfx	r3, r3, #16, #4
	lsl	r3, ip, r3				@ r3 = dcache line_size
	add	r2, r1, r3
	sub	r1, r3, #1
	add	r2, r2, r0
	and	r2, r2, r1				@ r2 = end_addr: (addr+size+line_size-1)&(line_size -1)
	and	r0, r0, r1				@ r0 = start_addr: addr & (line_size-1)
	dsb	sy
	cmp	r0, r2					@ check if the range is empty
	bcs	2f
1:
	WRITE_CP_ASM(r0, ID_DCCIMVAC)	@ clean & inval dcache by MVA
	add	r0, r0, r3					@ addr += line_size
	cmp	r2, r0
	bhi	1b
2:
	dsb	sy
	isb sy
	bx	lr
