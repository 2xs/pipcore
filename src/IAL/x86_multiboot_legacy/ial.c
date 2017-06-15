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
 * \file ial.c
 * \brief x86 interrupt abstraction layer.
 */

#include <stdint.h>
#include "debug.h"
#include "ial.h"
#include "x86int.h"
#include "x86hw.h"
#include "port.h"
#include "pic8259.h"
#include "maldefines.h"

#define MAX_VINT (uint32_t)0x100

#define ASSERT(u) \
	if (!(u)){ \
		kprintf("[%s:%d] Assert failed: " #u, __FILE__, __LINE__); \
		panic(); \
	}

#ifndef NULL
#define NULL ((void*)0)
#endif

extern uint32_t timer_ticks; //!< Timer ticks counter

extern uint32_t readCR2(void); //!< Reads CR2 register (faulting address)

extern int checkChild(const uintptr_t partition, const uint32_t l1, const uintptr_t va);

/**
 * \fn isKernel(uint32_t cs)
 * \brief Determines if we're in kernel mode or not.
 * \param cs Code segment
 * \return 1 if we're in kernel mode, 0 else
 */
int
isKernel (uint32_t cs)
{
  return cs == 8;
}
/**
 * \fn void panic (void)
 * \brief Just a loop acting like a kernel panic
 */
void
panic (void)
{
  krn_puts ("guru meditation\n");
  __asm__ ("cli; hlt");
	for(;;);
}

/**
 * \fn static inline uint32_t readPD(uint32_t partition)
 * \brief Reads the page directory address for a partition
 * \param partition The target partition
 * \return The page directory, as a physical address
 */
static inline uint32_t readPD(uint32_t partition)
{
	return (uint32_t)readPhysicalNoFlags((uintptr_t)partition, indexPD()+1);
}

/* TODO: remove me:
	- we can get paddr of child /w checkChild
	- vidt should be written in the partition descriptor by createPartition.
*/
static uint32_t
readPaddr(uint32_t partition, uint32_t vaddr)
{
	uint32_t t, v;

	/* read table addr & check if present */
	t = (uint32_t)readPhysical(readPD(partition), (vaddr>>22) & 0x3ff);
	if ((t & 1) == 0){
		DEBUG(TRACE, "no addr %x at idx 0\n", vaddr);
		return (uint32_t)-1;
	}

	/* read vidt physicall addr & check if present */
	v = (uint32_t)readPhysical((uintptr_t)(t &~0xfff),(vaddr>>12)&0x3ff);
	if ((v & 1) == 0){
		DEBUG(TRACE, "no addr %x at idx 1\n", vaddr);
		return (uint32_t)-1;
	}

	return v & ~0xfff;
}

/**
 * \fn static uint32_t readVidt(uint32_t descr)
 * \brief readVidt Reads the physical address of the VIDT of a given partition
 * \param descr The partition descriptor
 * \return Physical address of VIDT
 */
static uint32_t readVidt(uint32_t descr)
{
	return readPaddr(descr, 0xfffff000);
}

/**
 * \fn void readVidtInfo(uint32_t vidt, uint32_t vint_no, uint32_t *eip, uint32_t *esp, uint32_t *flags)
 * \brief Reads the information stored into the VIDT for the given partition and interrupt number
 * \param vidt VIDT address
 * \param vint_no Interrupt number
 * \param eip Storage for EIP
 * \param esp Storage for ESP
 * \param flags Storage for flags
 * \post Put eip, esp & flags from vidt with (trusted) vint_no into the parameter's destination area
 */
void
readVidtInfo(uint32_t vidt, uint32_t vint_no, uint32_t *eip, uint32_t *esp, uint32_t *flags)
{
	ASSERT(vint_no < MAX_VINT);

	*eip = (uint32_t)readPhysical (vidt, (2 * vint_no));
	*esp = (uint32_t)readPhysical (vidt, (2 * vint_no) + 1);
	*flags = (uint32_t)readPhysical (vidt, getTableSize () - 1);
}

/**
 * \fn uint32_t isInterruptHandled(uint32_t partition, uint32_t vint)
 * \brief Checks whether an interrupt is handled or not by a partition
 * \param partition Target partition
 * \param vint Virtual interrupt
 * \return 1 if the interrupt is handled, 0 else
 */
uint32_t
isInterruptHandled(uint32_t partition, uint32_t vint)
{
	uint32_t vidt, eip, esp, flags;

	/* get paddr of partition's vidt */
	if ((vidt=readVidt(partition)) == (uint32_t)-1){
		DEBUG(WARNING, "No vidt in partition %x\n", partition);
		return 0;
	}
	readVidtInfo(vidt, vint, &eip, &esp, &flags);

	if ( !eip							/* no handler registerd*/
		|| (vint > 0 && esp == 0)	/* no stack && !reset */
		|| ((vint == 0 || vint > 32) && (flags & 1)) /* int masked */
	){
		DEBUG (TRACE, "Unhandled(%d): eip=%x, esp=%x\n", vint, eip, esp);
		return 0;
	}
	else
	{
		return 1;
	}
}

/* \fn saveCurrentUserContext(uint32_t eip, pushad_regs_t *regs, uint32_t isr)
 * \brief Save interrupted partition context in it's vidt
 * \param eip		User eip
 * \param eflags	User eflags
 * \param regs		User registers
 * \param isr Save in isr context */
void
saveCurrentUserContext(uint32_t eip, uint32_t eflags, const pushad_regs_t *regs, unsigned index)
{
	uint32_t vidt;
	user_ctx_t *ctx;
	uint32_t partition = getCurPartition();

	DEBUG (TRACE, "Save context of partition %x at ip %x sp %x (%x)\n",
			partition, eip, regs->esp, 0x800 + 0x40*(index) );

	/* read vidt paddr*/
	if ((vidt=readVidt(partition)) == (uint32_t)-1){
		DEBUG(WARNING, "No vidt in partition %x\n", partition);
		return;
	}
	/*	int/isr saved by kernel in current partition's vidt (see x86int.h)
		800h: intCtx		// saved by pip when an interrupt occurs
		840h: isrCtx		// saved by pip when a fault occurs
		880h: notifyChildCtx	// saved by pip on a call of notify(child)
		8C0h: notifyParentCtx	// saved by pip on a call of notify(parent)
	*/

	/* ploploplop (FIXME) */
	disable_paging();
	ctx = (user_ctx_t*)(vidt + 0x800 + 0x40*index);

	ctx->eip = eip;
	ctx->pipflags = *(uint32_t*)(vidt+0xffc);
	ctx->eflags = eflags;
	ctx->regs = *regs;

	if (ctx->valid)
	{
		DEBUG(ERROR, "Overwriting a previous valid interrupted context\n");
		/* wathever */
	}
	ctx->valid = 1;

	enable_paging();
}

/**
 * \fn static void saveUserIntContext(int_ctx_t* ctx, unsigned index)
 * \brief Saves interrupted user context
 * \param ctx Target context list
 * \param index Index into the list
 */
static void
saveUserIntContext(int_ctx_t* ctx, unsigned index)
{
	/* In interrupt handlers, the esp pointer present in pusha regs
	 * is kernelland. We give only userland regs to saveUserCtx*/
	pushad_regs_t regs = ctx->regs;
	regs.esp = ctx->useresp;

	saveCurrentUserContext(ctx->eip, ctx->eflags, &regs, index);
}

/**
 * \fn static void saveUserGateContext(gate_ctx_t* gs, unsigned index)
 * \brief Saves interrupted user context during a callgate access
 * \param gs Target context list
 * \param index Index into the list
 */
static void
saveUserGateContext(gate_ctx_t* gs, unsigned index)
{
	/* We'll save this one only when a callgate triggers
	 * a fault in caller, so */
	saveCurrentUserContext(gs->eip, 0, &gs->regs, index);
}

/**
 * \fn void yieldRootPartition(void)
 * \brief Sends a null signal to root partition
 * \warning This is insane.
 */
void yieldRootPartition(void)
{
	dispatch2(getRootPartition(), 0, 0, 0, 0);
}

/* \fn irqHandler (int_ctx_t *is)
	\brief Interrupt handler logic
	\param is Interrupt context 
*/
void
irqHandler(int_ctx_t *is)
{
	uint32_t vint;

	/* Acknowledge*/
	if (is->int_no >= 40)
		outb (PIC2_COMMAND, PIC_EOI);
	outb (PIC1_COMMAND, PIC_EOI);

	/* Increment timer ticks */
	if (is->int_no == 32)
		timer_ticks++;

	if (isKernel(is->cs))
	{
	/* We might get there mostly when handling the first 
	 * instruction of a callgate (cli).
	 * When handling a callgate, we consider that current_partition
	 * variable holds a reference to the calling partition.
	 * Therefore, to keep current_partition consistent we cannot allow context 
	 * switch during callgate handling. */
		DEBUG (ERROR, "Skipping hw interrupt while kernelland\n");
		return;
	}

	/* Our virtual interrupt number, skipping reset/resume */
	vint = is->int_no + 1;
	if (vint >= MAX_VINT)
	{
		DEBUG(ERROR, "Invalid interrupt %d ?\n", vint);
		return;
	}

	/* If partition is multiplexer and interrupts are cleared,
	 * skip & resume context w/o saving */
	if ( !isInterruptHandled(getRootPartition(), vint))
	{
		DEBUG(WARNING, "Skipping unhandled interrupt %d\n", vint);
		return;
	}
	/* Save userland interrupt context */
	saveUserIntContext(is, INT_CTX);

	/* Dispatch interrupt to multiplexer w/ int_no as first argument */
	dispatch2(getRootPartition(), vint, is->int_no, 0, 0);
	ASSERT(0);
}

/**
 * \fn isrHandler(registers_t regs)
 * \param regs Registers
 * \brief Generic handler for ISR
 */
void
isrHandler (int_ctx_t *is)
{
	uint32_t from, to, vint;
	uint32_t data1 = is->err_code, data2 = 0;
	uint8_t isRoot = getCurPartition() == getRootPartition();

	DEBUG(WARNING, "Handling exception %d from %sland at eip %X\n",
		is->int_no, isKernel(is->cs)?"kernel":"user", is->eip);

	/* Some page fault debugging */
	if (is->int_no == 14)
	{
		data2 = readCR2();

		DEBUGRAW ("\e[91m");
		DEBUG (CRITICAL, "Page fault, Faulting EIP: %x\n", is->eip);
		DEBUG (CRITICAL, "page is %s, tried to %s from %s at address %x\n",
			(data1&1) ? "present" : "missing", (data1&2)? "write" : "read", 
			(data1&4) ? "userland" : "kernel land", data2);
		DEBUGRAW ("\e[91m");
	}
	/* Check for kernel faults */
	if (isKernel (is->cs))
	{ 
		if(is->int_no < 32)	// CPU ISR in kernel land?
		{
			DEBUGRAW ("\e[91m");
			DEBUG (CRITICAL, "Fault in kernel land! Mesovisor must have done "
					"something wrong. Now panicking kernel.\n");
			DEBUGRAW ("\e[0m");
			panic ();
		}
		/* TODO: isr handling ?*/
		ASSERT(0);
		return;
	}

	vint = is->int_no+1;
	if (vint >= MAX_VINT){
		DEBUG(WARNING, "Skipping invalid vint %d\n", vint);
		return;
	}
	/* whom should we dispatch to */
	if (isRoot)
	{
		to = getRootPartition();
		from = 0;
	}
	else{
		/* paddr of parent partition */
		to = readPhysicalNoFlags(getCurPartition(), PPRidx()+1);
		/* vaddr of faulty partition in parent */
		from = readPhysicalNoFlags(to, indexPR());
	}
	/* Save faulty context */
	saveUserIntContext(is, ISR_CTX);

	/* If parent don't handle isr */
	if (!isInterruptHandled(to, vint))
	{
		/* if a multiplexer fault gets unhandled, panic */
		if (isRoot && vint <= 32)
		{
			DEBUG(CRITICAL, "Multiplexer fault unhandled\n");
			panic();
		}
		/* TODO: check for double fault in root */
		DEBUG(WARNING, "Unhandled fault in %x\n", getCurPartition());
		yieldRootPartition();
	}

	/* Dispatch fault */
	dispatch2(to, vint, data1, data2, from);
	ASSERT(0);
}

/*! \fn dispatchGlue (uint32_t descriptor, uint32_t vint, uint32_t data1, uint32_t data2)
	\brief Enable a partition to trigger a vint on a child or the parent
	\param descriptor Vaddr of child partition or 0 for parent partition
	\param notify	Boolean to distinguish notify (w/ context saving)
	\param vint	Virtual interrupt number
	\param data1	vint handler param
	\param data2 	vint handler param 
 */
void
dispatchGlue (uint32_t descriptor, uint32_t vint, uint32_t notify,
			  uint32_t data1, uint32_t data2,
			  gate_ctx_t *ctx
){
	uint32_t from, to;
	uint32_t cur = getCurPartition();
	uint32_t fault;

	DEBUG(TRACE, "dispatchGlue(%d) %x -> %x\n", vint, getCurPartition(), descriptor);

	/* FIXME: This function should return to caller context with some 
	 *		  error code when notifying */
	if (vint >= MAX_VINT)
	{
		DEBUG(ERROR, "Invalid vint %d\n", vint);
		return;
	}
	/** 
	 * If the calling partition is dispatching a fault to it's parent,
	 * save it's context the same way we do for 'real' exceptions.
	 */
	fault = (descriptor == 0 && ((vint > 0 && vint <= 32) || vint >= 64));
	if (fault){
		saveUserGateContext(ctx, ISR_CTX);
	}
	else if (notify == 1)
	{
	/* Save calling context on a call of notify() */
		if (descriptor == 0)
			saveUserGateContext(ctx, NOTIF_PARENT_CTX);
		else
			saveUserGateContext(ctx, NOTIF_CHILD_CTX);
	}

	/* A child notifies it's parent */
	if (descriptor == 0)
	{
		if (cur == getRootPartition()){
			DEBUG(CRITICAL, "multiplexer has no parent\n");
			return;
		} 
		/* paddr of parent partition's descriptor */
		to = readPhysicalNoFlags(getCurPartition(), PPRidx()+1);
		/* vaddr of child in parent's partition */
		from = readPhysicalNoFlags(getCurPartition(), indexPR());
	}
	/* A parent notifies a child */
	else {
		if (!checkChild(getCurPartition(), getNbLevel(), descriptor))
		{
			DEBUG(WARNING, "Partition %x tried to access invalid child %x",
				getCurPartition(), descriptor);
			return;
		}
		/* TODO: checkChild should return paddr of child descriptor */
		to = readPaddr(getCurPartition(), descriptor);
		DEBUG(TRACE, "dispatch to child %x\n", to);
		/* identify parent by 0 */
		from = 0;
		/* re-enable interrupts in caller (TODO: may I?)*/
		*(uint32_t*) 0xfffffffc &= ~1;
	}

	if (!isInterruptHandled(to, vint))
	{
		if (fault)
		{
			/* A child fault was not handled by its parent.
			 * we should not return to the faulty context */
			/* FIXME: what should we do ?*/
			yieldRootPartition();
		}
		DEBUG(CRITICAL, "Unhandled int, back to caller\n");
		return;
	}

	DEBUG(TRACE, "dispatchGlue(from %x, to %x, int %d, data %x %x)\n",
		from, to, vint, data1, data2);
 
	/* go dispatch */
	dispatch2(to, vint, data1, data2, from);

	/* dispatch always suceeds !*/
	ASSERT(0);
}


/**
 * \fn void dispatch2(uint32_t partition, uint32_t vint, uint32_t data1, uint32_t data2, uint32_t caller)
 * \brief Dispatchs an interrupt to a partition, switching the current execution pointer, stack pointer and active page directory pointer to the required ones
 * \param partition The target partition, given as physical address
 * \param vint The virtual interrupt to dispatch
 * \param data1 handler data
 * \param data2 handler more handler data
 * \param caller handler argument 3, caller identifier: vaddr of child partition or 0 for parent
 */
void
dispatch2 (uint32_t partition, uint32_t vint,
		uint32_t data1, uint32_t data2, uint32_t caller)
{
	uint32_t vidt, eip, esp, vflags;

	/* vint must be validate before calling dispatch */
	ASSERT(vint < MAX_VINT);

	/* vidt must be present */
	ASSERT((vidt=readVidt(partition)) != (uint32_t)-1);

	/* gather interrupt handler & vflags infos from vidt */
	readVidtInfo(vidt, vint, &eip, &esp, &vflags);

	/* mask vint in partition's vidt */
	writePhysical(vidt, getTableSize()-1, vflags|1);

	/* Activate partition */
	DEBUG(TRACE, "Activate partition %x\n", partition);
	activate(readPhysicalNoFlags(partition, indexPD () + 1));
	updateCurPartition (partition);

	/* switch to userland */
	extern void dispatchAsm(uintptr_t eip, uintptr_t esp, uint32_t data1,
				uint32_t data2, uint32_t caller);
	dispatchAsm (eip, esp, data1, data2, caller);
}

/**
 * \fn void resume (uint32_t descriptor, user_ctx_role_t ctxNo)
 * \brief 		Activate a partition and switch to context
 * \param descriptor	The partition to resume (0 for parent)
 * \param ctxNo 	Index of context to resume */
void resume (uint32_t descriptor, user_ctx_role_t ctxNo)
{
	uint32_t partition, vidt, ctxValid;
	user_ctx_t *ctx;

	if (ctxNo >= INVALID_CTX ){
		DEBUG(WARNING, "partition %x tried to resume context %d\n",
			getCurPartition(), ctxNo);
		yieldRootPartition();
	}

	/* Child tries to resume it's parent. ie, return from notify */
	if (descriptor == 0)
	{
		/* Multiplexer is it's own parent there */
		if (getCurPartition() == getRootPartition())
		{
			partition = getRootPartition();
			/* multiplexer can resume any of it's contexes */
		}
		else
		{
			/* Parent's descriptor */
			partition = readPhysicalNoFlags(getCurPartition(), PPRidx()+1);
			/* only the parent's notify context can be resumed there */
			if (ctxNo != NOTIF_CHILD_CTX){
				DEBUG(WARNING, "Child partition %x tried to resume"
					" it's parent w/o notify context",
					getCurPartition());
				yieldRootPartition();
			}
		}
	}
	/* A parent tries to resume one of his childs */
	else{
		if (!checkChild(getCurPartition(), getNbLevel(), descriptor))
		{
			DEBUG(WARNING, "Partition %x tried to access invalid child %x",
				getCurPartition(), descriptor);
			yieldRootPartition();
		}
		/* FIXME: checkChild should just return paddr of child */
		partition = readPaddr(getCurPartition(), descriptor);
	}

	DEBUG(TRACE, "partition %x resuming context %d of %x\n",
		getCurPartition(), ctxNo, partition);

	/* Resume interrupts in caller */
	*(uint32_t*)0xfffffffc &= ~1;

	/* Now find & check resume context. (FIXME FIXME: this is very crade ) */
	vidt=readVidt(partition);
	ASSERT(vidt != (uint32_t)-1);
	ctx = (user_ctx_t*)(0x800 + 0x40*(ctxNo));
	ctxValid = readPhysical(vidt, (uint32_t)(&ctx->valid)>>2);
	if (!ctxValid)
	{
		DEBUG(WARNING, 
			"Partition %x tries to resume invalid ctx %d at %x\n",
			getCurPartition(), ctxNo, (uint32_t)ctx);
		/* Just resume the multiplexer to trigger some yielding */
		yieldRootPartition();
	}

	/* Activate target partition */
	activate(readPhysicalNoFlags(partition, indexPD () + 1));
	updateCurPartition (partition);

	/* FIXME: what the heck */
	ctx = (user_ctx_t*)((uint32_t)ctx|0xfffff000);
	/* We now have a valid context to resume. */
	ctx->valid = 0;

	extern void resumeAsm(user_ctx_t*);
	resumeAsm(ctx);
}
