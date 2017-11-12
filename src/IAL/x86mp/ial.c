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

/**
 * \file ial.c
 * \brief x86 interrupt abstraction layer.
 */

#include <stdint.h>
#include "debug.h"
#include "ial.h"
#include "x86int.h"
#include "port.h"
#include "pic8259.h"
#include "libc.h"
#include "maldefines.h"
#include "mmu.h"
#include "ial_defines.h"


#define MAX_VINT (uint32_t)0x100
#define MAX_PCID 4096

uint32_t next_pcid = 1; /* Next available PCID */
extern uint32_t pcid_enabled;

uint32_t* ioapic_base = 0x0; /* IO APIC base address */
uint32_t* lapic_base = 0x0; /* LAPIC base address */

#define ASSERT(u) \
	if (!(u)){ \
		kprintf("[%s:%d] Assert failed: " #u "\n", __FILE__, __LINE__); \
		panic(0); \
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
 * \fn dumpRegs(int_ctx_t* is, uint32_t outputLevel)
 * \brief Dumps the registers of a saved interrupt context onto the serial output.
 * \param is Interrupted state
 * \param outputLevel Serial log debugging output level
 */
void dumpRegs(int_ctx_t* is, uint32_t outputLevel)
{
	DEBUG(TRACE, "Register dump: eax=%x, ebx=%x, ecx=%x, edx=%x\n",
		  GENERAL_REG(is, eax),
		  GENERAL_REG(is, ebx),
		  GENERAL_REG(is, ecx),
		  GENERAL_REG(is, edx));
	DEBUG(TRACE, "               edi=%x, esi=%x, ebp=%x, esp=%x\n",
		  GENERAL_REG(is, edi),
		  GENERAL_REG(is, esi),
		  GENERAL_REG(is, ebp),
		  OPTIONAL_REG(is, useresp));
	if(isKernel(OPTIONAL_REG(is, cs)))
	{
		DEBUG(TRACE, "               cs=%x, eip=%x, int=%x\n",
			  OPTIONAL_REG(is, cs),
			  OPTIONAL_REG(is, eip),
			  OPTIONAL_REG(is, int_no));
	} else {
		DEBUG(TRACE, "               cs=%x, ss=%x, eip=%x, int=%x\n",
			  OPTIONAL_REG(is, cs),
			  OPTIONAL_REG(is, ss),
			  OPTIONAL_REG(is, eip),
			  OPTIONAL_REG(is, int_no));
	}
}

/**
 * \fn uint32_t saveCaller(int_ctx_t *is)
 * \brief Saves the caller partition's state
 * \param is Interrupted state location
 * \return Address of the saved context
 */
uint32_t saveCaller(int_ctx_t *is)
{
	IAL_DEBUG(INFO, "Saving interrupted state matching registers at %x\n", is);
	
	/* Copy the interrupted info into the caller's stack / VIDT buffer */
	if((*PIPFLAGS & 0x00000001) == 0x1) /* VCLI set */
	{
		IAL_DEBUG(INFO, "VCLI flag is set; saving into context buffer at %x\n", VIDT_CTX_BUFFER);
		memcpy((void*)VIDT_CTX_BUFFER, is, SIZEOF_CTX);
		/* dumpRegs((int_ctx_t*)VIDT_CTX_BUFFER); */
		dumpRegs(VIDT_CTX_BUFFER, TRACE);
		
		/* Partition is interrupted when it shouldn't be, this is tricky */
		*(uintptr_t*)(VIDT_CTX_BUFFER - sizeof(uintptr_t)) = *PIPFLAGS;
		
		return (uint32_t)VIDT_CTX_BUFFER;
	}
	else
	{
		IAL_DEBUG(INFO, "VCLI flag is not set; saving into stack at %x\n", OPTIONAL_REG(is, useresp));
		memcpy((void*)(OPTIONAL_REG(is, useresp) - SIZEOF_CTX), is, SIZEOF_CTX);
		
		/* Update resume (int. 0) interrupt ESP to point to our newly updated stack */
		VIDT_INT_ESP_SET(0, OPTIONAL_REG(is, useresp) - SIZEOF_CTX);
		IAL_DEBUG(INFO, "Set resume stack to %x.\n", OPTIONAL_REG(is, useresp) - SIZEOF_CTX);
		
		dumpRegs((void*)(OPTIONAL_REG(is, useresp)) - SIZEOF_CTX, TRACE);

		/* Push current state as well, which is stored into 0xFFFFFFFC */
		*(uintptr_t*)(OPTIONAL_REG(is, useresp) - SIZEOF_CTX - sizeof(uintptr_t)) = *PIPFLAGS;
		
		return (uint32_t)(OPTIONAL_REG(is, useresp) - SIZEOF_CTX);
	}

	
	
	
	/* Change interrupt level */
	/* IAL_DEBUG(DEBUG, "Changing interrupt level : was %d\n", INTLEVEL_GET);
	INTLEVEL_SET(OPTIONAL_REG(is, int_no));
	IAL_DEBUG(DEBUG, "Changing interrupt level : is now %d\n", INTLEVEL_GET); */
}

/**
 * \fn void saveCallgateCaller(gate_ctx_t* ctx)
 * \brief Saves the caller partition's state from a callgate-interrupted context
 * \param ctx Callgate context location
 */
void saveCallgateCaller(gate_ctx_t* ctx)
{
	IAL_DEBUG(TRACE, "Building dummy context info from callgate context %x\n", ctx);
	/* Build dummy context structure */
	int_ctx_t is;
	
	/* Copy general register info */
	memcpy((void*)&(is.regs), &(ctx->regs), sizeof(pushad_regs_t));
	
	/* TODO : the following & and * play is crap, I should consider removing that "const" attribute someday */
	
	/* Copy EIP */
	*(uintptr_t*)(&(is.eip)) = ctx->eip;
	
	/* Fake useresp to unify resume() behavior */
	*(uintptr_t*)(&(is.useresp)) = ctx->regs.esp;
	
	/* We should also get EFLAGS somewhere... */
	uint32_t eflags;
	__asm volatile("PUSHF; POP %%EAX; MOV %%EAX, %0"
				   : "=r"(eflags));
	
	*(uintptr_t*)(&(is.eflags)) = eflags;
	
	/* Remaining stuff might be crap; whatever, save caller using this structure */
	saveCaller(&is);
}

/**
 * \fn void panic (int_ctx_t *is)
 * \brief Just a loop acting like a kernel panic
 */
void panic (int_ctx_t *is)
{
	DEBUG(CRITICAL, "Pip kernel panic - something happened\n");
	if(is) {
		dumpRegs(is, CRITICAL);
	}
	DEBUG(CRITICAL, "\tSystem halted. ~\n");
	__asm volatile("cli; hlt;");
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
 * \fn void yieldRootPartition(void)
 * \brief Sends a null signal to root partition
 * \warning This is insane.
 */
void yieldRootPartition(void)
{
	dispatch2(getRootPartition(), 0, 0, 0, 0);
}

/**
 * \fn genericHandler(registers_t regs)
 * \param regs Registers
 * \brief Generic handler for ISR
 */
void
genericHandler (int_ctx_t *is)
{
	uint32_t vint, target, from, data1, data2;
	
	data1 = 0;
    extern uint32_t timer_ticks;
    
    /* Increment ticks on timer interrupt */
    if(is->int_no == 32)
        timer_ticks++;

    IAL_DEBUG(CRITICAL, "Interrupt %d occured through APIC, ticks: %d\n", is->int_no, timer_ticks);	
	/* A bit of the handling is different with hardware interrupts */
	if(INT_IRQ(is->int_no))
	{
		IAL_DEBUG(TRACE, "Got hardware interrupt %d.\n", is->int_no);
		/* Acknowledge hardware interrupt */
		if (is->int_no >= 40)
			outb (PIC2_COMMAND, PIC_EOI);
		outb (PIC1_COMMAND, PIC_EOI);
		
		/* Ignore kernel-land IRQ */
		if (isKernel(is->cs))
		{
			IAL_DEBUG (TRACE, "Ignoring kernel-land IRQ.\n");
			return;
		}
		
		IAL_DEBUG(TRACE, "Current partition is %x, root partition is %x.\n", PARTITION_CURRENT, PARTITION_ROOT);
		
		/* Special case : root partition might be running - TODO : remove this when it gets stable */
		/*if(PARTITION_CURRENT == PARTITION_ROOT)
		{
			IAL_DEBUG(TRACE, "Ignoring hardware interrupt while root partition is running.\n");
			return;
		}*/
		
		/* Special case : root partition might be VCLI'd - check this */
		uintptr_t rootVidt = readVidt(PARTITION_ROOT);
		
		IAL_DEBUG(TRACE, "Root VIDT at %x.\n", rootVidt);
		uint32_t flags = readPhysical(rootVidt, getTableSize()-1); /* *(uint32_t*)(rootVidt + 0x1000 - sizeof(uint32_t)); */
		IAL_DEBUG(TRACE, "Root VIDT flags are set to %x.\n", flags);
		if(flags & 0x1)
		{
			IAL_DEBUG(TRACE, "Ignoring hardware interrupt while root partition is busy.\n");
			return;
		}
		
		/* Set target as root partition */
		target = PARTITION_ROOT;
		from = PARTITION_CURRENT;
		
	} else {
		IAL_DEBUG(TRACE, "Got fault interrupt %d.\n", is->int_no);
		
		/* Page Fault */
		if(is->int_no == 0xE)
		{
			uint32_t cr2;
			__asm volatile("MOV %%CR2, %0;":"=r"(cr2));
			IAL_DEBUG (TRACE, "CR2 set to %x.\n", cr2);
			data1 = cr2;
			dumpRegs(is, CRITICAL);
		}
		
		if(is->int_no == 0xD)
		{
			IAL_DEBUG (CRITICAL, "Protection fault error code set to %x.\n", is->err_code);
			IAL_DEBUG (CRITICAL, "Partition %x faulted at EIP %x.\n", PARTITION_CURRENT, is->eip);
			dumpRegs(is, CRITICAL);
		}

		
		/* Kernel faults should not happen. Panic. */
		if (isKernel(is->cs))
		{
			IAL_DEBUG (CRITICAL, "Encountered fault (%x) within kernel. Halting system.\n", is->int_no);
			panic(is);
		}

		/* Set target as parent partition */
		
		/* Get PAddr of Parent Partition */
		target = readPhysicalNoFlags(PARTITION_CURRENT, PPRidx()+1);
		/* Get VAddr of caller in parent partition */
		from = readPhysicalNoFlags(PARTITION_CURRENT, indexPR());
	}
	
	/* Our virtual interrupt number, skipping reset/resume */
	vint = is->int_no + 1;
	if (vint >= MAX_VINT)
	{
		IAL_DEBUG(ERROR, "Invalid interrupt number %x ?\n", vint);
		return;
	}
	
	/* Current partition has been interrupted. Save its state. */
	uint32_t stackAddr = saveCaller(is);
	
	//ASSERT(0);
	dispatch2(target, vint, data1, stackAddr, from);
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
)
{
	uint32_t to, from;
	
	/* First, save caller context */
	IAL_DEBUG(TRACE, "Userland called dispatch(); saving context\n");
	saveCallgateCaller(ctx);
	
	/* Perform some sanity checks */
	ASSERT(vint < MAX_VINT);

	/* Identify caller and recipient */
	if (descriptor == 0)
	{
		/* A child is notifying a parent of something */
		if (PARTITION_CURRENT == PARTITION_ROOT){
			IAL_DEBUG(CRITICAL, "Root partition has no parent; incoherent behavior, halting\n");
			panic(0);
		}
		/* Get PAddr of Parent Partition */
		to = readPhysicalNoFlags(PARTITION_CURRENT, PPRidx()+1);
		/* Get VAddr of caller in parent partition */
		from = readPhysicalNoFlags(PARTITION_CURRENT, indexPR());
	}
	/* A parent notifies a child */
	else {
		if (!checkChild(PARTITION_CURRENT, getNbLevel(), descriptor))
		{
			IAL_DEBUG(WARNING, "Partition %x tried to access invalid child %x\n", getCurPartition(), descriptor);
			return;
		}
		
		/* Get the physical address of child descriptor */
		to = readPaddr(PARTITION_CURRENT, descriptor);
		
		IAL_DEBUG(TRACE, "Dispatching to child %x\n", to);
		
		/* Identify parent by 0 */
		from = 0;
		
		/* re-enable interrupts in caller (TODO: may I?)*/
		*(uint32_t*) 0xfffffffc &= ~1;
	}
	
	/* Perform the dispatch thingy */
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
	IAL_DEBUG(TRACE, "Requested dispatch of VINT %d to partition %x, caller is %x.\n", vint, partition, caller);
	uint32_t vidt, eip, esp, vflags;
	
	/* Check interrupt range */
	ASSERT(vint < MAX_VINT);
	
	/* Check VIDT validity */
	if(!((vidt=readVidt(partition)) != (uint32_t)-1))
	{
		IAL_DEBUG(CRITICAL, "0ops. Partition=%x, vint=%x, caller=%x\n", partition, vint, caller);
		ASSERT(0);
	}
	
	/* Read VIDT info */
	readVidtInfo(vidt, vint, &eip, &esp, &vflags);
	
	/* VCLI the partition */
	IAL_DEBUG(TRACE, "Dispatch2: VCLI'd vidt @%x.\n", vidt);
	writePhysical(vidt, getTableSize()-1, vflags|1);
	
	/* Activate partition */
	IAL_DEBUG(TRACE, "Switching to partition %x's Page Directory.\n", partition);
	updateCurPartition (partition);
	if(pcid_enabled)
		activate(readPhysicalNoFlags(partition, indexPD () + 1) | readPhysical(partition, 12));
	else
		activate(readPhysicalNoFlags(partition, indexPD () + 1));
	
	/* Switch execution to userland */
	extern void dispatchAsm(uintptr_t eip, uintptr_t esp, uint32_t data1,
							uint32_t data2, uint32_t caller);
	dispatchAsm (eip, esp, data1, data2, caller);
}

/**
 * \fn void resume (uint32_t descriptor, user_ctx_role_t ctxNo)
 * \brief 		Activate a partition and switch to context
 * \param descriptor	The partition to resume (0 for parent)
 * \param pipflags 	PipFlags value */
void resume (uint32_t descriptor, uint32_t pipflags)
{
	uintptr_t to, from;
	
	IAL_DEBUG(TRACE, "Partition asked for a resume.\n");
	
	/* On a resume() call we consider the parent's job done - forget about the context ? */
	
	if (descriptor == 0)
	{
		/* A child is resuming a parent */
		if (PARTITION_CURRENT == PARTITION_ROOT){
			IAL_DEBUG(CRITICAL, "Root partition has no parent; trying to resume herself\n");
			to = PARTITION_ROOT;
			from = PARTITION_ROOT;
		} else {
			/* Get PAddr of Parent Partition */
			to = readPhysicalNoFlags(PARTITION_CURRENT, PPRidx()+1);
			/* Get VAddr of caller in parent partition */
			from = readPhysicalNoFlags(PARTITION_CURRENT, indexPR());
		}
	}
	else if (descriptor == 0xFFFFFFFF)
	{
		/* A child kernel is resuming itself */
		to = PARTITION_CURRENT;
		from = PARTITION_CURRENT;
	}
	/* A parent notifies a child */
	else {
		if (!checkChild(PARTITION_CURRENT, getNbLevel(), descriptor))
		{
			IAL_DEBUG(WARNING, "Partition %x tried to access invalid child %x\n", getCurPartition(), descriptor);
			return;
		}
		
		/* Get the physical address of child descriptor */
		to = readPaddr(PARTITION_CURRENT, descriptor);
		
		IAL_DEBUG(TRACE, "Resuming child %x\n", to);

		/* Identify parent by 0 */
		from = 0;
		
		/* re-enable interrupts in caller (TODO: may I?)*/
		*(uint32_t*) 0xfffffffc &= ~1;
	}
	
	/* Activate partition */
	IAL_DEBUG(TRACE, "Switching to partition %x's Page Directory\n", to);
	updateCurPartition (to);
	if(pcid_enabled)
		activate(readPhysicalNoFlags(to, indexPD () + 1) | readPhysical(to, 12));
	else
		activate(readPhysicalNoFlags(to, indexPD () + 1));
	
	/* Get interrupted context info - FIXME: stack only ? */
	uintptr_t int_ctx;
	IAL_DEBUG(TRACE, "PIPFLAGS is %x\n", *PIPFLAGS);
	if(VIDT_VCLI)
	{
		int_ctx = (uintptr_t)VIDT_CTX_BUFFER;
		IAL_DEBUG(TRACE, "Interrupted context should be at %x\n", VIDT_CTX_BUFFER);
	} else
	{
		int_ctx = VIDT_INT_ESP(0);
		IAL_DEBUG(TRACE, "Interrupted context should be at %x\n", int_ctx);
	}
	int_ctx_t* intctx = (int_ctx_t*)int_ctx;
	dumpRegs(intctx, TRACE);
	/* dumpRegs(intctx); */

	/* Build user context from interrupted context */
	user_ctx_t ctxToResume;
	ctxToResume.eip = intctx->eip;
	ctxToResume.pipflags = pipflags; /* VSTI */
	ctxToResume.eflags = intctx->eflags;
	memcpy((void*)&(ctxToResume.regs), &(intctx->regs), sizeof(pushad_regs_t));
	ctxToResume.regs.esp = intctx->useresp;
	ctxToResume.valid = 0;
	
	IAL_DEBUG(TRACE, "Going back to userland.\n");
	
	extern void resumeAsm(user_ctx_t*);
	resumeAsm(&ctxToResume);
	
	ASSERT(0);
}

