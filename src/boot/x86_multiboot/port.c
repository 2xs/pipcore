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

/**
 * \file port.c
 * \brief IO-ports for x86
 */

#include "port.h"
#include "mal.h"
#include "x86int.h"
#include "debug.h"
#include "pic8259.h"

/* Get hardware index from IO-to-Hardware table */
//extern uint16_t io_to_hardware[X86_MAX_IO];

/* check wether the current partition can access 
 * given ioport according to its access mask
 * returns 1 when access is allowed */
static uint32_t
ioAccessValid(uint16_t port)
{
	/*uint32_t iomask, hwidx;

	if (port >= X86_MAX_IO)
		return 0;

	iomask = readPhysical(getCurPartition(), PPRidx());
	hwidx = (uint32_t)(io_to_hardware[port]);*/

	/* return (iomask >> hwidx) & 1; */
	if(port == PIC1_COMMAND ||
	   port == PIC2_COMMAND ||
	   port == PIC1_DATA	||
	   port == PIC2_DATA)
		return 0;
	else return 1; // For now, allow any IO. TODO : fix this according to new IAL
}

/**
 * \fn void outb(uint16_t port, uint8_t value)
 * \brief Out operation on 1-byte value
 * \param port The port number
 * \param value The value to write
 */
void outb(uint16_t port, uint8_t value)
{
    asm volatile ("outb %1, %0" : : "dN" (port), "a" (value));
}

/**
 * \fn void outw(uint16_t port, uint16_t value)
 * \brief Out operation on 2-byte value
 * \param port The port number
 * \param value The value to write
 */
void outw(uint16_t port, uint16_t value)
{
	asm volatile ("outw %1, %0" : : "dN" (port), "a" (value));
}

/**
 * \fn void outl(uint16_t port, uint32_t value)
 * \brief Out operation on 4-byte value
 * \param port The port number
 * \param value The value to write
 */
void outl(uint16_t port, uint32_t value)
{
	asm volatile ("outl %1, %0" : : "dN" (port), "a" (value));
}

/**
 * \fn uint8_t inb(uint16_t port)
 * \brief In operation on 1-byte value
 * \param port The port number
 * \return The value returned by the IO operation
 */
uint8_t inb(uint16_t port)
{
   uint8_t ret;
   asm volatile("inb %1, %0" : "=a" (ret) : "dN" (port));
   return ret;
}

/**
 * \fn uint16_t inw(uint16_t port)
 * \brief In operation on a 2-bytes value
 * \param port The port number
 * \return The value returned by the IO operation
 */
uint16_t inw(uint16_t port)
{
   uint16_t ret;
   asm volatile ("inw %1, %0" : "=a" (ret) : "dN" (port));
   return ret;
}


/**
 * \fn uint32_t inl(uint16_t port)
 * \brief In operation on a 4-bytes value
 * \param port The port number
 * \return The value returned by the IO operation
 */
uint32_t inl(uint16_t port)
{
	uint32_t ret;
	asm volatile ("inl %1, %0" : "=a" (ret) : "dN" (port));
	return ret;
}

/**
 * \fn void faultToParent(uint32_t data1, uint32_t data2, gate_ctx_t *ctx)
 * \param data1 First data to pass
 * \param data2 Second data to pass
 * \param ctx Interrupted context
 * \brief Dispatch an access fault to the parent partition.
 * \return This function does not return.
 * \note The parent partition should resume the caller on its own 
 */
void
faultToParent(uint32_t data1, uint32_t data2, gate_ctx_t *ctx)
{
	DEBUG(INFO, "Userland tried to access forbidden IO port (port %x, value %x)\n", data1, data2);
	//TODO call to yield
}

/**
 * \fn void outbGlue(gate_ctx_t *ctx, uint32_t port, uint32_t value)
 * \brief Glue function for outb callgate
 * \param port Target IO port
 * \param value The value to write
 * \param ctx Interrupted context
 * \note Trigger a fault in parent partition if not authorized
 */
void outbGlue(gate_ctx_t *ctx, uint32_t port, uint32_t value)
{
	if (!ioAccessValid(port))
	{
		faultToParent(port, value, ctx);
	}
	else{
		outb((uint16_t)port, (uint8_t)value);
	}
}

/**
 * \fn void outwGlue(gate_ctx_t *ctx, uint32_t port, uint32_t value)
 * \brief Glue function for outw callgate
 * \param port Target IO port
 * \param value The value to write
 * \param ctx Interrupted context
 * \note Trigger a fault in parent partition if not authorized
 */
void outwGlue(gate_ctx_t *ctx, uint32_t port, uint32_t value)
{
	if (!ioAccessValid(port))
	{
		faultToParent(port, value, ctx);
	}
	else{
		outw((uint16_t)port, (uint16_t)(value&0xffff));
	}
}

/**
 * \fn void outlGlue(gate_ctx_t *ctx, uint32_t port, uint32_t value)
 * \brief Glue function for outl callgate
 * \param port Target IO port
 * \param value The value to write
 * \param ctx Interrupted context
 * \note Trigger a fault in parent partition if not authorized
 */
void outlGlue(gate_ctx_t *ctx, uint32_t port, uint32_t value)
{
	if (!ioAccessValid(port))
	{
		faultToParent(port, value, ctx);
	}
	else{
		outl((uint16_t)port, value);
	}
}

/**
 * \fn void outaddrlGlue(gate_ctx_t *ctx, uint32_t port, uint32_t value)
 * \brief Glue function for outaddrl callgate
 * \param port Target IO port
 * \param value The value to write
 * \param ctx Interrupted context
 * \note Trigger a fault in parent partition if not authorized
 */
void outaddrlGlue(gate_ctx_t *ctx, uint32_t port, uint32_t value)
{
	/* Convert vaddr to paddr */
	uintptr_t vad = (uintptr_t)value;
	uintptr_t offset = (uintptr_t)value & 0x00000FFF;
	uintptr_t idxPd = getIndexOfAddr(vad, 1);
	uintptr_t idxPt = getIndexOfAddr(vad, 0);
	uintptr_t pd = readPhysical(getCurPartition(), 2);
	uintptr_t pt = readPhysical(pd, idxPd);
	uintptr_t pad = readPhysical(pt, idxPt) | offset;

	if (!ioAccessValid(port))
	{
		faultToParent(port, (uint32_t)pad, ctx);
	}
	else
	{
		DEBUG(TRACE, "Writing physical address ");
		DEBUGHEX(pad);
		DEBUGRAW(" of virtual address ");
		DEBUGHEX(vad);
		DEBUGRAW(" to IO port ");
		DEBUGHEX(port);
		DEBUGRAW("\n");
		outb((uint16_t)port, (uint32_t)pad);
	}
}

/**
 * \fn uint32_t inbGlue(gate_ctx_t *ctx, uint32_t port)
 * \brief Glue function for inb callgate
 * \param port Target IO port
 * \param ctx Interrupted context
 * \return IO port read value
 * \note Trigger a fault in parent partition if not authorized
 */
uint32_t inbGlue(gate_ctx_t *ctx, uint32_t port)
{
	uint32_t ret = 0;
	
	if (!ioAccessValid(port))
	{
		faultToParent(port|0xf0000000, 0, ctx);
	}
	else{
		ret = (uint32_t)inb((uint16_t)port);
	}
	return ret;
}

/**
 * \fn uint32_t inwGlue(gate_ctx_t *ctx, uint32_t port)
 * \brief Glue function for inw callgate
 * \param port Target IO port
 * \param ctx Interrupted context
 * \return IO port read value
 * \note Trigger a fault in parent partition if not authorized
 */
uint32_t inwGlue(gate_ctx_t *ctx, uint32_t port)
{
	uint32_t ret = 0;

	if (!ioAccessValid(port))
	{
		faultToParent(port|0xf0000000, 0, ctx);
	}
	else{
		ret = (uint32_t)inw((uint16_t)port);
	}

	return ret;
}

/**
 * \fn uint32_t inlGlue(gate_ctx_t *ctx, uint32_t port)
 * \brief Glue function for inl callgate
 * \param port Target IO port
 * \param ctx Interrupted context
 * \return IO port read value
 * \note Trigger a fault in parent partition if not authorized
 */
uint32_t inlGlue(gate_ctx_t *ctx, uint32_t port)
{
	uint32_t ret = 0;

	if (!ioAccessValid(port))
	{
		faultToParent(port|0xf0000000, 0, ctx);
	}
	else{
		ret = inl((uint16_t)port);
	}

	return ret;
}

/**
 * \fn uint32_t timerGlue(void)
 * \brief Glue function for timer callgate
 * \return Current timer ticks
 */
uint32_t timerGlue(void)
{
	/* extern uint32_t timer_ticks;
	return timer_ticks; */
	// DEBUG(CRITICAL, "Requested RDTSC !\n");
	uint32_t ret1, ret2;
	__asm volatile("RDTSC; \
					MOV %%EAX, %0; \
					MOV %%EDX, %1"
				   : "=r"(ret1), "=r"(ret2));
	return ret1; /* Get RET2 from EDX */
}
