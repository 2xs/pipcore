/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2021)                */
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
 * \file mal.c
 * \brief x86 memory abstraction layer
 */

#include <stdint.h>
#include "mal.h"
#include "maldefines.h"
#include "structures.h"
#include "debug.h"
#include "segment_selectors.h"

uint32_t current_partition; /* Current partition's CR3 */
uint32_t root_partition; /* Multiplexer's partition descriptor */
uint32_t next_pid = 1;
extern uint32_t pcid_enabled;
/*!	\fn void enable_paging()
	\brief enables paging
	\post paging mechanism is enabled
 */
void enable_paging()
{
	uint32_t cr0;
	asm volatile("mov %%cr0, %0": "=r"(cr0));
	
	cr0 |= 0x80000000;
	asm volatile("mov %0, %%cr0":: "r"(cr0));
}

/*!     \fn void disable_paging()
 \brief disables paging
	\post paging mechanism is disabled
 */
void disable_paging()
{
	// Get CR0 value
	uint32_t cr0;
	asm volatile("mov %%cr0, %0": "=r"(cr0));
	
	// Disable paging bit
	cr0 &= 0x7FFFFFFF;
	asm volatile("mov %0, %%cr0":: "r"(cr0));
}

/*!
 * \fn void writePhysical(uint32_t table, uint32_t index, uint32_t addr)
 * \brief Stores the given address into the given indirection table, at the given index, with physical addresses
 * \param table The table to store into
 * \param index The index in the table
 * \param addr The address to store
 */
void writePhysical(uint32_t table, uint32_t index, uint32_t val)
{
	/* Disable paging */
	disable_paging();
	
	/* Get the destination address */
	uint32_t dest = table | (index * sizeof(uint32_t));
	*(uint32_t*)dest = val;
	
	/* Enable paging */
	enable_paging();
	
	return;
}

/*!
 * \fn uint32_t readPhysicalNoFlags(uint32_t table, uint32_t index)
 * \brief Reads the address stored into table table, at index index, using physical addresses
 *        This function masks the least significant bits that are used by the kernel to store
 *        various flags (see `readVirEntry` and `readPhyEntry` in model)
 * \param table The table to read from
 * \param index The index in the table
 * \return The address stored in the given slot, with its least significant bits cleared
 */
uint32_t readPhysicalNoFlags(uint32_t table, uint32_t index)
{
	/* we need physical address space, disable paging */
	disable_paging();
	
	uint32_t paddr_to_read = table | (index * sizeof(uint32_t));
	uint32_t val = *(uint32_t *) paddr_to_read;
	
	/* zero the flags */
	uint32_t mask = 0xFFFFF000;
	val = val & mask;
	
	/* Re-enable paging */
	enable_paging();
	
	return val;
}

/*!
 * \var uint32_t tableSize()
 * \brief size (number of entries) of indirection tables
 */
uint32_t tableSize = 1024;

/*!
 * \fn uint32_t getTableSize()
 * \brief Gets size of indirection table
 * \return The amount of entries in a page table
 */
uint32_t getTableSize()
{
	return tableSize; // 1024 entries per table
}

/*!
 * \fn uint32_t getIndexOfAddr(uint32_t addr, uint32_t index)
 * \brief Gets the index of this address into the given indirection table level
 * \param addr The virtual address
 * \param index The indirection level address
 * \return The desired index
 */
uint32_t getIndexOfAddr(uint32_t addr, uint32_t index)
{
	/* First check the index value */
	if (index > 1)
		return 0;

	/* Index 1 is the first indirection and 2 is the second. */
	if(index == 1)
	{
		/* First level : Page Directory */
		uint32_t pd_idx = (addr & 0xFFC00000) >> 22;
		return pd_idx;
	} else /* index == 0*/{
		/* Second level : Page Table */
		uint32_t pt_idx = (addr >> 12) & 0x000003FF;
		return pt_idx;
	}
}

/*!
 * \fn uint32_t readAccessible(uint32_t table, uint32_t index)
 * \brief Gets the Accessible flag from the given entry.
 * \param table The table to read from
 * \param index The index in the given table
 * \return 1 if the page is user-mode accessible, 0 else
 */
bool readAccessible(uint32_t table, uint32_t index)
{
	disable_paging();
	
	/* Get destination */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	/* Get value */
	uint32_t val = *(uint32_t*)dest;
	
	/* Cast it into a page_table_entry_t structure */
	page_table_entry_t* entry = (page_table_entry_t*)&val;
	
	/* Now return the accessible flag */
	uint32_t ret = entry->user;
	
	enable_paging();
	
	return ret;
}

/*!
 * \fn void writeAccessible(uint32_t table, uint32_t index, uint32_t value)
 * \brief Marks a page as accessible or not.
 * \param table The indirection table
 * \param index The index into this indirection table
 * \param value 0 if the page is kernel-only, 1 else (any other value should be forbidden...)
 */
void writeAccessible(uint32_t table, uint32_t index, bool value)
{
	disable_paging();
	
	/* Get destination */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	/* Cast it into a page_table_entry_t structure */
	page_table_entry_t* entry = (page_table_entry_t*)dest;
	
	/* Write the flag */
	entry->user = value;
	
	enable_paging();
	
	/* Return so we avoid the warning */
	return;
}

/*! \fn uint32_t getCurPartition()
 \brief get the current page directory
	\return the current page directory
 */
uint32_t getCurPartition(void)
{
	return current_partition;
}

/*! \fn void updateCurPartition()
 \brief Set current partition paddr
 \param partition Current partition paddr
 */
void
updateCurPartition (uint32_t descriptor)
{
	extern uint32_t pcid_enabled;
	current_partition = descriptor;
	if(readPhysical(descriptor, 12) == 0x0 && pcid_enabled)
	{
		writePhysical(descriptor, 12, next_pid);
		DEBUG(TRACE, "Registered partition descriptor %x as PID %d.\n", descriptor, next_pid);
		next_pid++;
		/* TODO assert next_pid doesn't wrap-up */
	}
}

/*! \fn uint32_t getRootPartition()
 \brief get the root partition 
	\return the root partition 
 */
uint32_t getRootPartition(void)
{
	return root_partition;
}

/*! \fn uint32_t updateRootPartition()
 \brief Set root partition paddr
 \param partition Root partition paddr
 */
void
updateRootPartition(uint32_t partition)
{
	root_partition = partition;
}

/*!
 * \fn uint32_t readPresent(uint32_t table, uint32_t index)
 * \brief Gets the Present flag from the given entry.
 * \param table The table to read from
 * \param index The index in the given table
 * \return 1 if the page is present, 0 else
 */
bool readPresent(uint32_t table, uint32_t index)
{
	disable_paging();
	
	/* Get destination */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	/* Get value */
	uint32_t val = *(uint32_t*)dest;
	
	/* Cast it into a page_table_entry_t structure */
	page_table_entry_t* entry = (page_table_entry_t*)&val;
	
	uint32_t res = entry->present;
	
	enable_paging();
	
	/* Now return the present flag */
	return res;
}

/*!
 * \fn void writePresent(uint32_t table, uint32_t index, uint32_t value)
 * \brief Marks a page as present or not.
 * \param table The indirection table
 * \param index The index into this indirection table
 * \param value 0 if the page is not present, 1 else (any other value should be forbidden...)
 */
void writePresent(uint32_t table, uint32_t index, bool value)
{
	disable_paging();
	
	/* Get destination */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	/* Cast it into a page_table_entry_t structure */
	page_table_entry_t* entry = (page_table_entry_t*)dest;
	
	/* Write the flag */
	entry->present = value;
	
	enable_paging();
	
	/* Return so we avoid the warning */
	return;
}


/*!
 * \fn void writePDflag(uint32_t table, uint32_t index, uint32_t value)
 * \brief Writes the Page Directory flag into a shadow table
 * \param table The shadow page's last indirection
 * \param index The index into the shadow table
 * \param value The vamue of the PD flag
 */
void writePDflag(uint32_t table, uint32_t index, bool value)
{
	disable_paging();
	
	uint32_t dest = table | (index * sizeof(uint32_t));
	uint32_t curval = *(uint32_t*)dest;
	uint32_t curAddr = (uint32_t)curval & 0xFFFFFFFE;

	if(value == 1)
		*(uint32_t*)dest = curAddr | 0x00000001;
	else
		*(uint32_t*)dest = curAddr;
	
	enable_paging();
	
	return;
}

/*!
 * \fn uint32_t readPDflag(uint32_t table, uint32_t index)
 * \brief Reads the Page Directory flag into a shadow table
 * \param table The shadow page's last indirection
 * \param index The index into the shadow table
 * \return The value of the PD flag
 */
bool readPDflag(uint32_t table, uint32_t index)
{
	disable_paging();
	
	uint32_t dest = table | (index * sizeof(uint32_t));
	uint32_t curval = *(uint32_t*)dest;
	
	enable_paging();
	
	return (curval & 0x00000001);
}

uint32_t readPhysical(uint32_t table, uint32_t index)
{
	/* We're in kernel : we can disable paging */
	disable_paging();
	
	/* Binary OR with the table's address, page-aligned, and the offset */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	/* Now we got a fresh, cool, nice pointer, return its value */
	uint32_t val = *(uint32_t*)dest;
	
	/* Re-enable paging */
	enable_paging();
	
	return val;
}


void writePhysicalNoFlags(uint32_t table, uint32_t index, uint32_t addr)
{
	/* Disable paging */
	disable_paging();
	
	/* Just in case we're given bullshit, zero the potential flags. */
	uint32_t val = (uint32_t)addr & ~0xfff;
	
	/* Get the destination address */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	*(uint32_t*)dest = (*(uint32_t*)dest&0xfff)|val;
	
	/* Enable paging */
	enable_paging();
	
	return;
}


/*!	\fn uint32_t getNbIndex()
 * 	\brief Gets the amount of indirection tables
 * 	\return Amount of maximal indirection tables
 */
uint32_t nbLevel = 2;

uint32_t getNbIndex(void)
{
	return nbLevel-1;
}

/*!
 * \fn void writeAddr(uint32_t table, uint32_t index, uint32_t addr)
 * \brief Stores the given address into the given indirection table, at the given index
 * \param table The table to store into
 * \param index The index in the table
 * \param addr The address to store
 */
void writeTableVirtual(uint32_t table, uint32_t index, uint32_t addr)
{
	/* Just in case we're given bullshit, zero the potential flags. */
	uint32_t val = (uint32_t)addr & 0xFFFFF000;
	
	/* Get the destination address */
	uint32_t dest = table | (index * sizeof(uint32_t));
	
	/* Store this, leaving the current flags unchanged */
	uint32_t curFlags = *(uint32_t*)dest & 0x00000FFF;
	
	*(uint32_t*)dest = val | curFlags;
	
	return;
}

/*!
 * \fn uint32_t readAddr(uint32_t table, uint32_t index)
 * \brief Reads the address stored into table Table, at index index.
 * \param table The table to read from
 * \param index The index in the table
 * \return The address stored in the given slot
 */
uint32_t readTableVirtual(uint32_t table, uint32_t index)
{
	/* Binary OR with the table's address, page-aligned, and the offset */
	uint32_t dest = table | ((uint32_t)index * sizeof(uint32_t));
	
	/* Now we got a fresh, cool, nice pointer, return its value */
	uint32_t val = (uint32_t)*(uint32_t*)dest;
	
	return val & 0xFFFFF000;
}

/*!
 * \fn uint32_t checkRights(uint32_t read, uint32_t write, uint32_t execute)
 * \param read The read right
 * \param write The write right
 * \param execute The execute right
 * \brief Checks whether we can apply the given rights on the target architecture
 * \return 1 if we can, 0 if we can't
 */
bool checkRights(bool read, bool write, bool execute)
{
	// Read has to be 1 (only user/kernel in x86)
	if(read==0)
		return 0;
	
	// No XD bit on i386
	if(execute==0)
		return 0;
	
	// Well the complier will complain about a unused parameter thing so...
	if(write==0 || write == 1)
		return 1;
	else return 0;
}

uint32_t extractPreIndex(uint32_t addr, uint32_t index)
{
	/* First check the index value */
	if (index > 2)
		return 0;

	/* Index 1 is the first indirection and 2 is the second. */
	if(index == 0)
	{
		/* First level : Page Directory */
		uint32_t pd_idx = (addr & 0xFFC00000) >> 22;
		return pd_idx;
	} else if (index == 1) {
		/* Second level : Page Table */
		uint32_t pt_idx = (addr >> 12) & 0x000003FF;
		return pt_idx;
	} else {
        /* Offset */
        uint32_t off = addr & 0xFFF;
        return off;
    }
}

/**
 * This function is the real world version of the model's "mapKernel".
 * We use the same MMU table page for every partition that is configured at
 * boot time for the root partition. When creating a partition, that page is
 * looked up in the MMU configuration pages of the parent partition and written
 * at the same place.
 */
void writeKernelPhysicalEntry(uintptr_t child_mmu_root_page, uint32_t kernel_index)
{
    uint32_t cr3 = readPhysical(current_partition, indexPD() + 1);
    uint32_t kpt = readPhysical(cr3, kernel_index);
    writePhysicalWithLotsOfFlags(child_mmu_root_page, kernel_index, kpt, 1, 0, 1, 1, 1);
    return;
}

/* Combines a boolean and a virtual address (boolean on the least significant bit) */
uint32_t prepareType(bool b, uint32_t vaddr)
{
    return (vaddr & ~1) | (b ? 1 : 0);
}

vaddr getVidtVAddr() {
	return 0xFFFFF000;
}

vaddr getNthVAddrFrom(page base, uint32_t size) {
	return ((uint32_t) base) + size;
}

interruptMask getInterruptMaskFromCtx(contextAddr targetContext) {
	return targetContext->pipflags;
}

bool noInterruptRequest(interruptMask flagsOnWake) {
	return flagsOnWake == 0;	
}

bool firstVAddrGreaterThanSecond(vaddr vaddr1, vaddr vaddr2) {
	return ((uintptr_t) vaddr1) > ((uintptr_t) vaddr2);
}

contextAddr vaddrToContextAddr(vaddr contextVAddr) {
	return (contextAddr) contextVAddr;
}

bool checkIndexPropertyLTB(userValue userIndex) {
	return userIndex < getMaxIndex();
}

index userValueToIndex(userValue userIndex) {
	return (index) userIndex;
}

void writeContext(contextAddr ctx, vaddr ctxSaveVAddr, interruptMask flagsOnWake) {
	user_ctx_t *userland_save_ptr = (user_ctx_t *) ctxSaveVAddr;
	userland_save_ptr->eip      = ctx->eip;
	userland_save_ptr->pipflags = flagsOnWake;
	userland_save_ptr->eflags   = ctx->eflags;
	userland_save_ptr->regs     = ctx->regs;
	userland_save_ptr->valid    = 1;
}

/* copies or pushes SS, ESP, EFLAGS, CS, EIP from the given context to the stack
 * and then executes an `iret` in order to go back to userland
 * see x86int.h for infos related to user_ctx_t struct */
void loadContext(contextAddr ctx, bool enforce_interrupts) {
	asm(
	    /* retrieve user_ctx_t * in EAX register */
	    "mov %0, %%eax;"
	    "mov %1, %%ecx;"

	    /* push user ss */
	    "push %2;"

	    /* push user esp */
	    "push 0x18(%%eax);"

	    /* push eflags */
	    "push 0x8(%%eax);"

	    /* fix eflags to prevent potential security issues */
	    "orl %3, (%%esp);"
	    /* -- skip enable interrupts depending on parameter */
	    "jcxz 1f;" /* <------+ */
	    "orl %4, (%%esp);"/* | */
	    "1:;" /* <-----------+ */

	    "andl %5, (%%esp);"

	    /* push cs */
	    "push %6;"

	    /* push eip */
	    "push (%%eax);"

	    /* restore general purpose registers */
	    /* maybe we could `popad` but it seems complicated */
	    /* restore EDI */
	    "mov  0xC(%%eax), %%edi;"

	    /* restore ESI */
	    "mov 0x10(%%eax), %%esi;"

	    /* restore EBP */
	    "mov 0x14(%%eax), %%ebp;"

	    /* skipped ESP which was already pushed */

	    /* restore EBX */
	    "mov 0x1C(%%eax), %%ebx;"

	    /* restore EDX */
	    "mov 0x20(%%eax), %%edx;"

	    /* restore ECX */
	    "mov 0x24(%%eax), %%ecx;"

	    /* restore EAX */
	    "mov 0x28(%%eax), %%eax;"

	    /* switch to userland */
	    "iret;"

	    /* output operands */
	    :
	    /* input operands */
	    : "m"(ctx),
	      "m"(enforce_interrupts),
	      "i"(USER_DATA_SEGMENT_SELECTOR | USER_RING), /* TODO Correct ? Check RPL */
	    /* eflags related constants */
	    /* set bit 1 : always 1 */
	      "i"(0x2),
	    /* set bit conditional :
	     * 	       9 : interrupt enable
	     * controlled by parameter */
	      "i"(0x200),
	    /* unset bit 8 : trap flag
	     * 	     12-13 : I/O privilege level
	     *       14-32 : various system flags */
	      "i"(0xEFF),
	      "i"(USER_CODE_SEGMENT_SELECTOR | USER_RING)  /* TODO Correct ? Check RPL */
	    /* registers changed during inline assembly */
	    :
	);
}
