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

#include <stdint.h>
#include "x86hw.h"
#include "debug.h"
#include "libc.h"

uint32_t hwcount = 0;

void probeHardware()
{
    DEBUG(INFO, "Beginning hardware probe\n");
	addHardware("Terminal VGA controller", (uintptr_t)0xB8000, (uintptr_t)(0xB8000 + 80*25*sizeof(uint16_t)), 0x3D4, 0x3D5, TYPE_BUILTIN);
	addHardware("Legacy DMA controller", (uintptr_t)0x0, (uintptr_t)(0x0), 0x0000, 0x001F, TYPE_BUILTIN);
	addHardware("Programmable interrupt controller", (uintptr_t)0x0, (uintptr_t)(0x0), 0x0020, 0x0021, TYPE_BUILTIN);
	addHardware("Cyrix processors Model-Specific registers", (uintptr_t)0x0, (uintptr_t)(0x0), 0x0022, 0x0023, TYPE_BUILTIN);
	addHardware("Programmable Interval Timer", (uintptr_t)0x0, (uintptr_t)(0x0), 0x0040, 0x0047, TYPE_BUILTIN);
	addHardware("8042 PS/2 Controller", (uintptr_t)0x0, (uintptr_t)(0x0), 0x0060, 0x0064, TYPE_BUILTIN);
	addHardware("CMOS and RTC registers", (uintptr_t)0x0, (uintptr_t)(0x0), 0x0070, 0x0071, TYPE_BUILTIN);
	addHardware("DMA controller page registers", (uintptr_t)0x0, (uintptr_t)(0x0), 0x0080, 0x008F, TYPE_BUILTIN);
	addHardware("Fast A20 gate register", (uintptr_t)0x0, (uintptr_t)(0x0), 0x0092, 0x0092, TYPE_BUILTIN);
	addHardware("Secondary programmable interrupt controller", (uintptr_t)0x0, (uintptr_t)(0x0), 0x00A0, 0x00A1, TYPE_BUILTIN);
	addHardware("Secondary DMA controller", (uintptr_t)0x0, (uintptr_t)(0x0), 0x00C0, 0x00DF, TYPE_BUILTIN);
	addHardware("Bochs emulator port E9 hack", (uintptr_t)0x0, (uintptr_t)(0x0), 0x00E9, 0x00E9, TYPE_BUILTIN);
	addHardware("Secondary ATA controller", (uintptr_t)0x0, (uintptr_t)(0x0), 0x0170, 0x0177, TYPE_BUILTIN);
	addHardware("Primary ATA controller", (uintptr_t)0x0, (uintptr_t)(0x0), 0x01F0, 0x01F7, TYPE_BUILTIN);
	addHardware("Parallel port", (uintptr_t)0x0, (uintptr_t)(0x0), 0x0278, 0x27A, TYPE_BUILTIN);
	addHardware("Secondary serial port", (uintptr_t)0x0, (uintptr_t)(0x0), 0x02F8, 0x02FF, TYPE_BUILTIN);
	addHardware("IBM VGA controller / Legacy video card", (uintptr_t)0x0, (uintptr_t)(0x0), 0x03B0, 0x03BF, TYPE_BUILTIN);
	addHardware("Floppy disk controller", (uintptr_t)0x0, (uintptr_t)(0x0), 0x03F0, 0x03F7, TYPE_BUILTIN);
	addHardware("Primary serial port", (uintptr_t)0x0, (uintptr_t)(0x0), 0x03F8, 0x03FF, TYPE_BUILTIN);
	addHardware("Host-to-PCI bridge controller", (uintptr_t)0x0, (uintptr_t)(0x0), 0x0CF8, 0x0CFC, TYPE_BUILTIN);
	addHardware("(IO) Advanced Programmable Interrupt Controller", (uintptr_t)0xFEC00000, (uintptr_t)0xFEE00000, 0x0, 0x0, TYPE_BUILTIN);
    return;
}

/**
 * \fn  dumpHardware
 * \brief      Dumps a hardware.
 *
 * \param      hw    The hardware
 */
void dumpHardware(x86_hardware_t* hw)
{
	/* Display name and type */
	DEBUG(INFO, "%s %s", hw->name, (hw->type == TYPE_BUILTIN)?" : built-in hardware\n":" : PCI device\n");
	
	/* Display each resource info */
	uint8_t i = 0;
	while(i < 6 && hw->resources[i].type != RANGE_NULL)
	{
		DEBUG(INFO, "\tResource %d, %s %x to %x\n", i, hw->resources[i].type == RANGE_MEM ? "physical memory range " : "IO range", hw->resources[i].begin, hw->resources[i].end);
		i++;
	}
	return;
}

/**
 * \brief      Adds a hardware.
 *
 * \param      name      The name
 * \param[in]  membegin  The membegin
 * \param[in]  memend    The memend
 * \param[in]  iobegin   The iobegin
 * \param[in]  ioend     The ioend
 * \param[in]  type      The type
 */
void addHardware(char* name, uintptr_t membegin, uintptr_t memend, uint16_t iobegin, uint16_t ioend, x86_hw_type_t type)
{
	/* Get target slot and set type */
    x86_hardware_t* target = &hardware_list[hwcount];

	target->type = type;
    memset(target->name, 0x0, sizeof(target->name));
	strcat(target->name, name);
	
	/* Add resources, setting all existing resources to NULL */
	uint8_t i = 0;
	for(i=0; i<6; i++)
		target->resources[i].type = RANGE_NULL;
	
	i = 0;
	
	x86_resource_t* tar_res = &(target->resources[i]);
	
	if(membegin != 0x0)
	{
		tar_res->type = RANGE_MEM;
		tar_res->begin = membegin;
		tar_res->end = memend;
		i++;
		
		tar_res = &(target->resources[i]);
	}
	
	if(iobegin != 0x0)
	{
		tar_res->type = RANGE_IO;
		tar_res->begin = (uintptr_t)iobegin & 0x0000FFFF;
		tar_res->end = (uintptr_t)ioend & 0x0000FFFF;
	}
	
	/* Debug output of hardware */
	dumpHardware(target);
    mapIo(target, hwcount);
    hwcount++;
    return;
}

/**
 * @brief      Adds a hardware from existing.
 *
 * @param      info  The information
 */
void addHardwareFromExisting(x86_hardware_t* info) {
	x86_hardware_t* target = &hardware_list[hwcount];
	memcpy(target, info, sizeof(x86_hardware_t));
	dumpHardware(target);
	mapIo(target, hwcount);
	hwcount++;
	return;
}

void addResourceRange(x86_hardware_t* info, x86_res_range_t type, uintptr_t begin, uintptr_t end)
{
	uint8_t i = 0;
	while(i < 6 && info->resources[i].type != RANGE_NULL)
		i++;
	
	/* No more resource range ? */
	if(i == 6)
		return;
	
	/* Well we should have a free slot at index i */
	x86_resource_t* target = &(info->resources[i]);
	target->type = type;
	target->begin = begin;
	target->end = end;
	
	/* All done ! */
	return;
}

uint16_t findPortRange(uint16_t iobegin)
{
	switch(iobegin)
	{
		case 0xC000: /* Realtek network adapter */
			return 0xC0FF;
			break;
		default:
			return iobegin;
	}
}

void mapIo(x86_hardware_t* hw, uint16_t hwindex)
{
	uint16_t i = 0;
	uint8_t res_i = 0;
	while(i < 6 && hw->resources[res_i].type != RANGE_NULL)
	{
		if(hw->resources[res_i].type == RANGE_IO)
		{
			for(i=hw->resources[res_i].begin; i<=findPortRange(hw->resources[res_i].begin); i++)
				io_to_hardware[i] = hwindex;
			DEBUG(TRACE, "Registered ports %x to %x on hardware id %d\n", hw->resources[res_i].begin, findPortRange(hw->resources[res_i].begin), hwindex);
		}
		res_i++;
	}
	
	return;
}
