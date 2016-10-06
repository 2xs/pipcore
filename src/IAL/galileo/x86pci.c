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

#include "x86hw.h"
#include "x86pci.h"
#include "debug.h"
#include "libc.h"

void outportl(uint16_t port, uint32_t value)
{
	asm volatile ("outl %1, %0" : : "dN" (port), "a" (value));
}
void outportw(uint16_t port, uint16_t value)
{
	asm volatile ("outw %1, %0" : : "dN" (port), "a" (value));
}

uint32_t inportl(uint16_t port)
{
	uint32_t ret;
	asm volatile("inl %1, %0" : "=a" (ret) : "dN" (port));
	return ret;
}

uint16_t pciConfigReadWord(uint8_t bus, uint8_t slot, uint8_t func, uint8_t offset)
{
	uint32_t address;
	uint32_t lbus  = (uint32_t)bus;
	uint32_t lslot = (uint32_t)slot;
	uint32_t lfunc = (uint32_t)func;
	uint16_t tmp = 0;

	address = (uint32_t)((lbus << 16) | (lslot << 11) |
			  (lfunc << 8) | (offset & 0xfc) | ((uint32_t)0x80000000));

	outportl(PCI_CONFIG_ADDRESS, address);

	tmp = (uint16_t)((inportl(PCI_CONFIG_DATA) >> ((offset & 2) * 8)) & 0xFFFF);

	return tmp;
}

void pci_config_write_word(uint8_t bus, uint8_t slot, uint8_t func, uint8_t offset, uint16_t data)
{
	uint32_t address;
	uint32_t lbus  = (uint32_t)bus;
	uint32_t lslot = (uint32_t)slot;
	uint32_t lfunc = (uint32_t)func;
	uint16_t tmp = 0;
	
	address = (uint32_t)((lbus << 16) | (lslot << 11) |
						 (lfunc << 8) | (offset & 0xfc) | ((uint32_t)0x80000000));
	
	outportl(PCI_CONFIG_ADDRESS, address);
	outportl(PCI_CONFIG_DATA, data);
	//tmp = (uint16_t)((inportl(PCI_CONFIG_DATA) >> ((offset & 2) * 8)) & 0xFFFF);
	
	//return tmp;
}

uint16_t pciCheckVendor(uint8_t bus, uint8_t slot)
{
	uint16_t vendor, device;
	if((vendor = pciConfigReadWord(bus, slot, 0, 0)) != 0xFFFF) {
		return vendor;
	}
	else {
		return 0;
	}
}

char* getVendorName(uint32_t vendor)
{
	switch(vendor)
	{
		case 0x8086:
			return "Intel Corporation ";
			break;
		case 0x1013:
			return "Cirrus Logic ";
			break;
		case 0x1234:
			return "Technical Corp ";
			break;
		case 0x10EC:
			return "Realtek ";
			break;
		default:
			return "Unknown ";
	}
}
void register_pci_device(uint8_t bus, uint8_t slot, uint16_t vendor)
{
	char* vendorstr = getVendorName(vendor);
	
	// Get device id
	uint16_t device = pciConfigReadWord(bus,slot,0,2);
	/*puts("\tDevice ID : ");
	puthex(device);
	puts("\n");*/
	
	// Class and subclass
	uint16_t class_subclass = pciConfigReadWord(bus,slot,0,10);
	uint8_t class_id;
	class_id = (uint8_t)((class_subclass >> 8) & 0xF);
	
	char device_name[64];
	memcpy(device_name, vendorstr, strlen(vendorstr));
	
	// Print class string
	if(class_id == 0xFF)
		strcat(device_name, " Unknown class device");
	else if(class_id > 0x12 && class_id < 0xFE)
		strcat(device_name, " Reserved class device");
	else
		strcat(device_name, PCI_CLASSES[class_id]);
	
	/* Enable bus mastering for network devices */
	if(class_id == 0x2)
	{
		DEBUG(INFO, "Found network device, enabling bus mastering.\n");
		uint16_t pciconf = pciConfigReadWord(bus,slot,0,4);
		/* pciconf contains the command register for the PCI device. Write bus mastering bit and write it on the bus */
		pciconf = pciconf | 0x0004; /* Set bit 2 (Bus Master) into command register */
		pci_config_write_word(bus,slot, 0, 4, pciconf);
	}
	
	uint16_t pci_hdr_type = pciConfigReadWord(bus, slot, 0, 14);
	uint8_t hdr_type = (uint8_t)(pci_hdr_type & 0x00FF);
	/* If header type & 0x80 != 0 : multifunction device */
	if((hdr_type & 0x80) != 0)
	{
		DEBUG(INFO, "\t%s : multifunction PCI device detected, needs further parsing\n", device_name);
	}
	
	/* Create temporary PCI device info */
	x86_hardware_t pcidevice;
	memset(pcidevice.name, 0x0, sizeof(pcidevice.name));
	strcat(pcidevice.name, device_name);
	pcidevice.type = TYPE_PCI;
	
	uint8_t tmp = 0;
	for(tmp=0; tmp<6; tmp++)
		pcidevice.resources[tmp].type = RANGE_NULL;
	
	uint8_t dev_idx = 0;
	/* Parse each BAR from 0 to 5 */
	for(uint32_t i=0; i<5; i++)
	{
		/* Parse Base Address Register */
		uint16_t bar_lower, bar_upper;
		bar_lower = pciConfigReadWord(bus,slot,0,16 + 4*i);
		bar_upper = pciConfigReadWord(bus,slot,0,18 + 4*i);
		uint32_t bar = (bar_upper << 16) | bar_lower;
		
		if(bar != 0x00000000)
		{
			if(class_id == 0x03 && i == 0)
			{
				DEBUG(TRACE, "Registering VGA linear framebuffer.\n");
				extern uintptr_t vgaframebuffer;
				vgaframebuffer = (uintptr_t)(bar & 0xFFFFFFF0);
			}
			if((bar & 0x00000001) != 0)
			{
				pcidevice.resources[dev_idx].type = RANGE_IO;
				pcidevice.resources[dev_idx].begin = (uintptr_t)((bar & 0xFFFFFFFC) & 0x0000FFFF);
				pcidevice.resources[dev_idx].end = (uintptr_t)((bar & 0xFFFFFFFC) & 0x0000FFFF);
				
			} else {
				pcidevice.resources[dev_idx].type = RANGE_MEM;
				pcidevice.resources[dev_idx].begin = (uintptr_t)(bar & 0xFFFFFFF0);
				pcidevice.resources[dev_idx].end = (uintptr_t)(bar & 0xFFFFFFF0);
			}
			dev_idx++;
		}
	}
	addHardwareFromExisting(&pcidevice);
	
	return;
}

void enumeratePci()
{
	uint16_t bus;
	uint16_t device;
	uint16_t vendor;
    DEBUG(INFO, "Enumerating PCI devices.\n");
	 for(bus = 0; bus < 256; bus++) {
		 for(device = 0; device < 32; device++) {
			 vendor = pciCheckVendor((uint8_t)bus, (uint8_t)device);
			 if(vendor != 0)
                register_pci_device(bus, device, vendor);
		 }
	 }
    DEBUG(INFO, "Finished PCI probe.\n");
}
