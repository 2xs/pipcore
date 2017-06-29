/*
 * Copyright (C) 2015, Intel Corporation. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its
 *    contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <assert.h>
#include <pip/io.h>
#include "pci.h"
#include "helpers.h"
#include "pip/io.h"

/* I/O port for PCI configuration address */
#define PCI_CONFIG_ADDR_PORT 0xCF8
/* I/O port for PCI configuration data */
#define PCI_CONFIG_DATA_PORT 0xCFC


/*---------------------------------------------------------------------------*/
/* Initialize PCI configuration register address in preparation for accessing
 * the specified register.
 */
static void
set_addr(pci_config_addr_t addr)
{
  addr.en_mapping = 1;

  outl(PCI_CONFIG_ADDR_PORT, addr.raw);
}
/*---------------------------------------------------------------------------*/
/**
 * \brief      Read from the specified PCI configuration register.
 * \param addr Address of PCI configuration register.
 * \return     Value read from PCI configuration register.
 */
uint32_t
pci_config_read(pci_config_addr_t addr)
{
  set_addr(addr);

  return inl(PCI_CONFIG_DATA_PORT);
}
/*---------------------------------------------------------------------------*/
/**
 * \brief      Write to the PCI configuration data port.
 * \param addr Address of PCI configuration register.
 * \param data Value to write.
 */
void
pci_config_write(pci_config_addr_t addr, uint32_t data)
{
  set_addr(addr);

  outl(PCI_CONFIG_DATA_PORT, data);
}



 uint16_t pciConfigReadWord (pci_config_addr_t pci, uint8_t offset)
 {
    uint32_t address;
    uint32_t pci_e = pci.raw;
    uint16_t tmp = 0;
    /* create configuration address as per Figure 1 */
    address = ( pci_e) | (offset & 0xfc) | ((uint32_t)0x80000000);

    /* write out the address */
    outl (PCI_CONFIG_ADDR_PORT, address);
    /* read in the data */
    /* (offset & 2) * 8) = 0 will choose the first word of the 32 bits register */
    tmp = (uint16_t)((inl (PCI_CONFIG_DATA_PORT) >> ((offset & 2) * 8)) & 0xffff);
    return (tmp);
 }


 void pciConfigWriteWord (pci_config_addr_t pci,uint32_t data, uint8_t offset)
 {
    uint32_t address;
    uint32_t pci_e = pci.raw;
    uint16_t tmp = 0;
    /* create configuration address as per Figure 1 */
    address = (pci_e) | (offset & 0xfc) | ((uint32_t)0x80000000);

    /* write out the address */
    outl (PCI_CONFIG_ADDR_PORT, address);
    /* read in the data */
    /* (offset & 2) * 8) = 0 will choose the first word of the 32 bits register */
    outl ((PCI_CONFIG_DATA_PORT) >> ((offset & 2) * 8) & 0xffff,data);
 }



