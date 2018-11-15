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
 * \file multiboot.h
 * \brief Multiboot header file
 */

#ifndef __MULTIBOOT_HEADER__
#define __MULTIBOOT_HEADER__

#include <stdint.h>

#define MULTIBOOT_FLAG_MEM     0x001 //!< Is there basic upper/lower memory information ?
#define MULTIBOOT_FLAG_DEVICE  0x002 //!< Is there a boot device set ?
#define MULTIBOOT_FLAG_CMDLINE 0x004 //!< Is the command-line defined ?
#define MULTIBOOT_FLAG_MODS    0x008 //!< Are there modules to deal with ?
#define MULTIBOOT_FLAG_AOUT    0x010 //!< Is there a symbol table loaded ?
#define MULTIBOOT_FLAG_ELF     0x020 //!< Is there an ELF section header table ?
#define MULTIBOOT_FLAG_MMAP    0x040 //!< Is there a full memory map ?
#define MULTIBOOT_FLAG_CONFIG  0x080 //!< Is there a config table ?
#define MULTIBOOT_FLAG_LOADER  0x100 //!< Is there a boot loader name ?
#define MULTIBOOT_FLAG_APM     0x200 //!< Is there a APM table ?
#define MULTIBOOT_FLAG_VBE     0x400 //!< Is there video information ?

#define MULTIBOOT_MEMORY_AVAILABLE		        1 //!< Memory is available
#define MULTIBOOT_MEMORY_RESERVED		        2 //!< Memory is system-reserved
#define MULTIBOOT_MEMORY_ACPI_RECLAIMABLE      	 	3 //!< Memory is reclaimable by the ACPI
#define MULTIBOOT_MEMORY_NVS                    	4 //!< Memory is something (?)
#define MULTIBOOT_MEMORY_BADRAM                 	5 //!< No such memory here


typedef struct multiboot_header
{
    uint32_t Magic;
    uint32_t flags;
    uint32_t checksum;
    uint32_t header_addr;
    uint32_t load_addr;
    uint32_t load_end_addr;
    uint32_t bss_end_addr;
    uint32_t entry_addr;
    uint32_t video_mode;
    uint32_t width;
    uint32_t height;
    uint32_t depth;
} multiboot_header_t;


/**
 * \struct multiboot
 * \brief Multiboot header info
 */
struct multiboot
{
    uint32_t flags; //!< Header flags
    uint32_t mem_lower; //!< Lower memory available
    uint32_t mem_upper; //!< Upper memory available
    uint32_t boot_device; //!< Boot device ID
    uint32_t cmdline; //!< Pointer to the boot command line
    uint32_t mods_count; //!< Amount of modules loaded
    uint32_t mods_addr; //!< Address to the first module structure
    uint32_t num;
    uint32_t size;
    uint32_t addr;
    uint32_t shndx;
    unsigned long mmap_length;
    unsigned long mmap_addr;
    unsigned long drives_length;
    unsigned long drives_addr;
    unsigned long config_table;
    unsigned long boot_loader_name;
    unsigned long apm_table;
    unsigned long vbe_control_info;
    unsigned long vbe_mode_info;
    unsigned long vbe_mode;
    unsigned long vbe_interface_seg;
    unsigned long vbe_interface_off;
    unsigned long vbe_interface_len;
} __attribute__ ((packed));
/**
 * \struct multiboot_memory_map
 * \brief Memory map structure
 */
typedef struct multiboot_memory_map {
    unsigned int size; //!< Size of this entry
    unsigned int base_addr_low; //!< Lower bytes of the base address
    unsigned int base_addr_high; //!< Higher bytes of the base address
    unsigned int length_low; //!< Lower bytes of the length
    unsigned int length_high; //!< Higher bytes of the length
    unsigned int type; //!< Memory type
} multiboot_memory_map_t;


#endif // __MULTIBOOT_HEADER__
