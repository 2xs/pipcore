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
 * \file fpinfo.h
 * \brief First partition info structure header
 */

#ifndef __FPINFO__
#define __FPINFO__

#define FPINFO_MAGIC 0xDEADCAFE

/**
 * \enum fpinfo_devicetype
 * \brief Describes the device type
 */
enum fpinfo_devicetype {BUILTIN, PCI, OTHER};

/**
 * \struct fpinfo_pci_extendedinfo
 * \brief Describes a PCI device (leaves the further parsing up to the partition)
 */
typedef struct fpinfo_pci_extendedinfo 
{
    uint8_t device_class; //!< Device class
    uint8_t device_subclass; //!< Device subclass
    uint8_t bus; //!< PCI bus
    uint8_t slot; //!< PCI slot in bus
} pip_fpinfo_pci_extendedinfo;

/**
 * \struct fpinfo_device
 * \brief Represents a device, as probed by IAL
 * \warning extended_info pointer is *INVALID* in root partition. If NULL, there is no info, else, find it at &dev + sizeof(pip_fpinfo_device).
 */
typedef struct fpinfo_device {
    enum fpinfo_devicetype type; //!< Described device type
    uintptr_t mmio_begin; //!< Device memory range begin
    uintptr_t mmio_end; //!< Device memory range end
    uint32_t io_begin; //!< IO port range begin
    uint32_t io_end; //!< IO port range end
    struct fpinfo_pci_extendedinfo *extended_info; //!< Describes the internals of a PCI device. NULL on other device types
} pip_fpinfo_device;

/**
 * \struct fpinfotag_hw
 * \brief First partition info, hardware section
 */
typedef struct fpinfotag_hw
{
    uint32_t hwcount; //!< Amount of pip_fpinfo_device structures
    pip_fpinfo_device *devices; //!< Array containing hwcount devices
} pip_fpinfotag_hw;

/**
 * \struct fpinfo
 * \brief First partition info structure
 */
typedef struct fpinfo {
	uint32_t magic; //!< Magic number, should be FPINFO_MAGIC
	uint32_t membegin; //!< Available memory range begin
	uint32_t memend; //!< Available memory range end
	char revision[64]; //!< Pip Git revision
    pip_fpinfotag_hw hwinfo; //!< Hardware info
} pip_fpinfo;

#endif
