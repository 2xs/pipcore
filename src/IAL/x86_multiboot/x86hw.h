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
 * \file x86hw.h
 * \brief x86 hardware structures
 */

#ifndef __X86_HARDWARE__
#define __X86_HARDWARE__

#include <stdint.h>
#include "fpinfo.h"

#define X86_MAX_HARDWARE    0xFF
#define X86_MAX_IO          0xFFFF

enum x86_hw_type {TYPE_BUILTIN, TYPE_PCI, TYPE_UNK};
enum x86_res_range {RANGE_NULL, RANGE_MEM, RANGE_IO};
typedef enum x86_hw_type x86_hw_type_t;
typedef enum x86_res_range x86_res_range_t;

struct x86_resource {
	x86_res_range_t type;
	uintptr_t begin, end;
};

typedef struct x86_resource x86_resource_t;

struct x86_hardware {
    char name[64];
	x86_hw_type_t type;
	x86_resource_t resources[6];
    uint32_t data; /* Optional data */
} x86_hardware;

typedef struct x86_hardware x86_hardware_t;

uint16_t io_to_hardware[X86_MAX_IO]; // Mapping from IO-Port to hardware index
x86_hardware_t hardware_list[X86_MAX_HARDWARE]; // x86 hardware

void probeHardware(); //!< Trigger the platform-specific hardware probe
void addHardware(char* name, uintptr_t membegin, uintptr_t memend, uint16_t iobegin, uint16_t ioend, x86_hw_type_t type); //!< Adds the given hardware to the probed hardware list
void addHardwareFromExisting(x86_hardware_t* info); //!< Adds the given hardware to the probed hardware list
void addResourceRange(x86_hardware_t* info, x86_res_range_t type, uint32_t begin, uint32_t end); //!< Adds the given hardware to the probed hardware list
void mapIo(x86_hardware_t* hw, uint16_t hwindex); //!< Map IO range to given hardware
void fillHardwareInfo(pip_fpinfo* fpinfo); //!< Fill hardware info in First Partition Info page
#endif
