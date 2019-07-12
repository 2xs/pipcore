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

#ifndef __IDT__
#define __IDT__

#include <stdint.h>

/**
 * \struct idt_entry_struct
 * \brief Interrupt Descriptor Table entry
 */
struct idt_entry_struct
{
    uint16_t base_lo;   //!< Lower bytes of handler address
    uint16_t sel;       //!< Selector
    uint8_t  always0;	//!< RFU
    uint8_t  flags;     //!< Interrupt handler flags (Required Privilege Level etc)
    uint16_t base_hi;   //!< Higher bytes of handler address
} __attribute__((packed));

typedef struct idt_entry_struct idt_entry_t;

/**
 * \struct idt_ptr_struct
 * \brief IDT pointer structure
 */
struct idt_ptr_struct
{
    uint16_t limit;     //!< Address limit
    idt_entry_t *base;  //!< IDT pointer base
} __attribute__((packed));

typedef struct idt_ptr_struct idt_ptr_t;

#endif
