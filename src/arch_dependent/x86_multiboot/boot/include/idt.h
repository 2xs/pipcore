/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2019)                 */
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
 * \struct idt_int_trap_entry
 * \brief Interrupt Descriptor Table Trap and Interrupt entry common struct
 */
struct idt_int_trap_entry_s {
    unsigned offset_low  : 16; //<! Lower bits of handler address
    unsigned segment     : 16; //<! Segment selector
    unsigned rfu         :  5; //<! Reserved
    unsigned zero        :  3; //<! Always zero smh
    unsigned type        :  5; //<! TRAP_GATE_TYPE or INTERRUPT_GATE_TYPE
    unsigned dpl         :  2; //<! Descriptor Privilege Level
    unsigned present     :  1; //<! Present flag (validity)
    unsigned offset_high : 16; //<! Higher bits of handler address
};
typedef struct idt_int_trap_entry_s idt_trap_entry_t;
typedef struct idt_int_trap_entry_s idt_int_entry_t;


/**
 * \struct idt_task_entry_s
 * \brief Interrupt Descriptor Table Task entry struct
 */
struct idt_task_entry_s {
    unsigned rfu0    : 16; //<! Reserved
    unsigned segment : 16; //<! TSS segment selector
    unsigned rfu1    :  8; //<! Reserved
    unsigned type    :  5; //<! TASK_GATE_TYPE
    unsigned dpl     :  2; //<! Descriptor Privilege Level
    unsigned present :  1; //<! Present flag (validity)
    unsigned rfu2    : 16; //<! Reserved
};
typedef struct idt_task_entry_s idt_task_entry_t;

/**
 * \union idt_entry_u
 * \brief Interrupt Descriptor Table entry
 */
union idt_entry_u {
    idt_int_entry_t  interrupt;
    idt_trap_entry_t trap;
    idt_task_entry_t task;
};
typedef union idt_entry_u idt_entry_t;

#define TASK_GATE_TYPE      0b00101
#define INTERRUPT_GATE_TYPE 0b01110
#define TRAP_GATE_TYPE      0b01111

/**
 * \struct idt_ptr_struct
 * \brief IDT pointer structure
 */
struct idt_ptr_s
{
    uint16_t limit;     //!< Address limit
    idt_entry_t *base;  //!< IDT pointer base
} __attribute__((packed));

typedef struct idt_ptr_s idt_ptr_t;

void idt_init(void);

#endif
