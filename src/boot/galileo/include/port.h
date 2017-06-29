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
 * \file port.h
 * \brief Include file for IO-ports operations
 */

#ifndef __PORT__
#define __PORT__

#include <stdint.h>

#define FAULT_FORBIDDEN		64

void outb(uint16_t port, uint8_t value); //!< IO port write byte
void outw(uint16_t port, uint16_t value); //!< IO port write word
void outl(uint16_t port, uint32_t value);

uint8_t inb(uint16_t port); //!< IO port read byte
uint16_t inw(uint16_t port); //!< IO port read word
uint32_t inl(uint16_t port);


void halt();
/* Call-gate IO methods */
void cg_outb(uint32_t port, uint32_t value); //!< Outb callgate method
uint32_t cg_inb(uint32_t port); //!< Inb callgate method

void cg_outw(uint32_t port, uint32_t value); //!< Outw callgate method
uint32_t cg_inw(uint32_t port); //!< Inw callgate method

void cg_outl(uint32_t port, uint32_t value); //!< Outl callgate method
void cg_outaddrl(uint32_t port, uint32_t value); //!< Outaddrl callgate method
uint32_t cg_inl(uint32_t port); //!< Inl callgate method

#endif
