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
 * \file properties.c
 * \brief ARMv7 MAL properties methods
 */

#include <stdint.h>
#include "structures.h"

/*!
 * \brief Testing if the virtual address v of the page directory pd is
 *        accessible or not.
 * \param pd a page directory
 * \param v a virtual address
 * \result 1 if accessible, O else
 */
uint32_t accessible(uint32_t pd, uint32_t v)
{
    /* TODO */
    (void) pd;
    (void) v;
    return (uint32_t) 0;
}

/*!
 * \brief Testing if a given virtual address is mapped or not into a virtual
 *        space.
 * \param pd a page directory
 * \param v a virtual address
 * \result 1 if present, 0 else
 */
uint32_t present(uint32_t pd, uint32_t v)
{
    /* TODO */
    (void) pd;
    (void) v;
    return (uint32_t) 0;
}

/*!
 * \brief Modify the user bit value
 * \param pd a page directory
 * \param v  a virtual address
 * \param access the new value of the user bit
 * \post The accessible bit of the virtual address is equal to access
 */
void write_accessible(uint32_t pd, uint32_t v, uint32_t accessible)
{
    /* TODO */
    (void) pd;
    (void) v;
    (void) accessible;
    return;
}

/*!
 * \brief Modify the present bit value.
 * \param pd a page directory
 * \param v a virtual address
 * \param present the new value of the present bit
 * \post The present bit of the virtual address is equal to present
 */
void write_present(uint32_t pd, uint32_t v, uint32_t present)
{
    /* TODO */
    (void) pd;
    (void) v;
    (void) present;
    return;
}
