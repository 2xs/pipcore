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
 * \file malinternal.c
 * \brief This file contains some internal defines for MAL interface with Coq.
 * \warning These functions are roughly documented as their signification is quite straightforward. See mal.h for more information.
 */

#include <stdint.h>
#include "mal.h"
#include "structures.h"

/*!
 * \fn uint32_t defaultAddr()
 * \brief Returns the default null address.
 * \return The null address.
 */
uint32_t defaultAddr(void)
{
	return 0;
}

const uint32_t defaultVAddr = 0;

/*!
 * \fn uint32_t kernelIndex()
 * \brief Returns the kernel address.
 * \return The kernel address.
 */
uint32_t kernelIndex(void)
{
	extern uint32_t __code;
	return getIndexOfAddr((uint32_t)(&__code), 1);
}

/*!
 * \fn uint32_t indexPR()
 * \brief Returns the partition root.
 * \return The partition root.
 */
uint32_t indexPR(void)
{
	return 0;
}

/*!
 * \fn uint32_t zero()
 * \brief Returns zero.
 * \return zero.
 */
uint32_t zero(void)
{
	return 0;
}

/*!
 * \fn uint32_t indexPD()
 * \brief Returns the page directory index.
 * \return The page directory index.
 */
uint32_t indexPD(void)
{
	return 2;
}

/*!
 * \fn uint32_t indexSh1()
 * \brief Returns the shadow 1 index.
 * \return The shadow 1 index.
 */
uint32_t indexSh1(void)
{
	return 4;
}

/*!
 * \fn uint32_t indexSh2()
 * \brief Returns the shadow 2 index.
 * \return The shadow 2 index.
 */
uint32_t indexSh2(void)
{
	return 6;
}

/*!
 * \fn uint32_t indexSh3()
 * \brief Returns the shadow 3 index.
 * \return The shadow 3 index.
 */
uint32_t indexSh3(void)
{
	return 8;
}

/*!
 * \fn uint32_t PPRidx()
 * \brief Returns the parent partition root.
 * \return The parent partition root.
 */
uint32_t PPRidx(void)
{
	return 10;
}

/*!
 * \fn uint32_t addressEquals(uint32_t addr, uint32_t addr2)
 * \param addr Address to check
 * \param addr2 Address to compare to
 * \brief Checks if an address given is equal to another given.
 * \return 0 is not equal, 1 otherwise.
 */
uint32_t addressEquals(uint32_t addr, uint32_t addr2)
{
	return (addr == addr2);
}

/*!
 * \fn uint32_t geb()
 * \brief the first parameter is greater than or equal to the second one.
 * \return the comparison.
 */
int geb(const uint32_t a, const uint32_t b)
{
	return a >= b;
}

/*!
 * \fn uint32_t gtb()
 * \brief the first parameter is greater than the second one.
 * \return the comparison.
 */
int gtb(const uint32_t a, const uint32_t b)
{
	return a > b;
}

/*!
 * \fn uint32_t leb()
 * \brief the first parameter is less than or equal to the second one.
 * \return the comparison.
 */
int leb(const uint32_t a, const uint32_t b)
{
	return a <= b;
}

/*!
 * \fn uint32_t ltb()
 * \brief the first parameter is less than the second one.
 * \return the comparison.
 */
int ltb(const uint32_t a, const uint32_t b)
{
	return a < b;
}

/*!
 * \fn uint32_t eqb()
 * \brief the first parameter is equal to the second one.
 * \return the comparison.
 */
int eqb(const uint32_t a, const uint32_t b)
{
	return a == b;
}

/*!
 * \fn uint32_t inc()
 * \brief incremet the value.
 * \return the incremented value.
 */
uint32_t inc(uint32_t val)
{
	return ++val;
}

/*!
 * \fn uint32_t sub()
 * \brief decrement value.
 * \return the decremented value.
 */
uint32_t sub(uint32_t val)
{
	return --val;
}

/*!
 * \fn uint32_t mul3()
 * \brief multiplies by 3.
 * \return the result of the multiplication by 3.
 */
uint32_t mul3(uint32_t v)
{
	return 3 * v;
}

/*!
 * \fn uint32_t getMaxIndex()
 * \brief get the maximum addressable index in the translation table.
 * \return the maximum index.
 */
uint32_t getMaxIndex(void)
{
       return getTableSize() - 1;
}
