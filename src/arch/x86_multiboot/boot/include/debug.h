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
 * \file debug.h
 * \brief Include file for debugging output
 */


#ifndef __SCR__
#define __SCR__

#include <stdint.h>
#include <stdarg.h>
#include "x86int.h"
#include "mal.h"

/**
 * \brief Strings for debugging output.
 */
#define CRITICAL	0 //!< Critical output
#define	ERROR		1 //!< Error output
#define WARNING		2 //!< Warning output
#define	INFO		3 //!< Information output
#define LOG		4 //!< Log output
#define TRACE		5 //!< Annoying, verbose output

#ifdef PIPDEBUG

#ifndef LOGLEVEL
#define LOGLEVEL CRITICAL
#endif

/**
 * \brief Defines the appropriate DEBUGRAW behavior.
 */
#define DEBUGRAW(a) krn_puts(a)

/**
 * \brief Defines the appropriate DEBUG behavior.
 */

#define DEBUG(loglvl,msg,...) if(loglvl<=LOGLEVEL){ kprintf(#loglvl " [%s:%d] " msg, __FILE__, __LINE__, ##__VA_ARGS__);}

/**
 * \brief Defines the appropriate DEBUGHEX behavior.
 */
#define DEBUGHEX(a) puthex(a)
/**
 * \brief Defines the appropriate DEBUGDEC behavior. 
 */
#define DEBUGDEC(a) putdec(a)

#else

/**
 * \brief Defines the appropriate DEBUGRAW behavior.
 */
#define DEBUGRAW(...)

/**
 * \brief Defines the appropriate DEBUG behavior.
 */
#define DEBUG(...)

/**
 * \brief Defines the appropriate DEBUGHEX behavior.
 */
#define DEBUGHEX(...)

/**
 * \brief Defines the appropriate DEBUGDEC behavior.
 */
#define DEBUGDEC(...)

#endif

void krn_puts(char *c);
void kaput(char c);
void puthex(int n);
void putdec(int n);

void counter_update(uint32_t begin);
void display_time();

void kprintf(char *fmt, ...);
void dumpRegs(int_ctx_t *is, uint32_t outputLevel);

#define BENCH_BEGIN counter_update(1)
#define BENCH_END {counter_update(0); DEBUG(TRACE, "Benchmark lasted "); display_time();}

#endif
