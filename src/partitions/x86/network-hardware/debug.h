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
 * \file debug.h
 * \brief Include file for debugging output
 */


#ifndef __SCR__
#define __SCR__

#include <stdint.h>
#include <stdarg.h>

void krn_puts(char *c);
void kaput(char c);
void puthex(int n);
void putdec(int n);

void counter_update(uint32_t begin);
void display_time();

int printf(const char *format, ...);

/**
 * \brief Strings for debugging output.
 */

#define DEBUG_HARD 0
#define CRITICAL	1 //!< Critical output
#define	ERROR		2 //!< Error output
#define WARNING		3 //!< Warning output
#define	INFO		4 //!< Information output
#define LOG		    5 //!< Log output
#define TRACE		6 //!< Annoying, verbose output

#define True 1
#define False 0


#ifndef LOGLEVEL
#define LOGLEVEL TRACE
#endif

/**
 * \brief Defines the appropriate DEBUGRAW behavior.
 */
#define DEBUGRAW(a) printf(a)

/**
 * \brief Defines the appropriate DEBUG behavior.
 */
#define DEBUG(l,a,...) if(l <= LOGLEVEL){printf("["#l "] " a "\n", ##__VA_ARGS__);}
/* #define DEBUG(l,a) { krn_puts(debugstr[l]); krn_puts("["); krn_puts(__FILE__); krn_puts(":"); putdec(__LINE__); krn_puts("] "); krn_puts(a);} */

/**
 * \brief Defines the appropriate DEBUGHEX behavior.
 */
#define DEBUGHEX(a) puthex(a)
/**
 * \brief Defines the appropriate DEBUGDEC behavior.
 */
#define DEBUGDEC(a) putdec(a)




#define BENCH_BEGIN counter_update(1)
#define BENCH_END {counter_update(0); DEBUG(TRACE, "Benchmark lasted "); display_time();}
#endif
