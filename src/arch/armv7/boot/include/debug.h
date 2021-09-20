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

#ifndef DEF_DEBUG_H_
#define DEF_DEBUG_H_
#include <printf.h>

enum loglevel_e { ERROR = 0, WARNING, INFO, TRACE};

static unsigned debug_color[] = {
	[ERROR]		= 31,
	[WARNING]	= 33,
	[INFO]		= 32,
	[TRACE]		= 36,
};

#ifndef LOGLEVEL
#define LOGLEVEL ERROR
#endif

//#define DEBUG(lvl, fmt, ...) if (LOGLEVEL >= lvl){ printf("[" #lvl "] " fmt, #__VA_ARGS__);}
#define DEBUG(lvl, fmt, ...) if (LOGLEVEL >= lvl) { printf("\e[35m%s\e[0m:\e[31m%d\e[0m: " "\e[%dm" fmt "\e[0m", __FILE__, __LINE__, debug_color[lvl], ##__VA_ARGS__);}

/* FIXME: MOVE THIS
 * and also: mask interrupts  */
#define PANIC(fmt,...) { DEBUG(ERROR,fmt "\n", ##__VA_ARGS__); for(;;); }

#endif
