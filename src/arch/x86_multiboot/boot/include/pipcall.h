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

#ifndef ARCH_PIPCALL_H
#define ARCH_PIPCALL_H

#define LAST_PIPCALL PIPCALL_YIELD

#define PIPCALL_OUTB             6
#define PIPCALL_INB              7
#define PIPCALL_OUTW             8
#define PIPCALL_INW              9
#define PIPCALL_OUTL             10
#define PIPCALL_INL              11
#define PIPCALL_CREATEPARTITION  12
#define PIPCALL_COUNTTOMAP       13
#define PIPCALL_PREPARE          14
#define PIPCALL_ADDVADDR         15
#define PIPCALL_GET_INT_STATE    16
#define PIPCALL_OUTADDRL         17
#define PIPCALL_TIMER            18
#define PIPCALL_SET_INT_STATE    19
#define PIPCALL_REMOVEVADDR      20
#define PIPCALL_MAPPEDINCHILD    21
#define PIPCALL_DELETEPARTITION  22
#define PIPCALL_COLLECT          23
#define PIPCALL_YIELD            24

#define PIPCALL_NARGS_OUTB             2
#define PIPCALL_NARGS_INB              1
#define PIPCALL_NARGS_OUTW             2
#define PIPCALL_NARGS_INW              1
#define PIPCALL_NARGS_OUTL             2
#define PIPCALL_NARGS_INL              1
#define PIPCALL_NARGS_CREATEPARTITION  5
#define PIPCALL_NARGS_COUNTTOMAP       2
#define PIPCALL_NARGS_PREPARE          3
#define PIPCALL_NARGS_ADDVADDR         6
#define PIPCALL_NARGS_GET_INT_STATE    1
#define PIPCALL_NARGS_OUTADDRL         2
#define PIPCALL_NARGS_TIMER            0
#define PIPCALL_NARGS_SET_INT_STATE    1
#define PIPCALL_NARGS_REMOVEVADDR      2
#define PIPCALL_NARGS_MAPPEDINCHILD    1
#define PIPCALL_NARGS_DELETEPARTITION  1
#define PIPCALL_NARGS_COLLECT          2
#define PIPCALL_NARGS_YIELD            5

#endif
