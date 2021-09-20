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

#ifndef DEF_CONTEXT_H_
#define DEF_CONTEXT_H_

#include <stdint.h>

typedef enum arm_ctxreg_e {
	CTX_SP  ,
	CTX_LR  ,
	CTX_R0  ,
	CTX_R1  ,
	CTX_R2  ,
	CTX_R3  ,
	CTX_R4  ,
	CTX_R5  ,
	CTX_R6  ,
	CTX_R7  ,
	CTX_R8  ,
	CTX_R9  ,
	CTX_R10 ,
	CTX_R11 ,
	CTX_R12 ,
	CTX_PC
} arm_ctxreg_t;

/**
 * \struct gate_stack_s
 * \brief Stack context from callgate after assembly magic
 */
typedef struct gate_ctx_s
{
	uint32_t spsr;
	uint32_t reg[16];
} arm_ctx_t, gate_ctx_t;

/**
 * \struct user_ctx_s
 * \brief User saved context
 */
typedef struct user_ctx_s
{
	uint32_t spsr;
	uint32_t reg[16];
	uint32_t pipflags;
	uint32_t valid;
} user_ctx_t;

#endif
