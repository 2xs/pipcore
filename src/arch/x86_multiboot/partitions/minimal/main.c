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

#include <stdint.h>
#include <pip/fpinfo.h>
#include <pip/debug.h>
#include <pip/api.h>

#define SERIAL_PORT 0x3f8
#define INITIAL_STACK_TOP 0xFFFFE000

typedef struct pushad_regs_s
{
    uint32_t edi; //!< General register EDI
    uint32_t esi; //!< General register ESI
    uint32_t ebp; //!< EBP
    uint32_t esp; //!< Stack pointer
    uint32_t ebx; //!< General register EBX
    uint32_t edx; //!< General register EDX
    uint32_t ecx; //!< General register ECX
    uint32_t eax; //!< General register EAX
} pushad_regs_t;

typedef struct user_ctx_s
{
	uint32_t eip;
	uint32_t pipflags;
	uint32_t eflags;
	pushad_regs_t regs;
	uint32_t valid;
	uint32_t nfu[4];
} user_ctx_t;

uint32_t serial_transmit_ready(void);
void serial_putc(char c);
void serial_puts(const char *str);

void main(pip_fpinfo* bootinfo)
{
    user_ctx_t *setup_context = (user_ctx_t *) (INITIAL_STACK_TOP - sizeof(user_ctx_t));
    *((user_ctx_t **)0xFFFFF020) = setup_context;
    //Pip_Debug_Puts("Hello world from userland !\n");
    //Pip_Debug_Puts("Sending software int n°123\n");
    //asm("int $123;");
    //Pip_Debug_Puts("Trying to divide by zero\n");
    //int a = 3 / 0;
    //Pip_Debug_PutHex(a);
    const char *red_str   = "\033[0;31mRed !\n\033[0m";
    const char *green_str = "\033[0;32mGreen !\n\033[0m";
    while (1) {
        serial_puts(red_str);
        serial_puts(green_str);
    }
}

uint32_t serial_transmit_ready(void) {
    register uint32_t result asm("eax");
    asm (
       "push %1;"
       "lcall $0x38,$0x0;"
       "add $0x4, %%esp;"
       /* Outputs */
       : "=r" (result)
       /* Inputs */
       : "i" (SERIAL_PORT+5)
       /* Clobbers */
       :
    );
    return result & 0x20;
}

void serial_putc(char c) {
    asm (
        "push %1;"
        "push %0;"
	"lcall $0x30, $0x0;"
	"add $0x8, %%esp"
	/* Outputs */
	:
	/* Inputs */
	: "i" (SERIAL_PORT),
	  "r" ((uint32_t) c)
	/* Clobbers */
	:
    );
}

void serial_puts(const char *str) {
    for (char *it = str; *it; ++it) {
        //test if serial is ready
	while(!serial_transmit_ready());
        serial_putc(*it);
    }
}
