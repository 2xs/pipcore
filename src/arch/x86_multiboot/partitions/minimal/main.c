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

#define SERIAL_PORT 0x3f8

uint32_t serial_transmit_ready(void);
void serial_putc(char c);
void serial_puts(const char *str);

void _main()
{
    const char *Hello_world_str = "Hello World !\n";
    serial_puts(Hello_world_str);
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
	while(!serial_transmit_ready());
        serial_putc(*it);
    }
}
