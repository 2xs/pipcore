/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2024)                */
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

ENTRY(start)
SECTIONS
{
/* Kernel load address defined during make (Makefile.inc), used in everything */
.text 0x100000 :
{
__multiboot_header = .;
*(.multiboot_header)
. = ALIGN(4096);
code = .; _code = .; __code = .;
*(.text)
. = ALIGN(4096);
}

.data :
{
data = .; _data = .; __data = .;
*(.data)
*(.rodata)
. = ALIGN(4096);
}

.bss :
{
bss = .; _bss = .; __bss = .;
*(.bss)
. = ALIGN(4096);
}

/* Kernel stack address defined during make (Makefile.inc), used in boot_assembly.s */
.krnstack 0x300000 :
{
krnstack = .; _krnstack = .; __krnstack = .;
*(.krnstack)
. = ALIGN(4096);
}

/* Multiplexer load address defined during make (Makefile.inc), used in multiplexer.s */
.multiplexer 0x700000 :
{
multiplexer = .;
_multiplexer = .;
__multiplexer = .;
*(.multiplexer)
. = ALIGN(4096);
}

end = .; _end = .; __end = .;
}
