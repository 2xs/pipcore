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

/**
 * \file debug.c
 * \brief Benchmarking and serial line output
 */

#include "debug.h"
#include "serial.h"
#include <stdint.h>
#include "libc.h"
#include <stdarg.h>
#include "segment_selectors.h"
#include "hdef.h"

/**
 * \fn krn_puts(char* c)
 * \brief Writes a string to the serial output
 * \param c The string to write
 */
void krn_puts(char *c)
{
   int i = 0;
   while (c[i])
   {
       writeSerial(c[i++]);
   }
}

/**
 * \fn void panic (int_ctx_t *is)
 * \brief Just a loop acting like a kernel panic
 */
void panic (int_ctx_t *is)
{
	DEBUG(CRITICAL, "Pip kernel panic - something happened\n");
	if(is) {
		dumpRegs(is, CRITICAL);
	}
	DEBUG(CRITICAL, "\tSystem halted. ~\n");
	__asm volatile("cli; hlt;");
	for(;;);
}

/**
 * \fn dumpRegs(int_ctx_t* is, uint32_t outputLevel)
 * \brief Dumps the registers of a saved interrupt context onto the serial output.
 * \param is Interrupted state
 * \param outputLevel Serial log debugging output level
 */
void dumpRegs(int_ctx_t* is, uint32_t outputLevel)
{
	DEBUG(outputLevel, "Register dump: eax=%x, ebx=%x, ecx=%x, edx=%x\n",
		  GENERAL_REG(is, eax),
		  GENERAL_REG(is, ebx),
		  GENERAL_REG(is, ecx),
		  GENERAL_REG(is, edx));
	DEBUG(outputLevel, "               edi=%x, esi=%x, ebp=%x, esp=%x\n",
		  GENERAL_REG(is, edi),
		  GENERAL_REG(is, esi),
		  GENERAL_REG(is, ebp),
		  OPTIONAL_REG(is, useresp));
	if(OPTIONAL_REG(is, cs) == KERNEL_CODE_SEGMENT_SELECTOR)
	{
		DEBUG(outputLevel, "               cs=%x, eip=%x, int=%x\n",
			  OPTIONAL_REG(is, cs),
			  OPTIONAL_REG(is, eip),
			  OPTIONAL_REG(is, int_no));
	} else {
		DEBUG(outputLevel, "               cs=%x, ss=%x, eip=%x, int=%x\n",
			  OPTIONAL_REG(is, cs),
			  OPTIONAL_REG(is, ss),
			  OPTIONAL_REG(is, eip),
			  OPTIONAL_REG(is, int_no));
	}
}


/**
 * \fn void puthex(int n)
 * \brief Writes an hexadecimal number to the serial output
 * \param n The number to write
 */
void puthex(int n)
{
    int tmp;

    krn_puts("0x");

    char noZeroes = 1;

    int i;
    for (i = 28; i > 0; i -= 4)
    {
        tmp = (n >> i) & 0xF;
        if (tmp == 0 && noZeroes != 0)
        {
            continue;
        }
    
        if (tmp >= 0xA)
        {
            noZeroes = 0;
            writeSerial(tmp-0xA+'A' );
        }
        else
        {
            noZeroes = 0;
            writeSerial( tmp+'0' );
        }
    }
  
    tmp = n & 0xF;
    if (tmp >= 0xA)
    {
        writeSerial (tmp-0xA+'A');
    }
    else
    {
        writeSerial (tmp+'0');
    }

}

/**
 * \fn void putdec(int n)
 * \brief Writes a decimal number to the serial output
 * \param n The number to write
 */
void putdec(int n)
{

    if (n == 0)
    {
        writeSerial('0');
        return;
    }

    int acc = n;
    char c[32];
    int i = 0;
    while (acc > 0)
    {
        c[i] = '0' + acc%10;
        acc /= 10;
        i++;
    }
    c[i] = 0;

    char c2[32];
    c2[i--] = 0;
    int j = 0;
    while(i >= 0)
    {
        c2[i--] = c[j++];
    }
    krn_puts(c2);
}

uint32_t perfHighBegin;
uint32_t perfLowBegin;
uint32_t perfHighEnd;
uint32_t perfLowEnd;

void counterUpdate(uint32_t begin)
{
    uint32_t bufHigh, bufLow;
    __asm volatile(" \
                   MOV $0, %%ECX; \
                   RDTSC; \
                   MOV %%EAX, %0; \
                   MOV %%EDX, %1; "
                   : "=r" (bufLow), "=r" (bufHigh));
    
    if(begin) {
        perfLowBegin = bufLow;
        perfHighBegin = bufHigh;
    } else {
        perfLowEnd = bufLow;
        perfHighEnd = bufHigh;
    }
    
    return;
}

void displayTime()
{
    uint32_t resHigh, resLow;

    uint32_t carry;
    if(perfLowEnd > perfLowBegin)
    {
        resLow = perfLowEnd - perfLowBegin;
        carry = 0;
    } else {
        resLow = perfLowEnd + (0xFFFFFFFF - perfLowBegin);
        carry = 1;
    }
    
    resHigh = perfHighEnd - perfHighBegin - carry;
    
    DEBUGDEC(resHigh);
    DEBUGDEC(resLow);
    DEBUGRAW(" cycles\n");
}

static char* bf;
static char buf[12];
static unsigned int num;
static char uc;
static char zs;

/* Full credits to https://github.com/rlangoy/ZedBoard-BareMetal-Examples/blob/master/Hello05/printf.c for this, thanks buddy */
void kprintf(char *fmt, ...)
{
	va_list va;
	char ch;
	char* p;
	
	va_start(va,fmt);
	
	while ((ch=*(fmt++))) {
		if (ch!='%') {
			writeSerial(ch);
		}
		else {
			char lz=0;
			char w=0;
			ch=*(fmt++);
			if (ch=='0') {
				ch=*(fmt++);
				lz=1;
			}
			if (ch>='0' && ch<='9') {
				w=0;
				while (ch>='0' && ch<='9') {
					w=(((w<<2)+w)<<1)+ch-'0';
					ch=*fmt++;
				}
			}
			bf=buf;
			p=bf;
			zs=0;
			switch (ch) {
				case 0:
					goto abort;
				case 'u':
				case 'd' :
					num=va_arg(va, unsigned int);
					if (ch=='d' && (int)num<0) {
						num = -(int)num;
						writeSerial('-');
					}
					putdec(num);
					break;
				case 'x':
				case 'X' :
					uc= ch=='X';
					num=va_arg(va, unsigned int);
					puthex(num);
					break;
				case 'c' :
					writeSerial((char)(va_arg(va, int)));
					break;
				case 's' :
					p=va_arg(va, char*);
					break;
				case '%' :
					writeSerial('%');
				default:
					break;
			}
			*bf=0;
			bf=p;
			while (*bf++ && w > 0)
				w--;
			while (w-- > 0)
				writeSerial(lz ? '0' : ' ');
			while ((ch= *p++))
				writeSerial(ch);
		}
	}
abort:;
	va_end(va);
}
