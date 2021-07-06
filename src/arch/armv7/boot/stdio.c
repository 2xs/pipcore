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

#include "stdio.h"
#include "uart.h"

static void printchar(char **str, int c)
{
    if (str)
    {
        **str = (char)c;
        ++(*str);
    }
    else
    {
        uart_send(c);
    }
}

#define PAD_RIGHT 1
#define PAD_ZERO 2

static int prints(char **out, const char *string, int width, int pad)
{
    register int pc = 0, padchar = ' ';

    if (width > 0)
    {
        register int len = 0;
        register const char *ptr;

        for (ptr = string; *ptr; ++ptr)
        {
            ++len;
        }

        if (len >= width)
        {
            width = 0;
        }
        else
        {
            width -= len;
        }

        if (pad & PAD_ZERO)
        {
            padchar = '0';
        }
    }

    if (!(pad & PAD_RIGHT))
    {
        for ( ; width > 0; --width)
        {
            printchar(out, padchar);
            ++pc;
        }
    }

    for ( ; *string ; ++string)
    {
        printchar(out, *string);
        ++pc;
    }

    for ( ; width > 0; --width)
    {
        printchar(out, padchar);
        ++pc;
    }

    return pc;
}

#define PRINT_BUF_LEN 12

static int printi(char **out, int i, int b, int sg, int width, int pad, int letbase)
{
    char print_buf[PRINT_BUF_LEN];
    register char *s;
    register int t, neg = 0, pc = 0;
    register unsigned int u = (unsigned int)i;

    if (i == 0)
    {
        print_buf[0] = '0';
        print_buf[1] = '\0';
        return prints (out, print_buf, width, pad);
    }

    if (sg && b == 10 && i < 0)
    {
        neg = 1;
        u = (unsigned int)-i;
    }

    s = print_buf + PRINT_BUF_LEN-1;
    *s = '\0';

    while (u)
    {
        t = (unsigned int)u % b;
        if( t >= 10 )
            t += letbase - '0' - 10;
        *--s = (char)(t + '0');
        u /= b;
    }

    if (neg)
    {
        if(width && (pad & PAD_ZERO))
        {
            printchar(out, '-');
            ++pc;
            --width;
        }
        else
        {
            *--s = '-';
        }
    }

    return pc + prints(out, s, width, pad);
}

static int print(char **out, const char *format, va_list args)
{
    register int width, pad;
    register int pc = 0;
    char scr[2];

    for (; *format != 0; ++format)
    {
        if (*format == '%')
        {
            ++format;
            width = pad = 0;

            if (*format == '\0')
            {
                break;
            }

            if (*format == '%')
            {
                goto out;
            }

            if (*format == '-')
            {
                ++format;
                pad = PAD_RIGHT;
            }

            while (*format == '0')
            {
                ++format;
                pad |= PAD_ZERO;
            }

            for (; *format >= '0' && *format <= '9'; ++format)
            {
                width *= 10;
                width += *format - '0';
            }

            if (*format == 's')
            {
                register char *s = va_arg(args, char *);
                pc += prints(out, s?s:"(null)", width, pad);
                continue;
            }

            if (*format == 'd')
            {
                pc += printi(out, va_arg(args, int), 10, 1,
                        width, pad, 'a');
                continue;
            }

            if(*format == 'x')
            {
                pc += printi(out, va_arg(args, int), 16, 0,
                        width, pad, 'a');
                continue;
            }

            if(*format == 'X')
            {
                pc += printi(out, va_arg(args, int), 16, 0,
                        width, pad, 'A');
                continue;
            }

            if( *format == 'u' )
            {
                pc += printi(out, va_arg(args, int), 10, 0,
                        width, pad, 'a');
                continue;
            }

            if(*format == 'c')
            {
                scr[0] = (char) va_arg(args, int);
                scr[1] = '\0';

                pc += prints(out, scr, width, pad);

                continue;
            }
        }
        else
        {
            out:
            printchar(out, *format);
            ++pc;
        }
    }

    if (out)
    {
        **out = '\0';
    }

    va_end(args);

    return pc;
}

extern int printf(const char *format, ...)
{
    va_list args;

    va_start(args, format);

    return print(0, format, args);
}

extern int sprintf(char *str, const char *format, ...)
{
    va_list args;

    va_start(args, format);

    return print(&str, format, args);
}

extern int snprintf(char *str, unsigned int size, const char *format, ...)
{
    va_list args;
    (void) size;

    va_start(args, format);

    return print(&str, format, args);
}
