/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2017)                 */
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
 * \file libc.c
 * \brief Pseudo-libC implementation
 * \warning Some of these implementations are unsafe. We know. We're not proud of this.
 */

#include "libc.h"
#include <stdint.h>

/**
 * \fn memset ( void * ptr, int value, size_t num )
 * \brief Sets a memory space with a single, fixed value
 * \param ptr Pointer to the memory space
 * \param value The value to write
 * \param num The amount of memory to write to
 * \return Pointer to the memory space
 */
void * memset( void * ptr, int value, size_t num )
{
	char *temp = (char*) ptr;
	for(; num != 0; num--) *temp++ = value;
	return ptr;
}

/**
 * \fn void *strcpy(char* dest, const char* src)
 * \brief String copy
 */
void *strcpy(char* dest, const char* src)
{
	char *p = dest;

	while ((*p++ = *src++));

	return dest;
}

/**
 * \fn memcpy ( void * destination, const void * source, size_t num )
 * \brief Copies data from source to destination
 * \param destination Destination address
 * \param source Source address
 * \param num Size of data to copy
 * \return Pointer to the destination address
 */
void * memcpy ( void * destination, const void * source, size_t num )
{
	uint32_t i;
	uint8_t *src;
	uint8_t *dest;
	src = (uint8_t*) source;
	dest = (uint8_t*) destination;
	for(i=0; i<num; i++)
	{
		*dest = *src;
		dest++;
		src++;
	}
	return destination;
}

/**
 * \fn strcat(char* dest, const char* source)
 * \brief Concatenates a source string into a destination string, assuming the destination string buffer is large enough.
 * \param dest Destination string buffer
 * \param source Source string buffer
 * \return Destination string buffer, containing the concatenated strings.
 */
char* strcat(char* dest, const char* source)
{
        int idx, i, j;

        for(idx=0; *(dest+idx) != '\0'; idx++) {}
        for(i=0; *(source+i) != '\0'; i++) {}

	for(j = 0; j<(i+1); j++) {
		*(dest + idx + j) = *(source + j);
	}
	return dest;
}

/**
 * \fn int strlen(char* str)
 * \brief String length
 */
int strlen(char* str)
{
	int i = 0;
	while(str[i] != '\0')
		i++;
	
	return i;
}

int strcmp(const char *s1, const char* s2) {
    while(*s1 && (*s1==*s2))
        s1++,s2++;
    return *(const unsigned char*)s1-*(const unsigned char*)s2;
}

int memcmp(const void *s1, const void *s2, size_t n) {
    const unsigned char *p1 = s1, *p2 = s2;
    while(n--)
        if( *p1 != *p2 )
            return *p1 - *p2;
        else
            p1++,p2++;
    return 0;
}
