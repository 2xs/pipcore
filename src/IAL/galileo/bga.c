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

#include <stdint.h>
#include "port.h"
#include "gsod.h"

#define VBE_DISPI_IOPORT_INDEX		0x01CE
#define VBE_DISPI_IOPORT_DATA		0x01CF
#define VBE_DISPI_INDEX_ID			0
#define VBE_DISPI_INDEX_XRES		1
#define VBE_DISPI_INDEX_YRES		2
#define VBE_DISPI_INDEX_BPP			3
#define VBE_DISPI_INDEX_ENABLE		4
#define VBE_DISPI_INDEX_BANK		5
#define VBE_DISPI_INDEX_VIRT_WIDTH	6
#define VBE_DISPI_INDEX_VIRT_HEIGHT 7
#define VBE_DISPI_INDEX_X_OFFSET	8
#define VBE_DISPI_INDEX_Y_OFFSET	9
#define VBE_DISPI_ID0				0xB0C0
#define VBE_DISPI_ID1				0xB0C1
#define VBE_DISPI_ID2				0xB0C2
#define VBE_DISPI_ID3				0xB0C3
#define VBE_DISPI_ID4				0xB0C4
#define VBE_DISPI_ID5				0xB0C5
#define VBE_DISPI_DISABLED			0x0
#define VBE_DISPI_ENABLED			0x1
#define VBE_DISPI_LFB_ENABLED		0x40
#define VBE_DISPI_NOCLEARMEM		0x80

extern int isKernel (uint32_t cs);

uintptr_t vgaframebuffer = 0x0;

void
BgaWriteRegister (unsigned short IndexValue, unsigned short DataValue)
{
  outw (VBE_DISPI_IOPORT_INDEX, IndexValue);
  outw (VBE_DISPI_IOPORT_DATA, DataValue);
}

unsigned short
BgaReadRegister (unsigned short IndexValue)
{
  outw (VBE_DISPI_IOPORT_INDEX, IndexValue);
  return inw (VBE_DISPI_IOPORT_DATA);
}

int
BgaIsAvailable (void)
{
  return (BgaReadRegister (VBE_DISPI_INDEX_ID) == VBE_DISPI_ID4);
}

void
BgaSetVideoMode (unsigned int Width, unsigned int Height,
		 unsigned int BitDepth, int UseLinearFrameBuffer,
		 int ClearVideoMemory)
{
  BgaWriteRegister (VBE_DISPI_INDEX_ENABLE, VBE_DISPI_DISABLED);
  BgaWriteRegister (VBE_DISPI_INDEX_XRES, Width);
  BgaWriteRegister (VBE_DISPI_INDEX_YRES, Height);
  BgaWriteRegister (VBE_DISPI_INDEX_BPP, BitDepth);
  BgaWriteRegister (VBE_DISPI_INDEX_ENABLE, VBE_DISPI_ENABLED |
		    (UseLinearFrameBuffer ? VBE_DISPI_LFB_ENABLED : 0) |
		    (ClearVideoMemory ? 0 : VBE_DISPI_NOCLEARMEM));
}

void
BgaSetBank (unsigned short BankNumber)
{
  BgaWriteRegister (VBE_DISPI_INDEX_BANK, BankNumber);
}

uint32_t
color2int (uint8_t r, uint8_t g, uint8_t b, uint8_t a)
{
  uint32_t res =
    (b & 0x000000FF) | ((g << 8) & 0x0000FF00) | ((r << 16) & 0x00FF0000) |
    ((a << 24) & 0xFF000000);
  return res;
}

void
trigger_gsod (uint8_t int_no)
{
  BgaSetVideoMode (1024, 768, 32, 1, 1);
  //uintptr_t *lfb = (uintptr_t*)(0xFD000000);
  uintptr_t *lfb = (uintptr_t *) (vgaframebuffer);
  for (uint32_t i = 0; i < 1024 * 768; i++)
    *(uintptr_t *) ((uintptr_t) lfb + i * sizeof (uint32_t)) =
      color2int (255, 93, 249, 0);

  if ((int_no & 0x08) == 0x08)
    {
      lfb =
	(uintptr_t *) (vgaframebuffer + 224 * sizeof (uint32_t) * 1024 +
		       16 * sizeof (uint32_t));
      for (uint32_t y = 319; y > 0; y--)
	{
	  for (uint32_t x = 0; x < 240; x++)
	    {
	      uintptr_t dest =
		(uintptr_t) lfb + y * 1024 * sizeof (uint32_t) +
		x * sizeof (uint32_t);
	      uint32_t gsoddest =
		(uint32_t) gsod + 3 * sizeof (char) * 240 * (319 - y) +
		x * 3 * sizeof (char);
	      uint32_t pixel = ((*(uint32_t *) gsoddest) >> 16) & 0x00FFFFFF;
	      *(uint32_t *) dest = pixel;
	    }
	}
    }
  if ((int_no & 0x04) == 0x04)
    {
      lfb =
	(uintptr_t *) (vgaframebuffer + 224 * sizeof (uint32_t) * 1024 +
		       266 * sizeof (uint32_t));
      for (uint32_t y = 319; y > 0; y--)
	{
	  for (uint32_t x = 0; x < 240; x++)
	    {
	      uintptr_t dest =
		(uintptr_t) lfb + y * 1024 * sizeof (uint32_t) +
		x * sizeof (uint32_t);
	      uint32_t gsoddest =
		(uint32_t) gsod + 3 * sizeof (char) * 240 * (319 - y) +
		x * 3 * sizeof (char);
	      uint32_t pixel = ((*(uint32_t *) gsoddest) >> 8) & 0x00FFFFFF;
	      *(uint32_t *) dest = pixel;
	    }
	}
    }
  if ((int_no & 0x02) == 0x02)
    {
      lfb =
	(uintptr_t *) (vgaframebuffer + 224 * sizeof (uint32_t) * 1024 +
		       516 * sizeof (uint32_t));
      for (uint32_t y = 319; y > 0; y--)
	{
	  for (uint32_t x = 0; x < 240; x++)
	    {
	      uintptr_t dest =
		(uintptr_t) lfb + y * 1024 * sizeof (uint32_t) +
		x * sizeof (uint32_t);
	      uint32_t gsoddest =
		(uint32_t) gsod + 3 * sizeof (char) * 240 * (319 - y) +
		x * 3 * sizeof (char);
	      uint32_t pixel = ((*(uint32_t *) gsoddest)) & 0x00FFFFFF;
	      *(uint32_t *) dest = pixel;
	    }
	}
    }
  if ((int_no & 0x01) == 0x01)
    {
      lfb =
	(uintptr_t *) (vgaframebuffer + 224 * sizeof (uint32_t) * 1024 +
		       766 * sizeof (uint32_t));
      for (uint32_t y = 319; y > 0; y--)
	{
	  for (uint32_t x = 0; x < 240; x++)
	    {
	      uintptr_t dest =
		(uintptr_t) lfb + y * 1024 * sizeof (uint32_t) +
		x * sizeof (uint32_t);
	      uint32_t gsoddest =
		(uint32_t) gsod + 3 * sizeof (char) * 240 * (319 - y) +
		x * 3 * sizeof (char);
	      uint32_t pixel = ((*(uint32_t *) gsoddest) << 8) & 0x00FFFFFF;
	      *(uint32_t *) dest = pixel;
	    }
	}
    }
  lfb =
    (uintptr_t *) (vgaframebuffer + 600 * sizeof (uint32_t) * 1024 +
		   312 * sizeof (uint32_t));
  for (uint32_t y = 59; y > 0; y--)
    {
      for (uint32_t x = 0; x < 400; x++)
	{
	  uintptr_t dest =
	    (uintptr_t) lfb + y * 1024 * sizeof (uint32_t) +
	    x * sizeof (uint32_t);
	  uint32_t pascontentdest =
	    (uint32_t) pascontent + 3 * sizeof (char) * 400 * (59 - y) +
	    x * 3 * sizeof (char);
	  uint32_t pixel = ((*(uint32_t *) pascontentdest)) & 0x00FFFFFF;
	  *(uint32_t *) dest = pixel;
	}
    }
}

