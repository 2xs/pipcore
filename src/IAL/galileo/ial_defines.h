#ifndef __IAL_DEFINES__
#define __IAL_DEFINES__

#define IAL_PREFIX				"みちる"
#define IAL_VERSION				"0.1"

#define SIZEOF_CTX				sizeof(int_ctx_t)
#define GENERAL_REG(a, c)		a->regs.c
#define OPTIONAL_REG(a, c)		a->c

#define PIPFLAGS				((uintptr_t*)0xFFFFFFFC)
#define INTLEVEL_GET			(*PIPFLAGS & 0xFFFFFF00) >> 8
#define INTLEVEL_SET(a)			*PIPFLAGS = (*PIPFLAGS & 0xFFFFFF00) | (a << 8)
#define VIDT_VCLI				*PIPFLAGS & 0x00000001


#define VIDT_CTX_BUFFER			(int_ctx_t*)(PIPFLAGS - SIZEOF_CTX)
#define INT_IRQ(a)				(a >= 32 && a <= 47)

#define PARTITION_PARENT		0
#define PARTITION_ROOT			getRootPartition()
#define PARTITION_CURRENT		getCurPartition()

#define VIDT					0xFFFFF000
#define VIDT_INT_EIP(a)			readTableVirtualNoFlags (VIDT, (2 * a))
#define VIDT_INT_ESP(a)			readTableVirtualNoFlags (VIDT, (2 * a) + 1)
#define VIDT_INT_ESP_SET(a,s)	writeTableVirtualNoFlags (VIDT, (2 * a) + 1, s)
#endif
