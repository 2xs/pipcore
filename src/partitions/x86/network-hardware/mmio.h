#ifndef _MMIO_
#define _MMIO_

#include "pip/io.h"
#ifndef MMIO_READL
#define MMIO_READL(dst, src) writeMMIO((uintptr_t)dst,(uintptr_t)src);
#define MMIO_READW(dst, src) writeMMIO((uintptr_t)dst,(uintptr_t)src);
#define MMIO_READB(dst, src) writeMMIO((uintptr_t)dst,(uintptr_t)src);
#define MMIO_WRITEL(dst, src) MMIO_READL(dst, src)
#define MMIO_WRITEW(dst, src) MMIO_READW(dst, src)
#define MMIO_WRITEB(dst, src) MMIO_READB(dst, src)
#endif
#ifndef KERN_READL
#define KERN_READL(dst, src) writeMMIO((uintptr_t)dst,(uintptr_t)src);
#define KERN_READW(dst, src) writeMMIO((uintptr_t)dst,(uintptr_t)src);
#define KERN_READB(dst, src) writeMMIO((uintptr_t)dst,(uintptr_t)src);
#define KERN_WRITEL(dst, src) KERN_READL(dst, src)
#define KERN_WRITEW(dst, src) KERN_READW(dst, src)
#define KERN_WRITEB(dst, src) KERN_READB(dst, src)
#endif
#ifndef META_READL
#define META_READL(dst, src) writeMMIO((uintptr_t)dst,(uintptr_t)src);
#define META_READW(dst, src) writeMMIO((uintptr_t)dst,(uintptr_t)src);
#define META_READB(dst, src) writeMMIO((uintptr_t)dst,(uintptr_t)src);
#define META_WRITEL(dst, src) META_READL(dst, src)
#define META_WRITEW(dst, src) META_READw(dst, src)
#define META_WRITEB(dst, src) META_READB(dst, src)
#endif



#endif
