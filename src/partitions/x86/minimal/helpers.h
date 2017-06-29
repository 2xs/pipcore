
#ifndef HELPERS_H
#define HELPERS_H

#include <stdint.h>
#include <pip/io.h>
#include "mmio.h"
#include "fastmemcpy.h"




#define MEMCPY_TO_META(dest,src,count) fastmemcpy((void *)dest,(void *)src,(size_t)count)
#define MEMCPY_FROM_META(dest,src,count) fastmemcpy((void *)dest,(void *)src,(size_t)count)

#define BIT(n) (1 << (n))


#define PROT_DOMAINS_INIT_ID(nm)                                              \
  KERN_WRITEL((nm).dom_id, PROT_DOMAINS_GET_DOM_ID(&PROT_DOMAINS_PDCS_NM(nm)))

#define PROT_DOMAINS_GET_DOM_ID(dkd)                                          \
  ((dom_id_t)((dkd) - prot_domains_kern_data))

#define STRINGIFY(x) #x
/* The C preprocessor will not expand macro arguments that are converted to
 * strings in the macro body using the '#' operator.  The EXP_STRINGIFY macro
 * introduces an additional level of argument expansion for instances where
 * the developer wishes to convert the expanded argument to a string.
 */
#define EXP_STRINGIFY(x) STRINGIFY(x)

#define ALIGN(x, amt) \
  (((x) & ~((amt) - 1)) + ((((x) & ((amt) - 1)) == 0) ? 0 : (amt)))

/** MMIO MANAGEMENT */


#define ENABLE_MMIO()
#define DISABLE_MMIO()
#endif /* HELPERS_H */
