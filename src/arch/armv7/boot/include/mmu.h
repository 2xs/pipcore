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

#ifndef DEF_MMU_H
#define DEF_MMU_H

#include "types.h"

/* Truncated L1 translation table */
#define MMU_TTBR0_ENT_COUNT 0x400

/* Full translation table */
#define MMU_TTBR1_ENT_COUNT 0x1000

/* Use 1/4 of the translation table */
#define MMU_L1_ENT_COUNT 0x400
/* Use the whole L2 table */
#define MMU_L2_ENT_COUNT 0x100

typedef enum mmu_rgn_e {
	RGN_NOCACHE             = 0,
	RGN_CACHE_WBACK_WALLOC  = 1,
	RGN_CACHE_WTHROUGH      = 2,
	RGN_CACHE_WBACK_NOALLOC = 3,
} mmu_rgn_t;

/*	B3-1326: Short-descriptor page table (level 1) */
typedef union mmu_sd_pt_s {
	unsigned aslong;
	struct {
		unsigned one:2;		/* Must be 1 for a page table */
		unsigned pxn:1;		/* Privileged execute-never */
		unsigned ns:1;		/* Non-secure */
		unsigned zero:1;	/* SBZ */
		unsigned domain:4;	/* B3.7.3 Domains, Short-descriptor format only */
		unsigned unk:1;		/* Implementation defined */
		unsigned ptbaddr:22;
	};
} mmu_sd_pt_t ;

/* Short-format section */
typedef union mmu_sd_sec_s {
	unsigned aslong;
	struct {
		unsigned pxn:1;		/* Privileged execute-never */
		unsigned one:1;		/* Must be 1 for a section */
		unsigned B:1;		/* B3.8.2 : memory attributes */
		unsigned C:1;		/* B3.8.2 */
		unsigned xn:1;		/* eXecute Never */
		unsigned domain:4;	/* B3.7.3 Domains, Short-descriptor format only */
		unsigned unk:1;
		unsigned AP0:1;		/* Access permission bit 0 */
		unsigned AP1:1;		/* Access permission bit 1 */
		unsigned TEX:3;		/* B3.8.2 */
		unsigned AP2:1;		/* Access permission bit 2 */
		unsigned S:1;		/* B3-1366 : Shareable */
		unsigned nG:1;		/* B3-1378 : not Global */
		unsigned zero:1;	/* Must be zero for a section */
		unsigned ns:1;		/* Non-secure */
		unsigned secbaddr:12; /* paddr of section (1MB) */
	};
} mmu_sd_sec_t ;

/* Short-format supersection */
typedef union mmu_sd_ssec_s {
	unsigned aslong;
	struct {
		unsigned pxn:1;		/* Privileged execute-never */
		unsigned one1:1;		/* Must be 1 for a supersection */
		unsigned B:1;		/* B3.8.2 : memory attributes */
		unsigned C:1;		/* B3.8.2 */
		unsigned xn:1;		/* eXecute Never */
		unsigned PA2:4;		/* Extended base address, PA[39:36] */
		unsigned unk:1;
		unsigned AP0:1;		/* Access permission bit 0 */
		unsigned AP1:1;		/* Access permission bit 1 */
		unsigned TEX:3;		/* B3.8.2 */
		unsigned AP2:1;		/* Access permission bit 2 */
		unsigned S:1;		/* B3-1366 : Shareable */
		unsigned nG:1;		/* B3-1378 : not Global */
		unsigned one2:1;	/* Must be one for a supersection */
		unsigned ns:1;		/* Non-secure */
		unsigned PA1:4;		/* Extended base address, PA[39:36] */
		unsigned secbaddr:8; /* PA[31:24] of supersection (16MB) */
	};
} mmu_sd_ssec_t ;


/*	B3-1327: Short-descriptor small page descriptor (level 2)
 *	B3-1366: Memory attributes in the Short-descriptor translation table format descriptors */
typedef union mmu_sd_sp_s {
	unsigned aslong;
	struct {
		unsigned xn:1;		/* eXecute Never*/
		unsigned one:1;		/* Must be 1 for a small page */
		unsigned B:1;		/* B3.8.2 : memory attributes */
		unsigned C:1;		/* B3.8.2 */
		unsigned AP0:1;		/* Access permission bit 0 */
		unsigned AP1:1;		/* Access permission bit 1 */
		unsigned TEX:3;		/* B3.8.2 */
		unsigned AP2:1;		/* Access permission bit 2 */
		unsigned S:1;		/* B3-1366 : Shareable */
		unsigned nG:1;		/* B3-1378 : not Global (
			0: Global, page is available for all processes
			1: not Global, page availability depends on ASID */
		unsigned spbaddr:20;/* paddr of small page (4KB) */
	};
} mmu_sd_sp_t ;

mmu_sd_pt_t mmu_make_page_table(
	void	*ptbaddr		/* Full address of aligned(12) small page */
);

mmu_sd_sp_t mmu_make_small_page(
	void	*spbaddr		/* Full address of aligned(12) small page */
	, bool_t	user		/* User accessible */
	, bool_t	ro			/* Read only */
	, bool_t	xn			/* eXecute never */
	, bool_t	device
	, bool_t	global
);

/*	B4.1.154 TTBR0, Translation Table Base Register 0
 *	Build translation table register */
unsigned mmu_make_ttbr (
	void * base,
	mmu_rgn_t irgn,			/* Cache inner attributes */
	mmu_rgn_t rgn,			/* Cache outer attributes */
	bool_t shareable,
	bool_t not_outer_shareable
);

void mmu_map_small_page(
	unsigned int *tt	/* Translation table addr*/
	, void *pa, void *va /* Virtual & Physical addresses */
	, bool_t user		/* PL0 & PL1 accessible */
	, bool_t ro			/* Read only */
	, bool_t xn			/* eXecute never (FIXME: not applied to kernel ? */
	, bool_t device		/* Set memory as shareable device */
	, bool_t global
);

void mmu_map_anysection(
	unsigned int *tt,	/* Translation table addr*/
	void *pa, void *va, /* Virtual & Physical addresses */
	bool_t user,		/* PL0 & PL1 accessible */
	bool_t ro,			/* Read only */
	bool_t xn,			/* eXecute never */
	bool_t device,		/* Set memory as shareable device */
	bool_t global,		/* Mark memory as global  */
	int super
);

#define mmu_map_section(tt, pa, va, user, ro, xn, device, global)	\
	mmu_map_anysection(tt, pa, va, user, ro, xn, device, global, 0)

#define mmu_map_supersection(tt, pa, va, user, ro, xn, device, global)	\
	mmu_map_anysection(tt, pa, va, user, ro, xn, device, global, 1)

void mmu_init(void);
void mmu_debug(unsigned*tt);
mmu_sd_sp_t mmu_virt_to_sp(unsigned pd, unsigned va);
unsigned mmu_virt_to_phys(unsigned pd, unsigned va);
void cache_and_mmu_disable();
void cache_and_mmu_enable();

#endif
