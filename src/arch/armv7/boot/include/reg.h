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

#ifndef DEF_REG_H_
#define DEF_REG_H_

/* B4.1.89 */
typedef union reg_mmfr0_u {
	unsigned aslong;
	struct {
		unsigned vmsa_support:4;
		unsigned pmsa_support:4;
		unsigned outermost_share:4;
		unsigned share_levels:4;
		unsigned tcm_support:4;
		unsigned aux_registers:4;
		unsigned fcse_support:4;
		unsigned innermost_share:4;
	};
} reg_mmfr0_t;

/* B4.1.42 CTR, Cache Type Register, VMSA */
typedef union reg_ctr_u {
	unsigned aslong;
	struct {
		unsigned IminLine:4;
		unsigned zero1:10;
		unsigned L1Ip:2;
		unsigned DminLine:4;
		unsigned ERG:4;
		unsigned CWG:4;
		unsigned zero2:1;
		unsigned format:3;
	};
} reg_ctr_t;

/* B4.1.20 CLIDR, Cache Level ID Register, VMSA */
typedef union reg_clidr_u {
	unsigned aslong;
	struct {
		unsigned Ctype1:3;
		unsigned Ctype2:3;
		unsigned Ctype3:3;
		unsigned Ctype4:3;
		unsigned Ctype5:3;
		unsigned Ctype6:3;
		unsigned Ctype7:3;
		unsigned LoUIS:3;
		unsigned LoC:3;
		unsigned LoUU:3;
	};
} reg_clidr_t;

/* B4.1.19 CCSIDR, Cache Size ID Registers, VMSA */
typedef union reg_csidr_u {
	unsigned aslong;
	struct {
		unsigned LineSize:3;
		unsigned Associativity:10;
		unsigned NumSets:15;
		unsigned WA:1;
		unsigned RA:1;
		unsigned WB:1;
		unsigned WT:1;
	};
} reg_csidr_t;

/* B4.1.153 TTBCR, Translation Table Base Control Register,
	VMSA, Short format (implies that EAE = 0) */
typedef union reg_ttbcr_u {
	unsigned aslong;
	struct {
		unsigned N:3;		/* With of TTBR0 */
		unsigned zero:1;
		unsigned PD0:1;		/* Only when security extensions */
		unsigned PD1:1;		/* Only when security extensions */
		unsigned reserved:25;
		unsigned EAE:1;		/* Must be zero*/
	};
} reg_ttbcr_t;

/* B4.1.105 MIDR, Main ID Register, VMSA */
typedef union reg_midr_u {
	unsigned aslong;
	struct {
		unsigned revision:4;
		unsigned part_number:12;
		unsigned architecture:4;
		unsigned variant:4;
		unsigned implementor:8;
	};
} reg_midr_t;

#endif
