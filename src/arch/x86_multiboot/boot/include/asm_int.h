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

#ifndef ASM_INT_H
#define ASM_INT_H

/**
 * \brief Type of callback functions (IRQ handlers)
 * No return value, and no arguments
 */
typedef void (*callback_t)(void);


extern void fault_DE_asm(void);
extern void fault_DB_asm(void);
extern void fault_NMI_asm(void);
extern void fault_BP_asm(void);
extern void fault_OF_asm(void);
extern void fault_BR_asm(void);
extern void fault_UD_asm(void);
extern void fault_NM_asm(void);
extern void fault_DF_asm(void);
extern void fault_CSO_asm(void);
extern void fault_TS_asm(void);
extern void fault_NP_asm(void);
extern void fault_SS_asm(void);
extern void fault_GP_asm(void);
extern void fault_PF_asm(void);
extern void fault_RES_asm(void);
extern void fault_MF_asm(void);
extern void fault_AC_asm(void);
extern void fault_MC_asm(void);
extern void fault_XM_asm(void);
extern void fault_VE_asm(void);
extern void fault_RES_asm(void);
extern void fault_RES_asm(void);
extern void fault_RES_asm(void);
extern void fault_RES_asm(void);
extern void fault_RES_asm(void);
extern void fault_RES_asm(void);
extern void fault_RES_asm(void);
extern void fault_RES_asm(void);
extern void fault_RES_asm(void);
extern void fault_RES_asm(void);
extern void fault_RES_asm(void);
extern void hardware_ALRM_asm(void);
extern void hardware_KEYB_asm(void);
extern void hardware_CASC_asm(void);
extern void hardware_COM2_asm(void);
extern void hardware_COM1_asm(void);
extern void hardware_LPT2_asm(void);
extern void hardware_FLPD_asm(void);
extern void hardware_SPUR_asm(void);
extern void hardware_RTC_asm(void);
extern void hardware_PER1_asm(void);
extern void hardware_PER2_asm(void);
extern void hardware_PER3_asm(void);
extern void hardware_PS2M_asm(void);
extern void hardware_FPU_asm(void);
extern void hardware_PHD_asm(void);
extern void hardware_SHD_asm(void);
extern void software_48_asm(void);
extern void software_49_asm(void);
extern void software_50_asm(void);
extern void software_51_asm(void);
extern void software_52_asm(void);
extern void software_53_asm(void);
extern void software_54_asm(void);
extern void software_55_asm(void);
extern void software_56_asm(void);
extern void software_57_asm(void);
extern void software_58_asm(void);
extern void software_59_asm(void);
extern void software_60_asm(void);
extern void software_61_asm(void);
extern void software_62_asm(void);
extern void software_63_asm(void);
extern void software_64_asm(void);
extern void software_65_asm(void);
extern void software_66_asm(void);
extern void software_67_asm(void);
extern void software_68_asm(void);
extern void software_69_asm(void);
extern void software_70_asm(void);
extern void software_71_asm(void);
extern void software_72_asm(void);
extern void software_73_asm(void);
extern void software_74_asm(void);
extern void software_75_asm(void);
extern void software_76_asm(void);
extern void software_77_asm(void);
extern void software_78_asm(void);
extern void software_79_asm(void);
extern void software_80_asm(void);
extern void software_81_asm(void);
extern void software_82_asm(void);
extern void software_83_asm(void);
extern void software_84_asm(void);
extern void software_85_asm(void);
extern void software_86_asm(void);
extern void software_87_asm(void);
extern void software_88_asm(void);
extern void software_89_asm(void);
extern void software_90_asm(void);
extern void software_91_asm(void);
extern void software_92_asm(void);
extern void software_93_asm(void);
extern void software_94_asm(void);
extern void software_95_asm(void);
extern void software_96_asm(void);
extern void software_97_asm(void);
extern void software_98_asm(void);
extern void software_99_asm(void);
extern void software_100_asm(void);
extern void software_101_asm(void);
extern void software_102_asm(void);
extern void software_103_asm(void);
extern void software_104_asm(void);
extern void software_105_asm(void);
extern void software_106_asm(void);
extern void software_107_asm(void);
extern void software_108_asm(void);
extern void software_109_asm(void);
extern void software_110_asm(void);
extern void software_111_asm(void);
extern void software_112_asm(void);
extern void software_113_asm(void);
extern void software_114_asm(void);
extern void software_115_asm(void);
extern void software_116_asm(void);
extern void software_117_asm(void);
extern void software_118_asm(void);
extern void software_119_asm(void);
extern void software_120_asm(void);
extern void software_121_asm(void);
extern void software_122_asm(void);
extern void software_123_asm(void);
extern void software_124_asm(void);
extern void software_125_asm(void);
extern void software_126_asm(void);
extern void software_127_asm(void);
extern void software_128_asm(void);
extern void software_129_asm(void);
extern void software_130_asm(void);
extern void software_131_asm(void);
extern void software_132_asm(void);
extern void software_133_asm(void);
extern void software_134_asm(void);
extern void software_135_asm(void);
extern void software_136_asm(void);
extern void software_137_asm(void);
extern void software_138_asm(void);
extern void software_139_asm(void);
extern void software_140_asm(void);
extern void software_141_asm(void);
extern void software_142_asm(void);
extern void software_143_asm(void);
extern void software_144_asm(void);
extern void software_145_asm(void);
extern void software_146_asm(void);
extern void software_147_asm(void);
extern void software_148_asm(void);
extern void software_149_asm(void);
extern void software_150_asm(void);
extern void software_151_asm(void);
extern void software_152_asm(void);
extern void software_153_asm(void);
extern void software_154_asm(void);
extern void software_155_asm(void);
extern void software_156_asm(void);
extern void software_157_asm(void);
extern void software_158_asm(void);
extern void software_159_asm(void);
extern void software_160_asm(void);
extern void software_161_asm(void);
extern void software_162_asm(void);
extern void software_163_asm(void);
extern void software_164_asm(void);
extern void software_165_asm(void);
extern void software_166_asm(void);
extern void software_167_asm(void);
extern void software_168_asm(void);
extern void software_169_asm(void);
extern void software_170_asm(void);
extern void software_171_asm(void);
extern void software_172_asm(void);
extern void software_173_asm(void);
extern void software_174_asm(void);
extern void software_175_asm(void);
extern void software_176_asm(void);
extern void software_177_asm(void);
extern void software_178_asm(void);
extern void software_179_asm(void);
extern void software_180_asm(void);
extern void software_181_asm(void);
extern void software_182_asm(void);
extern void software_183_asm(void);
extern void software_184_asm(void);
extern void software_185_asm(void);
extern void software_186_asm(void);
extern void software_187_asm(void);
extern void software_188_asm(void);
extern void software_189_asm(void);
extern void software_190_asm(void);
extern void software_191_asm(void);
extern void software_192_asm(void);
extern void software_193_asm(void);
extern void software_194_asm(void);
extern void software_195_asm(void);
extern void software_196_asm(void);
extern void software_197_asm(void);
extern void software_198_asm(void);
extern void software_199_asm(void);
extern void software_200_asm(void);
extern void software_201_asm(void);
extern void software_202_asm(void);
extern void software_203_asm(void);
extern void software_204_asm(void);
extern void software_205_asm(void);
extern void software_206_asm(void);
extern void software_207_asm(void);
extern void software_208_asm(void);
extern void software_209_asm(void);
extern void software_210_asm(void);
extern void software_211_asm(void);
extern void software_212_asm(void);
extern void software_213_asm(void);
extern void software_214_asm(void);
extern void software_215_asm(void);
extern void software_216_asm(void);
extern void software_217_asm(void);
extern void software_218_asm(void);
extern void software_219_asm(void);
extern void software_220_asm(void);
extern void software_221_asm(void);
extern void software_222_asm(void);
extern void software_223_asm(void);
extern void software_224_asm(void);
extern void software_225_asm(void);
extern void software_226_asm(void);
extern void software_227_asm(void);
extern void software_228_asm(void);
extern void software_229_asm(void);
extern void software_230_asm(void);
extern void software_231_asm(void);
extern void software_232_asm(void);
extern void software_233_asm(void);
extern void software_234_asm(void);
extern void software_235_asm(void);
extern void software_236_asm(void);
extern void software_237_asm(void);
extern void software_238_asm(void);
extern void software_239_asm(void);
extern void software_240_asm(void);
extern void software_241_asm(void);
extern void software_242_asm(void);
extern void software_243_asm(void);
extern void software_244_asm(void);
extern void software_245_asm(void);
extern void software_246_asm(void);
extern void software_247_asm(void);
extern void software_248_asm(void);
extern void software_249_asm(void);
extern void software_250_asm(void);
extern void software_251_asm(void);
extern void software_252_asm(void);
extern void software_253_asm(void);
extern void software_254_asm(void);
extern void software_255_asm(void);

#endif
