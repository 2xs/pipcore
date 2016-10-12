;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;  © Université Lille 1, The Pip Development Team (2015-2016)                 ;
;                                                                             ;
;  This software is a computer program whose purpose is to run a minimal,     ;
;  hypervisor relying on proven properties such as memory isolation.          ;
;                                                                             ;
;  This software is governed by the CeCILL license under French law and       ;
;  abiding by the rules of distribution of free software.  You can  use,      ;
;  modify and/ or redistribute the software under the terms of the CeCILL     ;
;  license as circulated by CEA, CNRS and INRIA at the following URL          ;
;  "http://www.cecill.info".                                                  ;
;                                                                             ;
;  As a counterpart to the access to the source code and  rights to copy,     ;
;  modify and redistribute granted by the license, users are provided only    ;
;  with a limited warranty  and the software's author,  the holder of the     ;
;  economic rights,  and the successive licensors  have only  limited         ;
;  liability.                                                                 ;
;                                                                             ;
;  In this respect, the user's attention is drawn to the risks associated     ;
;  with loading,  using,  modifying and/or developing or reproducing the      ;
;  software by the user in light of its specific status of free software,     ;
;  that may mean  that it is complicated to manipulate,  and  that  also      ;
;  therefore means  that it is reserved for developers  and  experienced      ;
;  professionals having in-depth computer knowledge. Users are therefore      ;
;  encouraged to load and test the software's suitability as regards their    ;
;  requirements in conditions enabling the security of their systems and/or   ;
;  data to be ensured and,  more generally, to use and operate it in the      ;
;  same conditions as regards security.                                       ;
;                                                                             ;
;  The fact that you are presently reading this means that you have had       ;
;  knowledge of the CeCILL license and that you accept its terms.             ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Multiboot header.
; /**
; * \file boot0.s
; * \brief Assembly entrypoint.
; */
MBOOT_PAGE_ALIGN    equ 1<<0
MBOOT_MEM_INFO      equ 1<<1
MBOOT_HEADER_MAGIC  equ 0x1BADB002
MBOOT_HEADER_FLAGS  equ MBOOT_PAGE_ALIGN | MBOOT_MEM_INFO
MBOOT_CHECKSUM      equ -(MBOOT_HEADER_MAGIC + MBOOT_HEADER_FLAGS)

; 64 bits is WAYS too mainstream
[BITS 32]

; Multiboot header stuff
[GLOBAL mboot]
[EXTERN code]
[EXTERN bss]
[EXTERN end]

mboot:
  dd  MBOOT_HEADER_MAGIC
  dd  MBOOT_HEADER_FLAGS
  dd  MBOOT_CHECKSUM
  dd  mboot
  dd  code
  dd  bss
  dd  end
  dd  start

SECTION .text
[GLOBAL start]
[EXTERN c_main]

; Kernel entrypoint, setup stack, push multiboot header pointer, clear interrupts and jump to the C entrypoint
start:
	cli
	mov esp, _sys_stack
	push ebx
    push 0x1BADB002
	call c_main
	jmp $

; Early-boot kernel stack
SECTION .krnstack
	times 262144 db 0
	; Allocate 256kb for the stack
_sys_stack:
