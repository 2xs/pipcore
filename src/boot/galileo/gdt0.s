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

; Configuration of the x86 Global Descriptor Table and Task State Segment.

extern gp
global gdtFlush
gdtFlush:
    lgdt [gp] ; Load the GDT
    mov ax, 0x10 ; Set segments to kernel land
    mov ds, ax
    mov es, ax
    mov fs, ax
    mov gs, ax
    mov ss, ax
    jmp 0x08:flush2 ; Far jump to our newly, freshly-created GDT entry
flush2:
    ret ; Get back to business

global tssFlush
tssFlush:
	mov ax, 0x2B
	ltr ax
	ret

%macro CG_GLUE_NOARG 1
extern %1
global cg_%1
cg_%1:
	cli
 	call %1
	sti
	retf
%endmacro

; Callgate stack layout: 
;	usereip
;	cs
;	args, ...
;	useresp
;	ss
%macro CG_GLUE 2
extern %1
global cg_%1
cg_%1:
	cli
; save resume eip:cs
	pop esi
	pop edi
; call pip function
 	call %1
; restore eip:cs
	push edi
	push esi
; back to userland
	sti
	retf (4*%2)
%endmacro

%macro CG_GLUE_CTX 2
extern %1
global cg_%1
cg_%1:
	cli
; push user registers
	pusha
; useresp
	mov eax, dword [0x20+esp+8+4*%2]
; skip call arguments in saved esp
	add eax, 4*%2
; fix useresp in regs
	mov [esp+12], eax
; push &ctx
	push esp
; push callGlue arguments
%rep %2
	push dword [0x24+esp+8+4*(%2-1)]
%endrep
	call %1
	add esp, 0x24+4*%2
; back to userland
	sti
	retf (4*%2)
%endmacro


; These functions might trigger a call to dispatchGlue
; therefore they need a reference to calling context (regs + eip)
; in order to save it if needed
CG_GLUE_CTX outbGlue		, 2
CG_GLUE_CTX inbGlue		, 1
CG_GLUE_CTX outwGlue		, 2
CG_GLUE_CTX inwGlue		, 1
CG_GLUE_CTX outlGlue 		, 2
CG_GLUE_CTX inlGlue 		, 1
CG_GLUE_CTX dispatchGlue	, 5
CG_GLUE_CTX mmioReadGlue    , 3
CG_GLUE_CTX mmioWriteGlue   , 4
CG_GLUE_CTX mmioSetGlue     , 4
CG_GLUE_CTX mmioClearGlue   , 4
CG_GLUE_CTX mmioModifyGlue  , 5
CG_GLUE_CTX writeMMIOGlue 	, 2

CG_GLUE_CTX outaddrlGlue 	, 2

; Those ones won't trigger a fault in caller
CG_GLUE createPartition		, 5
CG_GLUE countToMap		, 2
CG_GLUE prepare			, 4
CG_GLUE addVAddr		, 6
CG_GLUE resume			, 2

CG_GLUE_NOARG  timerGlue
