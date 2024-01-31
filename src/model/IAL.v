(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2024)                *)
(*                                                                             *)
(*  This software is a computer program whose purpose is to run a minimal,     *)
(*  hypervisor relying on proven properties such as memory isolation.          *)
(*                                                                             *)
(*  This software is governed by the CeCILL license under French law and       *)
(*  abiding by the rules of distribution of free software.  You can  use,      *)
(*  modify and/ or redistribute the software under the terms of the CeCILL     *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL          *)
(*  "http://www.cecill.info".                                                  *)
(*                                                                             *)
(*  As a counterpart to the access to the source code and  rights to copy,     *)
(*  modify and redistribute granted by the license, users are provided only    *)
(*  with a limited warranty  and the software's author,  the holder of the     *)
(*  economic rights,  and the successive licensors  have only  limited         *)
(*  liability.                                                                 *)
(*                                                                             *)
(*  In this respect, the user's attention is drawn to the risks associated     *)
(*  with loading,  using,  modifying and/or developing or reproducing the      *)
(*  software by the user in light of its specific status of free software,     *)
(*  that may mean  that it is complicated to manipulate,  and  that  also      *)
(*  therefore means  that it is reserved for developers  and  experienced      *)
(*  professionals having in-depth computer knowledge. Users are therefore      *)
(*  encouraged to load and test the software's suitability as regards their    *)
(*  requirements in conditions enabling the security of their systems and/or   *)
(*  data to be ensured and,  more generally, to use and operate it in the      *)
(*  same conditions as regards security.                                       *)
(*                                                                             *)
(*  The fact that you are presently reading this means that you have had       *)
(*  knowledge of the CeCILL license and that you accept its terms.             *)
(*******************************************************************************)

Require Import Pip.Model.ADT Pip.Model.Lib Pip.Model.Hardware Pip.Model.Constants Pip.Model.Ops Pip.Model.MAL.
Require Import Bool Arith List.
Import List.ListNotations.

Module Vint.
Definition ltb (a b : vint) : LLI bool := ret (a <? b).
End Vint.

(** The 'getMaxVint' function returns the maximum interruption level *)
Definition getMaxVint : LLI vint:=
  ret maxVint.

Definition checkIndexPropertyLTB (userIndex : userValue) : LLI bool :=
  ret (Nat.ltb userIndex tableSize).

Definition checkVidtIndex (saveIndex : index) : LLI bool :=
  (* perform maxVint := getMaxVint in *)
  ret (saveIndex <=? maxVint).


Program Definition userValueToIndex (userIndex : userValue) : LLI index :=
  if lt_dec userIndex tableSize
  then
    ret (Build_index userIndex _ )
  else undefined 85.

(* Use readVirtualUser *)
(* Definition readUserlandVAddr (paddr : page) (idx : index)  : LLI vaddr :=
  perform s := get in
  let entry :=  lookup paddr idx s.(memory) beqPage beqIndex  in
  match entry with
  | Some (VA a) => ret a
  | _ => ret defaultVAddr
  end. *)

Definition FAIL_INVALID_INT_LEVEL := FAIL_INVALID_INT_LEVEL_Cons.
Definition FAIL_INVALID_CTX_SAVE_INDEX := FAIL_INVALID_CTX_SAVE_INDEX_Cons.
Definition FAIL_CALLER_CONTEXT_SAVE := FAIL_CALLER_CONTEXT_SAVE_Cons.
Definition FAIL_UNAVAILABLE_TARGET_VIDT := FAIL_UNAVAILABLE_TARGET_VIDT_Cons.
Definition FAIL_UNAVAILABLE_TARGET_CTX := FAIL_UNAVAILABLE_TARGET_CTX_Cons.
Definition FAIL_UNAVAILABLE_CALLER_VIDT := FAIL_UNAVAILABLE_CALLER_VIDT_Cons.
Definition FAIL_ROOT_CALLER := FAIL_ROOT_CALLER_Cons.
Definition FAIL_INVALID_CHILD := FAIL_INVALID_CHILD_Cons.
Definition FAIL_MASKED_INTERRUPT := FAIL_MASKED_INTERRUPT_Cons.
Definition SUCCESS := SUCCESS_Cons.

Definition loadContext (contextToLoad : contextAddr) (enforce_interrupt : bool) : LLI unit :=
  ret tt.

Definition contextSizeMinusOne := contextSize-1.

Definition setInterruptMask (mask : interruptMask) : LLI unit :=
  ret tt.

Definition readInterruptMask (childVidt : page) : LLI interruptMask :=
  ret int_mask_d.

Definition isInterruptMasked (intMask : interruptMask) (interrupt : vint) : LLI bool :=
  ret false.

Definition vaddrToContextAddr (va : vaddr) : LLI contextAddr :=
  ret 0.

Definition writeContext (callingContextAddr : contextAddr) (contextSaveAddr : vaddr) (flagsOnWake : interruptMask)
          : LLI unit := ret tt.

Definition updateMMURoot(pageDir : page)
          : LLI unit := ret tt.

Definition getNthVAddrFrom (start : vaddr) (range : nat) : LLI vaddr :=
  ret (getNthVAddrFromAux start range).

Definition getInterruptMaskFromCtx (context : contextAddr) : LLI interruptMask :=
  ret int_mask_d.

Definition noInterruptRequest (flags : interruptMask) : LLI bool :=
  ret true.

Program Definition firstVAddrGreaterThanSecond (first second : vaddr) : LLI bool :=
  ret (firstVAddrGreaterThanSecondAux first second _).
Next Obligation.
rewrite (ADT.Hva first ).
rewrite (ADT.Hva second).
reflexivity.
Qed.
