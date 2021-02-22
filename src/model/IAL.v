Require Import Model.ADT Model.Lib Model.Hardware Bool Arith List Model.MALInternal Model.MAL.
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

Definition FAIL_VINT := FAIL_VINT_Cons.
Definition FAIL_CTX_SAVE_INDEX := FAIL_CTX_SAVE_INDEX_Cons.
Definition FAIL_CALLER_CONTEXT_SAVE := FAIL_CALLER_CONTEXT_SAVE_Cons.
Definition FAIL_TARGET_VIDT := FAIL_TARGET_VIDT_Cons.
Definition FAIL_TARGET_CTX := FAIL_TARGET_CTX_Cons.
Definition FAIL_UNAVAILABLE_CALLER_VIDT := FAIL_UNAVAILABLE_CALLER_VIDT_Cons.
Definition FAIL_ROOT_CALLER := FAIL_ROOT_CALLER_Cons.
Definition FAIL_INVALID_CHILD := FAIL_INVALID_CHILD_Cons.
Definition FAIL_MASKED_INTERRUPT := FAIL_MASKED_INTERRUPT_Cons.
Definition SUCCESS := SUCCESS_Cons.

Definition loadContext (contextToLoad : contextAddr ) : LLI unit :=
  ret tt.

Definition contextSizeMinusOne := contextSize-1.

Definition setInterruptMask (vidt : page) (mask : interruptMask) : LLI unit :=
  ret tt.

Definition readInterruptMask (childVidt : page) : LLI interruptMask :=
  ret int_mask_d.

Definition isInterruptMasked (intMask : interruptMask) (interrupt : vint) : LLI bool :=
  ret false.

Definition vaddrToContextAddr (va : vaddr) : LLI contextAddr :=
  ret 0.

Definition writeContext (callingContextAddr : contextAddr) (contextSaveAddr : vaddr) (flagsOnWake : interruptMask)
          : LLI unit := ret tt.

Definition updateCR3(pageDir : page)
          : LLI unit := ret tt.

Definition updateCurPartAndActivate(partDesc pageDir : page)
          : LLI unit := activate partDesc;; updateCR3 pageDir.

Definition getNthVAddrFrom (start : vaddr) (range : nat) : LLI vaddr :=
  ret (getNthVAddrFromAux start range).

Program Definition firstVAddrGreaterThanSecond (first second : vaddr) : LLI bool :=
  ret (firstVAddrGreaterThanSecondAux first second _).
Next Obligation.
rewrite (ADT.Hva first ).
rewrite (ADT.Hva second).
reflexivity.
Qed.