Require Import Model.ADT Model.Lib Model.Hardware Bool Arith List Model.MALInternal Model.MAL.
Import List.ListNotations.

Module Vint.
Definition ltb (a b : vint) : LLI bool := ret (a <? b).
End Vint.

(** The 'getMaxVint' function returns the maximum interruption level *)
Definition getMaxVint : LLI vint:=
  ret maxVint.

Definition checkVint (interruption : vint) : LLI bool :=
  (* perform maxVint := getMaxVint in *)
  ret (interruption <=? maxVint).

Definition checkVidtIndex (saveIndex : index) : LLI bool :=
  (* perform maxVint := getMaxVint in *)
  ret (saveIndex <=? maxVint).

Definition checkCtxSaveIndex (ctxSaveIndex : userValue) : LLI bool :=
  ret (Nat.ltb ctxSaveIndex tableSize).

Definition getIndexFromUserValue (userIndex : userValue) : LLI index :=
  ret (CIndex userIndex).


Definition readUserData (paddr : page) ( idx : index)  : LLI vaddr :=
  perform s := get in
  let entry :=  lookup paddr idx s.(memory) beqPage beqIndex  in
  match entry with
  | Some (VA a) => ret a
  | Some _ => ret defaultVAddr
  | None => ret defaultVAddr
  end.

Definition FAIL_VINT := FAIL_VINT_Cons.
Definition FAIL_CTX_SAVE_INDEX := FAIL_CTX_SAVE_INDEX_Cons.
Definition FAIL_CTX_SAVE_ADDR := FAIL_CTX_SAVE_ADDR_Cons.
Definition FAIL_TARGET_VIDT := FAIL_TARGET_VIDT_Cons.
Definition FAIL_TARGET_CTX := FAIL_TARGET_CTX_Cons.
Definition FAIL_CALLER_VIDT := FAIL_CALLER_VIDT_Cons.
Definition FAIL_ROOT_CALLER := FAIL_ROOT_CALLER_Cons.
Definition FAIL_INVALID_CHILD := FAIL_INVALID_CHILD_Cons.
Definition FAIL_MASKED_INTERRUPT := FAIL_MASKED_INTERRUPT_Cons.
Definition SUCCESS := SUCCESS_Cons.

Definition contextSizeMinusOne := contextSize-1.

Definition setInterruptionMask (vidt : page) (mask : interruptionMask) : LLI unit :=
  ret tt.

Definition readInterruptionMask (childVidt : page) : LLI interruptionMask :=
  ret int_mask_d.

Definition isInterruptionMasked (interruptionMask : interruptionMask) (interruption : vint) : LLI bool :=
  ret false.

Definition saveCallerContext (callingContextAddr : contextAddr) (contextSaveAddr : vaddr)
                             (contextSaveIndex : index) (flagsOnWake : interruptionMask)
          : LLI unit := ret tt.

Definition updateCurPartAndActivate(partDesc pageDir : page)
          : LLI unit := activate partDesc;; ret tt.


Fixpoint getNextVaddrAux (indexList : list index) : LLI (bool * (list index)) :=
match indexList with
| nil   =>  ret (true, nil)
| h::t  =>  perform recursiveCall := getNextVaddrAux t in
            if (fst recursiveCall) then
              if (Nat.eq_dec (h+1) tableSize) then
                ret (true, (CIndex 0)::(snd recursiveCall))
              else
                ret (false, (CIndex (h+1)::(snd recursiveCall)))
            else
                ret (false, CIndex h::(snd recursiveCall))
end.

Definition getNextVaddr (va : vaddr) :=
perform auxRes := getNextVaddrAux va in
ret (CVaddr (snd auxRes)).

Fixpoint getNthVAddrFrom (start : vaddr) (range : nat) : LLI vaddr :=
match range with
| 0   => ret start
| S n => perform nextVAddr := getNextVaddr start in
         getNthVAddrFrom nextVAddr n
end.


Fixpoint firstVAddrGreaterThanSecondAux (firstIndexList secondIndexList : list index) : LLI bool :=
  match (firstIndexList, secondIndexList) with
  | (nil, nil) => ret true
  | (hf::tf, hs::ts) => perform trueOnTail := firstVAddrGreaterThanSecondAux tf ts in
                        if (trueOnTail) then
                          ret (Nat.leb hs hf)
                        else
                          ret false
  | (_, _) => undefined 34
  end.

Definition firstVAddrGreaterThanSecond (first second : vaddr) : LLI bool :=
  perform res := firstVAddrGreaterThanSecondAux first second in
  ret res.