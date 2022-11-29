Require Import List Arith.
Require Import Coq.Program.Tactics.

From Pip.Model.Meta Require Import TypesModel.

Module IsolationTypes <: TypesModel.

  (* Types *)
  Parameter tableSize : nat.
  Parameter nbPage : nat.
  Parameter nbLevel : nat.
  Parameter maxVint : nat.

  Record index_s := {
    i :> nat ;
    Hi : i < tableSize
  }.

  Definition index := index_s.

  Record page_s := { 
    p :> nat;
    Hp : p < nbPage
  }.

  Definition page := page_s.

  Definition paddr := (page * index)%type.

  Record vaddr_s := {
    va :> list index ;
    Hva : length va = nbLevel + 1
  }.

  Definition vaddr := vaddr_s.

  Record level_s := {
    l :> nat ;
    Hl : l < nbLevel
  }.

  Definition level := level_s.

  Record count_s := {
    c :> nat ;
    Hnb : c <= (3*nbLevel) + 1;
  }.

  Definition count := count_s.

  Record boolvaddr_s := {
    success : bool;
    FFvaddr : vaddr;
  }.

  Definition boolvaddr := boolvaddr_s.

  Definition userValue := nat.
  Definition vint := nat.
  Definition contextAddr := nat.

  Record interruptMask_s := {
    m :> list bool;
    Hm : length m = maxVint+1;
  }.

  Definition interruptMask := interruptMask_s.

  Parameter index_d : index.
  Parameter page_d : page.
  Parameter level_d : level.
  Parameter count_d : count.
  Parameter int_mask_d : interruptMask.

  Program Definition CIndex  (p : nat) : index :=
    if (lt_dec p tableSize) then
      Build_index_s p _ else index_d.

  Program Definition CPage (p : nat) : page :=
    if (lt_dec p nbPage) then
      Build_page_s p _ else page_d.

  Program Definition CVaddr (l: list index) : vaddr := 
    if (Nat.eq_dec (length l) (nbLevel+1))
      then Build_vaddr_s l _
    else
      Build_vaddr_s (repeat (CIndex 0) (nbLevel+1)) _.

  Next Obligation.
  apply repeat_length.
  Qed.

  Program Definition CLevel ( a :nat) : level := 
    if lt_dec a nbLevel then
      Build_level_s a _
    else level_d .

  Program Definition CCount ( a :nat) : count := 
    if le_dec a ((3*nbLevel) + 1) then
      Build_count_s a _
    else count_d .

  Program Definition CIntMask (m : list bool) : interruptMask :=
    if Nat.eq_dec (length m) (maxVint+1) then
      Build_interruptMask_s m _
    else int_mask_d.

Inductive yield_checks : Type :=
| FAIL_INVALID_INT_LEVEL
| FAIL_INVALID_CTX_SAVE_INDEX
| FAIL_CALLER_CONTEXT_SAVE
| FAIL_UNAVAILABLE_TARGET_VIDT
| FAIL_UNAVAILABLE_TARGET_CTX
| FAIL_UNAVAILABLE_CALLER_VIDT
| FAIL_ROOT_CALLER
| FAIL_INVALID_CHILD
| FAIL_MASKED_INTERRUPT
| SUCCESS.

End IsolationTypes.