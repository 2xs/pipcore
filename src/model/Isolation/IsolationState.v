From Pip.Model.Meta Require Import StateModel.
From Pip.Model.Isolation Require Import IsolationTypes.

(* Require Import Coq.Strings.String Lia NPeano. *)
(* Require Import Arith Bool List. *)
(* Import List.ListNotations. *)

Module IsolationState <: StateModel.
Export IsolationTypes.

  Record Pentry : Type:=
  {
    read    : bool;
    write   : bool;
    exec    : bool;
    present : bool;
    user    : bool;
    pa      : page
  }.

  Record Ventry : Type:=
  {
    pd : bool;
    va : vaddr
  }.

  Inductive value : Type := 
  |PE : Pentry -> value
  |VE : Ventry -> value
  |PP : page -> value
  |VA : vaddr -> value
  |I  : index -> value
  |U  : userValue -> value.

  Record IsolationState : Type := {
    currentPartition : page;
    memory : list (paddr * value)
  }.

  Definition state := IsolationState.

End IsolationState.