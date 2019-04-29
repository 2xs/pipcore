(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2017)                 *)
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

(**  * Summary 
      The Abstraction Data Type : In this file we define types used by memory Services *)
Require Import List Bool Arith Omega. 
Import List.ListNotations.

(* BEGIN SIMULATION

Definition maxVint := 5.
Definition nbLevel := 2.
Definition tableSize := 12.
Definition nbPage := 100.
Definition contextSize := 5.
Lemma nbLevelNotZero: nbLevel > 0.
Proof. unfold nbLevel; auto. Qed.
Lemma tableSizeNotZero : tableSize <> 0.
Proof. unfold tableSize; auto. Qed.


   END SIMULATION *)

(* BEGIN NOT SIMULATION *)
Axiom tableSize nbLevel nbPage maxVint contextSize : nat.
Axiom nbLevelNotZero: nbLevel > 0.
Axiom nbPageNotZero: nbPage > 0.
Axiom maxVintNotZero: maxVint > 0.
Axiom contextSizeNotZero: contextSize > 0.
Axiom contextSizeLessThanTableSize: contextSize < tableSize.

(* Axiom tableSizeNotZero : tableSize <> 0. *)

Axiom tableSizeIsEven : Nat.Even tableSize.
(* END NOT SIMULATION *)
Definition tableSizeLowerBound := 14.
Axiom tableSizeBigEnough : tableSize > tableSizeLowerBound. (* to be fixed on count **) 
Record index := {
  i :> nat ;
  Hi : i < tableSize }.

Record page := { 
  p :> nat;
  Hp : p < nbPage }.

Definition paddr := (page * index)%type.

Record vaddr := {
  va :> list index ;
  Hva : length va = nbLevel + 1}.

Record level := {
  l :> nat ;
  Hl : l < nbLevel }.

Record count := {
  c :> nat ;
  Hnb : c <= (3*nbLevel) + 1  ;
 }.

Definition userValue := nat.
Definition vint := nat.
Definition contextAddr := nat.

Record interruptMask := {
 m :> list bool;
 Hm : length m = maxVint+1;
}.

Parameter index_d : index.
Parameter page_d : page.
Parameter level_d : level.
Parameter int_mask_d : interruptMask.

Require Import Coq.Program.Tactics.

Program Definition CIndex  (p : nat) : index := 
if (lt_dec p tableSize) then 
Build_index p _ else index_d.


Program Definition CPage (p : nat) : page := 
if (lt_dec p nbPage) then Build_page p _ else  page_d.

Program Definition CVaddr (l: list index) : vaddr := 
if ( Nat.eq_dec (length l)  (nbLevel+1))  
  then Build_vaddr l _
  else Build_vaddr (repeat (CIndex 0) (nbLevel+1)) _.


(* BEGIN NOT SIMULATION *)

Next Obligation.
apply repeat_length.
Qed. 

(* END NOT SIMULATION *)


Program Definition CLevel ( a :nat) : level := 
if lt_dec a nbLevel then Build_level a _ 
else level_d .

Program Definition CIntMask (m : list bool) : interruptMask :=
if Nat.eq_dec (length m) (maxVint+1) then Build_interruptMask m _
else int_mask_d.