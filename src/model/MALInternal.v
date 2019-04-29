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

(** * Summary 
    This file contains the definition of some constants and its monadic getters;
    and the module definition of each abstract data type in which we define required
    monadic functions  *)
Require Import Model.ADT Model.Hardware Model.Lib. 
Require Import List Arith Omega.

(** Define some constants *)
(** default values *)
Definition defaultIndex := CIndex 0.
Definition defaultVAddr := CVaddr (repeat (CIndex 0) (nbLevel+1)).
Definition lastVAddr := CVaddr (repeat (CIndex (tableSize - 1)) (nbLevel+1)).
Definition vidtVAddr := CVaddr ((repeat (CIndex (tableSize - 1)) (nbLevel))++((CIndex 0)::nil)).
Definition defaultPage := CPage 0.

(** Define first level number *)
Definition fstLevel :=  CLevel 0.

(** Define the second parameter value of store and fetch *) 
Definition storeFetchIndex := CIndex 0.

(** Define the entry position of the kernel mapping into the first indirection 
    of partitions *)
Definition Kidx := CIndex 1.

Definition multiplexer := CPage 1.

(** Fix virtual addresses positions into the partition descriptor
    of the partition (+1 to get the physical page position) *)
Definition PRidx := CIndex 0.   (* descriptor *)
Definition PDidx := CIndex 2.   (* page directory *)
Definition sh1idx := CIndex 4.  (* shadow1 *) 
Definition sh2idx := CIndex 6.  (* shadow2 *)
Definition sh3idx := CIndex 8.  (* configuration pages list*)
Definition PPRidx := CIndex 10. (* parent (virtual address is null) *)

(** Define getter for each constant *)
Definition getDefaultVAddr :=  ret defaultVAddr.
Definition getDefaultPage := ret defaultPage.
Definition getVidtVAddr := ret vidtVAddr.
Definition getLastVAddr := ret lastVAddr.
Definition getKidx : LLI index:= ret Kidx.
Definition getPRidx : LLI index:= ret PRidx.
Definition getPDidx : LLI index:= ret PDidx.
Definition getSh1idx : LLI index:= ret sh1idx.
Definition getSh2idx : LLI index:= ret sh2idx.
Definition getSh3idx : LLI index:= ret sh3idx.
Definition getPPRidx : LLI index:= ret PPRidx.
Definition getStoreFetchIndex : LLI index := ret storeFetchIndex.
Definition getMultiplexer : LLI page := ret multiplexer.

Definition beqIndex (a b : index) : bool := a =? b.
Definition beqPage (a b : page) : bool := a =? b.
Definition beqVAddr (a b : vaddr) : bool := eqList a b beqIndex.

Module Index.
Definition geb (a b : index) : LLI bool := ret (b <=? a).
Definition leb (a b : index) : LLI bool := ret (a <=? b).
Definition ltb (a b : index) : LLI bool := ret (a <? b).
Definition gtb (a b : index) : LLI bool := ret (b <? a).
Definition eqb (a b : index) : LLI bool := ret (a =? b). 
Program Definition zero : LLI index:= ret (Build_index 0 _).
Next Obligation.
assert (tableSize > 14).
apply tableSizeBigEnough.
omega.
Qed.

Program Definition pred (n : index) : LLI index :=
let (i,P) := n in
if gt_dec i 0
then
  let ipred := i-1 in
  ret ( Build_index ipred _)
else  undefined 27.
Next Obligation.
omega.
Qed.

Program Definition succ (n : index) : LLI index :=
(* let (i,P) := n in*)
let isucc := n+1 in
if (lt_dec isucc tableSize )
then
  ret (Build_index isucc _ )
else  undefined 28.
(* Next Obligation.
  omega.
Qed.
 *)
End Index. 

Module Page.
Definition eqb (p1 : page)  (p2 : page) : LLI bool := ret (p1 =? p2).
End Page.

Module Level.
Program Definition pred (n : level) : LLI level :=
if gt_dec n 0
then
  let ipred := n-1 in
  ret (Build_level ipred _ )
else  undefined 30.
Next Obligation.
destruct n;simpl;omega.
Qed.

Program Definition succ (n : level) : LLI level :=
let isucc := n+1 in
if lt_dec isucc nbLevel
then
  ret (Build_level isucc _ )
else  undefined 31.
Definition gtb (a b : level) : LLI bool := ret (b <? a).
Definition eqb (a b : level) : LLI bool:= ret (a =? b).
End Level.

Module VAddr.
Definition eqbList(vaddr1 : vaddr) (vaddr2 : vaddr) : LLI bool :=
  ret (beqVAddr vaddr1 vaddr2).
End VAddr.

Module Count.
Program Definition mul3 (a : level) : LLI count :=
ret (Build_count (a * 3) _).
Next Obligation.
destruct a; simpl.
(* BEGIN SIMULATION
  unfold nbLevel in Hl.
   END SIMULATION *)
omega.
Qed.
Definition geb (a b : count) : LLI bool := ret (b <=? a).
Program Definition zero : LLI count :=  ret (Build_count 0 _).
Next Obligation.
omega.
Qed.
Program Definition succ (n : count) : LLI count :=
let isucc := n+1 in
if le_dec isucc ((3*nbLevel) + 1)
then
  ret (Build_count isucc _ )
else  undefined 34.
End Count.
