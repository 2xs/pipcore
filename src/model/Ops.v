(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2021)                *)
(*                                                                             *)
(*  This software is x computer program whose purpose is to run x minimal,     *)
(*  hypervisor relying on proven properties such as memory isolation.          *)
(*                                                                             *)
(*  This software is governed by the CeCILL license under French law and       *)
(*  abiding by the rules of distribution of free software.  You can  use,      *)
(*  modify and/ or redistribute the software under the terms of the CeCILL     *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL          *)
(*  "http://www.cecill.info".                                                  *)
(*                                                                             *)
(*  As x counterpart to the access to the source code and  rights to copy,     *)
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
    This module defines operations (both pure and monadic) on pip data types *)

Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib.
Require Import List Arith Lia.

Definition idxEq (x y : index) : bool := x =? y.
Definition idxGe (x y : index) : bool := y <=? x.
Definition idxGt (x y : index) : bool := y <? x.
Definition idxLe (x y : index) : bool := x <=? y.
Definition idxLt (x y : index) : bool := x <? y.

Notation idxEqM x y := (ret (idxEq x y)) (only parsing).
Notation idxGeM x y := (ret (idxGe x y)) (only parsing).
Notation idxGtM x y := (ret (idxGt x y)) (only parsing).
Notation idxLeM x y := (ret (idxLe x y)) (only parsing).
Notation idxLtM x y := (ret (idxLt x y)) (only parsing).

Program Definition idxPredM (n : index) : LLI index :=
  let (i,P) := n in
  if gt_dec i 0
  then let ipred := i-1 in
       ret (Build_index ipred _)
  else undefined 27.
Next Obligation. lia. Qed.

Program Definition idxSuccM (n : index) : LLI index :=
  let isucc := n+1 in
  if lt_dec isucc tableSize
  then ret (Build_index isucc _)
  else undefined 28.

Definition vaddrEq (x y : vaddr) : bool := eqList x y idxEq.
Notation vaddrEqM x y := (ret (vaddrEq x y)) (only parsing).

Definition pageEq (x y : page) : bool := x =? y.
Notation pageEqM x y := (ret (pageEq x y)) (only parsing).

Definition levelEq (x y : level) : bool := x =? y.
Definition levelGt (x y : level) : bool := y <? x.

Notation levelEqM x y := (ret (levelEq x y)) (only parsing).
Notation levelGtM x y := (ret (levelGt x y)) (only parsing).

Program Definition levelPredM (n : level) : LLI level :=
  if gt_dec n 0
  then let ipred := n-1 in
       ret (Build_level ipred _)
  else undefined 30.
Next Obligation.
destruct n; simpl; lia.
Qed.

Program Definition levelSuccM (n : level) : LLI level :=
  let isucc := n+1 in
  if lt_dec isucc nbLevel
  then ret (Build_level isucc _)
  else undefined 31.

Definition countEq (x y : count) : bool := x =? y.
Definition countGe (x y : count) : bool := y <=? x.

Notation countEqM x y := (ret (countEq x y)) (only parsing).
Notation countGeM x y := (ret (countGe x y)) (only parsing).

Program Definition countSuccM (n : count) : LLI count :=
  let isucc := n+1 in
  if le_dec isucc (3 * nbLevel + 1)
  then ret (Build_count isucc _)
  else undefined 34.

Program Definition countFromLevelM (x : level) : LLI count :=
  ret (Build_count (x * 3) _).
Next Obligation.
  destruct x; simpl.
  lia.
Qed.
