(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2021)                *)
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
Require Import Pip.Model.ADT.
Require Import List PeanoNat Lt Lia Coq.Logic.Classical_Prop Bool Coq.Program.Tactics.
Import List.ListNotations.


(** * Summary 
    This file contains required functions to manipulate an association list *) 
Fixpoint eqList {A : Type} (l1 l2 : list A) (eq : A -> A -> bool) : bool := 
 match l1, l2 with 
 |nil,nil => true
 |a::l1' , b::l2' => if  eq a b then eqList l1' l2' eq else false
 |_ , _ => false
end.

Definition beqPairs {A B: Type} (a : (A*B)) (b : (A*B)) (eqA : A -> A -> bool) (eqB : B -> B -> bool) :=
if (eqA (fst a) (fst b)) && (eqB (snd a) (snd b))  then true else false.

Fixpoint lookup {A B C: Type} (k : A) (i : B)  (assoc : list ((A * B)*C))  (eqA : A -> A -> bool) (eqB : B -> B -> bool) :=
  match assoc with
    | nil => None  
    | (a, b) :: assoc' => if beqPairs a (k,i) eqA eqB then Some b else lookup k i assoc' eqA eqB
  end. 
 
Fixpoint removeDup {A B C: Type} (k : A) (i : B) (assoc : list ((A * B)*C) )(eqA : A -> A -> bool) (eqB : B -> B -> bool)   :=
  match assoc with
    | nil => nil
    | (a, b) :: assoc' => if beqPairs a (k,i) eqA eqB then removeDup k i assoc' eqA eqB else (a, b) :: (removeDup k i assoc' eqA eqB)
  end.

Definition add {A B C: Type} (k : A) (i : B) (v : C) (assoc : list ((A * B)*C) ) (eqA : A -> A -> bool) (eqB : B -> B -> bool)  :=
  (k,i,v) :: removeDup k i assoc eqA eqB.

Program Fixpoint getNextVaddrAux (indexList : list index) : bool * (list index) :=
match indexList with
| nil   =>  (true, nil)
| h::t  =>  if (fst (getNextVaddrAux t)) then
              if (Nat.eq_dec (h+1) tableSize) then
                (true, (Build_index 0 _)::(snd (getNextVaddrAux t)))
              else
                (false, (Build_index (h+1) _::(snd (getNextVaddrAux t))))
            else
                (false, (Build_index h _::(snd (getNextVaddrAux t))))
end.

Next Obligation.
destruct tableSizeBigEnough.
unfold tableSizeLowerBound.
apply neq_0_lt.
trivial.
unfold tableSizeLowerBound in g.
apply Nat.lt_0_succ.
Qed.

Next Obligation.
assert(i h < tableSize) by (apply (ADT.Hi h)).
destruct h.
simpl in *.
lia.
Qed.

Next Obligation.
apply (ADT.Hi h).
Qed.

Definition getNextVaddr (va : vaddr) : vaddr :=
CVaddr (snd (getNextVaddrAux va)).

Fixpoint getNthVAddrFromAux (start : vaddr) (range : nat) : vaddr :=
match range with
| 0   => start
| S n => getNthVAddrFromAux (getNextVaddr start) n
end.


Obligation Tactic := idtac.

Program Fixpoint firstVAddrGreaterThanSecondAux (firstIndexList secondIndexList : list index)
(HlenVAddr   : length firstIndexList = length secondIndexList)
: bool :=
match (firstIndexList, secondIndexList) with
| (nil, nil) => true
| (hf::tf, hs::ts) => let hs_le_hf := Nat.leb hs hf in
                      if (hs_le_hf) then
                        true
                      else
                      let differentHeads := negb (Nat.eqb hf hs) in
                      if (differentHeads) then
                        false
                      else
                        firstVAddrGreaterThanSecondAux tf ts _
| (_,_) => False_rect _ _
end.

Next Obligation.
cbn.
intros firstIndexList secondIndexList HlenVAddr hf tf hs ts [=Hfirst Hsecond].
subst.
injection HlenVAddr.
trivial.
Qed.

Next Obligation.
cbn.
intros firstIndexList secondIndexList HlenVAddr someIndexList someIndexList2.
case_eq someIndexList.
- case_eq someIndexList2.
  * intros _ _ H _.
    destruct H as (_, Hcontradict).
    contradict Hcontradict.
    reflexivity.
  * intros.
    injection Heq_anonymous.
    intros.
    subst.
    contradict HlenVAddr.
    unfold length.
    trivial.
- case_eq someIndexList2.
  * intros.
    injection Heq_anonymous.
    intros.
    subst.
    contradict HlenVAddr.
    unfold length.
    apply Nat.neq_succ_0.
  * intros i l H i0 l0 H0 H1 H2.
    destruct H1.
    apply (H1 i0 l0 i l).
    trivial.
Qed.

Next Obligation.
cbn.
intros.
split; intros; unfold not; intro; inversion H.
Qed.

Next Obligation.
cbn.
intros.
split; intros; unfold not; intro; inversion H.
Qed.

Obligation Tactic := program_simpl.