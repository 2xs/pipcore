(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2016)                 *)
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
      This file contains some generic lemmas used by invariants **)
Require Import List Omega Coq.Logic.Classical_Prop Model.Lib.
Import List.ListNotations.

Lemma NoDupSplit (A: Type) :
forall l l': list A , 
NoDup (l++l') -> NoDup l /\ NoDup l'.
Proof. 
intros.
split. 
 + induction l'. 
   rewrite app_nil_r in H.
   assumption.
   apply IHl'.
   apply NoDup_remove_1 in H.
   assumption.
 + induction l'. 
   apply NoDup_nil.
   assert (NoDup (l ++ a :: l')). assumption.
   apply NoDup_remove_2 in H.
   constructor 2.
   unfold not in *. intro. apply H.
   apply in_or_app.
   right. assumption.
   apply IHl'.
   apply NoDup_remove_1 in H0.
   assumption.
Qed.

Definition disjoint {A : Type} (l1 l2 : list A) : Prop := 
forall x : A,  In x l1  -> ~ In x l2 . 

Lemma NoDupSplitInclIff (A: Type) :
forall l l': list A , 
NoDup (l++l') <-> (NoDup l /\ NoDup l') /\ disjoint l l'.
Proof. 
intros.
split.   
 + intros. split.
   -  apply NoDupSplit; trivial.
   - unfold disjoint. intros.
     revert x l H H0. 
     induction l'; intros.
     unfold not. intros. now contradict H1.
     simpl.
     apply and_not_or. 
     split.
     unfold not. intros. subst.
     unfold not in *.
     apply NoDup_remove in H.
     destruct H.
     contradict H1.
     apply in_or_app.
     left; trivial.
     apply NoDup_remove in H.
     destruct H.
     apply IHl' with l; trivial.
 + intros.
   revert l' H.
   induction l.
   - intros; simpl in *.
     intuition.
   - simpl.
     intros.
     constructor.
     intuition.
     apply in_app_iff in H0.
     destruct H0.
     apply NoDup_cons_iff in H.
     destruct H.
     now contradict H0.
     unfold disjoint in *.
     apply NoDup_cons_iff in H.
     
     destruct H.
     contradict H0.
     apply H2.
     simpl;left;trivial.
     apply IHl.
     intuition.
     apply NoDup_cons_iff in H; destruct H; trivial.
     unfold disjoint in *.
     intros.
     apply H1.
     simpl; right; trivial.          
Qed.
Lemma inclDisjoint (A : Type) (l l' l1 l2 : list A): 
disjoint l l'  -> incl l1 l -> incl l2 l' -> disjoint l1 l2.
Proof. 
intros.
unfold disjoint in *.
intros.
unfold incl in *.
unfold not.
intros.
apply H1 in H3.
contradict H3.
apply H.
apply H0; trivial.
Qed.
