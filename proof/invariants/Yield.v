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
    This file contains the invariant of [yield]. 
    We prove that this PIP service preserves the isolation property *)

Require Import Model.ADT Model.Hardware Model.Lib Model.MALInternal Model.MAL Core.Services DependentTypeLemmas InternalLemmas Isolation Invariants StateLib Consistency WeakestPreconditions GetTableAddr.
Import Omega List Bool.

Lemma yield      (targetPartitionDescriptor : vaddr)
                 (userTargetInterrupt : userValue)
                 (userCallerContextSaveIndex : userValue)
                 (flagsOnWake : interruptMask)
                 (flagsOnYield : interruptMask)
                 (interruptedContext : contextAddr) :
(* Precondition *)
{{fun (s : state) => partitionsIsolation s /\ 
                     kernelDataIsolation s /\
                     verticalSharing s /\
                     consistency s }}
(* fonction monadique *)
yield targetPartitionDescriptor userTargetInterrupt userCallerContextSaveIndex flagsOnWake flagsOnYield interruptedContext
(* Postcondition *)
{{fun _ (s' : state) => partitionsIsolation s' /\
                       kernelDataIsolation s' /\
                       verticalSharing s' /\
                       consistency s' }}.
Proof.
unfold yield.
eapply bindRev.
(** checkIndexPropertyLTB *)
eapply weaken.
apply Invariants.checkIndexPropertyLTB.
simpl.
intros. eapply H. simpl.
intro userTargetInterruptIsValid.
case_eq (negb userTargetInterruptIsValid).
intro. eapply weaken. eapply ret. simpl. intros. intuition.
rewrite Bool.negb_false_iff. intro HuserTargetInterruptIsValid. subst.
eapply bindRev.
(** getIndexFromUserValue *)
eapply WP.weaken.
eapply Invariants.getIndexFromUserValue.
simpl.
intros.
split.
rewrite Nat.ltb_lt in H.
apply H.
rewrite Nat.ltb_lt in H.
destruct H.
trivial.
simpl.
intro targetInterrupt.
eapply bindRev.
(** getCurPartition *)
eapply weaken.
eapply Invariants.getCurPartition.
simpl.
intros.
eapply H.
simpl. intro callerPartDesc.
eapply bindRev.
(** getPd *)
eapply weaken.
eapply Invariants.getPd.
simpl.
intros.
split.
apply H.
  (* First Property *)
  split.
  unfold consistency in *.
  intuition.
  (* Second Property *)
  assert (currentPartitionInPartitionsList s) as HcallerPartDescInPartList.
  unfold consistency in H.
  intuition.
  destruct H. subst.
  apply HcallerPartDescInPartList.
intro callerPageDir.
simpl.
eapply bindRev.
(** getNbLevel *)
eapply Invariants.getNbLevel.
simpl. intro nbL.
(** checkIndexPropertyLTB - callerContextSaveIndexIsValid *)
eapply bindRev.
eapply weaken.
apply Invariants.checkIndexPropertyLTB.
simpl.
intro s. intro preconditions. apply preconditions.
simpl.
intro callerContextSaveIndexIsValid.
case_eq (negb callerContextSaveIndexIsValid);
intro HcallerContextSaveIndexIsValid.
eapply weaken. eapply ret. simpl. intuition.
rewrite Bool.negb_false_iff in HcallerContextSaveIndexIsValid. subst.
(** getIndexFromUserValue - callerContextSaveIndex **)
eapply bindRev.
eapply weaken.
eapply Invariants.getIndexFromUserValue.
simpl.
intros.
rewrite Nat.ltb_lt in H.
split.
apply H.
destruct H.
apply H0.
intro callerContextSaveIndex.
(** vidtVaddr - getVidtVAddr **)
simpl.
eapply bindRev.
eapply weaken.
eapply Invariants.ret.
simpl.
intros.
apply H.
simpl.
intro vidtVAddr.
(** getTableAddr - callerVidtLastMMUPage **)
eapply WP.bindRev.
eapply WP.weaken.
apply getTableAddr.
simpl.
intros s H.
split.
destruct H.
pattern s in H. 
eexact H. subst.
split. 
intuition.
split.
instantiate (1:= callerPartDesc).
intuition. 
subst.
unfold consistency in *. 
unfold  currentPartitionInPartitionsList in *. 
intuition.
instantiate (1:= PDidx).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some nbL = StateLib.getNbLevel) by intuition. 
assert(Hcp : callerPartDesc = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP callerPartDesc PDidx callerPageDir s) by intuition.
exists callerPageDir.
split. intuition.

unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/  PDidx  = sh3idx
\/  PDidx  = PPRidx \/  PDidx = PRidx) as Htmp 
by auto.
generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry).
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
 unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
 [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
 as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict H0 | 
 now contradict H0 | 
 subst;assumption | now contradict H0| now contradict H0 ]  
 |now contradict H0] | now contradict H0].
subst. left. split;intuition.
intro callerVidtLastMMUPage. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
Focus 2.
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' callerVidtLastMMUPage PDidx callerPartDesc MALInternal.vidtVAddr s /\ callerVidtLastMMUPage = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr MALInternal.vidtVAddr fstLevel = idx ->
isPE callerVidtLastMMUPage idx s /\ getTableAddrRoot callerVidtLastMMUPage PDidx callerPartDesc MALInternal.vidtVAddr s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(_& Hfalse) | [(_&Hfalse) | (Hpe &Htrue) ]].
    - contradict Hfalse.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - split; assumption.
}
assert (HP := conj H0 H).
pattern s in HP.
eapply HP.
(** comparePageToNull - vidtLastMMUPageisNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro vidtLastMMUPageisNull. simpl.
case_eq vidtLastMMUPageisNull.
{ intros.
  eapply WP.weaken.
  eapply WP.ret .
  simpl. intros.
  intuition. }
intros. 
subst.
(** hypotheses cleanup *)
eapply weaken.
Focus 2.
intros.
destruct H as ((Hexec & Hconj) & Hlast).
destruct Hconj as [HFalse | HTrue].
- destruct HFalse.
  subst.
  rewrite Nat.eqb_refl in Hlast.
  now contradict Hlast.
Focus 2.
destruct HTrue with (StateLib.getIndexOfAddr MALInternal.vidtVAddr fstLevel).
trivial.
apply beq_nat_false in Hlast.
assert (Hdef:= conj (conj (conj Hexec H) H0) Hlast).
pattern s in Hdef.
apply Hdef.
(** getIndexOfAddr - idxVidtInLastMMUPage *)
eapply bindRev.
eapply Invariants.getIndexOfAddr.
simpl.
intro idxVidtInLastMMUPage.
(** readPresent - callerVidtIsPresent *)
eapply bindRev.
eapply weaken.
eapply Invariants.readPresent.
intros.
simpl.
split.
apply H.
intuition.
subst.
trivial.
simpl.
intro callerVidtIsPresent.
(** negb callerVidtIsPresent *)
case_eq (negb callerVidtIsPresent).
intro callerVidtIsNotPresent.
eapply weaken.
eapply ret.
simpl.
intros.
intuition.
intro.
apply negb_false_iff in H.
subst.

(** readAccessible - callerVidtIsAccessible *)
eapply bindRev.
eapply weaken.
eapply Invariants.readAccessible.
simpl.
intros.
split.
apply H.
intuition.
subst.
trivial.
simpl.
intro callerVidtIsAccessible.

(** negb callerVidtIsAccessible *)
case_eq (negb callerVidtIsAccessible).
intro.
eapply weaken.
eapply ret.
simpl.
intros.
intuition.
intro.
apply negb_false_iff in H.
subst.

(** readPhyEntry - callerVidt *)
eapply bindRev.
eapply weaken.
eapply Invariants.readPhyEntry.
simpl.
intros.
split.
apply H.
intuition.
subst.
trivial.
simpl.

(** compareVAddrToNull - calleePartDescVAddrIsDefault *)




Admitted. 
