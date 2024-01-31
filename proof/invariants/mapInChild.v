(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2024)                *)
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

Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Services.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.InternalLemmas
               Pip.Proof.Isolation Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Invariants GetTableAddr.
Require Import Bool List EqNat.

(** * Summary 
    This file contains the invariant of [addVaddr]. 
    We prove that this PIP service preserves the isolation property *)

Lemma mappedInChild (vaChild : vaddr) :
{{fun s => partitionsIsolation s   /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }} 
mappedInChild vaChild 
{{fun _ s  => partitionsIsolation s   /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold mappedInChild.
(** getCurPartition **)
eapply WP.bindRev.
eapply WP.weaken. 
eapply Invariants.getCurPartition .
cbn. 
intros. 
pattern s in H. 
eexact H.
intro currentPart.
(** getNbLevel **)
eapply WP.bindRev.
eapply weaken.
eapply Invariants.getNbLevel.
simpl. intros.
pattern s in H.
eexact H.
intros level.
simpl.
(** getPd **)  
eapply WP.bindRev. 
{ eapply WP.weaken. 
  eapply Invariants.getPd.
  simpl.
  intros.
  split.
  (* try repeat rewrite and_assoc in H. *)
  pattern s in H. eapply H.
  unfold consistency in *.
  unfold partitionDescriptorEntry in *.
  unfold currentPartitionInPartitionsList in *.
  intuition          subst. trivial. 
  }
intro currentPD. simpl. 
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      try repeat rewrite and_assoc in H.
      split.
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart). 
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= idxPageDir).
      split. intuition.
      assert(consistency s /\
              Some level = StateLib.getNbLevel /\ 
              currentPart = currentPartition s /\ 
              nextEntryIsPP currentPart idxPageDir currentPD s) as (Hcons & Hlevel & Hcp & Hrootpd)
      by intuition.
      clear H. 
      exists currentPD.
      split. assumption.
      split.
      unfold consistency in *.
      assert(partitionDescriptorEntry s /\ currentPartitionInPartitionsList s) as (Hpd &Hpr)
      by intuition. clear Hcons. 

      unfold partitionDescriptorEntry in Hpd.
      assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2\/idxPageDir = idxShadow3\/ idxPageDir = idxParentDesc \/ idxPageDir = idxPartDesc ) as Htmp
          by auto.
      subst.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.     
       generalize (Hpd idxPageDir Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ idxPageDir); [|now contradict Hrootpd];
      destruct (lookup (currentPartition s) i (memory s) pageEq idxEq); [|now contradict Hrootpd];
      destruct v ; try now contradict Hrootpd.
      subst; assumption.
      subst. left. split;intuition.
     intro ptvaChildFromPD. simpl.

 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2:{
      intros.
      destruct H as (H0 & H1).
      assert(( getTableAddrRoot' ptvaChildFromPD idxPageDir currentPart vaChild s /\  ptvaChildFromPD = pageDefault) \/
     (forall idx : index,
      StateLib.getIndexOfAddr vaChild levelMin = idx ->
      isPE ptvaChildFromPD idx s/\
     getTableAddrRoot ptvaChildFromPD idxPageDir currentPart vaChild s)).
      {
      destruct H1 as [H1 |(Hnew & Hi & H1)].
      + left. trivial. 
      + right. intros idx Hidx.
      
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse. apply idxPDidxSh1notEq.
       - contradict Hfalse. apply idxPDidxSh2notEq.
      -split;
       assumption. }
       
       assert (HP := conj H0 H).
       pattern s in HP.
       eapply HP. }   
(** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptvachildIsnull. simpl.
      case_eq ptvachildIsnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HisNullpd. subst.
(** StateLib.getIndexOfAddr    *)             
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros. 
        destruct H as ((H & [(Hptchild & Hi)| Hptchild]) & Hptchildnotnull).
        + subst. contradict Hptchildnotnull. intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in H. *)
          pattern s in HP.
          eapply HP.  }
       intro idxSh1. simpl.
(**readPresent **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readPresent. simpl.
         intros.
         split. 
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         destruct H as (H & Hidx).
         assert (forall idx : index,
         StateLib.getIndexOfAddr vaChild levelMin = idx -> 
         isPE ptvaChildFromPD idx s /\
     getTableAddrRoot ptvaChildFromPD idxPageDir currentPart vaChild s).  
         { intuition. }
         
         apply H0 in Hidx. destruct Hidx; assumption.
       }
       intro present. simpl.
(**readAccessible **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readAccessible. simpl.
         intros.
         split.
         
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         apply entryPresentFlagIsPE with present;intuition. }
       intros accessible. simpl.   
case_eq(present && accessible);intros Hand.
(** getFstShadow **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getFstShadow. cbn.
intros s H.
split.
pattern s in H.
eexact H.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
intros currentShadow.
(** getTableAddr : to check if the virtual address is available to map a new page  **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.

split. 
instantiate (1:= currentPart );trivial.
{ unfold consistency in *. 
unfold currentPartitionInPartitionsList in *.
intuition. subst. trivial. }
instantiate (1:= idxShadow1).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
exists currentShadow.
split. intuition.
split. 
apply sh1PartNotNull with currentPart s.
{ unfold consistency in *. 
unfold currentPartitionInPartitionsList in *.
intuition. subst. trivial. } 
intuition.
unfold consistency in *.
intuition.
left.
split;trivial.
intros ptVaChildFromSh1.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2:{
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptVaChildFromSh1 idxShadow1 currentPart vaChild s /\ 
ptVaChildFromSh1 = pageDefault) \/
(forall idx : index,
StateLib.getIndexOfAddr vaChild levelMin = idx ->
isVE ptVaChildFromSh1 idx s /\ getTableAddrRoot ptVaChildFromSh1 idxShadow1 currentPart vaChild s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
    -  split; assumption.
    - contradict Hfalse.
       unfold not;intros Hfalse;symmetry in Hfalse; contradict Hfalse.
      apply idxSh2idxSh1notEq.
    - contradict Hfalse. 
      unfold not;intros Hfalse;symmetry in Hfalse; contradict Hfalse.
      apply idxPDidxSh1notEq. }
assert (HP := conj H0 H).
pattern s in HP.
exact HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro isNull. simpl.
case_eq isNull.
{ intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition. }
intros HisNull. subst.
(** StateLib.getIndexOfAddr **)                
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getIndexOfAddr.
{ simpl. intros.
  destruct H as ((Ha1 & Ha3) & Ha4).
  assert (Hnewget :  isVE ptVaChildFromSh1
  (StateLib.getIndexOfAddr vaChild levelMin) s /\
       getTableAddrRoot ptVaChildFromSh1 idxShadow1 currentPart vaChild s /\ 
       (Nat.eqb pageDefault ptVaChildFromSh1) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr vaChild levelMin);trivial.
      intuition. }
   subst.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  eexact HP. }
intro idxvaChild.
simpl.
(** readVirEntry **)
eapply WP.weaken.
eapply WP.readVirEntry. simpl.
intros.
destruct H as (H & Hentry).
assert(Hx : isVE ptVaChildFromSh1 (StateLib.getIndexOfAddr vaChild levelMin) s ) by intuition.
unfold isVE in Hx.
subst.
destruct (lookup ptVaChildFromSh1 (StateLib.getIndexOfAddr vaChild levelMin)
         (memory s) pageEq idxEq);
         try now contradict Hx.
destruct v ; try now contradict Hx.
exists v.
split;intuition.
(** ret **)
eapply weaken.
eapply WP.ret . simpl.
  intros. intuition.
Qed.
