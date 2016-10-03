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
    This file contains the invariant of [checkChild] some associated lemmas *)
Require Import Isolation Consistency WeakestPreconditions List 
Core.Internal Invariants Model.MAL StateLib Model.Hardware 
Model.ADT DependentTypeLemmas Model.Lib GetTableAddr InternalLemmas.
Require Import Coq.Logic.ProofIrrelevance Omega.

Lemma checkChild (parent : page) (va : vaddr) (nbL : level) (P : state -> Prop) : 
{{fun s => P s /\ consistency s /\ parent = currentPartition s /\ Some nbL = getNbLevel}} 
Internal.checkChild parent nbL va
{{fun isChild s => P s /\ isChild = StateLib.checkChild parent nbL s va}}.
Proof.
unfold Internal.checkChild.
(** getFstShadow **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getFstShadow.
simpl; intros.
split.
pattern s in H.
eassumption.
unfold consistency in *.
intuition.
intros sh1.
simpl.
(** getIndexOfAddr **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getIndexOfAddr.
simpl; intros.
pattern s in H.
eassumption.
intros lastidx.
simpl.
(** getTableAddr **)
eapply WP.bindRev.
eapply WP.weaken.
eapply GetTableAddr.getTableAddr .
simpl; intros.
split.
pattern s in H.
eassumption.
split.
intuition. 
destruct H.
instantiate (2 := parent).
split.
intuition.
subst.
unfold consistency in *.
destruct H1 as (_ & _& _& _& H1 & _).
unfold currentPartitionInPartitionsList in H1; assumption. 
split.
instantiate(1 :=  sh1idx).
right.
left; trivial.  
exists sh1.
split.
destruct H; trivial.
split.
unfold consistency in *.
assert (partitionDescriptorEntry s) as Hdesc by intuition.
assert (parent = currentPartition s) as Hparent by intuition.
assert ( currentPartitionInPartitionsList s ) as HpartList by intuition.
destruct H as (_ & Hsh1).
subst. 
unfold partitionDescriptorEntry in Hdesc.
unfold currentPartitionInPartitionsList in *.
generalize (Hdesc (currentPartition s) HpartList); clear Hdesc; intros Hdesc.
assert ( sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx\/ sh1idx = sh3idx
        \/  sh1idx  = PPRidx \/  sh1idx  = PRidx) as Htmp by auto.
apply Hdesc in Htmp.
destruct Htmp as (_ & _ & Hroot).
destruct Hroot as (pg & Hroot & Hnotnull).
clear Hdesc.
unfold nextEntryIsPP in *. 
destruct (Index.succ sh1idx); [ | now contradict Hroot].
destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hroot | now contradict Hroot | 
subst ; assumption| now contradict Hroot | now contradict Hroot ]  |now contradict Hroot] .
left.
split;trivial.
intuition.
simpl.
intros ptsh1.
eapply WP.weaken.
intros.
Focus 2.
intros.
destruct H as (H0 & H1).
assert(  (getTableAddrRoot' ptsh1 sh1idx parent va s /\ ptsh1 = defaultPage )\/
          ( getTableAddrRoot ptsh1 sh1idx parent va s /\ ptsh1 <> defaultPage /\
          (forall idx : index,
          StateLib.getIndexOfAddr va fstLevel = idx ->
          isVE ptsh1 idx s))).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right.
       destruct H1 as (Hnew & H1).
       split; trivial.
       destruct H1 as (Hnull & H1).
       split; trivial.
       intros idx Hidx.
       generalize (H1 idx Hidx);clear H1;intros H1.
       destruct H1 as [(Hve & Hfalse) | [(_&Hfalse) |(_ &Hfalse)]].
      - assumption.
      - contradict Hfalse.
          unfold sh1idx.
          unfold sh2idx.
          apply indexEqFalse;
          assert (tableSize > tableSizeLowerBound).
          apply tableSizeBigEnough.
          unfold tableSizeLowerBound in *.
          omega.  apply tableSizeBigEnough.
          unfold tableSizeLowerBound in *.
          omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold sh1idx.
          unfold sh2idx.
          apply indexEqFalse;
          assert (tableSize > tableSizeLowerBound).
          apply tableSizeBigEnough.
          unfold tableSizeLowerBound in *.
          omega.  apply tableSizeBigEnough.
          unfold tableSizeLowerBound in *.
          omega. apply tableSizeBigEnough. omega. }
assert (HP := conj H0 H).
pattern s in HP.
eapply HP.
(** comparePageToNull  **)
eapply bindRev.
eapply weaken.
eapply Invariants.comparePageToNull.
simpl;intros.
pattern s in H.
eapply H.
intros isNullptSh1.
simpl.
(** case isNullptSh1 **)
case_eq isNullptSh1; intros HisNullptSh1.
{ (** ret false**) 
  eapply weaken.
  apply WP.ret.
  simpl;intros.
  split. 
  intuition.
  unfold checkChild.
  assert (nextEntryIsPP parent sh1idx sh1 s) as Hsh1 by intuition.
  unfold nextEntryIsPP in Hsh1.
  unfold getFstShadow.
  unfold readPhysical.
  case_eq (Index.succ sh1idx); intros.
  rewrite H0 in Hsh1.
  assert (parent = currentPartition s) as Hparent by intuition.
  subst.
  case_eq (lookup (currentPartition s) i (memory s) beqPage beqIndex); intros.  
  rewrite H1 in Hsh1.
  case_eq v ; intros; trivial.
  rewrite H2 in Hsh1.
  subst.
  destruct H.
  apply beq_nat_true in H2.
  assert (    (getTableAddrRoot' ptsh1 sh1idx (currentPartition s) va s /\ ptsh1 = defaultPage \/
  getTableAddrRoot ptsh1 sh1idx (currentPartition s) va s /\
  ptsh1 <> defaultPage /\
  (forall idx : index, getIndexOfAddr va fstLevel = idx -> isVE ptsh1 idx s))).
  intuition.
  destruct H3 as [(Hrootstruc & Hdef) |  Hx].
  unfold getTableAddrRoot' in Hrootstruc.
  assert (nextEntryIsPP (currentPartition s) sh1idx p s) as Hisroot by intuition.
  destruct Hrootstruc as (Htmp & Hrootstruc).
  apply Hrootstruc in Hisroot.
  destruct Hisroot as (nbl1 & Hnbl & stop2 & Hstop0 & Hstop2 & Hgetind).
  assert (Some nbL = getNbLevel) as Hlvl by intuition.
  rewrite <- Hlvl in Hnbl.
  inversion Hnbl.
  subst.
  clear Hnbl.
  unfold getNbLevel in Hlvl.
  clear H2. 
  case_eq(gt_dec nbLevel 0); intros.
  rewrite H2 in Hlvl.
  inversion Hlvl.
  rewrite <- H4.
  assert (getIndirection p va nbL (nbLevel - 1) s = Some defaultPage) as Hstopgt.
  apply getIndirectionStopLevelGT2 with (nbL + 1); try omega.
  rewrite H4.
  simpl in *. trivial.
  apply NPeano.Nat.lt_eq_cases in Hstop2.
  clear H Hrootstruc Hlvl Htmp H1.  
  destruct Hstop2.
  apply getIndirectionRetDefaultLtNbLevel with stop2; trivial. omega.
  apply getIndirectionStopLevelGT with stop2;trivial. omega.
  rewrite Hstopgt.
  destruct H.
  assert ((defaultPage =? defaultPage) = true).
  symmetry. apply beq_nat_refl.
  rewrite H5. trivial.
  assert (0 < nbLevel) by apply nbLevelNotZero. omega.
  trivial.
  trivial.
  destruct Hx as (_ & Hfalse & _).
  contradict Hfalse.
  clear H.
  unfold defaultPage in * .
  unfold CPage in *.
  case_eq (lt_dec 0 nbPage); intros.
  rewrite H in H2.
  destruct ptsh1.
  simpl in *.
  subst. f_equal.
  apply proof_irrelevance.
  rewrite H in H2.
  destruct ptsh1. destruct page_d. simpl in *.
  subst.
  f_equal.
  apply proof_irrelevance.
  trivial. trivial.   
  }
(** readPDflag **) 
  { eapply strengthen.
    + eapply weaken.
      - eapply Invariants.readPDflag.
      - intros; simpl.
        split.
        pattern s in H.
        eapply H.
        try repeat rewrite and_assoc in H.
        destruct H as (Hp & Hcons & Hparent &
        Hnbl & Hroot & Hidx & [(Hisroot & Hfalse) | Htrue ] & Hnotnull).
        apply beq_nat_false in Hnotnull.
        rewrite Hfalse in Hnotnull.
        now contradict Hnotnull.
        destruct Htrue as (Htrue & Hve).
        apply Hve in Hidx; assumption.
    +  simpl;intros.
        split.
        intuition.
        unfold checkChild.
        assert (nextEntryIsPP parent sh1idx sh1 s) as Hsh1 by intuition.
        unfold nextEntryIsPP in Hsh1.
        unfold getFstShadow.
        unfold readPhysical.
        case_eq (Index.succ sh1idx); intros.
        rewrite H0 in Hsh1.
        assert (parent = currentPartition s) as Hparent by intuition.
        subst.
        case_eq (lookup (currentPartition s) i (memory s) beqPage beqIndex); intros.  
        rewrite H1 in Hsh1.
        case_eq v ; intros; trivial; try rewrite H2 in Hsh1;
        subst; try
        now contradict Hsh1.
        assert (    (getTableAddrRoot' ptsh1 sh1idx (currentPartition s) va s /\ ptsh1 = defaultPage \/
        getTableAddrRoot ptsh1 sh1idx (currentPartition s) va s /\
        ptsh1 <> defaultPage /\
        (forall idx : index, getIndexOfAddr va fstLevel = idx -> isVE ptsh1 idx s))).
        intuition.
        destruct H2 as [(Hrootstruc & Hdef) |  Hx].
        destruct H. destruct H.
        subst.
        contradict H3.
        apply Bool.not_false_iff_true.
        symmetry. apply beq_nat_refl.
        assert ( getTableAddrRoot ptsh1 sh1idx (currentPartition s) va s) as Hrootstruc by intuition.
        unfold getTableAddrRoot in Hrootstruc.
        assert (nextEntryIsPP (currentPartition s) sh1idx p s) as Hisroot by intuition.
        destruct Hrootstruc as (Htmp & Hrootstruc).
        apply Hrootstruc in Hisroot.
        destruct Hisroot as (nbl1 & Hnbl & stop2 & Hstop2 & Hgetind).
        assert (Some nbL = getNbLevel) as Hlvl by intuition.
        rewrite <- Hlvl in Hnbl.
        inversion Hnbl.
        subst.
        clear Hnbl.
        unfold getNbLevel in Hlvl.
        case_eq(gt_dec nbLevel 0); intros.
        rewrite H2 in Hlvl.
        inversion Hlvl.
        rewrite <- H4.
        assert (getIndirection p va nbL (nbLevel - 1) s = Some ptsh1) as Hstopgt.
        apply getIndirectionStopLevelGT2 with (nbL + 1); try omega.
        rewrite H4.
        simpl in *. trivial.
        assumption.
        rewrite Hstopgt.
        destruct H.
        destruct H.
        assert (ptsh1 =? defaultPage = false).
        apply Nat.eqb_neq.
        apply beq_nat_false in H5.
        omega. 
        rewrite H6.
        subst.
        assert (getIndexOfAddr va fstLevel = lastidx) as Hidx by intuition.
        clear Hlvl Hgetind Hstopgt H Hrootstruc.
        unfold  entryPDFlag in H3.
        unfold readPDflag .
        rewrite Hidx.
        destruct (lookup ptsh1 lastidx (memory s) beqPage beqIndex)
        as [v |]; [ destruct v as [ p0 |v|p0|v|ii] ; [ now contradict H3 |  
        subst; trivial |now contradict H3 | now contradict H3 | 
        now contradict H3 ]  |now contradict H3] .
        assert (0 < nbLevel) by apply nbLevelNotZero. omega.
        trivial.
        rewrite H1 in Hsh1.
        now contradict Hsh1.
        rewrite H0 in Hsh1.
        now contradict Hsh1. }
Qed.

