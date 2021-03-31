(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2018)                 *)
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
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Internal.
Require Import Pip.Proof.Isolation Pip.Proof.Consistency Pip.Proof.WeakestPreconditions
               Pip.Proof.StateLib Pip.Proof.DependentTypeLemmas Pip.Proof.InternalLemmas.
Require Import Invariants GetTableAddr.

Require Import List Coq.Logic.ProofIrrelevance Lia EqNat Compare_dec.

Lemma checkChild (parent : page) (va : vaddr) (nbL : level) (P : state -> Prop) : 
{{fun s => P s /\ consistency s /\ parent = currentPartition s /\ Some nbL = StateLib.getNbLevel}} 
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
destruct (StateLib.Index.succ sh1idx); try now contradict Hroot.
destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex) ; try now contradict Hroot.
destruct v ; try now contradict Hroot.
subst; assumption.
left.
split;trivial.
intuition.
simpl.
intros ptsh1.
eapply WP.weaken.
intros.
2:{
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
          lia.  apply tableSizeBigEnough.
          unfold tableSizeLowerBound in *.
          lia. apply tableSizeBigEnough. lia.
       - contradict Hfalse.
          unfold sh1idx.
          unfold sh2idx.
          apply indexEqFalse;
          assert (tableSize > tableSizeLowerBound).
          apply tableSizeBigEnough.
          unfold tableSizeLowerBound in *.
          lia.  apply tableSizeBigEnough.
          unfold tableSizeLowerBound in *.
          lia. apply tableSizeBigEnough. lia. }
assert (HP := conj H0 H).
pattern s in HP.
eapply HP. }
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
  unfold StateLib.getFstShadow.
  unfold StateLib.readPhysical.
  case_eq (StateLib.Index.succ sh1idx); intros.
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
  (forall idx : index, StateLib.getIndexOfAddr va fstLevel = idx -> isVE ptsh1 idx s))).
  intuition.
  destruct H3 as [(Hrootstruc & Hdef) |  Hx].
  unfold getTableAddrRoot' in Hrootstruc.
  assert (nextEntryIsPP (currentPartition s) sh1idx p s) as Hisroot by intuition.
  destruct Hrootstruc as (Htmp & Hrootstruc).
  apply Hrootstruc in Hisroot.
  destruct Hisroot as (nbl1 & Hnbl & stop2 & Hstop0 & Hstop2 & Hgetind).
  assert (Some nbL = StateLib.getNbLevel) as Hlvl by intuition.
  rewrite <- Hlvl in Hnbl.
  inversion Hnbl.
  subst.
  clear Hnbl.
  unfold StateLib.getNbLevel in Hlvl.
  clear H2. 
  case_eq(gt_dec nbLevel 0); intros.
  rewrite H2 in Hlvl.
  inversion Hlvl.
  rewrite <- H4.
  assert (getIndirection p va nbL (nbLevel - 1) s = Some defaultPage) as Hstopgt.
  apply getIndirectionStopLevelGT2 with (nbL + 1); try lia.
  rewrite H4.
  simpl in *. trivial.
  apply NPeano.Nat.lt_eq_cases in Hstop2.
  clear H Hrootstruc Hlvl Htmp H1.  
  destruct Hstop2.
  apply getIndirectionRetDefaultLtNbLevel with stop2; trivial. lia.
  apply getIndirectionStopLevelGT with stop2;trivial. lia.
  rewrite Hstopgt.
  destruct H.
  assert ((Nat.eqb defaultPage defaultPage) = true).
  symmetry. apply beq_nat_refl.
  rewrite H5. trivial.
  assert (0 < nbLevel) by apply nbLevelNotZero. lia.
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
  {(*  eapply strengthen.
    + *) eapply weaken.
      - eapply WP.readPDflag.
      - intros; simpl.
      intuition.
      subst.
      apply beq_nat_false in H1.
      now contradict H1.
      subst.
      assert(isVE ptsh1 (StateLib.getIndexOfAddr va fstLevel) s ).
      apply H9; trivial.
      unfold isVE in H3.
      case_eq(lookup ptsh1 (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex);
      intros; rewrite H5 in *;
        
      try now contradict H3.
      case_eq v; intros; rewrite H8 in *; try now contradict H3.
      subst.
      exists v0;split; trivial.
      intuition.

        unfold checkChild.
        assert (nextEntryIsPP (currentPartition s) sh1idx sh1 s) as Hsh1 by intuition.
        unfold nextEntryIsPP in Hsh1.
        unfold StateLib.getFstShadow.
        unfold StateLib.readPhysical.
        case_eq (StateLib.Index.succ sh1idx); intros.
        rewrite H8 in Hsh1.
        subst.
        case_eq (lookup (currentPartition s) i (memory s) beqPage beqIndex); intros.  
        rewrite H10 in Hsh1.
        case_eq v ; intros; trivial; try rewrite H2 in Hsh1;
        subst; try
        now contradict Hsh1.
        assert (    (getTableAddrRoot' ptsh1 sh1idx (currentPartition s) va s /\ ptsh1 = defaultPage \/
        getTableAddrRoot ptsh1 sh1idx (currentPartition s) va s /\
        ptsh1 <> defaultPage /\
        (forall idx : index, StateLib.getIndexOfAddr va fstLevel = idx -> isVE ptsh1 idx s))).
        intuition.
        destruct H11 as [(Hrootstruc & Hdef) |  Hx].
        subst.
        now contradict H6.
        assert ( getTableAddrRoot ptsh1 sh1idx (currentPartition s) va s) as Hrootstruc by intuition.
        unfold getTableAddrRoot in Hrootstruc.
        subst.
        assert (nextEntryIsPP (currentPartition s) sh1idx p s) as Hisroot by intuition.
        destruct Hrootstruc as (Htmp & Hrootstruc).
        apply Hrootstruc in Hisroot.
        destruct Hisroot as (nbl1 & Hnbl & stop2 & Hstop2 & Hgetind).
        assert (Some nbL = StateLib.getNbLevel) as Hlvl by intuition.
        rewrite <- Hlvl in Hnbl.
        inversion Hnbl.
        subst.
        clear Hnbl.
        unfold StateLib.getNbLevel in Hlvl.
        case_eq(gt_dec nbLevel 0); intros.
        rewrite H11 in Hlvl.
        inversion Hlvl.
        rewrite <- H13.
        assert (getIndirection p va nbL (nbLevel - 1) s = Some ptsh1) as Hstopgt.
        apply getIndirectionStopLevelGT2 with (nbL + 1); try lia.
        rewrite H13.
        simpl in *. trivial.
        assumption.
        rewrite Hstopgt.
        destruct H.
        unfold  entryPDFlag in *.
        unfold StateLib.readPDflag .
        assert(Hfalse : (Nat.eqb ptsh1 defaultPage) = false).
        apply NPeano.Nat.eqb_neq.
        unfold not; intros;subst.
        apply H6.
        destruct ptsh1.
        destruct defaultPage.
        simpl in *.
        subst.
        f_equal.
        apply proof_irrelevance.
        rewrite Hfalse.
        rewrite H5.
        destruct ( pd v0); trivial.
        assert (0 < nbLevel) by apply nbLevelNotZero. lia.
        trivial.
        rewrite H10 in Hsh1.
        now contradict Hsh1.
        rewrite H8 in Hsh1.
        now contradict Hsh1. }
Qed.

Lemma checkChildInv vaInCurrentPartition vaChild currentPart descChild level:
{{ fun s : state =>   ((((partitionsIsolation s /\
    kernelDataIsolation s /\
    verticalSharing s /\
    consistency s) /\
    (Nat.eqb Kidx
       (List.nth (length vaInCurrentPartition - (nbLevel - 1 + 2)) vaInCurrentPartition defaultIndex))
       = false) /\
    (Nat.eqb Kidx
       (List.nth (length vaChild - (nbLevel - 1 + 2)) vaChild defaultIndex))
       = false) /\
    currentPart = currentPartition s) /\
    Some level = StateLib.getNbLevel
}}
  Internal.checkChild currentPart level descChild
{{
  fun res s =>
     (res = false /\
        partitionsIsolation s /\
        kernelDataIsolation s /\
        verticalSharing s /\
        consistency s
     )
  \/ (res = true /\
        exists currentShadow1 idxRefChild ptRefChild,
          partitionsIsolation s /\
          kernelDataIsolation s /\
          verticalSharing s /\
          consistency s /\

          (Nat.eqb
             Kidx
             (List.nth (length vaInCurrentPartition - (nbLevel - 1 + 2)) vaInCurrentPartition defaultIndex)
          ) = false /\
          (Nat.eqb
             Kidx
             (List.nth (length vaChild - (nbLevel - 1 + 2)) vaChild defaultIndex)
          ) = false /\

          currentPart = currentPartition s /\
          Some level = StateLib.getNbLevel /\

          nextEntryIsPP currentPart sh1idx currentShadow1 s /\
          StateLib.getIndexOfAddr descChild fstLevel = idxRefChild /\
          (getTableAddrRoot' ptRefChild sh1idx currentPart descChild s /\
             ptRefChild = defaultPage \/
             (forall idx : index,
                StateLib.getIndexOfAddr descChild fstLevel = idx ->
                  isVE ptRefChild idx s /\
                  getTableAddrRoot ptRefChild sh1idx currentPart descChild s
             )
          ) /\
          (Nat.eqb defaultPage ptRefChild) = false
     )
}}.
Proof.
{ eapply bindRev.
  (** getFstShadow **)
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
  intros currentShadow1.
  (** StateLib.getIndexOfAddr **)                
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getIndexOfAddr.
  { simpl. intros.
    pattern s in H.
    eexact H.  }
   intro idxRefChild. simpl.
(** getTableAddr **)
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
  instantiate (1:= currentPart).
  intuition. 
  subst.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *. 
  intuition.
  instantiate (1:= sh1idx).
  split. intuition.
  assert(Hcons : consistency s) by intuition.
  assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
  assert(Hcp : currentPart = currentPartition s) by intuition.
  assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
  exists currentShadow1.
  split. intuition.
  unfold consistency in *.
  destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
  unfold partitionDescriptorEntry in Hpd.
  assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/  sh1idx  = sh3idx
  \/  sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
  by auto.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
  generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
  destruct Hpd as (Hidxpd & _& Hentry). 
  destruct Hentry as (page1 & Hpd & Hnotnull).
  subst.
  split. 
  unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh1idx); try now contradict H0.
  destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex); try now contradict H0.
  destruct v ; try now contradict H0.
  subst; assumption.
  subst. left. split;intuition.
  intro ptRefChild. simpl.
(** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2:{
  intros.
  destruct H as (H0 & H1).
  assert ( (getTableAddrRoot' ptRefChild sh1idx currentPart descChild s /\ ptRefChild = defaultPage) \/
 (forall idx : index,
  StateLib.getIndexOfAddr descChild fstLevel = idx ->
  isVE ptRefChild idx s /\ getTableAddrRoot ptRefChild sh1idx currentPart descChild s  )).
  { destruct H1 as [H1 |(Hi & Hi1 & H1)].
    + left. trivial. 
    + right. intros idx Hidx.
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
      - split; assumption.
      - contradict Hfalse. 
        symmetrynot. 
        apply idxSh2idxSh1notEq.
      - contradict Hfalse. 
        symmetrynot. apply idxPDidxSh1notEq.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP. }
(** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro childListSh1Isnull. simpl.
  case_eq childListSh1Isnull.
  { intros.
   eapply WP.weaken.
     eapply WP.ret .
      simpl. intros.
      left.
      intuition.
      }
  intros HchildListSh1Isnull. 
  subst.
(* readPDflag *)
eapply strengthen.
eapply weaken.
eapply Invariants.readPDflag.
simpl;intros.
split.
pattern s in H.
eexact H.
destruct H as (H & Htrue).
destruct H as (H & Hor).
destruct Hor as [(Hor & Hfalse) | Hor].
subst.
apply beq_nat_false in Htrue.
now contradict Htrue.
destruct H as (H & Hidx).
subst.
destruct Hor with (StateLib.getIndexOfAddr descChild fstLevel);
trivial.

intros s ispd;simpl in *.
intros.
assert(Hor : ispd = true  \/ ispd = false).
destruct ispd.
left;trivial. right;trivial.
destruct Hor as [Hor | Hor].
right.
split. trivial.
exists currentShadow1,idxRefChild, ptRefChild.
intuition.
left. intuition. }
Qed.


Lemma childInPartTree (childPartDesc parentPartDesc parentPageDir childLastMMUPage : page)
                      (s : state)
                      (nbL : level)
                      (childPartDescVAddr : vaddr)
                      (idxChildPartDesc : index) :
 Some nbL = StateLib.getNbLevel
 -> nextEntryIsPP parentPartDesc PDidx parentPageDir s
 -> currentPartition s = parentPartDesc
 -> isPE childLastMMUPage (StateLib.getIndexOfAddr childPartDescVAddr fstLevel) s
 -> getTableAddrRoot childLastMMUPage PDidx parentPartDesc childPartDescVAddr s
 -> defaultPage <> childLastMMUPage
 -> StateLib.getIndexOfAddr childPartDescVAddr fstLevel = idxChildPartDesc
 -> isEntryPage childLastMMUPage idxChildPartDesc childPartDesc s
 -> entryPresentFlag childLastMMUPage idxChildPartDesc true s
 -> true = StateLib.checkChild parentPartDesc nbL s childPartDescVAddr
 -> consistency s
 -> In childPartDesc (getPartitions multiplexer s).
Proof.
intros Hlevel HnextEntryIsPP HparentPartDescIsCurrent HisPE HgetTableAddrRoot.
intros HchildLastMMUPageNotDef HidxChildPartDesc HisEntryPage HentryPresentFlag.
intros HcheckChild Hconsistency.
assert(Hchildren : In childPartDesc (getChildren (currentPartition s) s)).
{ unfold getChildren.
  rewrite <- Hlevel.
  assert(Hcurpd : StateLib.getPd parentPartDesc (memory s) = Some parentPageDir).
  { apply nextEntryIsPPgetPd.
    intuition. }
  subst parentPartDesc.
  rewrite Hcurpd.
  unfold getMappedPagesAux.
  rewrite filterOptionInIff.
  unfold getMappedPagesOption.
  rewrite in_map_iff.
  assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
  StateLib.checkVAddrsEqualityWOOffset nbLevel childPartDescVAddr va1 ( CLevel (nbLevel -1) ) = true )
  by apply AllVAddrWithOffset0.
  destruct Heqvars as (va1 & Hva1 & Hva11).  
  exists va1.  split;trivial.
  assert(Hnewgoal : getMappedPage parentPageDir s childPartDescVAddr = SomePage childPartDesc).
  {  apply getMappedPageGetTableRoot with childLastMMUPage (currentPartition s); trivial.
     { intros. split; subst; trivial. }
     { apply PeanoNat.Nat.eqb_neq. rewrite pageEqNatEqEquiv. trivial. }
     { subst. trivial. }
     { subst. trivial. }
  }
  rewrite <- Hnewgoal.
  symmetry.
  apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
  apply getNbLevelEqOption.
  unfold getPdsVAddr.
  apply filter_In.
  split;trivial.
  assert(Hnewgoal : StateLib.checkChild (currentPartition s) nbL s childPartDescVAddr = true).
  { rewrite HcheckChild; trivial. }
  { rewrite <- Hnewgoal. apply checkChildEq. symmetry. apply Hlevel.
    rewrite checkVAddrsEqualityWOOffsetPermut.
    rewrite <- Hva11. f_equal.
    assert(Hlvl : StateLib.getNbLevel = Some (CLevel (nbLevel - 1))) by apply getNbLevelEqOption. 
    rewrite  Hlvl in *.
    inversion Hlevel;trivial.
  }
}
unfold consistency in Hconsistency.
apply childrenPartitionInPartitionList with (currentPartition s); intuition.
Qed.
