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
    This file contains the invariant of [createPartition]. 
    We prove that this PIP service preserves the isolation property *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Services.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.InternalLemmas
Pip.Proof.Isolation Pip.Proof.Lib Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Invariants GetTableAddr PropagatedProperties WriteAccessible.
Import Bool Coq.Logic.ProofIrrelevance List EqNat.
 


Lemma writePhyEntry1 accessibleChild accessibleSh1 accessibleSh2 accessibleList 
pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
 ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
idxConfigPagesList presentConfigPagesList 
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2
derivedSh2Child childListSh1 derivedRefChildListSh1 listparam phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild :
presentRefChild && accessibleChild && presentPDChild && true && presentConfigPagesList &&
         accessibleList && presentSh1 && accessibleSh1 && presentSh2 && accessibleSh2 = true -> 
         derivedRefChild && derivedPDChild && derivedSh1Child && derivedSh2Child && derivedRefChildListSh1 = true -> 
{{ fun s : state =>
partitionsIsolation s /\
kernelDataIsolation s /\
verticalSharing s /\
consistency s /\
Some level = StateLib.getNbLevel /\
false =
StateLib.checkVAddrsEqualityWOOffset nbLevel descChild pdChild level /\
false =
StateLib.checkVAddrsEqualityWOOffset nbLevel descChild shadow1 level /\
false =
StateLib.checkVAddrsEqualityWOOffset nbLevel descChild shadow2 level /\
false = StateLib.checkVAddrsEqualityWOOffset nbLevel descChild listparam level /\
false =
StateLib.checkVAddrsEqualityWOOffset nbLevel pdChild shadow1 level /\
false =
StateLib.checkVAddrsEqualityWOOffset nbLevel pdChild shadow2 level /\
false = StateLib.checkVAddrsEqualityWOOffset nbLevel pdChild listparam level /\
false =
StateLib.checkVAddrsEqualityWOOffset nbLevel shadow1 shadow2 level /\
false = StateLib.checkVAddrsEqualityWOOffset nbLevel shadow1 listparam level /\
false = StateLib.checkVAddrsEqualityWOOffset nbLevel shadow2 listparam level /\
(Nat.eqb Kidx (nth (length descChild - (nbLevel - 1 + 2)) descChild defaultIndex))
= false /\
(Nat.eqb Kidx (nth (length pdChild - (nbLevel - 1 + 2)) pdChild defaultIndex))
= false /\
(Nat.eqb Kidx (nth (length shadow1 - (nbLevel - 1 + 2)) shadow1 defaultIndex))
= false /\
(Nat.eqb Kidx (nth (length shadow2 - (nbLevel - 1 + 2)) shadow2 defaultIndex))
= false /\
(Nat.eqb Kidx (nth (length listparam - (nbLevel - 1 + 2)) listparam defaultIndex))
= false /\
beqVAddr defaultVAddr pdChild = false /\
beqVAddr defaultVAddr shadow1 = false /\
beqVAddr defaultVAddr shadow2 = false /\
beqVAddr defaultVAddr listparam = false /\
currentPart = currentPartition s /\
nextEntryIsPP currentPart PDidx currentPD s /\
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\
getTableAddrRoot ptRefChild PDidx currentPart descChild s) /\
(Nat.eqb defaultPage ptRefChild) = false /\
StateLib.getIndexOfAddr descChild fstLevel = idxRefChild /\
entryPresentFlag ptRefChild idxRefChild presentRefChild s /\
entryUserFlag ptRefChild idxRefChild accessibleChild s /\
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isPE ptPDChild idx s /\
getTableAddrRoot ptPDChild PDidx currentPart pdChild s) /\
(Nat.eqb defaultPage ptPDChild) = false /\
StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild /\
entryPresentFlag ptPDChild idxPDChild presentPDChild s /\
entryUserFlag ptPDChild idxPDChild true s /\
(forall idx : index,
StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
isPE ptSh1Child idx s /\
getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) /\
(Nat.eqb defaultPage ptSh1Child) = false /\
StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1 /\
entryPresentFlag ptSh1Child idxSh1 presentSh1 s /\
entryUserFlag ptSh1Child idxSh1 accessibleSh1 s /\
(forall idx : index,
StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
isPE ptSh2Child idx s /\
getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) /\
(Nat.eqb defaultPage ptSh2Child) = false /\
StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2 /\
entryPresentFlag ptSh2Child idxSh2 presentSh2 s /\
entryUserFlag ptSh2Child idxSh2 accessibleSh2 s /\
(forall idx : index,
StateLib.getIndexOfAddr listparam fstLevel = idx ->
isPE ptConfigPagesList idx s /\
getTableAddrRoot ptConfigPagesList PDidx currentPart listparam s) /\
(Nat.eqb defaultPage ptConfigPagesList) = false /\
StateLib.getIndexOfAddr listparam fstLevel = idxConfigPagesList /\
entryPresentFlag ptConfigPagesList idxConfigPagesList
presentConfigPagesList s /\
entryUserFlag ptConfigPagesList idxConfigPagesList accessibleList s /\
nextEntryIsPP currentPart sh1idx currentShadow1 s /\
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isVE ptRefChildFromSh1 idx s /\
getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) /\
(Nat.eqb defaultPage ptRefChildFromSh1) = false /\
(exists va : vaddr,
isEntryVA ptRefChildFromSh1 idxRefChild va s /\
beqVAddr defaultVAddr va = derivedRefChild) /\
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isVE ptPDChildSh1 idx s /\
getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) /\
(Nat.eqb defaultPage ptPDChildSh1) = false /\
(exists va : vaddr,
isEntryVA ptPDChildSh1 idxPDChild va s /\
beqVAddr defaultVAddr va = derivedPDChild) /\
(forall idx : index,
StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
isVE ptSh1ChildFromSh1 idx s /\
getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) /\
(Nat.eqb defaultPage ptSh1ChildFromSh1) = false /\
(exists va : vaddr,
isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\
beqVAddr defaultVAddr va = derivedSh1Child) /\
(forall idx : index,
StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) /\
(Nat.eqb defaultPage childSh2) = false /\
(exists va : vaddr,
isEntryVA childSh2 idxSh2 va s /\ beqVAddr defaultVAddr va = derivedSh2Child) /\
(forall idx : index,
StateLib.getIndexOfAddr listparam fstLevel = idx ->
isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 sh1idx currentPart listparam s) /\
(Nat.eqb defaultPage childListSh1) = false /\
(exists va : vaddr,
isEntryVA childListSh1 idxConfigPagesList va s /\
beqVAddr defaultVAddr va = derivedRefChildListSh1) /\
isEntryPage ptPDChild idxPDChild phyPDChild s /\ (Nat.eqb defaultPage phyPDChild) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s))) /\
isEntryPage ptSh1Child idxSh1 phySh1Child s /\ (Nat.eqb defaultPage phySh1Child) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s))) /\
isEntryPage ptSh2Child idxSh2 phySh2Child s /\ (Nat.eqb defaultPage phySh2Child) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s))) /\
isEntryPage ptConfigPagesList idxConfigPagesList phyConfigPagesList s /\
(Nat.eqb defaultPage phyConfigPagesList) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s))) /\
isEntryPage ptRefChild idxRefChild phyDescChild s }} 
  MAL.writeAccessible ptPDChild idxPDChild false
   {{ fun _ s  =>
   ((((partitionsIsolation s /\
       kernelDataIsolation s /\
       verticalSharing s /\
       consistency s /\
       Some level = StateLib.getNbLevel /\
       false = StateLib.checkVAddrsEqualityWOOffset nbLevel descChild pdChild level /\
       false = StateLib.checkVAddrsEqualityWOOffset nbLevel descChild shadow1 level /\
       false = StateLib.checkVAddrsEqualityWOOffset nbLevel descChild shadow2 level /\
       false = StateLib.checkVAddrsEqualityWOOffset nbLevel descChild listparam level /\
       false = StateLib.checkVAddrsEqualityWOOffset nbLevel pdChild shadow1 level /\
       false = StateLib.checkVAddrsEqualityWOOffset nbLevel pdChild shadow2 level /\
       false = StateLib.checkVAddrsEqualityWOOffset nbLevel pdChild listparam level /\
       false = StateLib.checkVAddrsEqualityWOOffset nbLevel shadow1 shadow2 level /\
       false = StateLib.checkVAddrsEqualityWOOffset nbLevel shadow1 listparam level /\
       false = StateLib.checkVAddrsEqualityWOOffset nbLevel shadow2 listparam level /\
       (Nat.eqb Kidx (nth (length descChild - (nbLevel - 1 + 2)) descChild defaultIndex)) = false /\
       (Nat.eqb Kidx (nth (length pdChild - (nbLevel - 1 + 2)) pdChild defaultIndex)) = false /\
       (Nat.eqb Kidx (nth (length shadow1 - (nbLevel - 1 + 2)) shadow1 defaultIndex)) = false /\
       (Nat.eqb Kidx (nth (length shadow2 - (nbLevel - 1 + 2)) shadow2 defaultIndex)) = false /\
       (Nat.eqb Kidx (nth (length listparam - (nbLevel - 1 + 2)) listparam defaultIndex)) = false /\
       beqVAddr defaultVAddr pdChild = false /\
       beqVAddr defaultVAddr shadow1 = false /\
       beqVAddr defaultVAddr shadow2 = false /\
       beqVAddr defaultVAddr listparam = false /\
       currentPart = currentPartition s /\
       nextEntryIsPP currentPart PDidx currentPD s /\
       (forall idx : index,
        StateLib.getIndexOfAddr descChild fstLevel = idx ->
        isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) /\
       (Nat.eqb defaultPage ptRefChild) = false /\
       StateLib.getIndexOfAddr descChild fstLevel = idxRefChild /\
       entryPresentFlag ptRefChild idxRefChild presentRefChild s /\
       entryUserFlag ptRefChild idxRefChild accessibleChild s /\
       (forall idx : index,
        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
        isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) /\
       (Nat.eqb defaultPage ptPDChild) = false /\
       StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild /\
       entryPresentFlag ptPDChild idxPDChild presentPDChild s) /\
      (forall idx : index,
       StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
       isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) /\
      (Nat.eqb defaultPage ptSh1Child) = false /\
      StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1 /\
      entryPresentFlag ptSh1Child idxSh1 presentSh1 s /\
      entryUserFlag ptSh1Child idxSh1 accessibleSh1 s /\
      (forall idx : index,
       StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
       isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) /\
      (Nat.eqb defaultPage ptSh2Child) = false /\
      StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2 /\
      entryPresentFlag ptSh2Child idxSh2 presentSh2 s /\
      entryUserFlag ptSh2Child idxSh2 accessibleSh2 s /\
      (forall idx : index,
       StateLib.getIndexOfAddr listparam fstLevel = idx ->
       isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart listparam s) /\
      (Nat.eqb defaultPage ptConfigPagesList) = false /\
      StateLib.getIndexOfAddr listparam fstLevel = idxConfigPagesList /\
      entryPresentFlag ptConfigPagesList idxConfigPagesList presentConfigPagesList s /\
      entryUserFlag ptConfigPagesList idxConfigPagesList accessibleList s /\
      nextEntryIsPP currentPart sh1idx currentShadow1 s /\
      (forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\ getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) /\
      (Nat.eqb defaultPage ptRefChildFromSh1) = false /\
      (exists va : vaddr,
         isEntryVA ptRefChildFromSh1 idxRefChild va s /\ beqVAddr defaultVAddr va = derivedRefChild) /\
      (forall idx : index,
       StateLib.getIndexOfAddr pdChild fstLevel = idx ->
       isVE ptPDChildSh1 idx s /\ getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) /\
      (Nat.eqb defaultPage ptPDChildSh1) = false /\
      (exists va : vaddr, isEntryVA ptPDChildSh1 idxPDChild va s /\ beqVAddr defaultVAddr va = derivedPDChild) /\
      (forall idx : index,
       StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
       isVE ptSh1ChildFromSh1 idx s /\ getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) /\
      (Nat.eqb defaultPage ptSh1ChildFromSh1) = false /\
      (exists va : vaddr, isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) /\
      (forall idx : index,
       StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
       isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) /\
      (Nat.eqb defaultPage childSh2) = false /\
      (exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ beqVAddr defaultVAddr va = derivedSh2Child) /\
      (forall idx : index,
       StateLib.getIndexOfAddr listparam fstLevel = idx ->
       isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 sh1idx currentPart listparam s) /\
      (Nat.eqb defaultPage childListSh1) = false /\
      (exists va : vaddr,
         isEntryVA childListSh1 idxConfigPagesList va s /\ beqVAddr defaultVAddr va = derivedRefChildListSh1) /\
      isEntryPage ptPDChild idxPDChild phyPDChild s /\
      (Nat.eqb defaultPage phyPDChild) = false /\
      (forall partition : page,
       In partition (getPartitions multiplexer s) ->
       ~ (partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s))) /\
      isEntryPage ptSh1Child idxSh1 phySh1Child s /\
      (Nat.eqb defaultPage phySh1Child) = false /\
      (forall partition : page,
       In partition (getPartitions multiplexer s) ->
       ~ (partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s))) /\
      isEntryPage ptSh2Child idxSh2 phySh2Child s /\
      (Nat.eqb defaultPage phySh2Child) = false /\
      (forall partition : page,
       In partition (getPartitions multiplexer s) ->
       ~ (partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s))) /\
      isEntryPage ptConfigPagesList idxConfigPagesList phyConfigPagesList s /\
      (Nat.eqb defaultPage phyConfigPagesList) = false /\
      (forall partition : page,
       In partition (getPartitions multiplexer s) ->
       ~ (partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s)))) /\
     isEntryPage ptRefChild idxRefChild phyDescChild s) /\
    (Nat.eqb defaultPage phyDescChild) = false /\
    (forall partition : page,
     In partition (getPartitions multiplexer s) -> ~ In phyDescChild (getConfigPages partition s)) /\
    isPartitionFalse ptSh1ChildFromSh1 idxSh1 s /\
    isPartitionFalse childSh2 idxSh2 s /\
    isPartitionFalse childListSh1 idxConfigPagesList s /\
    isPartitionFalse ptRefChildFromSh1 idxRefChild s /\
    isPartitionFalse ptPDChildSh1 idxPDChild s /\
    isAccessibleMappedPageInParent currentPart pdChild phyPDChild s = true) /\
   entryUserFlag ptPDChild idxPDChild false s }} .
  Proof.
  intros Hlegit Hderiv.  
     eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
    assert (exists entry : Pentry,
      lookup ptPDChild idxPDChild (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      assert (forall idx : index,
          StateLib.getIndexOfAddr pdChild fstLevel = idx ->
          isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) as H1 by intuition.
      generalize (H1  idxPDChild);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild ) as H2 by intuition.
      apply H1 in H2. intuition. }      
    destruct Hlookup as (entry & Hlookup).
    exists entry ; split;trivial.
    assert(Hphynotnull : (Nat.eqb defaultPage phyDescChild) = false).
    { unfold consistency in *.
      assert(Hcons : isPresentNotDefaultIff s) by intuition.
      assert(Hpresent : entryPresentFlag ptRefChild idxRefChild presentRefChild s) by intuition.
      apply phyPageNotDefault with ptRefChild idxRefChild s;intuition.
      repeat rewrite andb_true_iff in Hlegit;intuition.
      subst. trivial. }
    assert(Hphy :forall partition, In partition (getPartitions multiplexer s) ->
      ~ In phyDescChild  (getConfigPages partition s)).
    { intros. 
      try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as ( presentPD & accessPD & _ ).
       unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial.
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptRefChild descChild 
      idxRefChild accessibleChild level presentRefChild currentPD; subst; intuition. }
    assert (Hreadflag : isPartitionFalse ptPDChildSh1 idxPDChild s ).
   { unfold isPartitionFalse.
    unfold consistency in *. 
    assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
    unfold accessibleVAIsNotPartitionDescriptor in *.
    assert (Hflag : getPDFlag currentShadow1 pdChild s = false).
    { apply Haccessva with currentPart currentPD phyPDChild.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst;assumption.
      apply nextEntryIsPPgetPd; intuition.
      apply nextEntryIsPPgetFstShadow;intuition.
      assert (pa entry = phyPDChild).
      apply isEntryPageLookupEq with ptPDChild idxPDChild s; trivial.
      intuition.
      subst.
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.      
      apply isAccessibleMappedPage with ptPDChild;trivial. }
    apply getPDFlagReadPDflag with currentShadow1 pdChild currentPart;trivial.
    intuition.  
    apply PeanoNat.Nat.eqb_neq.
    assert(Hfalsepge : (Nat.eqb defaultPage ptPDChildSh1) = false) by trivial.
    apply beq_nat_false in Hfalsepge.
    unfold not;intros Hfalse'.
    rewrite Hfalse' in Hfalsepge.    
    now contradict Hfalsepge.
    intuition.
    intuition.
    intuition. }
    assert (Hreadflagsh1 : isPartitionFalse ptSh1ChildFromSh1 idxSh1 s ).
   { unfold isPartitionFalse.
    unfold consistency in *. 
    assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
    unfold accessibleVAIsNotPartitionDescriptor in *.
    assert (Hflag : getPDFlag currentShadow1 shadow1 s = false).
    { apply Haccessva with currentPart currentPD phySh1Child.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst;assumption.
      apply nextEntryIsPPgetPd; intuition.
      apply nextEntryIsPPgetFstShadow;intuition.  
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.
      apply isAccessibleMappedPage2 with (currentPartition s) ptSh1Child;intuition. }
    apply getPDFlagReadPDflag with currentShadow1 shadow1 currentPart;trivial.
    intuition.  
    apply PeanoNat.Nat.eqb_neq.
    assert(Hfalsepge : (Nat.eqb defaultPage ptSh1ChildFromSh1) = false) by trivial.
    apply beq_nat_false in Hfalsepge.
    unfold not;intros Hfalse'.
    rewrite Hfalse' in Hfalsepge.    
    now contradict Hfalsepge.
    intuition.
    intuition.
    intuition. }
   assert (Hreadflagsh2 : isPartitionFalse childSh2 idxSh2 s ).
   { unfold isPartitionFalse.
    unfold consistency in *. 
    assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
    unfold accessibleVAIsNotPartitionDescriptor in *.
    assert (Hflag : getPDFlag currentShadow1 shadow2 s = false).
    { apply Haccessva with currentPart currentPD phySh2Child.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst;assumption.
      apply nextEntryIsPPgetPd; intuition.
      apply nextEntryIsPPgetFstShadow;intuition.  
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.
      apply isAccessibleMappedPage2 with (currentPartition s) ptSh2Child;intuition. }
    apply getPDFlagReadPDflag with currentShadow1 shadow2 currentPart;trivial.
    intuition.  
    apply PeanoNat.Nat.eqb_neq.
    assert(Hfalsepge : (Nat.eqb defaultPage childSh2) = false) by trivial.
    apply beq_nat_false in Hfalsepge.
    unfold not;intros Hfalse'.
    rewrite Hfalse' in Hfalsepge.    
    now contradict Hfalsepge.
    intuition.
    intuition.
    intuition. }
   assert (Hreadflaglist : isPartitionFalse childListSh1 idxConfigPagesList s ).
   { unfold isPartitionFalse.
    unfold consistency in *. 
    assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
    unfold accessibleVAIsNotPartitionDescriptor in *.
    assert (Hflag : getPDFlag currentShadow1 listparam s = false).
    { apply Haccessva with currentPart currentPD phyConfigPagesList.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst;assumption.
      apply nextEntryIsPPgetPd; intuition.
      apply nextEntryIsPPgetFstShadow;intuition.  
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.
      apply isAccessibleMappedPage2 with (currentPartition s) ptConfigPagesList;intuition. }
    apply getPDFlagReadPDflag with currentShadow1 listparam currentPart;trivial.
    intuition.  
    apply PeanoNat.Nat.eqb_neq.
    assert(Hfalsepge : (Nat.eqb defaultPage childListSh1) = false) by trivial.
    apply beq_nat_false in Hfalsepge.
    unfold not;intros Hfalse'.
    rewrite Hfalse' in Hfalsepge.    
    now contradict Hfalsepge.
    intuition.
    intuition.
    intuition. }
    assert (Hreadflagdesc : isPartitionFalse ptRefChildFromSh1 idxRefChild s ).
   { unfold isPartitionFalse.
    unfold consistency in *. 
    assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
    unfold accessibleVAIsNotPartitionDescriptor in *.
    assert (Hflag : getPDFlag currentShadow1 descChild s = false).
    { apply Haccessva with currentPart currentPD phyDescChild.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst;assumption.
      apply nextEntryIsPPgetPd; intuition.
      apply nextEntryIsPPgetFstShadow;intuition.  
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.
      apply isAccessibleMappedPage2 with (currentPartition s) ptRefChild;intuition. }
    apply getPDFlagReadPDflag with currentShadow1 descChild currentPart;trivial.
    intuition.  
    apply PeanoNat.Nat.eqb_neq.
    assert(Hfalsepge : (Nat.eqb defaultPage ptRefChildFromSh1) = false) by trivial.
    apply beq_nat_false in Hfalsepge.
    unfold not;intros Hfalse'.
    rewrite Hfalse' in Hfalsepge.    
    now contradict Hfalsepge.
    intuition.
    intuition.
    intuition. }
    assert(HpdChildaccess : getAccessibleMappedPage currentPD s pdChild = SomePage phyPDChild).
    { intuition.
      assert(Heqentry : pa entry =phyPDChild).
      apply isEntryPageLookupEq with ptPDChild idxPDChild s;subst;trivial.
      rewrite <- Heqentry in *.
      apply isAccessibleMappedPage with ptPDChild;subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. subst;trivial. 
     (*  repeat rewrite andb_true_iff in Hlegit.
      intuition. 
      subst;trivial. *) }
    assert(Hcurparts : In currentPart (getPartitions multiplexer s)).
    { unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst.
      assumption. }
    assert(Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
    { intuition. subst.
      apply nextEntryIsPPgetPd;trivial. }
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts PPRidx); clear Hpde; intros Hpde.
    
    assert(Hcurentparent : (exists entry : page, nextEntryIsPP currentPart PPRidx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 4 right;left;trivial. }
    clear Hpde.
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts sh2idx); clear Hpde; intros Hpde.
    
    assert(Hcurrentsh2 : (exists entry : page, nextEntryIsPP currentPart sh2idx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 2 right;left;trivial. }
    clear Hpde.
    assert(Hisaccessible : isAccessibleMappedPageInParent currentPart pdChild phyPDChild s = true).
               { assert(Hcons : consistency s).
        {  unfold propagatedProperties in *.  
          intuition. }
        unfold consistency in Hcons.
        assert(Haccess : accessibleChildPageIsAccessibleIntoParent s) by intuition.
        unfold accessibleChildPageIsAccessibleIntoParent in Haccess.
        apply Haccess with currentPD;intuition. }
         do 6 apply and_assoc.
      set (s' := {|
    currentPartition := currentPartition s;
    memory := add ptPDChild idxPDChild
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
     split.
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    apply and_assoc.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros partition1 partition2 Hp1 Hp2.
    assert( getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions in *.
    clear Hpartitions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (Hincl : incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros x Hx.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply Hincl; trivial.
    apply and_assoc.
    split.
  (** Vertical Sharing **)
    unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    apply and_assoc.
    split.
  (** Consistency **) 
    assert (Hcons : consistency s) by intuition.
    unfold consistency in *.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
    split.
    (** partitionDescriptorEntry **)
    apply partitionDescriptorEntryUpdateUserFlag;trivial.
    do 2 rewrite <- and_assoc.
    split.
    (** dataStructurePdSh1Sh2asRoot **)
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    split.
    (** currentPartitionInPartitionsList **)
    unfold currentPartitionInPartitionsList in *.    
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. trivial.
    split.
    (** noDupMappedPagesList **)
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    intuition.
    split.
    (* noDupConfigPagesList **)
(*     apply Hnodupmapped;assumption. *)
    apply getIndirectionsNoDupUpdateUserFlag; intuition.
    split.
    (** parentInPartitionList **)
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    split.
    (** accessibleVAIsNotPartitionDescriptor **)
    unfold s'.
    intuition. 
    subst.
    apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag with level
    (currentPartition s) currentPD ;trivial.
    assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
      isPE ptPDChild idx s /\ 
      getTableAddrRoot ptPDChild PDidx (currentPartition s) pdChild s) by trivial.     
    assert(isPE ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) s /\ 
            getTableAddrRoot ptPDChild PDidx (currentPartition s) pdChild s)
    as (_ & Hi).
    apply Hget; trivial.
    assumption.
    apply isAccessibleMappedPage with ptPDChild;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial. (* 
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial. *)
    (** accessibleChildPageIsAccessibleIntoParent *)
    split.
    intuition.
    subst.
    assert(Htrue : accessibleChildPageIsAccessibleIntoParent s) by intuition.
    unfold s'.
    assert(exists va : vaddr,
        isEntryVA ptPDChildSh1 (StateLib.getIndexOfAddr pdChild fstLevel) va s /\
        beqVAddr defaultVAddr va = derivedPDChild) as 
        (vaInAncestor & HvaInAncestor & Hnotderived) by trivial.
    destruct Hcurentparent as (ancestor & Hancestor & Hancestornotnull).
    assert(Hancestorpart : In ancestor (getPartitions multiplexer s)).
    unfold parentInPartitionList in *.
    apply Hparent with (currentPartition s);trivial.
    assert(Hpde : partitionDescriptorEntry s) by trivial.
    unfold partitionDescriptorEntry in *.
    assert(exists entry : page, nextEntryIsPP ancestor PDidx entry s /\ entry <> defaultPage) as (pdAncestor & Hpdancestor & Hpdancesnotnull).
    apply Hpde;trivial.
    left;trivial.      
    apply accessibleChildPageIsAccessibleIntoParentUpdate with 
    ptPDChildSh1 (currentPartition s) currentPD level;
    trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition;subst;trivial.
    repeat rewrite andb_true_iff in Hderiv.
    intuition;subst;trivial.
    exists vaInAncestor;split;trivial.
    split.
    intuition.
    (* noCycleInPartitionTree *)
    assert(Hdiff : noCycleInPartitionTree s) by trivial.
    unfold noCycleInPartitionTree in *.
    intros parent partition Hparts Hparentpart.
    simpl in *.
    assert (getPartitions multiplexer s'
             = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart in *. clear HgetPart.
    assert(HgetParent : getAncestors partition s' =
    getAncestors partition s). 
    apply getAncestorsUpdateUserFlag;trivial.
    rewrite HgetParent in *; clear HgetParent.
    apply Hdiff;trivial.
    split.
    intuition.
    (* configTablesAreDifferent *)
    assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
    unfold configTablesAreDifferent in *.
    simpl in *.
    fold s'.
    intros partition1 partition2 Hpart1 Hpart2 Hdiff.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart in *. clear HgetPart.
    assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
    apply getConfigPagesUpdateUserFlag;trivial.
    rewrite Hconfig;clear Hconfig.
    assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
    apply getConfigPagesUpdateUserFlag;trivial.
    rewrite Hconfig;clear Hconfig.
    apply Hconfigdiff;trivial.
    split.
    intuition.
    (** isChild **)
    unfold s' in *.
    assert(Hchid : isChild s) by intuition.
    unfold isChild in *.
    simpl in *.
    intros partition parent Hparts Hgetparent.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser;trivial.
    apply Hchid;trivial.
    split.
    (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial. 
    (** physicalPageNotDerived **)
    split.
    apply physicalPageNotDerivedUpdateUserFlag;intuition.
    split.
    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by intuition.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.
    split.  
    (** isParent  *)
    assert(Hisparent : isParent s) by intuition.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    split.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by intuition.
    unfold noDupPartitionTree in *.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    split. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by intuition.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va = Some vainparent).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    split.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by intuition.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh2 s va = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    assert(Hk :  StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild) by intuition.
    rewrite <- Hk.
    apply getVirtualAddressSh2UpdateUserFlag;intuition;subst;trivial.
    split.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by intuition.
    unfold wellFormedShadows in *.
    intros.
    unfold s' in *.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    split.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by intuition.
    unfold wellFormedShadows in *.
    intros.
    unfold s' in *.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** currentPartitionIsNotDefaultPage *)
    intuition.  
    (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by intuition.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    
    fold s'.
    assert(Htmp1 :getPDFlag sh1 va s' = getPDFlag sh1 va s).
    symmetry. 
    apply getPDFlagUpdateUserFlag;trivial.
    assert (Htmp2 :getVirtualAddressSh1 sh1 s' va =
    getVirtualAddressSh1 sh1 s va ).
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    rewrite Htmp1.
    rewrite Htmp2.
    apply Hwell with partition pd ;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by intuition.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    
    fold s'.
    assert(Htmp1 :getPDFlag sh1 va s' = getPDFlag sh1 va s).
    symmetry. 
    apply getPDFlagUpdateUserFlag;trivial.
    assert (Htmp2 :getVirtualAddressSh1 sh1 s' va =
    getVirtualAddressSh1 sh1 s va ).
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    rewrite Htmp1.
    rewrite Htmp2.
    apply Hwell with partition pd ;trivial.
(** Propagated properties **)
    {  intuition try eassumption.     
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);  intros (Htableroot & _). 
        apply isPEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'.
        assert(ptRefChild <> ptPDChild \/ idxRefChild  <>idxPDChild).
        apply toApplyPageTablesOrIndicesAreDifferent with descChild pdChild currentPart
         currentPD PDidx level isPE s; trivial.
         left;trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption. 
     
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
         generalize (Hi idx Hi1); intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(ptSh1Child  <> ptPDChild \/ idxSh1  <>idxPDChild).      
        apply toApplyPageTablesOrIndicesAreDifferent with  shadow1 pdChild currentPart
        currentPD PDidx level isPE s; trivial.
         left;trivial. 
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
         generalize (Hi1 idx Hi2); intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert( ptSh2Child <> ptPDChild \/ idxSh2 <> idxPDChild).
        apply toApplyPageTablesOrIndicesAreDifferent with shadow2
        pdChild   currentPart
        currentPD PDidx level isPE s; trivial.
         left;trivial. 
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr listparam fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart listparam s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr listparam fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr listparam fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart listparam s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr listparam fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(ptConfigPagesList <> ptPDChild \/ idxConfigPagesList <> idxPDChild ).
        apply toApplyPageTablesOrIndicesAreDifferent with listparam
        pdChild   currentPart
        currentPD PDidx level isPE s; trivial.
         left;trivial. 
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind. 
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr listparam fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart listparam s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr listparam fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr listparam fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart listparam s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr listparam fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      *  unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      *  unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      *  unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      *  unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      *  unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.      
      * 
        assert(HisAccess : isAccessibleMappedPageInParent currentPart pdChild phyPDChild s' =
          isAccessibleMappedPageInParent currentPart pdChild phyPDChild s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow currentPart (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt :  getVirtualAddressSh2 p
    {|
    currentPartition := currentPartition s;
    memory := add ptPDChild idxPDChild
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} pdChild
                    =
                            getVirtualAddressSh2 p s pdChild).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some level = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p pdChild level (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s pdChild);
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent currentPart (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
    {|
    currentPartition := currentPartition s;
    memory := add ptPDChild idxPDChild
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} v= 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In p0 (getPartitions multiplexer s)).
                apply Hparentpart with currentPart;trivial.
                apply nextEntryIsPPgetParent; trivial.
                subst.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions 
                with (currentPartition s) p0;trivial.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                        isPE ptPDChild idx s /\ 
                        getTableAddrRoot ptPDChild PDidx (currentPartition s) pdChild s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr pdChild fstLevel)
                as (Hpe & Hroot);
                trivial.
                 
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor;trivial.
                apply nextEntryIsPPgetParent;trivial. }
              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }

              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
      * (** New property **) 
        unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptPDChild, idxPDChild) (ptPDChild, idxPDChild)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity.  }
Qed.

Lemma writePhyEntry2 accessibleChild accessibleSh1 accessibleSh2 accessibleList 
pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
 ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
idxConfigPagesList presentConfigPagesList 
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2
derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild :
presentRefChild && accessibleChild && presentPDChild && true && presentConfigPagesList &&
         accessibleList && presentSh1 && accessibleSh1 && presentSh2 && accessibleSh2 = true -> 
         derivedRefChild && derivedPDChild && derivedSh1Child && derivedSh2Child && derivedRefChildListSh1 = true -> 
{{ fun s : state =>
   propagatedProperties accessibleChild accessibleSh1 accessibleSh2 accessibleList pdChild
     currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
     ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child
     shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList presentConfigPagesList
     currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild
     ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
     derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
     phyDescChild s /\
   (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phyPDChild (getAccessibleMappedPages partition s)) }} 
  MAL.writeAccessible ptSh1Child idxSh1 false {{ fun _ (s : state) => ((propagatedProperties accessibleChild false accessibleSh2 accessibleList pdChild
     currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
     ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child
     shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList presentConfigPagesList
     currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild
     ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
     derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
     phyDescChild s  /\ (forall partition : page,
      In partition (getAncestors currentPart s) ->
      ~ In phyPDChild (getAccessibleMappedPages partition s))) /\
    isAccessibleMappedPageInParent currentPart shadow1 phySh1Child s = true) /\
   entryUserFlag ptSh1Child idxSh1 false s }}.
  Proof.
  intros Hlegit Hderiv.
     eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
    assert (exists entry : Pentry,
      lookup ptSh1Child idxSh1 (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      unfold propagatedProperties in *.
      assert (forall idx : index,
       StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
       isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) as H1 by intuition.
      generalize (H1  idxSh1);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1 ) as H2 by intuition.
      apply H1 in H2. intuition. }
    destruct Hlookup as (entry & Hlookup).
    unfold propagatedProperties in *.
    exists entry ; split;trivial.
(** Here the first shadow is still accessible, so we summarize this property  **)
    assert(HpdChildaccess : getAccessibleMappedPage currentPD s shadow1 = SomePage phySh1Child).
    { intuition.
      assert(Heqentry : pa entry =phySh1Child).
      apply isEntryPageLookupEq with ptSh1Child idxSh1 s;subst;trivial.
      rewrite <- Heqentry in *.
      apply isAccessibleMappedPage with ptSh1Child;subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. 
      subst;trivial. }
    assert(Hcurparts : In currentPart (getPartitions multiplexer s)).
    { unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst.
      assumption. }
    assert(Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
    { intuition. subst.
      apply nextEntryIsPPgetPd;trivial. }
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts PPRidx); clear Hpde; intros Hpde.
    
    assert(Hcurentparent : (exists entry : page, nextEntryIsPP currentPart PPRidx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 4 right;left;trivial. }
    clear Hpde.
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts sh2idx); clear Hpde; intros Hpde.
    
    assert(Hcurrentsh2 : (exists entry : page, nextEntryIsPP currentPart sh2idx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 2 right;left;trivial. }
    clear Hpde.

(** Here the first shadow is still accessible, so we prove that in all ancestor this physical 
page is already accessible **)
     assert(Hisaccessible : isAccessibleMappedPageInParent currentPart shadow1 phySh1Child s = true).
           { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        assert(Haccess : accessibleChildPageIsAccessibleIntoParent s) by intuition.
        unfold accessibleChildPageIsAccessibleIntoParent in Haccess.
        apply Haccess with currentPD;intuition. }
 (*   destruct H0 as (H0 & Hnewpropx).
    do 40 rewrite <- and_assoc in H0.
    destruct H0 as (Hi & Hsplit ). 
    destruct Hi as (Hi & Hfalse). 
    try repeat rewrite and_assoc in Hi.
    assert (Hpost1 :=  conj (conj  Hi Hsplit) Hnewpropx).
    assert (Hpost := conj Hpost1 Hisaccessible).
    pattern s in Hpost.
    match type of Hpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptSh1Child idxSh1 false s)
    end. *)
    simpl.
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add ptSh1Child idxSh1
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
    do 8 rewrite and_assoc.             
    split. 
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions in *.
    clear Hpartitions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H2; trivial.
(** Vertical Sharing **)
    split. unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    split.
 (** Consistency **) 
    assert (Hcons : consistency s) by intuition.
    unfold consistency in *.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
    split.
    (** partitionDescriptorEntry **)
    apply partitionDescriptorEntryUpdateUserFlag;trivial.
    do 2 rewrite <- and_assoc.
    split.
    (** dataStructurePdSh1Sh2asRoot **)
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    split.
    (** currentPartitionInPartitionsList **)
    unfold currentPartitionInPartitionsList in *.    
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. trivial.
    split.
    (** noDupMappedPagesList **)
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    intuition.
    split.
    (* noDupConfigPagesList **)
    apply getIndirectionsNoDupUpdateUserFlag; intuition.
    split.
    (** parentInPartitionList **)
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    split.
    (** accessibleVAIsNotPartitionDescriptor **)
    unfold s'.
    intuition. 
    subst.
    apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag with level
    (currentPartition s) currentPD ;trivial.
    assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
      isPE ptSh1Child idx s /\ 
      getTableAddrRoot ptSh1Child PDidx (currentPartition s) shadow1 s) by trivial.     
    assert(isPE ptSh1Child (StateLib.getIndexOfAddr shadow1 fstLevel) s /\ 
            getTableAddrRoot ptSh1Child PDidx (currentPartition s) shadow1 s)
    as (_ & Hi).
    apply Hget; trivial.
    assumption.
    apply isAccessibleMappedPage with ptSh1Child;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    (** accessibleChildPageIsAccessibleIntoParent *)
    split. intuition.
    subst.
    assert(Htrue : accessibleChildPageIsAccessibleIntoParent s) by intuition.
    unfold s'.
     assert(exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 (StateLib.getIndexOfAddr shadow1 fstLevel) va s /\
        beqVAddr defaultVAddr va = derivedSh1Child) as 
        (vaInAncestor & HvaInAncestor & Hnotderived) by trivial.
   destruct Hcurentparent as (ancestor & Hancestor & Hancestornotnull).
   assert(Hancestorpart : In ancestor (getPartitions multiplexer s)).
   unfold parentInPartitionList in *.
   apply Hparent with (currentPartition s);trivial.
   assert(Hpde : partitionDescriptorEntry s) by trivial.
   unfold partitionDescriptorEntry in *.
   assert(exists entry : page, nextEntryIsPP ancestor PDidx entry s /\ entry <> defaultPage) as (pdAncestor & Hpdancestor & Hpdancesnotnull).
   apply Hpde;trivial.
   left;trivial.
    apply accessibleChildPageIsAccessibleIntoParentUpdate with ptSh1ChildFromSh1
     (currentPartition s) 
    currentPD level;
    trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition;subst;trivial.
    repeat rewrite andb_true_iff in Hderiv.
    intuition;subst;trivial.
    exists vaInAncestor;split;trivial.
    split.
    intuition.
    subst.
    (* noCycleInPartitionTree *)
    assert(Hdiff : noCycleInPartitionTree s) by trivial.
    unfold noCycleInPartitionTree in *.
    intros parent partition Hparts Hparentpart.
    simpl in *.
    assert (getPartitions multiplexer s'
             = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart in *. clear HgetPart.
    assert(HgetParent : getAncestors partition s' =
    getAncestors partition s). 
    apply getAncestorsUpdateUserFlag;trivial.
    rewrite HgetParent in *.
    apply Hdiff;trivial.
    split.
    intuition.
    subst.
    (* configTablesAreDifferent *)
    assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
    unfold configTablesAreDifferent in *.
    simpl in *.
    fold s'.
    intros partition1 partition2 Hpart1 Hpart2 Hdiff.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart in *. clear HgetPart.
    assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
    apply getConfigPagesUpdateUserFlag;trivial.
    rewrite Hconfig;clear Hconfig.
    assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
    apply getConfigPagesUpdateUserFlag;trivial.
    rewrite Hconfig;clear Hconfig.
    apply Hconfigdiff;trivial.   
    split.
    intuition.
    subst.
    (** isChild **)
    unfold s' in *.
    assert(Hchid : isChild s) by intuition.
    unfold isChild in *.
    simpl in *.
    intros partition parent Hparts Hgetparent.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser;trivial.
    apply Hchid;trivial.
    split.
    (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    split.
    (** physicalPageNotDerived **)
    apply physicalPageNotDerivedUpdateUserFlag;intuition.
    split.
    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by intuition.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.
    split.  
    (** isParent  *)
    assert(Hisparent : isParent s) by intuition.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    split.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by intuition.
    unfold noDupPartitionTree in *.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    split. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by intuition.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va = Some vainparent).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    split.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by intuition.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh2 s va = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    assert(Hk :  StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1) by intuition.
    rewrite <- Hk.
    apply getVirtualAddressSh2UpdateUserFlag;intuition;subst;trivial.
    split.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by intuition.
    unfold wellFormedShadows in *.
    intros.
    unfold s' in *.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    split.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by intuition.
    unfold wellFormedShadows in *.
    intros.
    unfold s' in *.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** currentPartitionIsNotDefaultPage *)
    intuition.
      (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by intuition.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    
    fold s'.
    assert(Htmp1 :getPDFlag sh1 va s' = getPDFlag sh1 va s).
    symmetry. 
    apply getPDFlagUpdateUserFlag;trivial.
    assert (Htmp2 :getVirtualAddressSh1 sh1 s' va =
    getVirtualAddressSh1 sh1 s va ).
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    rewrite Htmp1.
    rewrite Htmp2.
    apply Hwell with partition pd ;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by intuition.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    
    fold s'.
    assert(Htmp1 :getPDFlag sh1 va s' = getPDFlag sh1 va s).
    symmetry. 
    apply getPDFlagUpdateUserFlag;trivial.
    assert (Htmp2 :getVirtualAddressSh1 sh1 s' va =
    getVirtualAddressSh1 sh1 s va ).
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    rewrite Htmp1.
    rewrite Htmp2.
    apply Hwell with partition pd ;trivial.
  
(*     clear Hpost.
    rename H into Hcond. 
    assert (H :=  (conj (conj Hpost1 Hfalse) Hsplit)  ).
    clear Hpost1 Hfalse Hsplit . *)
(** Propagated properties **)
    {
      intuition try trivial. 
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); clear H23; intros (H23 & _). 
        apply isPEUpdateUserFlag; assumption.
      *  assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'.
        assert(ptRefChild <> ptSh1Child \/ idxRefChild  <>idxSh1).
        apply toApplyPageTablesOrIndicesAreDifferent with descChild shadow1 currentPart
          currentPD PDidx level isPE s; trivial.
         left;trivial.  
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue; trivial.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptSh1Child, idxSh1) (ptSh1Child, idxSh1) beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'. assert( ptSh2Child <> ptSh1Child \/ idxSh2 <> idxSh1).
        apply toApplyPageTablesOrIndicesAreDifferent with shadow2
        shadow1   currentPart
        currentPD PDidx level isPE s; trivial.
         left;trivial. 
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(ptConfigPagesList <> ptSh1Child \/ idxConfigPagesList <> idxSh1 ).
        apply toApplyPageTablesOrIndicesAreDifferent with list
        shadow1   currentPart
        currentPD PDidx level isPE s; trivial.
         left;trivial. 
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.  
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.  
      * assert(Hanc: getAncestors currentPart s' = getAncestors currentPart s) by
        (apply getAncestorsUpdateUserFlag; trivial).
        rewrite Hanc in *.
        assert(Hfalse : In phyPDChild (getAccessibleMappedPages partition s')) by trivial.
        contradict Hfalse.
        assert(Hnewpropx : forall partition : page,
            In partition (getAncestors currentPart s) ->
            ~ In phyPDChild (getAccessibleMappedPages partition s)) by trivial.
        assert(~ In phyPDChild (getAccessibleMappedPages partition s)).
        { unfold not; intros. apply Hnewpropx with partition; trivial. }
        assert(Hincl : incl
         (getAccessibleMappedPages partition
           s')
         (getAccessibleMappedPages partition s)).
         apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
         unfold incl in *.
         unfold not;intros Hfalse.
        assert(Htrue : ~ In phyPDChild (getAccessibleMappedPages partition s)) by 
        trivial.
        apply Htrue.
        apply Hincl;trivial.
      * assert(HisAccess : isAccessibleMappedPageInParent currentPart shadow1 phySh1Child s' =
          isAccessibleMappedPageInParent currentPart shadow1 phySh1Child s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow currentPart (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt :  getVirtualAddressSh2 p
    {|
    currentPartition := currentPartition s;
    memory := add ptSh1Child idxSh1
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} shadow1
                    =
                            getVirtualAddressSh2 p s shadow1).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some level = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p shadow1 level (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s shadow1);
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent currentPart (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
    {|
    currentPartition := currentPartition s;
    memory := add ptSh1Child idxSh1
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} v= 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In p0 (getPartitions multiplexer s)).
                apply Hparentpart with currentPart;trivial.
                apply nextEntryIsPPgetParent; trivial.
                subst.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions 
                with (currentPartition s) p0;trivial.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                        isPE ptSh1Child idx s /\ 
                        getTableAddrRoot ptSh1Child PDidx (currentPartition s) shadow1 s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr shadow1 fstLevel)
                as (Hpe & Hroot);
                trivial.
              
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor;trivial.
                apply nextEntryIsPPgetParent;trivial. }
              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }

              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
(** New property **) 
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptSh1Child, idxSh1) (ptSh1Child, idxSh1) beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. } 
 Qed.
 
 Lemma writePhyEntry3  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
 ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
idxConfigPagesList presentConfigPagesList 
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2
derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild :
presentRefChild && accessibleChild && presentPDChild && true && presentConfigPagesList &&
         accessibleList && presentSh1 && accessibleSh1 && presentSh2 && accessibleSh2 = true -> 
         derivedRefChild && derivedPDChild && derivedSh1Child && derivedSh2Child && derivedRefChildListSh1 = true -> 
 {{ fun s : state =>
   (propagatedProperties accessibleChild false accessibleSh2 accessibleList pdChild
      currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
      ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child
      shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child
      childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child
      phyConfigPagesList phyDescChild s /\
    (forall partition : page,
     In partition (getAncestors currentPart s) ->
     ~ In phyPDChild (getAccessibleMappedPages partition s))) /\
   (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phySh1Child (getAccessibleMappedPages partition s)) }} 
  MAL.writeAccessible ptSh2Child idxSh2 false {{ fun _ (s : state)  =>
   (((propagatedProperties accessibleChild false false accessibleList pdChild
      currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
      ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child
      shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child
      childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child
      phyConfigPagesList phyDescChild s /\
        isAccessibleMappedPageInParent currentPart shadow2 phySh2Child s = true) /\
     (forall partition : page,
      In partition (getAncestors currentPart s) ->
      ~ In phyPDChild (getAccessibleMappedPages partition s))) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) ->
     ~ In phySh1Child (getAccessibleMappedPages partition s))) /\
   entryUserFlag ptSh2Child idxSh2 false s}}.
   Proof.
   intros Hlegit Hderiv.
       eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
    assert (exists entry : Pentry,
      lookup ptSh2Child idxSh2 (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      unfold propagatedProperties in *.
      assert (forall idx : index,
       StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
       isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) as H1 by intuition.
      generalize (H1  idxSh2);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2 ) as H2 by intuition.
      apply H1 in H2. intuition. }
    destruct Hlookup as (entry & Hlookup).
    unfold propagatedProperties in *.
    exists entry ; split;trivial.
(** Here the first shadow is still accessible, so we summarize this property  **)
    assert(HpdChildaccess : getAccessibleMappedPage currentPD s shadow2 = SomePage phySh2Child).
    { intuition.
      assert(Heqentry : pa entry =phySh2Child).
      apply isEntryPageLookupEq with ptSh2Child idxSh2 s;subst;trivial.
      rewrite <- Heqentry in *.
      apply isAccessibleMappedPage with ptSh2Child;subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. 
      subst;trivial. }
    assert(Hcurparts : In currentPart (getPartitions multiplexer s)).
    { unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst.
      assumption. }
    assert(Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
    { intuition. subst.
      apply nextEntryIsPPgetPd;trivial. }
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts PPRidx); clear Hpde; intros Hpde.
    
    assert(Hcurentparent : (exists entry : page, nextEntryIsPP currentPart PPRidx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 4 right;left;trivial. }
    clear Hpde.
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts sh2idx); clear Hpde; intros Hpde.
    
    assert(Hcurrentsh2 : (exists entry : page, nextEntryIsPP currentPart sh2idx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 2 right;left;trivial. }
    clear Hpde.

(** Here the first shadow is still accessible, so we prove that in all ancestor this physical 
page is already accessible **)
     assert(Hisaccessible : isAccessibleMappedPageInParent currentPart shadow2 phySh2Child s = true).
           { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        assert(Haccess : accessibleChildPageIsAccessibleIntoParent s) by intuition.
        unfold accessibleChildPageIsAccessibleIntoParent in Haccess.
        apply Haccess with currentPD;intuition. }
        (*
    destruct H0 as ((H0 & Hnewpropx )& Hnewpropx1). 
      do 45 rewrite <- and_assoc in H0.

    destruct H0 as (Hi & Hsplit). 
    destruct Hi as (Hi & Hfalse). 
    try repeat rewrite and_assoc in Hi.
    assert (Hpost1 := conj  Hi Hsplit) .
    assert (Hpost :=conj ( conj (conj Hpost1  Hisaccessible)Hnewpropx ) Hnewpropx1).
    pattern s in Hpost.
    match type of Hpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptSh2Child idxSh2 false s)
    end.*)
    simpl.
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add ptSh2Child idxSh2
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
            
        
    do 8 rewrite and_assoc.             
    split. 
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions in *.
    clear Hpartitions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H2; trivial.
(** Vertical Sharing **)
    split. unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    split.
 (** Consistency **) 
    assert (Hcons : consistency s) by intuition. 
    unfold consistency in *.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
    split.
    (** partitionDescriptorEntry **)
    apply partitionDescriptorEntryUpdateUserFlag;trivial.
    do 2 rewrite <- and_assoc.
    split.
    (** dataStructurePdSh1Sh2asRoot **)
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    split.
    (** currentPartitionInPartitionsList **)
    unfold currentPartitionInPartitionsList in *.    
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. trivial.
    split.
    (** noDupMappedPagesList **)
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    intuition.
    split.
    (* noDupConfigPagesList **)
    apply getIndirectionsNoDupUpdateUserFlag; intuition.
    split.
    (** parentInPartitionList **)
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    split.
    (** accessibleVAIsNotPartitionDescriptor **)
    unfold s'. 
    intuition.
    subst.
    apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag with level
    (currentPartition s) currentPD ;trivial.
    assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
      isPE ptSh2Child idx s /\ 
      getTableAddrRoot ptSh2Child PDidx (currentPartition s) shadow2 s) by trivial.     
    assert(isPE ptSh2Child (StateLib.getIndexOfAddr shadow2 fstLevel) s /\ 
            getTableAddrRoot ptSh2Child PDidx (currentPartition s) shadow2 s)
    as (_ & Hi).
    apply Hget; trivial.
    assumption.
    apply isAccessibleMappedPage with ptSh2Child;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    (** accessibleChildPageIsAccessibleIntoParent *)
    split.
    intuition.
    subst.
    assert(Htrue : accessibleChildPageIsAccessibleIntoParent s) by intuition.
    unfold s'.
     assert(exists va : vaddr,
        isEntryVA childSh2 (StateLib.getIndexOfAddr shadow2 fstLevel) va s /\
        beqVAddr defaultVAddr va = derivedSh2Child) as 
        (vaInAncestor & HvaInAncestor & Hnotderived) by trivial.
   destruct Hcurentparent as (ancestor & Hancestor & Hancestornotnull).
   assert(Hancestorpart : In ancestor (getPartitions multiplexer s)).
   unfold parentInPartitionList in *.
   apply Hparent with (currentPartition s);trivial.
   assert(Hpde : partitionDescriptorEntry s) by trivial.
   unfold partitionDescriptorEntry in *.
   assert(exists entry : page, nextEntryIsPP ancestor PDidx entry s /\ entry <> defaultPage) as (pdAncestor & Hpdancestor & Hpdancesnotnull).
   apply Hpde;trivial.
   left;trivial.
      
    apply accessibleChildPageIsAccessibleIntoParentUpdate with childSh2 
    (currentPartition s) currentPD level;
    trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition;subst;trivial.
    repeat rewrite andb_true_iff in Hderiv.
    intuition;subst;trivial.
    exists vaInAncestor;split;trivial.
    split.
    intuition.
    (* noCycleInPartitionTree *)
    assert(Hdiff : noCycleInPartitionTree s) by trivial.
    unfold noCycleInPartitionTree in *.
    intros parent partition Hparts Hparentpart.
    simpl in *.
    assert (getPartitions multiplexer s'
             = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart in *. clear HgetPart.
    assert(HgetParent : getAncestors partition s' =
    getAncestors partition s). 
    apply getAncestorsUpdateUserFlag;trivial.
    rewrite HgetParent in *; clear HgetParent.
    apply Hdiff;trivial.
    split.
    intuition.
    (* configTablesAreDifferent *)
    assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
    unfold configTablesAreDifferent in *.
    simpl in *.
    fold s'.
    intros partition1 partition2 Hpart1 Hpart2 Hdiff.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart in *. clear HgetPart.
    assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
    apply getConfigPagesUpdateUserFlag;trivial.
    rewrite Hconfig;clear Hconfig.
    assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
    apply getConfigPagesUpdateUserFlag;trivial.
    rewrite Hconfig;clear Hconfig.
    apply Hconfigdiff;trivial.   
    split.
    intuition.
    (** isChild **)
    unfold s' in *.
    assert(Hchid : isChild s) by intuition.
    unfold isChild in *.
    simpl in *.
    intros partition parent Hparts Hgetparent.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser;trivial.
    apply Hchid;trivial.
    split.
    (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    split.
    (** physicalPageNotDerived **)
    apply physicalPageNotDerivedUpdateUserFlag;trivial.
    intuition.
    split.
    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by intuition.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.
    split.  
    (** isParent  *)
    assert(Hisparent : isParent s) by intuition.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    split.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by intuition.
    unfold noDupPartitionTree in *.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    split. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by intuition.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va = Some vainparent).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    split.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by intuition.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh2 s va = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    assert(Hk :  StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2) by intuition.
    rewrite <- Hk.
    apply getVirtualAddressSh2UpdateUserFlag;intuition;subst;trivial.
    split.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by intuition.
    unfold wellFormedShadows in *.
    intros.
    unfold s' in *.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    split.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by intuition.
    unfold wellFormedShadows in *.
    intros.
    unfold s' in *.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** currentPartitionIsNotDefaultPage *)
    intuition.  
      (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by intuition.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    
    fold s'.
    assert(Htmp1 :getPDFlag sh1 va s' = getPDFlag sh1 va s).
    symmetry. 
    apply getPDFlagUpdateUserFlag;trivial.
    assert (Htmp2 :getVirtualAddressSh1 sh1 s' va =
    getVirtualAddressSh1 sh1 s va ).
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    rewrite Htmp1.
    rewrite Htmp2.
    apply Hwell with partition pd ;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by intuition.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    
    fold s'.
    assert(Htmp1 :getPDFlag sh1 va s' = getPDFlag sh1 va s).
    symmetry. 
    apply getPDFlagUpdateUserFlag;trivial.
    assert (Htmp2 :getVirtualAddressSh1 sh1 s' va =
    getVirtualAddressSh1 sh1 s va ).
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    rewrite Htmp1.
    rewrite Htmp2.
    apply Hwell with partition pd ;trivial.

    (* 
    clear Hpost.
    rename H into Hcond. 
    assert (H :=  (conj (conj Hpost1 Hfalse) Hsplit) ).
    clear Hpost1 Hfalse Hsplit . *)
(** Propagated properties **)
    { intuition try eassumption. 
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); clear H23; intros (H23 & _). 
        apply isPEUpdateUserFlag; assumption.
      *  assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'.
        assert(ptRefChild <> ptSh2Child \/ idxRefChild  <>idxSh2).
        apply toApplyPageTablesOrIndicesAreDifferent with descChild shadow2 currentPart
         currentPD PDidx level isPE s; trivial.
         left;trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue; trivial.
      *  assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial.  
      * apply entryPresentFlagUpdateUserFlag;assumption.
       * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptSh2Child, idxSh2) (ptSh2Child, idxSh2) beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity.
      *  assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(ptConfigPagesList <> ptSh2Child \/ idxConfigPagesList <> idxSh2 ).
        apply toApplyPageTablesOrIndicesAreDifferent with list
        shadow2   currentPart
        currentPD PDidx level isPE s; trivial.
         left;trivial. 
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * assert(HisAccess : isAccessibleMappedPageInParent currentPart shadow2 phySh2Child s' =
          isAccessibleMappedPageInParent currentPart shadow2 phySh2Child s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow currentPart (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt :  getVirtualAddressSh2 p
    {|
    currentPartition := currentPartition s;
    memory := add ptSh2Child idxSh2
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} shadow2
                    =
                            getVirtualAddressSh2 p s shadow2).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some level = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p shadow2 level (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s shadow2);
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent currentPart (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
    {|
    currentPartition := currentPartition s;
    memory := add ptSh2Child idxSh2
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} v= 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
     assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In p0 (getPartitions multiplexer s)).
                apply Hparentpart with currentPart;trivial.
                apply nextEntryIsPPgetParent; trivial.
                subst.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions 
                with (currentPartition s) p0;trivial.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                        isPE ptSh2Child idx s /\ 
                        getTableAddrRoot ptSh2Child PDidx (currentPartition s) shadow2 s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr shadow2 fstLevel)
                as (Hpe & Hroot);
                trivial.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor;trivial.
                apply nextEntryIsPPgetParent;trivial. }
              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }

              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
      * assert(Hanc: getAncestors currentPart s' = getAncestors currentPart s) by
        (apply getAncestorsUpdateUserFlag; trivial).
        rewrite Hanc in *.
        assert(Hfalse : In phyPDChild (getAccessibleMappedPages partition s')) by trivial.
        contradict Hfalse.
        
        assert(~ In phyPDChild (getAccessibleMappedPages partition s)).
        { unfold not; intros.
          assert(Hnewpropx :  forall partition : page,
                   In partition (getAncestors currentPart s) ->
                   In phyPDChild (getAccessibleMappedPages partition s) -> False) by trivial.
          apply Hnewpropx with partition; trivial. }
        assert(Hincl : incl
         (getAccessibleMappedPages partition
           s')
         (getAccessibleMappedPages partition s)).
         apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
         unfold incl in *.
         unfold not;intros Hfalse.
        assert(Htrue : ~ In phyPDChild (getAccessibleMappedPages partition s)) by 
        trivial.
        apply Htrue.
        apply Hincl;trivial.
      * assert(Hanc: getAncestors currentPart s' = getAncestors currentPart s) by
        (apply getAncestorsUpdateUserFlag; trivial).
        rewrite Hanc in *.
        assert(Hfalse : In phySh1Child (getAccessibleMappedPages partition s')) by trivial.
        contradict Hfalse.
        assert(~ In phySh1Child (getAccessibleMappedPages partition s)).
        { unfold not; intros. 
         assert(Hnewpropx1 :  forall partition : page,
                   In partition (getAncestors currentPart s) ->
                   In phySh1Child (getAccessibleMappedPages partition s) -> False) by trivial.
         apply Hnewpropx1 with partition; trivial. }
        assert(Hincl : incl
         (getAccessibleMappedPages partition
           s')
         (getAccessibleMappedPages partition s)).
         apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
         unfold incl in *.
         unfold not;intros Hfalse.
        assert(Htrue : ~ In phySh1Child (getAccessibleMappedPages partition s)) by 
        trivial.
        apply Htrue.
        apply Hincl;trivial.
(** New property **) 
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptSh2Child, idxSh2) (ptSh2Child, idxSh2) beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. }
        Qed.
 
Lemma writeInaccessibleConfigList accessibleChild accessibleSh1 accessibleSh2 accessibleList 
pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
 ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
idxConfigPagesList presentConfigPagesList 
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2
derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild :
presentRefChild && accessibleChild && presentPDChild && true && presentConfigPagesList &&
         accessibleList && presentSh1 && accessibleSh1 && presentSh2 && accessibleSh2 = true -> 
         derivedRefChild && derivedPDChild && derivedSh1Child && derivedSh2Child && derivedRefChildListSh1 = true -> 
{{ fun s : state =>
   (propagatedProperties accessibleChild false false accessibleList pdChild currentPart currentPD
      level ptRefChild descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild
      ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList
      idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild
      ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child
      childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
      phyDescChild s /\
    (forall partition : page,
     In partition (getAncestors currentPart s) ->
     ~ In phyPDChild (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) ->
     ~ In phySh1Child (getAccessibleMappedPages partition s))) /\
   (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phySh2Child (getAccessibleMappedPages partition s)) }} 
  MAL.writeAccessible ptConfigPagesList idxConfigPagesList false {{ fun _ s =>  (((propagatedProperties accessibleChild false false false pdChild currentPart currentPD
      level ptRefChild descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild
      ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList
      idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild
      ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child
      childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
      phyDescChild s /\     (forall partition : page,
       In partition (getAncestors currentPart s) ->
       ~ In phyPDChild (getAccessibleMappedPages partition s)) /\
      (forall partition : page,
       In partition (getAncestors currentPart s) ->
       ~ In phySh1Child (getAccessibleMappedPages partition s))) /\
     (forall partition : page,
      In partition (getAncestors currentPart s) ->
      ~ In phySh2Child (getAccessibleMappedPages partition s))) /\
    isAccessibleMappedPageInParent currentPart list phyConfigPagesList s = true) /\
   entryUserFlag ptConfigPagesList idxConfigPagesList false s }}  .
  Proof.
  intros Hlegit Hderiv. 
      eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
        assert (exists entry : Pentry,
      lookup ptConfigPagesList idxConfigPagesList (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      unfold propagatedProperties in *.
      assert (forall idx : index,
       StateLib.getIndexOfAddr list fstLevel = idx ->
       isPE ptConfigPagesList idx s /\ 
       getTableAddrRoot ptConfigPagesList PDidx currentPart list s) as H1 by intuition.
      generalize (H1  idxConfigPagesList);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList ) as H2 by intuition.
      apply H1 in H2. intuition. }
    destruct Hlookup as (entry & Hlookup).
    unfold propagatedProperties in *.
    exists entry ; split;trivial.
(** Here the first shadow is still accessible, so we summarize this property  **)
    assert(HpdChildaccess : getAccessibleMappedPage currentPD s list = SomePage phyConfigPagesList).
    { intuition.
      assert(Heqentry : pa entry =phyConfigPagesList).
      apply isEntryPageLookupEq with ptConfigPagesList idxConfigPagesList s;subst;trivial.
      rewrite <- Heqentry in *.
      apply isAccessibleMappedPage with ptConfigPagesList;subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. 
      subst;trivial. }
    assert(Hcurparts : In currentPart (getPartitions multiplexer s)).
    { unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst.
      assumption. }
    assert(Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
    { intuition. subst.
      apply nextEntryIsPPgetPd;trivial. }
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts PPRidx); clear Hpde; intros Hpde.
    
    assert(Hcurentparent : (exists entry : page, nextEntryIsPP currentPart PPRidx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 4 right;left;trivial. }
    clear Hpde.
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts sh2idx); clear Hpde; intros Hpde.
    
    assert(Hcurrentsh2 : (exists entry : page, nextEntryIsPP currentPart sh2idx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 2 right;left;trivial. }
    clear Hpde.

(** Here the first shadow is still accessible, so we prove that in all ancestor this physical 
page is already accessible **)
     assert(Hisaccessible : isAccessibleMappedPageInParent currentPart list phyConfigPagesList s = true).
           { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        assert(Haccess : accessibleChildPageIsAccessibleIntoParent s) by intuition.
        unfold accessibleChildPageIsAccessibleIntoParent in Haccess.
        apply Haccess with currentPD;intuition. }

(*     destruct H0 as ((H0 & Hnew1) & Hnew2 ). 
      do 50 rewrite <- and_assoc in H0.
    destruct H0 as (Hi & Hsplit). 
    destruct Hi as (Hi & Hfalse). 
    try repeat rewrite and_assoc in Hi.
    assert (Hpost1 := conj (conj (conj  Hi Hsplit) Hnew1 ) Hnew2  ).

    assert (Hpost := conj Hpost1  Hisaccessible).
    pattern s in Hpost.
    match type of Hpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptConfigPagesList idxConfigPagesList false s)
    end. *)
    simpl.
   (*  destruct Hnew1 as (Hnew1 & Hnew11).  *)
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add  ptConfigPagesList idxConfigPagesList
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
    do 8 rewrite and_assoc.             
    split. 
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions in *.
    clear Hpartitions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H2; trivial.
(** Vertical Sharing **)
    split. unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    split.
   (** Consistency **) 
    assert (Hcons : consistency s) by intuition. 
    unfold consistency in *.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
    split.
    (** partitionDescriptorEntry **)
    apply partitionDescriptorEntryUpdateUserFlag;trivial.
    do 2 rewrite <- and_assoc.
    split.
    (** dataStructurePdSh1Sh2asRoot **)
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    split.
    (** currentPartitionInPartitionsList **)
    unfold currentPartitionInPartitionsList in *.    
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. trivial.
    split.
    (** noDupMappedPagesList **)
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    intuition.
    split.
    (* noDupConfigPagesList **)
    apply getIndirectionsNoDupUpdateUserFlag; intuition.
    split.
    (** parentInPartitionList **)
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    split.
    (** accessibleVAIsNotPartitionDescriptor **)
    unfold s'. 
    intuition.
    subst.
    apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag with level
    (currentPartition s) currentPD ;trivial.
    assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr list fstLevel = idx ->
      isPE ptConfigPagesList idx s /\ 
      getTableAddrRoot ptConfigPagesList PDidx (currentPartition s) list s) by trivial.     
    assert(isPE ptConfigPagesList (StateLib.getIndexOfAddr list fstLevel) s /\ 
            getTableAddrRoot ptConfigPagesList PDidx (currentPartition s) list s)
    as (_ & Hi).
    apply Hget; trivial.
    assumption.
    apply isAccessibleMappedPage with ptConfigPagesList;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    split.
    intuition.
    (** accessibleChildPageIsAccessibleIntoParent *)
    subst.
    assert(Htrue : accessibleChildPageIsAccessibleIntoParent s) by intuition.
    unfold s'.
    assert(exists va : vaddr,
      isEntryVA childListSh1 (StateLib.getIndexOfAddr list fstLevel) va s /\
      beqVAddr defaultVAddr va = derivedRefChildListSh1) as 
      (vaInAncestor & HvaInAncestor & Hnotderived) by trivial.
    destruct Hcurentparent as (ancestor & Hancestor & Hancestornotnull).
    assert(Hancestorpart : In ancestor (getPartitions multiplexer s)).
    unfold parentInPartitionList in *.
    apply Hparent with (currentPartition s);trivial.
    assert(Hpde : partitionDescriptorEntry s) by trivial.
    unfold partitionDescriptorEntry in *.
    assert(exists entry : page, nextEntryIsPP ancestor PDidx entry s /\ entry <> defaultPage) as (pdAncestor & Hpdancestor & Hpdancesnotnull).
    apply Hpde;trivial.
    left;trivial.      
    apply accessibleChildPageIsAccessibleIntoParentUpdate with  
    childListSh1 (currentPartition s) currentPD level;
    trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition;subst;trivial.
        repeat rewrite andb_true_iff in Hderiv.
    intuition;subst;trivial.
    exists vaInAncestor;split;trivial.
    split.
    intuition.
    (* noCycleInPartitionTree *)
    assert(Hdiff : noCycleInPartitionTree s) by trivial.
    unfold noCycleInPartitionTree in *.
    intros parent partition Hparts Hparentpart.
    simpl in *.
    assert (getPartitions multiplexer s'
             = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart in *. clear HgetPart.
    assert(HgetParent : getAncestors partition s' =
    getAncestors partition s). 
    apply getAncestorsUpdateUserFlag;trivial.
    rewrite HgetParent in *; clear HgetParent.
    apply Hdiff;trivial.
    split.
    intuition.
    (* configTablesAreDifferent *)
    assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
    unfold configTablesAreDifferent in *.
    simpl in *.
    fold s'.
    intros partition1 partition2 Hpart1 Hpart2 Hdiff.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart in *. clear HgetPart.
    assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
    apply getConfigPagesUpdateUserFlag;trivial.
    rewrite Hconfig;clear Hconfig.
    assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
    apply getConfigPagesUpdateUserFlag;trivial.
    rewrite Hconfig;clear Hconfig.
    apply Hconfigdiff;trivial.
    split.
    intuition.
    (** isChild **)
    unfold s' in *.
    assert(Hchid : isChild s) by intuition.
    unfold isChild in *.
    simpl in *.
    intros partition parent Hparts Hgetparent.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser;trivial.
    apply Hchid;trivial.
    split.
    (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    split.
    (** physicalPageNotDerived **)
    apply physicalPageNotDerivedUpdateUserFlag;trivial.
    intuition.
    split.
    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by intuition.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.
    split.  
    (** isParent  *)
    assert(Hisparent : isParent s) by intuition.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    split.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by intuition.
    unfold noDupPartitionTree in *.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    split. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by intuition.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va = Some vainparent).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    split.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by intuition.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh2 s va = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    assert(Hk :  StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList) by intuition.
    rewrite <- Hk.
    apply getVirtualAddressSh2UpdateUserFlag;intuition;subst;trivial.
    split.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by intuition.
    unfold wellFormedShadows in *.
    intros.
    unfold s' in *.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    split.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by intuition.
    unfold wellFormedShadows in *.
    intros.
    unfold s' in *.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** currentPartitionIsNotDefaultPage *)
    intuition. 
      (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by intuition.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    
    fold s'.
    assert(Htmp1 :getPDFlag sh1 va s' = getPDFlag sh1 va s).
    symmetry. 
    apply getPDFlagUpdateUserFlag;trivial.
    assert (Htmp2 :getVirtualAddressSh1 sh1 s' va =
    getVirtualAddressSh1 sh1 s va ).
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    rewrite Htmp1.
    rewrite Htmp2.
    apply Hwell with partition pd ;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by intuition.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    
    fold s'.
    assert(Htmp1 :getPDFlag sh1 va s' = getPDFlag sh1 va s).
    symmetry. 
    apply getPDFlagUpdateUserFlag;trivial.
    assert (Htmp2 :getVirtualAddressSh1 sh1 s' va =
    getVirtualAddressSh1 sh1 s va ).
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    rewrite Htmp1.
    rewrite Htmp2.
    apply Hwell with partition pd ;trivial.
(* 
    clear Hpost.
    rename H into Hcond. 
    assert (H := conj (conj  Hpost1 Hfalse) Hsplit) .
    clear Hpost1 Hfalse Hsplit . *)
(** Propagated properties **)
    { intuition try eassumption. 
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); clear H23; intros (H23 & _). 
        apply isPEUpdateUserFlag; assumption.
      *  assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'.
        assert(ptRefChild <> ptConfigPagesList \/ idxRefChild  <>idxConfigPagesList).
        apply toApplyPageTablesOrIndicesAreDifferent with descChild list currentPart
          currentPD PDidx level isPE s; trivial.
         left;trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptConfigPagesList, idxConfigPagesList) (ptConfigPagesList, idxConfigPagesList)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.      
      * assert(Hanc: getAncestors currentPart s' = getAncestors currentPart s) by
        (apply getAncestorsUpdateUserFlag; trivial).
        rewrite Hanc in *.
        assert(Hfalse : In phyPDChild (getAccessibleMappedPages partition s')) by trivial.
        contradict Hfalse.
        assert(Hnew1 : forall partition : page,
    In partition (getAncestors currentPart s) ->
    In phyPDChild (getAccessibleMappedPages partition s) -> False) by trivial.
        assert(~ In phyPDChild (getAccessibleMappedPages partition s)).
        { unfold not; intros. apply Hnew1 with partition; trivial. }
        assert(Hincl : incl
         (getAccessibleMappedPages partition
           s')
         (getAccessibleMappedPages partition s)).
         apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
         unfold incl in *.
         unfold not;intros Hfalse.
        assert(Htrue : ~ In phyPDChild (getAccessibleMappedPages partition s)) by 
        trivial.
        apply Htrue.
        apply Hincl;trivial.
      * assert(Hanc: getAncestors currentPart s' = getAncestors currentPart s) by
        (apply getAncestorsUpdateUserFlag; trivial).
        rewrite Hanc in *.
         assert(Hnew11 : forall partition : page,
    In partition (getAncestors currentPart s) ->
    In phySh1Child (getAccessibleMappedPages partition s) -> False) by trivial.
        assert(Hfalse : In phySh1Child (getAccessibleMappedPages partition s')) by trivial.
        contradict Hfalse.
        assert(~ In phySh1Child (getAccessibleMappedPages partition s)).
        { unfold not; intros. apply Hnew11 with partition; trivial. }
        assert(Hincl : incl
         (getAccessibleMappedPages partition
           s')
         (getAccessibleMappedPages partition s)).
         apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
         unfold incl in *.
         unfold not;intros Hfalse.
        assert(Htrue : ~ In phySh1Child (getAccessibleMappedPages partition s)) by 
        trivial.
        apply Htrue.
        apply Hincl;trivial.
      * assert(Hanc: getAncestors currentPart s' = getAncestors currentPart s) by
        (apply getAncestorsUpdateUserFlag; trivial).
        rewrite Hanc in *.
        assert(Hnew2 : forall partition : page,
    In partition (getAncestors currentPart s) ->
    In phySh2Child (getAccessibleMappedPages partition s) -> False) by trivial.
        assert(Hfalse : In phySh2Child (getAccessibleMappedPages partition s')) by trivial.
        contradict Hfalse.
        assert(~ In phySh2Child (getAccessibleMappedPages partition s)).
        { unfold not; intros. apply Hnew2 with partition; trivial. }
        assert(Hincl : incl
         (getAccessibleMappedPages partition
           s')
         (getAccessibleMappedPages partition s)).
         apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
         unfold incl in *.
         unfold not;intros Hfalse.
        assert(Htrue : ~ In phySh2Child (getAccessibleMappedPages partition s)) by 
        trivial.
        apply Htrue.
        apply Hincl;trivial.
      * assert(HisAccess : isAccessibleMappedPageInParent currentPart list phyConfigPagesList s' =
          isAccessibleMappedPageInParent currentPart list phyConfigPagesList s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow currentPart (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt :  getVirtualAddressSh2 p
    {|
    currentPartition := currentPartition s;
    memory := add ptConfigPagesList idxConfigPagesList
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} list
                    =
                            getVirtualAddressSh2 p s list).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some level = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p list level (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s list);
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent currentPart (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
    {|
    currentPartition := currentPartition s;
    memory := add ptConfigPagesList idxConfigPagesList
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} v= 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In p0 (getPartitions multiplexer s)).
                apply Hparentpart with currentPart;trivial.
                apply nextEntryIsPPgetParent; trivial.
                subst.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions 
                with (currentPartition s) p0;trivial.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr list fstLevel = idx ->
                        isPE ptConfigPagesList idx s /\ 
                        getTableAddrRoot ptConfigPagesList PDidx (currentPartition s) list s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr list fstLevel)
                as (Hpe & Hroot);
                trivial.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor;trivial.
                apply nextEntryIsPPgetParent;trivial. }
              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }

              rewrite Haccessible;trivial.
              assumption. }
                        rewrite HisAccess.
          assumption.
      
 (** New property **) 
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptConfigPagesList, idxConfigPagesList) (ptConfigPagesList, idxConfigPagesList)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. }
Qed.

Lemma writeInaccessibleDescChild  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
 ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
idxConfigPagesList presentConfigPagesList 
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2
derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild :
presentRefChild && accessibleChild && presentPDChild && true && presentConfigPagesList &&
         accessibleList && presentSh1 && accessibleSh1 && presentSh2 && accessibleSh2 = true -> 
         derivedRefChild && derivedPDChild && derivedSh1Child && derivedSh2Child && derivedRefChildListSh1 = true -> 
{{ fun s : state =>
   (propagatedProperties accessibleChild false false false pdChild currentPart currentPD level
      ptRefChild descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child
      shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList
      idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild
      ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child
      childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
      phyDescChild s /\
    ((forall partition : page,
      In partition (getAncestors currentPart s) ->
      ~ In phyPDChild (getAccessibleMappedPages partition s)) /\
     (forall partition : page,
      In partition (getAncestors currentPart s) ->
      ~ In phySh1Child (getAccessibleMappedPages partition s))) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) ->
     ~ In phySh2Child (getAccessibleMappedPages partition s))) /\
   (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phyConfigPagesList (getAccessibleMappedPages partition s)) }} 
  MAL.writeAccessible ptRefChild idxRefChild false {{   fun _ s => (((propagatedProperties false false false false pdChild currentPart currentPD level
      ptRefChild descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child
      shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList
      idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild
      ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child
      childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
      phyDescChild s /\    ((forall partition : page,
        In partition (getAncestors currentPart s) ->
        ~ In phyPDChild (getAccessibleMappedPages partition s)) /\
       (forall partition : page,
        In partition (getAncestors currentPart s) ->
        ~ In phySh1Child (getAccessibleMappedPages partition s))) /\
      (forall partition : page,
       In partition (getAncestors currentPart s) ->
       ~ In phySh2Child (getAccessibleMappedPages partition s))) /\
     (forall partition : page,
      In partition (getAncestors currentPart s) ->
      ~ In phyConfigPagesList (getAccessibleMappedPages partition s))) /\
    isAccessibleMappedPageInParent currentPart descChild phyDescChild s = true) /\
   entryUserFlag ptRefChild idxRefChild false s }}.
 Proof.
 intros Hlegit Hderiv. 
      eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
    assert (exists entry : Pentry,
      lookup ptRefChild idxRefChild (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      unfold propagatedProperties in *.
      assert (forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isPE ptRefChild idx s /\ 
       getTableAddrRoot ptRefChild PDidx currentPart descChild s) as H1 by intuition.
      generalize (H1  idxRefChild);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr descChild fstLevel = idxRefChild ) as H2 by intuition.
      apply H1 in H2. intuition. }
    destruct Hlookup as (entry & Hlookup).
    unfold propagatedProperties in *.
    exists entry ; split;trivial.
(** Here the first shadow is still accessible, so we summarize this property  **)
    assert(HpdChildaccess : getAccessibleMappedPage currentPD s descChild = SomePage phyDescChild).
    { intuition.
      assert(Heqentry : pa entry =phyDescChild).
      apply isEntryPageLookupEq with ptRefChild idxRefChild s;subst;trivial.
      rewrite <- Heqentry in *.
      apply isAccessibleMappedPage with ptRefChild;subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. subst;trivial.
      repeat rewrite andb_true_iff in Hlegit.
      intuition. 
      subst;trivial. }
    assert(Hcurparts : In currentPart (getPartitions multiplexer s)).
    { unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      subst.
      assumption. }
    assert(Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
    { intuition. subst.
      apply nextEntryIsPPgetPd;trivial. }
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts PPRidx); clear Hpde; intros Hpde.
    
    assert(Hcurentparent : (exists entry : page, nextEntryIsPP currentPart PPRidx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 4 right;left;trivial. }
    clear Hpde.
    assert (Hpde : partitionDescriptorEntry s).
    { unfold consistency in *. intuition. }
    unfold partitionDescriptorEntry in *.
    generalize (Hpde currentPart Hcurparts sh2idx); clear Hpde; intros Hpde.
    
    assert(Hcurrentsh2 : (exists entry : page, nextEntryIsPP currentPart sh2idx entry s /\
     entry <> defaultPage) ).
    { apply Hpde.
      do 2 right;left;trivial. }
    clear Hpde.

(** Here the first shadow is still accessible, so we prove that in all ancestor this physical 
page is already accessible **)
     assert(Hisaccessible : isAccessibleMappedPageInParent currentPart descChild phyDescChild s = true).
           { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        assert(Haccess : accessibleChildPageIsAccessibleIntoParent s) by intuition.
        unfold accessibleChildPageIsAccessibleIntoParent in Haccess.
        apply Haccess with currentPD;intuition. }
   (*
    destruct H0  as ((H0 & Hnew)&Hnew1).
      do 30 rewrite <- and_assoc in H0.
    destruct H0 as (Hi & Hsplit). 
    destruct Hi as (Hi & Hfalse). 
    try repeat rewrite and_assoc in Hi.
    assert (Hpost1 :=conj( conj (conj  Hi Hsplit) Hnew ) Hnew1)  .
    assert (Hpost := conj Hpost1 Hisaccessible).
    
    pattern s in Hpost.
    match type of Hpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptRefChild idxRefChild false s)
    end.
    simpl. *)
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add  ptRefChild idxRefChild
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
    do 8 rewrite and_assoc.
     destruct H  as ((H0 & Hnew)&Hnew1).
    destruct Hnew as ((Hnew & Hnew2) & Hnew3).
    split. 
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartitions in *.
    clear Hpartitions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H2; trivial.
(** Vertical Sharing **)
    split. unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. clear Hpartitions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    split.
   (** Consistency **) 
    assert (Hcons : consistency s) by intuition.
    unfold consistency in *.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
    split.
    (** partitionDescriptorEntry **)
    apply partitionDescriptorEntryUpdateUserFlag;trivial.
    do 2 rewrite <- and_assoc.
    split.
    (** dataStructurePdSh1Sh2asRoot **)
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    split.
    (** currentPartitionInPartitionsList **)
    unfold currentPartitionInPartitionsList in *.    
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartitions. trivial.
    split.
    (** noDupMappedPagesList **)
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    intuition.
    split.
    (* noDupConfigPagesList **)
    apply getIndirectionsNoDupUpdateUserFlag; intuition.
    split.
    (** parentInPartitionList **)
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    split.
    (** accessibleVAIsNotPartitionDescriptor **)
    unfold s'. 
    intuition.
    subst.
    apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag with level
    (currentPartition s) currentPD ;trivial.
    assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr descChild fstLevel = idx ->
      isPE ptRefChild idx s /\ 
      getTableAddrRoot ptRefChild PDidx (currentPartition s) descChild s) by trivial.     
    assert(isPE ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) s /\ 
            getTableAddrRoot ptRefChild PDidx (currentPartition s) descChild s)
    as (_ & Hi).
    apply Hget; trivial.
    assumption.
    apply isAccessibleMappedPage with ptRefChild;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    split.
    intuition.
    (** accessibleChildPageIsAccessibleIntoParent *)
    subst.
    assert(Htrue : accessibleChildPageIsAccessibleIntoParent s) by intuition.
    unfold s'.
    assert(exists va : vaddr,
        isEntryVA ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) va s /\
        beqVAddr defaultVAddr va = derivedRefChild) as 
      (vaInAncestor & HvaInAncestor & Hnotderived) by trivial.
    destruct Hcurentparent as (ancestor & Hancestor & Hancestornotnull).
    assert(Hancestorpart : In ancestor (getPartitions multiplexer s)).
    unfold parentInPartitionList in *.
    apply Hparent with (currentPartition s);trivial.
    assert(Hpde : partitionDescriptorEntry s) by trivial.
    unfold partitionDescriptorEntry in *.
    assert(exists entry : page, nextEntryIsPP ancestor PDidx entry s /\ entry <> defaultPage) as (pdAncestor & Hpdancestor & Hpdancesnotnull).
    apply Hpde;trivial.
    left;trivial.      
    apply accessibleChildPageIsAccessibleIntoParentUpdate with  
    ptRefChildFromSh1 (currentPartition s) currentPD level;
    trivial.
    repeat rewrite andb_true_iff in Hlegit.
    intuition;subst;trivial.
    move Hderiv at bottom.
    repeat rewrite andb_true_iff in Hderiv.
    intuition;subst;trivial.
    exists vaInAncestor;split;trivial.
    split.
    intuition.
    (* noCycleInPartitionTree *)
    assert(Hdiff : noCycleInPartitionTree s) by trivial.
    unfold noCycleInPartitionTree in *.
    intros parent partition Hparts Hparentpart.
    simpl in *.
    assert (getPartitions multiplexer s'
             = getPartitions multiplexer s) as HgetPart.
             

    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart in *. clear HgetPart.
       assert(HgetParent : getAncestors partition s' =
    getAncestors partition s). 
    apply getAncestorsUpdateUserFlag;trivial.
    rewrite HgetParent in *; clear HgetParent.
    apply Hdiff;trivial.
    split.
    intuition.
    (* configTablesAreDifferent *)
    assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
    unfold configTablesAreDifferent in *.
    simpl in *.
    fold s'.
    intros partition1 partition2 Hpart1 Hpart2 Hdiff.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart in *. clear HgetPart.
    assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
    apply getConfigPagesUpdateUserFlag;trivial.
    rewrite Hconfig;clear Hconfig.
    assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
    apply getConfigPagesUpdateUserFlag;trivial.
    rewrite Hconfig;clear Hconfig.
    apply Hconfigdiff;trivial.  
    split.
    intuition.
    (** isChild **)
    unfold s' in *.
    assert(Hchid : isChild s) by intuition.
    unfold isChild in *.
    simpl in *.
    intros partition parent Hparts Hgetparent.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser;trivial.
    apply Hchid;trivial.
    split.
    (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    split.
    (** physicalPageNotDerived **)
    apply physicalPageNotDerivedUpdateUserFlag;trivial.
    intuition.
    split.
    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by intuition.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.
    split.  
    (** isParent  *)
    assert(Hisparent : isParent s) by intuition.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    split.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by intuition.
    unfold noDupPartitionTree in *.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    split. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by intuition.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va = Some vainparent).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    split.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by intuition.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh2 s va = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    assert(Hk :  StateLib.getIndexOfAddr descChild fstLevel = idxRefChild) by intuition.
    rewrite <- Hk.
    apply getVirtualAddressSh2UpdateUserFlag;intuition;subst;trivial.
    split.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by intuition.
    unfold wellFormedShadows in *.
    intros.
    unfold s' in *.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    split.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by intuition.
    unfold wellFormedShadows in *.
    intros.
    unfold s' in *.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** currentPartitionIsNotDefaultPage *)
    intuition.
      (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by intuition.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    
    fold s'.
    assert(Htmp1 :getPDFlag sh1 va s' = getPDFlag sh1 va s).
    symmetry. 
    apply getPDFlagUpdateUserFlag;trivial.
    assert (Htmp2 :getVirtualAddressSh1 sh1 s' va =
    getVirtualAddressSh1 sh1 s va ).
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    rewrite Htmp1.
    rewrite Htmp2.
    apply Hwell with partition pd ;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by intuition.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    unfold s' in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    
    fold s'.
    assert(Htmp1 :getPDFlag sh1 va s' = getPDFlag sh1 va s).
    symmetry. 
    apply getPDFlagUpdateUserFlag;trivial.
    assert (Htmp2 :getVirtualAddressSh1 sh1 s' va =
    getVirtualAddressSh1 sh1 s va ).
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    rewrite Htmp1.
    rewrite Htmp2.
    apply Hwell with partition pd ;trivial.
(** Propagated properties **)
    { intuition try eassumption. 
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); clear H23; intros (H23 & _). 
        apply isPEUpdateUserFlag; assumption.
      *  assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptRefChild, idxRefChild) (ptRefChild, idxRefChild)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. 
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial.  
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply entryUserFlagUpdateUserFlagSameValue;trivial.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse' : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse' : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse' : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial.
      * assert (Hfalse' : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
     
      (* assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        left;trivial. *)
        
      *  
        (* assert (Hfalse : In phyDescChild (getConfigPages partition s')); trivial.
        contradict Hfalse. *)
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv in *. (* 
        unfold not.
        intros. *)
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartitions in *. assumption.
        unfold getConfigPages in *.  rewrite Hconfiginv in *. simpl in *.
        trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      * unfold isPartitionFalse; unfold s'; cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
      * assert(Hanc: getAncestors currentPart s' = getAncestors currentPart s) by
        (apply getAncestorsUpdateUserFlag; trivial).
        rewrite Hanc in *.
        assert(Hfalse : In phyPDChild (getAccessibleMappedPages partition s')) by intuition.
        contradict Hfalse.
        assert(~ In phyPDChild (getAccessibleMappedPages partition s)).
        { unfold not; intros. apply Hnew with partition; trivial. }
        assert(Hincl : incl
         (getAccessibleMappedPages partition
           s')
         (getAccessibleMappedPages partition s)).
         apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
         unfold incl in *.
         unfold not;intros Hfalse.
        assert(Htrue : ~ In phyPDChild (getAccessibleMappedPages partition s)) by 
        trivial.
        apply Htrue.
        apply Hincl;trivial.
      * assert(Hanc: getAncestors currentPart s' = getAncestors currentPart s) by
        (apply getAncestorsUpdateUserFlag; trivial).
        rewrite Hanc in *.
        assert(Hfalse : In phySh1Child (getAccessibleMappedPages partition s')) by trivial.
        contradict Hfalse.
        assert(~ In phySh1Child (getAccessibleMappedPages partition s)).
        { unfold not; intros. apply Hnew2 with partition; trivial. }
        assert(Hincl : incl
         (getAccessibleMappedPages partition
           s')
         (getAccessibleMappedPages partition s)).
         apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
         unfold incl in *.
         unfold not;intros Hfalse.
        assert(Htrue : ~ In phySh1Child (getAccessibleMappedPages partition s)) by 
        trivial.
        apply Htrue.
        apply Hincl;trivial.
      * assert(Hanc: getAncestors currentPart s' = getAncestors currentPart s) by
        (apply getAncestorsUpdateUserFlag; trivial).
        rewrite Hanc in *.
        assert(Hfalse : In phySh2Child (getAccessibleMappedPages partition s')) by trivial.
        contradict Hfalse.
        assert(~ In phySh2Child (getAccessibleMappedPages partition s)).
        { unfold not; intros. apply Hnew3 with partition; trivial. }
        assert(Hincl : incl
         (getAccessibleMappedPages partition
           s')
         (getAccessibleMappedPages partition s)).
         apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
         unfold incl in *.
         unfold not;intros Hfalse.
        assert(Htrue : ~ In phySh2Child (getAccessibleMappedPages partition s)) by 
        trivial.
        apply Htrue. 
        apply Hincl;trivial.
     * assert(Hanc: getAncestors currentPart s' = getAncestors currentPart s) by
        (apply getAncestorsUpdateUserFlag; trivial).
        rewrite Hanc in *.
        assert(Hfalse : In phyConfigPagesList (getAccessibleMappedPages partition s')) by trivial.
        contradict Hfalse.
        assert(~ In phyConfigPagesList (getAccessibleMappedPages partition s)).
        { unfold not; intros. apply Hnew1 with partition; trivial. }
        assert(Hincl : incl
         (getAccessibleMappedPages partition
           s')
         (getAccessibleMappedPages partition s)).
         apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
         unfold incl in *.
         unfold not;intros Hfalse.
        assert(Htrue : ~ In phyConfigPagesList (getAccessibleMappedPages partition s)) by 
        trivial.
        apply Htrue. 
        apply Hincl;trivial.
      * assert(HisAccess : isAccessibleMappedPageInParent currentPart descChild phyDescChild s' =
          isAccessibleMappedPageInParent currentPart descChild phyDescChild s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow currentPart (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt :  getVirtualAddressSh2 p
    {|
    currentPartition := currentPartition s;
    memory := add ptRefChild idxRefChild
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} descChild
                    =
                            getVirtualAddressSh2 p s descChild).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some level = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p descChild level (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s descChild);
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent currentPart (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
    {|
    currentPartition := currentPartition s;
    memory := add ptRefChild idxRefChild
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} v= 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In p0 (getPartitions multiplexer s)).
                apply Hparentpart with currentPart;trivial.
                apply nextEntryIsPPgetParent; trivial.
                subst.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions 
                with (currentPartition s) p0;trivial.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr descChild fstLevel = idx ->
                        isPE ptRefChild idx s /\ 
                        getTableAddrRoot ptRefChild PDidx (currentPartition s) descChild s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr descChild fstLevel)
                as (Hpe & Hroot);
                trivial.
              
                            unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor;trivial.
                apply nextEntryIsPPgetParent;trivial. }

              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }

              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
(** New property **) 
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptRefChild, idxRefChild) (ptRefChild, idxRefChild)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. }
Qed.