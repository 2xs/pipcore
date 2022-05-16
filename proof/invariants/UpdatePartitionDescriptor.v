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

(** * Summary 
    This file contains several invariants of [updatePartitionDescriptor]  *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Internal.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.Isolation
               Pip.Proof.InternalLemmas Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Invariants PropagatedProperties UpdateMappedPageContent.
Import Bool Coq.Logic.ProofIrrelevance EqNat List.

Lemma initConfigPagesListPostConditionUpdateMappedPageContent phyConfigPagesList s table1 PRidxsucc  x:
initConfigPagesListPostCondition phyConfigPagesList s ->
table1 <> phyConfigPagesList ->
     initConfigPagesListPostCondition phyConfigPagesList
{|
currentPartition := currentPartition s;
memory := add table1 PRidxsucc x (memory s) pageEq idxEq |}.
Proof.
intro Hgoal.
intros.
unfold initConfigPagesListPostCondition in *.
split.
assert (Htable : StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some pageDefault)
by intuition.
rewrite <- Htable.
apply readPhysicalUpdateMappedPageData; trivial.  split.
intros.
simpl.
assert (Htable : StateLib.readVirtual phyConfigPagesList (CIndex (tableSize - 2)) (memory s) = Some vaddrDefault)
by intuition.
rewrite <- Htable.
apply readVirtualUpdateMappedPageData; trivial.
split.
intros idx Ha1 Ha2 Ha3.
assert (Htable : (forall idx : index,
          PeanoNat.Nat.Odd idx ->
          idx > CIndex 1 ->
          idx < CIndex (tableSize - 2) ->
          exists idxValue : index,
           StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue))
by intuition.
generalize (Htable idx Ha1 Ha2 Ha3 );clear Htable;intros Htable.
destruct Htable as (idxValue & Htable).
exists idxValue;simpl.
rewrite <- Htable.
apply readIndexUpdateMappedPageData; trivial.
assert(Htable : (forall idx : index,
          PeanoNat.Nat.Even idx ->
          idx > CIndex 1 ->
          idx < CIndex (tableSize - 2) ->
          StateLib.readVirtual phyConfigPagesList idx (memory s) = Some vaddrDefault) ) by intuition.
intros.
simpl.
rewrite <-Htable with idx;trivial.
apply readVirtualUpdateMappedPageData; trivial.
Qed.


Lemma updatePartitionDescriptorPropagatedProperties 

(idxroot : index) table1 idxVa1 pt1 va1  value1 value2 zero nullv presentConfigPagesList 
          presentPDChild presentRefChild presentSh1 presentSh2 pdChild currentPart 
          currentPD level ptRefChild descChild idxRefChild ptPDChild
          idxPDChild ptSh1Child shadow1 idxSh1  ptSh2Child shadow2 idxSh2 ptConfigPagesList
          idxConfigPagesList  currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild
          ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild
          phySh1Child phySh2Child phyConfigPagesList phyDescChild  idxPR idxPD idxSH1 idxSH2 idxSH3
        idxPPR  : 
presentRefChild = true  /\ presentPDChild = true  /\
presentConfigPagesList = true /\ presentSh1 = true /\ presentSh2 = true -> 
{{ fun s : state =>
  (propagatedProperties  false false false false
   pdChild currentPart currentPD level ptRefChild descChild idxRefChild true ptPDChild idxPDChild
      true ptSh1Child shadow1 idxSh1 true ptSh2Child shadow2 idxSh2 true ptConfigPagesList idxConfigPagesList true
      currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child
      childSh2 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child
      phyConfigPagesList phyDescChild s /\ (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phyPDChild (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phySh1Child (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phySh2Child (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) ->
     ~ In phyConfigPagesList (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phyDescChild (getAccessibleMappedPages partition s)) /\
    zero = CIndex 0 /\
    isWellFormedSndShadow level phySh2Child s /\
    isWellFormedFstShadow level phySh1Child s /\
    (forall idx : index,
     StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\
     StateLib.readPresent phyPDChild idx (memory s) = Some false) /\
initConfigPagesListPostCondition phyConfigPagesList s /\
    nullv = vaddrDefault /\ idxPR = idxPartDesc /\ idxPD = idxPageDir /\ idxSH1 = idxShadow1 /\ idxSH2 = idxShadow2 /\ idxSH3 = idxShadow3) /\
   idxPPR = idxParentDesc  /\
   (forall partition : page,
          In partition (getPartitions pageRootPartition s) ->
          partition = table1 \/ In table1 (getConfigPagesAux partition s) ->False) /\ 
   (Nat.eqb pageDefault table1) = false /\
   isEntryPage pt1 idxVa1 table1 s /\
   StateLib.getIndexOfAddr va1 levelMin = idxVa1 /\
   (forall idx : index,
        StateLib.getIndexOfAddr va1 levelMin = idx ->
        isPE pt1 idx s /\ getTableAddrRoot pt1 idxPageDir (currentPartition s) va1 s) /\
  entryPresentFlag pt1 idxVa1 true s  /\
  false = StateLib.checkVAddrsEqualityWOOffset nbLevel va1 pdChild level /\
  false = StateLib.checkVAddrsEqualityWOOffset nbLevel va1 shadow1 level /\
  false = StateLib.checkVAddrsEqualityWOOffset nbLevel va1 shadow2 level /\
  false = StateLib.checkVAddrsEqualityWOOffset nbLevel va1 list level /\
  nextEntryIsPP (currentPartition s) idxPageDir currentPD s /\
  (Nat.eqb pageDefault pt1) = false /\
  idxroot < tableSize - 1 }} 

Internal.updatePartitionDescriptor table1 idxroot value1 value2 
{{ fun _ s  =>
     (propagatedProperties  false false false false
     pdChild currentPart currentPD level ptRefChild descChild idxRefChild true ptPDChild idxPDChild
      true ptSh1Child shadow1 idxSh1 true ptSh2Child shadow2 idxSh2 true ptConfigPagesList idxConfigPagesList true
      currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child
      childSh2 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child
      phyConfigPagesList phyDescChild s /\  (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phyPDChild (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phySh1Child (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phySh2Child (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) ->
     ~ In phyConfigPagesList (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phyDescChild (getAccessibleMappedPages partition s)) /\
    zero = CIndex 0 /\
    isWellFormedSndShadow level phySh2Child s /\
    isWellFormedFstShadow level phySh1Child s /\
    (forall idx : index,
     StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\
     StateLib.readPresent phyPDChild idx (memory s) = Some false) /\
    initConfigPagesListPostCondition phyConfigPagesList s   /\
    nullv = vaddrDefault /\ idxPR = idxPartDesc /\ idxPD = idxPageDir /\ idxSH1 = idxShadow1 /\ idxSH2 = idxShadow2 /\ idxSH3 = idxShadow3) /\
   idxPPR = idxParentDesc   }}.
Proof.
intros Hlegit.
unfold updatePartitionDescriptor.
eapply bindRev.
(** writeVirtual **)
   eapply weaken.
   eapply WP.writeVirtual.
   simpl;intros.
   try repeat rewrite and_assoc in H.
    subst. 
   pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s )
    end.
   simpl in *.
   split.
   intuition.
    apply propagatedPropertiesUpdateMappedPageData; trivial.
   unfold propagatedProperties in *.  
   assert(Hcurpart1 : In currentPart (getPartitions pageRootPartition s)).
   {unfold consistency in *. 
   intuition; 
   subst;
   unfold currentPartitionInPartitionsList in *;   
   subst;intuition. }
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition.  (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*)  
    split.
    intuition.
  assert(getPartitions pageRootPartition {|
      currentPartition := currentPartition s;
      memory := add table1 idxroot (VA value2) (memory s) pageEq idxEq |} = 
      getPartitions pageRootPartition s) as Hpartions.
    {
      apply getPartitionsUpdateMappedPageData ; trivial. + unfold consistency in *. intuition.
      + unfold getPartitions.
        destruct nbPage;simpl;left;trivial.
      + intuition.
      + assert(Hfalse : (Nat.eqb pageDefault table1) = false) by intuition.
        apply beq_nat_false in Hfalse.
        unfold not; intros.
        apply Hfalse.
        subst;trivial.
      + unfold propagatedProperties in *.
        unfold consistency in *.
        intuition.  }
    rewrite Hpartions in *; trivial.
    assert(Hconfig: forall partition : page,
     In partition (getPartitions pageRootPartition s) ->
     partition = table1 \/ In table1 (getConfigPagesAux partition s) -> False)
     by intuition.
    assert(Hcurpart : In (currentPartition s) (getPartitions pageRootPartition s)).
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    intuition.
    assert(Hpde : partitionDescriptorEntry s).
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    assert(Hprop : table1 <> phySh2Child). 
    {
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptSh2Child pt1  idxSh2  
    idxVa1   shadow2 va1 level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    subst.
    intuition.
        rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
    assert(Hprop2 : table1 <> phySh1Child). 
    { destruct H.
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
        apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptSh1Child pt1  idxSh1  
    idxVa1   shadow1 va1 level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    subst.
    intuition.
        rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
    assert(Hprop3 : table1 <> phyPDChild).
    {    
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptPDChild pt1  idxPDChild  
    idxVa1   pdChild va1 level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    subst.
    intuition.
        rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
     assert(Hprop4 : table1 <> phyConfigPagesList).
    {    
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptConfigPagesList pt1  idxConfigPagesList  
    idxVa1   list va1 level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    subst.
    intuition.
        rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
    split.
    apply isWellFormedSndShadowUpdateMappedPageData;trivial.
    intuition.
    split.
    apply isWellFormedFstShadowUpdateMappedPageData;trivial.
    intuition.
    split. 
    assert (Htable : (forall idx : index,
    StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\
    StateLib.readPresent phyPDChild idx (memory s) = Some false))
    by intuition.
    intros.
    generalize (Htable idx); clear Htable; intros Htable.
    destruct Htable as (Htable1 & Htable2).
    rewrite <- Htable1.
    rewrite <- Htable2.
    split. 
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial.
    symmetry.
    apply readPresentUpdateMappedPageData;trivial.
    split.
    intuition.
    apply initConfigPagesListPostConditionUpdateMappedPageContent;trivial.
    assert(Htableroot1 : forall idx : index,
      StateLib.getIndexOfAddr va1 levelMin = idx ->
      isPE pt1 idx s /\ getTableAddrRoot pt1 idxPageDir (currentPartition s) va1 s) by intuition.
      intuition.
      
    assert(Hpart : In partition (getPartitions pageRootPartition s)) by trivial.
    apply Hconfig in Hpart.
    now contradict Hpart.
    left; trivial.
    assert(Hpart : In partition (getPartitions pageRootPartition s)) by trivial.
    apply Hconfig in Hpart.
    now contradict Hpart.
    right.
    assert(Hconfaux :getConfigPagesAux partition {|
                      currentPartition := currentPartition s;
                      memory := add table1 idxroot (VA value2) (memory s) pageEq idxEq |} = 
                      getConfigPagesAux  partition s).
    { apply getConfigPagesAuxUpdateMappedPageData; trivial.
      unfold getConfigPages; unfold not; simpl.
      apply Hconfig; trivial. } 
    rewrite Hconfaux in *.
    assumption.
    apply isEntryPageUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with (currentPartition s)  currentPD isPE idxPageDir va1 idxVa1 s ;
    trivial. left;trivial.
    apply isPEUpdateUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with (currentPartition s)  currentPD isPE idxPageDir va1 idxVa1 s ;
    trivial. left;trivial.
    apply Htableroot1; trivial.
    apply getTableAddrRootUpdateMappedPageData; trivial.
    assert (isPE pt1 idx s /\ getTableAddrRoot pt1 idxPageDir (currentPartition s)  va1 s)
    as ( _ & Hget1).
    apply Htableroot1; trivial.
    trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with (currentPartition s)   currentPD isPE idxPageDir va1 idxVa1 s ;
    trivial. left;trivial.
    apply nextEntryIsPPUpdateMappedPageData; trivial.
    intros [].
 (** MALInternal.Index.succ **) 
   eapply bindRev.
   eapply WP.weaken. 
   eapply Invariants.Index.succ.
   intros.
   simpl.
   split.
   try repeat rewrite and_assoc in H.  
   pattern s in H.
   eassumption.
   repeat rewrite and_assoc in H.
   intuition.
   intros PRidxsucc.
(** writePhysical**)
  eapply weaken.
  eapply WP.writePhysical.
  simpl;intros.
  try repeat rewrite and_assoc in H.
  subst.
  pattern s in H.
  simpl in *.
  split.
  split.
  intuition.
  subst.
   apply propagatedPropertiesUpdateMappedPageData; trivial.
   unfold propagatedProperties in *. 
    assert(Hcurpart1 : In currentPart (getPartitions pageRootPartition s)).
   {unfold consistency in *. 
   intuition; 
   subst;
   unfold currentPartitionInPartitionsList in *;   
   subst;intuition. }
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition.  (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*)  
  
  split. intuition.
      assert(Hprop : table1 <> phySh2Child). 
    {
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptSh2Child pt1  idxSh2  
    idxVa1   shadow2 va1 level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    subst.
    intuition.
        rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
    assert(Hprop2 : table1 <> phySh1Child). 
    { destruct H.
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
        apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptSh1Child pt1  idxSh1  
    idxVa1   shadow1 va1 level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    subst.
    intuition.
        rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
    assert(Hprop3 : table1 <> phyPDChild).
    {    
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptPDChild pt1  idxPDChild  
    idxVa1   pdChild va1 level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    subst.
    intuition.
        rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
     assert(Hprop4 : table1 <> phyConfigPagesList).
    {    
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptConfigPagesList pt1  idxConfigPagesList  
    idxVa1   list va1 level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    subst.
    intuition.
        rewrite checkVAddrsEqualityWOOffsetPermut.
      assumption. }
    split.
    apply isWellFormedSndShadowUpdateMappedPageData;trivial.
    intuition.
    split.
    apply isWellFormedFstShadowUpdateMappedPageData;trivial.
    intuition.
    split. 
    assert (Htable : (forall idx : index,
    StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\
    StateLib.readPresent phyPDChild idx (memory s) = Some false))
    by intuition.
    intros.
    generalize (Htable idx); clear Htable; intros Htable.
    destruct Htable as (Htable1 & Htable2).
    rewrite <- Htable1.
    rewrite <- Htable2.
    split. 
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial.
    symmetry.
    apply readPresentUpdateMappedPageData;trivial.
    split.
    intuition.
    apply initConfigPagesListPostConditionUpdateMappedPageContent;trivial.
      intuition.
      intuition.  
Qed. 


Lemma updatePartitionDescriptorNewProperty (phyDescChild : page) (value2 : vaddr) value1 (idxPR : index) :
 {{ fun s : state =>  idxPR < tableSize - 1}} 
     Internal.updatePartitionDescriptor phyDescChild idxPR value1 value2
{{ fun _ s => isVA phyDescChild idxPR  s /\ nextEntryIsPP phyDescChild idxPR value1 s}}.
Proof.
unfold updatePartitionDescriptor.
eapply bindRev.
(** writeVirtual **) 
eapply weaken.
eapply WP.writeVirtual.
simpl.
intros.
pattern s in H.
match type of H with 
| ?HT s => instantiate (1 := fun tt s => HT s /\ 
         StateLib.readVirtual phyDescChild idxPR s.(memory) = Some value2 )
end.
simpl in *.
split; trivial.
unfold StateLib.readVirtual.
cbn.
assert (Htrue :Lib.beqPairs (phyDescChild, idxPR) (phyDescChild, idxPR) pageEq idxEq
= true).
apply beqPairsTrue;split;trivial.
rewrite Htrue; trivial.
intros [].
(** MALInternal.Index.succ **) 
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.Index.succ.
intros.
simpl.
split.
try repeat rewrite and_assoc in H.  
pattern s in H.
eassumption.
intuition.
intros idxsucc.
(** writeVirtual **) 
eapply weaken.
eapply WP.writePhysical.
simpl.
intros.
split.
(** isVA postcondition **)
unfold isVA.
cbn.
assert(Hidxsucc : idxsucc <> idxPR).
destruct H.
unfold not; intros.
symmetry in H1.
contradict H1.
apply indexSuccEqFalse; trivial.
assert(Hfalse : beqPairs (phyDescChild, idxsucc) (phyDescChild, idxPR) pageEq idxEq
                = false).
apply beqPairsFalse.
right; trivial.
rewrite Hfalse.
destruct H as ((Hixd & Hreadv )& Hsucc).
unfold StateLib.readVirtual in *.
assert(Hmemory : lookup phyDescChild idxPR (removeDup phyDescChild idxsucc (memory s) pageEq idxEq) pageEq
        idxEq = lookup phyDescChild idxPR (memory s) pageEq idxEq).
{ apply removeDupIdentity; trivial.
  right.
  unfold not; intros.
  subst.
  now contradict Hidxsucc.  }
rewrite Hmemory.
destruct (lookup phyDescChild idxPR (memory s) pageEq idxEq ); 
try now contradict Hreadv.
destruct v; try now contradict Hreadv.
trivial.
(** nextEntryIsPP postcondition **)
unfold nextEntryIsPP.
destruct H.
rewrite H0.
cbn.
assert (Htrue :Lib.beqPairs(phyDescChild, idxsucc) (phyDescChild, idxsucc) pageEq idxEq
              = true).
apply beqPairsTrue;split;trivial.
rewrite Htrue; trivial.
Qed.

Lemma updatePartitionDescriptorPropagatedProperties2 table (idx1 idx2: index) pageValue1 va  pageValue2 : 
{{ fun s : state => idx2 < tableSize - 1 /\ idx1 < tableSize - 1/\ idx1 <> idx2 /\  
(exists succidx1, StateLib.Index.succ idx1 = Some succidx1  /\ succidx1 <> idx2) /\
(exists succidx2, StateLib.Index.succ idx2 = Some succidx2 /\ succidx2 <> idx1) /\
isVA table idx1 s /\ nextEntryIsPP table idx1 pageValue1 s}}
 Internal.updatePartitionDescriptor table idx2 pageValue2 va 
{{ fun (_ : unit) (s : state) =>isVA table idx1 s /\  nextEntryIsPP table idx1 pageValue1 s }}.
Proof.
unfold updatePartitionDescriptor.
eapply bindRev.
(** writeVirtual **)
eapply weaken.
eapply WP.writeVirtual.
simpl.
intros.
pattern s in H.
match type of H with 
| ?HT s => instantiate (1 := fun tt s => HT s )
end.
simpl in *.
intuition.
(** propagate isVA **)
unfold isVA in *.
cbn.
assert(Hfalse:  beqPairs (table, idx2) (table, idx1) pageEq idxEq = false).
apply beqPairsFalse.
right.
unfold not; intros; subst.
now contradict H1.
rewrite Hfalse.
assert (Hmemory :  lookup table idx1 (removeDup table idx2 (memory s) pageEq idxEq)
    pageEq idxEq = lookup table idx1 (memory s) pageEq idxEq).
{ apply removeDupIdentity; right; unfold not; intros; subst; now contradict H1. }
rewrite Hmemory; assumption.
(** propagate nextEntryIsPP **)
destruct H2 as (idx1succ & Hidx1succ & Hnoteq).
unfold nextEntryIsPP in *.
rewrite Hidx1succ in *.
cbn.
assert(Hfalse:  beqPairs (table, idx2) (table, idx1succ) pageEq idxEq = false).
apply beqPairsFalse.
right.
unfold not; intros; subst.
now contradict Hnoteq.
rewrite Hfalse.
assert (Hmemory :  lookup table idx1succ (removeDup table idx2 (memory s) pageEq idxEq)
    pageEq idxEq = lookup table idx1succ (memory s) pageEq idxEq).
{ apply removeDupIdentity; right; unfold not; intros; subst; now contradict Hnoteq. }
rewrite Hmemory; assumption.
intros [].
(** MALInternal.Index.succ **) 
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.Index.succ.
intros.
simpl.
split.
try repeat rewrite and_assoc in H.  
pattern s in H.
eassumption.
intuition.
simpl.
intros idxsucc.
(** writeVirtual **) 
eapply weaken.
eapply WP.writePhysical.
simpl.
intros.
destruct H as ((H & H1 & H2 & H3 & H4 & H5 & H7) & H6).
destruct H4 as (succidx2 & Hsuccidx2 & Hnoteq).
rewrite H6 in Hsuccidx2.
inversion Hsuccidx2; clear Hsuccidx2.
subst.
split.
(** propagate isVA **)
unfold isVA in *.
cbn.
assert(Hfalse:  beqPairs (table, succidx2) (table, idx1) pageEq idxEq = false).
{ apply beqPairsFalse.
  right.
  unfold not; intros.
  intuition. }
rewrite Hfalse.
assert (Hmemory :  lookup table idx1 (removeDup table succidx2 (memory s) pageEq idxEq)
pageEq idxEq = lookup table idx1 (memory s) pageEq idxEq).
{ apply removeDupIdentity; right;  unfold not; intros; subst; now contradict Hnoteq. }
rewrite Hmemory; assumption.
(** propagate nextEntryIsPP **)
unfold nextEntryIsPP in *.
destruct H3 as (succidx1 & Hsuccidx1 & Hnoteqsucc12).
rewrite Hsuccidx1 in *.
cbn.
assert(Hfalse:  beqPairs (table, succidx2) (table, succidx1) pageEq idxEq = false).
apply beqPairsFalse.
right.
unfold not; intros; subst.
rewrite <- Hsuccidx1 in H6.
apply indexNotEqSuccNotEq in H2; trivial.
now contradict H2. 
rewrite Hfalse.
assert (Hmemory :  lookup table succidx1 (removeDup table succidx2 (memory s) pageEq idxEq)
    pageEq idxEq = lookup table succidx1 (memory s) pageEq idxEq).
{ apply removeDupIdentity; right.
  unfold not; intros. subst.
  rewrite <- Hsuccidx1 in H6.
  apply indexNotEqSuccNotEq in H2; trivial.
  now contradict H2.  }
rewrite Hmemory; assumption.
Qed.
