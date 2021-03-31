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
    This file contains several invariants of [initPEntryTable] and associated lemmas *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Internal.

Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.Isolation
               Pip.Proof.InternalLemmas Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.

Require Import Invariants InitPEntryTable InitVAddrTable UpdateMappedPageContent PropagatedProperties.
Require Import Coq.Logic.ProofIrrelevance Lia List Bool EqNat.



(******************************TO BE MOVED ***********************)


(********************************************)

Lemma initSndShadowNewProperty table (nbL : level)(curidx : index):
{{ fun s => initSndShadowPreconditionToProveNewProperty nbL s table  curidx }} 
Internal.initSndShadow table nbL curidx 
{{fun _ s => isWellFormedSndShadow nbL table s
  }}.
Proof.
unfold initSndShadowPreconditionToProveNewProperty.
unfold Internal.initSndShadow.
eapply WP.bindRev.
+ eapply WP.weaken.
  eapply Invariants.Level.eqb.
  simpl.
  intros.
  pattern s in H.
  eassumption.
+ simpl. 
  intros isFstLevel.
  case_eq isFstLevel.
  - intros.
    eapply strengthen.
    eapply postAnd.
    eapply weaken.
    apply initVAddrTableNewPropertyL.
    unfold initVAddrTablePreconditionToProveNewProperty.
    simpl.
    intros. 
    destruct H0 as (Htable & Hi).
    destruct Htable .
    destruct H0.
     symmetry in Hi.
    apply levelEqBEqNatTrue in Hi.
    contradiction.
    destruct H0.
    apply H2;trivial.
    instantiate(1:= fun _ s => true = StateLib.Level.eqb nbL fstLevel).
    eapply weaken.
    eapply initVAddrTablePreservesProp. 
    simpl.
    intros;intuition.
    intros.
    simpl in *.
    right.
    split.
    destruct H0.
    symmetry in H1.
    apply levelEqBEqNatTrue in H1.
    assumption.
    destruct H0.
    assumption.    
  - intros.
    eapply strengthen.
    eapply postAnd.
    eapply weaken.
    apply initPEntryTableNewPropertyL.
    unfold initPEntryTablePreconditionToProveNewProperty.
    simpl.
    intros.
    destruct H0 as (Htable & Hi).
    destruct Htable .
    destruct H0.
    apply H2;trivial.
    destruct H0.
    symmetry in Hi.
    apply levelEqBEqNatFalse in Hi.
    subst.
    lia.
    instantiate(1:= fun _ s => false = StateLib.Level.eqb nbL fstLevel).
    eapply weaken.
    eapply initPEntryTablePreservesProp. 
    simpl.
    intros;intuition.
    intros.
    simpl in *.
    left.
    split.
    destruct H0.
    symmetry in H1.
    apply levelEqBEqNatFalse in H1.
    unfold not;intros;subst.
    lia.
    destruct H0.
    assumption.    
Qed.

Lemma initSndShadowTablePropagateProperties1  nbL
table phyPDChild
       phySh1Child phySh2Child phyConfigPagesList phyDescChild  (curidx : index) zero  currentPart currentPD
 level ptRefChild descChild idxRefChild presentRefChild ptPDChild pdChild 
 idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child 
 shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList 
 presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild 
 ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 
 derivedSh2Child childListSh1 derivedRefChildListSh1 list :
{{fun s =>  
 ( propagatedProperties false false false false pdChild currentPart currentPD level ptRefChild
      descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1
      idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
      phyDescChild s  /\ 
      ((((forall partition : page,
        In partition (getAncestors currentPart s) -> ~ In phyPDChild (getAccessibleMappedPages partition s)) /\
       (forall partition : page,
        In partition (getAncestors currentPart s) -> ~ In phySh1Child (getAccessibleMappedPages partition s))) /\
      (forall partition : page,
       In partition (getAncestors currentPart s) -> ~ In phySh2Child (getAccessibleMappedPages partition s))) /\
     (forall partition : page,
      In partition (getAncestors currentPart s) -> ~ In phyConfigPagesList (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phyDescChild (getAccessibleMappedPages partition s)))/\
 
   zero = CIndex 0 ) /\
  (forall partition : page,
  In partition (getPartitions multiplexer s) ->
  partition = table \/ In table (getConfigPagesAux partition s) -> False) /\ 
  (Nat.eqb defaultPage table) = false 
}} 

initSndShadow table  nbL curidx 

{{ fun res s =>  
  ( propagatedProperties false false false false pdChild currentPart currentPD level ptRefChild
      descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1
      idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
      phyDescChild s  /\ 
      ((((forall partition : page,
        In partition (getAncestors currentPart s) -> ~ In phyPDChild (getAccessibleMappedPages partition s)) /\
       (forall partition : page,
        In partition (getAncestors currentPart s) -> ~ In phySh1Child (getAccessibleMappedPages partition s))) /\
      (forall partition : page,
       In partition (getAncestors currentPart s) -> ~ In phySh2Child (getAccessibleMappedPages partition s))) /\
     (forall partition : page,
      In partition (getAncestors currentPart s) -> ~ In phyConfigPagesList (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phyDescChild (getAccessibleMappedPages partition s)))/\

   zero = CIndex 0 )  }}.
Proof.
unfold Internal.initSndShadow.
eapply WP.bindRev.
+ eapply WP.weaken.
  eapply Invariants.Level.eqb.
  simpl.
  intros.
  pattern s in H.
  eassumption.
+ simpl. 
  intros isFstLevel.
  case_eq isFstLevel.
  - intros. eapply weaken.
    apply initVAddrTablePropagateProperties1.
    simpl.
    intros.
    intuition.
 -  intros. eapply weaken.
    apply initPEntryTablePropagateProperties1.
    simpl.
    intros.
    intuition.
Qed.

Lemma initSndShadowPropagateProperties2 nbL accessibleChild accessibleSh1 accessibleSh2 accessibleList 
partition  va1 va2 idxVa1 idxVa2 (table1 table2 : page) phyPage1 
      phyPage2 curidx pdChild currentPart currentPD level ptRefChild descChild idxRefChild
      presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1
      ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList 
      phyDescChild zero :
{{ fun s : state =>
   (propagatedProperties accessibleChild accessibleSh1 accessibleSh2 accessibleList 
   pdChild currentPart currentPD level ptRefChild descChild idxRefChild
      presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1
      ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild
      s  /\ 
      ((((forall partition : page,
        In partition (getAncestors currentPart s) -> ~ In phyPDChild (getAccessibleMappedPages partition s)) /\
       (forall partition : page,
        In partition (getAncestors currentPart s) -> ~ In phySh1Child (getAccessibleMappedPages partition s))) /\
      (forall partition : page,
       In partition (getAncestors currentPart s) -> ~ In phySh2Child (getAccessibleMappedPages partition s))) /\
     (forall partition : page,
      In partition (getAncestors currentPart s) -> ~ In phyConfigPagesList (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phyDescChild (getAccessibleMappedPages partition s)))/\
 zero = CIndex 0) /\
      
      (Nat.eqb defaultPage table1) = false /\
      (Nat.eqb defaultPage table2) = false /\
       nextEntryIsPP partition PDidx currentPD s /\
      In partition (getPartitions multiplexer s) /\
              
  ( forall idx, StateLib.readPhyEntry phyPage2  idx s.(memory) = Some defaultPage /\ 
              StateLib.readPresent phyPage2 idx (memory s) = Some false )
              /\ 
   
   
   (forall partition : page,
    In partition (getPartitions multiplexer s) -> 
    partition = phyPage1 \/ In phyPage1 (getConfigPagesAux partition s) -> False) /\
   ( (Nat.eqb defaultPage phyPage1) = false) /\ 
   isEntryPage table1 idxVa1 phyPage1 s /\
       isEntryPage table2 idxVa2 phyPage2 s /\
       StateLib.getIndexOfAddr va1 fstLevel = idxVa1 /\
       StateLib.getIndexOfAddr va2 fstLevel = idxVa2 /\
       (forall idx : index,
        StateLib.getIndexOfAddr va1 fstLevel = idx -> isPE table1 idx s /\
         getTableAddrRoot table1 PDidx partition va1 s) /\
       (forall idx : index,
        StateLib.getIndexOfAddr va2 fstLevel = idx -> 
        isPE table2 idx s /\ getTableAddrRoot table2 PDidx partition va2 s) /\
        Some level = StateLib.getNbLevel /\
       false = StateLib.checkVAddrsEqualityWOOffset nbLevel va2 va1 level /\
       entryPresentFlag table1 idxVa1 true s /\ entryPresentFlag table2 idxVa2 true s

}} 
 initSndShadow  phyPage1 nbL curidx {{ fun _  (s : state) =>
 ( forall idx, StateLib.readPhyEntry phyPage2  idx s.(memory) = Some defaultPage /\ 
              StateLib.readPresent phyPage2 idx (memory s) = Some false )
              }}.
Proof.
unfold initSndShadow.
eapply WP.bindRev.
+ eapply WP.weaken.
  eapply Invariants.Level.eqb.
  simpl.
  intros.
  pattern s in H.
  eassumption.
+ simpl. 
  intros isFstLevel.
  case_eq isFstLevel.
  - intros.
    eapply weaken.    
    eapply initVAddrTablePropagateProperties2.
    intros.
    simpl.
    destruct H0.
    eapply H0.   
  - intros.
    eapply weaken.    
    eapply initPEntryTablePropagateProperties2.
    intros.
    simpl.
    destruct H0.
    eapply H0.
Qed.

Lemma initSndShadowPropagateProperties3 nbL accessibleChild accessibleSh1 accessibleSh2 accessibleList 
partition  va1 va2 idxVa1 idxVa2 (table1 table2 : page) phyPage1 
      phyPage2 curidx pdChild currentPart currentPD level ptRefChild descChild idxRefChild
      presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1
      ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList 
      phyDescChild zero :
{{ fun s : state =>
   (propagatedProperties accessibleChild accessibleSh1 accessibleSh2 accessibleList 
   pdChild currentPart currentPD level ptRefChild descChild idxRefChild
      presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1
      ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild
      s  /\ 
      ((((forall partition : page,
        In partition (getAncestors currentPart s) -> ~ In phyPDChild (getAccessibleMappedPages partition s)) /\
       (forall partition : page,
        In partition (getAncestors currentPart s) -> ~ In phySh1Child (getAccessibleMappedPages partition s))) /\
      (forall partition : page,
       In partition (getAncestors currentPart s) -> ~ In phySh2Child (getAccessibleMappedPages partition s))) /\
     (forall partition : page,
      In partition (getAncestors currentPart s) -> ~ In phyConfigPagesList (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phyDescChild (getAccessibleMappedPages partition s)))/\
 zero = CIndex 0) /\
      
      (Nat.eqb defaultPage table1) = false /\
      (Nat.eqb defaultPage table2) = false /\
       nextEntryIsPP partition PDidx currentPD s /\
      In partition (getPartitions multiplexer s) /\
              
  ( (level <> fstLevel /\
    (forall idx : index,
     StateLib.readPhyEntry phyPage2 idx (memory s) = Some defaultPage /\ 
     StateLib.readPresent phyPage2 idx (memory s) = Some false) \/
    level = fstLevel /\
    (forall idx : index,
     StateLib.readVirEntry phyPage2 idx (memory s) = Some defaultVAddr /\ 
     StateLib.readPDflag phyPage2 idx (memory s) = Some false)) )
              /\ 
   
   
   (forall partition : page,
    In partition (getPartitions multiplexer s) -> 
    partition = phyPage1 \/ In phyPage1 (getConfigPagesAux partition s) -> False) /\
   ( (Nat.eqb defaultPage phyPage1) = false) /\ 
   isEntryPage table1 idxVa1 phyPage1 s /\
       isEntryPage table2 idxVa2 phyPage2 s /\
       StateLib.getIndexOfAddr va1 fstLevel = idxVa1 /\
       StateLib.getIndexOfAddr va2 fstLevel = idxVa2 /\
       (forall idx : index,
        StateLib.getIndexOfAddr va1 fstLevel = idx -> isPE table1 idx s /\
         getTableAddrRoot table1 PDidx partition va1 s) /\
       (forall idx : index,
        StateLib.getIndexOfAddr va2 fstLevel = idx -> 
        isPE table2 idx s /\ getTableAddrRoot table2 PDidx partition va2 s) /\
        Some level = StateLib.getNbLevel /\
       false = StateLib.checkVAddrsEqualityWOOffset nbLevel va2 va1 level /\
       entryPresentFlag table1 idxVa1 true s /\ entryPresentFlag table2 idxVa2 true s

}} 
 initSndShadow  phyPage1 nbL curidx {{ fun _  (s : state) =>
 ( (level <> fstLevel /\
    (forall idx : index,
     StateLib.readPhyEntry phyPage2 idx (memory s) = Some defaultPage /\ 
     StateLib.readPresent phyPage2 idx (memory s) = Some false) \/
    level = fstLevel /\
    (forall idx : index,
     StateLib.readVirEntry phyPage2 idx (memory s) = Some defaultVAddr /\ 
     StateLib.readPDflag phyPage2 idx (memory s) = Some false)) )
              }}.
Proof.
unfold initSndShadow.
eapply WP.bindRev.
+ eapply WP.weaken.
  eapply Invariants.Level.eqb.
  simpl.
  intros.
  pattern s in H.
  eassumption.
+ simpl. 
  intros isFstLevel.
  case_eq isFstLevel.
  - intros.
    eapply weaken.    
    eapply initVAddrTablePropagateProperties3.
    intros.
    simpl.
    destruct H0.
    eapply H0.   
  - intros.
    eapply weaken.    
    eapply initPEntryTablePropagateProperties3.
    intros.
    simpl.
    destruct H0.
    eapply H0.
Qed. 





Lemma initSndShadowPrepareHT lpred ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
      lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
      currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  
      idxFstVA idxSndVA idxTrdVA zeroI LLroot LLChildphy newLastLLable minFI indMMUToPreparebool:
   {{ fun s : state =>
   (propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
      lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
      currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false
      false true true true idxFstVA idxSndVA idxTrdVA zeroI minFI
    /\ isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA 
    /\ writeAccessibleRecPreparePostcondition currentPart phyMMUaddr s 
    /\ writeAccessibleRecPreparePostcondition currentPart phySh1addr s
    /\ writeAccessibleRecPreparePostcondition currentPart phySh2addr s 
    /\ StateLib.Level.pred l = Some lpred) 
    /\ isWellFormedMMUTables phyMMUaddr s 
    /\ isWellFormedFstShadow lpred phySh1addr s }} 
  initSndShadow phySh2addr lpred zeroI 
{{ fun _ s => (propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
      lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
      currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false
      false false true true true idxFstVA idxSndVA idxTrdVA zeroI minFI
    /\ isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA 
    /\ writeAccessibleRecPreparePostcondition currentPart phyMMUaddr s
    /\ writeAccessibleRecPreparePostcondition currentPart phySh1addr s
    /\ writeAccessibleRecPreparePostcondition currentPart phySh2addr s 
    /\ StateLib.Level.pred l = Some lpred) 
    /\ isWellFormedMMUTables phyMMUaddr s 
    /\ isWellFormedFstShadow lpred phySh1addr s 
    /\ isWellFormedSndShadow lpred phySh2addr s 
    /\ newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr
    /\ newIndirectionsAreNotMappedInChildrenAll s currentPart phyMMUaddr phySh1addr phySh2addr
    }}.
   Proof.
 unfold initSndShadow. 
eapply WP.bindRev.
+ eapply WP.weaken.
  eapply Invariants.Level.eqb.
  simpl.
  intros.
  pattern s in H.
  eassumption.
+ simpl. 
  intros isFstLevel.
  case_eq isFstLevel.
  - intros.
  eapply strengthen.
  eapply weaken.
  eapply postAnd.
  eapply postAnd. 
  eapply postAnd.
  eapply postAnd.
  6:{ intros. eapply H0. }
  eapply weaken.
  (** propagatedPropertiesPrepare **)
  eapply initVAddrTablePropagateProperties with (zeroI:=zeroI);trivial.
  intuition;try eassumption;unfold propagatedPropertiesPrepare in *;intuition.
  unfold initPEntryTablePreconditionToPropagatePreparePropertiesAll in *;intuition.
  eapply weaken.
  (** propagate isWellFormedMMUTables **)
  eapply initVAddrTablePropagateIsWellFormedMMUTable 
   with (phyPage1:= phySh2addr)
  (phyPage2:= phyMMUaddr)
  (va1:=trdVA) (va2 :=fstVA) (table1:=ptMMUTrdVA) (table2:=  ptMMUFstVA) 
  (partition:= currentPart) (level:=nbLgen) (currentPD:= currentPD).
  unfold PreCtoPropagateIsWellFormedMMUTables, propagatedPropertiesPrepare,
  initPEntryTablePreconditionToPropagatePreparePropertiesAll
      in *;intuition;subst;trivial.
  unfold consistency in *;intuition.
  apply phyPageNotDefault with ptMMUTrdVA (StateLib.getIndexOfAddr trdVA fstLevel) s;trivial.
  unfold consistency in *;intuition.
  (** prove new property *)
  eapply weaken.
  eapply initVAddrTableNewPropertyL.
  simpl. intros.
  unfold initVAddrTablePreconditionToProveNewProperty.
  intros idx Hfalse.
  assert(Hzero: zeroI = CIndex 0).
  { unfold propagatedPropertiesPrepare in *.
    intuition. }
  subst.
  apply index0Ltfalse in Hfalse.
  now contradict Hfalse.
  simpl.
  eapply weaken.
  eapply initVAddrTablePreservesProp with (v:= true)( nbL:= lpred).
  intros. intuition.
  (** propagate isWellFormedFstShadow **)
  eapply weaken.
  eapply initVAddrTablePropagateIsWellFormedFstShadow with (phyPage2:= phySh1addr)
  (va1:=trdVA) (va2 :=sndVA) (table1:=ptMMUTrdVA) (table2:=  ptMMUSndVA) 
  (partition:= currentPart) (level0 := nbLgen)(lpred:=lpred) (currentPD:= currentPD).
  unfold PreCtoPropagateIsWellFormedMMUTables, propagatedPropertiesPrepare,
  initPEntryTablePreconditionToPropagatePreparePropertiesAll
      in *;intuition;subst;trivial.
  unfold consistency in *;intuition.
  apply phyPageNotDefault with ptMMUTrdVA (StateLib.getIndexOfAddr trdVA fstLevel) s;trivial.
  unfold consistency in *;intuition.
  simpl;intros.
  intuition.
  simpl.
  intros.
  (** propagate isWellFormedSndShadow **)
  intuition.
  unfold isWellFormedSndShadow.
  unfold initVAddrTableNewProperty in *.
  assert(Hpred:true = StateLib.Level.eqb lpred fstLevel) by trivial.
  unfold StateLib.Level.eqb in *.
  symmetry in Hpred.
  apply beq_nat_true in Hpred.
  right.
  split;trivial.
  subst.
  destruct lpred;simpl in *.
  destruct fstLevel;simpl in *.
  subst;f_equal;apply proof_irrelevance.
  (** prove new property : newIndirectionsAreNotAccessible **)
  unfold  propagatedPropertiesPrepare, consistency in *. 
  intuition.
  unfold newIndirectionsAreNotAccessible.
  intros * Hpart Hor.
  { destruct Hor as [Hor| [Hor | Hor]];subst.
  * 
  eapply nextIndirectionNotAccessibleInAnyPartition with 
  (currentPart:=(currentPartition s))
  (currentPD:= currentPD)
  (ptMMUvaNextInd:= ptMMUFstVA) 
  (vaNextInd:= fstVA)
  (ptSh1VaNextInd:=ptSh1FstVA);trivial;unfold consistency;intuition.
  * 
  eapply nextIndirectionNotAccessibleInAnyPartition with 
  (currentPart:=(currentPartition s))
  (currentPD:= currentPD)
  (ptMMUvaNextInd:= ptMMUSndVA) 
  (vaNextInd:= sndVA)
  (ptSh1VaNextInd:=ptSh1SndVA);trivial;unfold consistency;intuition.
   
  * 
  eapply nextIndirectionNotAccessibleInAnyPartition with 
  (currentPart:=(currentPartition s))
  (currentPD:= currentPD)
  (ptMMUvaNextInd:= ptMMUTrdVA) 
  (vaNextInd:= trdVA)
  (ptSh1VaNextInd:=ptSh1TrdVA);trivial;unfold consistency;intuition. }
  (** Prove new property:  newIndirectionsAreNotMappedInChildrenAll **)
  unfold newIndirectionsAreNotMappedInChildrenAll , propagatedPropertiesPrepare in *.
  intuition;
  unfold newIndirectionsAreNotMappedInChildren;
  intros * Hchild; subst.
  eapply phyNotDerived with (ptSh1Child:= ptMMUFstVA) (currentPart:=  (currentPartition s) )
  (shadow1:= fstVA) (currentPD:= currentPD);trivial.
  apply vaNotDerived with ptSh1FstVA;trivial.
  unfold consistency in *;intuition.
  intros;subst;split;trivial.
  unfold consistency in *;intuition.
  intros;subst;split;trivial.
  eapply phyNotDerived with (ptSh1Child:= ptMMUSndVA) (currentPart:=  (currentPartition s) )
  (shadow1:= sndVA) (currentPD:= currentPD);trivial.
  apply vaNotDerived with ptSh1SndVA;trivial.
  unfold consistency in *;intuition.
  intros;subst;split;trivial.
  unfold consistency in *;intuition.
  intros;subst;split;trivial.
  eapply phyNotDerived with (ptSh1Child:= ptMMUTrdVA) (currentPart:=  (currentPartition s) )
  (shadow1:= trdVA) (currentPD:= currentPD);trivial.
  apply vaNotDerived with ptSh1TrdVA;trivial.
  unfold consistency in *;intuition.
  intros;subst;split;trivial.
  unfold consistency in *;intuition.
  intros;subst;split;trivial.    
  - intros. subst.
  eapply strengthen.
  eapply weaken.
  eapply postAnd.
  eapply postAnd.
  eapply postAnd.
  eapply postAnd.
  6:{ intros. eapply H. }
  eapply weaken.  
  (** propagatedPropertiesPrepare **)
  eapply initPEntryTablePropagateProperties with (zeroI:=zeroI);trivial.
  intuition;try eassumption;unfold propagatedPropertiesPrepare in *;intuition.
  unfold initPEntryTablePreconditionToPropagatePreparePropertiesAll in *;intuition.
  eapply weaken.
  (** propagate isWellFormedMMUTables **)
  eapply initPEntryTablePropagateIsWellFormedMMUTable  with (phyPage2:= phyMMUaddr)
  (va1:=trdVA) (va2 :=fstVA) (table1:=ptMMUTrdVA) (table2:=  ptMMUFstVA) 
  (partition:= currentPart) (level := nbLgen) (currentPD:= currentPD).
  unfold PreCtoPropagateIsWellFormedMMUTables, propagatedPropertiesPrepare,
  initPEntryTablePreconditionToPropagatePreparePropertiesAll 
      in *;intuition;subst;trivial.
  unfold consistency in *;intuition.
  unfold propagatedPropertiesPrepare in *.
  intuition.
  apply phyPageNotDefault with ptMMUTrdVA (StateLib.getIndexOfAddr trdVA fstLevel) s;trivial.
  unfold consistency in *;intuition.
  (** propagate new property *)
  eapply weaken.
  eapply initPEntryTableNewPropertyL.
  simpl. intros.
  unfold initVEntryTablePreconditionToProveNewProperty.
  intros idx Hfalse.
  assert(Hzero: zeroI = CIndex 0).
  { unfold propagatedPropertiesPrepare in *.
    intuition. }
  subst.
  apply index0Ltfalse in Hfalse.
  now contradict Hfalse.
  simpl.
  eapply weaken.
  eapply initPEntryTablePreservesProp with ( nbL:= lpred).
  intros. intuition.
   (** propagate isWellFormedFstShadow **)
  eapply weaken.
  eapply initPEntryTablePropagateIsWellFormedFstShadow with (phyPage1:= phySh2addr)
  (phyPage2:= phySh1addr)
  (va1:=trdVA) (va2 :=sndVA) (table1:=ptMMUTrdVA) (table2:=  ptMMUSndVA) 
  (partition:= currentPart) (level0 := nbLgen) (lpred:= lpred) (currentPD:= currentPD).
  unfold PreCtoPropagateIsWellFormedMMUTables, propagatedPropertiesPrepare,
  initPEntryTablePreconditionToPropagatePreparePropertiesAll
      in *;intuition;subst;trivial.
  unfold consistency in *;intuition.
  apply phyPageNotDefault with ptMMUTrdVA (StateLib.getIndexOfAddr trdVA fstLevel) s;trivial.
  unfold consistency in *;intuition.
  simpl.
  intros.
  intuition.
  unfold isWellFormedSndShadow.
  assert(Hwell:isWellFormedMMUTables phySh2addr s) by trivial.
  unfold isWellFormedMMUTables in Hwell.
  assert(Hpred:false = StateLib.Level.eqb lpred fstLevel) by trivial.
  unfold StateLib.Level.eqb in *.
  symmetry in Hpred.
  apply beq_nat_false in Hpred.
  left.
  split;trivial.
  subst.
  destruct lpred;simpl in *.
  destruct fstLevel;simpl in *.
  contradict Hpred.
  inversion Hpred.
  trivial.
(** prove new property : newIndirectionsAreNotAccessible **)
  { unfold  propagatedPropertiesPrepare, consistency in *. 
  intuition.
  unfold newIndirectionsAreNotAccessible.
  intros * Hpart Hor.
  destruct Hor as [Hor| [Hor | Hor]];subst.
  * 
  eapply nextIndirectionNotAccessibleInAnyPartition with 
  (currentPart:=(currentPartition s))
  (currentPD:= currentPD)
  (ptMMUvaNextInd:= ptMMUFstVA) 
  (vaNextInd:= fstVA)
  (ptSh1VaNextInd:=ptSh1FstVA);trivial;unfold consistency;intuition.
  * 
  eapply nextIndirectionNotAccessibleInAnyPartition with 
  (currentPart:=(currentPartition s))
  (currentPD:= currentPD)
  (ptMMUvaNextInd:= ptMMUSndVA) 
  (vaNextInd:= sndVA)
  (ptSh1VaNextInd:=ptSh1SndVA);trivial;unfold consistency;intuition.
   
  * 
  eapply nextIndirectionNotAccessibleInAnyPartition with 
  (currentPart:=(currentPartition s))
  (currentPD:= currentPD)
  (ptMMUvaNextInd:= ptMMUTrdVA) 
  (vaNextInd:= trdVA)
  (ptSh1VaNextInd:=ptSh1TrdVA);trivial;unfold consistency;intuition. }
(** Prove new property:  newIndirectionsAreNotMappedInChildrenAll **)
  unfold newIndirectionsAreNotMappedInChildrenAll , propagatedPropertiesPrepare in *.
  intuition;
  unfold newIndirectionsAreNotMappedInChildren;
  intros * Hchild; subst.
  eapply phyNotDerived with (ptSh1Child:= ptMMUFstVA) (currentPart:=  (currentPartition s) )
  (shadow1:= fstVA) (currentPD:= currentPD);trivial.
  apply vaNotDerived with ptSh1FstVA;trivial.
  unfold consistency in *;intuition.
  intros;subst;split;trivial.
  unfold consistency in *;intuition.
  intros;subst;split;trivial.
  eapply phyNotDerived with (ptSh1Child:= ptMMUSndVA) (currentPart:=  (currentPartition s) )
  (shadow1:= sndVA) (currentPD:= currentPD);trivial.
  apply vaNotDerived with ptSh1SndVA;trivial.
  unfold consistency in *;intuition.
  intros;subst;split;trivial.
  unfold consistency in *;intuition.
  intros;subst;split;trivial.
  eapply phyNotDerived with (ptSh1Child:= ptMMUTrdVA) (currentPart:=  (currentPartition s) )
  (shadow1:= trdVA) (currentPD:= currentPD);trivial.
  apply vaNotDerived with ptSh1TrdVA;trivial.
  unfold consistency in *;intuition.
  intros;subst;split;trivial.
  unfold consistency in *;intuition.
  intros;subst;split;trivial.      
Qed. 