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
Require Import Core.Internal Isolation Consistency WeakestPreconditions Invariants.
Require Import StateLib Model.Hardware Model.ADT DependentTypeLemmas 
UpdateMappedPageContent Model.Lib InternalLemmas PropagatedProperties
InitPEntryTable InitVEntryTable .
Require Import Coq.Logic.ProofIrrelevance Omega Model.MAL List Bool.

Lemma initFstShadowNewProperty table (nbL : level)(curidx : index):
{{ fun s => (nbL <> fstLevel /\  ( forall idx : index, idx < curidx -> 
(StateLib.readPhyEntry table idx (memory s) = Some defaultPage) /\ 
 StateLib.readPresent table idx (memory s) = Some false )) \/ 
 
 (nbL = fstLevel /\ (forall idx : index, idx < curidx -> 
(StateLib.readVirEntry table idx (memory s) = Some defaultVAddr) /\ 
 StateLib.readPDflag table idx (memory s) = Some false )) }} 
Internal.initFstShadow table nbL curidx 
{{fun _ s => isWellFormedFstShadow  nbL table s
  }}.
Proof.
unfold Internal.initFstShadow.
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
    apply initVEntryTableNewProperty.
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
    eapply initVEntryTablePreservesProp. 
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
    apply initPEntryTableNewProperty.
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
    omega.
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
    omega.
    destruct H0.
    assumption.    
Qed.

Lemma initFstShadowTablePropagateProperties1  nbL
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
      phyDescChild s /\ 
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
  (defaultPage =? table) = false 
}} 

initFstShadow table  nbL curidx 

{{ fun res s =>  
  ( propagatedProperties false false false false pdChild currentPart currentPD level ptRefChild
      descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1
      idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
      phyDescChild s /\  
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
unfold Internal.initFstShadow.
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
    apply initVEntryTablePropagateProperties1.
    simpl.
    intros.
    intuition.
 -  intros. eapply weaken.
    apply initPEntryTablePropagateProperties1.
    simpl.
    intros.
    intuition.
Qed.

Lemma initFstShadowPropagateProperties2 nbL accessibleChild accessibleSh1 accessibleSh2 accessibleList 
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
     In partition (getAncestors currentPart s) -> ~ In phyDescChild (getAccessibleMappedPages partition s)))
/\ zero = CIndex 0) /\
      
      (defaultPage =? table1) = false /\
      (defaultPage =? table2) = false /\
       nextEntryIsPP partition PDidx currentPD s /\
      In partition (getPartitions multiplexer s) /\
              
  ( forall idx, StateLib.readPhyEntry phyPage2  idx s.(memory) = Some defaultPage /\ 
              StateLib.readPresent phyPage2 idx (memory s) = Some false )
              /\ 
   
   
   (forall partition : page,
    In partition (getPartitions multiplexer s) -> 
    partition = phyPage1 \/ In phyPage1 (getConfigPagesAux partition s) -> False) /\
   ( (defaultPage =? phyPage1) = false) /\ 
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
       false = checkVAddrsEqualityWOOffset nbLevel va2 va1 level /\
       entryPresentFlag table1 idxVa1 true s /\ entryPresentFlag table2 idxVa2 true s

}} 
 initFstShadow  phyPage1 nbL curidx {{ fun _  (s : state) =>
 ( forall idx, StateLib.readPhyEntry phyPage2  idx s.(memory) = Some defaultPage /\ 
              StateLib.readPresent phyPage2 idx (memory s) = Some false )
              }}.
Proof.
unfold initFstShadow.
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
    eapply initVEntryTablePropagateProperties2.
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
