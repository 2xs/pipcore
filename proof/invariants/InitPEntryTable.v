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
    This file contains several invariants of [initPEntryTable] and associated lemmas *)
Require Import Core.Internal Isolation Consistency WeakestPreconditions Invariants.
Require Import StateLib Model.Hardware Model.ADT DependentTypeLemmas 
WritePhyEntry WriteAccessibleRec Model.Lib InternalLemmas.
Require Import Coq.Logic.ProofIrrelevance Omega Model.MAL List Bool.

Lemma initPEntryTableNewProperty table (curidx : index):
{{ fun s => (forall idx : index, idx < curidx -> StateLib.readPhyEntry table idx (memory s) = Some defaultPage) }} 
initPEntryTable table curidx 
{{fun _ s => forall idx, StateLib.readPhyEntry table  idx s.(memory) = Some defaultPage   }}.
Proof.
unfold initPEntryTable.
unfold initPEntryTableAux.
assert(Hsize : tableSize + curidx >= tableSize) by omega.
revert Hsize.
revert table curidx.
generalize tableSize at 1 3. 
induction n.  simpl. 
+ intros. eapply weaken.
  eapply WP.ret. simpl. intros.
  destruct curidx.
  simpl in *.
  omega.
+ intros. simpl. 
(** getMaxIndex *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getMaxIndex.
  intros. simpl.
  pattern s in H.  eassumption. 
  intros maxidx . simpl.
(** MALInternal.Index.ltb *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.Index.ltb.
  intros. simpl.
  pattern s in H.
  eapply H.
  intros ltbindex.     
  simpl. 
(** the last entry *) 
  case_eq ltbindex;intros HnotlastEntry.
  { eapply WP.bindRev.
    eapply WP.weaken.
    eapply Invariants.getDefaultPage.
    intros. simpl.
    pattern s in H.
    eassumption.
    simpl.
    subst.
    intros nullP. simpl. 
(** writePhyEntry **) 
    eapply WP.bindRev.
    eapply weaken.
    eapply WP.writePhyEntry.
    simpl.
    intros.
   try repeat rewrite and_assoc in H.
   pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                 StateLib.readPhyEntry table curidx s.(memory) = Some defaultPage )
    end.
    simpl.
    destruct H as (Hreadlt & Hmax & Hlt & Hnull ).
    split. split.
    intros idx Hidx.
    unfold StateLib.readPhyEntry.
    cbn; simpl in *.
    subst.
    assert(Hfalse : Lib.beqPairs (table, curidx) (table, idx) beqPage beqIndex= false).
    { apply beqPairsFalse. 
      right.
      apply indexDiffLtb.
      right;assumption. }
    rewrite Hfalse.
    assert (Lib.lookup  table idx (Lib.removeDup table curidx (memory s) beqPage beqIndex)
           beqPage beqIndex = Lib.lookup  table idx  (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity.
      right. 
      apply indexDiffLtb.
      left; trivial. }
    rewrite Hmemory.
    apply Hreadlt in Hidx; clear Hreadlt .
    unfold StateLib.readPhyEntry in *.
    assumption.
    repeat split; assumption.
    unfold StateLib.readPhyEntry; cbn.
    assert(Htrue : Lib.beqPairs (table, curidx) (table, curidx) beqPage beqIndex = true).
    { apply beqPairsTrue; split; reflexivity. }
    rewrite Htrue.
    subst;cbn; trivial.
    intros [].
  (** MALInternal.Index.succ **) 
   eapply bindRev.
   eapply WP.weaken. 
   eapply Invariants.Index.succ.
   intros.
   clear IHn.
   simpl.
   split.
   try repeat rewrite and_assoc in H.  
   pattern s in H.
   eassumption.   
   assert (maxidx = CIndex (tableSize - 1) /\ 
   true = StateLib.Index.ltb curidx maxidx)
   as (Hcuridx & Hidx').
   intuition.
   subst.
   symmetry in Hidx'.
   apply  ltbIndexTrue in Hidx'.
   unfold CIndex in Hidx'.
   destruct (lt_dec (tableSize - 1) tableSize).
   simpl in *. assumption. contradict n0.
   assert (tableSize > tableSizeLowerBound).
   apply tableSizeBigEnough.
   unfold tableSizeLowerBound in *.
   omega.
   intros idxsucc.
(** recursion **)
   simpl.
   unfold hoareTriple in *.
   intros.
   apply IHn.
   simpl.
   destruct H.
   clear H IHn.
   unfold StateLib.Index.succ in *.
   case_eq (lt_dec (curidx + 1) tableSize) ;intros; rewrite H in *.
   inversion H0.
   destruct idxsucc, curidx.
   simpl in *.
   omega.
   now contradict H0.
   intros idx Hidx.
   simpl.
   destruct H as  ( (H & Hread &Hnull & HreadPE & HnullP)  & Hsucc).
   assert (Hor : idx = curidx \/ idx < curidx).
    { destruct curidx.
      simpl in *. 
      unfold StateLib.Index.succ in Hsucc.
      simpl in *.
      destruct (lt_dec (i + 1) tableSize).
      destruct idxsucc.
      simpl in *.
      inversion Hsucc.
      simpl in *.
      subst.
      simpl in *. 
      rewrite NPeano.Nat.add_1_r in Hidx.
      apply lt_n_Sm_le in Hidx.
      apply le_lt_or_eq in Hidx.
      destruct Hidx.
      right. assumption.
      left. subst.
      destruct idx. simpl in *.
      subst. 
      assert (Hi = Hi1).
      apply proof_irrelevance.
      subst. reflexivity. inversion Hsucc. }
    destruct Hor.
    subst.
    assumption.
    intuition. }
(** not the last entry **)       
{   eapply WP.bindRev.
    eapply WP.weaken.
    eapply Invariants.getDefaultPage.
    intros. simpl.
    pattern s in H.
    eassumption.
    intros nullP. simpl. 
(** writePhyEntry **)
    eapply WP.bindRev.
    eapply weaken.
    eapply WP.writePhyEntry.
    simpl.
    intros.
   try repeat rewrite and_assoc in H.
   pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                 StateLib.readPhyEntry table curidx s.(memory) = Some defaultPage )
    end.
    simpl.
    destruct H as (Hreadlt & Hmax & Hlt & Hnull ).
    split. split.
    intros idx Hidx.
    unfold StateLib.readPhyEntry.
    cbn; simpl in *.
    subst.
    assert(Hfalse : Lib.beqPairs (table, curidx) (table, idx) beqPage beqIndex= false).
    { apply beqPairsFalse. 
      right.
      apply indexDiffLtb.
      right;assumption. }
    rewrite Hfalse.
    assert (Lib.lookup  table idx (Lib.removeDup table curidx (memory s) beqPage beqIndex)
           beqPage beqIndex = Lib.lookup  table idx  (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity.
      right. 
      apply indexDiffLtb.
      left; trivial. }
    rewrite Hmemory.
    apply Hreadlt in Hidx; clear Hreadlt .
    unfold StateLib.readPhyEntry in *.
    assumption.
    repeat split; assumption.
    unfold StateLib.readPhyEntry; cbn.
    assert(Htrue : Lib.beqPairs (table, curidx) (table, curidx) beqPage beqIndex = true).
    { apply beqPairsTrue; split; reflexivity. }
    rewrite Htrue.
    subst;cbn; trivial.
(** ret true **)
    intros [].
    eapply WP.weaken.  
    eapply WP.ret .
    simpl.
    intros.
    destruct H.  
    destruct H as  ( H  & HnullP  & Hsucc).
    intuition. subst. clear IHn. 
    assert (idx < CIndex (tableSize - 1) \/ idx = CIndex (tableSize - 1)).
    { destruct idx. simpl in *. 
      unfold CIndex.
      case_eq (lt_dec (tableSize - 1) tableSize).
      intros. simpl in *.
      assert (i <= tableSize -1).
      omega.
      apply NPeano.Nat.le_lteq in H3.
      destruct H3.
      left. assumption. right.
      subst.
      assert (Hi =  ADT.CIndex_obligation_1 (tableSize - 1) l).
      apply proof_irrelevance.
      subst. reflexivity.
      intros.
      omega. }
    destruct H2.
    symmetry in H1.
    apply ltbIndexFalse in H1.
    generalize (H idx);clear H;intros Hmaxi.
    apply Hmaxi. subst.
    apply indexBoundEq in H1.
    subst.
    assumption.
    symmetry in H1.
    apply ltbIndexFalse in H1.
    apply indexBoundEq in H1.
    subst.
    assumption.
}
Qed.

Lemma initPEntryTablePropagateProperties1 table phyPDChild
       phySh1Child phySh2Child phyConfigPagesList phyDescChild  (curidx : index) zero  currentPart currentPD
 level ptRefChild descChild idxRefChild presentRefChild ptPDChild pdChild 
 idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child 
 shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList 
 presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild 
 ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 
 derivedSh2Child childListSh1 derivedRefChildListSh1 list :
{{fun s =>  
  (propagatedProperties pdChild currentPart currentPD level ptRefChild descChild idxRefChild
      presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1
      ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list phyPDChild
       phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\ zero = CIndex 0) /\
  (forall partition : page,
  In partition (getPartitions multiplexer s) ->
  partition = table \/ In table (getConfigPagesAux partition s) -> False) /\ 
  (defaultPage =? table) = false 
}} 

initPEntryTable table  curidx 

{{ fun res s =>  
   (propagatedProperties pdChild currentPart currentPD level ptRefChild descChild idxRefChild
      presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1
      ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list phyPDChild
       phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\ zero = CIndex 0)   }}.
Proof.
unfold initPEntryTable.
unfold initPEntryTableAux.
assert(Hsize : tableSize + curidx >= tableSize) by omega.
revert Hsize.
revert curidx.
generalize tableSize at 1 3. 
induction n.  simpl. 
+ intros. eapply weaken.
  eapply WP.ret. simpl. intros.
  destruct curidx.
  simpl in *.
  split ;intuition.
+ intros. simpl. 
(** getMaxIndex *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getMaxIndex.
  intros. simpl.
  pattern s in H.  eassumption. 
  intros maxidx . simpl.
(** MALInternal.Index.ltb *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.Index.ltb.
  intros. simpl.
  pattern s in H.
  eapply H.
  intros ltbindex.     
  simpl. 
(** the last entry *) 
  case_eq ltbindex;intros HnotlastEntry.
  { eapply WP.bindRev.
    eapply WP.weaken.
    eapply Invariants.getDefaultPage.
    intros. simpl.
    (* try repeat rewrite and_assoc in H. *)
    pattern s in H.
    eassumption.
    simpl.
    subst.
    intros nullP. simpl. 
(** writePhyEntry **) 
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writePhyEntry.
    simpl.
    intros.
    try repeat rewrite and_assoc in H. 
    pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s )
    end.
    simpl.
    set (s' := {| currentPartition := currentPartition s;
                  memory := Lib.add table curidx
                              (PE {| read := false; write := false; 
                              exec := false; present := false; 
                              user := false; pa := nullP |})
                              (memory s) beqPage beqIndex |}) in *.
   simpl in *.
   destruct H.
   destruct H0 as (Hzero & Htable & Htablenotnull  & Hmax & Hlt & Hnull ).
   split.
   unfold s'. 
   apply propagatedPropertiesUpdateMappedPageData; trivial.
   split; trivial.
   split.
   intros.
   contradict H1.
   assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
   { unfold s'.
     apply getPartitionsUpdateMappedPageData ; trivial.
     + unfold getPartitions.
       destruct nbPage;simpl;left;trivial.
     + assert(Hfalse : (defaultPage =? table) = false) by trivial.
       apply beq_nat_false in Hfalse.
       unfold not; intros.
       apply Hfalse.
       subst;trivial.
     + unfold propagatedProperties in *; unfold consistency in *. intuition. }
   rewrite Hpartions in *.
   assert(Hconfaux :getConfigPagesAux partition s' = getConfigPagesAux partition s).
   apply getConfigPagesAuxUpdateMappedPageData; trivial.
   unfold getConfigPages; unfold not; simpl.
   apply Htable; trivial.
   rewrite Hconfaux.
   unfold not.
   apply Htable; trivial.
   split; trivial.
   split; intuition. 
   intros [].
  (** MALInternal.Index.succ **) 
   eapply WP.bindRev.
   eapply WP.weaken. 
   eapply Invariants.Index.succ.
   intros.
   clear IHn.
   simpl.
   split.
   pattern s in H.
   eassumption.
   destruct H.
   assert (maxidx = CIndex (tableSize - 1) /\ 
   true = StateLib.Index.ltb curidx maxidx)
   as (Hcuridx & Hidx').
   intuition.
   subst.
   symmetry in Hidx'.
   apply  ltbIndexTrue in Hidx'.
   unfold CIndex in Hidx'.
   destruct (lt_dec (tableSize - 1) tableSize).
   simpl in *. assumption. contradict n0.
   assert (tableSize > tableSizeLowerBound).
   apply tableSizeBigEnough.
   unfold tableSizeLowerBound in *.
   omega.
   intros idxsucc.
(** recursion **)
   simpl.
   unfold hoareTriple in *.
   intros.
   apply IHn.
   simpl.
   destruct H.
   clear H IHn.
   unfold StateLib.Index.succ in *.
   case_eq (lt_dec (curidx + 1) tableSize) ;intros; rewrite H in *.
   inversion H0.
   destruct idxsucc, curidx.
   simpl in *.
   omega.
   now contradict H0. 
   intuition. }
(** not the last entry **)       
{   eapply WP.bindRev.
    eapply WP.weaken.
    eapply Invariants.getDefaultPage.
    intros. simpl.
    pattern s in H.
    eassumption.
    intros nullP. simpl. 
(** writePhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writePhyEntry.
    simpl.
    intros.
    try repeat rewrite and_assoc in H. 
     pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s)
    end.
    simpl.
    set (s' := {| currentPartition := currentPartition s;
                  memory := Lib.add table curidx
                              (PE {| read := false; write := false; exec := false; present := false; user := false; pa := nullP |})
                              (memory s) beqPage beqIndex |}) in *.
    try repeat rewrite and_assoc.
    simpl in *.
    destruct H as (Hprop & Hzero & Htable & Htablenotnull &  Hmax & Hlt & Hnull ).
    split.
    unfold s'. 
    apply propagatedPropertiesUpdateMappedPageData; trivial.
    split; trivial.
    split.
    intros partition Hpartition.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
     { unfold s'.
       apply getPartitionsUpdateMappedPageData ; trivial.
       + unfold getPartitions.
         destruct nbPage;simpl;left;trivial.
       + assert(Hfalse : (defaultPage =? table) = false) by trivial.
         apply beq_nat_false in Hfalse.
         unfold not; intros.
         apply Hfalse.
         subst;trivial.
       + unfold propagatedProperties in *; unfold consistency in *. intuition. }
         rewrite Hpartions in *.
         assert(Hconfaux :getConfigPagesAux partition s' = getConfigPagesAux partition s).
         apply getConfigPagesAuxUpdateMappedPageData; trivial.
         unfold getConfigPages; unfold not; simpl.
         apply Htable; trivial.
         rewrite Hconfaux.
         unfold not.
         apply Htable; trivial.
         split; trivial.
    split; intuition.
    intros [].
    (** ret true **)
    eapply WP.weaken.  
    eapply WP.ret .
    simpl.
    intros. 
    destruct H as (HP & Hzero & Htable & Hnotnull  &  Hmaxidx & Hplt & Hnull).
    intuition.  }

Qed.

Lemma initPEntryTablePropagateProperties2  partition  va1 va2 idxVa1 idxVa2 (table1 table2 : page) phyPage1 
      phyPage2 curidx pdChild currentPart currentPD level ptRefChild descChild idxRefChild
      presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1
      ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList 
      phyDescChild zero :
{{ fun s : state =>
   (propagatedProperties pdChild currentPart currentPD level ptRefChild descChild idxRefChild
      presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1
      ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild
      s /\ zero = CIndex 0) /\
      
      (defaultPage =? table1) = false /\
      (defaultPage =? table2) = false /\
       nextEntryIsPP partition PDidx currentPD s /\
      In partition (getPartitions multiplexer s) /\
   (forall idx : index, StateLib.readPhyEntry phyPage2 idx (memory s) = Some defaultPage) /\ 
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
  Internal.initPEntryTable phyPage1 curidx {{ fun (_ : bool) (s : state) =>
                                               forall idx : index,
                                               StateLib.readPhyEntry phyPage2 idx
                                                 (memory s) = Some defaultPage }}.
Proof.
unfold initPEntryTable.
unfold initPEntryTableAux.
assert(Hsize : tableSize + curidx >= tableSize) by omega.
revert Hsize.
revert curidx.
generalize tableSize at 1 3. 
induction n.  simpl. 
+ intros. eapply weaken.
  eapply WP.ret. simpl. intros.
  destruct curidx.
  simpl in *.
  omega.
+ intros. simpl. 
(** getMaxIndex *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getMaxIndex.
  intros. simpl.
  pattern s in H.  eassumption. 
  intros maxidx . simpl.
(** MALInternal.Index.ltb *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.Index.ltb.
  intros. simpl.
  pattern s in H.
  eapply H.
  intros ltbindex.     
  simpl. 
(** the last entry *) 
  case_eq ltbindex;intros HnotlastEntry.
  { eapply WP.bindRev.
    eapply WP.weaken.
    eapply Invariants.getDefaultPage.
    intros. simpl.
    (* try repeat rewrite and_assoc in H. *)
    pattern s in H.
    eassumption.
    simpl.
    subst.
    intros nullP. simpl. 
(** writePhyEntry **) 
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writePhyEntry.
    simpl.
    intros.
    try repeat rewrite and_assoc in H. 
    pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s )
    end.
    simpl.
    set (s' := {| currentPartition := currentPartition s;
                  memory := Lib.add phyPage1 curidx
                              (PE {| read := false; write := false; 
                              exec := false; present := false; 
                              user := false; pa := nullP |})
                              (memory s) beqPage beqIndex |}) in *.
   simpl in *.
   destruct H.
   destruct H0 as ( Hzero &   Htl1notnull & Htbl2notnull & Hpp & Hmult &
                    Htable & Hpartition & Hnotnull & Hep1 & Hep2 & 
                    Hidx1 & Hidx2 & Htableroot1 & Htableroot2 & Hlevel & Hvas 
                    & Hprensent1 & Hprensent2 & Hmax & Hlt & Hnull ).
   split.
   unfold s'. 
   apply propagatedPropertiesUpdateMappedPageData; trivial.
   assert (Hpde :partitionDescriptorEntry s).
   { unfold propagatedProperties in *.
     unfold consistency in *.
     intuition. }
    split; trivial.
    split; trivial.
    split; trivial.
    split.
    apply nextEntryIsPPUpdateMappedPageData; trivial.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    { unfold s'.
      apply getPartitionsUpdateMappedPageData ; trivial.
      + unfold getPartitions.
        destruct nbPage;simpl;left;trivial.
      + assert(Hfalse : (defaultPage =? phyPage1) = false) by trivial.
        apply beq_nat_false in Hfalse.
        unfold not; intros.
        apply Hfalse.
        subst;trivial. }
    rewrite Hpartions in *; trivial.
    split; trivial.
    split. 
    intros. 
(** readPhyEntry : read the content of a mapped page **)      
    generalize (Htable idx); clear Htable; intros Htable.
    rewrite <- Htable.
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial. 
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with partition  table2 table1  idxVa2 idxVa1
    va2 va1 level s; trivial.
    split.
    unfold s'. 
    intros. contradict H1.
    rewrite getConfigPagesAuxUpdateMappedPageData; trivial.
    unfold not. apply Hpartition; trivial.
    unfold not.
    apply Hpartition; trivial.
    split; trivial.
    split.
    apply isEntryPageUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD va1 idxVa1 s ;
    trivial.
    split.
    apply isEntryPageUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD va2 idxVa2 s ;
    trivial.
    split; trivial.
    split; trivial.
    split.
    intros.
    split. 
    apply isPEUpdateUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD va1 idxVa1 s ;
    trivial.
    apply Htableroot1; trivial.
    apply getTableAddrRootUpdateMappedPageData; trivial.
    assert (isPE table1 idx s /\ getTableAddrRoot table1 PDidx partition va1 s)
    as ( _ & Hget1).
    apply Htableroot1; trivial.
    trivial.
    split.
    intros.
    split. 
    apply isPEUpdateUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD va2 idxVa2 s ;
    trivial.
    apply Htableroot2; trivial.
    apply getTableAddrRootUpdateMappedPageData; trivial.
    assert (isPE table2 idx s /\ getTableAddrRoot table2 PDidx partition va2 s)
    as ( _ & Hget1).
    apply Htableroot2; trivial.
    trivial.
    split; trivial.
    repeat split; trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD va1 idxVa1 s ;
    trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD va2 idxVa2 s ;
    trivial.
    intros [].
    (** MALInternal.Index.succ **) 
     eapply WP.bindRev.
     eapply WP.weaken. 
     eapply Invariants.Index.succ.
     intros.
     clear IHn.
     simpl.
     split.
     pattern s in H.
     eassumption.
     destruct H.
     assert (maxidx = CIndex (tableSize - 1) /\ 
     true = StateLib.Index.ltb curidx maxidx)
     as (Hcuridx & Hidx').
     intuition.
     subst.
     symmetry in Hidx'.
     apply  ltbIndexTrue in Hidx'.
     unfold CIndex in Hidx'.
     destruct (lt_dec (tableSize - 1) tableSize).
     simpl in *. assumption. contradict n0.
     assert (tableSize > tableSizeLowerBound).
     apply tableSizeBigEnough.
     unfold tableSizeLowerBound in *.
     omega.
     intros idxsucc.
(** recursion **)
     simpl.
     unfold hoareTriple in *.
     intros.
     apply IHn.
     simpl.
     destruct H.
     clear H IHn.
     unfold StateLib.Index.succ in *.
     case_eq (lt_dec (curidx + 1) tableSize) ;intros; rewrite H in *.
     inversion H0.
     destruct idxsucc, curidx.
     simpl in *.
     omega.
     now contradict H0. 
     intuition. }
  (** not the last entry **)       
  { eapply WP.bindRev.
    eapply WP.weaken.
    eapply Invariants.getDefaultPage.
    intros. simpl.
    pattern s in H.
    eassumption.
    intros nullP. simpl. 
(** writePhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writePhyEntry.
    simpl.
    intros.
    try repeat rewrite and_assoc in H. 
    pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s )
    end.
    simpl.
    set (s' := {| currentPartition := currentPartition s;
                  memory := Lib.add phyPage1 curidx
                              (PE {| read := false; write := false; 
                              exec := false; present := false; 
                              user := false; pa := nullP |})
                              (memory s) beqPage beqIndex |}) in *.
    simpl in *.
    destruct H.
    destruct H0 as ( Hzero & Htl1notnull & Htbl2notnull & Hpp & Hmult &
                    Htable & Hpartition & Hnotnull & Hep1 & Hep2 & 
                    Hidx1 & Hidx2 & Htableroot1 & Htableroot2 & Hlevel & Hvas & 
                    Hprensent1 & Hprensent2 &  Hmax & Hlt & Hnull ).
    split.
    unfold s'. 
    apply propagatedPropertiesUpdateMappedPageData; trivial.
    assert (Hpde :partitionDescriptorEntry s).
     { unfold propagatedProperties in *.
       unfold consistency in *.
       intuition. }
    split; trivial.
    split; trivial.
    split; trivial.
    split.
    apply nextEntryIsPPUpdateMappedPageData; trivial.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    { unfold s'.
      apply getPartitionsUpdateMappedPageData ; trivial.
      + unfold getPartitions.
        destruct nbPage;simpl;left;trivial.
      + assert(Hfalse : (defaultPage =? phyPage1) = false) by trivial.
        apply beq_nat_false in Hfalse.
        unfold not; intros.
        apply Hfalse.
        subst;trivial. }
    rewrite Hpartions in *; trivial.
    split; trivial.
    split. 
    intros. 
    (** readPhyEntry : read the content of a mapped page **)      
    generalize (Htable idx); clear Htable; intros Htable.
    rewrite <- Htable.
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial. 
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with partition  table2 table1  idxVa2 idxVa1
    va2 va1 level s; trivial.
    split.
    unfold s'. 
    intros. contradict H1.
    rewrite getConfigPagesAuxUpdateMappedPageData; trivial.
    unfold not. apply Hpartition; trivial.
    unfold not.
    apply Hpartition; trivial.
    split; trivial.
    split.
    apply isEntryPageUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD va1 idxVa1 s ;
    trivial.
    split.
    apply isEntryPageUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD va2 idxVa2 s ;
    trivial.
    split; trivial.
    split; trivial.
    split.
    intros.
    split. 
    apply isPEUpdateUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD va1 idxVa1 s ;
    trivial.
    apply Htableroot1; trivial.
    apply getTableAddrRootUpdateMappedPageData; trivial.
    assert (isPE table1 idx s /\ getTableAddrRoot table1 PDidx partition va1 s)
    as ( _ & Hget1).
    apply Htableroot1; trivial.
    trivial.
    split.
    intros.
    split. 
    apply isPEUpdateUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD va2 idxVa2 s ;
    trivial.
    apply Htableroot2; trivial.
    apply getTableAddrRootUpdateMappedPageData; trivial.
    assert (isPE table2 idx s /\ getTableAddrRoot table2 PDidx partition va2 s)
    as ( _ & Hget1).
    apply Htableroot2; trivial.
    trivial.
    split; trivial.
    repeat split; trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD va1 idxVa1 s ;
    trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD va2 idxVa2 s ;
    trivial.
    intros.
    (** ret true **)
    eapply WP.weaken.  
    eapply WP.ret .
    simpl.
    intros.
    intuition.  }
Qed.