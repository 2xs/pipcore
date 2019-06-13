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
UpdateMappedPageContent Model.Lib InternalLemmas PropagatedProperties.
Require Import Coq.Logic.ProofIrrelevance Omega Model.MAL List Bool.
(************************ TO BE MOVED ***********************)

(************************************************************)

Lemma initPEntryTableSchema table (curidx : index):
{{ fun (s : state)=> True }} 
initPEntryTable table curidx 
{{fun _ s => True  }}.
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
  eapply WP.bindRev.
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
               StateLib.readPhyEntry table curidx s.(memory) = Some defaultPage  /\
                      StateLib.readPresent table curidx (memory s) = Some false )
  end.
  simpl.
  destruct H as (Hreadlt & Hmax & Hlt & Hnull ).
  split. split.
  trivial. (** PROVE POSTCONDITION **)
  repeat split; assumption.
  unfold StateLib.readPhyEntry ,StateLib.readPresent; cbn.
  assert(Htrue : Lib.beqPairs (table, curidx) (table, curidx) beqPage beqIndex = true).
  { apply beqPairsTrue; split; reflexivity. }
  rewrite Htrue.
  subst;cbn; trivial.
  split;trivial.    
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
  apply  indexltbTrue in Hidx'.
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
  trivial. (** PROVE POSTCONDITION *) 
(** not the last entry **)       
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getDefaultPage.
  intros. simpl.
  pattern s in H.
  eassumption.
  intros nullP. simpl. 
(** writePhyEntry **)
  eapply strengthen.
  eapply weaken.
  eapply WP.writePhyEntry.
  simpl.
  intros.
 try repeat rewrite and_assoc in H.
 pattern s in H.
  match type of H with 
  | ?HT s => instantiate (1 := fun tt s => HT s /\ 
              ( StateLib.readPhyEntry table curidx s.(memory) = Some defaultPage /\
    StateLib.readPresent table curidx (memory s) = Some false))
  end.
  simpl.
  destruct H as (Hreadlt & Hmax & Hlt & Hnull ).
  split. split.
  trivial. (** PROVE PRECONDITION *) 
  repeat split; assumption.
  unfold StateLib.readPhyEntry, StateLib.readPresent ; cbn.
  assert(Htrue : Lib.beqPairs (table, curidx) (table, curidx) beqPage beqIndex = true).
  { apply beqPairsTrue; split; reflexivity. }
  rewrite Htrue.
  subst;cbn; split;trivial.
  simpl. 
(** ret true **)
  intros.
  trivial. (** PROVE POSTCONDITION *) 
Qed.

                    
Lemma initPEntryTableNewPropertyL table (curidx : index):
{{ fun s => initPEntryTablePreconditionToProveNewProperty s table curidx }} 
initPEntryTable table curidx 
{{fun _ s =>  isWellFormedMMUTables table s }}.
Proof.
unfold initPEntryTable, initPEntryTablePreconditionToProveNewProperty, isWellFormedMMUTables .
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
                 StateLib.readPhyEntry table curidx s.(memory) = Some defaultPage  /\
                        StateLib.readPresent table curidx (memory s) = Some false )
    end.
    simpl.
    destruct H as (Hreadlt & Hmax & Hlt & Hnull ).
    split. split.
    intros idx Hidx.
    unfold StateLib.readPhyEntry, StateLib.readPresent.
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
    unfold StateLib.readPhyEntry, StateLib.readPresent in *.
    simpl.
    assumption.
    repeat split; assumption.
    unfold StateLib.readPhyEntry ,StateLib.readPresent; cbn.
    assert(Htrue : Lib.beqPairs (table, curidx) (table, curidx) beqPage beqIndex = true).
    { apply beqPairsTrue; split; reflexivity. }
    rewrite Htrue.
    subst;cbn; trivial.
    split;trivial.    
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
   apply  indexltbTrue in Hidx'.
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
    apply H;trivial. }
(** not the last entry **)       
{   eapply WP.bindRev.
    eapply WP.weaken.
    eapply Invariants.getDefaultPage.
    intros. simpl.
    pattern s in H.
    eassumption.
    intros nullP. simpl. 
(** writePhyEntry **)
    eapply strengthen.
    eapply weaken.
    eapply WP.writePhyEntry.
    simpl.
    intros.
   try repeat rewrite and_assoc in H.
   pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                ( StateLib.readPhyEntry table curidx s.(memory) = Some defaultPage /\
      StateLib.readPresent table curidx (memory s) = Some false))
    end.
    simpl.
    destruct H as (Hreadlt & Hmax & Hlt & Hnull ).
    split. split.
    intros idx Hidx.
    unfold StateLib.readPhyEntry, StateLib.readPresent  .
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
    unfold StateLib.readPhyEntry , StateLib.readPresent in *.
    assumption.
    repeat split; assumption.
    unfold StateLib.readPhyEntry, StateLib.readPresent ; cbn.
    assert(Htrue : Lib.beqPairs (table, curidx) (table, curidx) beqPage beqIndex = true).
    { apply beqPairsTrue; split; reflexivity. }
    rewrite Htrue.
    subst;cbn; split;trivial.
    simpl. 
(** ret true **)
    intros.
    destruct H.  
    destruct H as  ( H  & HnullP  & Hsucc).
     subst. clear IHn. 
    assert (idx < CIndex (tableSize - 1) \/ idx = CIndex (tableSize - 1)).
    { destruct idx. simpl in *. 
      unfold CIndex.
      case_eq (lt_dec (tableSize - 1) tableSize).
      intros. simpl in *.
      assert (i <= tableSize -1).
      omega.
      apply NPeano.Nat.le_lteq in H2.
      destruct H2.
      left. assumption. right.
      subst.
      assert (Hi =  ADT.CIndex_obligation_1 (tableSize - 1) l).
      apply proof_irrelevance.
      subst. reflexivity.
      intros.
      omega. }
    destruct H1.
    destruct Hsucc.
    subst.
    symmetry in H2.
    apply indexltbFalse in H2.
    generalize (H idx);clear H;intros Hmaxi.
    apply Hmaxi. subst.
    apply indexBoundEq in H2.
    subst.
    assumption.
    destruct Hsucc.
    subst.
    symmetry in H2.
    apply indexltbFalse in H2.
    apply indexBoundEq in H2.
    subst.
    assumption.
    
}
Qed.

Lemma initPEntryTablePropagateProperties1  
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

initPEntryTable table  curidx 

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
   destruct H0 as (Hnew1 & Hnew2 & Hnew3 & Hnew4 & Hnew5 & Hzero & 
   Htable & Htablenotnull  & Hmax & Hlt & Hnull ).
   split.
   unfold s'. 
   apply propagatedPropertiesUpdateMappedPageData; trivial.
   rewrite Hnull.
   (** isPresentNotDefaultIff **)
   apply isPresentNotDefaultIffRightValue.
   unfold propagatedProperties in *.
   unfold consistency in *.
   intuition.
   unfold propagatedProperties in *.  
   assert(Hcurpart : In currentPart (getPartitions multiplexer s)).
   {unfold consistency in *. 
   intuition. 
   subst.
   unfold currentPartitionInPartitionsList in *.    
   subst;intuition. }
   try repeat split;trivial; try (   
   apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition).
   intros.
   contradict H1.
   assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
   { unfold s'.
     apply getPartitionsUpdateMappedPageData ; trivial.
     + unfold consistency in *. intuition. 
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
   apply  indexltbTrue in Hidx'.
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
    intros nullP.
    simpl. 
(** writePhyEntry **)
    eapply WP.strengthen.
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
    destruct H as (Hprop & Hnew1 & Hnew2 & Hnew3 & Hnew4 & Hnew5 & Hzero & Htable & Htablenotnull &  Hmax & Hlt & Hnull ).
    split.
    unfold s'. 
    apply propagatedPropertiesUpdateMappedPageData; trivial.
    (** isPresentNotDefaultIff **)
    rewrite Hnull.
   apply isPresentNotDefaultIffRightValue.
   unfold propagatedProperties in *.
   unfold consistency in *.
   intuition.
   unfold propagatedProperties in *. 
   assert(Hcurpart : In currentPart (getPartitions multiplexer s)).
   {  unfold consistency in *. 
      intuition. 
      subst.
      unfold currentPartitionInPartitionsList in *.    
      subst;intuition. }
   try repeat split;trivial; try (   
   apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition).
    intros partition Hpartition.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
     { unfold s'.
       apply getPartitionsUpdateMappedPageData ; trivial.
       + unfold consistency in *. intuition. 
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
     intuition.
     intuition. }
Qed.

Lemma initPEntryTablePropagateProperties2  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
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
      s /\ ((((forall partition : page,
        In partition (getAncestors currentPart s) -> ~ In phyPDChild (getAccessibleMappedPages partition s)) /\
       (forall partition : page,
        In partition (getAncestors currentPart s) -> ~ In phySh1Child (getAccessibleMappedPages partition s))) /\
      (forall partition : page,
       In partition (getAncestors currentPart s) -> ~ In phySh2Child (getAccessibleMappedPages partition s))) /\
     (forall partition : page,
      In partition (getAncestors currentPart s) -> ~ In phyConfigPagesList (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phyDescChild (getAccessibleMappedPages partition s))) /\ zero = CIndex 0) /\
      
      (defaultPage =? table1) = false /\
      (defaultPage =? table2) = false /\
       nextEntryIsPP partition PDidx currentPD s /\
      In partition (getPartitions multiplexer s) /\
   (forall idx : index, StateLib.readPhyEntry phyPage2 idx (memory s) = Some defaultPage /\
   StateLib.readPresent phyPage2 idx (memory s) = Some false ) /\ 
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
  Internal.initPEntryTable phyPage1 curidx {{ fun _  (s : state) =>
                                               forall idx : index,
                                               StateLib.readPhyEntry phyPage2 idx
                                                 (memory s) = Some defaultPage/\
                                               StateLib.readPresent phyPage2 idx
                                                 (memory s) = 
                                               Some false }}.
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
   destruct H0 as (  Hnew1 & Hnew2 & Hnew3 & Hnew4 & Hnew5 & Hzero &   Htl1notnull & Htbl2notnull & Hpp & Hmult &
                    Htable & Hpartition & Hnotnull & Hep1 & Hep2 & 
                    Hidx1 & Hidx2 & Htableroot1 & Htableroot2 & Hlevel & Hvas 
                    & Hprensent1 & Hprensent2 & Hmax & Hlt & Hnull ).
   split.
   unfold s'. 
   apply propagatedPropertiesUpdateMappedPageData; trivial.
      (** isPresentNotDefaultIff **)
    rewrite Hnull.
   apply isPresentNotDefaultIffRightValue.
   unfold propagatedProperties in *.
   unfold consistency in *.
      intuition.
   assert (Hpde :partitionDescriptorEntry s).
   { unfold propagatedProperties in *.
     unfold consistency in *.
     intuition. }
unfold propagatedProperties in *.  
   assert(Hcurpart : In currentPart (getPartitions multiplexer s)).
   {unfold consistency in *. 
   intuition. 
   subst.
   unfold currentPartitionInPartitionsList in *.    
   subst;intuition. }
   
  (*  try repeat split; trivial. *)
  split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
  split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition.  (** New Prop*) 
  split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
  split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
  split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*)  
    split; trivial.
    split; trivial.
    split; trivial.
    split.
    apply nextEntryIsPPUpdateMappedPageData; trivial.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    { unfold s'.
    
      apply getPartitionsUpdateMappedPageData ; trivial.
      + unfold consistency in *. intuition. 
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
    assert( phyPage1 <> phyPage2).
    { 
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with partition  table2 table1  idxVa2 idxVa1
    va2 va1 level s; trivial. }  
    generalize (Htable idx); clear Htable; intros Htable.
    split.
    destruct Htable as (Htable1 & Htable2). 
    rewrite <- Htable1.
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial.
     destruct Htable as (Htable1 & Htable2). 
    rewrite <- Htable2.
    symmetry.
    apply readPresentUpdateMappedPageData; trivial.
   
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
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va1 idxVa1 s ;
    trivial.
    left;trivial.
    split.
    apply isEntryPageUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va2 idxVa2 s ;
    trivial.
    left;trivial. 
    split; trivial.
    split; trivial.
    split.
    intros.
    split. 
    apply isPEUpdateUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va1 idxVa1 s ;
    trivial.
    left;trivial.
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
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va2 idxVa2 s ;
    trivial.
    left;trivial.
    apply Htableroot2; trivial.
    apply getTableAddrRootUpdateMappedPageData; trivial.
    assert (isPE table2 idx s /\ getTableAddrRoot table2 PDidx partition va2 s)
    as ( _ & Hget1).
    apply Htableroot2; trivial.
    trivial.
    split; trivial.
    repeat split; trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va1 idxVa1 s ;
    trivial. left;trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va2 idxVa2 s ;
    trivial. left;trivial.
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
     apply  indexltbTrue in Hidx'.
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
    eapply WP.strengthen.
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
    destruct H0 as (  Hnew1 & Hnew2 & Hnew3 & Hnew4 & Hnew5 & Hzero & Htl1notnull & Htbl2notnull & Hpp & Hmult &
                    Htable & Hpartition & Hnotnull & Hep1 & Hep2 & 
                    Hidx1 & Hidx2 & Htableroot1 & Htableroot2 & Hlevel & Hvas & 
                    Hprensent1 & Hprensent2 &  Hmax & Hlt & Hnull ).
    split.
    unfold s'. 
    apply propagatedPropertiesUpdateMappedPageData; trivial.
       (** isPresentNotDefaultIff **)
    rewrite Hnull.
   apply isPresentNotDefaultIffRightValue.
   unfold propagatedProperties in *.
   unfold consistency in *.
      intuition.
    assert (Hpde :partitionDescriptorEntry s).
     { unfold propagatedProperties in *.
       unfold consistency in *.
       intuition. }
    unfold propagatedProperties in *.  
   assert(Hcurpart : In currentPart (getPartitions multiplexer s)).
   {unfold consistency in *. 
   intuition. 
   subst.
   unfold currentPartitionInPartitionsList in *.    
   subst;intuition. }
    split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
  split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition.  (** New Prop*) 
  split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
  split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
  split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*)  
  
    split; trivial.
    split; trivial.
    split; trivial.
    split.
    apply nextEntryIsPPUpdateMappedPageData; trivial.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    { unfold s'.
      apply getPartitionsUpdateMappedPageData ; trivial.
      + unfold consistency in *. intuition. 
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
        assert (phyPage1 <> phyPage2).  
    { unfold propagatedProperties in *. 
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with partition  table2 table1  idxVa2 idxVa1
    va2 va1 level s; trivial. }
    destruct Htable as (Htable1 & Htable2).
    split.
    rewrite <- Htable1.
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial.
    rewrite <- Htable2.
    symmetry.
    apply readPresentUpdateMappedPageData;trivial.
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
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va1 idxVa1 s ;
    trivial. left;trivial.
    split.
    apply isEntryPageUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va2 idxVa2 s ;
    trivial. left;trivial.
    split; trivial.
    split; trivial.
    split.
    intros.
    split. 
    apply isPEUpdateUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va1 idxVa1 s ;
    trivial. left;trivial.
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
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va2 idxVa2 s ;
    trivial. left;trivial.
    apply Htableroot2; trivial.
    apply getTableAddrRootUpdateMappedPageData; trivial.
    assert (isPE table2 idx s /\ getTableAddrRoot table2 PDidx partition va2 s)
    as ( _ & Hget1).
    apply Htableroot2; trivial.
    trivial.
    split; trivial.
    repeat split; trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va1 idxVa1 s ;
    trivial. left;trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va2 idxVa2 s ;
    trivial. left;trivial.
    intros.
    simpl in *.
    assert((forall idx : index,
     StateLib.readPhyEntry phyPage2 idx (memory s) = Some defaultPage /\
     StateLib.readPresent phyPage2 idx (memory s) = Some false))  by intuition.
     apply H0. }
Qed.

Lemma initPEntryTablePropagateProperties3  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
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
      s /\ 
      ((((forall partition : page,
        In partition (getAncestors currentPart s) -> ~ In phyPDChild (getAccessibleMappedPages partition s)) /\
       (forall partition : page,
        In partition (getAncestors currentPart s) -> ~ In phySh1Child (getAccessibleMappedPages partition s))) /\
      (forall partition : page,
       In partition (getAncestors currentPart s) -> ~ In phySh2Child (getAccessibleMappedPages partition s))) /\
     (forall partition : page,
      In partition (getAncestors currentPart s) -> ~ In phyConfigPagesList (getAccessibleMappedPages partition s)) /\
    (forall partition : page,
     In partition (getAncestors currentPart s) -> ~ In phyDescChild (getAccessibleMappedPages partition s)))/\ zero = CIndex 0) /\
      
      (defaultPage =? table1) = false /\
      (defaultPage =? table2) = false /\
       nextEntryIsPP partition PDidx currentPD s /\
      In partition (getPartitions multiplexer s) /\
   ( (level <> fstLevel /\
    (forall idx : index,
     StateLib.readPhyEntry phyPage2 idx (memory s) = Some defaultPage /\ 
     StateLib.readPresent phyPage2 idx (memory s) = Some false) \/
    level = fstLevel /\
    (forall idx : index,
     StateLib.readVirEntry phyPage2 idx (memory s) = Some defaultVAddr /\ 
     StateLib.readPDflag phyPage2 idx (memory s) = Some false)
   
    
   
   )) /\ 
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
  Internal.initPEntryTable phyPage1 curidx {{ fun _  (s : state) =>
                                                (level <> fstLevel /\
    (forall idx : index,
     StateLib.readPhyEntry phyPage2 idx (memory s) = Some defaultPage /\ 
     StateLib.readPresent phyPage2 idx (memory s) = Some false) \/
    level = fstLevel /\
    (forall idx : index,
     StateLib.readVirEntry phyPage2 idx (memory s) = Some defaultVAddr /\ 
     StateLib.readPDflag phyPage2 idx (memory s) = Some false)
   
    
   
   ) }}.
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
  intuition.
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
   destruct H0 as (  Hnew1 & Hnew2 & Hnew3 & Hnew4 & Hnew5 & Hzero &  Htl1notnull & Htbl2notnull & Hpp & Hmult &
                    Htable & Hpartition & Hnotnull & Hep1 & Hep2 & 
                    Hidx1 & Hidx2 & Htableroot1 & Htableroot2 & Hlevel & Hvas 
                    & Hprensent1 & Hprensent2 & Hmax & Hlt & Hnull ).
   split.
   unfold s'. 
   apply propagatedPropertiesUpdateMappedPageData; trivial.
      (** isPresentNotDefaultIff **)
    rewrite Hnull.
   apply isPresentNotDefaultIffRightValue.
   unfold propagatedProperties in *.
   unfold consistency in *.
      intuition.
   assert (Hpde :partitionDescriptorEntry s).
   { unfold propagatedProperties in *.
     unfold consistency in *.
     intuition. }
   unfold propagatedProperties in *.  
   assert(Hcurpart : In currentPart (getPartitions multiplexer s)).
   { unfold consistency in *. 
   intuition;
   subst;
   unfold currentPartitionInPartitionsList in *;
   subst;intuition. }
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition.  (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*)  
    split; trivial.
    split; trivial.
    split; trivial.
    split.
    apply nextEntryIsPPUpdateMappedPageData; trivial.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    { unfold s'.
    
      apply getPartitionsUpdateMappedPageData ; trivial.
      + unfold consistency in *. intuition. 
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
    assert( phyPage1 <> phyPage2).
    { 
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with partition  table2 table1  idxVa2 idxVa1
    va2 va1 level s; trivial.
    intuition. }
     destruct Htable as [(HnbL & Htable )|(HnbL & Htable)].
    left.
    split;trivial.
    intros.
      
    generalize (Htable idx); clear Htable; intros Htable.
    split.
    destruct Htable as (Htable1 & Htable2). 
    rewrite <- Htable1.
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial.
     destruct Htable as (Htable1 & Htable2). 
    rewrite <- Htable2.
    symmetry.
    apply readPresentUpdateMappedPageData; trivial.
    right.
    split;trivial.
    intros.
     destruct Htable with idx as  (Htable1 & Htable2).
     split. 
    rewrite <- Htable1.
     apply readVirEntryUpdateMappedPageData; trivial.
    rewrite <- Htable2.
    apply readPDflagUpdateMappedPageData; trivial.
    unfold not;intros Hfalse;rewrite Hfalse in *; now contradict H0.
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
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va1 idxVa1 s ;
    trivial.
    left;trivial.
    split.
    apply isEntryPageUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va2 idxVa2 s ;
    trivial.
    left;trivial. 
    split; trivial.
    split; trivial.
    split.
    intros.
    split. 
    apply isPEUpdateUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va1 idxVa1 s ;
    trivial.
    left;trivial.
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
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va2 idxVa2 s ;
    trivial.
    left;trivial.
    apply Htableroot2; trivial.
    apply getTableAddrRootUpdateMappedPageData; trivial.
    assert (isPE table2 idx s /\ getTableAddrRoot table2 PDidx partition va2 s)
    as ( _ & Hget1).
    apply Htableroot2; trivial.
    trivial.
    split; trivial.
    repeat split; trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va1 idxVa1 s ;
    trivial. left;trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va2 idxVa2 s ;
    trivial. left;trivial.
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
     apply  indexltbTrue in Hidx'.
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
    eapply WP.strengthen.
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
    destruct H0 as ( Hnew1 & Hnew2 & Hnew3 & Hnew4 & Hnew5 & Hzero & Htl1notnull & Htbl2notnull & Hpp & Hmult &
                    Htable & Hpartition & Hnotnull & Hep1 & Hep2 & 
                    Hidx1 & Hidx2 & Htableroot1 & Htableroot2 & Hlevel & Hvas & 
                    Hprensent1 & Hprensent2 &  Hmax & Hlt & Hnull ).
    split.
    unfold s'. 
    apply propagatedPropertiesUpdateMappedPageData; trivial.
       (** isPresentNotDefaultIff **)
    rewrite Hnull.
   apply isPresentNotDefaultIffRightValue.
   unfold propagatedProperties in *.
   unfold consistency in *.
      intuition.
    assert (Hpde :partitionDescriptorEntry s).
     { unfold propagatedProperties in *.
       unfold consistency in *.
       intuition. }
   unfold propagatedProperties in *.  
   assert(Hcurpart : In currentPart (getPartitions multiplexer s)).
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
    split; trivial.
    split; trivial.
    split; trivial.
    split.
    apply nextEntryIsPPUpdateMappedPageData; trivial.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    { unfold s'.
      apply getPartitionsUpdateMappedPageData ; trivial.
      + unfold consistency in *. intuition. 
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
        assert (phyPage1 <> phyPage2).  
    { unfold propagatedProperties in *. 
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with partition  table2 table1  idxVa2 idxVa1
    va2 va1 level s; trivial.
    intuition. }
      destruct Htable as [(HnbL & Htable )|(HnbL & Htable)].
    left.
    split;trivial.
    intros.
    generalize (Htable idx); clear Htable; intros Htable.
    split.
    destruct Htable as (Htable1 & Htable2). 
    rewrite <- Htable1.
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial.
     destruct Htable as (Htable1 & Htable2). 
    rewrite <- Htable2.
    symmetry.
    apply readPresentUpdateMappedPageData; trivial.
    right.
    split;trivial.
    intros.
     destruct Htable with idx as  (Htable1 & Htable2).
     split. 
    rewrite <- Htable1.
     apply readVirEntryUpdateMappedPageData; trivial.
    rewrite <- Htable2.
    apply readPDflagUpdateMappedPageData; trivial.
    unfold not;intros Hfalse;rewrite Hfalse in *; now contradict H0.
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
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va1 idxVa1 s ;
    trivial. left;trivial.
    split.
    apply isEntryPageUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va2 idxVa2 s ;
    trivial. left;trivial.
    split; trivial.
    split; trivial.
    split.
    intros.
    split. 
    apply isPEUpdateUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va1 idxVa1 s ;
    trivial. left;trivial.
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
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va2 idxVa2 s ;
    trivial. left;trivial.
    apply Htableroot2; trivial.
    apply getTableAddrRootUpdateMappedPageData; trivial.
    assert (isPE table2 idx s /\ getTableAddrRoot table2 PDidx partition va2 s)
    as ( _ & Hget1).
    apply Htableroot2; trivial.
    trivial.
    split; trivial.
    repeat split; trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va1 idxVa1 s ;
    trivial. left;trivial.
    apply entryPresentFlagUpdateMappedPageData; trivial.
    apply mappedPageIsNotPTable with partition  currentPD isPE PDidx va2 idxVa2 s ;
    trivial. left;trivial.
    intros.
    simpl in *.
    intuition. }
Qed.

Lemma initPEntryTablePreservesProp table (nbL : level)(curidx : index):
{{ fun s : state =>

   false = StateLib.Level.eqb nbL fstLevel }} 
  initPEntryTable table curidx {{ fun (_ : unit) (_ : state) =>
                                  false = StateLib.Level.eqb nbL fstLevel }}.
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
  
  intuition.
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
   split;trivial.
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
   apply  indexltbTrue in Hidx'.
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
    eapply WP.strengthen.
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
    intuition.
    intros .
    simpl in *; intuition. }
Qed. 



 Lemma initPEntryTablePropagateProperties curidx table ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
        currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
        currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA lpred zeroI LLroot LLChildphy newLastLLable minFI:
{{ fun s : state =>
propagatedPropertiesPrepare LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
        lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
        currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false
        false false true true true idxFstVA idxSndVA idxTrdVA zeroI minFI
/\ isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA
/\ writeAccessibleRecPreparePostcondition currentPart phyMMUaddr s 
/\ writeAccessibleRecPreparePostcondition currentPart phySh1addr s 
/\ writeAccessibleRecPreparePostcondition currentPart phySh2addr s 
/\ StateLib.Level.pred l = Some lpred 
/\ zeroI = CIndex 0 
/\ initPEntryTablePreconditionToPropagatePrepareProperties s table }} 

      Internal.initPEntryTable table curidx 

{{ fun _ (s : state) => propagatedPropertiesPrepare LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
        lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
        currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false
        false false true true true idxFstVA idxSndVA idxTrdVA zeroI minFI
/\ isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA 
/\ writeAccessibleRecPreparePostcondition currentPart phyMMUaddr s 
/\ writeAccessibleRecPreparePostcondition currentPart phySh1addr s 
/\ writeAccessibleRecPreparePostcondition currentPart phySh2addr s 
/\ StateLib.Level.pred l = Some lpred  }}.
Proof.
unfold initPEntryTable.
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
  eapply WP.bindRev.
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
               StateLib.readPhyEntry table curidx s.(memory) = Some defaultPage  /\
                      StateLib.readPresent table curidx (memory s) = Some false )
  end.
  simpl.
  simpl in H.
(*   destruct H as (Hreadlt & Hmax & Hlt & Hnull ). *)
  split.
   (** PROVE POSTCONDITION **)
    assert(Hcurpart:In (currentPartition s) (getPartitions multiplexer s)) by (unfold propagatedPropertiesPrepare, consistency  in *;subst;intuition;subst;trivial).
    split.
    (** propagatedPropertiesPrepare *)
    intuition;subst.
    apply propagatePropertiesPrepareUpdateMappedPageContent;trivial.
    apply isPresentNotDefaultIffRightValue;trivial.
    unfold propagatedPropertiesPrepare in *;unfold consistency in *;intuition.
    split.
    unfold propagatedPropertiesPrepare in *.
    intuition.
    Set Nested Proofs Allowed.

apply isPartitionFalseAllUpdateMappedPageContent with 
 currentShadow1 fstVA sndVA trdVA;trivial.
     
    (** writeAccessibleRecPreparePostcondition  **)
    assert(initPEntryTablePreconditionToPropagatePrepareProperties s table) as (Hi & Hfalse) by intuition.
    unfold propagatedPropertiesPrepare, initPEntryTablePreconditionToPropagatePrepareProperties in *;intuition subst;trivial;
    unfold writeAccessibleRecPreparePostcondition in *.
    apply writeAccessibleRecPostCondUpdateMappedPageData;trivial.
    apply writeAccessibleRecPostCondUpdateMappedPageData;trivial.
    apply writeAccessibleRecPostCondUpdateMappedPageData;trivial.
    (** initPEntryTablePreconditionToPropagatePrepareProperties *)
    set(s':= {| currentPartition := _ |}) in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    { apply getPartitionsUpdateMappedPageData ; trivial;unfold consistency in *;intuition.
      + unfold getPartitions.
        destruct nbPage;simpl;left;trivial.
      + apply beq_nat_false in Hfalse.
        unfold not; intros.
        apply Hfalse.
        subst;trivial. }
    rewrite Hpartions in *.
    unfold s' in *.
    rewrite getConfigPagesUpdateMappedPageData in *.
    apply Hi with partition;trivial.
    unfold not;intros.
    apply Hi with partition;trivial.
  (** the postcondition of the current function *)
  unfold StateLib.readPhyEntry ,StateLib.readPresent; cbn.
  assert(Htrue : Lib.beqPairs (table, curidx) (table, curidx) beqPage beqIndex = true).
  { apply beqPairsTrue; split; reflexivity. }
  rewrite Htrue.
  subst;cbn; trivial.
  split;trivial.
  intuition.
  subst.
  trivial.    
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
  apply  indexltbTrue in Hidx'.
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
  intuition. (** PROVE PRECONDITION *) 
(** not the last entry **)       
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getDefaultPage.
  intros. simpl.
  pattern s in H.
  eassumption.
  intros nullP. simpl. 
(** writePhyEntry **)
  eapply strengthen.
  eapply weaken.
  eapply WP.writePhyEntry.
  simpl.
  intros.
 try repeat rewrite and_assoc in H.
 pattern s in H.
  match type of H with 
  | ?HT s => instantiate (1 := fun tt s => HT s /\ 
              ( StateLib.readPhyEntry table curidx s.(memory) = Some defaultPage /\
    StateLib.readPresent table curidx (memory s) = Some false))
  end.
  simpl.
  destruct H as (Hreadlt & Hmax & Hlt & Hnull ).
  split.
  (** PROVE POSTCONDITION **)
  assert(Hcurpart:In (currentPartition s) (getPartitions multiplexer s)) by (unfold propagatedPropertiesPrepare, consistency  in *;subst;intuition;subst;trivial).
  split.
  (** propagatedPropertiesPrepare *)
  intuition;subst.
  apply propagatePropertiesPrepareUpdateMappedPageContent;trivial.
  apply isPresentNotDefaultIffRightValue;trivial.
  unfold propagatedPropertiesPrepare in *;unfold consistency in *;intuition. 
  (** writeAccessibleRecPreparePostcondition  **)
  assert(initPEntryTablePreconditionToPropagatePrepareProperties s table) as (Hi & Hfalse) by intuition.
  unfold propagatedPropertiesPrepare, initPEntryTablePreconditionToPropagatePrepareProperties in *;intuition subst;trivial;
  unfold writeAccessibleRecPreparePostcondition in *.
apply isPartitionFalseAllUpdateMappedPageContent with 
 currentShadow1 fstVA sndVA trdVA;trivial.
 unfold initPEntryTablePreconditionToPropagatePrepareProperties;intuition.
  apply writeAccessibleRecPostCondUpdateMappedPageData;trivial.
  apply writeAccessibleRecPostCondUpdateMappedPageData;trivial.
  apply writeAccessibleRecPostCondUpdateMappedPageData;trivial.
  (** initPEntryTablePreconditionToPropagatePrepareProperties *)
  set(s':= {| currentPartition := _ |}) in *.
  assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
  { apply getPartitionsUpdateMappedPageData ; trivial;unfold consistency in *;intuition.
    + unfold getPartitions.
      destruct nbPage;simpl;left;trivial.
    + apply beq_nat_false in Hfalse.
      unfold not; intros.
      apply Hfalse.
      subst;trivial. }
  rewrite Hpartions in *.
  unfold s' in *.
  rewrite getConfigPagesUpdateMappedPageData in *.
  apply Hi with partition;trivial.
  unfold not;intros.
  apply Hi with partition;trivial.
  unfold StateLib.readPhyEntry, StateLib.readPresent ; cbn.
  assert(Htrue : Lib.beqPairs (table, curidx) (table, curidx) beqPage beqIndex = true).
  { apply beqPairsTrue; split; reflexivity. }
  rewrite Htrue.
  subst;cbn; split;trivial.
  simpl.
  intuition. subst;trivial. 
(** ret true **)
  intros.
  simpl in *.
  intuition. (** PROVE POSTCONDITION *) 
Qed.

Lemma initPEntryTablePropagateIsWellFormedMMUTable phyPage1 (curidx : index) 
phyPage2 va1 va2 table1 table2 (level:level) partition currentPD:
{{ fun s => isWellFormedMMUTables phyPage2 s 
/\ PreCtoPropagateIsWellFormedMMUTables phyPage1 phyPage2  
va1 va2  table1 table2 partition level currentPD s
  }} 
initPEntryTable phyPage1 curidx 
{{fun _ s =>  isWellFormedMMUTables phyPage2 s }}.
Proof.
unfold isWellFormedMMUTables.
unfold initPEntryTable.
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
    set (s' := {| currentPartition := _ |}) in *.
   simpl in *.
   split.
    intros. 
    
(** readPhyEntry : read the content of a mapped page **)     
    assert( phyPage1 <> phyPage2).
    { 
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    unfold PreCtoPropagateIsWellFormedMMUTables in *.
    unfold consistency in *.
    apply readMappedPageDataUpdateMappedPageData 
    with partition  table2 table1  (StateLib.getIndexOfAddr va2 fstLevel) (StateLib.getIndexOfAddr va1 fstLevel)
    va2 va1 level s; intuition; subst;trivial. } 
    assert(Htable : forall idx : index,
     StateLib.readPhyEntry phyPage2 idx (memory s) = Some defaultPage /\ StateLib.readPresent phyPage2 idx (memory s) = Some false) by intuition.
    generalize (Htable idx); clear Htable; intros Htable.
    split.
    destruct Htable as (Htable1 & Htable2). 
    rewrite <- Htable1.
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial.
     destruct Htable as (Htable1 & Htable2). 
    rewrite <- Htable2.
    symmetry.
    apply readPresentUpdateMappedPageData; trivial.
    intuition.
    subst.
    apply PreCtoPropagateIsWellFormedMMUTablesUpdateMappedPageData;trivial.
    unfold PreCtoPropagateIsWellFormedMMUTables in *. 
    apply isPresentNotDefaultIffRightValue.
    unfold consistency in *. 
    intuition.
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
     apply  indexltbTrue in Hidx'.
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
    eapply WP.strengthen.
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
    set (s' := {| currentPartition := _ |}) in *.
    simpl in *.
    split.
    intros.    
(** readPhyEntry : read the content of a mapped page **)     
    assert( phyPage1 <> phyPage2).
    { 
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    unfold PreCtoPropagateIsWellFormedMMUTables in *.
    unfold consistency in *.
    apply readMappedPageDataUpdateMappedPageData 
    with partition  table2 table1  (StateLib.getIndexOfAddr va2 fstLevel) (StateLib.getIndexOfAddr va1 fstLevel)
    va2 va1 level s; intuition; subst;trivial. } 
    assert(Htable : forall idx : index,
     StateLib.readPhyEntry phyPage2 idx (memory s) = Some defaultPage /\ StateLib.readPresent phyPage2 idx (memory s) = Some false) by intuition.
    generalize (Htable idx); clear Htable; intros Htable.
    split.
    destruct Htable as (Htable1 & Htable2). 
    rewrite <- Htable1.
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial.
     destruct Htable as (Htable1 & Htable2). 
    rewrite <- Htable2.
    symmetry.
    apply readPresentUpdateMappedPageData; trivial.
    intuition.
    subst.
    apply PreCtoPropagateIsWellFormedMMUTablesUpdateMappedPageData;trivial.
    unfold PreCtoPropagateIsWellFormedMMUTables in *. 
    apply isPresentNotDefaultIffRightValue.
    unfold consistency in *. 
    intuition.
    intros.
    simpl in *.
    destruct H.
    apply H. }
Qed.

Lemma initPEntryTablePropagateIsWellFormedFstShadow phyPage1 (curidx : index) 
phyPage2 va1 va2 table1 table2 (level:level) partition currentPD lpred:
{{ fun s => isWellFormedFstShadow lpred phyPage2  s 
/\ PreCtoPropagateIsWellFormedMMUTables phyPage1 phyPage2  
va1 va2  table1 table2 partition level currentPD s
  }} 
initPEntryTable phyPage1 curidx 
{{fun _ s =>  isWellFormedFstShadow lpred phyPage2 s }}.
Proof.
unfold initPEntryTable.
assert(Hsize : tableSize + curidx >= tableSize) by omega.
revert Hsize.
revert curidx.
generalize tableSize at 1 3. 
induction n.  simpl. 
+ intros. eapply weaken.
  eapply WP.ret. simpl. intros.
  destruct curidx.
  simpl in *.
  destruct H.
  trivial.
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
    set (s' := {| currentPartition := _ |}) in *.
   simpl in *.
    
(** readPhyEntry : read the content of a mapped page **)     
   assert( phyPage1 <> phyPage2).
    { 
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    unfold isWellFormedFstShadow in *.
    symmetry in Hfalse.
    contradict Hfalse.
    unfold PreCtoPropagateIsWellFormedMMUTables in *.
    unfold consistency in *.
    apply readMappedPageDataUpdateMappedPageData 
    with partition  table2 table1  (StateLib.getIndexOfAddr va2 fstLevel) (StateLib.getIndexOfAddr va1 fstLevel)
    va2 va1 level s; intuition; subst;trivial. } 
    assert( Hor : isWellFormedFstShadow lpred phyPage2 s) by intuition.
    split.
    intuition;subst.
    unfold isWellFormedFstShadow in Hor.
    destruct Hor as [(Hl & Hand) |(Hl & Hand)].    
    left.
    split;trivial.
    intros.
    simpl.
    rewrite  <- readPhyEntryUpdateMappedPageData;trivial.
    rewrite <- readPresentUpdateMappedPageData; trivial.
    right.
    split;trivial.
    intros.
    simpl.
    rewrite readVirEntryUpdateMappedPageData;trivial.
    rewrite readPDflagUpdateMappedPageData; trivial.
    intuition.
    intuition.
    subst.
    apply PreCtoPropagateIsWellFormedMMUTablesUpdateMappedPageData;trivial.
       unfold PreCtoPropagateIsWellFormedMMUTables in *. 
    apply isPresentNotDefaultIffRightValue.
    unfold consistency in *. 
    intuition.
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
     apply  indexltbTrue in Hidx'.
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
    eapply WP.strengthen.
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
    set (s' := {| currentPartition := _ |}) in *.
    simpl in *.
    split.
    intros.    
(** readPhyEntry : read the content of a mapped page **)     
   assert( phyPage1 <> phyPage2).
    { 
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    unfold isWellFormedFstShadow in *.
    symmetry in Hfalse.
    contradict Hfalse.
    unfold PreCtoPropagateIsWellFormedMMUTables in *.
    unfold consistency in *.
    apply readMappedPageDataUpdateMappedPageData 
    with partition  table2 table1  (StateLib.getIndexOfAddr va2 fstLevel) (StateLib.getIndexOfAddr va1 fstLevel)
    va2 va1 level s; intuition; subst;trivial. } 
    assert( Hor : isWellFormedFstShadow lpred phyPage2 s) by intuition.
    unfold isWellFormedFstShadow in Hor.
    destruct Hor as [(Hl & Hand) |(Hl & Hand)].    
    left.
    split;trivial.
    intros.
    simpl.
    rewrite  <- readPhyEntryUpdateMappedPageData;trivial.
    rewrite <- readPresentUpdateMappedPageData; trivial.
    right.
    split;trivial.
    intros.
    simpl.
    rewrite readVirEntryUpdateMappedPageData;trivial.
    rewrite readPDflagUpdateMappedPageData; trivial.
    intuition.
    intuition.
    subst.
    apply PreCtoPropagateIsWellFormedMMUTablesUpdateMappedPageData;trivial.
       unfold PreCtoPropagateIsWellFormedMMUTables in *. 
    apply isPresentNotDefaultIffRightValue.
    unfold consistency in *. 
    intuition.
    simpl;intuition.
}

 Qed.

