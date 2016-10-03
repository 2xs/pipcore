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
    This file contains the invariant of [Activate] some associated lemmas *)
Require Import Model.ADT Model.Hardware Core.Services Isolation 
Consistency Invariants WeakestPreconditions Model.Lib StateLib 
Model.MAL DependentTypeLemmas InternalLemmas Lib.
Require Import Omega Bool  Coq.Logic.ProofIrrelevance List Classical_Prop.
Import List.ListNotations.

Lemma getTablePagesUpdateCurrentPartition s rootStructure phyVA: 
getTablePages rootStructure tableSize s =
getTablePages rootStructure tableSize {| currentPartition := phyVA; memory := memory s |}.
Proof.
revert rootStructure.
induction tableSize; simpl; trivial.
intros. 
rewrite IHn.
reflexivity.
Qed.

Lemma getIndirectionsUpdateCurrentPartition phyVA rootStructure s:
getIndirections rootStructure s =
getIndirections rootStructure {| currentPartition := phyVA; memory := memory s |}.
Proof.
unfold getIndirections.
revert rootStructure s.
induction nbLevel; simpl; trivial.
intros.
f_equal.
rewrite <- getTablePagesUpdateCurrentPartition with s rootStructure phyVA.
induction  (getTablePages rootStructure tableSize s);simpl; trivial. 
f_equal.
apply IHn.
apply IHl.
Qed. 

Lemma getIndirectionUpdateCurrentPartition p a l phyVA s:
getIndirection p a l (nbLevel - 1) s =
getIndirection p a l (nbLevel - 1) {| currentPartition := phyVA; memory := memory s |} .
Proof. 
revert p a l.
induction (nbLevel - 1);simpl; trivial.
intros.
destruct ( StateLib.Level.eqb l fstLevel); trivial.
destruct (StateLib.readPhyEntry p (StateLib.getIndexOfAddr a l) (memory s)); trivial.
destruct ( defaultPage =? p0) ;trivial.
destruct (StateLib.Level.pred l ); trivial.
Qed.

Lemma getMappedPageUpdateCurrentPartition phyVA p s a :
 getMappedPage p s a =
 getMappedPage p {| currentPartition := phyVA; memory := memory s |} a.
 Proof.
 unfold getMappedPage.
 destruct (StateLib.getNbLevel ).
 rewrite <- getIndirectionUpdateCurrentPartition with p a l phyVA s.
  simpl.
  reflexivity.
  trivial.
Qed.

Lemma getAccessibleMappedPageUpdateCurrentPartition phyVA p s a :
 getAccessibleMappedPage p s a =
 getAccessibleMappedPage p {| currentPartition := phyVA; memory := memory s |} a.
 Proof.
 unfold getAccessibleMappedPage.
 destruct (StateLib.getNbLevel ).
 rewrite <- getIndirectionUpdateCurrentPartition with p a l phyVA s.
  simpl.
  reflexivity.
  trivial.
Qed.

Lemma getMappedPagesAuxUpdateCurrentPartition p l s phyVA : 
getMappedPagesAux p l s = getMappedPagesAux p l {| currentPartition := phyVA; memory := memory s |}.
Proof. 
revert p. 
induction l; simpl; trivial.
intros;cbn.
rewrite <- getMappedPageUpdateCurrentPartition with phyVA p s a.
destruct (getMappedPage p s a).
f_equal. f_equal.
clear IHl.
induction l; simpl; trivial. 
f_equal.
apply getMappedPageUpdateCurrentPartition .
apply IHl.
f_equal.
clear IHl.
induction l; simpl; trivial.
f_equal.
apply getMappedPageUpdateCurrentPartition.
assumption.
Qed.

Lemma getAccessibleMappedPagesAuxUpdateCurrentPartition p l s phyVA : 
getAccessibleMappedPagesAux p l s = getAccessibleMappedPagesAux p l {| currentPartition := phyVA; memory := memory s |}.
Proof. 
revert p. 
induction l; simpl; trivial.
intros.
cbn.
rewrite <- getAccessibleMappedPageUpdateCurrentPartition with phyVA p s a.
destruct (getAccessibleMappedPage p s a).
f_equal. f_equal.
clear IHl.
induction l; simpl; trivial.  f_equal.
apply getAccessibleMappedPageUpdateCurrentPartition .
apply IHl.
f_equal.
clear IHl.
induction l; simpl; trivial.
f_equal.
apply getAccessibleMappedPageUpdateCurrentPartition.
assumption.
Qed.

Lemma getMappedPagesUpdateCurrentPartition phyVA partition s:
getMappedPages partition s =
getMappedPages partition {| currentPartition := phyVA; memory := memory s |}.
Proof.
unfold getMappedPages.
simpl.
destruct( StateLib.getPd partition (memory s)); intros; trivial.
apply getMappedPagesAuxUpdateCurrentPartition.
Qed.

Lemma getAccessibleMappedPagesUpdateCurrentPartition phyVA partition s:
getAccessibleMappedPages partition s =
getAccessibleMappedPages partition {| currentPartition := phyVA; memory := memory s |}.
Proof.
unfold getAccessibleMappedPages.
simpl.
destruct( StateLib.getPd partition (memory s)); intros; trivial.
apply getAccessibleMappedPagesAuxUpdateCurrentPartition.
Qed.

Lemma getTrdShadowsUpdateCurrentPartition  s:
forall phyVA p2 : page,
getTrdShadows p2 s nbPage = 
getTrdShadows p2 {| currentPartition := phyVA; memory := memory s |} nbPage.
Proof.
induction nbPage; simpl; trivial.
intros.
destruct ( StateLib.getMaxIndex ); trivial.
destruct (StateLib.readPhyEntry p2 i (memory s)); trivial.
destruct (p =? defaultPage ); trivial.
f_equal.
apply IHn.
Qed.

Lemma getUsedPagesUpdateCurrentDescriptor s phyVA child1:
getUsedPages child1 s =
getUsedPages child1 {| currentPartition := phyVA; memory := memory s |}.
Proof.
unfold getUsedPages.
rewrite <- getMappedPagesUpdateCurrentPartition with phyVA child1 s.
f_equal.
unfold getConfigPages. f_equal.
unfold getConfigPagesAux.
simpl.
destruct (StateLib.getPd child1 (memory s) ); trivial. 
destruct ( getFstShadow child1 (memory s)); trivial.
destruct ( getSndShadow child1 (memory s)); trivial.
destruct(  getConfigTablesLinkedList child1 (memory s) ); trivial.
rewrite <- getIndirectionsUpdateCurrentPartition with phyVA p s.
rewrite <- getIndirectionsUpdateCurrentPartition with phyVA p0 s.
rewrite <- getIndirectionsUpdateCurrentPartition with phyVA p1 s.
f_equal. f_equal. f_equal. f_equal. f_equal. f_equal.
f_equal.
clear p child1 p0 p1.
revert phyVA p2.
apply getTrdShadowsUpdateCurrentPartition. 
Qed.

Lemma getPdsVAddrUpdateCurrentPartition phyVA parent lvl l  s :
getPdsVAddr parent lvl l s =
getPdsVAddr parent lvl l{| currentPartition := phyVA; memory := memory s |}.
Proof.
unfold getPdsVAddr.
revert lvl.
induction l; simpl; trivial.
intros.
rewrite <- IHl.
unfold checkChild.
simpl.
destruct ( getFstShadow parent (memory s) ) ; trivial.
rewrite <- getIndirectionUpdateCurrentPartition with p a lvl phyVA s.
reflexivity.
Qed.

Lemma getChildrenUpdateCurrentDescriptor parent phyVA s : 
getChildren parent s =
getChildren parent {| currentPartition := phyVA; memory := memory s |}.
Proof.
unfold getChildren.
destruct (StateLib.getNbLevel ); trivial.
simpl.
destruct (StateLib.getPd parent (memory s)); trivial.
rewrite <- getPdsVAddrUpdateCurrentPartition with phyVA parent l getAllVAddr s .
f_equal.
apply getMappedPagesAuxUpdateCurrentPartition .
Qed.

Lemma getPartitionsUpdateCurrentDescriptor s phyVA partition :
getPartitions partition s =
getPartitions partition {| currentPartition := phyVA; memory := memory s |}.
Proof.
unfold getPartitions.
revert partition.
induction (nbPage+1); simpl; trivial.
intros.
f_equal.
rewrite <- getChildrenUpdateCurrentDescriptor with partition phyVA s.

induction (getChildren partition s); trivial.
simpl.
f_equal. 
apply IHn.
apply IHl.
Qed. 

Lemma dataStructurePdSh1Sh2asRootUpdateCurrentDescriptor idxroot phyVA s :
dataStructurePdSh1Sh2asRoot idxroot s ->
dataStructurePdSh1Sh2asRoot idxroot {| currentPartition := phyVA; memory := memory s |}.
Proof.
intros.
unfold dataStructurePdSh1Sh2asRoot in *.
intros.
unfold isVE, isVA, isPE in *. simpl in *.  
apply H with partition entry va; trivial.
rewrite getPartitionsUpdateCurrentDescriptor with s phyVA multiplexer; trivial.
clear H H0 H3 H1. 
revert entry va level s H4.
induction stop; simpl in *.
intros.
assumption.
intros.
case_eq (StateLib.Level.eqb level fstLevel); intros;
rewrite H in H4.  assumption.
case_eq(StateLib.readPhyEntry entry
(StateLib.getIndexOfAddr va level) (memory s) ); intros;
rewrite H0 in H4. 
case_eq (defaultPage =? p); intros;
rewrite H1 in H4; try assumption.
case_eq (StateLib.Level.pred level);
intros; rewrite H3 in H4.
apply IHstop.
assumption.
now contradict H4.
now contradict H4.
Qed.

Lemma lengthNoDupPartitions : 
forall listPartitions : list page, NoDup listPartitions -> 
length listPartitions <= nbPage.
Proof.
intros.
assert (forall p : page, In p getAllPages) by apply AllPagesAll.
assert (length getAllPages <= nbPage).
unfold getAllPages.
rewrite map_length.
rewrite seq_length. trivial.
apply NoDup_incl_length with page listPartitions getAllPages in H.
omega.
unfold incl.
intros.
apply AllPagesAll.
Qed.

Lemma getPdsVAddrCheckChild partition descChild nbL s: 
true = checkChild partition nbL s descChild -> 
List.In descChild  (getPdsVAddr partition nbL getAllVAddr s).
Proof.
intros.
unfold getPdsVAddr.
apply filter_In.
split.
apply AllVAddrAll .
symmetry; trivial.
Qed.

Lemma VAisChild phyVA partition nbL pd descChild ptpd s: 
Some nbL = StateLib.getNbLevel -> 
nextEntryIsPP partition PDidx pd s -> 
true = checkChild partition nbL s descChild ->
getTableAddrRoot ptpd PDidx partition descChild s -> 
isEntryPage ptpd (StateLib.getIndexOfAddr descChild fstLevel) phyVA s ->
entryPresentFlag ptpd (StateLib.getIndexOfAddr descChild fstLevel) true s -> 
List.In phyVA (getChildren partition s).
Proof.
intros Hnbl HnextEntryIsPP HisChild Hget HphyVA Hpresent .
unfold getChildren.
rewrite <- Hnbl.
assert (nextEntryIsPP partition PDidx pd s) as Hroot by intuition. 
unfold nextEntryIsPP in HnextEntryIsPP.
unfold StateLib.getPd.
unfold StateLib.readPhysical.
case_eq (StateLib.Index.succ PDidx);intros;
rewrite H in HnextEntryIsPP;  [ | now contradict HnextEntryIsPP].
case_eq (lookup partition i (memory s) beqPage beqIndex); intros; 
rewrite H0 in HnextEntryIsPP; [ | now contradict HnextEntryIsPP].
destruct v as [ p |v|p|v|ii] ; [ now contradict HnextEntryIsPP | now contradict HnextEntryIsPP | 
subst | now contradict HnextEntryIsPP | now contradict HnextEntryIsPP ].
assert (List.In descChild  (getPdsVAddr partition nbL getAllVAddr s)).
apply getPdsVAddrCheckChild; trivial.
unfold getTableAddrRoot in *. 
unfold getMappedPagesAux.
rewrite nodup_In.
rewrite filterOptionInIff; trivial. 
unfold getMappedPagesOption.
apply in_map_iff. 
exists descChild.
split; trivial. 
unfold getMappedPage.
rewrite <- Hnbl.
destruct Hget as (_ & Hget).
apply Hget in Hroot; clear Hget.
destruct Hroot as ( nbl1 & Hnbl1 & stop2 & Hstop2 & Hget).
rewrite <- Hnbl1 in Hnbl.
inversion Hnbl.
subst.
assert (getIndirection p descChild nbl1 (nbLevel - 1) s = Some ptpd) as Hstopgt.
{ apply getIndirectionStopLevelGT2 with (nbl1 + 1); try omega.
  unfold StateLib.getNbLevel in Hnbl1.
  case_eq(gt_dec nbLevel 0); intros.
  rewrite H2 in Hnbl1.
  inversion Hnbl1.
  simpl in *.
  trivial.
  assert (0 < nbLevel) by apply nbLevelNotZero.
  omega.
  assumption. }

rewrite Hstopgt. 
unfold isEntryPage in *.
unfold StateLib.readPresent. 
case_eq (lookup ptpd (StateLib.getIndexOfAddr descChild fstLevel) 
             (memory s) beqPage beqIndex); intros; rewrite H2 in *; [| now contradict HphyVA].

destruct v as [ p0 |v|p0|v|ii] ; [ subst |now contradict HphyVA | now contradict HphyVA | 
 now contradict HphyVA | now contradict HphyVA ].
unfold entryPresentFlag in *.
rewrite H2 in Hpresent.
rewrite <- Hpresent.
unfold StateLib.readPhyEntry.
rewrite H2;trivial.
Qed.

Lemma activateChild descChild vaNotNulll currPart
root isMultiplexer nbL  ptpd lastIndex phyVA pd: 
{{ fun s : state =>((((((((((((partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s) /\
              beqVAddr defaultVAddr descChild = vaNotNulll) /\ currPart = currentPartition s) /\
            root = multiplexer) /\ isMultiplexer = StateLib.Page.eqb currPart root) /\
          Some nbL = StateLib.getNbLevel) /\
         true = StateLib.checkChild currPart nbL s descChild) /\ 
        nextEntryIsPP currPart PDidx pd s) /\
       (getTableAddrRoot' ptpd PDidx currPart descChild s /\ ptpd = defaultPage \/
        getTableAddrRoot ptpd PDidx currPart descChild s /\
        ptpd <> defaultPage /\
        (forall idx : index,
         StateLib.getIndexOfAddr descChild fstLevel = idx -> isPE ptpd idx s))) /\
      (defaultPage =? ptpd) = false) /\
     StateLib.getIndexOfAddr descChild fstLevel = lastIndex) /\
    isEntryPage ptpd lastIndex phyVA s) /\ entryPresentFlag ptpd lastIndex true s   }} activate phyVA {{ fun _ (s : state) =>
                       partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
eapply weaken.
eapply WP.activate.
simpl.
intros.
try repeat rewrite and_assoc in H.
destruct H as ( Hiso & Hanc & Hvs &Hcons & Hvanull & Hcurpart & Hroot & Hmultpx & Hnbl &HisChild
& HnextEntryIsPP &   
 [(Hfalse & Hget) | (Htrue & Hpe)] & Hnotnull & Hidx & HphyVA & Hpresent).
subst.
apply beq_nat_false in Hnotnull.
now contradict Hnotnull. 
split.
+ unfold partitionsIsolation in *.
  intros.
  subst.
  simpl in H.
  rewrite <- getUsedPagesUpdateCurrentDescriptor with s phyVA child1.
  rewrite <- getUsedPagesUpdateCurrentDescriptor with s phyVA child2.
  apply Hiso with parent.
  rewrite getPartitionsUpdateCurrentDescriptor with s phyVA multiplexer; trivial.
  rewrite getChildrenUpdateCurrentDescriptor with parent phyVA s; trivial.
  rewrite getChildrenUpdateCurrentDescriptor with parent phyVA s; trivial.
  assumption.
+ split.
  - unfold kernelDataIsolation in *.
    move Hanc at bottom.
    intros.
    rewrite <- getPartitionsUpdateCurrentDescriptor in *.
    unfold getConfigPages in *.
    simpl in *.
    generalize (Hanc partition1 partition2); clear Hanc; intros Hanc.
    apply Hanc in H; trivial. clear Hanc.
    rewrite <- getAccessibleMappedPagesUpdateCurrentPartition with phyVA partition1 s.
    unfold disjoint in *.
    intros.
    apply H in H1.   
    unfold getConfigPagesAux in *. simpl.
    destruct (StateLib.getPd partition2 (memory s) ); trivial. 
    destruct ( getFstShadow partition2 (memory s)); trivial.
    destruct ( getSndShadow partition2 (memory s)); trivial.
    destruct(  getConfigTablesLinkedList partition2 (memory s) ); trivial.
    rewrite <- getIndirectionsUpdateCurrentPartition with phyVA p s.
    rewrite <- getIndirectionsUpdateCurrentPartition with phyVA p0 s.
    rewrite <- getIndirectionsUpdateCurrentPartition with phyVA p1 s.
    rewrite <- getTrdShadowsUpdateCurrentPartition.
    simpl in *. 
    apply H1; trivial.
  - split.
    * unfold verticalSharing in *. intros.
      rewrite <- getUsedPagesUpdateCurrentDescriptor with s phyVA child.
      rewrite <- getMappedPagesUpdateCurrentPartition with phyVA parent s.
      apply Hvs.
      rewrite getPartitionsUpdateCurrentDescriptor with s phyVA multiplexer; trivial.
      rewrite getChildrenUpdateCurrentDescriptor with parent phyVA s; trivial.
    * unfold consistency in *.
      split.
      { unfold partitionDescriptorEntry in *.
        destruct Hcons.
        intros.
        subst.
        rewrite <- getPartitionsUpdateCurrentDescriptor with s phyVA multiplexer in H1 . 
        generalize (H partition H1); clear H; intros H. 
        apply H in H2; clear H.
        destruct H2; split; trivial. }
      { try repeat split.
        + apply dataStructurePdSh1Sh2asRootUpdateCurrentDescriptor; intuition. 
        + apply dataStructurePdSh1Sh2asRootUpdateCurrentDescriptor; intuition.
        + apply dataStructurePdSh1Sh2asRootUpdateCurrentDescriptor; intuition.
        + destruct Hcons as (_ & _& _& _ & Hpartlist & _ & _ ).
          unfold currentPartitionInPartitionsList in *.
          simpl in *.
          rewrite <- getPartitionsUpdateCurrentDescriptor with s phyVA multiplexer.
          assert (List.In phyVA (getChildren (currentPartition s) s) ).
          subst.
          apply VAisChild with nbL pd descChild ptpd; trivial.
          unfold getPartitions in *.
          apply childrenPartitionInPartitionList with (currentPartition s); trivial. 
        + unfold noDupMappedPagesList in *.
          destruct Hcons as (_ & _& _& _ & _ & Hnodup & _ ).        
          intros. 
          rewrite <- getMappedPagesUpdateCurrentPartition with  phyVA partition s.
          apply Hnodup.
          rewrite getPartitionsUpdateCurrentDescriptor with s phyVA multiplexer; trivial. 
        + unfold noDupConfigPagesList in *.
          destruct Hcons as (_ & _& _& _ & _ & _ & Hnodup ).
          intros.
          subst.
          rewrite <- getIndirectionsUpdateCurrentPartition with phyVA root0 s; trivial.
          apply Hnodup with idxroot partition; trivial.
          rewrite getPartitionsUpdateCurrentDescriptor with s phyVA multiplexer; trivial. 
        + unfold parentInPartitionList in *.
          intros. 
          destruct Hcons as (_ & _& _& _ & _ & _ & _ & Hparent ).
          rewrite  <-getPartitionsUpdateCurrentDescriptor with s phyVA multiplexer.
          rewrite  <-getPartitionsUpdateCurrentDescriptor in H.
          generalize (Hparent partition H); clear Hparent; intros Hparent.
          apply Hparent.
          unfold nextEntryIsPP in *.
          simpl in *. assumption. }
Qed.

Lemma activateParent parent currPart root descChild :
{{ fun s : state =>
   (((((partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s) /\ beqVAddr defaultVAddr descChild = true) /\
      currPart = currentPartition s) /\ root = multiplexer) /\ false = StateLib.Page.eqb currPart root) /\
   nextEntryIsPP currPart PPRidx parent s }}  
  MAL.activate parent {{ fun _ s => partitionsIsolation s/\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof. 
eapply weaken.
eapply WP.activate.
simpl.
intros.
try repeat rewrite and_assoc in H.
destruct H as ( Hiso & Hanc & Hvs &Hcons & Hvanull & Hcurpart & Hmultpx &Hcur& HnextEntryIsPP).
subst. 
split.
+ unfold partitionsIsolation in *.
  intros.
  subst.
  rewrite <- getUsedPagesUpdateCurrentDescriptor with s parent child1.
  rewrite <- getUsedPagesUpdateCurrentDescriptor with s parent child2.
  apply Hiso with parent0.
  rewrite getPartitionsUpdateCurrentDescriptor with s parent multiplexer; trivial.
  rewrite getChildrenUpdateCurrentDescriptor with parent0 parent s; trivial.
  rewrite getChildrenUpdateCurrentDescriptor with parent0 parent s; trivial.
  assumption.
+ split.
  - unfold kernelDataIsolation in *.
    move Hanc at bottom.
    intros.
    rewrite <- getPartitionsUpdateCurrentDescriptor in *.
    unfold getConfigPages in *.
    simpl in *.
    generalize (Hanc partition1 partition2); clear Hanc; intros Hanc.
    apply Hanc in H; trivial. clear Hanc.
    rewrite <- getAccessibleMappedPagesUpdateCurrentPartition with parent partition1 s.
    unfold disjoint in *.
    intros.
    apply H in H1.   
    unfold getConfigPagesAux in *. simpl in *.
    destruct (StateLib.getPd partition2 (memory s) ); trivial. 
    destruct ( getFstShadow partition2 (memory s)); trivial.
    destruct ( getSndShadow partition2 (memory s)); trivial.
    destruct(  getConfigTablesLinkedList partition2 (memory s) ); trivial.
    rewrite <- getIndirectionsUpdateCurrentPartition with parent p s.
    rewrite <- getIndirectionsUpdateCurrentPartition with parent p0 s.
    rewrite <- getIndirectionsUpdateCurrentPartition with parent p1 s.
    rewrite <- getTrdShadowsUpdateCurrentPartition.
    apply H1; trivial.
  - split.  unfold verticalSharing in *. intros.
    rewrite <- getUsedPagesUpdateCurrentDescriptor with s parent child.
    rewrite <- getMappedPagesUpdateCurrentPartition with parent parent0 s.
    apply Hvs.
    rewrite getPartitionsUpdateCurrentDescriptor with s parent multiplexer; trivial.
    rewrite getChildrenUpdateCurrentDescriptor with parent0 parent s; trivial.
  * unfold consistency in *.
    split.
    { unfold partitionDescriptorEntry in *.
      destruct Hcons.
      intros.
      subst.
      rewrite <- getPartitionsUpdateCurrentDescriptor with s parent multiplexer in H1 . 
      generalize (H partition H1); clear H; intros H. 
      apply H in H2; clear H.
      destruct H2; split; trivial. }
    { try repeat split.
      + apply dataStructurePdSh1Sh2asRootUpdateCurrentDescriptor; intuition.
      + apply dataStructurePdSh1Sh2asRootUpdateCurrentDescriptor; intuition.
      + apply dataStructurePdSh1Sh2asRootUpdateCurrentDescriptor; intuition.
      + destruct Hcons as (_ & _& _& _ & Hpartlist & _ & _  & Hpart).
        unfold currentPartitionInPartitionsList in *.
        simpl in *.
        rewrite <- getPartitionsUpdateCurrentDescriptor with s parent multiplexer.
        unfold parentInPartitionList in Hpart.
        generalize (Hpart (currentPartition s) Hpartlist); clear Hpart; intros Hpart.
        apply Hpart; trivial.  
      + unfold noDupMappedPagesList in *.
        destruct Hcons as (_ & _& _& _ & _ & Hnodup & _ ).        
        intros. 
        rewrite <- getMappedPagesUpdateCurrentPartition with  parent partition s.
        apply Hnodup.
        rewrite getPartitionsUpdateCurrentDescriptor with s parent multiplexer; trivial.
      + unfold noDupConfigPagesList in *.
        destruct Hcons as (_ & _& _& _ & _ & _ & Hnodup ).
        intros.
        subst.
        rewrite <- getIndirectionsUpdateCurrentPartition with parent root s; trivial.
        apply Hnodup with idxroot partition; trivial.
        rewrite getPartitionsUpdateCurrentDescriptor with s parent multiplexer; trivial.
      + unfold parentInPartitionList in *.
         intros. 
         destruct Hcons as (_ & _& _& _ & _ & _ & _ & Hparent ).
          rewrite  <-getPartitionsUpdateCurrentDescriptor with s parent multiplexer.
          rewrite  <-getPartitionsUpdateCurrentDescriptor in H.
          generalize (Hparent partition H); clear Hparent; intros Hparent.
          apply Hparent.
           unfold nextEntryIsPP in *.
           simpl in *. assumption. } 
Qed.