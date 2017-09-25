(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2017)                 *)
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

Lemma getIndirectionUpdateCurrentPartition1 p a l phyVA stop s:
getIndirection p a l stop s =
getIndirection p a l stop {| currentPartition := phyVA; memory := memory s |} .
Proof. 
revert p a l.
induction stop;simpl; trivial.
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
*
f_equal. f_equal.
clear IHl.
induction l; simpl; trivial. 
f_equal.
apply getMappedPageUpdateCurrentPartition .
apply IHl.
*
f_equal.
clear IHl.
induction l; simpl; trivial.
f_equal.
apply getMappedPageUpdateCurrentPartition.
assumption.
* f_equal.
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
*
f_equal. f_equal.
clear IHl.
induction l; simpl; trivial.  f_equal.
apply getAccessibleMappedPageUpdateCurrentPartition .
apply IHl.
*
f_equal.
clear IHl.
induction l; simpl; trivial.
f_equal.
apply getAccessibleMappedPageUpdateCurrentPartition.
assumption.
*
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
getTrdShadows p2 s (nbPage+1) = 
getTrdShadows p2 {| currentPartition := phyVA; memory := memory s |} (nbPage+1).
Proof.
induction nbPage; simpl; trivial.
intros.
destruct ( StateLib.getMaxIndex ); trivial.
destruct (StateLib.readPhysical p2 i (memory s)); trivial.
destruct (p =? defaultPage ); trivial.
f_equal.
apply IHn.
Qed.

Lemma getconfigPagesUpdateCurrentDescriptor partition phyVA s:
getConfigPages partition s = 
getConfigPages partition {| currentPartition := phyVA; memory := memory s |}.
Proof.
unfold getConfigPages. f_equal.
unfold getConfigPagesAux.
simpl.
destruct (StateLib.getPd partition (memory s) ); trivial. 
destruct ( getFstShadow partition (memory s)); trivial.
destruct ( getSndShadow partition (memory s)); trivial.
destruct(  getConfigTablesLinkedList partition (memory s) ); trivial.
rewrite <- getIndirectionsUpdateCurrentPartition with phyVA p s.
rewrite <- getIndirectionsUpdateCurrentPartition with phyVA p0 s.
rewrite <- getIndirectionsUpdateCurrentPartition with phyVA p1 s.
do 3 f_equal. 
clear p partition p0 p1.
revert phyVA p2.
apply getTrdShadowsUpdateCurrentPartition. 
Qed.

Lemma getUsedPagesUpdateCurrentDescriptor s phyVA child1:
getUsedPages child1 s =
getUsedPages child1 {| currentPartition := phyVA; memory := memory s |}.
Proof.
unfold getUsedPages.
rewrite <- getMappedPagesUpdateCurrentPartition with phyVA child1 s.
f_equal.
apply getconfigPagesUpdateCurrentDescriptor.
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
rewrite <- getPdsVAddrUpdateCurrentPartition with phyVA parent l getAllVAddrWithOffset0 s .
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
In descChild getAllVAddrWithOffset0 -> 
List.In descChild  (getPdsVAddr partition nbL getAllVAddrWithOffset0 s).
Proof.
intros.
unfold getPdsVAddr.
apply filter_In.
split;trivial.
symmetry;trivial.
Qed. 

Lemma VAisChild phyVA partition nbL pd descChild (ptpd : page) s: 
Some nbL = StateLib.getNbLevel -> 
(defaultPage =? ptpd) = false -> 
nextEntryIsPP partition PDidx pd s -> 
true = checkChild partition nbL s descChild ->
getTableAddrRoot ptpd PDidx partition descChild s -> 
isEntryPage ptpd (StateLib.getIndexOfAddr descChild fstLevel) phyVA s ->
entryPresentFlag ptpd (StateLib.getIndexOfAddr descChild fstLevel) true s -> 
List.In phyVA (getChildren partition s).
Proof.
intros Hnbl Hnotnull HnextEntryIsPP HisChild Hget HphyVA Hpresent .
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
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel descChild va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).
assert (List.In va1  (getPdsVAddr partition nbL getAllVAddrWithOffset0 s)).
apply getPdsVAddrCheckChild; trivial.
rewrite  HisChild. 
apply  checkChildEq;trivial.
symmetry;trivial.
rewrite <- Hva11.
f_equal.
assert(StateLib.getNbLevel = Some (CLevel (nbLevel - 1))). 
apply getNbLevelEqOption.
rewrite <- Hnbl in *.
inversion H1;trivial.
unfold getTableAddrRoot in *. 
unfold getMappedPagesAux.
rewrite filterOptionInIff; trivial. 
unfold getMappedPagesOption.
apply in_map_iff. 
exists va1.
split; trivial. 
assert(getMappedPage p s descChild = SomePage phyVA).
{ unfold getMappedPage.
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
rewrite Hnotnull.
rewrite H2;trivial. }
rewrite <- H2.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.
Qed.

Lemma getPDFlagUpdateCurrentPartition sh1 va phyVA s:
getPDFlag sh1 va {| currentPartition := phyVA; memory := memory s |}  = 
 getPDFlag sh1 va s.
Proof.
unfold getPDFlag.
case_eq (StateLib.getNbLevel); intros;trivial.
assert(Hind: getIndirection sh1 va l (nbLevel - 1)
              {| currentPartition := phyVA; memory := memory s |} 
              = getIndirection sh1 va l (nbLevel - 1) s).
symmetry.
 apply getIndirectionUpdateCurrentPartition.
rewrite Hind.
case_eq(getIndirection sh1 va l (nbLevel - 1) s);intros;trivial.
Qed.

Lemma accessibleVAIsNotPartitionDescriptorUpdateCurrentDescriptor phyVA s:
accessibleVAIsNotPartitionDescriptor s -> 
accessibleVAIsNotPartitionDescriptor {| currentPartition := phyVA; memory := memory s |}.
Proof.
unfold accessibleVAIsNotPartitionDescriptor.
cbn.
intros.
assert (getPartitions multiplexer {| currentPartition := phyVA; memory := memory s |} = 
        getPartitions multiplexer s).
symmetry.
apply getPartitionsUpdateCurrentDescriptor.
rewrite H4 in *;clear H4.
assert(getAccessibleMappedPage pd {| currentPartition := phyVA; memory := memory s |} va =
      getAccessibleMappedPage pd s va).
symmetry.
apply getAccessibleMappedPageUpdateCurrentPartition.
rewrite H4 in *;clear H4.
assert(getPDFlag sh1 va {| currentPartition := phyVA; memory := memory s |}   = 
getPDFlag sh1 va s ).
apply getPDFlagUpdateCurrentPartition.
rewrite H4 in *;clear H4.
apply H with partition pd page ;trivial.
Qed.

Lemma getVirtualAddressSh2UpdateCurrentPartition sh2 phyVA va s :
getVirtualAddressSh2 sh2 {| currentPartition := phyVA; memory := memory s |} va =
     getVirtualAddressSh2 sh2 s va.
Proof.
unfold getVirtualAddressSh2.
destruct ( StateLib.getNbLevel);trivial.
rewrite <- getIndirectionUpdateCurrentPartition.
destruct (getIndirection sh2 va l (nbLevel - 1) s );trivial.
Qed.

Lemma isAccessibleMappedPageInParentUpdateCurrentPartition
 partition va accessiblePage s parent:
isAccessibleMappedPageInParent partition va accessiblePage 
{| currentPartition := parent; memory := memory s |} = 
isAccessibleMappedPageInParent partition va accessiblePage s.
Proof.
unfold isAccessibleMappedPageInParent.
simpl.
destruct( getSndShadow partition (memory s) );trivial.
rewrite getVirtualAddressSh2UpdateCurrentPartition.
destruct(getVirtualAddressSh2 p s va );trivial.
destruct(getParent partition (memory s) );trivial.
destruct(StateLib.getPd p0 (memory s) );trivial.
rewrite <- getAccessibleMappedPageUpdateCurrentPartition .
trivial.
Qed.

Lemma noCycleInPartitionTreeUpdateCurrentPartition
parent s :
noCycleInPartitionTree s -> 
noCycleInPartitionTree 
{| currentPartition := parent; memory := memory s |} .
Proof.
unfold noCycleInPartitionTree.
simpl.
assert (getPartitions multiplexer {| currentPartition := parent; memory := memory s |} = 
        getPartitions multiplexer s).
symmetry.
apply getPartitionsUpdateCurrentDescriptor.
rewrite H in *;clear H.
trivial.
Qed.

Lemma configTablesAreDifferentUpdateCurrentPartition
parent s : 
configTablesAreDifferent s -> configTablesAreDifferent
{| currentPartition := parent; memory := memory s |} .
Proof.
unfold configTablesAreDifferent.
simpl.
assert (getPartitions multiplexer {| currentPartition := parent; memory := memory s |} = 
        getPartitions multiplexer s).
symmetry.
apply getPartitionsUpdateCurrentDescriptor.
rewrite H in *;clear H.
assert (Hconfig : forall partition ,getConfigPages partition s =getConfigPages partition {| currentPartition := parent; memory := memory s |}
).
intros. 
apply getconfigPagesUpdateCurrentDescriptor.
intros.
rewrite <-  Hconfig.
rewrite <-  Hconfig.
apply H;trivial.
Qed.

Lemma isChildUpdateCurrentPartition phyVA s :
isChild s ->
isChild {| currentPartition := phyVA; memory := memory s |}.
Proof.
unfold isChild;intros.
rewrite <- getChildrenUpdateCurrentDescriptor with parent phyVA s;trivial.
rewrite  <-getPartitionsUpdateCurrentDescriptor in *.
simpl in *.
apply H;trivial.
Qed.

Lemma getVirtualAddressSh1UpdateCurrentPartition sh1 phyVA va s :
getVirtualAddressSh1 sh1 s va  = 
getVirtualAddressSh1 sh1 {| currentPartition := phyVA; memory := memory s |} va.
Proof.
unfold getVirtualAddressSh1.
simpl.
destruct(StateLib.getNbLevel );trivial.
rewrite <- getIndirectionUpdateCurrentPartition with  sh1 va l phyVA s;
trivial.
Qed.

Lemma isDerivedUpdateCurrentPartition parent va phyVA s :
isDerived parent va s -> 
isDerived parent va  {| currentPartition := phyVA; memory := memory s |}.
Proof.
unfold isDerived.
intros.
simpl in *.
destruct (getFstShadow parent (memory s) );try now contradict H.
rewrite <- getVirtualAddressSh1UpdateCurrentPartition with p phyVA va s;
trivial.
Qed.   

Lemma physicalPageNotDerivedUpdateCurrentPartition phyVA s :
physicalPageNotDerived s ->
physicalPageNotDerived {| currentPartition := phyVA; memory := memory s |}.
Proof.
unfold physicalPageNotDerived.
intros.
rewrite <- getChildrenUpdateCurrentDescriptor in *.
simpl in *.
rewrite <- getMappedPageUpdateCurrentPartition in *.
rewrite <- getPartitionsUpdateCurrentDescriptor in *.
apply H with  parent va pdParent child pdChild vaInChild ;trivial.
unfold not;intros.
apply H2.
apply isDerivedUpdateCurrentPartition;trivial.
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
        + 
          unfold currentPartitionInPartitionsList in *.
          simpl in *.
          rewrite <- getPartitionsUpdateCurrentDescriptor with s phyVA multiplexer.
          assert (List.In phyVA (getChildren (currentPartition s) s) ).
          subst.
          apply VAisChild with nbL pd descChild ptpd; trivial.
          unfold getPartitions in *.
          apply childrenPartitionInPartitionList with (currentPartition s); trivial.
          unfold  consistency in *. intuition. subst. 
          unfold currentPartitionInPartitionsList in *.
          intuition. 
        + unfold noDupMappedPagesList in *.
          destruct Hcons as (_ & _& _& _ & _ & Hnodup & _ ).        
          intros. 
          rewrite <- getMappedPagesUpdateCurrentPartition with  phyVA partition s.
          apply Hnodup.
          rewrite getPartitionsUpdateCurrentDescriptor with s phyVA multiplexer; trivial. 
        + assert(Hnodup : noDupConfigPagesList s) by intuition
          destruct Hcons as (_ & _& _& _ & _ & _ & Hnodup ).
          unfold noDupConfigPagesList in *.
          intros.
          subst.
          assert(Hparts  : In partition (getPartitions multiplexer s)) .
          rewrite getPartitionsUpdateCurrentDescriptor with s phyVA multiplexer; trivial.
          apply Hnodup in Hparts.
          assert( Heq : getConfigPages partition s = getConfigPages partition 
          {| currentPartition := phyVA; memory := memory s |}).
          {  unfold getConfigPages . f_equal.
          unfold getConfigPagesAux; simpl. 
          destruct (StateLib.getPd partition (memory s) ); trivial. 
          destruct ( getFstShadow partition (memory s)); trivial.
          destruct ( getSndShadow partition (memory s)); trivial.
          destruct(  getConfigTablesLinkedList partition (memory s) ); trivial.
          rewrite <- getIndirectionsUpdateCurrentPartition with phyVA p s.
          rewrite <- getIndirectionsUpdateCurrentPartition with phyVA p0 s.
          rewrite <- getIndirectionsUpdateCurrentPartition with phyVA p1 s.
          rewrite <- getTrdShadowsUpdateCurrentPartition;trivial. }
          rewrite <- Heq.
          apply Hnodup;trivial.
          rewrite getPartitionsUpdateCurrentDescriptor with s phyVA multiplexer; trivial.
        + unfold parentInPartitionList in *.
          intros. 
          destruct Hcons as (_ & _& _& _ & _ & _ & _ & Hparent & _ ).
          rewrite  <-getPartitionsUpdateCurrentDescriptor with s phyVA multiplexer.
          rewrite  <-getPartitionsUpdateCurrentDescriptor in H.
          generalize (Hparent partition H); clear Hparent; intros Hparent.
          apply Hparent.
          unfold nextEntryIsPP in *.
          simpl in *. assumption.
       + apply accessibleVAIsNotPartitionDescriptorUpdateCurrentDescriptor; intuition.
       + assert(Haccess : accessibleChildPageIsAccessibleIntoParent s) by intuition.
         unfold accessibleChildPageIsAccessibleIntoParent in *.
         simpl.
         intros.
         rewrite  <-getPartitionsUpdateCurrentDescriptor in H.
         rewrite <- getAccessibleMappedPageUpdateCurrentPartition in *.
         rewrite  isAccessibleMappedPageInParentUpdateCurrentPartition.
         apply Haccess with pd0;trivial. 
       + apply noCycleInPartitionTreeUpdateCurrentPartition;
         intuition.
       + apply configTablesAreDifferentUpdateCurrentPartition; intuition.
       + apply isChildUpdateCurrentPartition;intuition.
       + unfold isPresentNotDefaultIff in *;simpl; intuition.
         assert(Hcons : forall (table : page) (idx : index),
         StateLib.readPresent table idx (memory s) = Some false <->
         StateLib.readPhyEntry table idx (memory s) = Some defaultPage) by trivial.
         apply Hcons;trivial.
       + unfold isPresentNotDefaultIff in *;simpl; intuition.
         assert(Hcons : forall (table : page) (idx : index),
         StateLib.readPresent table idx (memory s) = Some false <->
         StateLib.readPhyEntry table idx (memory s) = Some defaultPage) by trivial.
         apply Hcons;trivial.
       + apply physicalPageNotDerivedUpdateCurrentPartition;intuition.
       + unfold multiplexerWithoutParent in *.
          simpl in *. intuition.
       + assert (Hisparent : isParent s) by intuition.
          unfold isParent in *. simpl in *.
          intros partition parent Hpart Hchild .
          rewrite <- getPartitionsUpdateCurrentDescriptor in Hpart.
          rewrite <- getChildrenUpdateCurrentDescriptor in Hchild.
          apply Hisparent;trivial.
      +  assert(Hnodup : noDupPartitionTree s) by intuition.
         unfold noDupPartitionTree in *.
         rewrite <- getPartitionsUpdateCurrentDescriptor;trivial.
      + assert(Hwell :  wellFormedFstShadow s) by intuition.
         unfold wellFormedFstShadow in *.
          intros.
          rewrite <- getVirtualAddressSh1UpdateCurrentPartition.
          apply Hwell with partition pg pd0;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in *;trivial.
          rewrite <- getMappedPageUpdateCurrentPartition in *;trivial.
       + assert(Hwell :  wellFormedSndShadow s) by intuition.
         unfold wellFormedSndShadow in *.
          intros.
          rewrite getVirtualAddressSh2UpdateCurrentPartition in *.
          apply Hwell with partition pg pd0;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in *;trivial.
          rewrite <- getMappedPageUpdateCurrentPartition in *;trivial.
       +  assert (Hwell :  wellFormedShadows sh1idx s ) by intuition.
          unfold wellFormedShadows in *.
          intros. 
          assert(Hgoal : exists indirection2 : page, getIndirection structroot va nbL0 stop s = Some indirection2 /\
                  (defaultPage =? indirection2) = false).
          apply Hwell with partition pdroot indirection1;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in * ;trivial.
           rewrite <- getIndirectionUpdateCurrentPartition1 in *;trivial. 
           rewrite <- getIndirectionUpdateCurrentPartition1 in *;trivial.
         + assert (Hwell :  wellFormedShadows sh2idx s ) by intuition.
          unfold wellFormedShadows in *.
          intros.
          assert(Hgoal :exists indirection2 , getIndirection structroot va nbL0 stop s = Some indirection2 /\
                  (defaultPage =? indirection2) = false).
          apply Hwell with partition pdroot indirection1;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in * ;trivial.
           rewrite <- getIndirectionUpdateCurrentPartition1 in *;trivial.            
           rewrite <- getIndirectionUpdateCurrentPartition1 in *;trivial.
         + assert(Hcur :  currentPartitionIsNotDefaultPage s) by intuition.
            unfold currentPartitionIsNotDefaultPage in *.
            simpl in *.
            assert( isEntryPage ptpd lastIndex phyVA s) as Hmapphy by intuition.
            assert(Hconsprent : isPresentNotDefaultIff s).
            { unfold consistency in *.
              intuition. }
            unfold isPresentNotDefaultIff in *.
            assert(Hread : StateLib.readPhyEntry ptpd lastIndex  (memory s) <> Some defaultPage).
            unfold not;intros.
            apply Hconsprent in H.
            rewrite entryPresentFlagReadPresent with s ptpd lastIndex  true in H ;
            trivial.
            now contradict H.
            unfold isEntryPage in Hmapphy.
           unfold StateLib.readPhyEntry in Hread. 
           destruct ( lookup ptpd lastIndex  (memory s) beqPage beqIndex);simpl in *;
           try now contradict Hmapphy.
           destruct v;try now contradict Hmapphy.
           subst.
           contradict Hread.
           f_equal.
           trivial.
       + assert(Hwell : wellFormedFstShadowIfNone s) by intuition.
         unfold wellFormedFstShadowIfNone  in *.
          intros.
          rewrite  getPDFlagUpdateCurrentPartition in *.
          apply Hwell with partition pd0;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in *;trivial.
          rewrite <- getMappedPageUpdateCurrentPartition in *;trivial. 
          +  assert(Hwell : wellFormedFstShadowIfNone s) by intuition.
         unfold wellFormedFstShadowIfNone  in *.
          intros.
          rewrite <- getVirtualAddressSh1UpdateCurrentPartition  in *;trivial.
          apply Hwell with partition pd0;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in *;trivial.
          rewrite <- getMappedPageUpdateCurrentPartition in *;trivial.
          + assert(Hwell : wellFormedFstShadowIfDefaultValues s) by intuition.
         unfold wellFormedFstShadowIfDefaultValues  in *.
          intros.
          rewrite  getPDFlagUpdateCurrentPartition.
          apply Hwell with partition pd0;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in *;trivial.
          rewrite <- getMappedPageUpdateCurrentPartition in *;trivial. 
          +  assert(Hwell : wellFormedFstShadowIfDefaultValues s) by intuition.
         unfold wellFormedFstShadowIfDefaultValues  in *.
          intros.
          rewrite <- getVirtualAddressSh1UpdateCurrentPartition  in *;trivial.
          apply Hwell with partition pd0;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in *;trivial.
          rewrite <- getMappedPageUpdateCurrentPartition in *;trivial.  }
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
      + destruct Hcons as (_ & _& _& _ & Hpartlist & _ & _  & Hpart & _).
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
      + assert(Hnodup : noDupConfigPagesList s) by intuition
          destruct Hcons as (_ & _& _& _ & _ & _ & Hnodup ).
          unfold noDupConfigPagesList in *.
          intros.
          subst.
          assert(Hparts  : In partition (getPartitions multiplexer s)) .
          rewrite getPartitionsUpdateCurrentDescriptor with s parent multiplexer; trivial.
          apply Hnodup in Hparts.
          assert( Heq : getConfigPages partition s = getConfigPages partition 
          {| currentPartition := parent; memory := memory s |}).
          {  unfold getConfigPages . f_equal.
          unfold getConfigPagesAux; simpl. 
          destruct (StateLib.getPd partition (memory s) ); trivial. 
          destruct ( getFstShadow partition (memory s)); trivial.
          destruct ( getSndShadow partition (memory s)); trivial.
          destruct(  getConfigTablesLinkedList partition (memory s) ); trivial.
          rewrite <- getIndirectionsUpdateCurrentPartition with parent p s.
          rewrite <- getIndirectionsUpdateCurrentPartition with parent p0 s.
          rewrite <- getIndirectionsUpdateCurrentPartition with parent p1 s.
          rewrite <- getTrdShadowsUpdateCurrentPartition;trivial. }
          rewrite <- Heq.
          apply Hnodup;trivial.
          rewrite getPartitionsUpdateCurrentDescriptor with s parent multiplexer; trivial.
      + unfold parentInPartitionList in *.
         intros. 
         destruct Hcons as (_ & _& _& _ & _ & _ & _ & Hparent & _ ).
          rewrite  <-getPartitionsUpdateCurrentDescriptor with s parent multiplexer.
          rewrite  <-getPartitionsUpdateCurrentDescriptor in H.
          generalize (Hparent partition H); clear Hparent; intros Hparent.
          apply Hparent.
           unfold nextEntryIsPP in *.
           simpl in *. assumption.
     + apply accessibleVAIsNotPartitionDescriptorUpdateCurrentDescriptor; intuition.
     + destruct Hcons as (_ & _& _& _ & _ & _ & _ & _ & _ & Haccess).
       unfold accessibleChildPageIsAccessibleIntoParent in *.
       simpl.
       intros.
       rewrite  <-getPartitionsUpdateCurrentDescriptor in H.
       rewrite <- getAccessibleMappedPageUpdateCurrentPartition in *.
       rewrite  isAccessibleMappedPageInParentUpdateCurrentPartition.
       apply Haccess with pd;trivial.
       + apply noCycleInPartitionTreeUpdateCurrentPartition;
         intuition.
       + apply configTablesAreDifferentUpdateCurrentPartition; intuition.
       + apply isChildUpdateCurrentPartition;intuition.
       + unfold isPresentNotDefaultIff in *;simpl; intuition.
         assert(Hcons : forall (table : page) (idx : index),
         StateLib.readPresent table idx (memory s) = Some false <->
         StateLib.readPhyEntry table idx (memory s) = Some defaultPage) by trivial.
         apply Hcons;trivial.
       + unfold isPresentNotDefaultIff in *;simpl; intuition.
         assert(Hcons : forall (table : page) (idx : index),
         StateLib.readPresent table idx (memory s) = Some false <->
         StateLib.readPhyEntry table idx (memory s) = Some defaultPage) by trivial.
         apply Hcons;trivial.
      + apply physicalPageNotDerivedUpdateCurrentPartition;intuition.
      + unfold multiplexerWithoutParent in *.
          simpl in *. intuition.
      + assert (Hisparent : isParent s) by intuition.
          unfold isParent in *. simpl in *.
          intros partition parent1 Hpart Hchild .
          rewrite <- getPartitionsUpdateCurrentDescriptor in Hpart.
          rewrite <- getChildrenUpdateCurrentDescriptor in Hchild.
          apply Hisparent;trivial.
      +  assert(Hnodup : noDupPartitionTree s) by intuition.
         unfold noDupPartitionTree in *.
         rewrite <- getPartitionsUpdateCurrentDescriptor;trivial.
      + assert(Hwell :  wellFormedFstShadow s) by intuition.
         unfold wellFormedFstShadow in *.
          intros.
          rewrite <- getVirtualAddressSh1UpdateCurrentPartition.
          apply Hwell with partition pg pd;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in *;trivial.
          rewrite <- getMappedPageUpdateCurrentPartition in *;trivial.
       + assert(Hwell :  wellFormedSndShadow s) by intuition.
         unfold wellFormedSndShadow in *.
          intros.
          rewrite getVirtualAddressSh2UpdateCurrentPartition in *.
          apply Hwell with partition pg pd;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in *;trivial.
          rewrite <- getMappedPageUpdateCurrentPartition in *;trivial.
       +  assert (Hwell :  wellFormedShadows sh1idx s ) by intuition.
          unfold wellFormedShadows in *.
          intros.
          assert(Hgoal : exists indirection2 : page,getIndirection structroot va nbL stop s = Some indirection2 /\
                  (defaultPage =? indirection2) = false).
          apply Hwell with partition pdroot indirection1;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in * ;trivial.
           rewrite <- getIndirectionUpdateCurrentPartition1 in *;trivial.
           rewrite <- getIndirectionUpdateCurrentPartition1 in *;trivial.
       +  assert (Hwell :  wellFormedShadows sh2idx s ) by intuition.
          unfold wellFormedShadows in *.
          intros. simpl in *.
          rewrite <- getPartitionsUpdateCurrentDescriptor in * ;trivial.
           rewrite <- getIndirectionUpdateCurrentPartition1 in *;trivial. 
           
            apply Hwell with partition pdroot indirection1;trivial. 
         + assert(Hcurdef :  currentPartitionIsNotDefaultPage s) by intuition.
            unfold currentPartitionIsNotDefaultPage in *.
            simpl in *.
            assert(Hpde : partitionDescriptorEntry s) by intuition.
            unfold partitionDescriptorEntry in *.
            assert(exists entry : page, nextEntryIsPP (currentPartition s) PPRidx entry s /\ entry <> defaultPage) as
            Hexist.
            apply Hpde. 
            unfold currentPartitionInPartitionsList in *.
            intuition.
            do 4 right;left;trivial.
            destruct Hexist as (entry & Hentry & Hnotnull).
            assert(entry= parent).
            apply getParentNextEntryIsPPEq with (currentPartition s) s;trivial.
            rewrite nextEntryIsPPgetParent in *;trivial.
            subst;trivial.
          + assert(Hwell : wellFormedFstShadowIfNone s) by intuition.
         unfold wellFormedFstShadowIfNone  in *.
          intros.
          rewrite  getPDFlagUpdateCurrentPartition.
          apply Hwell with partition pd;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in *;trivial.
          rewrite <- getMappedPageUpdateCurrentPartition in *;trivial. 
          +  assert(Hwell : wellFormedFstShadowIfNone s) by intuition.
         unfold wellFormedFstShadowIfNone  in *.
          intros.
          rewrite <- getVirtualAddressSh1UpdateCurrentPartition  in *;trivial.
          apply Hwell with partition pd;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in *;trivial.
          rewrite <- getMappedPageUpdateCurrentPartition in *;trivial.
          + assert(Hwell : wellFormedFstShadowIfDefaultValues s) by intuition.
         unfold wellFormedFstShadowIfDefaultValues  in *.
          intros.
          rewrite  getPDFlagUpdateCurrentPartition.
          apply Hwell with partition pd;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in *;trivial.
          rewrite <- getMappedPageUpdateCurrentPartition in *;trivial. 
          +  assert(Hwell : wellFormedFstShadowIfDefaultValues s) by intuition.
         unfold wellFormedFstShadowIfDefaultValues  in *.
          intros.
          rewrite <- getVirtualAddressSh1UpdateCurrentPartition  in *;trivial.
          apply Hwell with partition pd;trivial.
          rewrite <- getPartitionsUpdateCurrentDescriptor in *;trivial.
          rewrite <- getMappedPageUpdateCurrentPartition in *;trivial.
            }
Qed.