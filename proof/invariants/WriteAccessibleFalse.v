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
    This file contains required lemmas to prove the [writeAccessible] invariant *)
Require Import Core.Internal Isolation Consistency WeakestPreconditions 
Invariants StateLib Model.Hardware Model.ADT DependentTypeLemmas
GetTableAddr Model.MAL Model.Lib Lib InternalLemmas PropagatedProperties WriteAccessible.
Require Import Coq.Logic.ProofIrrelevance Omega List.
Import List.ListNotations.
(*************************Move into InternalLemmas ************************)
(********************************************************)
(*************************Move into PropagatedProperties ************************)
(********************************************************)

Lemma writeAccessibleRecPreconditionProofFstVA s currentPart ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
  currentShadow1 descChildphy phySh1Child trdVA nextVA vaToPrepare sndVA fstVA nbLgen l 
  idxFstVA idxSndVA idxTrdVA zeroI LLroot LLChildphy newLastLLable minFI indMMUToPreparebool: 
 propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable  s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA 
  currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false true true  true true true
  idxFstVA idxSndVA idxTrdVA zeroI minFI/\
  isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA /\
    isAccessibleMappedPageInParent currentPart fstVA phyMMUaddr s = true -> 
  writeAccessibleRecRecurtionInvariantConj fstVA currentPart phyMMUaddr ptMMUFstVA currentPart s.
Proof.
intros.
unfold propagatedPropertiesPrepare in *.
assert(currentPart = currentPartition s) by intuition.
subst.
assert(Hcurpart: In (currentPartition s) (getPartitions multiplexer s)) by (
unfold consistency in *;unfold currentPartitionInPartitionsList in *;intuition).  
unfold writeAccessibleRecRecurtionInvariantConj.
unfold propagatedPropertiesPrepare in *.
intuition;subst;trivial.
unfold isAncestor;left;trivial.
assert(Hcons:isPresentNotDefaultIff s)  by (
unfold consistency in *;intuition).
unfold isPresentNotDefaultIff in *.
assert(Hpres:  entryPresentFlag ptMMUFstVA (StateLib.getIndexOfAddr fstVA fstLevel) true s) by trivial.
apply entryPresentFlagReadPresent in Hpres.
apply isPresentNotDefaultIffTrue in Hpres.
assert(Hpage: isEntryPage ptMMUFstVA (StateLib.getIndexOfAddr fstVA fstLevel) phyMMUaddr s) by trivial.
apply isEntryPageReadPhyEntry1 in Hpage.
rewrite Hpage in Hpres.
rewrite Nat.eqb_neq.
unfold not;intros;subst.
contradict Hpres.
f_equal.
destruct phyMMUaddr;simpl in *;destruct defaultPage;simpl in *.
subst.
f_equal.
apply proof_irrelevance.
intuition.
Qed. 

Lemma writeAccessibleRecPreconditionProofSndVA s currentPart ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
  currentShadow1 descChildphy phySh1Child trdVA nextVA vaToPrepare sndVA fstVA nbLgen l 
  idxFstVA idxSndVA idxTrdVA zeroI LLroot LLChildphy newLastLLable  minFI indMMUToPreparebool:  
 propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable  s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA 
  currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false true true true true
  idxFstVA idxSndVA idxTrdVA zeroI minFI  /\
  isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA /\
    isAccessibleMappedPageInParent currentPart sndVA phySh1addr s = true -> 
  writeAccessibleRecRecurtionInvariantConj sndVA currentPart phySh1addr ptMMUSndVA currentPart s.
Proof.
intros.
unfold propagatedPropertiesPrepare in *.
assert(currentPart = currentPartition s) by intuition.
subst.
assert(Hcurpart: In (currentPartition s) (getPartitions multiplexer s)) by (
unfold consistency in *;unfold currentPartitionInPartitionsList in *;intuition).  
unfold writeAccessibleRecRecurtionInvariantConj.
unfold propagatedPropertiesPrepare in *.
intuition;subst;trivial.
unfold isAncestor;left;trivial.
assert(Hcons:isPresentNotDefaultIff s)  by (
unfold consistency in *;intuition).
unfold isPresentNotDefaultIff in *.
assert(Hpres:  entryPresentFlag ptMMUSndVA (StateLib.getIndexOfAddr sndVA fstLevel) true s) by trivial.
apply entryPresentFlagReadPresent in Hpres.
apply isPresentNotDefaultIffTrue in Hpres.
assert(Hpage: isEntryPage ptMMUSndVA (StateLib.getIndexOfAddr sndVA fstLevel) phySh1addr s) by trivial.
apply isEntryPageReadPhyEntry1 in Hpage.
rewrite Hpage in Hpres.
rewrite Nat.eqb_neq.
unfold not;intros;subst.
contradict Hpres.
f_equal.
destruct phySh1addr;simpl in *;destruct defaultPage;simpl in *.
subst.
f_equal.
apply proof_irrelevance.
intuition.
Qed. 

Lemma writeAccessibleRecPreconditionProofTrdVA s currentPart ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
  currentShadow1 descChildphy phySh1Child trdVA nextVA vaToPrepare sndVA fstVA nbLgen l 
  idxFstVA idxSndVA idxTrdVA zeroI minFI LLroot LLChildphy newLastLLable indMMUToPreparebool: 
 propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA 
  currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false true true true
  idxFstVA idxSndVA idxTrdVA zeroI minFI /\
  isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA /\
    isAccessibleMappedPageInParent currentPart trdVA phySh2addr s = true -> 
  writeAccessibleRecRecurtionInvariantConj trdVA currentPart phySh2addr ptMMUTrdVA currentPart s.
Proof.
intros.
unfold propagatedPropertiesPrepare in *.
assert(currentPart = currentPartition s) by intuition.
subst.
assert(Hcurpart: In (currentPartition s) (getPartitions multiplexer s)) by (
unfold consistency in *;unfold currentPartitionInPartitionsList in *;intuition).  
unfold writeAccessibleRecRecurtionInvariantConj.
unfold propagatedPropertiesPrepare in *.
intuition;subst;trivial.
unfold isAncestor;left;trivial.
assert(Hcons:isPresentNotDefaultIff s)  by (
unfold consistency in *;intuition).
unfold isPresentNotDefaultIff in *.
assert(Hpres:  entryPresentFlag ptMMUTrdVA (StateLib.getIndexOfAddr trdVA fstLevel) true s) by trivial.
apply entryPresentFlagReadPresent in Hpres.
apply isPresentNotDefaultIffTrue in Hpres.
assert(Hpage: isEntryPage ptMMUTrdVA (StateLib.getIndexOfAddr trdVA fstLevel) phySh2addr s) by trivial.
apply isEntryPageReadPhyEntry1 in Hpage.
rewrite Hpage in Hpres.
rewrite Nat.eqb_neq.
unfold not;intros;subst.
contradict Hpres.
f_equal.
destruct phySh2addr;simpl in *;destruct defaultPage;simpl in *.
subst.
f_equal.
apply proof_irrelevance.
intuition.
Qed. 


Lemma writeAccessibleRecInternalPropertiesUpdateUserFlag currentPart descParent ancestor pdAncestor pt va 
sh2 lastIndex ptsh2 vaInAncestor entry L defaultV ptvaInAncestor idxva s :
let s':={|
      currentPartition := currentPartition s;
      memory := add ptvaInAncestor idxva
                  (PE
                     {|
                     read := read entry;
                     write := write entry;
                     exec := exec entry;
                     present := present entry;
                     user := false;
                     pa := pa entry |}) (memory s) beqPage beqIndex |} in 
getPartitions multiplexer s = getPartitions multiplexer s' ->                      
lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
  (memory s) beqPage beqIndex = Some (PE entry) -> 
 writeAccessibleRecInternalPropertiesPrepare currentPart descParent ancestor pdAncestor pt va 
sh2 lastIndex ptsh2 vaInAncestor entry L defaultV ptvaInAncestor idxva s -> 
 writeAccessibleRecInternalPropertiesPrepare currentPart descParent ancestor pdAncestor pt va 
sh2 lastIndex ptsh2 vaInAncestor entry L defaultV ptvaInAncestor idxva s'.
Proof.
unfold writeAccessibleRecInternalPropertiesPrepare.
set(s':= {|currentPartition:= _ |}) in *.
intros Hpartitions.
intros.
intuition;subst;trivial.
+ rewrite <- Hpartitions;trivial.
+ unfold s'.
  apply isAncestorUpdateUserFlag;trivial. 
+ rewrite <- Hpartitions;trivial.
+ apply isPEUpdateUserFlag;trivial.
+ assert(Hroot : isPE pt (StateLib.getIndexOfAddr va fstLevel ) s /\
  getTableAddrRoot pt PDidx descParent va s) by intuition.
  destruct Hroot as (Hve & Hroot). 
  unfold getTableAddrRoot in *.
  destruct Hroot as (Hor & Hroot).
  split;trivial.
  intros root Hpp.
  unfold s' in Hpp.
  apply nextEntryIsPPUpdateUserFlag' in Hpp.
  apply Hroot in Hpp.
  destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
  exists nbL ; split;trivial.
  exists stop;split;trivial.
  rewrite <- Hind.
  unfold s'.
  apply getIndirectionUpdateUserFlag;trivial. 
+  apply entryPresentFlagUpdateUserFlag;trivial. 
+ apply entryUserFlagUpdateUserFlagSameValue;trivial.
+  apply isEntryPageUpdateUserFlag;trivial. 
+ apply nextEntryIsPPUpdateUserFlag; assumption. 
+ apply isVAUpdateUserFlag; intuition.
+ assert ( Hi : getTableAddrRoot ptsh2 sh2idx descParent va s) by intuition.
  unfold getTableAddrRoot in *.
  destruct Hi as (Hii & Htableroot).
  split; trivial.
  intros tableroot Hnepp.
  apply nextEntryIsPPUpdateUserFlag' in Hnepp.      
  generalize(Htableroot tableroot Hnepp );clear Htableroot; intros Htableroot.
  destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
  unfold getTableAddrRoot.
  exists nbL. split;trivial.
  exists stop. split; trivial.
  rewrite <- Hind.
  apply getIndirectionUpdateUserFlag;trivial. 
+ apply isVA'UpdateUserFlag; trivial. 
+ apply  nextEntryIsPPUpdateUserFlag; trivial. 
+ apply  nextEntryIsPPUpdateUserFlag; trivial. 
+ apply isPEUpdateUserFlag;assumption. 
+ assert(Hi :
  isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by intuition.
  unfold getTableAddrRoot in *.
  destruct Hi as (Hii & Hor &Htableroot  ).
  split;trivial.
  intros tableroot Hnepp.
  apply nextEntryIsPPUpdateUserFlag' in Hnepp.         
  generalize(Htableroot tableroot Hnepp );clear Htableroot; intros Htableroot.
  destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
  exists nbL. split;trivial.
  exists stop. split; trivial.
  rewrite <- Hind.
  apply getIndirectionUpdateUserFlag;trivial. 
Qed. 

Lemma isAccessibleMappedPageInParentUpdateUserFlagFalse s entry (ptvaInAncestor : page)
vaInAncestor ancestor L (descParent : page):
Some L = StateLib.getNbLevel -> 
parentInPartitionList s -> 
In ancestor (getPartitions multiplexer s) ->
noCycleInPartitionTree s -> 
configTablesAreDifferent s -> 
 accessibleChildPageIsAccessibleIntoParent s -> 
partitionDescriptorEntry s -> 
In descParent (getPartitions multiplexer s) -> 
(defaultPage =? ptvaInAncestor) = false -> 
getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s -> 
lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) (memory s) beqPage beqIndex = Some (PE entry) ->
isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) {|
  currentPartition := currentPartition s;
  memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} = 
isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s.
Proof.
intros HnbL Hparentpart Hancestor Hdiff Hdisjoint Haccess Hpde. 
intros.
set(s':= {| currentPartition := _ |}). 
unfold isAccessibleMappedPageInParent.
simpl.
unfold s'.
rewrite getSndShadowUpdateUserFlag;trivial.
case_eq( StateLib.getSndShadow ancestor (memory s));
intros * Hsh2 ;trivial.
assert( Hvirt : getVirtualAddressSh2 p
                 s' vaInAncestor =
                getVirtualAddressSh2 p s vaInAncestor).
{ unfold getVirtualAddressSh2.
  rewrite <- HnbL;trivial.
  unfold s'.
  rewrite getIndirectionUpdateUserFlag;trivial.
  destruct(getIndirection p vaInAncestor L (nbLevel - 1) s );trivial.
  simpl.
  rewrite readVirtualUpdateUserFlag;trivial. }
fold s'.
rewrite Hvirt;trivial.
case_eq (getVirtualAddressSh2 p s vaInAncestor );
intros * Hvainances;trivial.
rewrite getParentUpdateUserFlag;trivial.
case_eq( StateLib.getParent ancestor (memory s)); 
intros * HparentAcestor;trivial.
rewrite getPdUpdateUserFlag;trivial.
case_eq(StateLib.getPd p0 (memory s) );
intros * Hpdparentances;trivial.
assert( Haccessible : 
          getAccessibleMappedPage p1
           s' v = 
          getAccessibleMappedPage p1 s v).
{ symmetry.
  unfold consistency in *.
  unfold s'.
  unfold parentInPartitionList in *.
  apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions with ancestor p0;trivial.
  unfold consistency in *.
  intuition.
  apply Hparentpart with ancestor;trivial.
  apply nextEntryIsPPgetParent;trivial.
  unfold noCycleInPartitionTree in *.
  apply Hdiff;trivial.
  apply parentIsAncestor.
  apply nextEntryIsPPgetParent;trivial.
  assert(Hdiff1 : p0 <> ancestor).
  unfold noCycleInPartitionTree in *.
  apply Hdiff;trivial.
  apply parentIsAncestor.
  apply nextEntryIsPPgetParent;trivial.
  unfold configTablesAreDifferent in *.
  apply Hdisjoint;trivial.
  unfold parentInPartitionList in *.
  apply Hparentpart with ancestor;trivial.
  rewrite nextEntryIsPPgetParent;trivial.
  unfold not;intros Hfalsei;subst.
  now contradict Hdiff1. }
unfold accessibleChildPageIsAccessibleIntoParent in *.
unfold partitionDescriptorEntry in *.
assert(exists entry : page, nextEntryIsPP descParent PDidx entry s /\
        entry <> defaultPage) as (pdParent & Hpp & Hnotnull).
apply Hpde;trivial.
left;trivial.
clear Hpde.
apply nextEntryIsPPgetPd in Hpp.
rewrite Haccessible;trivial.
Qed.

 
Lemma partitionsIsolationUpdateUserFlag s pt vaValue entry flag:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
partitionsIsolation s -> 
partitionsIsolation
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hiso.
unfold partitionsIsolation in *.
intros parent child1 child2 Hparentpart Hchild1 Hchild2 Hchildrennoteq.
assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
apply getPartitionsUpdateUserFlag; trivial. 
rewrite Hpartitions in *. clear Hpartitions.
generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
assert(getChildren parent s' = getChildren parent s) as Hchildren.
apply getChildrenUpdateFlagUser;trivial.
rewrite Hchildren in *. clear Hchildren.
assert (forall child, getUsedPages child s'= getUsedPages child s) as Hch1used.
intros. apply getUsedPagesUpdateUserFlag;trivial.
rewrite Hch1used. rewrite Hch1used. clear Hch1used.
apply Hiso; trivial.
Qed.

Lemma kernelDataIsolationUpdateUserFlagFalse s pt vaValue entry :
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
kernelDataIsolation s -> 
kernelDataIsolation
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hkdi.
unfold kernelDataIsolation in *.
intros part1 part2 Hpart1 Hpart2.
assert( getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
apply getPartitionsUpdateUserFlag; trivial. 
rewrite Hpartitions in *.
clear Hpartitions.
assert(  (getConfigPages part2 s') = (getConfigPages part2 s)) as Hconfig.
apply getConfigPagesUpdateUserFlag; trivial.
rewrite Hconfig. clear Hconfig.
assert (Hincl : incl (getAccessibleMappedPages part1 s') (getAccessibleMappedPages part1 s)).
apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
unfold disjoint in *.
intros x Hx.
unfold incl in *.
apply Hkdi with part1; trivial.
apply Hincl; trivial.
Qed.

Lemma verticalSharingUpdateUserFlag s pt vaValue entry flag:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
verticalSharing s -> 
verticalSharing
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hvs.
unfold verticalSharing in *.
intros parent child Hparent Hchild.
assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
apply getPartitionsUpdateUserFlag; trivial.
rewrite Hpartitions in *.
clear Hpartitions.
generalize (Hvs parent child); clear Hvs; intros Hvs.
assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
apply getUsedPagesUpdateUserFlag;trivial.
rewrite   Husedpage. clear Husedpage.
assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
unfold getMappedPages.
assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
apply getPdUpdateUserFlag;trivial.
rewrite HgetPd.
clear HgetPd.
destruct (StateLib.getPd parent (memory s)) ;trivial.
apply getMappedPagesAuxUpdateUserFlag;trivial.
rewrite Hmaps. clear Hmaps. apply Hvs;trivial.
assert (getChildren parent s' = getChildren parent s) as Hchild'.
apply getChildrenUpdateFlagUser;trivial.
rewrite <- Hchild'. assumption.
Qed.

Lemma noDupMappedPagesListUpdateUserFlag s pt vaValue entry flag:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
noDupMappedPagesList s -> 
noDupMappedPagesList
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hnodup.
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
Qed.

Lemma parentInPartitionListUpdateUserFlag s pt vaValue entry flag:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
parentInPartitionList s -> 
parentInPartitionList
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hcons.
unfold parentInPartitionList in *.
assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
apply getPartitionsUpdateUserFlag; trivial.
rewrite HgetPart.
intros partition HgetParts parent Hroot.
generalize (Hcons partition HgetParts); clear Hcons; intros Hparent; trivial.
apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
apply Hparent; trivial.
Qed.

Lemma noCycleInPartitionTreeUpdateUserFlag s pt vaValue entry flag:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
noCycleInPartitionTree s -> 
noCycleInPartitionTree
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hcons.
unfold noCycleInPartitionTree in *.
assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
apply getPartitionsUpdateUserFlag; trivial.
rewrite HgetPart.
intros.
assert(HgetParent : getAncestors partition s' =
    getAncestors partition s). 
apply getAncestorsUpdateUserFlag;trivial.
rewrite HgetParent in *; clear HgetParent.
    apply Hcons;trivial.
Qed.

Lemma configTablesAreDifferentUpdateUserFlag s pt vaValue entry flag:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
configTablesAreDifferent s -> 
configTablesAreDifferent
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hcons.
unfold configTablesAreDifferent in *.
assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
apply getPartitionsUpdateUserFlag; trivial.
rewrite HgetPart.
intros partition1 partition2 Hpart1 Hpart2 Hdiff.
assert(Hconfig :forall part, getConfigPages part s' = getConfigPages part s).
intros. apply getConfigPagesUpdateUserFlag;trivial.
do 2 rewrite Hconfig;clear Hconfig.
apply Hcons;trivial.
Qed.

Lemma isChildUpdateUserFlag s pt vaValue entry flag:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
isChild s -> 
isChild
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hcons.
unfold isChild in *.
assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
apply getPartitionsUpdateUserFlag; trivial.
rewrite HgetPart.
intros.
unfold s' in H0;simpl in *.
rewrite getParentUpdateUserFlag in *;trivial.
assert(getChildren parent s' = getChildren parent s) as Hchildren.
apply getChildrenUpdateFlagUser;trivial.
rewrite Hchildren in *. clear Hchildren.
apply Hcons;trivial.
Qed.

Lemma wellFormedFstShadowUpdateUserFlag s pt vaValue entry flag:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
wellFormedFstShadow s -> 
wellFormedFstShadow
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hcons.
unfold wellFormedFstShadow in *;
intros;unfold s' in *;simpl in *.
rewrite getFstShadowUpdateUserFlag in *;trivial.
rewrite getPdUpdateUserFlag in *;trivial.
rewrite getPartitionsUpdateUserFlag in *;trivial.
rewrite getMappedPageUpdateUserFlag in *;trivial.
fold s'.
assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va = Some vainparent).
apply Hcons with partition pg pd;trivial.
destruct Hexist as (vainparent & Hexist).
exists vainparent.
rewrite <- Hexist.
symmetry.
apply getVirtualAddressSh1UpdateUserFlag;trivial.
Qed.

Lemma wellFormedFstShadowIfNoneUpdateUserFlag s pt vaValue entry flag:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
wellFormedFstShadowIfNone s -> 
wellFormedFstShadowIfNone
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hcons.
unfold wellFormedFstShadowIfNone in *;
intros;unfold s' in *;simpl in *.
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
apply Hcons with partition pd ;trivial.
Qed.

Lemma wellFormedFstShadowIfDefaultValuesUpdateUserFlag s pt vaValue entry flag:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
wellFormedFstShadowIfDefaultValues s -> 
wellFormedFstShadowIfDefaultValues
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hcons.
unfold wellFormedFstShadowIfDefaultValues in *;
intros;unfold s' in *;simpl in *.
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
apply Hcons with partition pd ;trivial.
Qed.


Lemma wellFormedSndShadowUpdateUserFlag s pt vaValue entry flag:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
wellFormedSndShadow s -> 
wellFormedSndShadow
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hcons.
unfold wellFormedSndShadow in *;
intros;unfold s' in *;simpl in *.
rewrite getSndShadowUpdateUserFlag in *;trivial.
rewrite getPdUpdateUserFlag in *;trivial.
rewrite getPartitionsUpdateUserFlag in *;trivial.
rewrite getMappedPageUpdateUserFlag in *;trivial.
fold s'.
assert(Hexist : exists vainparent : vaddr,
      getVirtualAddressSh2 sh2 s va = Some vainparent /\ 
      beqVAddr defaultVAddr vainparent = false).
apply Hcons with partition pg pd;trivial.
destruct Hexist as (vainparent & Hexist & Hnotnul).
exists vainparent.
rewrite <- Hexist.
split;trivial.
symmetry.
unfold s'.
subst.
apply getVirtualAddressSh2UpdateUserFlag;intuition;subst;trivial.
Qed.

Lemma wellFormedShadowsUpdateUserFlag s pt vaValue entry flag idxroot:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
wellFormedShadows idxroot s -> 
wellFormedShadows idxroot
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hcons.
unfold wellFormedShadows in *.
intros.
unfold s' in *. 
rewrite getIndirectionUpdateUserFlag in *;trivial.
simpl in *.
rewrite getPdUpdateUserFlag in *;trivial.
assert(Hpp :   nextEntryIsPP partition idxroot structroot s') by trivial. 
apply nextEntryIsPPUpdateUserFlag' in Hpp.
rewrite getPartitionsUpdateUserFlag in *;trivial.
fold s'.
apply Hcons with partition pdroot indirection1;trivial.
Qed.

Lemma accessibleVAIsNotPartitionDescriptorUpdateUserFlagFalse s pt vaValue entry (nbL:level) (currentPD:page) curPart:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
accessibleVAIsNotPartitionDescriptor s -> 
Some nbL = StateLib.getNbLevel -> 
partitionDescriptorEntry s -> 
noDupConfigPagesList s -> 
(defaultPage =? pt) = false -> 
nextEntryIsPP curPart PDidx currentPD s -> 
getTableAddrRoot pt PDidx curPart vaValue s -> 
isPE pt  (StateLib.getIndexOfAddr vaValue fstLevel) s -> 
entryPresentFlag pt (StateLib.getIndexOfAddr vaValue fstLevel) true s -> 
entryUserFlag pt (StateLib.getIndexOfAddr vaValue fstLevel) true s ->
In curPart (getPartitions multiplexer s) ->
accessibleVAIsNotPartitionDescriptor
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hlookup Hcons.
intros.
apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag with nbL
    curPart currentPD ;trivial;[apply nextEntryIsPPgetPd;trivial|].
apply isAccessibleMappedPage2 with curPart pt;trivial.
unfold isEntryPage.
rewrite Hlookup;trivial.
intros;subst;split;trivial.
Qed.

Lemma accessibleChildPageIsAccessibleIntoParentUpdateUserFlagFlase s pt vaValue entry 
ptsh1 currentPD nbL curPart:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
accessibleChildPageIsAccessibleIntoParent s -> 
(exists va : vaddr, isEntryVA ptsh1 (StateLib.getIndexOfAddr vaValue fstLevel) va s /\ 
beqVAddr defaultVAddr va = true) -> 
parentInPartitionList s -> 
partitionDescriptorEntry s ->
currentPartitionInPartitionsList s -> 
nextEntryIsPP  curPart PDidx currentPD s -> 
Some nbL = StateLib.getNbLevel -> 
isChild s -> 
physicalPageNotDerived s -> 
configTablesAreDifferent s -> 
noDupConfigPagesList s ->
noDupMappedPagesList s ->
(defaultPage =? pt) = false ->
isPE pt (StateLib.getIndexOfAddr vaValue fstLevel) s -> 
getTableAddrRoot pt PDidx curPart vaValue s -> 
entryPresentFlag pt (StateLib.getIndexOfAddr vaValue fstLevel) true s -> 
isVE ptsh1 (StateLib.getIndexOfAddr vaValue fstLevel) s -> 
getTableAddrRoot ptsh1 sh1idx curPart vaValue s -> 
(defaultPage =? ptsh1) = false -> 
In curPart (getPartitions multiplexer s) ->
accessibleChildPageIsAccessibleIntoParent
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hcons Hexist Hparent Hpde.
intros.
destruct Hexist as (vaInAncestor & HvaInAncestor & Hnotderived).
assert(Hcurentparent : (exists entry : page, nextEntryIsPP curPart PPRidx entry s /\
     entry <> defaultPage) ).
{ apply Hpde;trivial.
  do 4 right;left;trivial. }
destruct Hcurentparent as (ancestor & Hancestor & Hancestornotnull).
assert(Hancestorpart : In ancestor (getPartitions multiplexer s)).
{ unfold parentInPartitionList in *.
  apply Hparent with curPart;trivial. }
unfold partitionDescriptorEntry in *.
assert(exists entry : page, nextEntryIsPP ancestor PDidx entry s /\ entry <> defaultPage)
  as (pdAncestor & Hpdancestor & Hpdancesnotnull).
apply Hpde;trivial.
left;trivial.      
apply accessibleChildPageIsAccessibleIntoParentUpdate with 
ptsh1 curPart currentPD nbL;
trivial.
+ apply nextEntryIsPPgetPd;trivial.
+ intros; subst;split;trivial.
+ intros;subst;split;trivial.
+ exists vaInAncestor;split;trivial.
Qed.

Lemma consistencyUpdateUserFlagFalse s pt vaValue entry currentPD nbL (ptsh1:page) curPart:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
consistency s -> 
Some nbL = StateLib.getNbLevel -> 
(defaultPage =? pt) = false -> 
nextEntryIsPP curPart PDidx currentPD s -> 
getTableAddrRoot pt PDidx curPart vaValue s -> 
isPE pt  (StateLib.getIndexOfAddr vaValue fstLevel) s -> 
entryPresentFlag pt (StateLib.getIndexOfAddr vaValue fstLevel) true s -> 
entryUserFlag pt (StateLib.getIndexOfAddr vaValue fstLevel) true s ->
(exists va : vaddr,
 isEntryVA ptsh1 (StateLib.getIndexOfAddr vaValue fstLevel) va s /\ beqVAddr defaultVAddr va = true) ->
isVE ptsh1 (StateLib.getIndexOfAddr vaValue fstLevel) s -> 
getTableAddrRoot ptsh1 sh1idx curPart vaValue s -> 
(defaultPage =? ptsh1) = false -> 
In curPart (getPartitions multiplexer s) ->
consistency
  {|
  currentPartition := currentPartition s;
  memory := add pt  (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Hcons.
intros.
assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
apply getPartitionsUpdateUserFlag; trivial.
unfold consistency in *.
intuition.
+ (** partitionDescriptorEntry **)
  apply partitionDescriptorEntryUpdateUserFlag;trivial.
+ (** dataStructurePdSh1Sh2asRoot **)
  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;trivial.
+ (** dataStructurePdSh1Sh2asRoot **)
  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;trivial.
+ (** dataStructurePdSh1Sh2asRoot **)
  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;trivial.
+ (** currentPartitionInPartitionsList **)
  unfold currentPartitionInPartitionsList in *.    
  rewrite Hpartitions. trivial.
+ (** noDupMappedPagesList **)
  apply noDupMappedPagesListUpdateUserFlag;trivial.
+ (** noDupConfigPagesList **)
  apply getIndirectionsNoDupUpdateUserFlag; trivial.
+ (** parentInPartitionList **)
  apply parentInPartitionListUpdateUserFlag;trivial.
+ (** accessibleVAIsNotPartitionDescriptor **)
  apply accessibleVAIsNotPartitionDescriptorUpdateUserFlagFalse with  nbL currentPD curPart;trivial.
+ (** accessibleChildPageIsAccessibleIntoParent **)
  apply accessibleChildPageIsAccessibleIntoParentUpdateUserFlagFlase with ptsh1 currentPD nbL curPart;trivial.
+ (** noCycleInPartitionTree **)
  apply noCycleInPartitionTreeUpdateUserFlag;trivial.
+ (** configTablesAreDifferent **)
  apply configTablesAreDifferentUpdateUserFlag;trivial.
+ (** isChild **)
  apply isChildUpdateUserFlag;trivial.
+ (** isPresentNotDefaultIff **)
  unfold isPresentNotDefaultIff in *; intros; unfold s';simpl.
  rewrite readPhyEntryUpdateUserFlag;trivial.
  rewrite readPresentUpdateUserFlag;trivial.
+ (** physicalPageNotDerived **)
  apply physicalPageNotDerivedUpdateUserFlag;intuition.
+ (** multiplexerWithoutParent  *)
    unfold multiplexerWithoutParent in *;unfold s';simpl.
    rewrite getParentUpdateUserFlag;trivial.
+ (** isParent **)
  unfold isParent in *; intros parent partition Hin1 Hin2;
  unfold s' in *;simpl in *.
  rewrite getPartitionsUpdateUserFlag in *;trivial.
  rewrite getParentUpdateUserFlag in *;trivial.
  rewrite getChildrenUpdateFlagUser in *;trivial.
  intuition.
+ (** noDupPartitionTree *)
  unfold noDupPartitionTree in *; unfold s' in *.
  rewrite getPartitionsUpdateUserFlag in *;trivial. 
+ (** wellFormedFstShadow **)
   apply wellFormedFstShadowUpdateUserFlag;trivial. 
+ (** wellFormedSndShadow **) 
  apply wellFormedSndShadowUpdateUserFlag;trivial.
+ (** wellFormedShadows **)
  apply wellFormedShadowsUpdateUserFlag;trivial.
+ (** wellFormedShadows **)
  apply wellFormedShadowsUpdateUserFlag;trivial.
+ (**  wellFormedFstShadowIfNone **)
  apply wellFormedFstShadowIfNoneUpdateUserFlag;trivial.
+ (** wellFormedFstShadowIfDefaultValues **)
  apply wellFormedFstShadowIfDefaultValuesUpdateUserFlag;trivial.
Qed.

Lemma getTableAddrRootUpdateUserFlag s pt vaValue entry flag 
root part vaTranslate idxroot:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
getTableAddrRoot root idxroot part vaTranslate s -> 
getTableAddrRoot root idxroot part vaTranslate
  {|
  currentPartition := currentPartition s;
  memory := add pt (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Htoprop.
unfold getTableAddrRoot in *.
destruct Htoprop as (Htrue & Htableroot).
split; trivial.
intros tableroot Hi3.
apply nextEntryIsPPUpdateUserFlag' in Hi3.
generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
exists nbL. split;trivial.
exists stop. split; trivial.
rewrite <- Hind.
apply getIndirectionUpdateUserFlag;trivial.
Qed.

Lemma indirectionDescriptionUpdateUserFlag s pt vaValue entry flag 
root part vaTranslate idxroot nbL:
lookup pt (StateLib.getIndexOfAddr vaValue fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
indirectionDescription s part root idxroot vaTranslate nbL -> 
indirectionDescription   {|
  currentPartition := currentPartition s;
  memory := add pt (StateLib.getIndexOfAddr vaValue fstLevel) 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} part root idxroot vaTranslate nbL.
Proof.
set(s':= {| currentPartition := _ |} ) in *.
intros Hlookup Htoprop.
unfold indirectionDescription in *.
destruct Htoprop as (tableroot & Hpp & Hnotnull & Htableroot).
exists tableroot;split.
apply nextEntryIsPPUpdateUserFlag;trivial.
split;trivial.
destruct Htableroot as [Htableroot | Htableroot] ;[left;trivial|right].
destruct Htableroot as (nbL0 & stop & Hnbl0 & Hstop & Hind & Hdef & Hnbl).
exists nbL0;exists stop. try repeat split;trivial.
rewrite <- Hind.
apply getIndirectionUpdateUserFlag;trivial.
Qed.

Set Nested Proofs Allowed.
Lemma isAccessibleMappedPageInParentUpdateUserFlagFalseEq s entry fstVA currentPart ptMMUFstVA phyMMUaddr nbL:
let s' := {|
currentPartition := currentPartition s;
memory := add ptMMUFstVA (StateLib.getIndexOfAddr fstVA fstLevel)
    (PE
       {|
       read := read entry;
       write := write entry;
       exec := exec entry;
       present := present entry;
       user := false;
       pa := pa entry |}) (memory s) beqPage beqIndex |} in 
       Some nbL = StateLib.getNbLevel -> 
lookup ptMMUFstVA (StateLib.getIndexOfAddr fstVA fstLevel) (memory s) beqPage beqIndex = Some (PE entry) ->
In currentPart (getPartitions multiplexer s) -> 
noCycleInPartitionTree s ->    parentInPartitionList s ->   
partitionDescriptorEntry s -> 
(defaultPage =? ptMMUFstVA) = false -> 
getTableAddrRoot ptMMUFstVA PDidx currentPart fstVA s ->  
configTablesAreDifferent s ->
accessibleChildPageIsAccessibleIntoParent s -> 
isAccessibleMappedPageInParent currentPart fstVA phyMMUaddr s' =
isAccessibleMappedPageInParent currentPart fstVA phyMMUaddr s.
Proof.
intros. 
unfold isAccessibleMappedPageInParent.
unfold s'.
simpl.
rewrite getSndShadowUpdateUserFlag;trivial.
case_eq( StateLib.getSndShadow currentPart (memory s));
intros * Hsh2 ;trivial.
assert( Hvirt :  getVirtualAddressSh2 p
s' fstVA
      =
              getVirtualAddressSh2 p s fstVA).
{ unfold getVirtualAddressSh2.
assert(HnbL: Some nbL = StateLib.getNbLevel) by trivial.
rewrite <- HnbL;trivial.
unfold s'.
rewrite getIndirectionUpdateUserFlag;trivial.
destruct(getIndirection p fstVA nbL (nbLevel - 1) s );trivial.
simpl.
rewrite readVirtualUpdateUserFlag;trivial. }
fold s'.
rewrite Hvirt;trivial.
case_eq (getVirtualAddressSh2 p s fstVA);
intros * Hvainances;trivial.
rewrite getParentUpdateUserFlag;trivial.
case_eq( StateLib.getParent currentPart (memory s)); 
intros * HparentAcestor;trivial.
rewrite getPdUpdateUserFlag;trivial.
case_eq(StateLib.getPd p0 (memory s) );
intros * Hpdparentances;trivial.
assert( Haccessible : 
          getAccessibleMappedPage p1
s' v= 
          getAccessibleMappedPage p1 s v).
{ symmetry.
  
  unfold consistency in *.
  assert(Hdiff : noCycleInPartitionTree s)
  by intuition.
  assert (Hparentpart : parentInPartitionList s ) by  intuition.
  unfold parentInPartitionList in *.
  assert(Hancestor : In p0 (getPartitions multiplexer s)).
  apply Hparentpart with currentPart ;trivial.
  apply nextEntryIsPPgetParent; trivial.
  subst.
  apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions 
  with currentPart p0;trivial.

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
Qed.

Lemma isIndexValueUpdateUserFlag s entry table1 table2 idx1 idx2 flag vx:
lookup table2 idx2 
            (memory s) beqPage beqIndex = Some (PE entry) ->
isIndexValue table1 idx1 vx s ->
isIndexValue table1 idx1 vx {|
      currentPartition := currentPartition s;
      memory := add table2
                  idx2
                  (PE
                     {|
                     read := read entry;
                     write := write entry;
                     exec := exec entry;
                     present := present entry;
                     user := flag;
                     pa := pa entry |}) (memory s) beqPage
                  beqIndex |}.
Proof.
intros.
unfold isIndexValue in *. 
cbn. 
case_eq (beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite H in H0. trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  table1 idx1   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed. 
                
                  
Lemma getAccessibleMappedPageNoneUpdateUserFlagFalse pd va1 entry idxva ptvaInAncestor s:
getAccessibleMappedPage pd s va1 = NonePage -> 
lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry) -> 
getAccessibleMappedPage pd  {|
currentPartition := currentPartition s;
memory := add ptvaInAncestor idxva
      (PE
         {|
         read := read entry;
         write := write entry;
         exec := exec entry;
         present := present entry;
         user := false;
         pa := pa entry |}) (memory s) beqPage beqIndex |} va1 = NonePage.
Proof.
intros Heq Hlookup.
set(s':=  {|
currentPartition := _ |}).
unfold getAccessibleMappedPage in *.
destruct (StateLib.getNbLevel); trivial.
assert(Hind : getIndirection pd va1 l (nbLevel - 1) s' =
getIndirection pd va1 l (nbLevel - 1) s) by ( 
apply getIndirectionUpdateUserFlag; trivial).
rewrite Hind in *.            
destruct (getIndirection pd va1 l (nbLevel - 1) s);trivial.
destruct ( defaultPage =? p);trivial.
assert(Hread :  StateLib.readPresent p (StateLib.getIndexOfAddr va1 fstLevel) (memory s')=
StateLib.readPresent p (StateLib.getIndexOfAddr va1 fstLevel) (memory s))
by (apply readPresentUpdateUserFlag; trivial).
rewrite Hread in *.
destruct (StateLib.readPresent p (StateLib.getIndexOfAddr va1 fstLevel) (memory s));
trivial. destruct b;trivial.
unfold StateLib.readAccessible in *.
simpl in *. 
case_eq( beqPairs (ptvaInAncestor, idxva) (p, StateLib.getIndexOfAddr va1 fstLevel) beqPage beqIndex);
intros Hpairs.  
simpl in *;trivial. 
assert(lookup p (StateLib.getIndexOfAddr va1 fstLevel)
(removeDup ptvaInAncestor idxva (memory s) beqPage beqIndex) beqPage beqIndex =
lookup p (StateLib.getIndexOfAddr va1 fstLevel) (memory s) beqPage beqIndex).
apply removeDupIdentity.
apply beqPairsFalse in Hpairs.
intuition.
rewrite H.
case_eq( match lookup p (StateLib.getIndexOfAddr va1 fstLevel) (memory s) beqPage beqIndex with
| Some (PE a) => Some (user a)
| _ => None
end);intros; trivial.
rewrite H0 in *.
destruct b;trivial.
rewrite readPhyEntryUpdateUserFlag; trivial. 
Qed.


Lemma writeAccessiblePropagatePropertiesPrepareFstVA ( ptMMUTrdVA phySh2addr phySh1addr
indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 
phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 
descChildphy phySh1Child currentPart: page) (trdVA  nextVA  vaToPrepare sndVA fstVA : vaddr) 
(nbLgen  l:level) (userMMUSndVA userMMUTrdVA :bool) idxFstVA idxSndVA idxTrdVA zeroI LLroot LLChildphy newLastLLable minFI indMMUToPreparebool:
{{ fun s => propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable  s ptMMUTrdVA phySh2addr phySh1addr
indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 
phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 
descChildphy phySh1Child currentPart trdVA  nextVA  vaToPrepare sndVA fstVA nbLgen  l true userMMUSndVA userMMUTrdVA true true true
idxFstVA idxSndVA idxTrdVA zeroI minFI
/\ isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA
}}
 writeAccessible ptMMUFstVA idxFstVA false 
{{  fun _ s => propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable  s ptMMUTrdVA phySh2addr phySh1addr
indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 
phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 
descChildphy phySh1Child currentPart trdVA  nextVA  vaToPrepare sndVA fstVA nbLgen  l false userMMUSndVA userMMUTrdVA true true true
idxFstVA idxSndVA idxTrdVA zeroI minFI
/\ isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA
/\ isAccessibleMappedPageInParent currentPart fstVA phyMMUaddr s = true }}.
Proof.
intros.
subst.
eapply WP.weaken.
eapply WP.writeAccessible.
simpl.
intros;simpl. 
assert (exists entry : Pentry,
lookup ptMMUFstVA (StateLib.getIndexOfAddr fstVA fstLevel) (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
{ apply isPELookupEq.
  unfold propagatedPropertiesPrepare in *. intuition. }
destruct Hlookup as (entry & Hlookup).
exists entry.
split.
unfold propagatedPropertiesPrepare in *. 
intuition;subst;trivial.
set (s':= {| currentPartition := _ |}).
assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
{ apply getPartitionsUpdateUserFlag; trivial.
 unfold propagatedPropertiesPrepare in *.
 intuition;subst;trivial. }
assert(getChildren currentPart s' = getChildren currentPart s) as Hchildren.
{ apply getChildrenUpdateFlagUser; trivial.
 unfold propagatedPropertiesPrepare in *.
 intuition;subst;trivial. }
unfold propagatedPropertiesPrepare, indirectionDescriptionAll, initPEntryTablePreconditionToPropagatePreparePropertiesAll in *.
intuition;subst;trivial.
+ apply kernelDataIsolationUpdateUserFlagFalse;trivial.
+ apply partitionsIsolationUpdateUserFlag;trivial.
+ apply verticalSharingUpdateUserFlag;trivial.
+ apply consistencyUpdateUserFlagFalse with  currentPD nbLgen ptSh1FstVA (currentPartition s);trivial.
  unfold consistency in *. intuition.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isPEUpdateUserFlag; assumption.
(* + apply isVAUserUpdateUserFlag;trivial. *)
+ assert(exists va : vaddr, isEntryVA ptSh1TrdVA (StateLib.getIndexOfAddr trdVA fstLevel) va s 
  /\ beqVAddr defaultVAddr va = true) as (va & Hva & Hdef);trivial .
  exists va.
  split; [ apply isEntryVAUpdateUserFlag | ];trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isVEUpdateUserFlag;assumption.
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply entryPresentFlagUpdateUserFlag;assumption.
+ unfold s'.
  assert(ptMMUFstVA <> ptMMUTrdVA \/ 
  (StateLib.getIndexOfAddr fstVA fstLevel) <> (StateLib.getIndexOfAddr trdVA fstLevel)).
  apply toApplyPageTablesOrIndicesAreDifferent with fstVA trdVA (currentPartition s)
    currentPD PDidx nbLgen isPE s; intuition;subst;trivial.
  apply entryUserFlagUpdateUserFlagRandomValue; intuition.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isPEUpdateUserFlag; assumption.
+ assert(exists va : vaddr, isEntryVA ptSh1SndVA (StateLib.getIndexOfAddr sndVA fstLevel) va s 
  /\ beqVAddr defaultVAddr va = true) as (va & Hva & Hdef);trivial .
  exists va.
  split; [ apply isEntryVAUpdateUserFlag | ];trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isVEUpdateUserFlag;assumption.
+ assert(exists va : vaddr, isEntryVA ptSh1FstVA (StateLib.getIndexOfAddr fstVA fstLevel) va s 
  /\ beqVAddr defaultVAddr va = true) as (va & Hva & Hdef);trivial .
  exists va.
  split; [ apply isEntryVAUpdateUserFlag | ];trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isVEUpdateUserFlag;assumption.
(* + apply isVAUserUpdateUserFlag;trivial. *)
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply entryPresentFlagUpdateUserFlag;assumption.
+ unfold s'.
  assert(ptMMUFstVA <> ptMMUSndVA \/ (StateLib.getIndexOfAddr fstVA fstLevel) <> 
  (StateLib.getIndexOfAddr sndVA fstLevel) ).
  apply toApplyPageTablesOrIndicesAreDifferent with  fstVA sndVA (currentPartition s)
    currentPD PDidx nbLgen isPE s; intuition;subst;trivial.
  apply entryUserFlagUpdateUserFlagRandomValue; intuition.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isPEUpdateUserFlag; assumption.
(* + apply isVAUserUpdateUserFlag;trivial. *)
+ (** new property **)
  unfold entryUserFlag; unfold s'; cbn.
  assert( beqPairs (ptMMUFstVA, StateLib.getIndexOfAddr fstVA fstLevel) (ptMMUFstVA, StateLib.getIndexOfAddr fstVA fstLevel) beqPage beqIndex = true) as Hpairs.
  apply beqPairsTrue; split;trivial.
  rewrite Hpairs;  cbn;trivial.
+ apply entryPresentFlagUpdateUserFlag;assumption.
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply nextEntryIsPPUpdateUserFlag;trivial.
+ apply nextEntryIsPPUpdateUserFlag;trivial.
+ apply nextEntryIsPPUpdateUserFlag;trivial.
+ rewrite Hpartitions;trivial.
+ unfold s' in *;simpl. rewrite Hchildren;trivial.
+ apply indirectionDescriptionUpdateUserFlag;trivial.
+ apply indirectionDescriptionUpdateUserFlag;trivial.
+ apply indirectionDescriptionUpdateUserFlag;trivial. 
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateUserFlag;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateUserFlag;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateUserFlag;trivial.
+ assert(Hconf: getConfigTablesLinkedList descChildphy (memory s) = Some LLroot) by trivial.
  rewrite <- Hconf.
  apply getConfigTablesLinkedListUpdateUserFlag;trivial.
+ assert(Hconf: getLLPages LLroot s (nbPage + 1) = getLLPages LLroot s' (nbPage + 1)).
  symmetry.
  apply getConfigTablesLinkedListsUpdateUserFlag;trivial.
  rewrite <- Hconf;trivial.
+ assert(Hconf: getLLPages LLroot s (nbPage + 1) = getLLPages LLroot s' (nbPage + 1)).
  symmetry.
  apply getConfigTablesLinkedListsUpdateUserFlag;trivial.
  rewrite <- Hconf;trivial.
+ assert(exists NbFI : index, isIndexValue newLastLLable (CIndex 1) NbFI s /\ NbFI >=  minFI) as (x & Hx & Hx1) by trivial.
  exists x.
  split;trivial.
  apply isIndexValueUpdateUserFlag;trivial.
+ unfold isPartitionFalseAll in *;
  unfold isPartitionFalse; unfold s'; cbn.
  repeat rewrite readPDflagUpdateUserFlag;trivial.
+ assert(Hisaccessible : isAccessibleMappedPageInParent (currentPartition s) fstVA phyMMUaddr s = true).
  assert(Hcons : consistency s) by (unfold propagatedProperties in *; intuition).
  unfold consistency in Hcons.
  assert(Haccess : accessibleChildPageIsAccessibleIntoParent s) by intuition.
  unfold accessibleChildPageIsAccessibleIntoParent in Haccess.
  apply Haccess with currentPD;intuition.
  apply nextEntryIsPPgetPd;trivial.
  apply isAccessibleMappedPage2 with (currentPartition s) ptMMUFstVA;trivial.
  intros;subst;split;trivial.
  rewrite <- Hisaccessible.
  unfold consistency in *. 
  apply isAccessibleMappedPageInParentUpdateUserFlagFalseEq with nbLgen;intuition. 
Qed.

Lemma writeAccessiblePropagatePropertiesPrepareSndVA ( ptMMUTrdVA phySh2addr phySh1addr
indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 
phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 
descChildphy phySh1Child currentPart: page) (trdVA  nextVA  vaToPrepare sndVA fstVA : vaddr) 
(nbLgen  l:level) ( userMMUTrdVA :bool) idxFstVA idxSndVA idxTrdVA zeroI LLroot LLChildphy newLastLLable minFI indMMUToPreparebool:
{{ fun s => propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr
indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 
phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 
descChildphy phySh1Child currentPart trdVA  nextVA  vaToPrepare sndVA fstVA nbLgen  l false true userMMUTrdVA true true true
idxFstVA idxSndVA idxTrdVA  zeroI minFI
/\ isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA
}}
 writeAccessible ptMMUSndVA idxSndVA false 
{{  fun _ s => propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr
indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 
phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 
descChildphy phySh1Child currentPart trdVA  nextVA  vaToPrepare sndVA fstVA nbLgen  l false false userMMUTrdVA true true true
idxFstVA idxSndVA idxTrdVA  zeroI minFI
/\ isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA
/\ isAccessibleMappedPageInParent currentPart sndVA phySh1addr s = true }}.
Proof.
intros.
subst.
eapply WP.weaken.
eapply WP.writeAccessible.
simpl.
intros;simpl.
unfold propagatedPropertiesPrepare, indirectionDescriptionAll, initPEntryTablePreconditionToPropagatePreparePropertiesAll in *.  
assert (exists entry : Pentry,
lookup ptMMUSndVA (StateLib.getIndexOfAddr sndVA fstLevel) (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
{ apply isPELookupEq.
  intuition. }
destruct Hlookup as (entry & Hlookup).
exists entry.
split. 
intuition;subst;trivial.
set (s':= {| currentPartition := _ |}).
assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
{ apply getPartitionsUpdateUserFlag; trivial. intuition;subst;trivial. }
assert(getChildren currentPart s' = getChildren currentPart s) as Hchildren.
{ apply getChildrenUpdateFlagUser; trivial.
 unfold propagatedPropertiesPrepare in *.
 intuition;subst;trivial. }
intuition;subst;trivial.
+ apply kernelDataIsolationUpdateUserFlagFalse;trivial.
+ apply partitionsIsolationUpdateUserFlag;trivial.
+ apply verticalSharingUpdateUserFlag;trivial.
+ apply consistencyUpdateUserFlagFalse with  currentPD nbLgen ptSh1SndVA (currentPartition s);trivial.
  unfold consistency in *. intuition.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isPEUpdateUserFlag; assumption.
(* + apply isVAUserUpdateUserFlag;trivial. *)
+ assert(exists va : vaddr, isEntryVA ptSh1TrdVA (StateLib.getIndexOfAddr trdVA fstLevel) va s 
  /\ beqVAddr defaultVAddr va = true) as (va & Hva & Hdef);trivial .
  exists va.
  split; [ apply isEntryVAUpdateUserFlag | ];trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isVEUpdateUserFlag;assumption.
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply entryPresentFlagUpdateUserFlag;assumption.
+ unfold s'.
  assert(ptMMUSndVA <> ptMMUTrdVA \/ 
  (StateLib.getIndexOfAddr sndVA fstLevel) <> (StateLib.getIndexOfAddr trdVA fstLevel)).
  apply toApplyPageTablesOrIndicesAreDifferent with sndVA trdVA (currentPartition s)
    currentPD PDidx nbLgen isPE s; intuition;subst;trivial.
  apply entryUserFlagUpdateUserFlagRandomValue; intuition.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isPEUpdateUserFlag; assumption.
+ assert(exists va : vaddr, isEntryVA ptSh1SndVA (StateLib.getIndexOfAddr sndVA fstLevel) va s 
  /\ beqVAddr defaultVAddr va = true) as (va & Hva & Hdef);trivial .
  exists va.
  split; [ apply isEntryVAUpdateUserFlag | ];trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isVEUpdateUserFlag;assumption.
+ assert(exists va : vaddr, isEntryVA ptSh1FstVA (StateLib.getIndexOfAddr fstVA fstLevel) va s 
  /\ beqVAddr defaultVAddr va = true) as (va & Hva & Hdef);trivial .
  exists va.
  split; [ apply isEntryVAUpdateUserFlag | ];trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isVEUpdateUserFlag;assumption.
(* + apply isVAUserUpdateUserFlag;trivial. *)
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply entryPresentFlagUpdateUserFlag;assumption.
+ (** new property **)
  unfold entryUserFlag; unfold s'; cbn.
  assert( beqPairs (ptMMUSndVA, StateLib.getIndexOfAddr sndVA fstLevel) (ptMMUSndVA, StateLib.getIndexOfAddr sndVA fstLevel) beqPage beqIndex = true) as Hpairs.
  apply beqPairsTrue; split;trivial.
  rewrite Hpairs;  cbn;trivial. 
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isPEUpdateUserFlag; assumption.
(* + apply isVAUserUpdateUserFlag;trivial. *)
+ unfold s'.
  assert(ptMMUFstVA <> ptMMUSndVA \/ (StateLib.getIndexOfAddr fstVA fstLevel) <> 
  (StateLib.getIndexOfAddr sndVA fstLevel) ).
  apply toApplyPageTablesOrIndicesAreDifferent with  fstVA sndVA (currentPartition s)
    currentPD PDidx nbLgen isPE s; intuition;subst;trivial.
  apply entryUserFlagUpdateUserFlagRandomValue; intuition.
+ apply entryPresentFlagUpdateUserFlag;assumption.
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply nextEntryIsPPUpdateUserFlag;trivial.
+ apply nextEntryIsPPUpdateUserFlag;trivial.
+ apply nextEntryIsPPUpdateUserFlag;trivial.
+ rewrite Hpartitions;trivial.
+ unfold s' in *;simpl. rewrite Hchildren;trivial.
+ apply indirectionDescriptionUpdateUserFlag;trivial.
+ apply indirectionDescriptionUpdateUserFlag;trivial.
+ apply indirectionDescriptionUpdateUserFlag;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateUserFlag;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateUserFlag;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateUserFlag;trivial.
+ assert(Hconf: getConfigTablesLinkedList descChildphy (memory s) = Some LLroot) by trivial.
  rewrite <- Hconf.
  apply getConfigTablesLinkedListUpdateUserFlag;trivial. 
+ assert(Hconf: getLLPages LLroot s (nbPage + 1) = getLLPages LLroot s' (nbPage + 1)).
  symmetry.
  apply getConfigTablesLinkedListsUpdateUserFlag;trivial.
  rewrite <- Hconf;trivial.
+ assert(Hconf: getLLPages LLroot s (nbPage + 1) = getLLPages LLroot s' (nbPage + 1)).
  symmetry.
  apply getConfigTablesLinkedListsUpdateUserFlag;trivial.
  rewrite <- Hconf;trivial.
+ assert(exists NbFI : index, isIndexValue newLastLLable (CIndex 1) NbFI s /\ NbFI >=  minFI) as (x & Hx & Hx1) by trivial.
  exists x.
  split;trivial.
  apply isIndexValueUpdateUserFlag;trivial.
+ unfold isPartitionFalseAll in *;
  unfold isPartitionFalse; unfold s'; cbn.
  repeat rewrite readPDflagUpdateUserFlag;trivial.
   
+ assert(Hisaccessible : isAccessibleMappedPageInParent (currentPartition s) sndVA phySh1addr s = true).
  assert(Hcons : consistency s) by (unfold propagatedProperties in *; intuition).
  unfold consistency in Hcons.
  assert(Haccess : accessibleChildPageIsAccessibleIntoParent s) by intuition.
  unfold accessibleChildPageIsAccessibleIntoParent in Haccess.
  apply Haccess with currentPD;intuition.
  apply nextEntryIsPPgetPd;trivial.
  apply isAccessibleMappedPage2 with (currentPartition s) ptMMUSndVA;trivial.
  intros;subst;split;trivial.
  rewrite <- Hisaccessible.
  unfold consistency in *.
  apply isAccessibleMappedPageInParentUpdateUserFlagFalseEq with nbLgen;intuition.
Qed. 
 
Lemma writeAccessiblePropagatePropertiesPrepareTrdVA ( ptMMUTrdVA phySh2addr phySh1addr
indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 
phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 
descChildphy phySh1Child currentPart: page) (trdVA  nextVA  vaToPrepare sndVA fstVA : vaddr) 
(nbLgen  l:level) (* ( userMMUTrdVA :bool)  *)idxFstVA idxSndVA idxTrdVA zeroI LLroot LLChildphy newLastLLable minFI indMMUToPreparebool:
{{ fun s => propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr
indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 
phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 
descChildphy phySh1Child currentPart trdVA  nextVA  vaToPrepare sndVA fstVA nbLgen  l false false true true true true
idxFstVA idxSndVA idxTrdVA  zeroI minFI
/\ isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA
}}
 writeAccessible ptMMUTrdVA idxTrdVA false 
{{  fun _ s => propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr
indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 
phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 
descChildphy phySh1Child currentPart trdVA  nextVA  vaToPrepare sndVA fstVA nbLgen  l false false false true true true
idxFstVA idxSndVA idxTrdVA  zeroI minFI
/\ isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA
/\ isAccessibleMappedPageInParent currentPart trdVA phySh2addr s = true }}.
Proof.
intros.
subst.
eapply WP.weaken.
eapply WP.writeAccessible.
simpl.
intros;simpl.
unfold propagatedPropertiesPrepare, indirectionDescriptionAll, initPEntryTablePreconditionToPropagatePreparePropertiesAll in *.  
assert (exists entry : Pentry,
lookup ptMMUTrdVA (StateLib.getIndexOfAddr trdVA fstLevel) (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
{ apply isPELookupEq.
  intuition. }
destruct Hlookup as (entry & Hlookup).
exists entry.
split. 
intuition;subst;trivial.
set (s':= {| currentPartition := _ |}).
assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
{ apply getPartitionsUpdateUserFlag; trivial. intuition;subst;trivial. }
assert(getChildren currentPart s' = getChildren currentPart s) as Hchildren.
{ apply getChildrenUpdateFlagUser; trivial.
 unfold propagatedPropertiesPrepare in *.
 intuition;subst;trivial. }
intuition;subst;trivial.
+ apply kernelDataIsolationUpdateUserFlagFalse;trivial.
+ apply partitionsIsolationUpdateUserFlag;trivial.
+ apply verticalSharingUpdateUserFlag;trivial.
+ apply consistencyUpdateUserFlagFalse with  currentPD nbLgen ptSh1TrdVA (currentPartition s);trivial.
  unfold consistency in *. intuition.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isPEUpdateUserFlag; assumption.
(* + apply isVAUserUpdateUserFlag;trivial. *)
+ assert(exists va : vaddr, isEntryVA ptSh1TrdVA (StateLib.getIndexOfAddr trdVA fstLevel) va s 
  /\ beqVAddr defaultVAddr va = true) as (va & Hva & Hdef);trivial .
  exists va.
  split; [ apply isEntryVAUpdateUserFlag | ];trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isVEUpdateUserFlag;assumption.
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply entryPresentFlagUpdateUserFlag;assumption.
+ (** new property **)
  unfold entryUserFlag; unfold s'; cbn.
  assert( beqPairs (ptMMUTrdVA, StateLib.getIndexOfAddr trdVA fstLevel) (ptMMUTrdVA, StateLib.getIndexOfAddr trdVA fstLevel) beqPage beqIndex = true) as Hpairs.
  apply beqPairsTrue; split;trivial.
  rewrite Hpairs;  cbn;trivial. 
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isPEUpdateUserFlag; assumption.
+ assert(exists va : vaddr, isEntryVA ptSh1SndVA (StateLib.getIndexOfAddr sndVA fstLevel) va s 
  /\ beqVAddr defaultVAddr va = true) as (va & Hva & Hdef);trivial .
  exists va.
  split; [ apply isEntryVAUpdateUserFlag | ];trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isVEUpdateUserFlag;assumption.
+ assert(exists va : vaddr, isEntryVA ptSh1FstVA (StateLib.getIndexOfAddr fstVA fstLevel) va s 
  /\ beqVAddr defaultVAddr va = true) as (va & Hva & Hdef);trivial .
  exists va.
  split; [ apply isEntryVAUpdateUserFlag | ];trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isVEUpdateUserFlag;assumption.
(* + apply isVAUserUpdateUserFlag;trivial. *)
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply entryPresentFlagUpdateUserFlag;assumption.
+ unfold s'.
  assert(ptMMUSndVA <> ptMMUTrdVA \/ 
  (StateLib.getIndexOfAddr sndVA fstLevel) <> (StateLib.getIndexOfAddr trdVA fstLevel)).
  apply toApplyPageTablesOrIndicesAreDifferent with sndVA trdVA (currentPartition s)
    currentPD PDidx nbLgen isPE s; intuition;subst;trivial.
  apply entryUserFlagUpdateUserFlagRandomValue; intuition.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isPEUpdateUserFlag; assumption.
(* + apply isVAUserUpdateUserFlag;trivial. *)
+ unfold s'.
  assert(ptMMUFstVA <> ptMMUTrdVA \/ (StateLib.getIndexOfAddr fstVA fstLevel) <> 
  (StateLib.getIndexOfAddr trdVA fstLevel) ).
  apply toApplyPageTablesOrIndicesAreDifferent with  fstVA trdVA (currentPartition s)
    currentPD PDidx nbLgen isPE s; intuition;subst;trivial.
  apply entryUserFlagUpdateUserFlagRandomValue; intuition.
+ apply entryPresentFlagUpdateUserFlag;assumption.
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply nextEntryIsPPUpdateUserFlag;trivial.
+ apply nextEntryIsPPUpdateUserFlag;trivial.
+ apply nextEntryIsPPUpdateUserFlag;trivial.
+ rewrite Hpartitions;trivial.
+ unfold s' in *;simpl. rewrite Hchildren;trivial.
+ apply indirectionDescriptionUpdateUserFlag;trivial.
+ apply indirectionDescriptionUpdateUserFlag;trivial.
+ apply indirectionDescriptionUpdateUserFlag;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateUserFlag;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateUserFlag;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateUserFlag;trivial.
+ assert(Hconf: getConfigTablesLinkedList descChildphy (memory s) = Some LLroot) by trivial.
  rewrite <- Hconf.
  apply getConfigTablesLinkedListUpdateUserFlag;trivial.
+ assert(Hconf: getLLPages LLroot s (nbPage + 1) = getLLPages LLroot s' (nbPage + 1)).
  symmetry.
  apply getConfigTablesLinkedListsUpdateUserFlag;trivial.
  rewrite <- Hconf;trivial.
+ assert(Hconf: getLLPages LLroot s (nbPage + 1) = getLLPages LLroot s' (nbPage + 1)).
  symmetry.
  apply getConfigTablesLinkedListsUpdateUserFlag;trivial.
  rewrite <- Hconf;trivial.
+ assert(exists NbFI : index, isIndexValue newLastLLable (CIndex 1) NbFI s /\ NbFI >=  minFI) as (x & Hx & Hx1) by trivial.
  exists x.
  split;trivial.
  apply isIndexValueUpdateUserFlag;trivial.  
+ unfold isPartitionFalseAll in *;
  unfold isPartitionFalse; unfold s'; cbn.
  repeat rewrite readPDflagUpdateUserFlag;trivial. 
+ assert(Hisaccessible : isAccessibleMappedPageInParent (currentPartition s) trdVA phySh2addr s = true).
  assert(Hcons : consistency s) by (unfold propagatedProperties in *; intuition).
  unfold consistency in Hcons.
  assert(Haccess : accessibleChildPageIsAccessibleIntoParent s) by intuition.
  unfold accessibleChildPageIsAccessibleIntoParent in Haccess.
  apply Haccess with currentPD;intuition.
  apply nextEntryIsPPgetPd;trivial.
  apply isAccessibleMappedPage2 with (currentPartition s) ptMMUTrdVA;trivial.
  intros;subst;split;trivial.
  rewrite <- Hisaccessible.
  unfold consistency in *.
  apply isAccessibleMappedPageInParentUpdateUserFlagFalseEq with nbLgen;intuition.
Qed. 
  
Lemma writeAccessiblePropagateWriteAccessibleRecProperty pg currentPart idxToUpdate ptToUpdate (vaToUpdate: vaddr):
{{ fun s => preconditionToPropagateWriteAccessibleRecProperty s ptToUpdate vaToUpdate idxToUpdate
/\ (forall partition : page, In partition (getAncestors currentPart s) -> ~ In pg (getAccessibleMappedPages partition s))
}}
 writeAccessible ptToUpdate idxToUpdate false 
{{  fun _ s =>
 (forall partition : page, In partition (getAncestors currentPart s) -> ~ In pg (getAccessibleMappedPages partition s)) 
 }}.
Proof.
intros.
subst.
eapply WP.weaken.
eapply WP.writeAccessible.
simpl.
intros;simpl.
unfold preconditionToPropagateWriteAccessibleRecProperty in *.  
assert (exists entry : Pentry,
lookup ptToUpdate (StateLib.getIndexOfAddr vaToUpdate fstLevel) (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
{ apply isPELookupEq.
  intuition. }
destruct Hlookup as (entry & Hlookup).
exists entry.
split.
intuition;subst;trivial.
set (s':= {| currentPartition := _ |}).
assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
{ apply getPartitionsUpdateUserFlag; trivial. intuition;subst;trivial. }
intuition;subst.
assert(Hanc: getAncestors currentPart s' = getAncestors currentPart s) by
      (apply getAncestorsUpdateUserFlag; trivial).
rewrite Hanc in *.
assert(Hfalse : In pg (getAccessibleMappedPages partition s')) by trivial.
contradict Hfalse.
assert(Hnewpropx : forall partition : page,
          In partition (getAncestors currentPart s) ->
          ~ In pg (getAccessibleMappedPages partition s)) by trivial.
assert(~ In pg (getAccessibleMappedPages partition s)).
{ unfold not; intros. apply Hnewpropx with partition; trivial. }
assert(Hincl : incl (getAccessibleMappedPages partition s')(getAccessibleMappedPages partition s)).
apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
unfold incl in *.
unfold not;intros Hfalse.
assert(Htrue : ~ In pg (getAccessibleMappedPages partition s)) by 
trivial.
apply Htrue.
apply Hincl;trivial.
Qed.
 
Lemma consistencyUpdateWriteAccessibleRec s currentPart descParent ancestor pdAncestor pt  va 
sh2 lastIndex  ptsh2  vaInAncestor entry L  defaultV ptvaInAncestor idxva : 
let s' :=  {|
      currentPartition := currentPartition s;
      memory := add ptvaInAncestor idxva
                  (PE
                     {|
                     read := read entry;
                     write := write entry;
                     exec := exec entry;
                     present := present entry;
                     user := false;
                     pa := pa entry |}) (memory s) beqPage beqIndex |} in 
lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
  (memory s) beqPage beqIndex = Some (PE entry) ->
  accessibleVAIsNotPartitionDescriptor s' -> 
partitionsIsolation s -> 
 consistency s ->  
 In ancestor (getPartitions multiplexer s) ->
(* isAccessibleMappedPageInParent descParent va (pa entry) s = true ->  *)
writeAccessibleRecInternalPropertiesPrepare currentPart descParent ancestor pdAncestor pt va 
sh2 lastIndex ptsh2 vaInAncestor entry L defaultV ptvaInAncestor idxva s ->
Some L = StateLib.getNbLevel -> 
StateLib.getIndexOfAddr vaInAncestor fstLevel = idxva -> 
consistency s'.
Proof.    
intros.
unfold writeAccessibleRecInternalPropertiesPrepare in *.
(* set(s':= {|currentPartition := _|} ).
 *) assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
     apply getPartitionsUpdateUserFlag; intuition;subst;trivial.
unfold consistency in *.
intuition;subst.
+ (** partitionDescriptorEntry **)
  apply partitionDescriptorEntryUpdateUserFlag;trivial.
+ (** dataStructurePdSh1Sh2asRoot **)
  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;trivial.
+ (** dataStructurePdSh1Sh2asRoot **)
  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;trivial.
+ (** dataStructurePdSh1Sh2asRoot **)
  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;trivial.
+ (** currentPartitionInPartitionsList **)
  unfold currentPartitionInPartitionsList in *.    
  rewrite Hpartitions. trivial.
+ (** noDupMappedPagesList **)
  apply noDupMappedPagesListUpdateUserFlag;trivial.
+ (** noDupConfigPagesList **)
  apply getIndirectionsNoDupUpdateUserFlag; trivial.
+ (** parentInPartitionList **)
  apply parentInPartitionListUpdateUserFlag;trivial.
+ (** accessibleVAIsNotPartitionDescriptor **)
 (*  assert(HaccessInParent : isAccessibleMappedPageInParent descParent va (pa entry) s = true) by trivial.
  assert(entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) true s/\
        entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) true s) as (Hi & Hii)
    by (apply isAccessibleMappedPageInParentTruePresentAccessible with va entry descParent L sh2 ptsh2 ancestor pdAncestor;trivial).
  apply accessibleVAIsNotPartitionDescriptorUpdateUserFlagFalse with L pdAncestor ancestor;trivial.
 *) 
 (** accessibleChildPageIsAccessibleIntoParent **) 
  apply WriteAccessible.accessibleChildPageIsAccessibleIntoParentUpdateUserFlagFlase
      with L ancestor pdAncestor va ptsh2 descParent pt;trivial;intros;subst;trivial; split;trivial.
+ (** noCycleInPartitionTree **) 
  apply noCycleInPartitionTreeUpdateUserFlag;trivial. 
+ (** configTablesAreDifferent **)
  apply configTablesAreDifferentUpdateUserFlag;trivial.
+ (** isChild **)
  apply isChildUpdateUserFlag;trivial.
+ (** isPresentNotDefaultIff **)
  unfold isPresentNotDefaultIff in *; intros; unfold s';simpl.
  rewrite readPhyEntryUpdateUserFlag;trivial.
  rewrite readPresentUpdateUserFlag;trivial.
+ (** physicalPageNotDerived **)
  apply physicalPageNotDerivedUpdateUserFlag;intuition.
+ (** multiplexerWithoutParent  *)
  unfold multiplexerWithoutParent in *;unfold s';simpl.
  rewrite getParentUpdateUserFlag;trivial.
+ (** isParent **)
  unfold isParent in *; intros parent partition Hin1 Hin2;
  unfold s' in *;simpl in *.
  rewrite getPartitionsUpdateUserFlag in *;trivial.
  rewrite getParentUpdateUserFlag in *;trivial.
  rewrite getChildrenUpdateFlagUser in *;trivial.
  intuition.
+ (** noDupPartitionTree *)
  unfold noDupPartitionTree in *; unfold s' in *.
  rewrite getPartitionsUpdateUserFlag in *;trivial. 
+ (** wellFormedFstShadow **)
   apply wellFormedFstShadowUpdateUserFlag;trivial. 
+ (** wellFormedSndShadow **) 
  apply wellFormedSndShadowUpdateUserFlag;trivial.
+ (** wellFormedShadows **)
  apply wellFormedShadowsUpdateUserFlag;trivial.
+ (** wellFormedShadows **)
  apply wellFormedShadowsUpdateUserFlag;trivial.
+ (**  wellFormedFstShadowIfNone **)
  apply wellFormedFstShadowIfNoneUpdateUserFlag;trivial.
+ (** wellFormedFstShadowIfDefaultValues **)
  apply wellFormedFstShadowIfDefaultValuesUpdateUserFlag;trivial.
  Qed.

Lemma WriteAccessibleRecRecursionInvariant currentPart descParent ancestor pdAncestor pt va 
sh2 lastIndex ptsh2 vaInAncestor entry L defaultV ptvaInAncestor idxva s:
let s':={|
      currentPartition := currentPartition s;
      memory := add ptvaInAncestor idxva
                  (PE
                     {|
                     read := read entry;
                     write := write entry;
                     exec := exec entry;
                     present := present entry;
                     user := false;
                     pa := pa entry |}) (memory s) beqPage beqIndex |} in 
lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) (memory s) beqPage beqIndex = Some (PE entry) /\                     
isAccessibleMappedPageInParent descParent va (pa entry) s = true /\
(isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s = true 
/\ partitionsIsolation s 
/\ consistency s 
/\ writeAccessibleRecInternalPropertiesPrepare currentPart descParent ancestor pdAncestor pt va 
sh2 lastIndex ptsh2 vaInAncestor entry L defaultV ptvaInAncestor idxva s) 
->
(isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s' = true 
/\ partitionsIsolation s' 
/\ consistency s' 
/\ writeAccessibleRecInternalPropertiesPrepare currentPart descParent ancestor pdAncestor pt va 
  sh2 lastIndex ptsh2 vaInAncestor entry L defaultV ptvaInAncestor idxva s')
/\ entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) false s' 
/\ isEntryPage ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) (pa entry) s' 
/\ entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) true s'.
Proof.
intros.
unfold writeAccessibleRecInternalPropertiesPrepare in H.
assert(Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s = true) by intuition.
split.
(** Prove the recursion invariant **)
assert(In ancestor (getPartitions multiplexer s)) as Hancestor.
{ intros;subst;intuition.
assert(Hparentpart : parentInPartitionList s).
unfold consistency in *; intuition.
unfold parentInPartitionList in *.
apply Hparentpart with descParent;trivial. }
split.
(** isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s' = true : postcondition*)
rewrite <- Htrue.
unfold s';intuition;subst.
unfold consistency in *;intuition.
apply isAccessibleMappedPageInParentUpdateUserFlagFalse with L descParent;trivial.
split.
(** partitionsIsolation **)
unfold s';intuition;subst.
apply partitionsIsolationUpdateUserFlag;trivial.
split.
(** consistency **) 
unfold s';intuition;subst.
apply consistencyUpdateWriteAccessibleRec with  currentPart descParent ancestor
      pdAncestor pt va sh2 (StateLib.getIndexOfAddr va fstLevel) ptsh2 vaInAncestor L defaultVAddr;intuition;subst;trivial.
(** PROVE accessibleVAIsNotPartitionDescriptor s' *)
  unfold consistency in *;intuition.
  assert(HaccessInParent : isAccessibleMappedPageInParent descParent va (pa entry) s = true) by trivial.
  assert(entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) true s/\
          entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) true s) as (Hi & Hii)
      by (apply isAccessibleMappedPageInParentTruePresentAccessible with va entry descParent L sh2 ptsh2 ancestor pdAncestor;trivial).
  apply accessibleVAIsNotPartitionDescriptorUpdateUserFlagFalse with L pdAncestor ancestor;trivial.
  unfold writeAccessibleRecInternalPropertiesPrepare in *;intuition. 
(** remaining invariant recursion propeties **) 
apply writeAccessibleRecInternalPropertiesUpdateUserFlag;fold s';intuition.
symmetry.
apply getPartitionsUpdateUserFlag; subst;trivial.
intuition subst;trivial.
unfold writeAccessibleRecInternalPropertiesPrepare;intuition.
(** prove the postcondition **)
unfold entryUserFlag; unfold isEntryPage ; unfold entryPresentFlag.
unfold s'; cbn.
assert( beqPairs (ptvaInAncestor, StateLib.getIndexOfAddr vaInAncestor fstLevel)
 (ptvaInAncestor, StateLib.getIndexOfAddr vaInAncestor fstLevel) beqPage beqIndex = true) as Hpairs
 by(apply beqPairsTrue;  split;trivial).
intuition;subst;
rewrite Hpairs;  cbn;intuition.
unfold consistency in *.
assert(Hpres : isPresentNotDefaultIff s ) by intuition.
symmetry. 
apply phyPageIsPresent with ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s;trivial.
Qed.

Lemma propagatedPropertiesPrepareUpdateUserFlag s descParent pt sh2 lastIndex ancestor pdAncestor ptsh2 defaultV va ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable
           phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
           descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA L l b1 b2 b3 idxFstVA idxSndVA
           idxTrdVA entry idxva ptvaInAncestor vaInAncestor zeroI LLroot LLChildphy newLastLLable minFI indMMUToPreparebool:
let s' := 
  {|
  currentPartition := currentPartition s;
  memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}  in            
propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable
           phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
           descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA L l b1 b2 b3 true true true idxFstVA idxSndVA
           idxTrdVA zeroI minFI ->
lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry) -> 
isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s = true -> 
In ancestor (getPartitions MALInternal.multiplexer s) -> 
partitionsIsolation s /\
     consistency s /\
     In currentPart (getPartitions MALInternal.multiplexer s) /\
     isAncestor currentPart descParent s /\
     In descParent (getPartitions MALInternal.multiplexer s) /\
     (defaultPage =? pa entry) = false /\
     isPE pt (StateLib.getIndexOfAddr va fstLevel) s /\
     getTableAddrRoot pt PDidx descParent va s /\
     (defaultPage =? pt) = false /\
     entryPresentFlag pt (StateLib.getIndexOfAddr va fstLevel) true s /\
     entryUserFlag pt (StateLib.getIndexOfAddr va fstLevel) false s /\
     isEntryPage pt (StateLib.getIndexOfAddr va fstLevel) (pa entry) s /\
     multiplexer = MALInternal.multiplexer /\
     false = StateLib.Page.eqb descParent multiplexer /\
     nextEntryIsPP descParent sh2idx sh2 s /\
     Some L = StateLib.getNbLevel /\
     StateLib.getIndexOfAddr va fstLevel = lastIndex /\
     isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\
     getTableAddrRoot ptsh2 sh2idx descParent va s /\
     (defaultPage =? ptsh2) = false /\
     isVA' ptsh2 lastIndex vaInAncestor s /\
     nextEntryIsPP descParent PPRidx ancestor s /\
     nextEntryIsPP ancestor PDidx pdAncestor s /\
     defaultV = defaultVAddr /\
     false = StateLib.VAddr.eqbList defaultV vaInAncestor /\
     isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\
     getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s /\
     (defaultPage =? ptvaInAncestor) = false /\ StateLib.getIndexOfAddr vaInAncestor fstLevel = idxva -> 
accessibleVAIsNotPartitionDescriptor s' -> 
propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s' ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable
           phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
           descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA L l b1 b2 b3 true true true idxFstVA idxSndVA
           idxTrdVA zeroI minFI .
Proof.
intros.
intuition;subst.
unfold propagatedPropertiesPrepare, indirectionDescriptionAll, initPEntryTablePreconditionToPropagatePreparePropertiesAll in *.
intros.
assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartitions.
{ apply getPartitionsUpdateUserFlag; trivial. }
assert(getChildren currentPart s' = getChildren currentPart s) as Hchildren.
{ apply getChildrenUpdateFlagUser; trivial.
}
intuition;subst;trivial; unfold s'.
+ apply kernelDataIsolationUpdateUserFlagFalse;trivial.
+ apply partitionsIsolationUpdateUserFlag;trivial.
+ apply verticalSharingUpdateUserFlag;trivial.
+ apply consistencyUpdateWriteAccessibleRec with  (currentPartition s) descParent ancestor
      pdAncestor pt va sh2 (StateLib.getIndexOfAddr va fstLevel) ptsh2 vaInAncestor L defaultVAddr;intuition;subst;trivial.
  unfold writeAccessibleRecInternalPropertiesPrepare .
  intuition.  
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isPEUpdateUserFlag; assumption.
(* + apply isVAUserUpdateUserFlag;trivial. *)
+ assert(exists va : vaddr, isEntryVA ptSh1TrdVA (StateLib.getIndexOfAddr trdVA fstLevel) va s 
  /\ beqVAddr defaultVAddr va = true) as (vax & Hva & Hdef);trivial .
  exists vax.
  split; [ apply isEntryVAUpdateUserFlag | ];trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isVEUpdateUserFlag;assumption.
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply entryPresentFlagUpdateUserFlag;assumption.
+ apply entryUserFlagUpdateUserFlagRandomValue;trivial.
left.
apply childAncestorConfigTablesAreDifferent with s 
(currentPartition s) descParent ancestor trdVA vaInAncestor;trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isPEUpdateUserFlag; assumption.
+ assert(exists va : vaddr, isEntryVA ptSh1SndVA (StateLib.getIndexOfAddr sndVA fstLevel) va s 
  /\ beqVAddr defaultVAddr va = true) as (vax & Hva & Hdef);trivial .
  exists vax.
  split; [ apply isEntryVAUpdateUserFlag | ];trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isVEUpdateUserFlag;assumption.
+ assert(exists va : vaddr, isEntryVA ptSh1FstVA (StateLib.getIndexOfAddr fstVA fstLevel) va s 
  /\ beqVAddr defaultVAddr va = true) as (vax & Hva & Hdef);trivial .
  exists vax.
  split; [ apply isEntryVAUpdateUserFlag | ];trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isVEUpdateUserFlag;assumption.
(* + apply isVAUserUpdateUserFlag;trivial. *)
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply entryPresentFlagUpdateUserFlag;assumption.
+ apply entryUserFlagUpdateUserFlagRandomValue;trivial.
left.
apply childAncestorConfigTablesAreDifferent with s 
(currentPartition s) descParent ancestor sndVA vaInAncestor;trivial.
+ apply getTableAddrRootUpdateUserFlag;trivial.
+ apply isPEUpdateUserFlag; assumption.
(* + apply isVAUserUpdateUserFlag;trivial. *)
+ apply entryUserFlagUpdateUserFlagRandomValue;trivial.
  left.
  apply childAncestorConfigTablesAreDifferent with s 
  (currentPartition s) descParent ancestor fstVA vaInAncestor;trivial.
+ apply entryPresentFlagUpdateUserFlag;assumption.
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply isEntryPageUpdateUserFlag;trivial.
+ apply nextEntryIsPPUpdateUserFlag;trivial.
+ apply nextEntryIsPPUpdateUserFlag;trivial.
+ apply nextEntryIsPPUpdateUserFlag;trivial.
+ simpl. fold s'. rewrite Hpartitions;trivial.
+ unfold s' in *;simpl. rewrite Hchildren;trivial.
+ apply indirectionDescriptionUpdateUserFlag;trivial.
+ apply indirectionDescriptionUpdateUserFlag;trivial.
+ apply indirectionDescriptionUpdateUserFlag;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateUserFlag;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateUserFlag;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateUserFlag;trivial.
+ assert(Hconf: getConfigTablesLinkedList descChildphy (memory s) = Some LLroot) by trivial.
  rewrite <- Hconf.
  apply getConfigTablesLinkedListUpdateUserFlag;trivial.
+ fold s'. assert(Hconf: getLLPages LLroot s (nbPage + 1) = getLLPages LLroot s' (nbPage + 1)).
  symmetry.
  apply getConfigTablesLinkedListsUpdateUserFlag;trivial.
  rewrite <- Hconf;trivial.
+ fold s'. assert(Hconf: getLLPages LLroot s (nbPage + 1) = getLLPages LLroot s' (nbPage + 1)).
  symmetry.
  apply getConfigTablesLinkedListsUpdateUserFlag;trivial.
  rewrite <- Hconf;trivial.
+ assert(exists NbFI : index, isIndexValue newLastLLable (CIndex 1) NbFI s /\ NbFI >= minFI) as (x & Hx1 & Hx2) by trivial.
  exists x;split;trivial.
  apply isIndexValueUpdateUserFlag;trivial.
Qed.