(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2024)                *)
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
    This file contains required lemmas to prove that updating physical mapped 
    pages content do not modify partitions configuration tables  *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Internal.
Require Import Pip.Proof.DependentTypeLemmas Pip.Proof.Isolation Pip.Proof.InternalLemmas
               Pip.Proof.Consistency Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Invariants PropagatedProperties.
Require Import Coq.Logic.ProofIrrelevance Lia List Bool EqNat Compare_dec.
(*************************Move into InternalLemmas ************************)
Lemma indirectionDescriptionIsConfigPage descChildphy phyPDChild  vaToPrepare l s:
 indirectionDescription s descChildphy phyPDChild idxPageDir vaToPrepare l -> 
 partitionDescriptorEntry s -> 
In descChildphy (getPartitions pageRootPartition s) -> 
In phyPDChild (getConfigPages descChildphy s).
Proof.
intros Hind.
intros.
unfold indirectionDescription in *.
destruct Hind as (  tableroot & Hpp & Hnotnull & Hind).
destruct Hind as [(Heq & Hl) | (nbl & stop & Hnbl & Hstop & Hind & Hnotnul & Hl)].
subst.
unfold getConfigPages.
simpl. 
right.
apply inGetIndirectionsAuxInConfigPagesPD with phyPDChild;trivial.
assert(nbLevel > 0) by apply nbLevelNotZero.
destruct nbLevel. lia.
simpl.
left;trivial.
apply nextEntryIsPPgetPd;trivial.
unfold getConfigPages.
simpl;right. 
apply inGetIndirectionsAuxInConfigPagesPD with tableroot;trivial.
apply getIndirectionInGetIndirections with  vaToPrepare nbl stop;trivial.
apply nbLevelNotZero.
subst.
apply getNbLevelLe;trivial.
apply nextEntryIsPPgetPd;trivial.
Qed. 
(********************************************************)
Lemma readPhysicalUpdateMappedPageData partition table idxroot  s idx x :
(* lookup table idx (memory s) beqPage beqIndex = None ->  *)
table <> partition -> 
StateLib.readPhysical partition idxroot
  (add table idx x
     (memory s) pageEq idxEq) = StateLib.readPhysical partition idxroot (memory s).
Proof.
intros.
cbn.
unfold StateLib.readPhysical.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) pageEq idxEq); intros Hpairs.
apply beqPairsTrue in Hpairs.
destruct Hpairs as (Htable & Hidx);subst.
(* rewrite H. trivial. *) now contradict H. 
apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  partition idxroot   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma readVirtualUpdateMappedPageData partition table idxroot  s idx x :
(* lookup table idx (memory s) beqPage beqIndex = None ->  *)
table <> partition -> 
StateLib.readVirtual partition idxroot
  (add table idx x
     (memory s) pageEq idxEq) = StateLib.readVirtual partition idxroot (memory s).
Proof.
intros.
cbn.
unfold StateLib.readVirtual.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) pageEq idxEq); intros Hpairs.
apply beqPairsTrue in Hpairs.
destruct Hpairs as (Htable & Hidx);subst.
(* rewrite H. trivial. *) now contradict H. 
apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  partition idxroot   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma readVirEntryUpdateMappedPageData partition table idxroot  s idx x :
table <> partition -> 
StateLib.readVirEntry partition idxroot
  (add table idx x
     (memory s) pageEq idxEq) = StateLib.readVirEntry partition idxroot (memory s).
Proof.
intros.
cbn.
unfold StateLib.readVirEntry.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) pageEq idxEq); intros Hpairs.
apply beqPairsTrue in Hpairs.
destruct Hpairs as (Htable & Hidx);subst.
(* rewrite H. trivial. *) now contradict H. 
apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  partition idxroot   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma readIndexUpdateMappedPageData partition table idxroot  s idx x :
(* lookup table idx (memory s) beqPage beqIndex = None ->  *)
table <> partition -> 
StateLib.readIndex partition idxroot
  (add table idx x
     (memory s) pageEq idxEq) = StateLib.readIndex partition idxroot (memory s).
Proof.
intros.
cbn.
unfold StateLib.readIndex.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) pageEq idxEq); intros Hpairs.
apply beqPairsTrue in Hpairs.
destruct Hpairs as (Htable & Hidx);subst.
(* rewrite H. trivial. *) now contradict H. 
apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  partition idxroot   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma getPdUpdateMappedPageData partition table idx s x: 
table <> partition ->
StateLib.getPd partition
  (add table idx x
     (memory s) pageEq idxEq) = StateLib.getPd partition (memory s).
Proof.
cbn.
unfold StateLib.getPd.
case_eq (StateLib.Index.succ idxPageDir);trivial.
intros.
apply readPhysicalUpdateMappedPageData; trivial.
Qed. 

Lemma getFstShadowUpdateMappedPageData partition table idx s x: 
table <> partition ->
StateLib.getFstShadow partition
  (add table idx x
     (memory s) pageEq idxEq) = StateLib.getFstShadow partition (memory s).
Proof.
cbn.
unfold StateLib.getFstShadow.
case_eq (StateLib.Index.succ idxShadow1);trivial.
intros.
apply readPhysicalUpdateMappedPageData; trivial.
Qed. 

Lemma getSndShadowUpdateMappedPageData partition table idx s x: 
table <> partition ->
StateLib.getSndShadow partition
  (add table idx x
     (memory s) pageEq idxEq) = StateLib.getSndShadow partition (memory s).
Proof.
cbn.
unfold StateLib.getSndShadow.
case_eq (StateLib.Index.succ idxShadow2);trivial.
intros.
apply readPhysicalUpdateMappedPageData; trivial.
Qed.

Lemma getTrdShadowUpdateMappedPageData partition table idx s x: 
table <> partition ->
StateLib.getConfigTablesLinkedList partition
  (add table idx x
     (memory s) pageEq idxEq) = StateLib.getConfigTablesLinkedList partition (memory s).
Proof.
cbn.
unfold StateLib.getConfigTablesLinkedList.
case_eq (StateLib.Index.succ idxShadow3 );trivial.
intros.
apply readPhysicalUpdateMappedPageData; trivial.
Qed.

Lemma getParentUpdateMappedPageData partition table idx s x: 
table <> partition ->
StateLib.getParent partition
  (add table idx x
     (memory s) pageEq idxEq) = StateLib.getParent partition (memory s).
Proof.
cbn.
unfold StateLib.getParent.
case_eq (StateLib.Index.succ idxParentDesc);trivial.
intros.
apply readPhysicalUpdateMappedPageData; trivial.
Qed. 

Lemma getIndirectionUpdateMappedPageData tableRoot table idx  nbL
 (curlevel : level) va stop   x s: 

Some nbL = StateLib.getNbLevel ->
curlevel <= nbL -> 
 ~ In table (getIndirectionsAux tableRoot s (S stop)  ) -> 
 getIndirection tableRoot va curlevel stop
    {|
    currentPartition := currentPartition s;
    memory := add table idx
                x  (memory s) pageEq idxEq |} =  
 getIndirection tableRoot va curlevel stop s.
Proof.
intros Hlevel Hcurlevel Hii.
revert Hlevel Hcurlevel Hii.
revert tableRoot table idx x nbL curlevel va.
induction stop; simpl; intros.
+ f_equal.
+ case_eq (levelEq curlevel levelMin); intros;
  f_equal.  
  set (memory' := add table idx
       x (memory s) pageEq idxEq) in *.
  set(curidx := StateLib.getIndexOfAddr va curlevel) in *.
  assert (StateLib.readPhyEntry tableRoot curidx (memory s)
  = StateLib.readPhyEntry tableRoot curidx memory' ).
  { unfold memory'.
    clear memory'.
    unfold  StateLib.readPhyEntry.
    cbn. apply Classical_Prop.not_or_and in Hii.
    destruct Hii.
    assert (Hfalse : beqPairs (table, idx) (tableRoot, curidx) pageEq idxEq = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup tableRoot curidx (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq 
              = lookup tableRoot curidx (memory s) pageEq idxEq) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory. reflexivity. }
  rewrite <- H0.
  clear H0.
  case_eq (StateLib.readPhyEntry tableRoot curidx (memory s));
  intros; trivial.
  case_eq (Nat.eqb pageDefault p); intros; trivial.
  f_equal.
  case_eq (StateLib.Level.pred curlevel); intros; trivial.
  apply IHstop with nbL; trivial.
  unfold StateLib.Level.pred in H2.
  destruct ( gt_dec curlevel 0).
  inversion H2.
  simpl in *.
  destruct l.
  inversion H4.
  subst. lia.
  now contradict H2.
  simpl.
  apply Classical_Prop.not_or_and in Hii.
  destruct Hii.
  apply Classical_Prop.and_not_or.
  split.
  rewrite in_flat_map in H4.
  unfold not  in *.
  intros.
  contradict H4.
  exists p.
  split.
  apply readPhyEntryInGetTablePages with curidx; trivial.
  trivial.
  destruct curidx. simpl in *. 
  trivial.
  apply beq_nat_false in H1. 
  unfold not in *.
  intros.
  contradict H1.
  rewrite H4. reflexivity.
  assert (curidx = (CIndex curidx)) as Hcidx.
  symmetry. apply indexEqId. rewrite <- Hcidx. assumption.
  simpl. subst. left. trivial.
  rewrite in_flat_map in H4.
  unfold not  in *.
  intros.
  contradict H4.
  exists p.
  split. trivial.
  apply readPhyEntryInGetTablePages with curidx; trivial.
  trivial.
  destruct curidx. simpl in *. 
  trivial.
  apply beq_nat_false in H1. 
  unfold not in *.
  intros.
  contradict H1.
  rewrite H4. reflexivity.
  assert (curidx = (CIndex curidx)) as Hcidx.
  symmetry. apply indexEqId. rewrite <- Hcidx. assumption.
  simpl. subst. right. assumption.
Qed.

Lemma checkChildUpdateMappedPageData partition  s a table idx   x nbL: 
In partition (getPartitions pageRootPartition s) -> 
partitionDescriptorEntry s ->
~ In table (getConfigPages partition s) -> 
Some nbL = StateLib.getNbLevel -> 
 table<>partition ->
StateLib.checkChild partition nbL
   {|
    currentPartition := currentPartition s;
    memory := add table idx
                x (memory s) pageEq idxEq |} a =
StateLib.checkChild partition nbL s a.
Proof. 
unfold StateLib.checkChild.
intros.
set (s' :=  {|
    currentPartition := currentPartition s;
    memory := add table idx
                x (memory s) pageEq idxEq |}  ) in *.
assert( StateLib.getFstShadow partition (memory s')= StateLib.getFstShadow partition (memory s) ) as Hfstsh.
apply getFstShadowUpdateMappedPageData ;trivial.
rewrite Hfstsh. 
case_eq (StateLib.getFstShadow partition (memory s));trivial.
+ intros.
 assert (getIndirection p a nbL (nbLevel - 1)  s' = getIndirection p a nbL (nbLevel - 1)  s) as Hind.
  { apply getIndirectionUpdateMappedPageData with nbL ;trivial.
    assert(0 < nbLevel) by apply nbLevelNotZero.
    replace (S (nbLevel - 1)) with nbLevel by lia.
    apply notConfigTableNotSh1configTable with partition; trivial.
    unfold getConfigPages in *.
    simpl in *.
    apply Classical_Prop.not_or_and in H1.
    destruct H1.
    assumption. }
  rewrite Hind.
 case_eq (getIndirection p a nbL (nbLevel - 1) s); intros.
 case_eq(Nat.eqb p0 pageDefault); intros; trivial.
  assert (StateLib.readPDflag p0 (StateLib.getIndexOfAddr a levelMin) (memory s') = 
  StateLib.readPDflag p0 (StateLib.getIndexOfAddr a levelMin) (memory s)) as Hpdflag.
  unfold StateLib.readPDflag.
  unfold s'.
  cbn.
  assert (table <> p0).
  assert (In p0 (getIndirections p s)).
  apply getIndirectionInGetIndirections with a nbL (nbLevel - 1); trivial.
  assert (0 < nbLevel) by apply nbLevelNotZero.
  lia.
  apply beq_nat_false in H6.
  unfold not; intros;subst.
  now contradict H6.
  apply getNbLevelEq in H2.
  rewrite H2.
  lia.
  unfold partitionDescriptorEntry in *.
  apply H0  with partition idxShadow1 in H; clear H0.
  destruct H as (_ & _ & entrypd & Hpp & Hnotnul).
  apply nextEntryIsPPgetFstShadow in Hpp.
  rewrite Hpp in H4.
  inversion H4.
  subst.
  unfold not; intros; subst; now contradict Hnotnul.
  right; left; trivial.
  unfold getIndirections in H7.
  unfold not; intros; subst.
  assert(~ In p0 (getIndirectionsAux p s nbLevel)).
  apply notConfigTableNotSh1configTable with partition; trivial.
  unfold getConfigPages in *.
  simpl in *.
  apply Classical_Prop.not_or_and in H1.
  destruct H1.
  assumption.
  now contradict H8.
  assert (Hfalse : beqPairs (table, idx) (p0, StateLib.getIndexOfAddr a levelMin) 
          pageEq idxEq = false).
  apply beqPairsFalse.
  left. assumption.
  rewrite Hfalse.
  assert(Hmemory :  lookup p0 (StateLib.getIndexOfAddr a levelMin) (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq
  =  lookup p0 (StateLib.getIndexOfAddr a levelMin)(memory s) pageEq idxEq).
  apply removeDupIdentity; trivial.
  left; unfold not; intros ; subst; now contradict H7.
  rewrite Hmemory.
  reflexivity.
  rewrite Hpdflag. reflexivity. trivial.
Qed.

Lemma getPdsVAddrUpdateMappedPageData partition table idx nbL x s: 
In partition (getPartitions pageRootPartition s) -> 
partitionDescriptorEntry s ->
~ In table (getConfigPages partition s) -> 
Some nbL = StateLib.getNbLevel -> 
 table<>partition ->
getPdsVAddr partition nbL getAllVAddrWithOffset0
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              x(memory s) pageEq
              idxEq |} =
getPdsVAddr partition nbL getAllVAddrWithOffset0 s.
Proof.
unfold getPdsVAddr.
revert partition nbL.
induction getAllVAddrWithOffset0; simpl;trivial.
intros. 
assert(checkChild partition nbL
    {|
    currentPartition := currentPartition s;
    memory := add table idx x
                (memory s) pageEq idxEq |} a  =   checkChild partition nbL s a).
apply checkChildUpdateMappedPageData;trivial.
rewrite H4. 
case_eq (checkChild partition nbL s a); intros.
f_equal.
apply IHl; trivial.
apply IHl; trivial.
Qed.

Lemma getMappedPagesAuxUpdateMappedPageData pd table idx listVA  s nbL x :
table <> pageDefault -> pd <> pageDefault ->
~ In table (getIndirectionsAux pd s nbLevel) ->
Some nbL = StateLib.getNbLevel -> 
getMappedPagesAux pd listVA
  {|
  currentPartition := currentPartition s;
  memory := add table idx x (memory s) pageEq idxEq |} =
getMappedPagesAux pd listVA s.
Proof.
intros Htablenotnull Hpdnotnull Hindirections HnbL.
unfold getMappedPagesAux.
f_equal.
unfold getMappedPagesOption.
revert pd Hindirections Htablenotnull Hpdnotnull.
induction listVA;simpl;intros;trivial.
rewrite IHlistVA; trivial.
f_equal.
unfold getMappedPage.
rewrite <- HnbL.
assert(Hind : getIndirection pd a nbL (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx
                x
                (memory s) pageEq idxEq |} = getIndirection pd a nbL (nbLevel - 1) s).
apply getIndirectionUpdateMappedPageData with nbL; auto.
assert(0<nbLevel) by apply nbLevelNotZero.
assert( (S (nbLevel - 1)) = nbLevel) by lia.
rewrite H0.
assumption.
subst.
rewrite Hind.
case_eq (getIndirection pd a nbL (nbLevel - 1) s); intros; trivial.
cbn.            
set(curidx := (StateLib.getIndexOfAddr a levelMin)) in *.
assert(p <> table).
clear IHlistVA.
unfold not in *.
intros.
subst.
apply Hindirections.
apply getIndirectionInGetIndirections with a nbL (nbLevel -1); trivial.
apply nbLevelNotZero.
apply getNbLevelLe; trivial.
assert(Hpres : StateLib.readPresent p curidx
    (add table idx x (memory s) pageEq idxEq) = 
 StateLib.readPresent p curidx (memory s)).
 unfold StateLib.readPresent.
 cbn.
 assert (Hfalse : beqPairs (table, idx) (p, curidx) pageEq idxEq = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup p curidx (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq 
              = lookup p curidx (memory s) pageEq idxEq) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory; reflexivity.
 rewrite Hpres; trivial.
 case_eq (StateLib.readPresent p curidx (memory s)); intros; trivial.
 case_eq b; intros; trivial.
 unfold StateLib.readPhyEntry.
 cbn.
 assert (Hfalse : beqPairs (table, idx) (p, curidx) pageEq idxEq = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup p curidx (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq 
              = lookup p curidx (memory s) pageEq idxEq) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory; reflexivity.
Qed.

Lemma getMappedPagesUpdateMappedPageData partition (table : page) idx level x s: 
partitionDescriptorEntry s -> 
(Nat.eqb pageDefault table) = false -> 
Some level = StateLib.getNbLevel-> 
 In partition (getPartitions pageRootPartition s) -> 
(forall partition1 : page,
         In partition1 (getPartitions pageRootPartition s) ->
         partition1 = table \/ 
         In table (getConfigPagesAux partition1 s) -> False) -> 
getMappedPages partition
  {|
  currentPartition := currentPartition s; 
  memory := add table idx x (memory s) pageEq idxEq |} =
getMappedPages partition s. 
Proof.
intros Hpde Hfalse Hlevel Hpartmult Hconfig. 
set(s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx x (memory s) pageEq idxEq |}) in *.
unfold getMappedPages.
assert(Hpd : StateLib.getPd partition (memory s') =
              StateLib.getPd partition (memory s)).
  { apply getPdUpdateMappedPageData.
    generalize (Hconfig partition Hpartmult); clear Hconfig; intros Hconfig.
    unfold not.
    intros. apply Hconfig.
    subst.
    left; trivial. }
rewrite Hpd.
destruct (StateLib.getPd partition (memory s)); trivial.
assert(Hpdchild1 : StateLib.getPd partition (memory s') =
              StateLib.getPd partition (memory s)).
{ apply getPdUpdateMappedPageData.
  generalize (Hconfig partition Hpartmult); clear Hconfig; intros Hconfig.
  unfold not.
  intros. apply Hconfig.
  subst.
  left; trivial. }
apply getMappedPagesAuxUpdateMappedPageData with level; trivial.
{ 
 apply beq_nat_false in Hfalse.
 unfold not; intros.
 apply Hfalse.
 subst;trivial. }
{ unfold consistency in *.
 unfold partitionDescriptorEntry in Hpde.
  apply Hpde  with partition idxPageDir in Hpartmult; clear Hpde.
  destruct Hpartmult as (_ & _ & entrypd & Hpp & Hnotnul).
  rewrite Hpdchild1 in Hpd.
  clear Hpdchild1.
  assert (Heq : entrypd = p).
  apply getPdNextEntryIsPPEq with partition s; trivial.
  rewrite <- Heq; assumption.
 left; trivial. }
{ generalize (Hconfig partition Hpartmult); clear Hconfig; intros Hconfig.
      apply Classical_Prop.not_or_and in Hconfig.
      destruct Hconfig as (Hi1 & Hi2).
      apply notConfigTableNotPdconfigTable with partition; trivial.
      unfold consistency in *; intuition.
      rewrite <- Hpdchild1; trivial. }
Qed.

Lemma getAccessibleMappedPageUpdateMappedPageData  pd table idx s (* nbL *) x va:
table <> pageDefault -> pd <> pageDefault ->
~ In table (getIndirectionsAux pd s nbLevel) ->
(* Some nbL = StateLib.getNbLevel ->  *)
getAccessibleMappedPage pd
  {| currentPartition := currentPartition s; memory := add table idx x (memory s) pageEq idxEq |} va =
getAccessibleMappedPage pd s va.
Proof.
intros Htablenotnull Hpdnotnull Hindirections (* HnbL *).
unfold getAccessibleMappedPage.
case_eq(StateLib.getNbLevel);[intros nbL HnbL| intros; trivial].
assert(Hind : getIndirection pd va nbL (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx x
                (memory s) pageEq idxEq |} = getIndirection pd va nbL (nbLevel - 1) s).
apply getIndirectionUpdateMappedPageData with nbL; auto.
assert(0<nbLevel) by apply nbLevelNotZero.
assert( (S (nbLevel - 1)) = nbLevel) by lia.
rewrite H0.
assumption.
subst.
rewrite Hind.
case_eq (getIndirection pd va nbL (nbLevel - 1) s); intros; trivial.
cbn.            
set(curidx := (StateLib.getIndexOfAddr va levelMin)) in *.
assert(p <> table).
unfold not in *.
intros.
subst.
apply Hindirections.
apply getIndirectionInGetIndirections with va nbL (nbLevel -1); trivial.
apply nbLevelNotZero.
apply getNbLevelLe; trivial.
symmetry;trivial.
assert(Hpres : StateLib.readPresent p curidx
    (add table idx x (memory s) pageEq idxEq) = 
 StateLib.readPresent p curidx (memory s)).
 unfold StateLib.readPresent.
 cbn.
 assert (Hfalse : beqPairs (table, idx) (p, curidx) pageEq idxEq = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup p curidx (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq 
              = lookup p curidx (memory s) pageEq idxEq) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory; reflexivity.
 rewrite Hpres; trivial.
 case_eq (StateLib.readPresent p curidx (memory s)); intros; trivial.
 case_eq b; intros; trivial.
assert(Haccess : StateLib.readAccessible p curidx
    (add table idx
       x (memory s) pageEq idxEq) = 
 StateLib.readAccessible p curidx (memory s)).
 unfold StateLib.readAccessible.
 cbn.
 assert (Hfalse : beqPairs (table, idx) (p, curidx) pageEq idxEq = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup p curidx (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq 
              = lookup p curidx (memory s) pageEq idxEq) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory; reflexivity.
 rewrite Haccess; trivial.
 case_eq (StateLib.readAccessible p curidx (memory s)); intros; trivial.
 case_eq b0; intros; trivial. 
 
 unfold StateLib.readPhyEntry.
 cbn.
 assert (Hfalse : beqPairs (table, idx) (p, curidx) pageEq idxEq = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup p curidx (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq 
              = lookup p curidx (memory s) pageEq idxEq) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory; reflexivity.
Qed.
      
Lemma getMappedPageUpdateMappedPageData  pd table idx s (* nbL *) x va:
table <> pageDefault -> pd <> pageDefault ->
~ In table (getIndirectionsAux pd s nbLevel) ->
(* Some nbL = StateLib.getNbLevel ->  *)
getMappedPage pd
  {| currentPartition := currentPartition s; memory := add table idx x (memory s) pageEq idxEq |} va =
getMappedPage pd s va.
Proof.
intros Htablenotnull Hpdnotnull Hindirections (* HnbL *).
unfold getMappedPage.
case_eq(StateLib.getNbLevel);[intros nbL HnbL| intros; trivial].
assert(Hind : getIndirection pd va nbL (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx x
                (memory s) pageEq idxEq |} = getIndirection pd va nbL (nbLevel - 1) s).
apply getIndirectionUpdateMappedPageData with nbL; auto.
assert(0<nbLevel) by apply nbLevelNotZero.
assert( (S (nbLevel - 1)) = nbLevel) by lia.
rewrite H0.
assumption.
subst.
rewrite Hind.
case_eq (getIndirection pd va nbL (nbLevel - 1) s); intros; trivial.
cbn.            
set(curidx := (StateLib.getIndexOfAddr va levelMin)) in *.
assert(p <> table).
unfold not in *.
intros.
subst.
apply Hindirections.
apply getIndirectionInGetIndirections with va nbL (nbLevel -1); trivial.
apply nbLevelNotZero.
apply getNbLevelLe; trivial.
symmetry;trivial.
assert(Hpres : StateLib.readPresent p curidx
    (add table idx x (memory s) pageEq idxEq) = 
 StateLib.readPresent p curidx (memory s)).
 unfold StateLib.readPresent.
 cbn.
 assert (Hfalse : beqPairs (table, idx) (p, curidx) pageEq idxEq = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup p curidx (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq 
              = lookup p curidx (memory s) pageEq idxEq) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory; reflexivity.
 rewrite Hpres; trivial.
 case_eq (StateLib.readPresent p curidx (memory s)); intros; trivial.
 case_eq b; intros; trivial.
 unfold StateLib.readPhyEntry.
 cbn.
 assert (Hfalse : beqPairs (table, idx) (p, curidx) pageEq idxEq = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup p curidx (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq 
              = lookup p curidx (memory s) pageEq idxEq) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory; reflexivity.
Qed.
         
Lemma getAccessibleMappedPagesAuxUpdateMappedPageData pd table idx listVA s (* nbL *) x :
table <> pageDefault -> pd <> pageDefault ->
~ In table (getIndirectionsAux pd s nbLevel) ->
(* Some nbL = StateLib.getNbLevel ->  *)
getAccessibleMappedPagesAux pd listVA
  {|
  currentPartition := currentPartition s;
  memory := add table idx x (memory s) pageEq
              idxEq |} =
getAccessibleMappedPagesAux pd listVA s.
Proof.
intros Htablenotnull Hpdnotnull Hindirections (* HnbL *).
unfold getAccessibleMappedPagesAux.
f_equal.
unfold getAccessibleMappedPagesOption.
revert pd Hindirections Htablenotnull Hpdnotnull.
induction listVA;simpl;intros;trivial.
rewrite IHlistVA; trivial.
f_equal.
apply getAccessibleMappedPageUpdateMappedPageData; trivial.
Qed.

Lemma getAccessibleMappedPagesUpdateMappedPageData partition (table : page) 
idx x (* level *)  s: 
partitionDescriptorEntry s -> 
(Nat.eqb pageDefault table) = false -> 
(* Some level = StateLib.getNbLevel->  *)
 In partition (getPartitions pageRootPartition s) -> 
(forall partition1 : page,
         In partition1 (getPartitions pageRootPartition s) ->
         partition1 = table \/ 
         In table (getConfigPagesAux partition1 s) -> False) -> 
getAccessibleMappedPages partition
  {|
  currentPartition := currentPartition s; 
  memory := add table idx
              x (memory s) pageEq idxEq |} =
getAccessibleMappedPages partition s. 
Proof.
intros Hpde Hfalse (* Hlevel *) Hpartmult Hconfig. 
set(s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx
              x
              (memory s) pageEq idxEq |}) in *.
unfold getAccessibleMappedPages.
 assert(Hpd : StateLib.getPd partition (memory s') =
              StateLib.getPd partition (memory s)).
  { apply getPdUpdateMappedPageData.

    generalize (Hconfig partition Hpartmult); clear Hconfig; intros Hconfig.
    unfold not.
    intros. apply Hconfig.
    subst.
    left; trivial. }
rewrite Hpd.
destruct (StateLib.getPd partition (memory s)); trivial.
assert(Hpdchild1 : StateLib.getPd partition (memory s') =
              StateLib.getPd partition (memory s)).
{ apply getPdUpdateMappedPageData.

  generalize (Hconfig partition Hpartmult); clear Hconfig; intros Hconfig.
  unfold not.
  intros. apply Hconfig.
  subst.
  left; trivial. }
apply getAccessibleMappedPagesAuxUpdateMappedPageData ; trivial.
{ 
 apply beq_nat_false in Hfalse.
 unfold not; intros.
 apply Hfalse.
 subst;trivial. }
{ unfold consistency in *.
 unfold partitionDescriptorEntry in Hpde.
  apply Hpde  with partition idxPageDir in Hpartmult; clear Hpde.
  destruct Hpartmult as (_ & _ & entrypd & Hpp & Hnotnul).
  rewrite Hpdchild1 in Hpd.
  clear Hpdchild1.
  assert (Heq : entrypd = p).
  apply getPdNextEntryIsPPEq with partition s; trivial.
  rewrite <- Heq; assumption.
 left; trivial. }
{ generalize (Hconfig partition Hpartmult); clear Hconfig; intros Hconfig.
      apply Classical_Prop.not_or_and in Hconfig.
      destruct Hconfig as (Hi1 & Hi2).
      apply notConfigTableNotPdconfigTable with partition; trivial.
      unfold consistency in *; intuition.
      rewrite <- Hpdchild1; trivial. }
Qed.

Lemma getChildrenUpdateMappedPageData partition table idx s x (* nbL *) (* pd *) :
table <> pageDefault -> 
(* pd <> defaultPage ->  *)
(* Some pd = StateLib.getPd partition (memory s) ->  *)
In partition (getPartitions pageRootPartition s) -> 
partitionDescriptorEntry s ->
~ In table (getConfigPages partition s) -> 
(* Some nbL = StateLib.getNbLevel ->  *)
 table<>partition ->
getChildren partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              x 
              (memory s) pageEq idxEq |} = getChildren partition s.
Proof.
intros  Htablenotnull Hgetparts Hpde (* Hpdnotnull HgetPd *) Hind (* HnbLevel *) Hdiff.
unfold getChildren.
case_eq (StateLib.getNbLevel);intros; trivial.
assert ( StateLib.getPd partition
    (memory
       {|
       currentPartition := currentPartition s;
       memory := add table idx
                   x
                   (memory s) pageEq idxEq |}) = StateLib.getPd partition (memory s)) as Hpd.
apply getPdUpdateMappedPageData; trivial.
rewrite Hpd; clear Hpd.
f_equal.
case_eq (StateLib.getPd partition (memory s));intros; trivial.
assert(getPdsVAddr partition l getAllVAddrWithOffset0
     {|
     currentPartition := currentPartition s;
     memory := add table idx
                 x
                 (memory s) pageEq idxEq |} = getPdsVAddr partition l getAllVAddrWithOffset0 s) as Hvaddrpd.
apply getPdsVAddrUpdateMappedPageData; trivial.
symmetry; assumption.
rewrite Hvaddrpd; clear Hvaddrpd.
apply getMappedPagesAuxUpdateMappedPageData with l; trivial.
unfold partitionDescriptorEntry in *.
apply Hpde with partition idxPageDir in Hgetparts;clear Hpde.
destruct Hgetparts as (Hpdidx & Hisva & Hpd  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ idxPageDir); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq);auto.
destruct v; auto.
inversion H0.
subst; assumption.
left;trivial.
unfold getConfigPages in *.
simpl in *.
apply Classical_Prop.not_or_and in Hind.
destruct Hind.
apply notConfigTableNotPdconfigTable with partition; trivial.
auto.
Qed.

Lemma getPartitionAuxUpdateMappedPageData s table idx x : 
noDupPartitionTree s -> 
forall partition, 
In partition (getPartitions pageRootPartition s) ->
(forall subpartition, In subpartition  (getPartitions pageRootPartition s ) ->
~ In table (getConfigPages subpartition s)) -> 
table <> pageDefault ->
partitionDescriptorEntry s ->
getPartitionAux partition {|
  currentPartition := currentPartition s;
  memory := add table idx
              x
              (memory s) pageEq idxEq |} (nbPage+1) =
getPartitionAux partition s (nbPage+1).
Proof.
intros Hnoduptree. 
intros partition HgetParts Hnotconfig Htablenotnull Hpde.
revert partition HgetParts Hnotconfig .
induction (nbPage + 1).
simpl; intuition.
simpl; intros.
f_equal.
set(s':=  {|
     currentPartition := currentPartition s;
     memory := add table idx
                 x
                 (memory s) pageEq idxEq |}) in *.
                 unfold s'.
rewrite getChildrenUpdateMappedPageData; auto.
fold s'.
+ assert(forall child, In child (getChildren partition s) -> 
                       In child (getPartitions  pageRootPartition s)).
  intros.
  apply childrenPartitionInPartitionList with partition; trivial.
  induction ((getChildren partition s)); simpl; trivial.
  rewrite IHn; trivial.
  - f_equal. apply IHl.
    intros. apply H. simpl. right;trivial.
  - clear IHl.
  apply H. simpl. left;trivial.
+ generalize (Hnotconfig partition ); clear Hnotconfig; intros Hnotconfig.
  apply Hnotconfig; trivial.
+ generalize (Hnotconfig partition ); clear Hnotconfig; intros Hnotconfig.
  assert (In partition (getPartitions partition s)).
  unfold getPartitions.
  destruct nbPage;
  simpl; left;trivial.
  apply Hnotconfig in HgetParts.
  apply Classical_Prop.not_or_and in HgetParts.
  intuition.
Qed.

Lemma getPartitionsUpdateMappedPageData partition table idx s x:
noDupPartitionTree s -> 
In partition (getPartitions pageRootPartition s) ->
(forall subpartition, In subpartition  (getPartitions pageRootPartition s ) ->
~ In table (getConfigPages subpartition s)) -> 
table <> pageDefault ->
partitionDescriptorEntry s ->
getPartitions partition
  {| currentPartition := currentPartition s;
     memory := add table idx x (memory s) pageEq idxEq |} = 
getPartitions partition s.
Proof.
intros.
unfold getPartitions.
apply getPartitionAuxUpdateMappedPageData; trivial.
Qed.

Lemma getTablePagesUpdateMappedPageData table1 table2 idx x size s: 
table2 <> table1 -> 
getTablePages table1 size
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx
              x (memory s) pageEq idxEq |} =
getTablePages table1 size s.
Proof.
intros Htables.
revert idx.
induction size;
intros;  trivial.
simpl.
set (s':= {|
      currentPartition := currentPartition s;
      memory := add table2 idx
                  x (memory s) pageEq idxEq |}) in *.
assert (Hfalse : beqPairs (table2, idx) (table1, CIndex size) pageEq idxEq = false).
apply beqPairsFalse; left;trivial.
rewrite Hfalse.
  assert (lookup table1 (CIndex size) (removeDup table2 idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  table1 (CIndex size) (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. subst.  intuition. }
  rewrite  Hmemory; clear Hmemory.
  destruct (lookup table1 (CIndex size) (memory s) pageEq idxEq); [
  destruct v | 
  apply IHsize] ; try apply IHsize.
  destruct (Nat.eqb (pa p) pageDefault);
  [apply IHsize |
  f_equal;
  apply IHsize].
Qed.

Lemma getIndirectionsAuxUpdateMappedPageData partition table idx x s nbL:
~ In table (getIndirectionsAux partition s nbL) -> 
getIndirectionsAux partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              x
              (memory s) pageEq idxEq |} nbL = getIndirectionsAux partition s nbL.
Proof. 
intros Hind.
revert table partition Hind.
induction nbL; [
simpl; trivial |].
intros.
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx
       x (memory s) pageEq idxEq |}) in *.
simpl.
f_equal.
assert (getTablePages partition tableSize s' = 
        getTablePages partition tableSize s) as Htablepages. 
{ unfold s'; apply getTablePagesUpdateMappedPageData ;trivial. 
  simpl in Hind.
  apply Classical_Prop.not_or_and in Hind.
  destruct Hind.
  unfold not in *.
  intros.
  subst.
  now contradict H. }
rewrite Htablepages.
clear Htablepages.
simpl in Hind.
induction (getTablePages partition tableSize s); intros; trivial.
simpl in *.
apply Classical_Prop.not_or_and in Hind.
destruct Hind as (Hpart & Hind).
rewrite in_app_iff in Hind.
apply Classical_Prop.not_or_and in Hind.
destruct Hind as (Haux & Hflat).
rewrite IHl.
+ f_equal; apply IHnbL; trivial.
+ apply Classical_Prop.and_not_or.
  split; trivial.
Qed.

Lemma getLLPagesUpdateMappedPageData sh3 table idx x s :
~ In table (getLLPages sh3 s (nbPage+1)) -> 
getLLPages sh3
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              x (memory s) pageEq idxEq |} (nbPage+1) = 
getLLPages sh3 s (nbPage+1).
Proof. 
revert sh3.
induction (nbPage+1);trivial.
intros. simpl in *.
 set (s' :=    {|
        currentPartition := currentPartition s;
        memory := add table idx
                    x (memory s) pageEq idxEq |}) in *.
destruct (StateLib.getMaxIndex);trivial.
assert(sh3 <> table).
{ case_eq ( StateLib.readPhysical sh3 i (memory s)); intros;
  rewrite H0 in H ; [
  case_eq (Nat.eqb p pageDefault); intros; rewrite H1 in H |];
   apply Classical_Prop.not_or_and in H;
destruct H as (H & _); assumption. }
assert(Hread :   StateLib.readPhysical sh3 i
    (add table idx
       x
       (memory s) pageEq idxEq) = StateLib.readPhysical sh3 i (memory s)).
{ unfold StateLib.readPhysical.
  cbn.
  assert (Hfalse : beqPairs (table, idx) (sh3, i) pageEq idxEq = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup sh3 i (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq 
              = lookup sh3 i (memory s) pageEq idxEq) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory. reflexivity. }  
rewrite Hread.
case_eq ( StateLib.readPhysical sh3 i (memory s) ); intros; trivial.
case_eq (Nat.eqb p pageDefault); intros; trivial.
f_equal.
apply IHn.
rewrite H1 in H; trivial.
rewrite H2 in H.
simpl in H.  
apply Classical_Prop.not_or_and in H.
destruct H as (H & Hneed); assumption.
Qed.

Lemma getConfigPagesUpdateMappedPageData partition table idx x s : 
~ In table (getConfigPages partition s) -> 
getConfigPages partition
{| currentPartition := currentPartition s;
   memory := Lib.add  table idx x
            (memory s) pageEq idxEq |} = getConfigPages partition s.
Proof.
intros Ha.
unfold getConfigPages in *.
f_equal.
simpl in *.
 apply Classical_Prop.not_or_and in Ha.
 destruct Ha as (Hpart & Hconfig).
 assert (table <> partition) by intuition.
 clear Hpart. 
 rename  H into Hpart.
unfold getConfigPagesAux in *.
cbn.
rewrite getPdUpdateMappedPageData; trivial.
case_eq (StateLib.getPd partition (memory s)); trivial.
rewrite getFstShadowUpdateMappedPageData in *;trivial.
case_eq (StateLib.getFstShadow partition (memory s)); trivial.
rewrite getSndShadowUpdateMappedPageData in *;trivial.
case_eq (StateLib.getSndShadow partition (memory s)); trivial.
rewrite getTrdShadowUpdateMappedPageData in *;trivial.
case_eq (StateLib.getConfigTablesLinkedList partition (memory s)); trivial.
f_equal.
unfold getIndirections.
intros sh3 Hsh3 sh2 Hsh2 sh1 Hsh1 pd Hpd.
rewrite Hpd in *.
rewrite Hsh1 in *.
rewrite Hsh2 in *.
rewrite Hsh3 in *.
try repeat rewrite in_app_iff in Hconfig.
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig; simpl in H.
apply Classical_Prop.not_or_and in H0;
destruct H0.
apply Classical_Prop.not_or_and in H1;
destruct H1.
 unfold getIndirections in *. 
try repeat rewrite getIndirectionsAuxUpdateMappedPageData; f_equal; trivial.
do 2 f_equal.
apply getLLPagesUpdateMappedPageData; trivial.
Qed.
Lemma getConfigPagesAuxUpdateMappedPageData partition table idx x s : 
~ In table (getConfigPages partition s) -> 
getConfigPagesAux partition
{| currentPartition := currentPartition s;
   memory := Lib.add  table idx
            x
            (memory s) pageEq idxEq |} = getConfigPagesAux partition s.
Proof.
intros.
assert(getConfigPages partition {| currentPartition := currentPartition s;
   memory := Lib.add  table idx
           x
            (memory s) pageEq idxEq |} = getConfigPages partition s).
            apply getConfigPagesUpdateMappedPageData; trivial.
unfold getConfigPages in H0.
inversion H0. reflexivity.
Qed.

Lemma isVAUpdateMappedPageData partition table idxroot idx x s: 
(forall partition : page,
          In partition (getPartitions pageRootPartition s) ->
          partition = table \/ In table (getConfigPagesAux partition s) ->
          False )->
(Nat.eqb pageDefault table) = false ->
In partition (getPartitions pageRootPartition s) ->
isVA partition idxroot s -> 
isVA partition idxroot
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              x
              (memory s) pageEq idxEq |}.
Proof.
intros Hconfig Hfalse Hpde Hva.
unfold isVA in *.
cbn.
assert (Hnoteq : beqPairs (table, idx) (partition, idxroot) pageEq idxEq = false).
{ apply beqPairsFalse; intuition.
  left.
  generalize (Hconfig partition Hpde); clear Hconfig; intros Hconfig.
  apply Classical_Prop.not_or_and in Hconfig.
  destruct Hconfig.
  unfold not in *.
  intros Hf. rewrite Hf in H.
  now contradict H. }
rewrite Hnoteq.
assert ( lookup partition idxroot (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq 
              = lookup partition idxroot (memory s) pageEq idxEq) as Hmemory.
{ apply removeDupIdentity. left. 
  generalize (Hconfig partition Hpde); clear Hconfig; intros Hconfig.
  apply Classical_Prop.not_or_and in Hconfig.
  destruct Hconfig. assumption. }
rewrite  Hmemory; clear Hmemory. assumption.
Qed.

Lemma nextEntryIsPPUpdateMappedPageData partition table idxroot root idx x s: 
(forall partition : page,
          In partition (getPartitions pageRootPartition s) ->
          partition = table \/ In table (getConfigPagesAux partition s) ->
          False )->
(Nat.eqb pageDefault table) = false ->
In partition (getPartitions pageRootPartition s) ->
nextEntryIsPP partition idxroot root s <-> 
nextEntryIsPP partition idxroot root
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              x
              (memory s) pageEq idxEq |}.
Proof.
intros Hconfig Hfalse Hpde .
split.
+ unfold nextEntryIsPP in *.
  destruct (StateLib.Index.succ idxroot); trivial.
  cbn.
  assert (Hnoteq : beqPairs (table, idx) (partition, i) pageEq idxEq = false).
  { apply beqPairsFalse; intuition.
    left.
    generalize (Hconfig partition Hpde); clear Hconfig; intros Hconfig.
    apply Classical_Prop.not_or_and in Hconfig.
    destruct Hconfig.
    unfold not in *.
    intros Hf. rewrite Hf in H.
    now contradict H. }
  rewrite Hnoteq.
  assert ( lookup partition i (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq 
                = lookup partition i (memory s) pageEq idxEq) as Hmemory.
  { apply removeDupIdentity. left. 
    generalize (Hconfig partition Hpde); clear Hconfig; intros Hconfig.
    apply Classical_Prop.not_or_and in Hconfig.
    destruct Hconfig. assumption. }
  rewrite  Hmemory; clear Hmemory. trivial.
+ unfold nextEntryIsPP in *.
  destruct (StateLib.Index.succ idxroot); trivial.
  cbn in *.
  assert (Hnoteq : beqPairs (table, idx) (partition, i) pageEq idxEq = false).
  { apply beqPairsFalse; intuition.
    left.
    generalize (Hconfig partition Hpde); clear Hconfig; intros Hconfig.
    apply Classical_Prop.not_or_and in Hconfig.
    destruct Hconfig.
    unfold not in *.
    intros Hf. rewrite Hf in H.
    now contradict H. }
  rewrite Hnoteq .
  assert ( lookup partition i (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq 
                = lookup partition i (memory s) pageEq idxEq) as Hmemory.
  { apply removeDupIdentity. left. 
    generalize (Hconfig partition Hpde); clear Hconfig; intros Hconfig.
    apply Classical_Prop.not_or_and in Hconfig.
    destruct Hconfig. assumption. }
  rewrite  Hmemory in *; clear Hmemory. trivial.
Qed.

Lemma partitionDescriptorEntryUpdateMappedPageData (table : page) idx x s: 
consistency s -> 
initPEntryTablePreconditionToPropagatePrepareProperties s table ->
partitionDescriptorEntry
  {|
  currentPartition := currentPartition s;
  memory := add table idx
             x (memory s) pageEq idxEq |}.
Proof.
intros Hcons (Hconfig & Hfalse).
unfold consistency in *.
intuition.
assert(Hnoduptree: noDupPartitionTree s) by trivial.
assert(Hpde: partitionDescriptorEntry s) by trivial.
set (s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx
              x (memory s) pageEq idxEq |}) in *.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
 { unfold s'.
   apply getPartitionsUpdateMappedPageData ; trivial.
   + unfold getPartitions.
     destruct nbPage;simpl;left;trivial.
   + apply beq_nat_false in Hfalse.
     unfold not in *; intros.
     apply Hfalse.
     subst;trivial. }
unfold partitionDescriptorEntry in *.
intros.
rewrite Hpartions in *.
generalize (Hpde partition H23 idxroot  H25);
clear Hpde; intros Hpde.
destruct Hpde as (Hi1 & Hi2 &  root & Hpp & Hnotnull).
split; trivial.
split; clear H0.
unfold s'.
apply isVAUpdateMappedPageData; trivial.
exists root.
split; trivial.
unfold s'.
apply nextEntryIsPPUpdateMappedPageData; trivial.
Qed.

Lemma isPEUpdateUpdateMappedPageData table1 table2 idx1 idx2 x s :
table2 <> table1 -> 
isPE table1 idx1 s -> 
isPE table1 idx1
{|
currentPartition := currentPartition s;
memory := add table2 idx2
         x
          (memory s) pageEq idxEq |}.
Proof.
intros.
unfold isPE in *.
cbn.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) pageEq idxEq = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq)
          pageEq idxEq = lookup  table1 idx1 (memory s) pageEq idxEq) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. assumption.
Qed.

Lemma isVEUpdateMappedPageData table1 table2 idx1 idx2 x s :
table2 <> table1 -> 
isVE table1 idx1 s -> 
isVE table1 idx1
{|
currentPartition := currentPartition s;
memory := add table2 idx2
          x
          (memory s) pageEq idxEq |}.
Proof.
intros.
unfold isVE in *.
cbn.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) pageEq idxEq = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq)
          pageEq idxEq = lookup  table1 idx1 (memory s) pageEq idxEq) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. assumption.
Qed.

Lemma isVAUpdateMappedPageData' table1 table2 idx1 idx2 x s :
table2 <> table1 -> 
isVA table1 idx1 s -> 
isVA table1 idx1
{|
currentPartition := currentPartition s;
memory := add table2 idx2
          x
          (memory s) pageEq idxEq |}.
Proof.
intros.
unfold isVA in *.
cbn.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) pageEq idxEq = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq)
          pageEq idxEq = lookup  table1 idx1 (memory s) pageEq idxEq) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. assumption.
Qed.

Lemma dataStructurePdSh1Sh2asRootUpdateMappedPageData idxroot table idx  x s: 
consistency s -> 
(idxroot = idxPageDir \/ idxroot = idxShadow1 \/ idxroot = idxShadow2) -> 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
dataStructurePdSh1Sh2asRoot idxroot s -> 
dataStructurePdSh1Sh2asRoot idxroot
  {|
  currentPartition := currentPartition s;
  memory := add table idx
             x (memory s) pageEq idxEq |}.
Proof.
intros Hcons Hor (Hconfig & Hfalse) Hds.
unfold consistency in *.

assert(Hnoduptree: noDupPartitionTree s) by intuition.
assert(Hpde: partitionDescriptorEntry s) by intuition.
set (s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx
              x (memory s) pageEq idxEq |}) in *.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
 { unfold s'.
   apply getPartitionsUpdateMappedPageData ; trivial.
   + unfold getPartitions.
     destruct nbPage;simpl;left;trivial.
   + apply beq_nat_false in Hfalse.
     unfold not in *; intros.
     apply Hfalse.
     subst;trivial. }
unfold dataStructurePdSh1Sh2asRoot in *.
intros partition Hpart entrypp Hpp va true nbL stop HnbL indirection idx0 Hgetind.
rewrite Hpartions in *.
apply nextEntryIsPPUpdateMappedPageData in  Hpp; trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
assert(HnbLevel : (S nbL) = nbLevel).
{ apply getNbLevelEq in HnbL.
  unfold CLevel in HnbL.
  case_eq (lt_dec (nbLevel - 1) nbLevel); intros;
  rewrite H0 in *.
  simpl in *.
  destruct nbL.
  simpl in *.
  inversion HnbL. lia.
  assert(0 < nbLevel) by apply nbLevelNotZero. 
  lia. }
assert(Htable :stop <= (nbLevel -1) -> ~ In table (getIndirectionsAux entrypp s (S stop))).
intros.
{ assert (Hstop : stop < (nbLevel -1) \/ stop = (nbLevel -1) ) by lia.
  clear H.
  destruct Hstop as [Hlt |  Heq ].
  +
generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig .
destruct Hor as [Hpd | [Hsh1 | Hsh2]].
{ subst.
  apply  notConfigTableNotPdconfigTableLt with partition; trivial.
  apply nextEntryIsPPgetPd; trivial. }
{ subst.
  apply  notConfigTableNotSh1configTableLt with partition; trivial.
  apply nextEntryIsPPgetFstShadow; trivial. }
{ subst.
  apply  notConfigTableNotSh2configTableLt with partition; trivial.
  apply nextEntryIsPPgetSndShadow; trivial. }
+ subst.

assert(0<nbLevel) by apply nbLevelNotZero.
assert(Hsnbl :  (S (nbLevel - 1)) = nbLevel) by lia.
rewrite Hsnbl.
destruct Hor as [Hpd | [Hsh1 | Hsh2]].
{ subst.
  apply  notConfigTableNotPdconfigTable with partition; trivial.
  generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetPd; trivial. }
{ subst.
  apply  notConfigTableNotSh1configTable with partition; trivial.
  generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetFstShadow; trivial. }
{ subst.
  apply  notConfigTableNotSh2configTable with partition; trivial.
  generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetSndShadow; trivial. } }
 
assert( getIndirection entrypp va nbL stop s' = getIndirection entrypp va nbL stop s).
{ assert (Hstop3 : stop < (nbLevel -1) \/ stop = (nbLevel -1) \/ stop > (nbLevel -1)) by lia.
  destruct Hstop3 as [Hlt | [ Heq | Hgt]].
  + apply getIndirectionUpdateMappedPageData with nbL;
    trivial. apply Htable. lia.
  + subst.
    apply getIndirectionUpdateMappedPageData with nbL ;trivial.
    apply Htable. lia.
  + assert( getIndirection entrypp va nbL stop s' = 
            getIndirection entrypp va nbL nbL s').
    { rewrite Hgetind.
      symmetry.
      apply getIndirectionStopLevelGT2 with stop; trivial.
      apply getNbLevelLe in HnbL.
      unfold CLevel in HnbL.
      case_eq (lt_dec (nbLevel - 1) nbLevel); intros;
      rewrite H0 in *.
      simpl in *.
      destruct nbL.
      simpl in *. lia.
      assert(0 < nbLevel) by apply nbLevelNotZero. 
      lia. }
    rewrite Hgetind.
    symmetry.
    apply getIndirectionStopLevelGT with nbL; trivial.
    apply getNbLevelLe in HnbL.
    unfold CLevel in HnbL.
    case_eq (lt_dec (nbLevel - 1) nbLevel); intros;
    rewrite H0 in *.
    simpl in *.
    destruct nbL.
    simpl in *. lia.
    assert(0 < nbLevel) by apply nbLevelNotZero. 
    lia.
    rewrite <- Hgetind.
    rewrite H0.
    symmetry.
    apply getIndirectionUpdateMappedPageData with nbL ;trivial.
    rewrite HnbLevel.
    destruct Hor as [Hpd | [Hsh1 | Hsh2]].
    { subst.
      apply  notConfigTableNotPdconfigTable with partition; trivial.
      generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      apply nextEntryIsPPgetPd; trivial. }
    { subst.
      apply  notConfigTableNotSh1configTable with partition; trivial.
      generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      apply nextEntryIsPPgetFstShadow; trivial. }
    { subst.
      apply  notConfigTableNotSh2configTable with partition; trivial.
      generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      apply nextEntryIsPPgetSndShadow; trivial. } }
rewrite H0 in *.
generalize (Hds partition Hpart entrypp  Hpp va true nbL stop HnbL indirection 
idx0 Hgetind);clear Hds; intros Hind.
destruct Hind as [ Hind | Hind].
left. assumption.
right.
destruct Hind as (Hind & Hnotnull). 
split;trivial.
assert (In indirection (getIndirectionsAux entrypp s nbLevel)).
{ apply getIndirectionInGetIndirections with va nbL stop; trivial.
  apply getNbLevelLe in HnbL; trivial.
  unfold partitionDescriptorEntry in Hpde.
  assert(exists entry : page, nextEntryIsPP partition idxroot entry s /\
         entry <> pageDefault).
  apply Hpde; trivial.
  intuition.
  destruct H1 as ( entry & Hentry & Hnotnul).
  unfold nextEntryIsPP in * .
  destruct (StateLib.Index.succ idxroot ); 
  [| now contradict Hentry].
  destruct (lookup partition i (memory s) pageEq idxEq);
  [| now contradict Hentry].
  destruct v; try now contradict Hentry.
  subst. assumption. }
assert (~ In table (getIndirectionsAux entrypp s nbLevel)).
{ destruct Hor as [Hpd | [Hsh1 | Hsh2]].
{ subst.
  apply  notConfigTableNotPdconfigTable with partition; trivial.
  generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetPd; trivial. }
{ subst.
  apply  notConfigTableNotSh1configTable with partition; trivial.
  generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetFstShadow; trivial. }
{ subst.
  apply  notConfigTableNotSh2configTable with partition; trivial.
  generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetSndShadow; trivial. } }
  assert (table <> indirection).
  unfold not.
  intros.
  subst. now contradict H2.
  destruct Hind as [(Hlevel & Hind) | (Hlevel & Hind)].
  + left. split; trivial.
    apply isPEUpdateUpdateMappedPageData;trivial.
  + right. split; trivial.
    destruct Hind as [ (Hvalu & Hidx) | [(Hvalu & Hidx) |(Hvalu & Hidx)]].
    left; split; trivial.
    apply isVEUpdateMappedPageData; trivial.
    right. left.
    split; trivial.
    apply isVAUpdateMappedPageData'; trivial.
    right; right; split; trivial.
    apply isPEUpdateUpdateMappedPageData; trivial.
Qed.

Lemma getTableAddrRootUpdateMappedPageData table1 table2 idx2 idxroot partition va 
x s:
(forall partition0 : page,
In partition0 (getPartitions pageRootPartition s) ->
partition0 = table2 \/ In table2 (getConfigPagesAux partition0 s) -> False) -> 
(Nat.eqb pageDefault table2) = false -> 
In partition (getPartitions pageRootPartition s) -> 
partitionDescriptorEntry s -> 
getTableAddrRoot table1 idxroot partition va s -> 
getTableAddrRoot table1 idxroot partition va
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2
             x (memory s) pageEq idxEq |}.
Proof.
intros Hconfig Htbl2notnull Hmult Hpde Htblroot.
unfold getTableAddrRoot in *.
destruct Htblroot as (Htrue & Htblroot).
split; trivial.
intros.
assert (Hpp : nextEntryIsPP partition idxroot tableroot s).
rewrite nextEntryIsPPUpdateMappedPageData; try eassumption.
clear H.
generalize (Htblroot tableroot Hpp); clear Htblroot; intros Htblroot.
destruct Htblroot as (nbL & HnbL & stop & Hstop & Hind).
exists nbL.
split; trivial.
exists stop.
split; trivial.
rewrite <- Hind.
assert( getIndirection tableroot va nbL stop s = 
            getIndirection tableroot va nbL nbL s).
    { rewrite Hind.
      symmetry.
      apply getIndirectionStopLevelGT2 with stop; trivial.
      lia. }
rewrite Hind.
apply getIndirectionStopLevelGT with nbL; trivial.
lia.
rewrite <- Hind.
rewrite H.
apply getIndirectionUpdateMappedPageData with nbL ;trivial.
assert (HnbLevel : stop = nbLevel).
apply getNbLevelEq in HnbL.
unfold CLevel in HnbL.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros; rewrite H0 in *; trivial.
destruct nbL.
simpl in *.
inversion HnbL.
lia.
assert (0 < nbLevel) by apply nbLevelNotZero.
lia.
subst.
rewrite <- NPeano.Nat.add_1_r.
rewrite HnbLevel.
destruct Htrue as [Hpd | [Hsh1 | Hsh2]].
{ subst.
  apply  notConfigTableNotPdconfigTable with partition; trivial.
  generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetPd; trivial. }
{ subst.
  apply  notConfigTableNotSh1configTable with partition; trivial.
  generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetFstShadow; trivial. }
{ subst.
  apply  notConfigTableNotSh2configTable with partition; trivial.
  generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetSndShadow; trivial. }
Qed.

Lemma entryPresentFlagUpdateMappedPageData table1 table2 idx1 idx2 
flag x s: 
table2 <> table1 -> 
entryPresentFlag table1 idx1 flag s -> 
entryPresentFlag table1 idx1 flag
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2
              x (memory s) pageEq idxEq |}.
Proof.
intros.
unfold entryPresentFlag in *.
cbn.

assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) pageEq idxEq = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq)
          pageEq idxEq = lookup  table1 idx1 (memory s) pageEq idxEq) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. assumption.
Qed.

Lemma entryUserFlagUpdateMappedPageData table1 table2 idx1 idx2 
flag x s: 
table2 <> table1 -> 
entryUserFlag table1 idx1 flag s -> 
entryUserFlag table1 idx1 flag
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2
              x (memory s) pageEq idxEq |}.
Proof.
intros.
unfold entryUserFlag in *.
cbn.

assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) pageEq idxEq = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq)
          pageEq idxEq = lookup  table1 idx1 (memory s) pageEq idxEq) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. assumption.
Qed.

Lemma isEntryVAUpdateMappedPageData table1 table2 idx1 idx2 va x s :
table2 <> table1 -> 
isEntryVA table1 idx1 va s ->
isEntryVA table1 idx1 va
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2
              x (memory s) pageEq idxEq |}.
Proof.
intros Hentryva.
unfold isEntryVA in *.
cbn.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) pageEq idxEq = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq)
          pageEq idxEq = lookup  table1 idx1 (memory s) pageEq idxEq) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. trivial.
Qed.

Lemma isEntryPageUpdateMappedPageData table1 table2 idx1 idx2 phytable1 x s :
table2 <> table1 -> 
isEntryPage table1 idx1 phytable1 s ->
isEntryPage table1 idx1 phytable1
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2 x (memory s) pageEq idxEq |}.
Proof.
intros Hentryva.
unfold isEntryPage in *.
cbn.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) pageEq idxEq = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq)
          pageEq idxEq = lookup  table1 idx1 (memory s) pageEq idxEq) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. trivial.
Qed.

Lemma readPhyEntryUpdateMappedPageData table1 table2 idx1 idx2 x s :
table2 <> table1 -> 
StateLib.readPhyEntry table1 idx1 (memory s) =
StateLib.readPhyEntry table1 idx1 
 ( add table2 idx2
              x (memory s) pageEq idxEq ).
Proof.
intros Hnoteq.
unfold StateLib.readPhyEntry in *.
cbn.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) pageEq idxEq = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq)
          pageEq idxEq = lookup  table1 idx1 (memory s) pageEq idxEq) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. trivial.
Qed.


Lemma readPresentUpdateMappedPageData table1 table2 idx1 idx2 x s :
table2 <> table1 -> 
StateLib.readPresent table1 idx1 (memory s) =
StateLib.readPresent table1 idx1 
 ( add table2 idx2
              x (memory s) pageEq idxEq ).
Proof.
intros Hnoteq.
unfold StateLib.readPresent in *.
cbn.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) pageEq idxEq = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq)
          pageEq idxEq = lookup  table1 idx1 (memory s) pageEq idxEq) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. trivial.
Qed.

Lemma readMappedPageDataUpdateMappedPageData partition (pt1 pt2 : page) phy1 phy2 
idxVa1 idxVa2 va1 va2  level s  : 
In partition (getPartitions pageRootPartition s) -> 
Some level = StateLib.getNbLevel -> 
partitionDescriptorEntry s -> 
noDupMappedPagesList s ->
(Nat.eqb pageDefault pt2) = false ->
(Nat.eqb pageDefault pt1) = false ->
isEntryPage pt1 idxVa1 phy1 s -> 
isEntryPage pt2 idxVa2 phy2 s ->
StateLib.getIndexOfAddr va1 levelMin = idxVa1 -> 
StateLib.getIndexOfAddr va2 levelMin = idxVa2 -> 
(forall idx : index,
 StateLib.getIndexOfAddr va1 levelMin = idx ->
 isPE pt1 idx s /\ 
 getTableAddrRoot pt1 idxPageDir partition va1 s) -> 
(forall idx : index,
 StateLib.getIndexOfAddr va2 levelMin = idx ->
 isPE pt2 idx s /\ 
 getTableAddrRoot pt2 idxPageDir partition va2 s) ->  
false = StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 level -> 
entryPresentFlag pt1 idxVa1 true s -> 
entryPresentFlag pt2 idxVa2 true s -> 
phy1 <> phy2.
Proof.
intros Hmult Hlevel Hpde Hnodup Hpt2notnull Hpt1notnull Hep1 Hep2 Hidxva1 Hidxva2 Hget1 Hget2 Hvas
Hpresent1 Hpresent2 .
rewrite Hidxva1 in *.
rewrite Hidxva2 in *.
destruct Hget1 with idxVa1 as (Hpe1 & Hgetroot1); trivial.
destruct Hget2 with idxVa2 as (Hpe2 & Hgetroot2); trivial.
clear Hget1 Hget2.
unfold getTableAddrRoot in *.
destruct Hgetroot1 as (_ & Hget1).
destruct Hgetroot2 as (_ & Hget2).
unfold partitionDescriptorEntry in *.
assert(idxPageDir < tableSize - 1 /\
       isVA partition idxPageDir s /\ 
       (exists entry : page, nextEntryIsPP partition idxPageDir entry s /\ 
       entry <> pageDefault)).
apply Hpde; trivial.
left; trivial.
destruct H as (Hsize & _ & pd & Htrue & Hpdnotnull).
clear Hpde.
assert(Hind1 :exists nbL : ADT.level,
          Some nbL = StateLib.getNbLevel /\
          (exists stop : nat, stop = nbL + 1 /\ 
          getIndirection pd va1 nbL stop s = Some pt1)).
apply Hget1; trivial.
assert(Hind2 :exists nbL : ADT.level,
          Some nbL = StateLib.getNbLevel /\
          (exists stop : nat, stop = nbL + 1 /\ 
          getIndirection pd va2 nbL stop s = Some pt2)).
apply Hget2; trivial.
destruct Hind1 as (nbL1 & HnbL1 & stop1 & Hstop1 & Hind1).
destruct Hind2 as (nbL2 & HnbL2 & stop2 & Hstop2 & Hind2).
rewrite <- HnbL1 in HnbL2.
inversion HnbL2 as [HnbL].
subst.
unfold noDupMappedPagesList in *.
apply Hnodup in Hmult; clear Hnodup.
assert(Hphy2 : getMappedPage pd s va2 = SomePage phy2).
{ unfold getMappedPage.
  rewrite <- HnbL1.
assert(Hgetlastind2 :getIndirection pd va2 nbL1 (nbLevel - 1) s = Some pt2).
  apply getIndirectionStopLevelGT2 with (nbL1 + 1); trivial.
  lia.
  apply getNbLevelEq in HnbL1.
  rewrite HnbL1.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel); intros.
  simpl; trivial.
  assert(0 < nbLevel) by apply nbLevelNotZero.
  lia.
  rewrite Hgetlastind2.
  rewrite Hpt2notnull.  
  unfold entryPresentFlag in Hpresent2.
  unfold StateLib.readPresent.
  subst.
  destruct (lookup pt2 (StateLib.getIndexOfAddr va2 levelMin)
             (memory s) pageEq idxEq); try now contradict Hpresent2.
  destruct v; try now contradict Hpresent2.
  destruct (present p); try now contradict Hpresent2.
  unfold isEntryPage in Hep2.
  unfold StateLib.readPhyEntry.
  destruct(lookup pt2 
  (StateLib.getIndexOfAddr va2 levelMin) (memory s) pageEq idxEq);
  try now contradict Hpe2.
  destruct v; try now contradict Hpe2.
  subst. trivial. }
assert(Hphy1 :getMappedPage pd s va1 = SomePage phy1).
{ 
  unfold getMappedPage.
  rewrite <- HnbL1.
  assert(Hgetlastind1 :getIndirection pd va1 nbL1 (nbLevel - 1) s = Some pt1).
  apply getIndirectionStopLevelGT2 with (nbL1 + 1); trivial.
  lia.
  apply getNbLevelEq in HnbL1.
  rewrite HnbL1.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel); intros.
  simpl; trivial.
  assert(0 < nbLevel) by apply nbLevelNotZero.
  lia.
  rewrite Hgetlastind1.
  rewrite Hpt1notnull.
  unfold entryPresentFlag in Hpresent1.
  unfold StateLib.readPresent.
  subst.
  destruct (lookup pt1 (StateLib.getIndexOfAddr va1 levelMin)
             (memory s) pageEq idxEq); try now contradict Hpresent1.
  destruct v; try now contradict Hpresent1.
  destruct (present p); try now contradict Hpresent1.
  unfold isEntryPage in Hep1.
  unfold StateLib.readPhyEntry.
  destruct(lookup pt1 
  (StateLib.getIndexOfAddr va1 levelMin) (memory s) pageEq idxEq);
  try now contradict Hpe1.
  destruct v; try now contradict Hpe1.
  subst. trivial. }
  
assert(Hin : In phy1 (getMappedPages partition s)).
{ unfold getMappedPages.
  assert( Hpd : StateLib.getPd partition (memory s) = Some pd).
  apply nextEntryIsPPgetPd; trivial.
  rewrite Hpd.
  unfold getMappedPagesAux.
  apply filterOptionInIff.
  unfold getMappedPagesOption.
  apply in_map_iff.
  assert(Heqvars : exists va10, In va10 getAllVAddrWithOffset0 /\ 
      StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va10 ( CLevel (nbLevel -1) ) = true )
      by apply AllVAddrWithOffset0.
      destruct Heqvars as (va10 & Hva1 & Hva11).  
      exists va10.
      split;trivial.
      rewrite  <- Hphy1.
      symmetry.
      apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
      apply getNbLevelEqOption. }
      

  move Hmult at bottom.
  unfold getMappedPages in *.
  case_eq (StateLib.getPd partition (memory s));intros; rewrite H in *;
  try now contradict Hin.
  unfold getMappedPagesAux in *.
  unfold getMappedPagesOption in *.
  assert(p = pd).
  apply nextEntryIsPPgetPd in Htrue.
  rewrite Htrue in H.
  inversion H; trivial.
  subst.
  apply  twoMappedPagesAreDifferent with va1 va2 pd level s; trivial; try apply AllVAddrAll.
  symmetry;trivial.
  symmetry.
  trivial.
Qed.

Lemma readPDflagUpdateMappedPageData table1 table2 idx1 idx2 x s :
table1 <> table2 -> 
StateLib.readPDflag table1 idx1 (add table2 idx2 x (memory s) pageEq idxEq) =
StateLib.readPDflag table1 idx1 (memory s).
Proof.
intros.
unfold StateLib.readPDflag .
cbn.
assert(Hfalse : beqPairs (table2, idx2) (table1, idx1) pageEq idxEq = false).
{ apply beqPairsFalse;intuition. }
rewrite Hfalse.
assert(Hmemory : lookup table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq) 
         pageEq idxEq = lookup table1 idx1 (memory s) pageEq idxEq).
{ apply removeDupIdentity;intuition. }
rewrite Hmemory.
trivial.
Qed.

Lemma getPDFlagUpdateMappedPageData partition table curidx sh1 va x s:
  nextEntryIsPP partition idxShadow1 sh1 s  -> 
  In partition (getPartitions pageRootPartition s) -> 
  partitionDescriptorEntry s -> 
  ~ In table (getIndirectionsAux sh1 s (S (nbLevel - 1))) -> 
getPDFlag sh1 va
{| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} = 
getPDFlag sh1 va s.
Proof.
intros Hpp Hpart Hpde Hnotconfig.
unfold getPDFlag.
case_eq (StateLib.getNbLevel); intros;trivial.
assert(Hind: getIndirection sh1 va l (nbLevel - 1)
              {| currentPartition := currentPartition s; 
                  memory := add table curidx x (memory s) pageEq idxEq |} 
              = getIndirection sh1 va l (nbLevel - 1) s).
 apply getIndirectionUpdateMappedPageData  with l;intuition.
rewrite Hind.
case_eq(getIndirection sh1 va l (nbLevel - 1) s);intros;trivial.
case_eq (Nat.eqb p pageDefault);intros;trivial.
cbn.
assert (In p (getIndirectionsAux sh1 s nbLevel)).
{ apply getIndirectionInGetIndirections with va l (nbLevel - 1); trivial.
  assert(0 <nbLevel) by apply nbLevelNotZero.
  lia.
  apply beq_nat_false in H1.
  unfold not;intros;subst.
  now contradict H1.
  symmetry in H.
  apply getNbLevelLe in H; trivial.
  unfold partitionDescriptorEntry in Hpde.
  assert(Hentry : exists entry : page, nextEntryIsPP partition idxShadow1 entry s /\
         entry <> pageDefault).
  apply Hpde; trivial.
  intuition.
  destruct Hentry as ( entry & Hentry & Hnotnul).
  unfold nextEntryIsPP in * .
  destruct (StateLib.Index.succ idxShadow1 ); 
  [| now contradict Hentry].
  destruct (lookup partition i (memory s) pageEq idxEq);
  [| now contradict Hentry].
  destruct v; try now contradict Hentry.
  subst. assumption. }
assert(StateLib.readPDflag p (StateLib.getIndexOfAddr va levelMin)
        (add table curidx x (memory s) pageEq idxEq) =
       StateLib.readPDflag p (StateLib.getIndexOfAddr va levelMin) (memory s)).
{ apply readPDflagUpdateMappedPageData; trivial.
  unfold not;intros;subst.
  assert(0<nbLevel) by apply nbLevelNotZero.
  replace (S (nbLevel - 1)) with nbLevel in * by lia.
  now contradict Hnotconfig. }
rewrite H3.
trivial.
Qed.
Lemma getVirtualAddressSh2UpdateMappedPageData sh2 s va table curidx x :
~ In table (getIndirectionsAux sh2 s nbLevel) -> 
sh2 <> pageDefault -> 
getVirtualAddressSh2 sh2 s va =
getVirtualAddressSh2 sh2 
 {| currentPartition := currentPartition s; 
      memory := add table curidx x (memory s) pageEq idxEq |} va.
Proof.
intros.
unfold getVirtualAddressSh2.
case_eq(StateLib.getNbLevel);trivial.
intros nbL HnbL.
symmetry in HnbL.
rewrite  getIndirectionUpdateMappedPageData with sh2 table curidx nbL nbL va 
          (nbLevel -1) x s;trivial.
case_eq( getIndirection sh2 va nbL (nbLevel - 1) s);trivial.
intros lastIndirection Hind.
simpl.
case_eq(Nat.eqb pageDefault lastIndirection);intros;trivial.
rewrite readVirtualUpdateMappedPageData;trivial.
 assert(In lastIndirection (getIndirectionsAux sh2 s nbLevel)).
 { apply getIndirectionInGetIndirections with va nbL (nbLevel - 1);trivial;
  try lia.
  apply nbLevelNotZero.
  unfold not;intros.
  apply beq_nat_false in H1.
  subst.
  now contradict H1.
  apply getNbLevelEq in HnbL.
  subst. lia. }
  unfold not;intros.
  subst.
  now contradict H.
  assert(0<nbLevel) by apply nbLevelNotZero.
  replace (S (nbLevel - 1)) with nbLevel by lia.
  trivial.
Qed.

Lemma getVirtualAddressSh1UpdateMappedPageData sh1 s va table curidx x :
~ In table (getIndirectionsAux sh1 s nbLevel) -> 
sh1 <> pageDefault -> 
getVirtualAddressSh1 sh1 s va =
getVirtualAddressSh1 sh1 
 {| currentPartition := currentPartition s; 
      memory := add table curidx x (memory s) pageEq idxEq |} va.
Proof.
intros.
unfold getVirtualAddressSh1.
case_eq(StateLib.getNbLevel);trivial.
intros nbL HnbL.
symmetry in HnbL.
rewrite  getIndirectionUpdateMappedPageData with sh1 table curidx nbL nbL va 
          (nbLevel -1) x s;trivial.
case_eq( getIndirection sh1 va nbL (nbLevel - 1) s);trivial.
intros lastIndirection Hind.
simpl.
case_eq(Nat.eqb pageDefault lastIndirection);intros;trivial.
rewrite readVirEntryUpdateMappedPageData;trivial.
 assert(In lastIndirection (getIndirectionsAux sh1 s nbLevel)).
 { apply getIndirectionInGetIndirections with va nbL (nbLevel - 1);trivial;
  try lia.
  apply nbLevelNotZero.
  unfold not;intros.
  apply beq_nat_false in H1.
  subst.
  now contradict H1.
  apply getNbLevelEq in HnbL.
  subst. lia. }
  unfold not;intros.
  subst.
  now contradict H.
  assert(0<nbLevel) by apply nbLevelNotZero.
  replace (S (nbLevel - 1)) with nbLevel by lia.
  trivial.
Qed.


Lemma isAccessibleMappedPageInParentUpdateMappedPageData  partition (* nbL *) va
 phypage table curidx x s:
table <> pageDefault -> 
partitionDescriptorEntry s ->
parentInPartitionList s -> 
(* Some nbL = StateLib.getNbLevel ->  *)
In partition (getPartitions pageRootPartition s) -> 
(forall partition1 ,In partition1 (getPartitions pageRootPartition s)
->  ~ In table (getConfigPages partition1 s)) -> 
isAccessibleMappedPageInParent partition va phypage s =
isAccessibleMappedPageInParent partition va phypage
  {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros Ha Hb Hc (* Hd *) He Hf.

unfold isAccessibleMappedPageInParent.
simpl.
rewrite getSndShadowUpdateMappedPageData;trivial.
case_eq (StateLib.getSndShadow partition (memory s));trivial.
intros sh2 Hsh2.
rewrite <- getVirtualAddressSh2UpdateMappedPageData.
case_eq(getVirtualAddressSh2 sh2 s va);trivial.
intros vaInParent HvaInParent.
rewrite getParentUpdateMappedPageData;trivial.
case_eq(StateLib.getParent partition (memory s));trivial.
intros parent Hparent.
rewrite getPdUpdateMappedPageData.
case_eq(StateLib.getPd parent (memory s) );trivial.
intros pdParent HpdParent.
rewrite <- getAccessibleMappedPageUpdateMappedPageData  with 
pdParent table curidx s  x vaInParent;trivial.

unfold getVirtualAddressSh2.
simpl.
+ unfold partitionDescriptorEntry in *.
  assert((exists entry : page, nextEntryIsPP parent idxPageDir entry s /\ 
  entry <> pageDefault)).
  apply Hb;trivial.
  unfold parentInPartitionList in *.
  apply Hc with partition;trivial.
  rewrite nextEntryIsPPgetParent in *;trivial.  
  left;trivial.
  destruct H as (entrypd & Hpp & Hnotnul).
  assert(entrypd = pdParent).
  apply getPdNextEntryIsPPEq with parent s;trivial.
  subst. trivial.
+ assert(HinpartList : In parent (getPartitions pageRootPartition s)).
  unfold parentInPartitionList in *.
  apply Hc with partition;trivial.
  rewrite nextEntryIsPPgetParent in *;trivial.
   apply notConfigTableNotPdconfigTable with parent;trivial.
  apply Hf in HinpartList.
  unfold getConfigPages in *.
  simpl in *.
  apply Classical_Prop.not_or_and in HinpartList.
  intuition.
+ assert(HinpartList : In parent (getPartitions pageRootPartition s)).
  unfold parentInPartitionList in *.
  apply Hc with partition;trivial.
  rewrite nextEntryIsPPgetParent in *;trivial.
  apply Hf in HinpartList.
  unfold getConfigPages in *.
  simpl in *.
  apply Classical_Prop.not_or_and in HinpartList.
  intuition.
+ apply Hf in He.
  unfold getConfigPages in *.
  simpl in *.
  apply Classical_Prop.not_or_and in He.
  intuition.
+ apply notConfigTableNotSh2configTable with partition;trivial.
  apply Hf in He.
  unfold getConfigPages in *.
  simpl in *.
  apply Classical_Prop.not_or_and in He.
  intuition.
+ assert(Hexistpd :(exists entry : page, nextEntryIsPP partition idxShadow2 entry s /\
  entry <> pageDefault)).
  unfold partitionDescriptorEntry in *.
  apply Hb;trivial. 
  do 2 right;left;trivial.
  destruct Hexistpd as (entrypd & Hpp & Hnotnul).
  assert(entrypd = sh2).
  apply getSh2NextEntryIsPPEq with partition s;trivial.
  subst. trivial.
+ apply Hf in He.
  unfold getConfigPages in *.
  simpl in *.
  apply Classical_Prop.not_or_and in He.
  intuition.
Qed.

Lemma accessibleChildPageIsAccessibleIntoParentUpdateMAppedPageContent
 table curidx s x (* nbL *) :
 noDupPartitionTree s -> 
table <> pageDefault -> 
partitionDescriptorEntry s ->
parentInPartitionList s -> 
(* Some nbL = StateLib.getNbLevel ->  *)
(forall partition1 ,In partition1 (getPartitions pageRootPartition s)
->  ~ In table (getConfigPages partition1 s)) -> 
accessibleChildPageIsAccessibleIntoParent s ->
accessibleChildPageIsAccessibleIntoParent
  {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros Hnoduptree.
set (s' :=  {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |}).
  intros Htablenotnull Hpde Hparentpart Hconfig Hcons.
unfold accessibleChildPageIsAccessibleIntoParent.
intros  partition va pd  accessiblePage.
intros Hpart Hpd HaccessPage.
unfold s'.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsUpdateMappedPageData; trivial.
  unfold getPartitions.
  destruct nbPage;simpl;left;trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
simpl in *.
assert(Hnottable :table<> partition).
{ apply Hconfig in Hpart.
   apply Classical_Prop.not_or_and in Hpart.
   intuition. }
rewrite getPdUpdateMappedPageData in *;trivial.
unfold s' in *.
assert(Hpdnotnull : pd<> pageDefault).
{ assert(Hexistpd :(exists entry : page, nextEntryIsPP partition idxPageDir entry s /\ 
  entry <> pageDefault)).
  unfold partitionDescriptorEntry in *.
  apply Hpde;trivial.  
  left;trivial.
  destruct Hexistpd as (entrypd & Hpp & Hnotnul).
  assert(entrypd = pd).
  apply getPdNextEntryIsPPEq with partition s;trivial.
  subst. trivial. }
rewrite getAccessibleMappedPageUpdateMappedPageData  
with pd table curidx  s (* nbL *) x va in HaccessPage;trivial. 

rewrite <- isAccessibleMappedPageInParentUpdateMappedPageData with partition
(* nbL *) va accessiblePage table curidx x s;trivial.
unfold accessibleChildPageIsAccessibleIntoParent in *.
apply Hcons with pd;trivial.
clear HaccessPage.
apply  notConfigTableNotPdconfigTable with partition;trivial.
apply Hconfig in Hpart.
  apply Classical_Prop.not_or_and in Hpart.
  intuition.
Qed.

Lemma getAncestorsUpdateMappedPageData partition table curidx x  s :
parentInPartitionList s -> 
(*  ~ In table (getPartitions multiplexer s)->  *)
(forall partition : page,
    In partition (getPartitions pageRootPartition s) ->
    partition = table \/ In table (getConfigPagesAux partition s) -> False) -> 
In partition (getPartitions pageRootPartition s) -> 
getAncestors partition s =
getAncestors partition
{|
currentPartition := currentPartition s;
memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros.
assert (~ In table (getPartitions pageRootPartition s)).
assert(forall part, In part (getPartitions pageRootPartition s) -> part <> table ).
{ intros.
  unfold not.
  intros.
  apply H0 with table.
  subst;trivial.
  left;trivial. }
unfold not.
intros.
apply H2 in H3.
now contradict H3.
clear H0.
unfold getAncestors.
revert partition H1 H2.
induction (nbPage +1);
simpl;trivial;intros.
rewrite getParentUpdateMappedPageData;trivial.
case_eq(StateLib.getParent partition (memory s));intros;trivial.
f_equal.
simpl in *.
apply IHn;trivial.
unfold parentInPartitionList in *.
apply H with partition;trivial.
apply nextEntryIsPPgetParent;trivial.
unfold not; intros Hfalse'.
subst.
now contradict H2.
Qed.

Lemma isChildUpdateMappedPageData table curidx x  s:
noDupPartitionTree s -> 
partitionDescriptorEntry s -> 
parentInPartitionList s -> 
table <> pageDefault -> 
(forall partition : page,
  In partition (getPartitions pageRootPartition s) ->
  partition = table \/ In table (getConfigPagesAux partition s) -> False) ->
isChild s -> 
isChild {|  currentPartition := currentPartition s;
        memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros Hnoduptree. 
unfold isChild.
intros Hpde Hparent Hnotnull Hget1 Hget2 partition parent Hparts Hgetparent .
simpl in *.
assert(HgetParts : getPartitions pageRootPartition
  {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |} = 
  getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
rewrite HgetParts in *.
assert (Htable : table <> partition).
unfold not;intros.
subst.
apply Hget1 with partition;trivial.
left;trivial.
rewrite getParentUpdateMappedPageData in *;trivial.
assert(Hchildren : getChildren parent
{|
currentPartition := currentPartition s;
memory := add table curidx x (memory s) pageEq idxEq |} = 
getChildren parent s).
apply getChildrenUpdateMappedPageData;trivial.
unfold parentInPartitionList in *.
apply Hparent with partition;trivial.
apply nextEntryIsPPgetParent;trivial.
unfold not. 
intros.
apply Hget1 with parent;trivial.
unfold parentInPartitionList in *.
apply Hparent with partition;trivial.
apply nextEntryIsPPgetParent;trivial.
unfold not;intros.
subst.
apply Hget1 with parent;trivial.
  unfold parentInPartitionList in *.
apply Hparent with partition;trivial.
apply nextEntryIsPPgetParent;trivial.
left;trivial.
rewrite Hchildren.
apply Hget2;trivial.
Qed.

Lemma isParentUpdateMappedPageData table curidx x  s:
noDupPartitionTree s -> 
partitionDescriptorEntry s -> 
parentInPartitionList s -> 
table <> pageDefault -> 
(forall partition : page,
  In partition (getPartitions pageRootPartition s) ->
  partition = table \/ In table (getConfigPagesAux partition s) -> False) ->
isParent s -> 
isParent {|  currentPartition := currentPartition s;
        memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros Hnoduptree. 
unfold isParent.
intros Hpde Hparent Hnotnull Hget1 Hget2 partition parent Hparts Hgetparent .
simpl in *.
assert(HgetParts : getPartitions pageRootPartition
  {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |} = 
  getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
rewrite HgetParts in *. clear HgetParts.
assert(Hchildren : getChildren parent
{|
currentPartition := currentPartition s;
memory := add table curidx x (memory s) pageEq idxEq |} = 
getChildren parent s).
apply getChildrenUpdateMappedPageData;trivial.
unfold not;intros.
apply Hget1 with parent;trivial.
  
assert (Htable : table <> parent).
{
unfold not;intros.
subst.
apply Hget1 with parent;trivial.
left;trivial. }
trivial.
rewrite Hchildren in *.
clear Hchildren. 
assert (Htable : table <> partition).
{
unfold not;intros.
subst.
apply Hget1 with partition;trivial.
apply childrenPartitionInPartitionList with parent;trivial.

left;trivial. }
rewrite getParentUpdateMappedPageData in *;trivial.
apply Hget2;trivial.
Qed.
Lemma wellFormedFstShadowtUpdateMappedPageData table curidx x  s:
noDupPartitionTree s -> 
partitionDescriptorEntry s -> 
parentInPartitionList s -> 
table <> pageDefault -> 
(forall partition : page,
  In partition (getPartitions pageRootPartition s) ->
  partition = table \/ In table (getConfigPagesAux partition s) -> False) ->
wellFormedFstShadow s -> 
wellFormedFstShadow {|  currentPartition := currentPartition s;
        memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros Hnoduptree. 
unfold wellFormedFstShadow.
intros Hpde Hparent Hnotnull Hget1 Hget2. 
simpl in *.
assert(HgetParts : getPartitions pageRootPartition
  {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |} = 
  getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
rewrite HgetParts in *. clear HgetParts.
intros.
assert(table <> partition).
    {
    unfold not;intros. apply Hget1 with partition;trivial.
    left;trivial. intuition. }
assert(Hpd :  StateLib.getPd partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getPd partition (memory s)).  
  { intros.    
    apply getPdUpdateMappedPageData;trivial.
     }
assert(Hpdchildnotnull : pd <> pageDefault).
{ unfold partitionDescriptorEntry in *.
rewrite Hpd in *. clear Hpd. 
assert( exists entry : page, nextEntryIsPP partition idxPageDir entry s 
/\ entry <> pageDefault) as (pdtmp & Hpdtmp & Hnotnul).
apply Hpde;trivial.
left;trivial.
assert( pdtmp = pd).
apply getPdNextEntryIsPPEq with partition s;trivial.
subst.
trivial. }
 assert(Hmap : getMappedPage pd
       {|
       currentPartition := currentPartition s;
       memory := add table curidx x (memory s) pageEq idxEq |} va =
       getMappedPage pd s va).
{ apply getMappedPageUpdateMappedPageData;trivial.
apply notConfigTableNotPdconfigTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial.
    
rewrite Hpd in *;clear Hpd.
trivial. }

rewrite Hmap in *. clear Hmap.
assert(Hsh1 :  StateLib.getFstShadow partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getFstShadow partition (memory s)).  
  { intros.    
    apply getFstShadowUpdateMappedPageData;trivial.
     }
rewrite Hsh1 in *.
assert(   sh1<> pageDefault  ).
{
assert( exists entry : page, nextEntryIsPP partition idxShadow1 entry s 
/\ entry <> pageDefault) as (pdtmp & Hpdtmp & Hnotnul).
apply Hpde;trivial.
right;left;trivial.
assert( pdtmp = sh1).
apply getSh1NextEntryIsPPEq with partition s;trivial.
subst.
trivial. }
assert(Hv1 : getVirtualAddressSh1 sh1
    {|
    currentPartition := currentPartition s;
    memory := add table curidx x (memory s) pageEq idxEq |} va = getVirtualAddressSh1 sh1
    s va).
    symmetry.
     
apply getVirtualAddressSh1UpdateMappedPageData;trivial.
apply notConfigTableNotSh1configTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial.
rewrite Hv1.
apply Hget2 with partition pg pd;trivial.
rewrite Hpd in *.
trivial. 
Qed.

Lemma wellFormedFstShadowIfNoneUpdateMappedPageData table curidx x  s:
noDupPartitionTree s -> 
partitionDescriptorEntry s -> 
parentInPartitionList s -> 
table <> pageDefault -> 
(forall partition : page,
  In partition (getPartitions pageRootPartition s) ->
  partition = table \/ In table (getConfigPagesAux partition s) -> False) ->
wellFormedFstShadowIfNone s -> 
wellFormedFstShadowIfNone {|  currentPartition := currentPartition s;
        memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros Hnoduptree. 
unfold wellFormedFstShadowIfNone.
intros Hpde Hparent Hnotnull Hget1 Hget2. 
simpl in *.
assert(HgetParts : getPartitions pageRootPartition
  {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |} = 
  getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
rewrite HgetParts in *. clear HgetParts.
intros.
assert(table <> partition).
    {
    unfold not;intros. apply Hget1 with partition;trivial.
    left;trivial. intuition. }
assert(Hpd :  StateLib.getPd partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getPd partition (memory s)).  
  { intros.    
    apply getPdUpdateMappedPageData;trivial.
     }
assert(Hpdchildnotnull : pd <> pageDefault).
{ unfold partitionDescriptorEntry in *.
rewrite Hpd in *. clear Hpd.
apply pdPartNotNull with partition s;trivial.
apply nextEntryIsPPgetPd;trivial. }
 assert(Hmap : getMappedPage pd
       {|
       currentPartition := currentPartition s;
       memory := add table curidx x (memory s) pageEq idxEq |} va =
       getMappedPage pd s va).
{ apply getMappedPageUpdateMappedPageData;trivial.
apply notConfigTableNotPdconfigTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial.
    
rewrite Hpd in *;clear Hpd.
trivial. }

rewrite Hmap in *. clear Hmap.
assert(Hsh1 :  StateLib.getFstShadow partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getFstShadow partition (memory s)).  
  { intros.    
    apply getFstShadowUpdateMappedPageData;trivial.
     }
rewrite Hsh1 in *.
assert(   sh1<> pageDefault  ).
{ apply sh1PartNotNull with partition s;trivial.
  apply nextEntryIsPPgetFstShadow;trivial. }
assert(Hv1 : getPDFlag sh1 va
    {|
    currentPartition := currentPartition s;
    memory := add table curidx x (memory s) pageEq idxEq |}  = getPDFlag sh1
    va s).
{    
apply getPDFlagUpdateMappedPageData with partition;trivial.
apply nextEntryIsPPgetFstShadow;trivial.
assert(nbLevel> 0) by apply nbLevelNotZero.
replace (S (nbLevel - 1)) with nbLevel by lia.
apply notConfigTableNotSh1configTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial. }
rewrite Hv1.
assert(Hv2 : getVirtualAddressSh1 sh1
    {|
    currentPartition := currentPartition s;
    memory := add table curidx x (memory s) pageEq idxEq |}  va = getVirtualAddressSh1 sh1
     s va).
{ symmetry.    
apply getVirtualAddressSh1UpdateMappedPageData ;trivial.
apply notConfigTableNotSh1configTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial. }
rewrite Hv2.
apply Hget2 with partition  pd;trivial.
rewrite Hpd in *.
trivial. 
Qed.


Lemma wellFormedFstShadowIfDefaultValuesUpdateMappedPageData table curidx x  s:
noDupPartitionTree s -> 
partitionDescriptorEntry s -> 
parentInPartitionList s -> 
table <> pageDefault -> 
(forall partition : page,
  In partition (getPartitions pageRootPartition s) ->
  partition = table \/ In table (getConfigPagesAux partition s) -> False) ->
wellFormedFstShadowIfDefaultValues s -> 
wellFormedFstShadowIfDefaultValues {|  currentPartition := currentPartition s;
        memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros Hnoduptree. 
unfold wellFormedFstShadowIfDefaultValues.
intros Hpde Hparent Hnotnull Hget1 Hget2. 
simpl in *.
assert(HgetParts : getPartitions pageRootPartition
  {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |} = 
  getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
rewrite HgetParts in *. clear HgetParts.
intros.
assert(table <> partition).
    {
    unfold not;intros. apply Hget1 with partition;trivial.
    left;trivial. intuition. }
assert(Hpd :  StateLib.getPd partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getPd partition (memory s)).  
  { intros.    
    apply getPdUpdateMappedPageData;trivial.
     }
assert(Hpdchildnotnull : pd <> pageDefault).
{ unfold partitionDescriptorEntry in *.
rewrite Hpd in *. clear Hpd.
apply pdPartNotNull with partition s;trivial.
apply nextEntryIsPPgetPd;trivial. }
 assert(Hmap : getMappedPage pd
       {|
       currentPartition := currentPartition s;
       memory := add table curidx x (memory s) pageEq idxEq |} va =
       getMappedPage pd s va).
{ apply getMappedPageUpdateMappedPageData;trivial.
apply notConfigTableNotPdconfigTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial.
    
rewrite Hpd in *;clear Hpd.
trivial. }

rewrite Hmap in *. clear Hmap.
assert(Hsh1 :  StateLib.getFstShadow partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getFstShadow partition (memory s)).  
  { intros.    
    apply getFstShadowUpdateMappedPageData;trivial.
     }
rewrite Hsh1 in *.
assert(   sh1<> pageDefault  ).
{ apply sh1PartNotNull with partition s;trivial.
  apply nextEntryIsPPgetFstShadow;trivial. }
assert(Hv1 : getPDFlag sh1 va
    {|
    currentPartition := currentPartition s;
    memory := add table curidx x (memory s) pageEq idxEq |}  = getPDFlag sh1
    va s).
{    
apply getPDFlagUpdateMappedPageData with partition;trivial.
apply nextEntryIsPPgetFstShadow;trivial.
assert(nbLevel> 0) by apply nbLevelNotZero.
replace (S (nbLevel - 1)) with nbLevel by lia.
apply notConfigTableNotSh1configTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial. }
rewrite Hv1.
assert(Hv2 : getVirtualAddressSh1 sh1
    {|
    currentPartition := currentPartition s;
    memory := add table curidx x (memory s) pageEq idxEq |}  va = getVirtualAddressSh1 sh1
     s va).
{ symmetry.    
apply getVirtualAddressSh1UpdateMappedPageData ;trivial.
apply notConfigTableNotSh1configTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial. }
rewrite Hv2.
apply Hget2 with partition  pd;trivial.
rewrite Hpd in *.
trivial. 
Qed.



Lemma wellFormedSndShadowtUpdateMappedPageData table curidx x  s:
noDupPartitionTree s -> 
partitionDescriptorEntry s -> 
parentInPartitionList s -> 
table <> pageDefault -> 
(forall partition : page,
  In partition (getPartitions pageRootPartition s) ->
  partition = table \/ In table (getConfigPagesAux partition s) -> False) ->
wellFormedSndShadow s -> 
wellFormedSndShadow {|  currentPartition := currentPartition s;
        memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros Hnoduptree. 
unfold wellFormedSndShadow.
intros Hpde Hparent Hnotnull Hget1 Hget2. 
simpl in *.
assert(HgetParts : getPartitions pageRootPartition
  {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |} = 
  getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
rewrite HgetParts in *. clear HgetParts.
intros.
assert(table <> partition).
    {
    unfold not;intros. apply Hget1 with partition;trivial.
    left;trivial. intuition. }
assert(Hpd :  StateLib.getPd partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getPd partition (memory s)).  
  { intros.    
    apply getPdUpdateMappedPageData;trivial.
     }
assert(Hpdchildnotnull : pd <> pageDefault).
{ unfold partitionDescriptorEntry in *.
rewrite Hpd in *. clear Hpd. 
assert( exists entry : page, nextEntryIsPP partition idxPageDir entry s 
/\ entry <> pageDefault) as (pdtmp & Hpdtmp & Hnotnul).
apply Hpde;trivial.
left;trivial.
assert( pdtmp = pd).
apply getPdNextEntryIsPPEq with partition s;trivial.
subst.
trivial. }
 assert(Hmap : getMappedPage pd
       {|
       currentPartition := currentPartition s;
       memory := add table curidx x (memory s) pageEq idxEq |} va =
       getMappedPage pd s va).
{ apply getMappedPageUpdateMappedPageData;trivial.
apply notConfigTableNotPdconfigTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial.
    
rewrite Hpd in *;clear Hpd.
trivial. }

rewrite Hmap in *. clear Hmap.
assert(Hsh1 :  StateLib.getSndShadow partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getSndShadow partition (memory s)).  
  { intros.    
    apply getSndShadowUpdateMappedPageData;trivial.
     }
rewrite Hsh1 in *.
assert(   sh2<> pageDefault  ).
{
assert( exists entry : page, nextEntryIsPP partition idxShadow2 entry s 
/\ entry <> pageDefault) as (pdtmp & Hpdtmp & Hnotnul).
apply Hpde;trivial.
do 2 right;left;trivial.
assert( pdtmp = sh2).
apply getSh2NextEntryIsPPEq with partition s;trivial.
subst.
trivial. }
assert(Hv1 : getVirtualAddressSh2 sh2
    {|
    currentPartition := currentPartition s;
    memory := add table curidx x (memory s) pageEq idxEq |} va = getVirtualAddressSh2 sh2
    s va).
    symmetry.
     
apply getVirtualAddressSh2UpdateMappedPageData;trivial.
apply notConfigTableNotSh2configTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial.
rewrite Hv1.
apply Hget2 with partition pg pd;trivial.
rewrite Hpd in *.
trivial. 
Qed.

Lemma wellFormedShadowstUpdateMappedPageData table curidx x  idxroot s:
(idxroot = idxShadow1 \/ idxroot =idxShadow2) -> 
noDupPartitionTree s -> 
partitionDescriptorEntry s -> 
parentInPartitionList s -> 
table <> pageDefault -> 
(forall partition : page,
  In partition (getPartitions pageRootPartition s) ->
  partition = table \/ In table (getConfigPagesAux partition s) -> False) ->
wellFormedShadows idxroot s -> 
wellFormedShadows idxroot {|  currentPartition := currentPartition s;
        memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros Hor.
intros Hnoduptree. 
unfold wellFormedShadows.
intros Hpde Hparent Hnotnull Hconfig Hget2. 
simpl in *.

assert(HgetParts : getPartitions pageRootPartition
  {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |} = 
  getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
rewrite HgetParts in *. clear HgetParts.
intros partition Hpart.
intros.
set (s':=  {|
  currentPartition := _ |}) in *.
  assert(Hind : getIndirection pdroot va nbL stop s' = Some indirection1) by trivial.
assert(table <> partition).
    {
    unfold not;intros. apply Hconfig with partition;trivial.
    left;trivial. intuition. }
assert(Htable :stop <= (nbLevel -1) -> ~ In table (getIndirectionsAux structroot s (S stop))).
intros.
{ assert (Hstop : stop < (nbLevel -1) \/ stop = (nbLevel -1) ) by lia.
  clear H.
  destruct Hstop as [Hlt |  Heq ].
  +
generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig .
destruct Hor as [Hsh1 | Hsh2].
{ subst.
  apply  notConfigTableNotSh1configTableLt with partition; trivial.
  rewrite nextEntryIsPPgetFstShadow in *.
  rewrite <- H0.
  symmetry.
  apply  getFstShadowUpdateMappedPageData;trivial. }
{ subst.
  apply  notConfigTableNotSh2configTableLt with partition; trivial.
  rewrite nextEntryIsPPgetSndShadow in *.
  rewrite <- H0.
  symmetry.
  apply  getSndShadowUpdateMappedPageData;trivial. }
+ subst.

assert(0<nbLevel) by apply nbLevelNotZero.
assert(Hsnbl :  (S (nbLevel - 1)) = nbLevel) by lia.
rewrite Hsnbl.
destruct Hor as  [Hsh1 | Hsh2].
{ subst.
  apply  notConfigTableNotSh1configTable with partition; trivial.
  generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  rewrite nextEntryIsPPgetFstShadow in *.
  rewrite <- H0.
  symmetry.
  apply  getFstShadowUpdateMappedPageData;trivial. }
{ subst.
  apply  notConfigTableNotSh2configTable with partition; trivial.
  generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  rewrite nextEntryIsPPgetSndShadow in *.
  rewrite <- H0.
  symmetry.
  apply  getSndShadowUpdateMappedPageData;trivial. } } 
 assert(Hgetind : exists indirection2 : page, getIndirection structroot va nbL stop s = Some indirection2 /\
        (Nat.eqb pageDefault indirection2) = b).
        apply Hget2  with partition pdroot indirection1;trivial.
    rewrite getPdUpdateMappedPageData in *;trivial.
    destruct Hor as [Hor | Hor]; subst.
    rewrite nextEntryIsPPgetFstShadow in *.
    simpl in *.
    assert(Hsh1 : StateLib.getFstShadow partition (add table curidx x (memory s) pageEq idxEq) = Some structroot)
    by trivial.
    rewrite <- Hsh1.
    symmetry.
    apply getFstShadowUpdateMappedPageData;trivial.
    rewrite nextEntryIsPPgetSndShadow in *.
    simpl in *.
    assert(Hsh1 : StateLib.getSndShadow partition (add table curidx x (memory s) pageEq idxEq) = Some structroot)
    by trivial.
    rewrite <- Hsh1.
    symmetry.
    apply getSndShadowUpdateMappedPageData;trivial.
    { clear Htable.
        assert(Htable :stop <= (nbLevel -1) -> ~ In table (getIndirectionsAux pdroot s (S stop))).
intros.
{ assert (Hstop : stop < (nbLevel -1) \/ stop = (nbLevel -1) ) by lia.
  destruct Hstop as [Hlt |  Heq ].
  +
generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig .
  apply  notConfigTableNotPdconfigTableLt with partition; trivial.
  rewrite <- H.
  symmetry. 
  apply  getPdUpdateMappedPageData;trivial.
+ subst.

assert(0<nbLevel) by apply nbLevelNotZero.
assert(Hsnbl :  (S (nbLevel - 1)) = nbLevel) by lia.
rewrite Hsnbl.
  apply  notConfigTableNotPdconfigTable with partition; trivial.
  generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  rewrite <- H.
  symmetry.
  apply  getPdUpdateMappedPageData;trivial. }
  
assert( getIndirection pdroot va nbL stop s' = getIndirection pdroot va nbL stop s).
{ assert (Hstop3 : stop < (nbLevel -1) \/ stop = (nbLevel -1) \/ stop > (nbLevel -1)) by lia.
  destruct Hstop3 as [Hlt | [ Heq | Hgt]].
  + apply getIndirectionUpdateMappedPageData with nbL;
    trivial. apply Htable. lia.
  + subst.
    apply getIndirectionUpdateMappedPageData with nbL ;trivial.
    apply Htable. lia.
    +
 
  assert(HnbL : Some nbL = StateLib.getNbLevel) by trivial.
assert(Hneww : getIndirection pdroot va nbL stop s' = 
            getIndirection pdroot va nbL nbL s').
    { rewrite Hind.
      symmetry.
      apply getIndirectionStopLevelGT2 with stop; trivial.      
      apply getNbLevelLe in HnbL.
      unfold CLevel in HnbL.
      case_eq (lt_dec (nbLevel - 1) nbLevel); intros ii Hii; rewrite Hii in *. 
      simpl in *.
      destruct nbL.
      simpl in *. lia.
      assert(0 < nbLevel) by apply nbLevelNotZero. 
      lia. }
    rewrite Hind.
    symmetry.
    apply getIndirectionStopLevelGT with nbL; trivial.
    apply getNbLevelLe in HnbL.
    unfold CLevel in HnbL.
    case_eq (lt_dec (nbLevel - 1) nbLevel); intros ii Hii;rewrite Hii in *.
    simpl in *.
    destruct nbL.
    simpl in *. lia.
    assert(0 < nbLevel) by apply nbLevelNotZero. 
    lia.
    rewrite <- Hind.
    rewrite Hneww.
    symmetry.
    apply getIndirectionUpdateMappedPageData with nbL ;trivial.
assert(HnbLevel : S nbL = nbLevel).

apply getNbLevelEq in HnbL.
subst.
rewrite <-  nbLevelEq.
assert(0 < nbLevel) by apply nbLevelNotZero.
lia. 
rewrite HnbLevel. 
 
      apply  notConfigTableNotPdconfigTable with partition; trivial.
      generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      rewrite <- H.
      symmetry.
      apply getPdUpdateMappedPageData;trivial. 
       }
    rewrite <- H5;trivial. }
    destruct Hgetind as (indirection2 & Hgetind & Hdef).
    exists indirection2.
    
    split;trivial.
        
assert( getIndirection structroot va nbL stop s' = getIndirection structroot va nbL stop s).
{ assert (Hstop3 : stop < (nbLevel -1) \/ stop = (nbLevel -1) \/ stop > (nbLevel -1)) by lia.
  destruct Hstop3 as [Hlt | [ Heq | Hgt]].
  + apply getIndirectionUpdateMappedPageData with nbL;
    trivial. apply Htable. lia.
  + subst.
    apply getIndirectionUpdateMappedPageData with nbL ;trivial.
    apply Htable. lia.
  + 
      assert(HnbL : Some nbL = StateLib.getNbLevel) by trivial.
      assert(Hneww : getIndirection structroot va nbL stop s = 
            getIndirection structroot va nbL nbL s).
    { rewrite Hgetind.
      symmetry.
      apply getIndirectionStopLevelGT2 with stop; trivial.
      apply getNbLevelLe in HnbL.
      unfold CLevel in HnbL.
      case_eq (lt_dec (nbLevel - 1) nbLevel); intros ii Hii;
      rewrite Hii in *.
      simpl in *.
      destruct nbL.
      simpl in *. lia.
      assert(0 < nbLevel) by apply nbLevelNotZero. 
      lia. }
    rewrite Hgetind.
    apply getIndirectionStopLevelGT with nbL; trivial.
    
    apply getNbLevelLe in HnbL.
    unfold CLevel in HnbL.
    case_eq (lt_dec (nbLevel - 1) nbLevel); intros ii Hii;
      rewrite Hii in *.
    simpl in *.
    destruct nbL.
    simpl in *. lia.
    assert(0 < nbLevel) by apply nbLevelNotZero. 
    lia.
    rewrite <- Hgetind.
    rewrite Hneww.
    apply getIndirectionUpdateMappedPageData with nbL ;trivial.
    assert(HnbLevel : (S nbL) = nbLevel).
{ apply getNbLevelEq in HnbL.
  unfold CLevel in HnbL.
  case_eq (lt_dec (nbLevel - 1) nbLevel);intros ii Hii;
      rewrite Hii in *.
  simpl in *.
  destruct nbL.
  simpl in *.
  inversion HnbL. lia.
  assert(0 < nbLevel) by apply nbLevelNotZero. 
  lia. }
    rewrite HnbLevel.
   destruct Hor as [Hsh1 | Hsh2].
    (* { subst.
      apply  notConfigTableNotPdconfigTable with partition; trivial.
      generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      apply nextEntryIsPPgetPd; trivial. }
     *) 
     { subst.
      apply  notConfigTableNotSh1configTable with partition; trivial.
      generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      rewrite nextEntryIsPPgetFstShadow in *.
  rewrite <- H0.
  symmetry.
  apply  getFstShadowUpdateMappedPageData;trivial. }
    { subst.
      apply  notConfigTableNotSh2configTable with partition; trivial.
      generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      apply nextEntryIsPPgetSndShadow; trivial.
      rewrite nextEntryIsPPgetSndShadow in *.
  rewrite <- H0.
  symmetry.
  apply  getSndShadowUpdateMappedPageData;trivial. } }
  rewrite H5. trivial. 

Qed.

Lemma isDerivedUpdateMappedPageData  table curidx x s parent va :
(forall subpartition : page, 
In subpartition (getPartitions pageRootPartition s) ->
 ~ In table (getConfigPages subpartition s)) ->
partitionDescriptorEntry s -> 
In parent (getPartitions pageRootPartition s) -> 
table <> parent -> 
isDerived parent va s -> 
isDerived parent va 
       {| currentPartition := currentPartition s; 
       memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
unfold isDerived.
intros.
simpl.
rewrite getFstShadowUpdateMappedPageData;trivial.
case_eq(StateLib.getFstShadow parent (memory s) );[intros sh1 Hsh1 | intros Hsh1]
; rewrite Hsh1 in *;trivial.
assert(Hvirt : getVirtualAddressSh1 sh1 
{| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |}
va = getVirtualAddressSh1 sh1 s va).
symmetry.
apply getVirtualAddressSh1UpdateMappedPageData;trivial.
apply notConfigTableNotSh1configTable with parent;trivial.
unfold getConfigPages in *.
apply H in H1.
simpl in *.
intuition.
  { unfold partitionDescriptorEntry in *.
    assert( exists entry : page, nextEntryIsPP parent idxShadow1 entry s 
    /\ entry <> pageDefault) as (shadow1 & Hshadow1 & Hnotnul). 
    apply H0;trivial.
    right;left;trivial.
    assert(shadow1 = sh1).
    apply getSh1NextEntryIsPPEq with parent s;trivial.
    subst.
    trivial. }
rewrite Hvirt;trivial.
Qed.
       
Lemma physicalPageNotDerivedUpdateMappedPageData table curidx x s :
noDupPartitionTree s -> 
table <> pageDefault-> 
partitionDescriptorEntry s -> 
(forall subpartition : page, 
In subpartition (getPartitions pageRootPartition s) ->
 ~ In table (getConfigPages subpartition s)) ->
physicalPageNotDerived s ->
physicalPageNotDerived
  {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros Hnoduptree.
unfold physicalPageNotDerived.
intros.  
simpl in *.
assert(Htablenotpart : forall part , In part (getPartitions pageRootPartition s) ->
table <> part).
  { intros.
    apply H1 in H10;intuition. }
assert(Hmult : In pageRootPartition (getPartitions pageRootPartition s)).
  { unfold getPartitions;
    destruct nbPage;simpl;left;trivial. }  
assert(Hpart : getPartitions pageRootPartition s =
getPartitions pageRootPartition
          {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} ).
  { symmetry.
    apply getPartitionsUpdateMappedPageData;trivial. }
rewrite <- Hpart in *.
assert(Hconfig1 : ~ In table (getConfigPages parent s)).
  { apply H1 in H3.
    intuition. }
assert(Hconfig2 :  table <> parent).
  { apply H1 in H3.
    intuition. }
assert(Hchild : getChildren parent
          {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |}
          = getChildren parent s).
  { apply getChildrenUpdateMappedPageData;trivial. }
rewrite Hchild in *.
assert(Hchildpart : In child (getPartitions pageRootPartition s)).
  { apply childrenPartitionInPartitionList with parent;trivial. }
assert(Hconfig3 :  table <> child).
  { apply H1 in Hchildpart.
    intuition. }
assert(Hpd :  StateLib.getPd parent 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getPd parent (memory s)).  
  { intros.    
    apply getPdUpdateMappedPageData;trivial. }
rewrite Hpd in *;clear Hpd.
  assert(Hpd :  StateLib.getPd child 
(add table curidx x (memory s) pageEq idxEq) = 
StateLib.getPd child (memory s)).
  { intros.    
    apply getPdUpdateMappedPageData;trivial. }
rewrite Hpd in *;clear Hpd.
assert(Hpdchildnotnull : pdChild <> pageDefault).
{ unfold partitionDescriptorEntry in *.
assert( exists entry : page, nextEntryIsPP child idxPageDir entry s 
/\ entry <> pageDefault) as (pd & Hpd & Hnotnul).
apply H0;trivial.
left;trivial.
assert(pd = pdChild).
apply getPdNextEntryIsPPEq with child s;trivial.
subst.
trivial. }
assert(Hconfig4 : ~ In table (getIndirectionsAux pdChild s nbLevel)).
  { apply notConfigTableNotPdconfigTable with child;trivial.
    apply H1 in Hchildpart.
    intuition. }
assert(Hgetmapped : getMappedPage pdChild
       {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} vaInChild =
        getMappedPage pdChild s vaInChild).
apply  getMappedPageUpdateMappedPageData ;trivial.      
rewrite Hgetmapped in *. clear Hgetmapped.
assert(Hpdparent : pdParent <> pageDefault).
  { unfold partitionDescriptorEntry in *.
    assert( exists entry : page, nextEntryIsPP parent idxPageDir entry s 
    /\ entry <> pageDefault) as (pd & Hpd & Hnotnul). 
    apply H0;trivial.
    left;trivial.
    assert(pd = pdParent).
    apply getPdNextEntryIsPPEq with parent s;trivial.
    subst.
    trivial. } 
assert(Hgetmapped : getMappedPage pdParent
       {| currentPartition := currentPartition s;
        memory := add table curidx x (memory s) pageEq idxEq |} va =
        getMappedPage pdParent s va).
  { apply  getMappedPageUpdateMappedPageData ;trivial.
    apply notConfigTableNotPdconfigTable with parent;trivial.
    apply H1 in H3.
    intuition. }
rewrite Hgetmapped in *. clear Hgetmapped. 
assert(~ isDerived parent va s).
unfold not;intros Hfalse;contradict H5.
apply isDerivedUpdateMappedPageData;trivial.
apply H2 with  parent va pdParent child pdChild vaInChild;trivial.
Qed.


Lemma isPresentNotDefaultIffUpdateMappedPageData table curidx x s:
match x with
| PE _ => isPresentNotDefaultIff {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |}
| _ => True
end -> 
isPresentNotDefaultIff s -> 
isPresentNotDefaultIff {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros.
unfold isPresentNotDefaultIff in *.
simpl in *.
unfold StateLib.readPresent.
unfold StateLib.readPhyEntry.
simpl in *.
case_eq x; intros * Hii; rewrite Hii in *; try assumption ;
intros table0 idx0 ;
case_eq(beqPairs (table, curidx) (table0, idx0) pageEq idxEq) ;

try (
  intros * Haa ;
  split; 
  intros * Hi;
  now contradict Hi
);
  intros * Haa ;
  assert(lookup table0 idx0 (removeDup table curidx (memory s) pageEq idxEq) pageEq idxEq
= lookup table0 idx0  (memory s) pageEq idxEq);

try (
  apply removeDupIdentity;
  apply beqPairsFalse in Haa;
  intuition
);
  rewrite H1;
  unfold StateLib.readPresent in *;
  unfold StateLib.readPhyEntry in *;
  trivial.
Qed.

Lemma isPresentNotDefaultIffRightValue table curidx s :
isPresentNotDefaultIff s -> 
isPresentNotDefaultIff
  {|
  currentPartition := currentPartition s;
  memory := add table curidx
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := pageDefault |}) (memory s) pageEq idxEq |}.
Proof.
intros.
unfold isPresentNotDefaultIff in *.
simpl.
intros.
unfold StateLib.readPresent in *.
unfold StateLib.readPhyEntry in *.
simpl.
case_eq( beqPairs (table, curidx) (table0, idx) pageEq idxEq);intros.
simpl;trivial.
split;reflexivity.
assert(lookup table0 idx (removeDup table curidx (memory s) pageEq idxEq) pageEq idxEq =
lookup table0 idx (memory s) pageEq idxEq).
apply removeDupIdentity.
apply beqPairsFalse in H0.
intuition.
rewrite H1.
apply H.
Qed.

Lemma  isWellFormedFstShadowUpdateMappedPageData table1 table2 level  x  idx s :
table2 <> table1 -> 
isWellFormedFstShadow level table1 s  -> 
isWellFormedFstShadow level table1  {|
currentPartition := currentPartition s;
memory := Lib.add table2 idx x(memory s) pageEq idxEq |}.
Proof.

(*  assert (Htable :  isWellFormedSndShadow level phySh2Child s)
by intuition.
clear H IHn. *)
unfold isWellFormedFstShadow in *.
simpl.
intros Hnoteq Htable. 
destruct Htable as [(HnbL & Htable) | (HnbL & Htable)].
left;split;trivial.
intros.
generalize (Htable idx0); clear Htable; intros Htable.
destruct Htable as (Htable1 & Htable2).
rewrite <- Htable1.
rewrite <- Htable2.
split. 
symmetry.
apply readPhyEntryUpdateMappedPageData; trivial.
symmetry.
apply readPresentUpdateMappedPageData;trivial.
right.
split;trivial.
intros.
destruct Htable with idx0 as (Htable1 & Htable2).
rewrite <- Htable1.
rewrite <- Htable2.
split. 
apply readVirEntryUpdateMappedPageData;trivial.
apply readPDflagUpdateMappedPageData;trivial.
unfold not;intros;subst; now contradict Hnoteq.
Qed.

Lemma  isWellFormedSndShadowUpdateMappedPageData table1 table2 level  x  idx s :
table2 <> table1 -> 
isWellFormedSndShadow level table1 s  -> 
isWellFormedSndShadow level table1  {|
currentPartition := currentPartition s;
memory := Lib.add table2 idx x(memory s) pageEq idxEq |}.
Proof.
unfold isWellFormedSndShadow in *.
simpl.
intros Hnoteq Htable. 
destruct Htable as [(HnbL & Htable) | (HnbL & Htable)].
left;split;trivial.
intros.
generalize (Htable idx0); clear Htable; intros Htable.
destruct Htable as (Htable1 & Htable2).
rewrite <- Htable1.
rewrite <- Htable2.
split. 
symmetry.
apply readPhyEntryUpdateMappedPageData; trivial.
symmetry.
apply readPresentUpdateMappedPageData;trivial.
right.
split;trivial.
intros.
rewrite <- Htable with idx0.
apply readVirtualUpdateMappedPageData;trivial.
Qed.

Lemma writeAccessibleRecPostCondUpdateMappedPageData table idx s x currentPart phy: 
let s' := {|
  currentPartition := currentPartition s;
  memory := add table idx
             x(memory s) pageEq idxEq |} in 
consistency s ->  
In currentPart (getPartitions pageRootPartition s) -> 
(Nat.eqb pageDefault table) = false -> 
(forall partition1 : page,
In partition1 (getPartitions pageRootPartition s) ->
partition1 = table \/ In table (getConfigPagesAux partition1 s) -> False) -> 
(forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phy (getAccessibleMappedPages partition s)) -> 
forall partition : page,
In partition (getAncestors currentPart s') -> 
~ In phy (getAccessibleMappedPages partition s'). 
Proof.
intros s' Hcons Hcurpart Htable Hnotconf HpartS partition Hpartition.
unfold s' in Hpartition;
unfold propagatedProperties in *; 
unfold consistency in *.
rewrite <- getAncestorsUpdateMappedPageData in *; trivial.
{ unfold s'.
 rewrite getAccessibleMappedPagesUpdateMappedPageData;trivial.
 apply HpartS; trivial.
 intuition.
 apply ancestorInPartitionTree with currentPart;
 intuition. }
intuition.
Qed.



Lemma kernelDataIsolationUpdateMappedPageData table curidx x s nbLgen:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
kernelDataIsolation s -> 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
consistency s -> 
 Some nbLgen = StateLib.getNbLevel -> 
kernelDataIsolation s'. 
Proof.
intro.
intros Hiso.
intros.
unfold kernelDataIsolation, initPEntryTablePreconditionToPropagatePrepareProperties , consistency in *.
intros partition1 partition2 Hpart1 Hpart2.
intuition.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
 { unfold s'.
   apply getPartitionsUpdateMappedPageData ; trivial.
   + unfold getPartitions.
     destruct nbPage;simpl;left;trivial.
   + intros. subst. 
      assert(Hfalse : (Nat.eqb pageDefault table) = false) by trivial.
     apply beq_nat_false in Hfalse.
     unfold not; intros.
     apply Hfalse.
     subst;trivial.
}
rewrite Hpartions in *.
assert(Hpde : partitionDescriptorEntry s).
{ unfold consistency in *; intuition. }
assert (Hallmap: getMappedPages partition1 s' = getMappedPages partition1 s).
apply getMappedPagesUpdateMappedPageData with nbLgen; trivial.
assert (Haccss : getAccessibleMappedPages partition1 s' = 
                 getAccessibleMappedPages partition1 s).
apply getAccessibleMappedPagesUpdateMappedPageData; trivial.
rewrite Haccss.
unfold s'.
rewrite getConfigPagesUpdateMappedPageData.
apply Hiso; trivial.
assert(Hconfig : forall partition : page,
                   In partition (getPartitions pageRootPartition s) ->
                   partition = table \/ 
                   In table (getConfigPagesAux partition s) -> False) by trivial.
unfold not.
apply Hconfig; trivial.
Qed.

Lemma partitionsIsolationUpdateMappedPageData table curidx x s nbLgen:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
partitionsIsolation s -> 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
consistency s -> 
Some nbLgen = StateLib.getNbLevel -> 
partitionsIsolation s'. 
Proof.
intros s' Hiso (Hpre1 & Hpre2).
intros.
unfold consistency in *;intuition.
unfold partitionsIsolation, initPEntryTablePreconditionToPropagatePrepareProperties in * .
intros.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
{ unfold s'.
 apply getPartitionsUpdateMappedPageData ; trivial.
 + unfold getPartitions.
   destruct nbPage;simpl;left;trivial.
 + assert(Hfalse : (Nat.eqb pageDefault table) = false) by trivial.
   apply beq_nat_false in Hfalse.
   unfold not; intros.
   apply Hfalse.
   subst;trivial. }
rewrite Hpartions in *.
unfold getUsedPages.
assert (Hchild1 : In child1 (getChildren parent s')) by trivial.
assert (Hchild2 : In child2 (getChildren parent s')) by trivial.
assert (Hchild1mult : In child1 (getPartitions pageRootPartition s)).
{ apply childrenPartitionInPartitionList with parent; trivial.
 unfold s' in Hchild1, Hchild2.
 rewrite getChildrenUpdateMappedPageData in Hchild1; fold s'; trivial.
 assert(Hfalse : (Nat.eqb pageDefault table) = false) by trivial.
 apply beq_nat_false in Hfalse.
unfold not; intros.
apply Hfalse.
subst;trivial.
unfold getConfigPages in *.
simpl.
unfold not.
apply Hpre1; trivial.
assert(Hparent : In parent (getPartitions pageRootPartition s)); trivial.
generalize (Hpre1 parent Hparent); clear Hpre1; intros Hpre1. unfold not.
intros. apply Hpre1.
subst.
left; trivial. }
assert (Hchild2mult : In child2 (getPartitions pageRootPartition s)).
{ apply childrenPartitionInPartitionList with parent; trivial.
 unfold s' in Hchild1, Hchild2.
 rewrite getChildrenUpdateMappedPageData in Hchild2; fold s'; trivial.
 assert(Hfalse : (Nat.eqb pageDefault table) = false) by trivial.
 apply beq_nat_false in Hfalse.
 unfold not; intros.
 apply Hfalse.
 subst;trivial.
unfold getConfigPages.
simpl.
unfold not.
apply Hpre1; trivial.
assert(Hparent : In parent (getPartitions pageRootPartition s)); trivial.
generalize (Hpre1 parent Hparent); clear Hpre1; intros Hpre1. unfold not.
intros. apply Hpre1.
subst.
left; trivial. }    
assert (Hmapped : getMappedPages child1 s' = getMappedPages child1 s).
apply getMappedPagesUpdateMappedPageData with nbLgen; trivial.
unfold consistency in *; intuition.
rewrite Hmapped; clear Hmapped.
 
assert (Hmapped : getMappedPages child2 s' = getMappedPages child2 s).
apply getMappedPagesUpdateMappedPageData with nbLgen; trivial.
unfold consistency in *; intuition.
rewrite Hmapped.
unfold s'.
rewrite getConfigPagesUpdateMappedPageData.
rewrite getConfigPagesUpdateMappedPageData.
unfold getUsedPages in Hiso.
apply Hiso with parent; trivial.
unfold s' in Hchild1.
rewrite getChildrenUpdateMappedPageData in Hchild1; trivial.
{ assert(Hfalse : (Nat.eqb pageDefault table) = false) by trivial.
  apply beq_nat_false in Hfalse.
  unfold not; intros.
  apply Hfalse.
  subst;trivial. }
{  assert(Hconfig : forall partition : page,
               In partition (getPartitions pageRootPartition s) ->
               partition = table \/ 
               In table (getConfigPagesAux partition s) -> False) by trivial.
         unfold not. apply Hconfig; trivial. }
{ assert(Hconfig : forall partition : page,
    In partition (getPartitions pageRootPartition s) ->
    partition = table \/ 
    In table (getConfigPagesAux partition s) -> False) by trivial.
    assert (Hparent : In parent (getPartitions pageRootPartition s)) by trivial.
     generalize (Hconfig parent Hparent); clear Hconfig; intros Hconfig.
        apply Classical_Prop.not_or_and in Hconfig.
        destruct Hconfig as (Hi1 & Hi2).
         unfold not.
        intros Hfalse. rewrite Hfalse in Hi1.
        now contradict Hi1. }
{ unfold s' in Hchild2.
  rewrite getChildrenUpdateMappedPageData in Hchild2; trivial.
   { assert(Hfalse : (Nat.eqb pageDefault table) = false) by trivial.
     apply beq_nat_false in Hfalse.
     unfold not; intros.
     apply Hfalse.
     subst;trivial. }
   { assert(Hconfig : forall partition : page,
                   In partition (getPartitions pageRootPartition s) ->
                   partition = table \/ 
                   In table (getConfigPagesAux partition s) -> False) by trivial.
     unfold not. apply Hconfig; trivial. }
   { assert(Hconfig : forall partition : page,
        In partition (getPartitions pageRootPartition s) ->
        partition = table \/ 
        In table (getConfigPagesAux partition s) -> False) by trivial.
     assert (Hparent : In parent (getPartitions pageRootPartition s)) by trivial.
     generalize (Hconfig parent Hparent); clear Hconfig; intros Hconfig.
     apply Classical_Prop.not_or_and in Hconfig.
     destruct Hconfig as (Hi1 & Hi2).
     unfold not.
     intros Hfalse. rewrite Hfalse in Hi1.
     now contradict Hi1. } }
assert (Hconfig : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = table \/ 
      In table (getConfigPagesAux partition s) -> False) by trivial.
unfold not. apply Hconfig; trivial.
  assert (Hconfig : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = table \/ 
      In table (getConfigPagesAux partition s) -> False) by trivial.
unfold not. apply Hconfig; trivial.
Qed.

Lemma verticalSharingUpdateMappedPageData table curidx x s nbLgen:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
verticalSharing s -> 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
consistency s -> 
Some nbLgen = StateLib.getNbLevel -> 
verticalSharing s'. 
Proof.
intros s' Hvs.
intros.
unfold consistency, initPEntryTablePreconditionToPropagatePrepareProperties in *;intuition.
unfold verticalSharing in *.
intros parent child Hparentmult Hchild.
intuition.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
   { unfold s'.
     apply getPartitionsUpdateMappedPageData ; trivial.
     + unfold getPartitions.
       destruct nbPage;simpl;left;trivial.
     + assert(Hfalse : (Nat.eqb pageDefault table) = false) by trivial.
       apply beq_nat_false in Hfalse.
       unfold not; intros.
       apply Hfalse.
       subst;trivial. }
rewrite Hpartions in *; clear Hpartions.
assert(Hpde : partitionDescriptorEntry s) by trivial.
assert (Hchildmult : In child (getPartitions pageRootPartition s)).
{ apply childrenPartitionInPartitionList with parent; trivial.
  unfold s' in Hchild.
  rewrite getChildrenUpdateMappedPageData in Hchild; fold s'; trivial.
  assert(Hfalse : (Nat.eqb pageDefault table) = false) by trivial.
  apply beq_nat_false in Hfalse.
  unfold not; intros.
  apply Hfalse.
  subst;trivial.
  assert(Hconfig : forall partition : page,
  In partition (getPartitions pageRootPartition s) ->
  partition = table \/ In table (getConfigPagesAux partition s) -> False) by trivial.
  unfold getConfigPages.
  simpl.
  unfold not.
  apply Hconfig; trivial.
  assert(Hconfig : forall partition : page,
  In partition (getPartitions pageRootPartition s) ->
  partition = table \/ In table (getConfigPagesAux partition s) -> False) by trivial.
  assert(Hparent : In parent (getPartitions pageRootPartition s)); trivial.
  generalize (Hconfig parent Hparent); clear Hconfig; intros Hconfig. unfold not.
  intros. apply Hconfig.
  subst.
  left; trivial. }
assert (Hmapped : getMappedPages parent s' = getMappedPages parent s).
apply getMappedPagesUpdateMappedPageData with nbLgen; trivial.
rewrite Hmapped; clear Hmapped.     
unfold getUsedPages.
assert (Hmapped : getMappedPages child s' = getMappedPages child s).
apply getMappedPagesUpdateMappedPageData with nbLgen; trivial.      
rewrite Hmapped; clear Hmapped.    
unfold s'.
rewrite getConfigPagesUpdateMappedPageData.
{ apply Hvs; trivial.
unfold s' in Hchild.
rewrite getChildrenUpdateMappedPageData in Hchild; fold s'; trivial.
{ assert(Hfalse : (Nat.eqb pageDefault table) = false) by trivial.
   apply beq_nat_false in Hfalse.
   unfold not; intros.
   apply Hfalse.
   subst;trivial. }
 { assert(Hconfig : forall partition : page,
                 In partition (getPartitions pageRootPartition s) ->
                 partition = table \/ 
                 In table (getConfigPagesAux partition s) -> False) by trivial.
   unfold not. apply Hconfig; trivial. }
 { assert(Hconfig : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = table \/ 
      In table (getConfigPagesAux partition s) -> False) by trivial.
   assert (Hparent : In parent (getPartitions pageRootPartition s)) by trivial.
   generalize (Hconfig parent Hparent); clear Hconfig; intros Hconfig.
   apply Classical_Prop.not_or_and in Hconfig.
   destruct Hconfig as (Hi1 & Hi2).
   unfold not.
   intros Hfalse. rewrite Hfalse in Hi1.
   now contradict Hi1. } }
 { assert(Hconfig : forall partition : page,
                 In partition (getPartitions pageRootPartition s) ->
                 partition = table \/ 
                 In table (getConfigPagesAux partition s) -> False) by trivial.
   unfold not. apply Hconfig; trivial. }
Qed.

Set Nested Proofs Allowed. 
Lemma   noDupMappedPagesListUpdateMappedPageContent table curidx x s nbLgen:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
Some nbLgen = StateLib.getNbLevel -> 
consistency s -> 
noDupMappedPagesList s'.
Proof.
intros s' (Hpre1 & Hpre2).
intros.
unfold consistency in *;intuition.
assert(Hnodup : noDupMappedPagesList s ) by trivial.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
{ unfold s'.
 apply getPartitionsUpdateMappedPageData ; intuition.
 + unfold getPartitions.
   destruct nbPage;simpl;left;trivial.
 + assert(Hfalse : (Nat.eqb pageDefault table) = false) by intuition.
   apply beq_nat_false in Hfalse.
   unfold not; intros.
   apply Hfalse.
   subst;trivial. }
    unfold noDupMappedPagesList in *; intros.
    rewrite Hpartions in *.
    assert (Hmapped : getMappedPages partition s' = getMappedPages partition s).
    apply getMappedPagesUpdateMappedPageData with nbLgen; trivial.
    rewrite Hmapped.
    apply Hnodup; trivial.
Qed.
 
Lemma   noDupConfigPagesListUpdateMappedPageContent table curidx x s nbLgen:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
Some nbLgen = StateLib.getNbLevel -> 
consistency s -> 
noDupConfigPagesList s'.
Proof.
Proof.
intros s' (Hconfig & Hpre2).
intros.
unfold consistency in *;intuition.
assert(Hnodup: noDupConfigPagesList s ) by trivial.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
{ unfold s'.
 apply getPartitionsUpdateMappedPageData ; intuition.
 + unfold getPartitions.
   destruct nbPage;simpl;left;trivial.
 + assert(Hfalse : (Nat.eqb pageDefault table) = false) by intuition.
   apply beq_nat_false in Hfalse.
   unfold not; intros.
   apply Hfalse.
   subst;trivial. }
unfold noDupConfigPagesList in *; intros.
rewrite Hpartions in *.
assert(Hpart : In partition (getPartitions pageRootPartition s)).
intuition.
assert(table <> partition).
{ unfold not;intros.
subst. 
intuition.
apply Hconfig in Hpart.
now contradict Hpart.
left;trivial. }
assert( Heq : getConfigPages partition s = getConfigPages partition 
    {| currentPartition :=  currentPartition s;
       memory := add table curidx x (memory s) pageEq idxEq  |}).
{ unfold getConfigPages . f_equal.
unfold getConfigPagesAux; simpl.
assert(Hpd : StateLib.getPd partition (add table curidx x (memory s) pageEq idxEq)  =
    StateLib.getPd partition (memory s)).
{ apply getPdUpdateMappedPageData;trivial. }
rewrite Hpd in *. clear Hpd.
assert(Hpd : StateLib.getFstShadow partition (add table curidx x (memory s) pageEq idxEq)  =
    StateLib.getFstShadow partition (memory s)).
{ apply getFstShadowUpdateMappedPageData;trivial. }
rewrite Hpd in *. clear Hpd.
assert(Hpd : StateLib.getSndShadow partition (add table curidx x (memory s) pageEq idxEq)  =
    StateLib.getSndShadow partition (memory s)).
{ apply getSndShadowUpdateMappedPageData;trivial. }
rewrite Hpd in *. clear Hpd.
assert(Hpd : StateLib.getConfigTablesLinkedList partition (add table curidx x (memory s) pageEq idxEq)  =
    StateLib.getConfigTablesLinkedList partition (memory s)).
{ apply getTrdShadowUpdateMappedPageData;trivial. }
rewrite Hpd in *. clear Hpd.
case_eq (StateLib.getPd partition (memory s) );intros; trivial. 
case_eq ( StateLib.getFstShadow partition (memory s));intros; trivial.
case_eq ( StateLib.getSndShadow partition (memory s));intros; trivial.
case_eq(  StateLib.getConfigTablesLinkedList partition (memory s) );intros; trivial.
unfold getIndirections.
rewrite  getIndirectionsAuxUpdateMappedPageData.     
rewrite  getIndirectionsAuxUpdateMappedPageData.
rewrite  getIndirectionsAuxUpdateMappedPageData. 
rewrite getLLPagesUpdateMappedPageData;trivial.
{ apply notConfigTableNotListconfigTable with partition;trivial.
  generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
unfold not.
intros.
apply Hconfig.
right; trivial. }
{ subst.
apply  notConfigTableNotSh2configTable with partition; trivial.
generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
unfold not.
intros.
apply Hconfig.
right; trivial. }
{ subst.
apply  notConfigTableNotSh1configTable with partition; trivial.
generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
unfold not.
intros.
apply Hconfig.
right; trivial. }
{ subst.
apply  notConfigTableNotPdconfigTable with partition; trivial.      
generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
unfold not.
intros.
apply Hconfig.
right; trivial. } }
unfold s'.
rewrite <- Heq.
apply Hnodup;trivial.
Qed.

Lemma   parentInPartitionListUpdateMappedPageContent table curidx x s nbLgen:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
Some nbLgen = StateLib.getNbLevel -> 
consistency s -> 
parentInPartitionList s'.
Proof.
Proof.
intros s' (Hconfig & Hpre2).
intros.
unfold consistency in *;intuition.
assert(Hnotpart : parentInPartitionList s ) by trivial.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
{ unfold s'.
 apply getPartitionsUpdateMappedPageData ; intuition.
 + unfold getPartitions.
   destruct nbPage;simpl;left;trivial.
 + assert(Hfalse : (Nat.eqb pageDefault table) = false) by intuition.
   apply beq_nat_false in Hfalse.
   unfold not; intros.
   apply Hfalse.
   subst;trivial. }
unfold parentInPartitionList in *.
    intros.
    rewrite Hpartions in *.
    assert ( nextEntryIsPP partition idxParentDesc parent s).
    rewrite nextEntryIsPPUpdateMappedPageData; trivial.
    unfold s' in *; eassumption.
    apply Hconfig.
    trivial.
    apply Hnotpart with partition;trivial.
Qed.
Lemma   accessibleVAIsNotPartitionDescriptorUpdateMappedPageContent table curidx x s nbLgen:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
Some nbLgen = StateLib.getNbLevel -> 
consistency s -> 
accessibleVAIsNotPartitionDescriptor s'.
Proof.
Proof.
intros s' (Hconfig & Hfalse).
intros.
unfold consistency in *;intuition.
assert(Hnotpart: accessibleVAIsNotPartitionDescriptor s ) by trivial.
assert(Hpde: partitionDescriptorEntry s) by trivial.
unfold s'.
unfold  accessibleVAIsNotPartitionDescriptor in *.
intros.
cbn in *.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
{ unfold s'.
 apply getPartitionsUpdateMappedPageData ; intuition.
 + unfold getPartitions.
   destruct nbPage;simpl;left;trivial.
 +   apply beq_nat_false in Hfalse.
   unfold not; intros.
   apply Hfalse.
   subst;trivial. }
unfold s' in Hpartions.
rewrite Hpartions in *.
assert(table <> partition).
{ unfold not;intros.
  subst.
      assert(Hpart : In partition (getPartitions pageRootPartition s)).
 intuition.

   apply Hconfig in Hpart.
  now contradict Hpart.
  left;trivial. }
rewrite getFstShadowUpdateMappedPageData in *;trivial.
assert(Hpd : StateLib.getPd partition (add table curidx x (memory s) pageEq idxEq)  =
          StateLib.getPd partition (memory s)).
    apply getPdUpdateMappedPageData;trivial.
    rewrite Hpd in *.
assert(Hacc : getAccessibleMappedPage pd
   {|
   currentPartition := currentPartition s;
   memory := add table curidx x (memory s) pageEq idxEq |} va =
   getAccessibleMappedPage pd s va).  
{ apply getAccessibleMappedPageUpdateMappedPageData ;trivial.
  + apply beq_nat_false in Hfalse.
    unfold not; intros.
    apply Hfalse.
    subst;trivial.
  + unfold consistency in *.
    unfold partitionDescriptorEntry in Hpde.
        assert(Hpart : In partition (getPartitions pageRootPartition s)).
 intuition.

    apply Hpde  with partition idxPageDir in Hpart; clear Hpde.
    destruct Hpart as (_ & _ & entrypd & Hpp & Hnotnul).
    assert (Heq : entrypd = pd).
    apply getPdNextEntryIsPPEq with partition s; trivial.
    rewrite <- Heq; assumption.
   left; trivial.
  +     assert(Hpart : In partition (getPartitions pageRootPartition s)).
 intuition.

generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
        apply Classical_Prop.not_or_and in Hconfig.
        destruct Hconfig as (Hi1 & Hi2).
        apply notConfigTableNotPdconfigTable with partition; trivial. }
rewrite Hacc in *.
rewrite  getPDFlagUpdateMappedPageData with  partition table curidx  sh1 va x s; trivial.
apply Hnotpart with partition pd page; trivial.
apply nextEntryIsPPgetFstShadow;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
replace (S (nbLevel - 1)) with nbLevel by lia.
apply notConfigTableNotSh1configTable with partition;trivial.
unfold not; intros.
apply Hconfig with partition;trivial.
right; assumption.
Qed.
Lemma  accessibleChildPageIsAccessibleIntoParentUpdateMappedPageContent table curidx x s nbLgen:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
Some nbLgen = StateLib.getNbLevel -> 
consistency s -> 
accessibleChildPageIsAccessibleIntoParent s'.
Proof.
Proof.
intros s' (Hconfig & Hfalse).
intros.
unfold consistency in *;intuition.
assert(Hpde: partitionDescriptorEntry s) by trivial.
unfold s'.
unfold  accessibleVAIsNotPartitionDescriptor in *.
intros.
cbn in *.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
{ unfold s'.
 apply getPartitionsUpdateMappedPageData ; intuition.
 + unfold getPartitions.
   destruct nbPage;simpl;left;trivial.
 +   apply beq_nat_false in Hfalse.
   unfold not; intros.
   apply Hfalse.
   subst;trivial. }
(** accessibleChildPageIsAccessibleIntoParent *)
assert(Haccess : accessibleChildPageIsAccessibleIntoParent s) by trivial.
unfold s'.
unfold accessibleChildPageIsAccessibleIntoParent in *.
intros partition va pd accessiblePage.
intros Hpart Hpd Haccesspage .
unfold s' in *.
rewrite Hpartions in *.
simpl in *.
 assert(table <> partition).
{ unfold not;intros.
  subst.
   apply Hconfig in Hpart.
  now contradict Hpart.
  left;trivial. }
 assert(Hpdeq : StateLib.getPd partition (add table curidx x (memory s) pageEq idxEq)  =
          StateLib.getPd partition (memory s)).
    apply getPdUpdateMappedPageData;trivial.
    rewrite Hpdeq in *. clear Hpdeq.
 assert(Hacc : getAccessibleMappedPage pd
   {|
   currentPartition := currentPartition s;
   memory := add table curidx x (memory s) pageEq idxEq |} va =
   getAccessibleMappedPage pd s va).  
{ apply getAccessibleMappedPageUpdateMappedPageData ;trivial.
  + apply beq_nat_false in Hfalse.
    unfold not; intros.
    apply Hfalse.
    subst;trivial.
  + unfold consistency in *.
    unfold partitionDescriptorEntry in Hpde.
    apply Hpde  with partition idxPageDir in Hpart; clear Hpde.
    destruct Hpart as (_ & _ & entrypd & Hpp & Hnotnul).
    assert (Heq : entrypd = pd).
    apply getPdNextEntryIsPPEq with partition s; trivial.
    rewrite nextEntryIsPPgetPd in *.
    subst. assumption.
   left; trivial.
  + generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
        apply Classical_Prop.not_or_and in Hconfig.
        destruct Hconfig as (Hi1 & Hi2).
        apply notConfigTableNotPdconfigTable with partition; trivial.    }
  rewrite Hacc in *.
intuition.
rewrite <- isAccessibleMappedPageInParentUpdateMappedPageData
with partition
 va accessiblePage table curidx x s;trivial.
unfold accessibleChildPageIsAccessibleIntoParent in *.
apply Haccess with pd;trivial.
assert(Hnotnull : (Nat.eqb pageDefault table) = false) by trivial.
unfold not;intros Hii.
rewrite Hii in Hnotnull.
apply beq_nat_false in Hnotnull.
now contradict Hnotnull.
Qed.
Lemma  noCycleInPartitionTreeUpdateMappedPageContent table curidx x s nbLgen:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
Some nbLgen = StateLib.getNbLevel -> 
consistency s -> 
noCycleInPartitionTree s'.
Proof.
intros s' (Hconfig & Hfalse).
intros.
 unfold consistency in *.
     assert(Hdiff : noCycleInPartitionTree s) by intuition.
    unfold noCycleInPartitionTree in *.
    intros parent partition Hparts Hparentpart.
    simpl in *.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
{ unfold s'.
 apply getPartitionsUpdateMappedPageData ; intuition.
 + unfold getPartitions.
   destruct nbPage;simpl;left;trivial.
 +   apply beq_nat_false in Hfalse.
   unfold not; intros.
   apply Hfalse.
   subst;trivial. }   
    
    rewrite Hpartions in *. clear Hpartions.
    assert(HgetParent : getAncestors partition s = 
                    getAncestors partition s').
                    unfold s'.

   
   apply getAncestorsUpdateMappedPageData;trivial.
   intuition.
    rewrite <- HgetParent in *. 
    apply Hdiff;trivial.
Qed.
Lemma  configTablesAreDifferentUpdateMappedPageContent table curidx x s nbLgen:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
Some nbLgen = StateLib.getNbLevel -> 
consistency s -> 
configTablesAreDifferent s'.
Proof.
intros s' (Hconfig & Hfalse).
intros.
 unfold consistency in *; intuition.
 assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
{ unfold s'.
 apply getPartitionsUpdateMappedPageData ; intuition.
 + unfold getPartitions.
   destruct nbPage;simpl;left;trivial.
 +   apply beq_nat_false in Hfalse.
   unfold not; intros.
   apply Hfalse.
   subst;trivial. }   
assert(Hconfigdiff : configTablesAreDifferent s) by intuition.
unfold configTablesAreDifferent in *.
simpl in *.
intros partition1 partition2 Hpart1 Hpart2 Hdiff.
rewrite Hpartions in *. clear Hpartions.
assert(Hdisjoint : getConfigPages partition1 s' = getConfigPages partition1 s).
apply getConfigPagesUpdateMappedPageData;trivial.
unfold not. apply Hconfig; trivial.
rewrite Hdisjoint;clear Hdisjoint.
assert(Hdisjoint : getConfigPages partition2 s' = getConfigPages partition2 s).
apply getConfigPagesUpdateMappedPageData;trivial.
unfold not. apply Hconfig; trivial.
rewrite Hdisjoint;clear Hdisjoint.
apply Hconfigdiff;trivial.
Qed.

Lemma  isChildUpdateMappedPageContent table curidx x s :
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
consistency s -> 
isChild s'.
Proof.
intros s' (Hconfig & Hfalse).
intros.
 unfold consistency in *; intuition.
unfold s'.
apply isChildUpdateMappedPageData;trivial.
intuition.
unfold not;intros;subst;apply beq_nat_false in Hfalse;
now contradict Hfalse.
Qed.

Lemma physicalPageNotDerivedUpdateMappedPageData' table curidx x s :
let s':= {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
consistency s -> 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
physicalPageNotDerived
 s' .
Proof.
intros s' Hcons (Hconfig & Hfalse).
unfold physicalPageNotDerived.
intros.  
simpl in *.
assert(Hpde: partitionDescriptorEntry s) by (unfold  consistency in *; intuition).
assert(Htablenotpart : forall part , In part (getPartitions pageRootPartition s) ->
table <> part).
  { intros.
    apply Hconfig in H6;intuition. }
assert(Hmult : In pageRootPartition (getPartitions pageRootPartition s)).
  { unfold getPartitions;
    destruct nbPage;simpl;left;trivial. }
assert(table<> pageDefault). 
{   apply beq_nat_false in Hfalse.
   unfold not; intros.
   apply Hfalse.
   subst;trivial.   }
 assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpart.
{ unfold s'.
 apply getPartitionsUpdateMappedPageData ; intuition.
+  unfold consistency in *. intuition.

 }
rewrite Hpart in *.
assert(Hconfig1 : ~ In table (getConfigPages parent s)).
  { apply Hconfig in H.
    intuition. }
assert(Hconfig2 :  table <> parent).
  { apply Hconfig in H.
    intuition. }
assert(Hchild : getChildren parent
         s'
          = getChildren parent s).
  { apply getChildrenUpdateMappedPageData;trivial.
    }
rewrite Hchild in *.
assert(Hchildpart : In child (getPartitions pageRootPartition s)).
  { apply childrenPartitionInPartitionList with parent;trivial.
  unfold consistency in *. intuition. }
assert(Hconfig3 :  table <> child).
  { apply Hconfig in Hchildpart.
    intuition. }
assert(Hpd :  StateLib.getPd parent 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getPd parent (memory s)).  
  { intros.    
    apply getPdUpdateMappedPageData;trivial. }
rewrite Hpd in *;clear Hpd.
  assert(Hpd :  StateLib.getPd child 
(add table curidx x (memory s) pageEq idxEq) = 
StateLib.getPd child (memory s)).
  { intros.    
    apply getPdUpdateMappedPageData;trivial. }
rewrite Hpd in *;clear Hpd.
assert(Hpdchildnotnull : pdChild <> pageDefault).
{ 
 unfold partitionDescriptorEntry in *.

assert( exists entry : page, nextEntryIsPP child idxPageDir entry s 
/\ entry <> pageDefault) as (pd & Hpd & Hnotnul).

apply Hpde;trivial.
left;trivial.
assert(pd = pdChild).
apply getPdNextEntryIsPPEq with child s;trivial.
subst.
trivial. }
assert(Hconfig4 : ~ In table (getIndirectionsAux pdChild s nbLevel)).
  { apply notConfigTableNotPdconfigTable with child;trivial.    
    apply Hconfig in Hchildpart.
    intuition.
     }
assert(Hgetmapped : getMappedPage pdChild
      s' vaInChild =
        getMappedPage pdChild s vaInChild).
apply  getMappedPageUpdateMappedPageData ;trivial.      
rewrite Hgetmapped in *. clear Hgetmapped.
assert(Hpdparent : pdParent <> pageDefault).
  { unfold partitionDescriptorEntry in *.
    assert( exists entry : page, nextEntryIsPP parent idxPageDir entry s 
    /\ entry <> pageDefault) as (pd & Hpd & Hnotnul). 
    apply Hpde;trivial.
    left;trivial.
    assert(pd = pdParent).
    apply getPdNextEntryIsPPEq with parent s;trivial.
    subst.
    trivial. } 
assert(Hgetmapped : getMappedPage pdParent
       s' va =
        getMappedPage pdParent s va).
  { apply  getMappedPageUpdateMappedPageData ;trivial.
    apply notConfigTableNotPdconfigTable with parent;trivial.
    apply Hconfig in H.
    intuition. }
rewrite Hgetmapped in *. clear Hgetmapped. 
assert(~ isDerived parent va s).
unfold not;intros Hfalse';contradict H1.
apply isDerivedUpdateMappedPageData;trivial.
assert(Hnotderiv: physicalPageNotDerived s) by (unfold consistency in *;intuition).
apply Hnotderiv with  parent va pdParent child pdChild vaInChild;trivial.
Qed.

Lemma  multiplexerWithoutParentUpdateMappedPageContent table curidx x s :
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
consistency s -> 
multiplexerWithoutParent s'.
Proof.
intros s' (Hconfig & Hfalse).
intros.
unfold consistency in *; intuition.
assert(Hmultnone : multiplexerWithoutParent s) by intuition.
unfold multiplexerWithoutParent in *.
rewrite <- Hmultnone.
apply getParentUpdateMappedPageData;trivial.
assert(Hmultpart : In pageRootPartition (getPartitions pageRootPartition s)). 
unfold getPartitions.
destruct nbPage;simpl;left;trivial.
unfold not;intros. 
apply Hconfig in Hmultpart. trivial.
left. subst. trivial.
Qed.
      Lemma  noDupPartitionTreeUpdateMappedPageData' table curidx x s :
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
consistency s -> 
noDupPartitionTree s'.
Proof.
intros s' (Hconfig & Hfalse).
intros.
unfold consistency in *; intuition.
assert(table<> pageDefault). 
apply beq_nat_false in Hfalse.
contradict Hfalse.
rewrite Hfalse.
trivial.
assert(Hpde: partitionDescriptorEntry s ) by trivial.
assert(Hparentpart : parentInPartitionList s )by trivial.
assert(Hnodup : noDupPartitionTree s) by intuition.
unfold noDupPartitionTree in *.
assert(HgetParts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
 rewrite HgetParts . trivial.
Qed.



Lemma isParentUpdateMappedPageData' table curidx x  s:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
consistency s -> 
isParent {|  currentPartition := currentPartition s;
        memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros s' (Hget1 & Hfalse).
intros.
unfold consistency in *;intuition.
assert(Hpde: partitionDescriptorEntry s ) by trivial.
assert(Hparentpart : parentInPartitionList s )by trivial.
assert(Hnodup : noDupPartitionTree s) by intuition.
assert(table <> pageDefault).
apply beq_nat_false in Hfalse.
contradict Hfalse.
rewrite Hfalse.
trivial.
unfold isParent.
intros (* Hpde Hparent Hnotnull Hget1 Hget2 *) partition parent Hparts Hgetparent .
simpl in *.
assert(HgetParts : getPartitions pageRootPartition
  {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |} = 
  getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
rewrite HgetParts in *. clear HgetParts.
assert(Hchildren : getChildren parent
{|
currentPartition := currentPartition s;
memory := add table curidx x (memory s) pageEq idxEq |} = 
getChildren parent s).
apply getChildrenUpdateMappedPageData;trivial.
unfold not;intros.
apply Hget1 with parent;trivial.
  
assert (Htable : table <> parent).
{
unfold not;intros.
subst.
apply Hget1 with parent;trivial.
left;trivial. }
trivial.
rewrite Hchildren in *.
clear Hchildren. 
assert (Htable : table <> partition).
{
unfold not;intros.
subst.
apply Hget1 with partition;trivial.
apply childrenPartitionInPartitionList with parent;trivial.

left;trivial. }
rewrite getParentUpdateMappedPageData in *;trivial.
assert(Hget2: isParent s) by trivial.
apply Hget2;trivial.
Qed.     
Lemma wellFormedFstShadowtUpdateMappedPageData' table curidx x  s:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
consistency s -> 
wellFormedFstShadow {|  currentPartition := currentPartition s;
        memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros s' (Hget1 & Hfalse).
intros.
unfold consistency in *;intuition.
assert(Hpde: partitionDescriptorEntry s ) by trivial.
assert(Hparentpart : parentInPartitionList s )by trivial.
assert(Hnodup : noDupPartitionTree s) by intuition.
assert(table <> pageDefault).
apply beq_nat_false in Hfalse.
contradict Hfalse.
rewrite Hfalse.
trivial.
assert(Hget2:  wellFormedFstShadow s) by trivial.
unfold wellFormedFstShadow in *.
simpl in *.
assert(HgetParts : getPartitions pageRootPartition
  {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |} = 
  getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
rewrite HgetParts in *. clear HgetParts.
intros.
assert(table <> partition).
    {
    unfold not;intros. apply Hget1 with partition;trivial.
    left;trivial. intuition. }
assert(Hpd :  StateLib.getPd partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getPd partition (memory s)).  
  { intros.    
    apply getPdUpdateMappedPageData;trivial.
     }
assert(Hpdchildnotnull : pd <> pageDefault).
{ unfold partitionDescriptorEntry in *.
rewrite Hpd in *. clear Hpd. 
assert( exists entry : page, nextEntryIsPP partition idxPageDir entry s 
/\ entry <> pageDefault) as (pdtmp & Hpdtmp & Hnotnul).
apply Hpde;trivial.
left;trivial.
assert( pdtmp = pd).
apply getPdNextEntryIsPPEq with partition s;trivial.
subst.
trivial. }
 assert(Hmap : getMappedPage pd
       {|
       currentPartition := currentPartition s;
       memory := add table curidx x (memory s) pageEq idxEq |} va =
       getMappedPage pd s va).
{ apply getMappedPageUpdateMappedPageData;trivial.
apply notConfigTableNotPdconfigTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial.
    
rewrite Hpd in *;clear Hpd.
trivial. }

rewrite Hmap in *. clear Hmap.
assert(Hsh1 :  StateLib.getFstShadow partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getFstShadow partition (memory s)).  
  { intros.    
    apply getFstShadowUpdateMappedPageData;trivial.
     }
rewrite Hsh1 in *.
assert(   sh1<> pageDefault  ).
{
assert( exists entry : page, nextEntryIsPP partition idxShadow1 entry s 
/\ entry <> pageDefault) as (pdtmp & Hpdtmp & Hnotnul).
apply Hpde;trivial.
right;left;trivial.
assert( pdtmp = sh1).
apply getSh1NextEntryIsPPEq with partition s;trivial.
subst.
trivial. }
assert(Hv1 : getVirtualAddressSh1 sh1
    {|
    currentPartition := currentPartition s;
    memory := add table curidx x (memory s) pageEq idxEq |} va = getVirtualAddressSh1 sh1
    s va).
    symmetry.
     
apply getVirtualAddressSh1UpdateMappedPageData;trivial.
apply notConfigTableNotSh1configTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial.
rewrite Hv1.
apply Hget2 with partition pg pd;trivial.
rewrite Hpd in *.
trivial. 
Qed.

Lemma wellFormedSndShadowtUpdateMappedPageData' table curidx x  s:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
consistency s -> 
wellFormedSndShadow {|  currentPartition := currentPartition s;
        memory := add table curidx x (memory s) pageEq idxEq |}.
Proof.
intros s' (Hget1 & Hfalse).
intros.
unfold consistency in *;intuition.
assert(Hpde: partitionDescriptorEntry s ) by trivial.
assert(Hparentpart : parentInPartitionList s )by trivial.
assert(Hnodup : noDupPartitionTree s) by intuition.
assert(table <> pageDefault).
apply beq_nat_false in Hfalse.
contradict Hfalse.
rewrite Hfalse.
trivial.
assert(Hget2:  wellFormedSndShadow s) by trivial.
unfold wellFormedSndShadow in *.
simpl in *.
assert(HgetParts : getPartitions pageRootPartition
  {|
  currentPartition := currentPartition s;
  memory := add table curidx x (memory s) pageEq idxEq |} = 
  getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
rewrite HgetParts in *. clear HgetParts.
intros.
assert(table <> partition).
    {
    unfold not;intros. apply Hget1 with partition;trivial.
    left;trivial. intuition. }
assert(Hpd :  StateLib.getPd partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getPd partition (memory s)).  
  { intros.    
    apply getPdUpdateMappedPageData;trivial.
     }
assert(Hpdchildnotnull : pd <> pageDefault).
{ unfold partitionDescriptorEntry in *.
rewrite Hpd in *. clear Hpd. 
assert( exists entry : page, nextEntryIsPP partition idxPageDir entry s 
/\ entry <> pageDefault) as (pdtmp & Hpdtmp & Hnotnul).
apply Hpde;trivial.
left;trivial.
assert( pdtmp = pd).
apply getPdNextEntryIsPPEq with partition s;trivial.
subst.
trivial. }
 assert(Hmap : getMappedPage pd
       {|
       currentPartition := currentPartition s;
       memory := add table curidx x (memory s) pageEq idxEq |} va =
       getMappedPage pd s va).
{ apply getMappedPageUpdateMappedPageData;trivial.
apply notConfigTableNotPdconfigTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial.
    
rewrite Hpd in *;clear Hpd.
trivial. }

rewrite Hmap in *. clear Hmap.
assert(Hsh1 :  StateLib.getSndShadow partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getSndShadow partition (memory s)).  
  { intros.    
    apply getSndShadowUpdateMappedPageData;trivial.
     }
rewrite Hsh1 in *.
assert(   sh2<> pageDefault  ).
{
assert( exists entry : page, nextEntryIsPP partition idxShadow2 entry s 
/\ entry <> pageDefault) as (pdtmp & Hpdtmp & Hnotnul).
apply Hpde;trivial.
do 2 right;left;trivial.
assert( pdtmp = sh2).
apply getSh2NextEntryIsPPEq with partition s;trivial.
subst.
trivial. }
assert(Hv1 : getVirtualAddressSh2 sh2
    {|
    currentPartition := currentPartition s;
    memory := add table curidx x (memory s) pageEq idxEq |} va = getVirtualAddressSh2 sh2
    s va).
    symmetry.
     
apply getVirtualAddressSh2UpdateMappedPageData;trivial.
apply notConfigTableNotSh2configTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial.
rewrite Hv1.
apply Hget2 with partition pg pd;trivial.
rewrite Hpd in *.
trivial. 
Qed.

Lemma wellFormedShadowsUpdateMappedPageData' table curidx x idxroot s:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
idxroot = idxShadow1 \/ idxroot = idxShadow2 -> 
wellFormedShadows idxroot s ->
consistency s -> 

wellFormedShadows idxroot s'.
Proof.
intros s' (Hconfig & Hfalse) Hor Hget2.
intros.
unfold consistency in *.
assert(Hpde: partitionDescriptorEntry s ) by intuition.
assert(Hparentpart : parentInPartitionList s )by intuition.
assert(Hnodup : noDupPartitionTree s) by intuition.
assert(Hnotnull: table <> pageDefault).
{
apply beq_nat_false in Hfalse.
contradict Hfalse.
rewrite Hfalse.
trivial. }

assert(HgetParts : getPartitions pageRootPartition
 s' = 
  getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
unfold wellFormedShadows.

intros partition Hpart.
rewrite HgetParts in * . clear HgetParts.
intros.
  assert(Hind : getIndirection pdroot va nbL stop s' = Some indirection1) by trivial.
assert(table <> partition).
    {
    unfold not;intros.
     apply Hconfig with partition;trivial.
    left;trivial. intuition. }
assert(Htable :stop <= (nbLevel -1) -> ~ In table (getIndirectionsAux structroot s (S stop))).
intros.
{ assert (Hstop : stop < (nbLevel -1) \/ stop = (nbLevel -1) ) by lia.
  clear H.
  destruct Hstop as [Hlt |  Heq ].
  +
generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig .
destruct Hor as [Hsh1 | Hsh2].
{ subst.
  apply  notConfigTableNotSh1configTableLt with partition; trivial.
  rewrite nextEntryIsPPgetFstShadow in *.
  rewrite <- H1.
  symmetry.
  apply  getFstShadowUpdateMappedPageData;trivial. }
{ subst.
  apply  notConfigTableNotSh2configTableLt with partition; trivial.
  rewrite nextEntryIsPPgetSndShadow in *.
  rewrite <- H1.
  symmetry.
  apply  getSndShadowUpdateMappedPageData;trivial. }
+ subst.

assert(0<nbLevel) by apply nbLevelNotZero.
assert(Hsnbl :  (S (nbLevel - 1)) = nbLevel) by lia.
rewrite Hsnbl.
destruct Hor as  [Hsh1 | Hsh2].
{ subst.
  apply  notConfigTableNotSh1configTable with partition; trivial.
  generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  rewrite nextEntryIsPPgetFstShadow in *.
  rewrite <- H1.
  symmetry.
  apply  getFstShadowUpdateMappedPageData;trivial. }
{ subst.
  apply  notConfigTableNotSh2configTable with partition; trivial.
  generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  rewrite nextEntryIsPPgetSndShadow in *.
  rewrite <- H1.
  symmetry.
  apply  getSndShadowUpdateMappedPageData;trivial. } } 
 assert(Hgetind : exists indirection2 : page, getIndirection structroot va nbL stop s = Some indirection2 /\
        (Nat.eqb pageDefault indirection2) = b).
        apply Hget2  with partition pdroot indirection1;trivial.
        cbn in *.
    rewrite getPdUpdateMappedPageData in *;trivial.
    
    destruct Hor as [Hor | Hor]; subst.
    rewrite nextEntryIsPPgetFstShadow in *.
    simpl in *.
    assert(Hsh1 : StateLib.getFstShadow partition (add table curidx x (memory s) pageEq idxEq) = Some structroot)
    by trivial.
    rewrite <- Hsh1.
    symmetry.
    apply getFstShadowUpdateMappedPageData;trivial.
    rewrite nextEntryIsPPgetSndShadow in *.
    simpl in *.
    assert(Hsh1 : StateLib.getSndShadow partition (add table curidx x (memory s) pageEq idxEq) = Some structroot)
    by trivial.
    rewrite <- Hsh1.
    symmetry.
    apply getSndShadowUpdateMappedPageData;trivial.
    
    { clear Htable.
        assert(Htable :stop <= (nbLevel -1) -> ~ In table (getIndirectionsAux pdroot s (S stop))).
intros.
{ assert (Hstop : stop < (nbLevel -1) \/ stop = (nbLevel -1) ) by lia.
  destruct Hstop as [Hlt |  Heq ].
  +
generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig .
  apply  notConfigTableNotPdconfigTableLt with partition; trivial.
  rewrite <- H0.
  symmetry. 
  apply  getPdUpdateMappedPageData;trivial.
+ subst.

assert(0<nbLevel) by apply nbLevelNotZero.
assert(Hsnbl :  (S (nbLevel - 1)) = nbLevel) by lia.
rewrite Hsnbl.
  apply  notConfigTableNotPdconfigTable with partition; trivial.
  generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
  unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  rewrite <- H0.
  symmetry.
  apply  getPdUpdateMappedPageData;trivial. }
  
assert( getIndirection pdroot va nbL stop s' = getIndirection pdroot va nbL stop s).
{ assert (Hstop3 : stop < (nbLevel -1) \/ stop = (nbLevel -1) \/ stop > (nbLevel -1)) by lia.
  destruct Hstop3 as [Hlt | [ Heq | Hgt]].
  + apply getIndirectionUpdateMappedPageData with nbL;
    trivial. apply Htable. lia.
  + subst.
    apply getIndirectionUpdateMappedPageData with nbL ;trivial.
    apply Htable. lia.
    +
 
  assert(HnbL : Some nbL = StateLib.getNbLevel) by trivial.
assert(Hneww : getIndirection pdroot va nbL stop s' = 
            getIndirection pdroot va nbL nbL s').
    { rewrite Hind.
      symmetry.
      apply getIndirectionStopLevelGT2 with stop; trivial.      
      apply getNbLevelLe in HnbL.
      unfold CLevel in HnbL.
      case_eq (lt_dec (nbLevel - 1) nbLevel); intros ii Hii; rewrite Hii in *. 
      simpl in *.
      destruct nbL.
      simpl in *. lia.
      assert(0 < nbLevel) by apply nbLevelNotZero. 
      lia. }
    rewrite Hind.
    symmetry.
    apply getIndirectionStopLevelGT with nbL; trivial.
    apply getNbLevelLe in HnbL.
    unfold CLevel in HnbL.
    case_eq (lt_dec (nbLevel - 1) nbLevel); intros ii Hii;rewrite Hii in *.
    simpl in *.
    destruct nbL.
    simpl in *. lia.
    assert(0 < nbLevel) by apply nbLevelNotZero. 
    lia.
    rewrite <- Hind.
    rewrite Hneww.
    symmetry.
    apply getIndirectionUpdateMappedPageData with nbL ;trivial.
assert(HnbLevel : S nbL = nbLevel).

apply getNbLevelEq in HnbL.
subst.
rewrite <-  nbLevelEq.
assert(0 < nbLevel) by apply nbLevelNotZero.
lia. 
rewrite HnbLevel. 
 
      apply  notConfigTableNotPdconfigTable with partition; trivial.
      generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      rewrite <- H0.
      symmetry.
      apply getPdUpdateMappedPageData;trivial. 
       }
    rewrite <- H6;trivial. }
    destruct Hgetind as (indirection2 & Hgetind & Hdef).
    exists indirection2.
    
    split;trivial.
        
assert( getIndirection structroot va nbL stop s' = getIndirection structroot va nbL stop s).
{ assert (Hstop3 : stop < (nbLevel -1) \/ stop = (nbLevel -1) \/ stop > (nbLevel -1)) by lia.
  destruct Hstop3 as [Hlt | [ Heq | Hgt]].
  + apply getIndirectionUpdateMappedPageData with nbL;
    trivial. apply Htable. lia.
  + subst.
    apply getIndirectionUpdateMappedPageData with nbL ;trivial.
    apply Htable. lia.
  + 
      assert(HnbL : Some nbL = StateLib.getNbLevel) by trivial.
      assert(Hneww : getIndirection structroot va nbL stop s = 
            getIndirection structroot va nbL nbL s).
    { rewrite Hgetind.
      symmetry.
      apply getIndirectionStopLevelGT2 with stop; trivial.
      apply getNbLevelLe in HnbL.
      unfold CLevel in HnbL.
      case_eq (lt_dec (nbLevel - 1) nbLevel); intros ii Hii;
      rewrite Hii in *.
      simpl in *.
      destruct nbL.
      simpl in *. lia.
      assert(0 < nbLevel) by apply nbLevelNotZero. 
      lia. }
    rewrite Hgetind.
    apply getIndirectionStopLevelGT with nbL; trivial.
    
    apply getNbLevelLe in HnbL.
    unfold CLevel in HnbL.
    case_eq (lt_dec (nbLevel - 1) nbLevel); intros ii Hii;
      rewrite Hii in *.
    simpl in *.
    destruct nbL.
    simpl in *. lia.
    assert(0 < nbLevel) by apply nbLevelNotZero. 
    lia.
    rewrite <- Hgetind.
    rewrite Hneww.
    apply getIndirectionUpdateMappedPageData with nbL ;trivial.
    assert(HnbLevel : (S nbL) = nbLevel).
{ apply getNbLevelEq in HnbL.
  unfold CLevel in HnbL.
  case_eq (lt_dec (nbLevel - 1) nbLevel);intros ii Hii;
      rewrite Hii in *.
  simpl in *.
  destruct nbL.
  simpl in *.
  inversion HnbL. lia.
  assert(0 < nbLevel) by apply nbLevelNotZero. 
  lia. }
    rewrite HnbLevel.
   destruct Hor as [Hsh1 | Hsh2].
    (* { subst.
      apply  notConfigTableNotPdconfigTable with partition; trivial.
      generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      apply nextEntryIsPPgetPd; trivial. }
     *) 
     { subst.
      apply  notConfigTableNotSh1configTable with partition; trivial.
      generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      rewrite nextEntryIsPPgetFstShadow in *.
  rewrite <- H1.
  symmetry.
  apply  getFstShadowUpdateMappedPageData;trivial. }
    { subst.
      apply  notConfigTableNotSh2configTable with partition; trivial.
      generalize (Hconfig partition Hpart); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      apply nextEntryIsPPgetSndShadow; trivial.
      rewrite nextEntryIsPPgetSndShadow in *.
  rewrite <- H1.
  symmetry.
  apply  getSndShadowUpdateMappedPageData;trivial. } }
  rewrite H6. trivial. 
Qed.

Lemma wellFormedFstShadowIfNoneUpdateMappedPageData' table curidx x  s:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
consistency s -> 
wellFormedFstShadowIfNone s'.
Proof.
intros s' (Hget1 & Hfalse).
intros.
unfold consistency in *.
assert(Hget2:wellFormedFstShadowIfNone s ) by intuition.
assert(Hpde: partitionDescriptorEntry s ) by intuition.
assert(Hparentpart : parentInPartitionList s )by intuition.
assert(Hnodup : noDupPartitionTree s) by intuition.
assert(Hnotnull: table <> pageDefault).
{
apply beq_nat_false in Hfalse.
contradict Hfalse.
rewrite Hfalse.
trivial. }

assert(HgetParts : getPartitions pageRootPartition
 s' = 
  getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
unfold wellFormedFstShadowIfNone.
rewrite HgetParts in *. clear HgetParts.
intros;simpl in *.
assert(table <> partition).
    {
    unfold not;intros. apply Hget1 with partition;trivial.
    left;trivial. intuition. }
assert(Hpd :  StateLib.getPd partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getPd partition (memory s)).  
  { intros.    
    apply getPdUpdateMappedPageData;trivial.
     }
assert(Hpdchildnotnull : pd <> pageDefault).
{ unfold partitionDescriptorEntry in *.
rewrite Hpd in *. clear Hpd.
apply pdPartNotNull with partition s;trivial.
apply nextEntryIsPPgetPd;trivial. }
 assert(Hmap : getMappedPage pd
       s'  va =
       getMappedPage pd s va).
{ apply getMappedPageUpdateMappedPageData;trivial.
apply notConfigTableNotPdconfigTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial.
    
rewrite Hpd in *;clear Hpd.
trivial. }

rewrite Hmap in *. clear Hmap.
assert(Hsh1 :  StateLib.getFstShadow partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getFstShadow partition (memory s)).  
  { intros.    
    apply getFstShadowUpdateMappedPageData;trivial.
     }
rewrite Hsh1 in *.
assert(   sh1<> pageDefault  ).
{ apply sh1PartNotNull with partition s;trivial.
  apply nextEntryIsPPgetFstShadow;trivial. }
assert(Hv1 : getPDFlag sh1 va
   s'  = getPDFlag sh1
    va s).
{    
apply getPDFlagUpdateMappedPageData with partition;trivial.
apply nextEntryIsPPgetFstShadow;trivial.
assert(nbLevel> 0) by apply nbLevelNotZero.
replace (S (nbLevel - 1)) with nbLevel by lia.
apply notConfigTableNotSh1configTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial. }
rewrite Hv1.
assert(Hv2 : getVirtualAddressSh1 sh1
    s'  va = getVirtualAddressSh1 sh1
     s va).
{ symmetry.    
apply getVirtualAddressSh1UpdateMappedPageData ;trivial.
apply notConfigTableNotSh1configTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial. }
rewrite Hv2.
apply Hget2 with partition  pd;trivial.
rewrite Hpd in *.
trivial. 
Qed.

Lemma wellFormedFstShadowIfDefaultValuesUpdateMappedPageData' table curidx x  s:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
consistency s -> 
wellFormedFstShadowIfDefaultValues s'.
Proof.
intros s' (Hget1 & Hfalse).
intros.
unfold consistency in *.
assert(Hget2:wellFormedFstShadowIfDefaultValues s ) by intuition.
assert(Hpde: partitionDescriptorEntry s ) by intuition.
assert(Hparentpart : parentInPartitionList s )by intuition.
assert(Hnodup : noDupPartitionTree s) by intuition.
assert(Hnotnull: table <> pageDefault).
{
apply beq_nat_false in Hfalse.
contradict Hfalse.
rewrite Hfalse.
trivial. }

assert(HgetParts : getPartitions pageRootPartition
 s' = 
  getPartitions pageRootPartition s).
apply getPartitionsUpdateMappedPageData ;trivial.
unfold getPartitions.
destruct nbPage;
simpl;left;trivial.
unfold wellFormedFstShadowIfDefaultValues.
rewrite HgetParts in *. clear HgetParts.
intros;simpl in *.
assert(table <> partition).
    {
    unfold not;intros. apply Hget1 with partition;trivial.
    left;trivial. intuition. }
assert(Hpd :  StateLib.getPd partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getPd partition (memory s)).  
  { intros.    
    apply getPdUpdateMappedPageData;trivial.
     }
assert(Hpdchildnotnull : pd <> pageDefault).
{ unfold partitionDescriptorEntry in *.
rewrite Hpd in *. clear Hpd.
apply pdPartNotNull with partition s;trivial.
apply nextEntryIsPPgetPd;trivial. }
 assert(Hmap : getMappedPage pd
       s' va =
       getMappedPage pd s va).
{ apply getMappedPageUpdateMappedPageData;trivial.
apply notConfigTableNotPdconfigTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial.
    
rewrite Hpd in *;clear Hpd.
trivial. }

rewrite Hmap in *. clear Hmap.
assert(Hsh1 :  StateLib.getFstShadow partition 
    (add table curidx x (memory s) pageEq idxEq) = 
      StateLib.getFstShadow partition (memory s)).  
  { intros.    
    apply getFstShadowUpdateMappedPageData;trivial.
     }
rewrite Hsh1 in *.
assert(   sh1<> pageDefault  ).
{ apply sh1PartNotNull with partition s;trivial.
  apply nextEntryIsPPgetFstShadow;trivial. }
assert(Hv1 : getPDFlag sh1 va
    s' = getPDFlag sh1
    va s).
{    
apply getPDFlagUpdateMappedPageData with partition;trivial.
apply nextEntryIsPPgetFstShadow;trivial.
assert(nbLevel> 0) by apply nbLevelNotZero.
replace (S (nbLevel - 1)) with nbLevel by lia.
apply notConfigTableNotSh1configTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial. }
rewrite Hv1.
assert(Hv2 : getVirtualAddressSh1 sh1
    s' va = getVirtualAddressSh1 sh1
     s va).
{ symmetry.    
apply getVirtualAddressSh1UpdateMappedPageData ;trivial.
apply notConfigTableNotSh1configTable with partition;trivial.
unfold not;intros. 
    apply Hget1 with partition;trivial.
    right;trivial. }
rewrite Hv2.
apply Hget2 with partition  pd;trivial.
rewrite Hpd in *.
trivial. 
Qed.

Lemma consistencyUpdateMappedPageData table curidx x s nbLgen:
let s' := {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |} in 
consistency s -> 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
Some nbLgen = StateLib.getNbLevel -> 
match x with
| PE _ => isPresentNotDefaultIff {| currentPartition := currentPartition s; memory := add table curidx x (memory s) pageEq idxEq |}
| _ => True
end -> 
consistency s'. 
Proof.
intros s' Hcons (* (Hpre1 & Hpre2) *).
intros.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
{ unfold consistency, initPEntryTablePreconditionToPropagatePrepareProperties in *. 
  unfold s'.
 apply getPartitionsUpdateMappedPageData ; intuition.
 + unfold getPartitions.
   destruct nbPage;simpl;left;trivial.
 + assert(Hfalse : (Nat.eqb pageDefault table) = false) by intuition.
   apply beq_nat_false in Hfalse.
   unfold not; intros.
   apply Hfalse.
   subst;trivial. }
unfold consistency. 
intuition.
+ apply partitionDescriptorEntryUpdateMappedPageData; trivial.
+ apply dataStructurePdSh1Sh2asRootUpdateMappedPageData; trivial.
    left; trivial.
    unfold consistency in *;intuition.
+ apply dataStructurePdSh1Sh2asRootUpdateMappedPageData; trivial.
  right;left; trivial.
   unfold consistency in *;intuition.
+ apply dataStructurePdSh1Sh2asRootUpdateMappedPageData; trivial.
  right;right;trivial.
   unfold consistency in *;intuition.
+ unfold currentPartitionInPartitionsList in *.
  rewrite Hpartions.  unfold consistency in *;intuition.
+ apply noDupMappedPagesListUpdateMappedPageContent with nbLgen;trivial.
+ apply noDupConfigPagesListUpdateMappedPageContent with nbLgen;trivial.
+ apply parentInPartitionListUpdateMappedPageContent with nbLgen;trivial.
+ apply accessibleVAIsNotPartitionDescriptorUpdateMappedPageContent with nbLgen;trivial.
+ apply accessibleChildPageIsAccessibleIntoParentUpdateMappedPageContent with nbLgen;trivial.
+ apply noCycleInPartitionTreeUpdateMappedPageContent with nbLgen;trivial.
+ apply configTablesAreDifferentUpdateMappedPageContent with nbLgen;trivial.
+ apply isChildUpdateMappedPageContent;trivial.
+ apply isPresentNotDefaultIffUpdateMappedPageData;unfold consistency in *;intuition.
+ apply physicalPageNotDerivedUpdateMappedPageData';trivial. 
+ apply multiplexerWithoutParentUpdateMappedPageContent;trivial.
+ apply isParentUpdateMappedPageData';trivial.
+ apply noDupPartitionTreeUpdateMappedPageData';trivial.
+  apply wellFormedFstShadowtUpdateMappedPageData';trivial.
+  apply wellFormedSndShadowtUpdateMappedPageData';trivial.
+ apply wellFormedShadowsUpdateMappedPageData';trivial. 
  left;trivial.
  unfold consistency in *;intuition.
+ apply wellFormedShadowsUpdateMappedPageData';trivial. 
  right;trivial.
  unfold consistency in *;intuition.
+ unfold consistency in *;intuition.
+ apply wellFormedFstShadowIfNoneUpdateMappedPageData';trivial.
+ apply wellFormedFstShadowIfDefaultValuesUpdateMappedPageData';trivial.
Qed.




Lemma propagatedPropertiesUpdateMappedPageData accessibleChild accessibleSh1 accessibleSh2 accessibleList 
curidx x table pdChild currentPart 
currentPD level ptRefChild descChild idxRefChild presentRefChild ptPDChild
idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 
idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList presentConfigPagesList 
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1 
derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList 
phyDescChild s :
match x with 
| PE a => isPresentNotDefaultIff {|
                    currentPartition := currentPartition s;
                    memory := add table curidx
                              x (memory s) pageEq idxEq |} 
| _ => True
end -> 
propagatedProperties accessibleChild accessibleSh1 accessibleSh2 accessibleList 
pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2
presentSh2 ptConfigPagesList idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1
derivedRefChild ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child
childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
phyDescChild s  -> 

  (forall partition : page,
  In partition (getPartitions pageRootPartition s) ->
  partition = table \/ In table (getConfigPagesAux partition s) -> False) -> 
  (Nat.eqb pageDefault table) = false -> 
   propagatedProperties accessibleChild accessibleSh1 accessibleSh2 accessibleList 
    pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2
  presentSh2 ptConfigPagesList idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1
  derivedRefChild ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child
  childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
  phyDescChild   {|
                    currentPartition := currentPartition s;
                    memory := add table curidx
                              x (memory s) pageEq idxEq |}.
Proof.
set (s' := {|
  currentPartition := currentPartition s;
  memory := add table curidx
              x (memory s) pageEq idxEq |}).
   unfold propagatedProperties in *.
   intros. 
   assert(Hnoduptree : noDupPartitionTree s) .
     unfold consistency in *. intuition.
assert(initPEntryTablePreconditionToPropagatePrepareProperties s table).
unfold initPEntryTablePreconditionToPropagatePrepareProperties;intuition.    
split.
(** partitionsIsolation **)
apply partitionsIsolationUpdateMappedPageData  with level;intuition.
split.
 (** kernelDataIsolation **)
apply kernelDataIsolationUpdateMappedPageData with level;intuition.
split.
(** verticalSharing **)
apply verticalSharingUpdateMappedPageData with level;intuition.
split.
(** consistency *)
apply consistencyUpdateMappedPageData with level;intuition.
(** Propagated properties **)
  {
    unfold consistency in *.
    assert (Hcurpart : In currentPart (getPartitions pageRootPartition s)). 
    assert (Hcurpart : currentPartitionInPartitionsList s)by intuition.
    unfold currentPartitionInPartitionsList in *.
    assert (currentPart = currentPartition s) by intuition.
    subst. intuition.
    assert( Hpde : partitionDescriptorEntry s) by intuition.
    assert (Hnotconfig : forall partition : page,
     In partition (getPartitions pageRootPartition s) ->
     ~ (partition = table \/ In table (getConfigPagesAux partition s))) by intuition.
    assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
     { unfold s'.
       apply getPartitionsUpdateMappedPageData ; trivial.
       + unfold getPartitions.
         destruct nbPage;simpl;left;trivial.
       + assert(Hfalse : (Nat.eqb pageDefault table) = false) by intuition.
         apply beq_nat_false in Hfalse.
         unfold not; intros.
         apply Hfalse.
         subst;trivial. }
    intuition try assumption. 
    + apply nextEntryIsPPUpdateMappedPageData; trivial.
    + assert(Hptref : forall idx : index,
        StateLib.getIndexOfAddr descChild levelMin = idx ->
        isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild idxPageDir currentPart descChild s)
        by trivial.
      apply isPEUpdateUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD isPE idxPageDir descChild idxRefChild s ;
       trivial.
       left;trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
          StateLib.getIndexOfAddr descChild levelMin = idx ->
          isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild idxPageDir currentPart descChild s) 
      by trivial.
      assert (StateLib.getIndexOfAddr descChild levelMin = idxRefChild) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr descChild levelMin = idx ->
      isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild idxPageDir currentPart descChild s)
      by trivial.
      apply entryPresentFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD  isPE idxPageDir descChild idxRefChild s ;
      trivial.
      left;trivial.
    + apply entryUserFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD isPE idxPageDir descChild idxRefChild s ;
      trivial. left;trivial.
    + assert(Hptref : forall idx : index,
        StateLib.getIndexOfAddr pdChild levelMin = idx ->
        isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s)
        by trivial.
      apply isPEUpdateUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD  isPE idxPageDir  pdChild idxPDChild s ;
       trivial.
      left;trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr pdChild levelMin = idx ->
        isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s) 
      by trivial.
      assert (StateLib.getIndexOfAddr pdChild levelMin = idxPDChild) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial. 
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr pdChild levelMin = idx ->
      isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s)
      by trivial.
      apply entryPresentFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD  isPE idxPageDir pdChild idxPDChild s ;
      trivial.
      left;trivial.
    + apply entryUserFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD isPE idxPageDir pdChild idxPDChild s ;
      trivial. left;trivial.
    + assert(Hptref : forall idx : index,
        StateLib.getIndexOfAddr shadow1 levelMin = idx ->
        isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s)
        by trivial.
      apply isPEUpdateUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD  isPE idxPageDir shadow1 idxSh1 s ;
         trivial.
      left;trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr shadow1 levelMin = idx ->
        isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s) 
      by trivial.
      assert (StateLib.getIndexOfAddr shadow1 levelMin = idxSh1) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr shadow1 levelMin = idx ->
      isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s)
      by trivial.
      apply entryPresentFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD  isPE idxPageDir shadow1 idxSh1 s ;
      trivial.
      left;trivial.
    + apply entryUserFlagUpdateMappedPageData; trivial. 
      apply mappedPageIsNotPTable with currentPart currentPD isPE idxPageDir shadow1 idxSh1 s ;
      trivial. left;trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr shadow2 levelMin = idx ->
      isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child idxPageDir currentPart shadow2 s)
      by trivial.
      apply isPEUpdateUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD  isPE idxPageDir shadow2 idxSh2 s ;
      trivial.
      left;trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr shadow2 levelMin = idx ->
        isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child idxPageDir currentPart shadow2 s) 
      by trivial.
      assert (StateLib.getIndexOfAddr shadow2 levelMin = idxSh2) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial. 
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr shadow2 levelMin = idx ->
      isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child idxPageDir currentPart shadow2 s)
      by trivial.
      apply entryPresentFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD  isPE idxPageDir shadow2 idxSh2 s ;
      trivial.
      left;trivial.
     + apply entryUserFlagUpdateMappedPageData; trivial. 
      apply mappedPageIsNotPTable with currentPart currentPD isPE idxPageDir shadow2 idxSh2 s ;
      trivial. left;trivial.
    + assert(Hptref : forall idx : index,
        StateLib.getIndexOfAddr list levelMin = idx ->
        isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList idxPageDir currentPart list s)
        by trivial.
      apply isPEUpdateUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD  isPE idxPageDir list idxConfigPagesList s ;
           trivial.
      left;trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr list levelMin = idx ->
        isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList idxPageDir currentPart list s) 
      by trivial.
      assert (StateLib.getIndexOfAddr list levelMin = idxConfigPagesList) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial. 
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr list levelMin = idx ->
      isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList idxPageDir currentPart list s)
      by trivial.
      apply entryPresentFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD  isPE idxPageDir list idxConfigPagesList s ;
      trivial.
      left;trivial.
    + apply entryUserFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD isPE idxPageDir list idxConfigPagesList s ;
      trivial. left;trivial.
 
    + apply nextEntryIsPPUpdateMappedPageData; trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr descChild levelMin = idx ->
      isVE ptRefChildFromSh1 idx s /\ getTableAddrRoot ptRefChildFromSh1 idxShadow1 currentPart descChild s)
        by trivial.
      apply isVEUpdateMappedPageData; trivial.
     apply mappedPageIsNotPTable with currentPart currentShadow1  isVE idxShadow1 descChild idxRefChild s ;trivial.
     right;left;trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr descChild levelMin = idx ->
        isVE ptRefChildFromSh1 idx s /\ getTableAddrRoot ptRefChildFromSh1 idxShadow1 currentPart descChild s) 
      by trivial.
      assert (StateLib.getIndexOfAddr descChild levelMin = idxRefChild) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hvaref : exists va : vaddr, 
            isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
            vaddrEq vaddrDefault va = derivedRefChild) by trivial.
      destruct Hvaref as (vaRef & Hvaref & Hderivref).
      exists vaRef; split; trivial.
      unfold s'.
      apply isEntryVAUpdateMappedPageData; trivial.
        apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1  descChild idxRefChild s ;
         trivial.
         right;left;trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr pdChild levelMin = idx ->
      isVE ptPDChildSh1 idx s /\ getTableAddrRoot ptPDChildSh1 idxShadow1 currentPart pdChild s)
        by trivial.
      apply isVEUpdateMappedPageData; trivial.
       apply mappedPageIsNotPTable with currentPart currentShadow1  isVE idxShadow1 pdChild idxPDChild s ;
           trivial.
      right;left;trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr pdChild levelMin = idx ->
        isVE ptPDChildSh1 idx s /\ getTableAddrRoot ptPDChildSh1 idxShadow1 currentPart pdChild s) 
      by trivial.
      assert (StateLib.getIndexOfAddr pdChild levelMin = idxPDChild) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hvaref : exists va : vaddr, 
            isEntryVA ptPDChildSh1 idxPDChild va s /\ 
            vaddrEq vaddrDefault va = derivedPDChild) by trivial.
      destruct Hvaref as (vaRef & Hvaref & Hderivref).
      exists vaRef; split; trivial.
      unfold s'.
      apply isEntryVAUpdateMappedPageData; trivial.
        apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1  pdChild idxPDChild s ;
      trivial. right;left;trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr shadow1 levelMin = idx ->
      isVE ptSh1ChildFromSh1 idx s /\ getTableAddrRoot ptSh1ChildFromSh1 idxShadow1 currentPart shadow1 s)
        by trivial.
      apply isVEUpdateMappedPageData; trivial.
       apply mappedPageIsNotPTable with currentPart currentShadow1  isVE idxShadow1 shadow1 idxSh1 s ;
           trivial.
      right;left;trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr shadow1 levelMin = idx ->
        isVE ptSh1ChildFromSh1 idx s /\ getTableAddrRoot ptSh1ChildFromSh1 idxShadow1 currentPart shadow1 s) 
      by trivial.
      assert (StateLib.getIndexOfAddr shadow1 levelMin = idxSh1) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hvaref : exists va : vaddr, 
            isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ 
            vaddrEq vaddrDefault va = derivedSh1Child) by trivial.
      destruct Hvaref as (vaRef & Hvaref & Hderivref).
      exists vaRef; split; trivial.
      unfold s'.
      apply isEntryVAUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1  shadow1 idxSh1 s ;
         trivial.
         right;left;trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr shadow2 levelMin = idx ->
      isVE childSh2 idx s /\ getTableAddrRoot childSh2 idxShadow1 currentPart shadow2 s)
        by trivial.
      apply isVEUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 shadow2 idxSh2 s ;
           trivial.
       right;left;trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr shadow2 levelMin = idx ->
        isVE childSh2 idx s /\ getTableAddrRoot childSh2 idxShadow1 currentPart shadow2 s) 
      by trivial.
      assert (StateLib.getIndexOfAddr shadow2 levelMin = idxSh2) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hvaref : exists va : vaddr, 
            isEntryVA childSh2 idxSh2 va s /\ 
            vaddrEq vaddrDefault va = derivedSh2Child) by trivial.
      destruct Hvaref as (vaRef & Hvaref & Hderivref).
      exists vaRef; split; trivial.
      unfold s'.
      apply isEntryVAUpdateMappedPageData; trivial.
       apply mappedPageIsNotPTable with currentPart currentShadow1  isVE idxShadow1 shadow2 idxSh2 s ;
         trivial.
       right;left;trivial. 
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr list levelMin = idx ->
      isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 idxShadow1 currentPart list s)
        by trivial.
      apply isVEUpdateMappedPageData; trivial.
       apply mappedPageIsNotPTable with currentPart currentShadow1  isVE idxShadow1 list idxConfigPagesList s ;
           trivial.
      right;left;trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr list levelMin = idx ->
        isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 idxShadow1 currentPart list s) 
      by trivial.
      assert (StateLib.getIndexOfAddr list levelMin = idxConfigPagesList) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hvaref : exists va : vaddr, 
            isEntryVA childListSh1 idxConfigPagesList va s /\ 
            vaddrEq vaddrDefault va = derivedRefChildListSh1) by trivial.
      destruct Hvaref as (vaRef & Hvaref & Hderivref).
      exists vaRef; split; trivial.
      unfold s'.
      apply isEntryVAUpdateMappedPageData; trivial.
       apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1  list 
      idxConfigPagesList s ;
         trivial.
      right;left;trivial.
    + apply isEntryPageUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD isPE idxPageDir pdChild idxPDChild s ;
      trivial.
      left;trivial.
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions pageRootPartition s)) by trivial.
      generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
      apply Hconfig.
      left; assumption.
    +  assert (Hconfig : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions pageRootPartition s)) by trivial.      
      generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
      apply Hconfig.
      assert (Hconfigeq : In phyPDChild (getConfigPages partition s')).
      unfold getConfigPages.
      simpl. right; trivial.
      unfold s' in Hconfigeq.
      rewrite getConfigPagesUpdateMappedPageData in *.
      unfold getConfigPages in Hconfigeq.
      simpl in *.
      assumption.
      assert (Hconfigpd : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False)
      by trivial.
      unfold not.
      intros Hfalse. 
      apply Hconfigpd with partition; trivial.
    + apply isEntryPageUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD isPE idxPageDir shadow1 idxSh1 s ;
      trivial.
      left;trivial.
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions pageRootPartition s)) by trivial.
      generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
      apply Hconfig.
      left; assumption. 
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions pageRootPartition s)) by trivial.      
      generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
      apply Hconfig.
      assert (Hconfigeq : In phySh1Child (getConfigPages partition s')).
      unfold getConfigPages.
      simpl. right; trivial.
      unfold s' in Hconfigeq.
      rewrite getConfigPagesUpdateMappedPageData in *.
      unfold getConfigPages in Hconfigeq.
      simpl in *.
      assumption.
      assert (Hconfigpd : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False)
      by trivial.
      unfold not.
      intros Hfalse. 
      apply Hconfigpd with partition; trivial.
    + apply isEntryPageUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD isPE idxPageDir shadow2 idxSh2 s ;
      trivial. left;trivial.
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions pageRootPartition s)) by trivial.
      generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
      apply Hconfig.
      left; assumption. 
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions pageRootPartition s)) by trivial.      
      generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
      apply Hconfig.
      assert (Hconfigeq : In phySh2Child (getConfigPages partition s')).
      unfold getConfigPages.
      simpl. right; trivial.
      unfold s' in Hconfigeq.
      rewrite getConfigPagesUpdateMappedPageData in *.
      unfold getConfigPages in Hconfigeq.
      simpl in *.
      assumption.
      assert (Hconfigpd : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False)
      by trivial.
      unfold not.
      intros Hfalse. 
      apply Hconfigpd with partition; trivial.
    + apply isEntryPageUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD isPE idxPageDir list idxConfigPagesList s ;
      trivial. left;trivial.
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions pageRootPartition s)) by trivial.
      generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
      apply Hconfig.
      left; assumption. 
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions pageRootPartition s)) by trivial.      
      generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
      apply Hconfig.
      assert (Hconfigeq : In phyConfigPagesList (getConfigPages partition s')).
      unfold getConfigPages.
      simpl. right; trivial.
      unfold s' in Hconfigeq.
      rewrite getConfigPagesUpdateMappedPageData in *.
      unfold getConfigPages in Hconfigeq.
      simpl in *.
      assumption.
      assert (Hconfigpd : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False)
      by trivial.
      unfold not.
      intros Hfalse. 
      apply Hconfigpd with partition; trivial.
    + apply isEntryPageUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD isPE idxPageDir descChild idxRefChild s ;
      trivial. left;trivial.
    + rewrite Hpartions in *. 
      assert((getConfigPages partition s') = 
         (getConfigPages partition s)) as Hconfig.
      apply getConfigPagesUpdateMappedPageData; trivial.
      assert (Hconfigpd : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False)
      by trivial.
      unfold not.
      intros Hfalse. 
      apply Hconfigpd with partition; trivial.
      rewrite Hconfig in *.
      assert(Hii : forall partition : page,
        In partition (getPartitions pageRootPartition s) -> 
        In phyDescChild (getConfigPages partition s) -> False) by trivial.
      assert(Hfalse' : In phyDescChild (getConfigPages partition s)) by trivial.
      apply Hii in Hfalse';trivial. 
(*     + unfold isPartitionFalse;unfold s';cbn.
       rewrite readPDflagUpdateMappedPageData.
       trivial.
       unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse. 
       apply mappedPageIsNotPTable with currentPart currentShadow1 isVE sh1idx pdChild idxPDChild s ;
      trivial. right; left;trivial.
    + unfold s'.
      unfold s' in *.
      rewrite <- isAccessibleMappedPageInParentUpdateMappedPageData
      with currentPart
      level pdChild phyPDChild table curidx x s;trivial.
      assert(Hnotnull : (Nat.eqb defaultPage table) = false) by trivial.
      unfold not;intros Hii.
      rewrite Hii in Hnotnull.
      apply beq_nat_false in Hnotnull.
      now contradict Hnotnull.
    + apply entryUserFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD isPE PDidx pdChild idxPDChild s ;
      trivial. left;trivial.*)
    + unfold isPartitionFalse;unfold s';cbn.
       rewrite readPDflagUpdateMappedPageData.
       trivial.
       unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse. 
      apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 shadow1 idxSh1 s ;
      trivial. right; left;trivial.
(*     + apply entryUserFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD isPE PDidx shadow1 idxSh1 s ;
      trivial. left;trivial. *)
    + unfold isPartitionFalse;unfold s';cbn.
       rewrite readPDflagUpdateMappedPageData.
       trivial.
       unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse. 
       apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 shadow2 idxSh2 s ;
      trivial. right; left;trivial.
(*     + apply entryUserFlagUpdateMappedPageData; trivial. 
      apply mappedPageIsNotPTable with currentPart currentPD isPE PDidx shadow2 idxSh2 s ;
      trivial. left;trivial. *)
    + unfold isPartitionFalse;unfold s';cbn.
       rewrite readPDflagUpdateMappedPageData.
       trivial.
       unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse. 
      apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 list idxConfigPagesList s ;
      trivial. right; left;trivial.
(*     + apply entryUserFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD isPE PDidx list idxConfigPagesList s ;
      trivial. left;trivial. *)
    + unfold isPartitionFalse;unfold s';cbn.
       rewrite readPDflagUpdateMappedPageData.
       trivial.
       unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse. 
       apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 descChild idxRefChild s ;
      trivial. right; left;trivial.
 + unfold isPartitionFalse;unfold s';cbn.
       rewrite readPDflagUpdateMappedPageData.
       trivial.
       unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse. 
       apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 pdChild idxPDChild s ;
      trivial. right; left;trivial.
 (*   + apply entryUserFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD isPE PDidx descChild idxRefChild s ;
      trivial. left;trivial. *) }
Qed.

Lemma indirectionDescriptionUpdateMappedPageContent s descChildphy phyPDChild vaToPrepare l x curidx table idxroot:
let s':= {|      currentPartition := currentPartition s;
          memory := add table curidx
                            x (memory s) pageEq idxEq |} in
 initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
indirectionDescription s descChildphy phyPDChild idxroot vaToPrepare l -> 
In descChildphy (getPartitions pageRootPartition s) ->
partitionDescriptorEntry s -> 
(idxroot = idxPageDir \/ idxroot = idxShadow1 \/ idxroot = idxShadow2)  -> 
indirectionDescription s' descChildphy phyPDChild idxroot vaToPrepare l.
Proof.
intros s' (Hconfig & Hfalse) Hind Hpart Hpde Hor3.
intros.
unfold indirectionDescription in *.
destruct Hind as (  tableroot & Hpp & Hnotnull & Hind).
exists tableroot.
split.
apply nextEntryIsPPUpdateMappedPageData;trivial.
split;trivial.
destruct Hind as [(Heq & Hl) | (nbl & stop & Hnbl & Hstopx & Hind & Hnotnul & Hl)].
+ left. intuition.
+ right.
  exists nbl, stop. 
  split;trivial. 
  split;trivial. 
  split;trivial.
  *
  assert(Htable :stop <= (nbLevel -1) -> ~ In table (getIndirectionsAux tableroot s (S stop))).
intros.
{ assert (Hstop : stop < (nbLevel -1) \/ stop = (nbLevel -1) ) by lia.
  destruct Hstop as [Hlt |  Heq ].
  +
generalize (Hconfig descChildphy Hpart); clear Hconfig; intros Hconfig.
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig .
destruct Hor3 as[Hor3 |[Hor3|Hor3]];subst.
  apply  notConfigTableNotPdconfigTableLt with descChildphy; trivial.
  apply nextEntryIsPPgetPd in Hpp;trivial.
  apply  notConfigTableNotSh1configTableLt with descChildphy; trivial.
  apply nextEntryIsPPgetFstShadow in Hpp;trivial.
  apply  notConfigTableNotSh2configTableLt with descChildphy; trivial.
  apply nextEntryIsPPgetSndShadow in Hpp;trivial.
  
+ subst.
assert(0<nbLevel) by apply nbLevelNotZero.
assert(Hsnbl :  (S (nbLevel - 1)) = nbLevel) by lia.
rewrite Hsnbl.
  generalize (Hconfig descChildphy Hpart); clear Hconfig; intros Hconfig.

destruct Hor3 as[Hor3 |[Hor3|Hor3]];subst.
apply  notConfigTableNotPdconfigTable with descChildphy; trivial.
unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetPd;trivial.
apply  notConfigTableNotSh1configTable with descChildphy; trivial.
unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetFstShadow;trivial.

apply  notConfigTableNotSh2configTable with descChildphy; trivial.
unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetSndShadow;trivial. }
  
assert( getIndirection tableroot vaToPrepare nbl stop s' = getIndirection tableroot vaToPrepare nbl stop s).
{ assert (Hstop3 : stop < (nbLevel -1) \/ stop = (nbLevel -1) \/ stop > (nbLevel -1)) by lia.
  destruct Hstop3 as [Hlt | [ Heq | Hgt]].
  + apply getIndirectionUpdateMappedPageData with nbl;
    trivial. apply Htable. lia.
  + subst.
    apply getIndirectionUpdateMappedPageData with nbl ;trivial.
    apply Htable. lia.
    +
 
  assert(HnbL : Some nbl = StateLib.getNbLevel) by trivial.
assert(Hneww : getIndirection tableroot vaToPrepare nbl stop s = 
            getIndirection tableroot vaToPrepare nbl nbl s).
    { rewrite Hind.
      symmetry.
      apply getIndirectionStopLevelGT2 with stop; trivial.      
      apply getNbLevelLe in HnbL.
      unfold CLevel in HnbL.
      case_eq (lt_dec (nbLevel - 1) nbLevel); intros ii Hii; rewrite Hii in *. 
      simpl in *.
      destruct nbl.
      simpl in *. lia.
      assert(0 < nbLevel) by apply nbLevelNotZero. 
      lia. }
    rewrite Hind.
    apply getIndirectionStopLevelGT with nbl; trivial.
    apply getNbLevelLe in HnbL.
    unfold CLevel in HnbL.
    case_eq (lt_dec (nbLevel - 1) nbLevel); intros ii Hii;rewrite Hii in *.
    simpl in *.
    destruct nbl.
    simpl in *. lia.
    assert(0 < nbLevel) by apply nbLevelNotZero. 
    lia.
    rewrite <- Hind.
    rewrite Hneww.
    apply getIndirectionUpdateMappedPageData with nbl ;trivial.
assert(HnbLevel : S nbl = nbLevel).

apply getNbLevelEq in HnbL.
subst.
rewrite <-  nbLevelEq.
assert(0 < nbLevel) by apply nbLevelNotZero.
lia. 
rewrite HnbLevel. 
 
 generalize (Hconfig descChildphy Hpart); clear Hconfig; intros Hconfig.

destruct Hor3 as[Hor3 |[Hor3|Hor3]];subst.
apply  notConfigTableNotPdconfigTable with descChildphy; trivial.
unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetPd;trivial.
apply  notConfigTableNotSh1configTable with descChildphy; trivial.
unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetFstShadow;trivial.

apply  notConfigTableNotSh2configTable with descChildphy; trivial.
unfold not.
  intros.
  apply Hconfig.
  right; trivial.
  apply nextEntryIsPPgetSndShadow;trivial.
       }
    rewrite H;trivial.
  * intuition.
    
Qed.
Lemma initPEntryTablePreconditionToPropagatePreparePropertiesUpdateMappedPageContent userPage  table curidx x  s:
let  s':={|
      currentPartition := currentPartition s;
      memory := add table curidx x (memory s) pageEq idxEq |} in 
match x with
 | PE _ => isPresentNotDefaultIff s'
 | _ => True
end -> 
consistency s -> 
initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
initPEntryTablePreconditionToPropagatePrepareProperties s userPage -> 
initPEntryTablePreconditionToPropagatePrepareProperties s' userPage.
Proof.
intros s' Hx Hcons (Hcond & Hfalse1) (Hconf & Hfalse).
unfold initPEntryTablePreconditionToPropagatePrepareProperties.
split;trivial.
intros part Hpart.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
{ apply getPartitionsUpdateMappedPageData.
  + unfold consistency in *. intuition.
  + unfold getPartitions.
    destruct nbPage;simpl;left;trivial.
  + unfold initPEntryTablePreconditionToPropagatePrepareProperties in *.
     intros. apply Hcond;trivial.
  + apply beq_nat_false in Hfalse1.
    unfold not; intros.
    apply Hfalse1.
    subst;trivial.
  + unfold consistency in *. intuition. }
rewrite Hpartions in *.
unfold s'.
rewrite getConfigPagesUpdateMappedPageData;trivial.
apply Hconf;trivial.
apply Hcond;trivial.
Qed.
Lemma  propagatePropertiesPrepareUpdateMappedPageContent  s table curidx ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
            currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
            currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA x zeroI fstLL LLChildphy newLastLLable n indMMUToPreparebool:
match x with 
| PE a => isPresentNotDefaultIff {|
                    currentPartition := currentPartition s;
                    memory := add table curidx
                              x (memory s) pageEq idxEq |} 
| _ => True
end ->             
 propagatedPropertiesPrepare indMMUToPreparebool fstLL LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
            currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
            currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false true true true idxFstVA idxSndVA idxTrdVA zeroI n -> 
 initPEntryTablePreconditionToPropagatePrepareProperties s table -> 
 propagatedPropertiesPrepare indMMUToPreparebool fstLL LLChildphy newLastLLable
   {|      currentPartition := currentPartition s;
            memory := add table curidx
                              x (memory s) pageEq idxEq |}ptMMUTrdVA
  phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
  currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
  currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA
  fstVA nbLgen l false false false true true true idxFstVA idxSndVA idxTrdVA zeroI n.
Proof.
intros.
set (s' := {|
  currentPartition := _|}) in *.
unfold propagatedPropertiesPrepare in *.
intros.
unfold indirectionDescriptionAll in *.
unfold  initPEntryTablePreconditionToPropagatePreparePropertiesAll in *.
assert(Hnoduptree : noDupPartitionTree s) .
unfold consistency in *. intuition.
split. 
(** kernelDataIsolation **)
apply kernelDataIsolationUpdateMappedPageData with nbLgen;intuition.
split.
(** partitionsIsolation **)
apply partitionsIsolationUpdateMappedPageData  with nbLgen;intuition.
split.
(** verticalSharing **)
apply verticalSharingUpdateMappedPageData with nbLgen;intuition.
split.
(** consistency *)
apply consistencyUpdateMappedPageData with nbLgen;intuition.
(** propagatedPropertiesPrepare **)
unfold consistency in *.
assert (Hcurpart : In currentPart (getPartitions pageRootPartition s)). 
assert (Hcurpart : currentPartitionInPartitionsList s)by intuition.
unfold currentPartitionInPartitionsList in *.
assert (currentPart = currentPartition s) by intuition.
subst. intuition.
assert( Hpde : partitionDescriptorEntry s) by intuition.
assert (Hnotconfig : forall partition : page,
In partition (getPartitions pageRootPartition s) ->
~ (partition = table \/ In table (getConfigPagesAux partition s))) by 
(unfold  initPEntryTablePreconditionToPropagatePrepareProperties in *; 
  intuition).
 assert(Hfalse : (Nat.eqb pageDefault table) = false) by 
(unfold  initPEntryTablePreconditionToPropagatePrepareProperties in *; 
  intuition).
 
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
{ unfold s'.
 apply getPartitionsUpdateMappedPageData ; trivial.
 + unfold getPartitions.
   destruct nbPage;simpl;left;trivial.
 +
   apply beq_nat_false in Hfalse.
   unfold not; intros.
   apply Hfalse.
   subst;trivial. }
intuition try assumption.
+ apply getTableAddrRootUpdateMappedPageData; trivial.
+ apply isPEUpdateUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s) currentPD isPE idxPageDir trdVA  (StateLib.getIndexOfAddr trdVA levelMin) s ;
  trivial.
  left;trivial.
  intros;subst;split;trivial.
+ assert(Hvaref : exists va : vaddr, 
            isEntryVA ptSh1TrdVA (StateLib.getIndexOfAddr trdVA levelMin) va s /\ 
            vaddrEq vaddrDefault va = true) by trivial.
  destruct Hvaref as (vaRef & Hvaref & Hderivref).
  exists vaRef; split; trivial.
  unfold s'.
  apply isEntryVAUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s) currentShadow1 isVE idxShadow1  trdVA  (StateLib.getIndexOfAddr trdVA levelMin)  s ;
  trivial.
  right;left;trivial.
  intros;subst;split;trivial.
+ apply getTableAddrRootUpdateMappedPageData; trivial.
+ apply isVEUpdateMappedPageData;trivial.
  apply mappedPageIsNotPTable with (currentPartition s) currentShadow1 isVE idxShadow1  trdVA  (StateLib.getIndexOfAddr trdVA levelMin)  s ;
  trivial.
  right;left;trivial.
  intros;subst;split;trivial.
+ apply isEntryPageUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s)  currentPD isPE idxPageDir trdVA  (StateLib.getIndexOfAddr trdVA levelMin) s ;
  trivial.
  left;trivial.
  intros;subst;split;trivial.
+ apply entryPresentFlagUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s)  currentPD  isPE idxPageDir trdVA  (StateLib.getIndexOfAddr trdVA levelMin)  s ;
  trivial.
  left;trivial.
  intros;subst;split;trivial.
+ apply entryUserFlagUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s)  currentPD  isPE idxPageDir trdVA  (StateLib.getIndexOfAddr trdVA levelMin)  s ;
  trivial. left;trivial.    intros;subst;split;trivial.
+ apply getTableAddrRootUpdateMappedPageData; trivial.
+ apply isPEUpdateUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s) currentPD isPE idxPageDir sndVA  (StateLib.getIndexOfAddr sndVA levelMin) s ;
  trivial.
  left;trivial.
  intros;subst;split;trivial.
+ assert(Hvaref : exists va : vaddr, 
            isEntryVA ptSh1SndVA (StateLib.getIndexOfAddr sndVA levelMin) va s /\ 
            vaddrEq vaddrDefault va = true) by trivial.
  destruct Hvaref as (vaRef & Hvaref & Hderivref).
  exists vaRef; split; trivial.
  unfold s'.
  apply isEntryVAUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s) currentShadow1 isVE idxShadow1  sndVA  (StateLib.getIndexOfAddr sndVA levelMin) s ;
  trivial.
  right;left;trivial.
  intros;subst;split;trivial.
+ apply getTableAddrRootUpdateMappedPageData; trivial.
+ apply isVEUpdateMappedPageData;trivial.
  apply mappedPageIsNotPTable with (currentPartition s) currentShadow1 isVE idxShadow1  sndVA  (StateLib.getIndexOfAddr sndVA levelMin)  s ;
  trivial.
  right;left;trivial.
  intros;subst;split;trivial.
+ assert(Hvaref : exists va : vaddr, 
            isEntryVA ptSh1FstVA (StateLib.getIndexOfAddr fstVA levelMin) va s /\ 
            vaddrEq vaddrDefault va = true) by trivial.
  destruct Hvaref as (vaRef & Hvaref & Hderivref).
  exists vaRef; split; trivial.
  unfold s'.
  apply isEntryVAUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s) currentShadow1 isVE idxShadow1  fstVA  (StateLib.getIndexOfAddr fstVA levelMin) s ;
  trivial.
  right;left;trivial.
  intros;subst;split;trivial.
+ apply getTableAddrRootUpdateMappedPageData; trivial.
+ apply isVEUpdateMappedPageData;trivial.
  apply mappedPageIsNotPTable with (currentPartition s) currentShadow1 isVE idxShadow1  fstVA  (StateLib.getIndexOfAddr fstVA levelMin)  s ;
  trivial.
  right;left;trivial.
  intros;subst;split;trivial.
+ apply isEntryPageUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s) currentPD isPE idxPageDir  sndVA  (StateLib.getIndexOfAddr sndVA levelMin)  s ;
  trivial.
  left;trivial.
  intros;subst;split;trivial.
+ apply entryPresentFlagUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s)  currentPD  isPE idxPageDir sndVA  (StateLib.getIndexOfAddr sndVA levelMin)  s ;
  trivial.
  left;trivial.
  intros;subst;split;trivial.
+ apply entryUserFlagUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s)  currentPD  isPE idxPageDir sndVA  (StateLib.getIndexOfAddr sndVA levelMin)  s ;
  trivial. left;trivial.    intros;subst;split;trivial.
+ apply getTableAddrRootUpdateMappedPageData; trivial.
+ apply isPEUpdateUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s) currentPD isPE idxPageDir fstVA  (StateLib.getIndexOfAddr fstVA levelMin) s ;
  trivial.
  left;trivial.
  intros;subst;split;trivial.
+ apply entryUserFlagUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s)  currentPD  isPE idxPageDir fstVA  (StateLib.getIndexOfAddr fstVA levelMin)  s ;
  trivial. left;trivial.    intros;subst;split;trivial.
+ apply entryPresentFlagUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s)  currentPD  isPE idxPageDir fstVA  (StateLib.getIndexOfAddr fstVA levelMin)  s ;
  trivial.
  left;trivial.
  intros;subst;split;trivial.
+ apply isEntryPageUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with (currentPartition s) currentPD isPE idxPageDir  fstVA  (StateLib.getIndexOfAddr fstVA levelMin)  s ;
  trivial.
  left;trivial.
  intros;subst;split;trivial.
+ apply isEntryPageUpdateMappedPageData; trivial.
  assert(Hindchild :
  In phyPDChild (getConfigPages descChildphy s)) .
  apply indirectionDescriptionIsConfigPage  with vaToPrepare l;trivial.
  
  assert (Hchildpart :  In descChildphy (getPartitions pageRootPartition s)) by trivial.
  unfold not . intros.
  apply Hnotconfig with descChildphy ;trivial.
  unfold getConfigPages in Hindchild;simpl in *.
  subst;trivial.
+ apply nextEntryIsPPUpdateMappedPageData; trivial.
+ apply nextEntryIsPPUpdateMappedPageData; trivial.
+ apply nextEntryIsPPUpdateMappedPageData; trivial.
+ rewrite Hpartions;trivial.
+ unfold s';simpl.
  rewrite getChildrenUpdateMappedPageData;trivial.
  apply beq_nat_false in Hfalse.
  unfold not;intros;subst.
  now contradict Hfalse.
  unfold getConfigPages;  simpl.
  unfold not.
  apply Hnotconfig;trivial.
  unfold not;intros;subst.
  apply Hnotconfig with  (currentPartition s);trivial.
  left;trivial.
+ apply indirectionDescriptionUpdateMappedPageContent;trivial.
  left;trivial.
+ apply indirectionDescriptionUpdateMappedPageContent;trivial.
  right;left;trivial.
+ apply indirectionDescriptionUpdateMappedPageContent;trivial.
right;right;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateMappedPageContent;trivial.
  unfold consistency in *;intuition.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateMappedPageContent;trivial.
  unfold consistency in *;intuition.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateMappedPageContent;trivial.
  unfold consistency in *;intuition.
+ 
(* (* + unfold isPartitionFalseAll in *.
  unfold isPartitionFalse;unfold s';cbn;
  repeat  rewrite readPDflagUpdateMappedPageData;trivial;
  unfold not;intros Hfalse1;symmetry in Hfalse1;contradict Hfalse1. 
  apply mappedPageIsNotPTable with (currentPartition s) currentShadow1 isVE sh1idx trdVA idxTrdVA s ;
      trivial.
  right; left;trivial.
  intros;split;subst;trivial.
  apply mappedPageIsNotPTable with (currentPartition s) currentShadow1 isVE sh1idx sndVA idxSndVA s ;
      trivial.
  right; left;trivial.
  intros;split;subst;trivial.
  apply mappedPageIsNotPTable with (currentPartition s) currentShadow1 isVE sh1idx fstVA idxFstVA s ;
      trivial.
  right; left;trivial.
  intros;split;subst;trivial. *)
Qed. *)
Admitted.



Lemma PreCtoPropagateIsWellFormedMMUTablesUpdateMappedPageData curidx
phyPage1 phyPage2 va1 va2 table1 table2 partition level
currentPD s x:
let s':= {|
  currentPartition := currentPartition s;
  memory := add phyPage1 curidx
             x (* (PE {| read := false; write := false; exec := false; present := false; user := false; pa := defaultPage |}) *) 
              (memory s) pageEq idxEq |} in 
match x with
| PE _ =>
    isPresentNotDefaultIff
      {| currentPartition := currentPartition s; memory := add phyPage1 curidx x (memory s) pageEq idxEq |}
| _ => True
end ->              
PreCtoPropagateIsWellFormedMMUTables phyPage1 phyPage2 va1 va2 table1 table2 partition level currentPD s ->
PreCtoPropagateIsWellFormedMMUTables phyPage1 phyPage2 va1 va2 table1 table2 partition level currentPD s'.
Proof.
intros.
unfold PreCtoPropagateIsWellFormedMMUTables in *.
unfold initPEntryTablePreconditionToPropagatePrepareProperties in *.
assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartions.
{ apply getPartitionsUpdateMappedPageData.
  + unfold consistency in *. intuition.
  + unfold getPartitions.
    destruct nbPage;simpl;left;trivial.
  + intuition.
  + assert(Hfalse: (Nat.eqb pageDefault phyPage1) = false) by intuition.
    apply beq_nat_false in Hfalse.
    unfold not; intros.
    apply Hfalse.
    subst;trivial.
  + unfold consistency in *. intuition. }
rewrite Hpartions in *.

assert(Hconfig: forall partition0 : page,
 In partition0 (getPartitions pageRootPartition s) -> partition0 = phyPage1 \/
  In phyPage1 (getConfigPagesAux partition0 s') -> False).
  { assert(Hi:  (forall partition : page,
    In partition (getPartitions pageRootPartition s) -> partition = phyPage1 \/ In phyPage1 (getConfigPagesAux partition s) -> False) ) by intuition.
    intros part Hpart Hor.
    contradict Hor.
    unfold s'.
    rewrite getConfigPagesAuxUpdateMappedPageData; trivial.
    unfold not. apply Hi; trivial.
    unfold not.
    apply Hi; trivial. }
assert(Hi  : initPEntryTablePreconditionToPropagatePrepareProperties s phyPage1) by (unfold initPEntryTablePreconditionToPropagatePrepareProperties;
intuition).
assert(Hpde: partitionDescriptorEntry s) by (unfold consistency in *;intuition).
intuition.
+ apply consistencyUpdateMappedPageData with level;intuition.
(*   apply isPresentNotDefaultIffRightValue.
  unfold consistency in *. 
  intuition.
 *)
+ apply nextEntryIsPPUpdateMappedPageData;trivial.
+ apply isEntryPageUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with partition  currentPD isPE idxPageDir va1 (StateLib.getIndexOfAddr va1 levelMin) s ;
  trivial.
  left;trivial.
  intros;subst;split;trivial.
+ apply isEntryPageUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with partition  currentPD isPE idxPageDir va2 (StateLib.getIndexOfAddr va2 levelMin) s ;
  trivial.
  left;trivial.
  intros;subst;split;trivial.
+ apply isPEUpdateUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with partition  currentPD isPE idxPageDir va1 (StateLib.getIndexOfAddr va1 levelMin) s ;
  trivial.
  left;trivial.
  intros;subst;split;trivial.
+ apply getTableAddrRootUpdateMappedPageData; trivial.
+ apply isPEUpdateUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with partition  currentPD isPE idxPageDir va2 (StateLib.getIndexOfAddr va2 levelMin) s ;
  trivial.
  left;trivial.
  intros;subst;split;trivial.
+ apply getTableAddrRootUpdateMappedPageData; trivial.
+ apply entryPresentFlagUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with partition  currentPD isPE idxPageDir va1  (StateLib.getIndexOfAddr va1 levelMin) s ;
  trivial. left;trivial.
  intros;subst;split;trivial.
+ apply entryPresentFlagUpdateMappedPageData; trivial.
  apply mappedPageIsNotPTable with partition  currentPD isPE idxPageDir va2 (StateLib.getIndexOfAddr va2 levelMin) s ;
  trivial. left;trivial.
  intros;subst;split;trivial.
Qed.

Lemma isPartitionFalseAllUpdateMappedPageContent s currentShadow1 table curidx  ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA  (fstVA sndVA trdVA : vaddr) x:
 initPEntryTablePreconditionToPropagatePrepareProperties s table ->
isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA ->
In (currentPartition s) (getPartitions pageRootPartition s) ->
nextEntryIsPP (currentPartition s) idxShadow1 currentShadow1 s ->
consistency s -> 
StateLib.getIndexOfAddr trdVA levelMin = idxTrdVA ->
isVE ptSh1TrdVA (StateLib.getIndexOfAddr trdVA levelMin) s ->
getTableAddrRoot ptSh1TrdVA idxShadow1 (currentPartition s) trdVA s ->
(Nat.eqb pageDefault ptSh1TrdVA) = false ->
StateLib.getIndexOfAddr sndVA levelMin = idxSndVA ->
isVE ptSh1SndVA (StateLib.getIndexOfAddr sndVA levelMin) s ->
getTableAddrRoot ptSh1SndVA idxShadow1 (currentPartition s) sndVA s ->
(Nat.eqb pageDefault ptSh1SndVA) = false ->
StateLib.getIndexOfAddr fstVA levelMin = idxFstVA ->
isVE ptSh1FstVA (StateLib.getIndexOfAddr fstVA levelMin) s ->
getTableAddrRoot ptSh1FstVA idxShadow1 (currentPartition s) fstVA s ->
(Nat.eqb pageDefault ptSh1FstVA) = false ->
isPartitionFalseAll
  {|
  currentPartition := currentPartition s;
  memory := add table curidx
              x (memory s) pageEq idxEq |}
  ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA.
  Proof.
  intros Hinit Hi.
  intros.
    unfold isPartitionFalseAll in *.
        unfold initPEntryTablePreconditionToPropagatePrepareProperties in *.

    unfold isPartitionFalse in *;cbn;
    repeat  rewrite readPDflagUpdateMappedPageData;trivial;
    unfold not;intros Hfalse1;symmetry in Hfalse1;contradict Hfalse1.  

    eapply mappedPageIsNotPTable with (currentPartition s) currentShadow1 isVE idxShadow1 trdVA idxTrdVA s ;
      trivial.
    right; left;trivial.
    intuition.
    unfold consistency in *;intuition.
    intros;split;subst;trivial.
    apply mappedPageIsNotPTable with (currentPartition s) currentShadow1 isVE idxShadow1 sndVA idxSndVA s ;
      trivial.
    right; left;trivial.
    intuition.
     unfold consistency in *;intuition.
    intros;split;subst;trivial.
    apply mappedPageIsNotPTable with (currentPartition s) currentShadow1 isVE idxShadow1 fstVA idxFstVA s ;
      trivial.
    right; left;trivial.
    intuition.
     unfold consistency in *;intuition.    
    intros;split;subst;trivial.
Qed.
