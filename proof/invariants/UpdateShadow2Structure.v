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
    This file contains required lemmas to prove that updating the second shadow 
    structure preserves isolation and consistency properties  *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Internal.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.InternalLemmas
               Pip.Proof.Isolation Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Invariants PropagatedProperties.
Require Import Coq.Logic.ProofIrrelevance Lia List Bool Compare_dec EqNat.

Lemma getConfigTablesLinkedListUpdateSh2 partition (vaInParent : vaddr) 
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
StateLib.getConfigTablesLinkedList partition
  (add table idx (VA vaInParent) (memory s) beqPage beqIndex) =
StateLib.getConfigTablesLinkedList partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getConfigTablesLinkedList.
case_eq ( StateLib.Index.succ sh3idx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma getFstShadowUpdateSh2 partition (vaInParent : vaddr) 
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
StateLib.getFstShadow partition
  (add table idx (VA vaInParent) (memory s) beqPage beqIndex) =
StateLib.getFstShadow partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getFstShadow.
case_eq ( StateLib.Index.succ sh1idx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma getSndShadowUpdateSh2 partition (vaInParent : vaddr) 
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
StateLib.getSndShadow partition
  (add table idx (VA vaInParent) (memory s) beqPage beqIndex) =
StateLib.getSndShadow partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getSndShadow.
case_eq ( StateLib.Index.succ sh2idx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma getPdUpdateSh2 partition (vaInParent : vaddr) 
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
StateLib.getPd partition
  (add table idx (VA vaInParent) (memory s) beqPage beqIndex) =
StateLib.getPd partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getPd.
case_eq ( StateLib.Index.succ PDidx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.
Lemma getParentUpdateSh2 partition (vaInParent : vaddr) 
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
StateLib.getParent partition
  (add table idx (VA vaInParent) (memory s) beqPage beqIndex) =
StateLib.getParent partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getParent.
case_eq ( StateLib.Index.succ PPRidx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.


Lemma getTablePagesUpdateSh2   (descChild : vaddr) table idx entry size p (s : state)  vaInCurrentPartition:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) -> 
getTablePages p size
 {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |} =
getTablePages p size s.
Proof.
revert p .
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}).
induction size;
intros;  trivial.
simpl.
case_eq(beqPairs (table, idx) (p, CIndex size) beqPage beqIndex);intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
  subst.
  rewrite H.
  apply IHsize;trivial.
+ apply beqPairsFalse in Hpairs.
  assert (lookup   p (CIndex size) (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  p (CIndex size) (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. subst.  intuition. }
  rewrite  Hmemory. 
  destruct (lookup p (CIndex size) (memory s) beqPage beqIndex); 
  [ |apply IHsize; trivial].
  destruct v; try apply IHsize; trivial.
  apply IHsize with p in H.
  rewrite H.
  reflexivity.
Qed.

Lemma getIndirectionsUpdateSh2  (descChild : vaddr) table idx entry pd (s : state) vaInCurrentPartition:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->  
getIndirections pd
  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}  =
getIndirections pd s.
Proof.
intros Hentry.
unfold getIndirections.
revert pd.
induction nbLevel.
simpl. trivial. simpl.
intros. f_equal.
assert (getTablePages pd tableSize {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}= getTablePages pd tableSize s) as Htablepages.
apply getTablePagesUpdateSh2 with entry ;trivial.
rewrite Htablepages.
clear Htablepages.
induction (getTablePages pd tableSize s); intros; trivial.
simpl in *.
rewrite IHn. 
f_equal.
apply IHl.
Qed.

Lemma readPhysicalUpdateSh2 (descChild : vaddr) 
table idx (s : state)  p idx2  entry vaInCurrentPartition: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) -> 
StateLib.readPhysical p idx2
  (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) =
StateLib.readPhysical p idx2 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPhysical.
cbn.
case_eq( beqPairs (table, idx) (p, idx2) beqPage beqIndex); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx2 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
 lookup p idx2 (memory s) beqPage beqIndex ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma getConfigTablesLinkedListsUpdateSh2 sh3  (descChild : vaddr) table idx entry
 (s : state) vaInCurrentPartition:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) -> 
getLLPages sh3
 {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |} (nbPage+1) =
getLLPages sh3 s (nbPage+1).
Proof.
revert sh3.
induction (nbPage+1);trivial.
intros. simpl.
 set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |} ) in *.
destruct (StateLib.getMaxIndex);trivial.
assert(HreadPhyEnt :  StateLib.readPhysical sh3 i
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) = 
    StateLib.readPhysical sh3 i (memory s) ).
apply readPhysicalUpdateSh2 with entry;trivial.
rewrite HreadPhyEnt.
destruct (StateLib.readPhysical sh3 i (memory s));trivial.
destruct (Nat.eqb p defaultPage) ;trivial.
f_equal.
apply IHn; trivial.
Qed. 

Lemma getConfigPagesUpdateSh2 s vaInCurrentPartition table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
forall part : page, getConfigPages part {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}  = getConfigPages part s.
Proof.
intros.
unfold getConfigPages. 
f_equal.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s)
              beqPage beqIndex |}) in *.
unfold getConfigPagesAux.
assert(Hgetpd: StateLib.getPd part (memory s') = StateLib.getPd part (memory s)).
{ simpl. apply getPdUpdateSh2 with entry;trivial. }
rewrite Hgetpd. clear Hgetpd.
case_eq(StateLib.getPd part (memory s));intros; trivial.
assert(Hgetsh1: StateLib.getFstShadow part (memory s') = StateLib.getFstShadow part (memory s)).
{ simpl. apply getFstShadowUpdateSh2 with entry;trivial. }
rewrite Hgetsh1. clear Hgetsh1.
case_eq(StateLib.getFstShadow part (memory s));intros; trivial.
assert(Hgetsh2: StateLib.getSndShadow part (memory s') = StateLib.getSndShadow part (memory s)).
{ simpl. apply getSndShadowUpdateSh2 with entry;trivial. }
rewrite Hgetsh2. clear Hgetsh2.
case_eq(StateLib.getSndShadow part (memory s));intros; trivial.
assert(Hgetconfig: StateLib.getConfigTablesLinkedList part (memory s') =
 StateLib.getConfigTablesLinkedList part (memory s)).
{ simpl. apply getConfigTablesLinkedListUpdateSh2 with entry;trivial. }
rewrite Hgetconfig. clear Hgetconfig.
case_eq(StateLib.getConfigTablesLinkedList part (memory s));intros; trivial.
simpl.
assert(Hind : forall root, getIndirections root s' = getIndirections root s).
{ intros.  
  apply getIndirectionsUpdateSh2 with entry;trivial. }
do 3 rewrite Hind.
do 3 f_equal.
apply getConfigTablesLinkedListsUpdateSh2 with entry;trivial.
Qed.


Lemma getIndirectionUpdateSh2 sh1 table idx s entry va nbL stop vaInCurrentPartition:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
getIndirection sh1 va nbL stop
  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |} =
getIndirection sh1 va nbL stop s .
Proof.
intros Hentry.
revert sh1 nbL.
induction  stop.
+ simpl. trivial.
+ simpl. intros. 
  destruct (StateLib.Level.eqb nbL fstLevel);trivial.
  set (entry0 := (VA vaInCurrentPartition)  ) in *.
  simpl.
  assert ( StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr va nbL)
                  (add table idx entry0 (memory s) beqPage beqIndex) = 
           StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr va nbL) (memory s)) as HreadPhyEnt.
  { unfold StateLib.readPhyEntry.
    cbn.  
    case_eq ( beqPairs (table, idx) (sh1, StateLib.getIndexOfAddr va nbL) beqPage beqIndex);trivial;intros Hpairs.
    + apply beqPairsTrue in Hpairs.
    
      destruct Hpairs as (Htable & Hidx).  subst.
      rewrite Hentry. 
      cbn. trivial.
    + apply beqPairsFalse in Hpairs.
      assert (lookup sh1 (StateLib.getIndexOfAddr va nbL)
                 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
              lookup sh1 (StateLib.getIndexOfAddr va nbL) (memory s) beqPage beqIndex) as Hmemory.
        { apply removeDupIdentity. subst.  intuition. }
      rewrite Hmemory. reflexivity.
   } 
  rewrite HreadPhyEnt.
  destruct (StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr va nbL) (memory s) );trivial.
  destruct (Nat.eqb defaultPage p);trivial.
  destruct ( StateLib.Level.pred nbL );trivial.
Qed.

Lemma readPresentUpdateSh2  idx1
table idx (s : state)  p   entry vaInCurrentPartition: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) -> 
StateLib.readPresent p idx1
  (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) =
StateLib.readPresent p idx1 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPresent.
cbn.
case_eq( beqPairs (table, idx) (p, idx1) beqPage beqIndex); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx1 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
 lookup p idx1 (memory s) beqPage beqIndex ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readAccessibleUpdateSh2 
table idx (s : state)  p  idx1 entry vaInCurrentPartition: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) -> 
StateLib.readAccessible p idx1
  (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) =
StateLib.readAccessible p idx1 (memory s).
Proof.
intros Hentry.
unfold StateLib.readAccessible.
cbn.
case_eq( beqPairs (table, idx) (p, idx1) beqPage beqIndex); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx1 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
 lookup p idx1 (memory s) beqPage beqIndex ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readPhyEntryUpdateSh2 
table idx (s : state)  p  idx1 entry vaInCurrentPartition: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) -> 
StateLib.readPhyEntry p idx1
  (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) =
StateLib.readPhyEntry p idx1 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPhyEntry.
cbn.
case_eq( beqPairs (table, idx) (p, idx1) beqPage beqIndex); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx1 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
 lookup p idx1 (memory s) beqPage beqIndex ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readVirEntryUpdateSh2 
table idx (s : state)  p  idx1 entry vaInCurrentPartition: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) -> 
StateLib.readVirEntry p idx1
  (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) =
StateLib.readVirEntry p idx1 (memory s).
Proof.
intros Hentry.
unfold StateLib.readVirEntry.
cbn.
case_eq( beqPairs (table, idx) (p, idx1) beqPage beqIndex); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx1 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
 lookup p idx1 (memory s) beqPage beqIndex ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readPDflagUpdateSh2 idx1
table idx (s : state)  p   entry vaInCurrentPartition: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) -> 
StateLib.readPDflag p idx1
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) =
   StateLib.readPDflag p idx1 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPDflag.
cbn.
case_eq( beqPairs (table, idx) (p, idx1) beqPage beqIndex); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx1 (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex = 
 lookup p idx1 (memory s) beqPage beqIndex ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma getMappedPageUpdateSh2 root s vaInCurrentPartition table idx va entry:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
getMappedPage root {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}  va = getMappedPage root s va.
Proof.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}) in *.
intros Hentry. 
unfold getMappedPage.
destruct(StateLib.getNbLevel);intros;trivial.
assert(Hind : getIndirection root va l (nbLevel - 1) s' =
getIndirection root va l (nbLevel - 1) s).
apply getIndirectionUpdateSh2 with entry;trivial.
rewrite Hind.  
destruct(getIndirection root va l (nbLevel - 1)  s); intros; trivial.
destruct(Nat.eqb defaultPage p);trivial.
 assert(Hpresent :    StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
  (memory s) = StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) ).
symmetry.
apply readPresentUpdateSh2 with entry; trivial.
unfold s'. simpl.
rewrite <- Hpresent.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) ); trivial.
destruct b; trivial.
assert(Heq :StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) =
   StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s) );intros.
apply readPhyEntryUpdateSh2  with entry; trivial .
rewrite Heq;trivial.
Qed.

Lemma getAccessibleMappedPageUpdateSh2 root s vaInCurrentPartition table idx va entry:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
getAccessibleMappedPage root {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}  va = getAccessibleMappedPage root s va.
Proof.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}) in *.
intros Hentry. 
unfold getAccessibleMappedPage.
destruct(StateLib.getNbLevel);intros;trivial.
assert(Hind : getIndirection root va l (nbLevel - 1) s' =
getIndirection root va l (nbLevel - 1) s).
apply getIndirectionUpdateSh2 with entry;trivial.
rewrite Hind.  
destruct(getIndirection root va l (nbLevel - 1)  s); intros; trivial.
destruct(Nat.eqb defaultPage p);trivial.
 assert(Hpresent :    StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
  (memory s) = StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) ).
symmetry.
apply readPresentUpdateSh2 with entry; trivial.
unfold s'. simpl.
rewrite <- Hpresent.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) ); trivial.
destruct b; trivial.
assert(Haccess :    StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel)
  (memory s) = StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) ).
symmetry.
apply readAccessibleUpdateSh2 with entry; trivial.
unfold s'. simpl.
rewrite <- Haccess.
destruct(StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel) (memory s) ); trivial.
destruct b; trivial.
assert(Heq :StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) =
   StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s) );intros.
apply readPhyEntryUpdateSh2  with entry; trivial .
rewrite Heq;trivial.
Qed.

Lemma getMappedPagesAuxUpdateSh2 root s vaInCurrentPartition table idx entry l:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
getMappedPagesAux root l {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |} = 
getMappedPagesAux root l s.
Proof.
intros Hentry.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}) in *.
unfold getMappedPagesAux.
f_equal.
unfold getMappedPagesOption.
simpl.
induction l.
simpl;trivial.
simpl. 
rewrite IHl;f_equal.
apply getMappedPageUpdateSh2 with entry; trivial.
Qed.


Lemma getAccessibleMappedPagesAuxUpdateSh2 root s vaInCurrentPartition table idx entry l:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
getAccessibleMappedPagesAux root l {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |} = 
getAccessibleMappedPagesAux root l s.
Proof.
intros Hentry.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}) in *.
unfold getAccessibleMappedPagesAux.
f_equal.
unfold getAccessibleMappedPagesOption.
simpl.
induction l.
simpl;trivial.
simpl. 
rewrite IHl;f_equal.
apply getAccessibleMappedPageUpdateSh2 with entry; trivial.
Qed.

Lemma getMappedPagesUpdateSh2 s vaInCurrentPartition table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
forall part : page, getMappedPages part {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}  = getMappedPages part s.
Proof.
intros.
unfold getMappedPages.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s)
              beqPage beqIndex |}) in *.
assert(Hgetpd: StateLib.getPd part (memory s') = StateLib.getPd part (memory s)).
{ simpl. apply getPdUpdateSh2 with entry;trivial. }
rewrite Hgetpd.
case_eq(StateLib.getPd part (memory s));intros; trivial.
apply getMappedPagesAuxUpdateSh2 with entry;trivial.
Qed.

Lemma getAccessibleMappedPagesUpdateSh2 s vaInCurrentPartition table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
forall part : page,
getAccessibleMappedPages part {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}  = getAccessibleMappedPages part s.
Proof.
intros.
unfold getAccessibleMappedPages.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s)
              beqPage beqIndex |}) in *.
assert(Hgetpd: StateLib.getPd part (memory s') = StateLib.getPd part (memory s)).
{ simpl. apply getPdUpdateSh2 with entry;trivial. }
rewrite Hgetpd.
case_eq(StateLib.getPd part (memory s));intros; trivial.
apply getAccessibleMappedPagesAuxUpdateSh2 with entry;trivial.
Qed.

Lemma checkChildUpdateSh2 s vaInCurrentPartition table idx entry l va: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
forall part : page, 
checkChild part l {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |} va = checkChild part l s va.
Proof.
intros Hentry part.
unfold checkChild.
simpl.
assert(Hsh1 : StateLib.getFstShadow part
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex)=
    StateLib.getFstShadow part (memory s)). 
apply getFstShadowUpdateSh2 with entry;trivial.
rewrite Hsh1.
destruct(StateLib.getFstShadow part (memory s) );trivial.
assert(Hind : getIndirection p va l (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} = getIndirection p va l (nbLevel - 1)
    s).
apply getIndirectionUpdateSh2 with entry;trivial.
rewrite Hind.
destruct (getIndirection p va l (nbLevel - 1) s );trivial.
destruct (Nat.eqb p0 defaultPage);trivial.
assert(Hpdflag :  StateLib.readPDflag p0 (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) =
   StateLib.readPDflag p0 (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
  apply readPDflagUpdateSh2 with entry;trivial.
rewrite Hpdflag.
trivial.
Qed.

Lemma getPdsVAddrUpdateSh2 s vaInCurrentPartition table idx entry l: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
forall part : page, 
 getPdsVAddr part l getAllVAddrWithOffset0 {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}  = getPdsVAddr part l getAllVAddrWithOffset0 s.
Proof.
intros.
unfold getPdsVAddr.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s)
              beqPage beqIndex |}) in *.
induction getAllVAddrWithOffset0;simpl;trivial.
assert(Hcheckchild: checkChild part l s' a = checkChild part l s a).
{ simpl. apply checkChildUpdateSh2 with entry;trivial. }
rewrite Hcheckchild;trivial.
case_eq(checkChild part l s a);intros;[
f_equal|];
apply IHl0.
Qed.

Lemma getChildrenUpdateSh2 s vaInCurrentPartition table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) -> 
forall part : page,
getChildren part s = 
getChildren part{|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold getChildren.
set (s' := {|
             currentPartition := currentPartition s;
             memory := add table idx (VA vaInCurrentPartition) (memory s)
                         beqPage beqIndex |}) in *.
intros. 
destruct ( StateLib.getNbLevel);trivial.
simpl.
assert(Hpd :  StateLib.getPd part (memory s) =
StateLib.getPd part
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry.  apply getPdUpdateSh2 with entry;trivial. }
rewrite <- Hpd.
destruct(StateLib.getPd part (memory s));trivial.
assert(Hpds : getPdsVAddr part l getAllVAddrWithOffset0 s' =
 getPdsVAddr part l getAllVAddrWithOffset0 s).
apply getPdsVAddrUpdateSh2 with entry;trivial.
rewrite Hpds.
unfold s'.
symmetry.
apply getMappedPagesAuxUpdateSh2 with entry;trivial.
Qed.

Lemma getPartitionsUpdateSh2 s vaInCurrentPartition table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) -> 
getPartitions multiplexer s = getPartitions multiplexer{|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}. 
Proof.
intros.
generalize multiplexer at 1 2.
unfold getPartitions.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s)
              beqPage beqIndex |}) in *.
induction (nbPage + 1);simpl;trivial.
intros.
f_equal.
assert(Hchildren: getChildren p s' =getChildren p s).
{ symmetry. apply getChildrenUpdateSh2 with entry;trivial. }
rewrite Hchildren. clear Hchildren.
induction (getChildren p s);simpl;trivial.
rewrite IHn.
f_equal.
apply IHl.
Qed.

Lemma isVAUpdateSh2 idx partition table entry idxroot s vaInCurrentPartition:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
isVA partition idxroot s -> 
isVA partition idxroot
  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold isVA.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) beqPage beqIndex);trivial;intros Hpairs.
apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition idxroot   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma nextEntryIsPPUpdateSh2 idx partition table  entry idxroot PPentry s vaInCurrentPartition:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
nextEntryIsPP partition idxroot PPentry s <-> 
nextEntryIsPP partition idxroot PPentry
   {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}.
Proof.
split;intros Hentry;
unfold nextEntryIsPP in *;
cbn;
destruct ( StateLib.Index.succ idxroot); trivial.
- case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
   + apply beqPairsTrue in Hpairs.
     destruct Hpairs as (Htable & Hidx).  subst.      
     rewrite H in *.
     trivial.
   + apply beqPairsFalse in Hpairs.
     assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
             beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
     { apply removeDupIdentity. intuition. }
       rewrite Hmemory. trivial.
- cbn in *.
  case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
  + rewrite Hpairs in *; now contradict Hentry.
  + rewrite Hpairs in *.
    assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity.  apply beqPairsFalse in Hpairs. intuition. }
     rewrite Hmemory in *. trivial.     
Qed.

Lemma isPEUpdateSh2 idx partition table  entry idxroot s vaInCurrentPartition:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
isPE partition idxroot s -> 
isPE partition idxroot
  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold isPE.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition idxroot   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma isVEUpdateSh2 idx partition table  entry idxroot s vaInCurrentPartition:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
isVE partition idxroot s -> 
isVE partition idxroot
  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold isVE.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition idxroot   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.


Lemma entryUserFlagUpdateSh2 idx ptVaInCurPartpd idxvaInCurPart table 
 entry s vaInCurrentPartition accessiblesrc:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
entryUserFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc s -> 
entryUserFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc
  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold entryUserFlag.
cbn.
case_eq (beqPairs (table, idx) (ptVaInCurPartpd, idxvaInCurPart) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptVaInCurPartpd idxvaInCurPart (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  ptVaInCurPartpd idxvaInCurPart   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma entryPresentFlagUpdateSh2 idx ptVaInCurPartpd idxvaInCurPart table 
 entry s vaInCurrentPartition accessiblesrc:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
entryPresentFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc s -> 
entryPresentFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc
  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold entryPresentFlag.
cbn.
case_eq (beqPairs (table, idx) (ptVaInCurPartpd, idxvaInCurPart) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptVaInCurPartpd idxvaInCurPart (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  ptVaInCurPartpd idxvaInCurPart   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma entryPDFlagUpdateSh2 idx ptDescChild table idxDescChild entry s vaInCurrentPartition flag:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
entryPDFlag ptDescChild idxDescChild flag s -> 
entryPDFlag ptDescChild idxDescChild flag
  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold entryPDFlag.
cbn.
case_eq (beqPairs (table, idx) (ptDescChild, idxDescChild) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptDescChild idxDescChild (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  ptDescChild idxDescChild   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma isEntryVAUpdateSh2 idx ptVaInCurPart table idxvaInCurPart entry s  vainve vaInCurrentPartition:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
isEntryVA ptVaInCurPart idxvaInCurPart vainve s -> 
isEntryVA ptVaInCurPart idxvaInCurPart vainve
  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold isEntryVA.
cbn.
case_eq (beqPairs (table, idx) (ptVaInCurPart, idxvaInCurPart) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptVaInCurPart idxvaInCurPart (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  ptVaInCurPart idxvaInCurPart  (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma isEntryPageUpdateSh2 idx ptVaInCurPart table idxvaInCurPart entry s  vainve vaInCurrentPartition:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
isEntryPage ptVaInCurPart idxvaInCurPart vainve s -> 
isEntryPage ptVaInCurPart idxvaInCurPart vainve
  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold isEntryPage.
cbn.
case_eq (beqPairs (table, idx) (ptVaInCurPart, idxvaInCurPart) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptVaInCurPart idxvaInCurPart (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  ptVaInCurPart idxvaInCurPart  (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma partitionsIsolationUpdateSh2 s vaInCurrentPartition table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
partitionsIsolation s ->
partitionsIsolation {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}) in *. 
unfold partitionsIsolation in *. 
  intros Hisopart parent child1 child2 Hparent Hchild1 Hchild2 Hdist.
  assert (Hused : forall part, getUsedPages part s' = getUsedPages part s). 
  { intros. 
    unfold getUsedPages in *. 
    assert(Hconfig : forall part, getConfigPages part s' = getConfigPages part s).
    { intros.
      apply getConfigPagesUpdateSh2 with entry;trivial. } 
    rewrite Hconfig in *.
    f_equal.
    assert(Hmap :  forall part, getMappedPages part s' = getMappedPages part s).
    { intros.
      apply getMappedPagesUpdateSh2 with entry;trivial. } 
    rewrite Hmap in *;trivial. }
    do 2 rewrite Hused.
  assert(Hparts : getPartitions multiplexer s = getPartitions multiplexer s').
  apply getPartitionsUpdateSh2 with entry;trivial.
  rewrite Hparts in *;trivial.
  assert(Hchildren : getChildren parent s = getChildren parent s').
  apply getChildrenUpdateSh2 with entry;trivial.
  rewrite <- Hchildren in *.
  apply Hisopart with parent;trivial.
Qed.

Lemma kernelDataIsolationUpdateSh2 s vaInCurrentPartition table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
kernelDataIsolation s ->
kernelDataIsolation {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}) in *. 
unfold kernelDataIsolation in *. 
intros Hkdi partition1 partition2 Hpart1 Hpart2.
assert(Hparts : getPartitions multiplexer s = getPartitions multiplexer s').
apply getPartitionsUpdateSh2 with entry;trivial.
rewrite <- Hparts in *;trivial. clear Hparts.
assert(Hconfig : forall part, getConfigPages part s' = getConfigPages part s).
{ intros.
apply getConfigPagesUpdateSh2 with entry;trivial. } 
rewrite Hconfig in *. clear Hconfig.
assert(Haccessmap : forall part, getAccessibleMappedPages part s' =
getAccessibleMappedPages part s).
{ apply getAccessibleMappedPagesUpdateSh2 with entry;trivial. }
rewrite Haccessmap in *. 
apply Hkdi;trivial.
Qed.  

Lemma verticalSharingUpdateSh2 s vaInCurrentPartition table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
verticalSharing s ->
verticalSharing {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}) in *. 
unfold verticalSharing in *.
intros Hvs parent child Hparent Hchild.
assert(Hparts : getPartitions multiplexer s = getPartitions multiplexer s').
apply getPartitionsUpdateSh2 with entry;trivial.
rewrite <- Hparts in *;trivial. clear Hparts.
assert(Hchildren : getChildren parent s = getChildren parent s').
apply getChildrenUpdateSh2 with entry;trivial.
rewrite <- Hchildren in *. clear Hchildren.
assert(Hmap :  forall part, getMappedPages part s' = getMappedPages part s).
{ intros.
  apply getMappedPagesUpdateSh2 with entry;trivial. } 
  rewrite Hmap in *;trivial.
assert (Hused : forall part, getUsedPages part s' = getUsedPages part s). 
{ intros. 
  unfold getUsedPages in *. 
  assert(Hconfig : forall part, getConfigPages part s' = getConfigPages part s).
  { intros.
    apply getConfigPagesUpdateSh2 with entry;trivial. } 
  rewrite Hconfig in *.
  f_equal. trivial.  }
rewrite Hused;trivial.
apply Hvs;trivial.
Qed.

Lemma partitionDescriptorEntryUpdateSh2 s vaInCurrentPartition table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
partitionDescriptorEntry s ->
partitionDescriptorEntry {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}) in *. 
unfold partitionDescriptorEntry in *. 
intros Hpde part Hpart idxroot Hidxroot.
assert(Hidx : idxroot < tableSize - 1 ).
{ assert(tableSizeLowerBound < tableSize).
  apply tableSizeBigEnough.
  unfold tableSizeLowerBound in *.
  intuition subst.
  unfold PDidx.
  unfold CIndex.
  case_eq( lt_dec 2 tableSize );intros;
  simpl;lia.
  unfold sh1idx.
  unfold CIndex.
  case_eq( lt_dec 4 tableSize );intros;
  simpl;lia.
   unfold sh2idx.
  unfold CIndex.
  case_eq( lt_dec 6 tableSize );intros;
  simpl;lia.
   unfold sh3idx.
  unfold CIndex.
  case_eq( lt_dec 8 tableSize );intros;
  simpl;lia.
  unfold PPRidx.
  unfold CIndex.
  case_eq( lt_dec 10 tableSize );intros;
  simpl;lia.    
  unfold PRidx.
  unfold CIndex.
  case_eq( lt_dec 0 tableSize );intros;
  simpl;lia. }
assert(Hparts : getPartitions multiplexer s = getPartitions multiplexer s').
apply getPartitionsUpdateSh2 with entry;trivial.
rewrite <- Hparts in *;trivial. clear Hparts.
assert (HVA : forall p idx, isVA p idx s -> isVA p idx s').
{ intros.
  apply  isVAUpdateSh2 with entry;trivial. }
assert (HPE : forall p idx x, nextEntryIsPP p idx x s -> 
            nextEntryIsPP   p idx x s').
{ intros. apply nextEntryIsPPUpdateSh2 with entry;trivial. }
assert(Hconcl : idxroot < tableSize - 1 /\
       isVA part idxroot s /\
       (exists entry : page,
          nextEntryIsPP part idxroot entry s /\ entry <> defaultPage)).
apply Hpde;trivial.
destruct Hconcl as (Hi1 & Hi2 & Hi3).
split;trivial.
split.
apply HVA;trivial.
destruct Hi3 as (entry0 & Hentry & Htrue).
exists entry0;split;trivial.
apply HPE;trivial.
Qed.

Lemma dataStructurePdSh1Sh2asRootUpdateSh2 s vaInCurrentPartition table idx entry idxroot: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
dataStructurePdSh1Sh2asRoot idxroot s ->
dataStructurePdSh1Sh2asRoot idxroot {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}) in *. 
unfold dataStructurePdSh1Sh2asRoot in *.
intros Hds.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer s').
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions.
unfold s' in *.
intros.
rewrite <- nextEntryIsPPUpdateSh2 in H0; try eassumption.
assert (Hind : getIndirection entry0 va level stop s = Some indirection).
{ rewrite <- H3. symmetry.
  apply getIndirectionUpdateSh2 with entry; trivial. }
clear H3.
assert(Hdss :indirection = defaultPage \/
      (stop < level /\ isPE indirection idx0 s \/
       stop >= level /\
       (isVE indirection idx0 s /\ idxroot = sh1idx \/
        isVA indirection idx0 s /\ idxroot = sh2idx \/ isPE indirection idx0 s /\ idxroot = PDidx)) /\
      indirection <> defaultPage).
apply Hds with partition entry0 va; trivial.
clear Hds.
destruct Hdss as [Hds | Hds];[left;trivial|].
right.
destruct Hds as (Hds & Hnotnull); split; trivial.
destruct Hds as [(Hlt & Hpe) | Hds].
+ left; split; trivial.
  apply isPEUpdateSh2 with entry; trivial.
+ right.
  destruct Hds as (Hlevel & [(Hve & Hidx) | [(Hva & Hidx) | (Hpe & Hidx)]]).
  split; trivial.
  - left; split; trivial.
    apply isVEUpdateSh2 with entry; trivial.
  - split; trivial.
    right; left;split; trivial.
    apply isVAUpdateSh2 with entry; trivial.
  - split;trivial.
    right;right; split; trivial.
    apply isPEUpdateSh2 with entry; trivial.
Qed.

Lemma currentPartitionInPartitionsListUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
currentPartitionInPartitionsList s ->
currentPartitionInPartitionsList {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup.
unfold currentPartitionInPartitionsList.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions;trivial.
Qed.

Lemma noDupMappedPagesListUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
noDupMappedPagesList s ->
noDupMappedPagesList {|
currentPartition := currentPartition s;
memory := add table idx (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup.
unfold noDupMappedPagesList.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hmap :  forall part, getMappedPages part {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}= getMappedPages part s).
{ intros.
  apply getMappedPagesUpdateSh2 with entry;trivial. }
  rewrite Hmap;trivial.
apply H;trivial.
Qed.

Lemma noDupConfigPagesListUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
noDupConfigPagesList s ->
noDupConfigPagesList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}. 
Proof.
intros Hlookup.
unfold noDupConfigPagesList.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hind :  forall part, getConfigPages part {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}= getConfigPages part s).
{ intros.
  apply getConfigPagesUpdateSh2 with entry;trivial. }
  rewrite Hind;trivial.
apply H ;trivial.
Qed. 

Lemma parentInPartitionListUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
parentInPartitionList s ->
parentInPartitionList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}. 
Proof.
intros Hlookup.
unfold parentInPartitionList.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
apply H with partition;trivial.
rewrite nextEntryIsPPUpdateSh2 with entry;trivial.
eapply H1.
eapply Hlookup.
Qed. 

Lemma getPDFlagUpdateSh2 s vaInCurrentPartition table idx entry sh1 va: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
getPDFlag sh1 va
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |} = getPDFlag sh1 va s.
Proof.
intros Hentry.
unfold getPDFlag.
simpl.
destruct (StateLib.getNbLevel);trivial.
assert(Hind : getIndirection sh1 va l (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} = getIndirection  sh1 va l (nbLevel - 1)
    s).
apply getIndirectionUpdateSh2 with entry;trivial.
rewrite Hind.
destruct (getIndirection  sh1 va l (nbLevel - 1) s );trivial.
destruct (Nat.eqb p defaultPage);trivial.
assert(Hpdflag :  StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) =
   StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
  apply readPDflagUpdateSh2 with entry;trivial.
rewrite Hpdflag.
trivial.
Qed. 

Lemma accessibleVAIsNotPartitionDescriptorUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
accessibleVAIsNotPartitionDescriptor s ->
accessibleVAIsNotPartitionDescriptor
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}. 
Proof.
intros Hlookup.
unfold accessibleVAIsNotPartitionDescriptor.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Haccessmap : forall part, getAccessibleMappedPage part {|
       currentPartition := currentPartition s;
       memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                   beqIndex |} va =
getAccessibleMappedPage part s va).
{ intros. apply getAccessibleMappedPageUpdateSh2 with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
assert(Hpd :  StateLib.getPd partition (memory s) =
StateLib.getPd partition
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry.  apply getPdUpdateSh2 with entry;trivial. }
rewrite <- Hpd in *.
assert(Hsh1 :  StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry.  apply getFstShadowUpdateSh2 with entry;trivial. }
rewrite <- Hsh1 in *.
rewrite <- H with partition va pd sh1 page;trivial.
apply getPDFlagUpdateSh2 with entry;trivial.
Qed. 

Lemma readVirtualUpdateSh2 table1 table2 idx1 idx2  vaInCurrentPartition s :
table1 <> table2 \/ idx1 <> idx2 -> 
 StateLib.readVirtual table1 idx1
         (add table2 idx2 (VA vaInCurrentPartition) (memory s) beqPage
     beqIndex)  = 
 StateLib.readVirtual table1 idx1 (memory s).
Proof.
unfold StateLib.readVirtual.
cbn.
intros Hnoteq.
assert(Hfalse : beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex = false).
apply beqPairsFalse; intuition.
rewrite Hfalse.
assert(Hmemory : lookup table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex) 
          beqPage beqIndex =  lookup table1 idx1 (memory s) beqPage beqIndex ).
apply removeDupIdentity ; intuition.
rewrite Hmemory.
trivial. 
Qed.

Lemma accessibleChildPageIsAccessibleIntoParentUpdateSh2 s entry (vaInCurrentPartition vaChild: vaddr)  currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level:
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
negb presentDescPhy = false -> 
lookup ptVaChildsh2 idxvaChild  (memory s) beqPage beqIndex = Some (VA entry) ->
propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level -> 
accessibleChildPageIsAccessibleIntoParent s ->
accessibleChildPageIsAccessibleIntoParent
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildsh2 idxvaChild  (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}. 
Proof.
intros Hlegit1 Hlegit Hlookup Hprops.

unfold accessibleChildPageIsAccessibleIntoParent.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add ptVaChildsh2 idxvaChild  (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Haccessmap : forall part, getAccessibleMappedPage part {|
       currentPartition := currentPartition s;
       memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
                   beqIndex |} va =
getAccessibleMappedPage part s va).
{ intros. apply getAccessibleMappedPageUpdateSh2 with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
assert(Hpd :  StateLib.getPd partition (memory s) =
StateLib.getPd partition
    (add ptVaChildsh2 idxvaChild  (VA vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry.  apply getPdUpdateSh2 with entry;trivial. }
rewrite <- Hpd in *.
clear Hpd.
assert(Hor : partition = phyDescChild \/ partition <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor];
subst.
+ unfold propagatedPropertiesAddVaddr in *.
  assert (Hpdeq : pdChildphy = pd). 
  { apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
    intuition. }
  subst pd.
  assert(Hor: StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/ 
         StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va level = false).
  { destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va level);intuition. }
  destruct Hor as [Hor | Hor].
  - assert(Hlastidx : (StateLib.getIndexOfAddr vaChild fstLevel) = 
  (StateLib.getIndexOfAddr va fstLevel)).
    { apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level; trivial.
      unfold fstLevel.
      unfold CLevel.
      case_eq ( lt_dec 0 nbLevel );intros.
      simpl.
      lia.
      assert(0<nbLevel) by apply nbLevelNotZero.
      lia.
      destruct level;simpl; lia. }
  rewrite Hlastidx in *. 
  assert(Htrue : getAccessibleMappedPage pdChildphy s va = NonePage).
  { apply getAccessibleMappedPageNotPresent with ptVaChildpd phyDescChild;intuition.
    + subst;trivial.
    + assert(Hget : getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
      unfold getTableAddrRoot in *.
      destruct Hget as(Hi & Hget).
      split;trivial.
      intros tableroot Hpp.
      apply Hget in Hpp.
      destruct Hpp as ( nbL & HnbL & stop & Hstop & Hind).
      exists nbL;split;trivial.
      exists stop;split;trivial.
      rewrite <- Hind.
      apply getIndirectionEq;trivial.
      apply getNbLevelLt.
      symmetry;trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
      rewrite <- HnbL in *. 
      assert(Hlevel : Some level = Some nbL) by trivial.
      inversion Hlevel.
      subst;trivial.
    + repeat rewrite andb_true_iff in Hlegit1.
      rewrite negb_true_iff in *. 
      intuition.
      subst;trivial. }
  rewrite Htrue in *. 
  assert(Hfalse : NonePage = SomePage accessiblePage) by trivial.
  now contradict Hfalse.
  - assert(Hconcl : isAccessibleMappedPageInParent phyDescChild va accessiblePage
    {|
    currentPartition := currentPartition s;
    memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s)
              beqPage beqIndex |} = 
  isAccessibleMappedPageInParent  phyDescChild va accessiblePage s). 
  { unfold isAccessibleMappedPageInParent.
    simpl.
    assert(Hsh2 :  StateLib.getSndShadow phyDescChild
    (add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
       beqIndex) =  StateLib.getSndShadow phyDescChild (memory s)).
    apply getSndShadowUpdateSh2 with entry;trivial.
    rewrite Hsh2. clear Hsh2.
    assert(Hsh2child :  nextEntryIsPP phyDescChild sh2idx sh2Childphy s) by intuition.
     rewrite nextEntryIsPPgetSndShadow in *. 
 rewrite Hsh2child.
 assert(Hsh2virt : getVirtualAddressSh2 sh2Childphy
    {|
    currentPartition := currentPartition s;
    memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition)
                (memory s) beqPage beqIndex |} va = getVirtualAddressSh2 sh2Childphy s va ).
  { unfold getVirtualAddressSh2.  
    assert (Hlevel : Some level = StateLib.getNbLevel) by intuition.
    rewrite <- Hlevel.
    assert(Hind : getIndirection sh2Childphy va level (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} = getIndirection  sh2Childphy va level (nbLevel - 1)
    s).
    { apply getIndirectionUpdateSh2 with entry;trivial. }
    rewrite Hind.
    case_eq (getIndirection  sh2Childphy va level (nbLevel - 1) s );
    [ intros tbl Htbl | intros Htbl]; trivial.
    case_eq (Nat.eqb defaultPage tbl);trivial.
    intros Htblnotnul.
    simpl. 
    assert(Hdiff : tbl <> ptVaChildsh2 \/ 
         (StateLib.getIndexOfAddr va fstLevel) <> 
         StateLib.getIndexOfAddr vaChild fstLevel).
   {
  unfold consistency in *.
  assert(Hnodup : noDupConfigPagesList s) by intuition.
 { apply pageTablesOrIndicesAreDifferent with sh2Childphy sh2Childphy level 
      nbLevel  s;trivial.
  apply rootStructNotNull with phyDescChild s sh2idx;intuition.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
  apply rootStructNotNull with phyDescChild s sh2idx;intuition.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
  apply noDupConfigPagesListNoDupGetIndirections with phyDescChild sh2idx;trivial.
  intuition.  unfold noDupConfigPagesList in Hnodup. 
  apply Hnodup ;intuition.
  do 2 right;trivial.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
    apply noDupConfigPagesListNoDupGetIndirections with phyDescChild sh2idx;trivial.
  intuition.  unfold noDupConfigPagesList in Hnodup. 
  apply Hnodup ;intuition.
  do 2 right;trivial.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
  rewrite <- Hor.
  rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
  assert(level = CLevel (nbLevel - 1) ). 
  apply getNbLevelEq;trivial.
  left;split;trivial.
  apply beq_nat_false in Htblnotnul.
  unfold not; intros Htmp;subst;now contradict Htblnotnul.
  assert(Hnotnull : (Nat.eqb defaultPage ptVaChildsh2) = false) by intuition.
  apply beq_nat_false in Hnotnull.
  unfold not; intros Htmp;subst;now contradict Hnotnull.
  apply getIndirectionStopLevelGT  with (nbLevel - 1) ;trivial.
  apply getNbLevelLt;intuition.
  apply getNbLevelEq in Hlevel.
  subst.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel);intros Hl Hli .
  simpl.
  lia.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia.
  subst.
  assert(getTableAddrRoot ptVaChildsh2 sh2idx phyDescChild vaChild s /\
   isVA ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel) s)
   as (Htblroot & Hva) 
  by intuition.
  assert(Hnewgoal : getIndirection sh2Childphy vaChild level (nbLevel -1) s 
  = Some ptVaChildsh2). 
  apply getIndirectionGetTableRoot2 with phyDescChild;trivial.
  rewrite Hlevel;trivial.
  intros.
  split;subst;trivial.
  apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
    apply getNbLevelLt;intuition.
  apply getNbLevelEq in Hlevel.
  subst.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel);intros Hl Hli .
  simpl.
  lia.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia.
 } }
 move Hlookup at bottom.
 clear Hind .
apply readVirtualUpdateSh2.
destruct Hdiff.
left;trivial.
right. 
assert(Hidx :  StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild ) by intuition.
rewrite <- Hidx.
trivial.
 } 
  rewrite Hsh2virt.
  case_eq(getVirtualAddressSh2 sh2Childphy s va );[ intros vaInParent Hvainparent | intros Hvainparent];
  trivial. 
  assert(Hparent : StateLib.getParent phyDescChild
      (add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
         beqIndex) = StateLib.getParent phyDescChild (memory s)).
  apply getParentUpdateSh2 with entry;trivial.
  rewrite Hparent.
  destruct (StateLib.getParent phyDescChild (memory s) );trivial.
  assert(Hpd :  StateLib.getPd p (memory s) =
  StateLib.getPd p
      (add ptVaChildsh2 idxvaChild  (VA vaInCurrentPartition) (memory s) beqPage beqIndex)).
  { symmetry.  apply getPdUpdateSh2 with entry;trivial. }
  rewrite <- Hpd in *.
  clear Hpd.
  destruct (StateLib.getPd p (memory s));trivial.
  assert(Haccessmap : forall part, getAccessibleMappedPage part {|
         currentPartition := currentPartition s;
         memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
                     beqIndex |} vaInParent =
  getAccessibleMappedPage part s vaInParent).
  { intros. apply getAccessibleMappedPageUpdateSh2 with entry;trivial. }
  rewrite Haccessmap in *. clear Haccessmap.
  trivial. }
  rewrite Hconcl.
  apply H with pdChildphy;trivial.
+ assert  (Htrue : isAccessibleMappedPageInParent partition va accessiblePage
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s)
              beqPage beqIndex |} = 
      isAccessibleMappedPageInParent partition va accessiblePage s). 
 { unfold   isAccessibleMappedPageInParent.
   simpl. 
  assert(Hsh2 : StateLib.getSndShadow partition
    (add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
       beqIndex) = StateLib.getSndShadow partition (memory s)).
  { apply getSndShadowUpdateSh2 with entry;trivial. }
  rewrite Hsh2.
  case_eq (StateLib.getSndShadow partition (memory s));[ intros sh2 Hsh2part | intros Hnone];trivial. 
  assert(Hgetva : getVirtualAddressSh2 sh2
    {|
    currentPartition := currentPartition s;
    memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition)
                (memory s) beqPage beqIndex |} va =
     getVirtualAddressSh2 sh2 s va). 
  { unfold getVirtualAddressSh2. 
    unfold propagatedPropertiesAddVaddr in *. 
    assert(Hlevel : Some level = StateLib.getNbLevel) by intuition.
    rewrite <- Hlevel.
    assert(Hind : getIndirection sh2 va level (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} = getIndirection  sh2 va level (nbLevel - 1)
    s).
    { apply getIndirectionUpdateSh2 with entry;trivial. }
    rewrite Hind.
    case_eq (getIndirection  sh2 va level (nbLevel - 1) s );
    [ intros tbl Htbl | intros Htbl]; trivial.
    case_eq (Nat.eqb defaultPage tbl);trivial.
    intros Htblnotnul.
    simpl.
    apply readVirtualUpdateSh2;trivial.
    left. 
    assert(Hconfig : configTablesAreDifferent s ) by (
    unfold consistency in *; intuition).
    unfold configTablesAreDifferent in *. 
    assert(Hinconfig1 : In tbl (getConfigPages partition s)).
    { assert (Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
      apply pdSh1Sh2ListExistsNotNull with s partition  in Hpde;trivial.
      destruct Hpde as ((pd1 & Hpd1 & Hpdnotnull) 
        & (sh1 & Hsh1 & Hsh1notnull) & (sh22 & Hsh22 & Hsh2notnull) & 
        (sh3 & Hsh3 & Hsh3notnull)).
      unfold getConfigPages.
      unfold getConfigPagesAux.
      rewrite H1, Hsh1, Hsh2part, Hsh3.
      simpl.
      right.
      do 2 (rewrite in_app_iff;
      right).
       rewrite in_app_iff.
      left.
      apply getIndirectionInGetIndirections with va level (nbLevel - 1);trivial.
      apply nbLevelNotZero.
      apply beq_nat_false in Htblnotnul.
      unfold not;intros Hfalse;subst; now contradict Htblnotnul.
      apply getNbLevelLe;intuition.
      unfold consistency in *.
      apply rootStructNotNull with partition s sh2idx;intuition.
      rewrite nextEntryIsPPgetSndShadow in *;trivial.  }
    assert(Hinconfig2 : In ptVaChildsh2 (getConfigPages phyDescChild s)).
    { assert (Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
      (* apply pdSh1Sh2ListExistsNotNull with s phyDescChild  in Hpde;trivial.
      Focus 2.
      assert(Hchild : In phyDescChild (getChildren (currentPartition s) s) )
      by intuition.
      unfold consistency in *. 
      apply childrenPartitionInPartitionList with (currentPartition s);intuition. 
      subst;trivial. *)
      apply isConfigTableSh2WithVA with vaChild;trivial.
      assert(Hchild : In phyDescChild (getChildren (currentPartition s) s) )
      by intuition.
      unfold consistency in *. 
      apply childrenPartitionInPartitionList with (currentPartition s);intuition. 
      subst;trivial.
      intros;subst;split;intuition.
      intuition. }
    unfold not;intros; subst.
    unfold Lib.disjoint in *.
    contradict Hinconfig2.
    apply Hconfig with partition;trivial.  
    assert(Hchild : In phyDescChild (getChildren (currentPartition s) s) )
      by intuition.
      unfold consistency in *. 
      apply childrenPartitionInPartitionList with (currentPartition s);intuition. 
  }           
  rewrite Hgetva.  
  case_eq (getVirtualAddressSh2 sh2 s va);[ intros vainparent Hvainparent | intros Hnone];trivial. 
  assert(Hparent : StateLib.getParent partition
    (add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
       beqIndex) = StateLib.getParent partition (memory s)).
  apply getParentUpdateSh2 with entry;trivial.
  rewrite Hparent.
  destruct (StateLib.getParent partition (memory s) );trivial.
  assert(Hpd :  StateLib.getPd p (memory s) =
  StateLib.getPd p
      (add ptVaChildsh2 idxvaChild  (VA vaInCurrentPartition) (memory s) beqPage beqIndex)).
  { symmetry.  apply getPdUpdateSh2 with entry;trivial. }
  rewrite <- Hpd in *.
  clear Hpd.
  destruct (StateLib.getPd p (memory s));trivial.
  assert(Haccessmap : forall part, getAccessibleMappedPage part {|
         currentPartition := currentPartition s;
         memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
                     beqIndex |} vainparent =
  getAccessibleMappedPage part s vainparent).
  { intros. apply getAccessibleMappedPageUpdateSh2 with entry;trivial. }
  rewrite Haccessmap in *. clear Haccessmap.
  trivial. }
  rewrite Htrue.
  apply H with pd;trivial.     
Qed.

Lemma getAncestorsUpdateSh2 s vaInCurrentPartition table idx entry partition: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
getAncestors partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s)
              beqPage beqIndex |} =
                      getAncestors partition s.
Proof. 
intros Hlookup.
unfold getAncestors.
simpl.
revert partition. 
induction (nbPage + 1);trivial.
simpl;intros.
assert(Hparent : StateLib.getParent partition
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage
       beqIndex) = StateLib.getParent partition (memory s)).
{  apply getParentUpdateSh2 with entry;trivial. }
rewrite Hparent.
destruct (StateLib.getParent partition (memory s) );trivial.
f_equal.
apply IHn;trivial.
Qed.

Lemma noCycleInPartitionTreeUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
noCycleInPartitionTree s -> 
noCycleInPartitionTree
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold noCycleInPartitionTree.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hancestor :getAncestors partition
          {|
          currentPartition := currentPartition s;
          memory := add table idx (VA vaInCurrentPartition) (memory s)
                      beqPage beqIndex |} =
                      getAncestors partition s).
apply getAncestorsUpdateSh2 with entry;trivial.
rewrite Hancestor in *.
apply H;trivial.
Qed.

Lemma configTablesAreDifferentUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
configTablesAreDifferent s -> 
configTablesAreDifferent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold configTablesAreDifferent.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hconfig : forall part, getConfigPages part {|
          currentPartition := currentPartition s;
          memory := add table idx (VA vaInCurrentPartition) (memory s)
                      beqPage beqIndex |} = getConfigPages part s).
{ intros.
apply getConfigPagesUpdateSh2 with entry;trivial. } 
rewrite Hconfig in *. 
rewrite Hconfig in *. 
clear Hconfig.
apply H;trivial.
Qed.

Lemma isChildUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
isChild s -> 
isChild
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold isChild.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hchildren : forall part, getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |} = getChildren part s).
{ intros.
symmetry.
apply getChildrenUpdateSh2 with entry;trivial. } 
rewrite Hchildren in *.
clear Hchildren.
assert(Hparent : StateLib.getParent partition
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage
       beqIndex) = StateLib.getParent partition (memory s)).
{  apply getParentUpdateSh2 with entry;trivial. }
rewrite Hparent in *.
apply H;trivial.
Qed.

Lemma isPresentNotDefaultIffUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
isPresentNotDefaultIff s -> 
isPresentNotDefaultIff
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold isPresentNotDefaultIff.
intros; 
simpl.
 assert(Hpresent :    StateLib.readPresent table0 idx0
  (memory s) = StateLib.readPresent table0 idx0
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) ).
symmetry.
apply readPresentUpdateSh2 with entry; trivial.
rewrite <- Hpresent.
 assert(Hread :    StateLib.readPhyEntry table0 idx0
  (memory s) = StateLib.readPhyEntry table0 idx0
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex) ).
symmetry.
apply readPhyEntryUpdateSh2 with entry;trivial.
rewrite <- Hread.
apply H.
Qed.
Lemma getVirtualAddressSh1UpdateSh2  s vaInCurrentPartition table idx entry p va: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
getVirtualAddressSh1 p s va  =
getVirtualAddressSh1 p {|
    currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va.
Proof.
intros Hlookup.
unfold getVirtualAddressSh1.
destruct (StateLib.getNbLevel);trivial.
assert(Hind : getIndirection p va l (nbLevel - 1)
{|
currentPartition := currentPartition s;
memory := add table idx  (VA vaInCurrentPartition) (memory s) beqPage
            beqIndex |} = getIndirection  p va l  (nbLevel - 1)
s).
{ apply getIndirectionUpdateSh2 with entry;trivial. }
rewrite Hind.
case_eq (getIndirection  p va l  (nbLevel - 1) s );
[ intros tbl Htbl | intros Htbl]; trivial.
case_eq (Nat.eqb defaultPage tbl);trivial.
intros Htblnotnul.
simpl.
symmetry.
apply readVirEntryUpdateSh2 with entry;trivial.
Qed.
                
Lemma isDerivedUpdateSh2  s vaInCurrentPartition table idx entry parent va: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
isDerived parent va s ->  isDerived parent va  {|
       currentPartition := currentPartition s;
       memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                   beqIndex |}
       . 
Proof.
intros Hlookup.
unfold isDerived.
simpl.
assert(Hsh1 :  StateLib.getFstShadow parent (memory s) =
StateLib.getFstShadow parent
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry.  apply getFstShadowUpdateSh2 with entry;trivial. }
rewrite <- Hsh1 in *.
destruct (StateLib.getFstShadow parent (memory s));trivial.
assert(Hgetvir1 : getVirtualAddressSh1 p s va  =
getVirtualAddressSh1 p {|
    currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va ).
apply getVirtualAddressSh1UpdateSh2 with entry;trivial.
rewrite <- Hgetvir1;trivial.
Qed.
 
Lemma physicalPageNotDerivedUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
physicalPageNotDerived s -> 
physicalPageNotDerived
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold physicalPageNotDerived.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hchildren : forall part, getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |} = getChildren part s).
{ intros.
symmetry.
apply getChildrenUpdateSh2 with entry;trivial. } 
rewrite Hchildren in *.
clear Hchildren.
assert(Hpd : forall partition, StateLib.getPd partition
       (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros.
  apply getPdUpdateSh2 with entry;trivial. }
rewrite Hpd in *. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateSh2 with entry;trivial. }
rewrite Hmap in *. clear Hmap.
assert(~ isDerived parent va s ). 
unfold not;intros. 
contradict H2.
apply isDerivedUpdateSh2 with entry;trivial.
apply H with  parent va pdParent
child pdChild vaInChild;trivial.
Qed.

Lemma multiplexerWithoutParentUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
multiplexerWithoutParent s -> 
multiplexerWithoutParent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold multiplexerWithoutParent.
intros; 
simpl.

assert(Hparent : StateLib.getParent multiplexer
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage
       beqIndex) = StateLib.getParent multiplexer (memory s)).
{  apply getParentUpdateSh2 with entry;trivial. }
rewrite Hparent in *.
apply H;trivial.
Qed.

Lemma isParentUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
isParent s -> 
isParent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold isParent.
intros.
simpl in *. 
assert(Hparent : StateLib.getParent partition
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage
       beqIndex) = StateLib.getParent partition (memory s)).
{  apply getParentUpdateSh2 with entry;trivial. }
rewrite Hparent in *. clear Hparent.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hchildren : forall part, getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |} = getChildren part s).
{ intros.
symmetry.
apply getChildrenUpdateSh2 with entry;trivial. } 
rewrite Hchildren in *.
clear Hchildren.
apply H; trivial.
Qed.

Lemma noDupPartitionTreeUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
noDupPartitionTree s -> 
noDupPartitionTree
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold noDupPartitionTree.
intros.
simpl in *.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
Qed.
 
Lemma wellFormedFstShadowUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
wellFormedFstShadow s -> 
wellFormedFstShadow
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold wellFormedFstShadow.
intros.
simpl in *.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, StateLib.getPd partition
       (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros.
  apply getPdUpdateSh2 with entry;trivial. }
rewrite Hpd in *. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateSh2 with entry;trivial. }
rewrite Hmap in *. clear Hmap.
assert(Hsh1 : forall partition, StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry.  apply getFstShadowUpdateSh2 with entry;trivial. }
rewrite <- Hsh1 in *. clear Hsh1.
assert(Hgetvir1 : getVirtualAddressSh1 sh1 s va  =
getVirtualAddressSh1 sh1 {|
    currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va ).
apply getVirtualAddressSh1UpdateSh2 with entry;trivial.
rewrite <- Hgetvir1;trivial.
apply H with partition pg pd;trivial.
Qed.

Lemma wellFormedFstShadowIfNoneUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
wellFormedFstShadowIfNone s -> 
wellFormedFstShadowIfNone
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold wellFormedFstShadowIfNone.
intros.
simpl in *.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, StateLib.getPd partition
       (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros.
  apply getPdUpdateSh2 with entry;trivial. }
rewrite Hpd in *. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateSh2 with entry;trivial. }
rewrite Hmap in *. clear Hmap.
assert(Hsh1 : forall partition, StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry.  apply getFstShadowUpdateSh2 with entry;trivial. }
rewrite <- Hsh1 in *. clear Hsh1.
assert(Hgetvir1 : getPDFlag sh1 va s  =
getPDFlag sh1 va {|
    currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} ).
symmetry.
apply getPDFlagUpdateSh2 with entry;trivial.
rewrite <- Hgetvir1;trivial.
assert(Hgetvir2 : getVirtualAddressSh1 sh1 s va =
getVirtualAddressSh1 sh1 {|
    currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va).
apply getVirtualAddressSh1UpdateSh2 with entry;trivial.
rewrite <- Hgetvir2.
apply H with partition pd;trivial.
Qed.

Lemma wellFormedFstShadowIfDefaultValuesUpdateSh2 s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
wellFormedFstShadowIfDefaultValues s -> 
wellFormedFstShadowIfDefaultValues
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold wellFormedFstShadowIfDefaultValues.
intros.
simpl in *.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, StateLib.getPd partition
       (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros.
  apply getPdUpdateSh2 with entry;trivial. }
rewrite Hpd in *. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateSh2 with entry;trivial. }
rewrite Hmap in *. clear Hmap.
assert(Hsh1 : forall partition, StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry.  apply getFstShadowUpdateSh2 with entry;trivial. }
rewrite <- Hsh1 in *. clear Hsh1.
assert(Hgetvir1 : getPDFlag sh1 va s  =
getPDFlag sh1 va {|
    currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} ).
symmetry.
apply getPDFlagUpdateSh2 with entry;trivial.
rewrite <- Hgetvir1;trivial.
assert(Hgetvir2 : getVirtualAddressSh1 sh1 s va =
getVirtualAddressSh1 sh1 {|
    currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va).
apply getVirtualAddressSh1UpdateSh2 with entry;trivial.
rewrite <- Hgetvir2.
apply H with partition pd;trivial.
Qed.

Lemma wellFormedSndShadowUpdateSh2 s entry (vaInCurrentPartition vaChild: vaddr)  currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level:
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
negb presentDescPhy = false -> 
lookup ptVaChildsh2 idxvaChild  (memory s) beqPage beqIndex = Some (VA entry) ->
propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level -> 
wellFormedSndShadow s ->
wellFormedSndShadow
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildsh2 idxvaChild  (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}. 
Proof.
intros Hlegit1 Hlegit Hlookup Hprops.
unfold wellFormedSndShadow.
intros.
simpl in *.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, StateLib.getPd partition
       (add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros.
  apply getPdUpdateSh2 with entry;trivial. }
rewrite Hpd in *. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateSh2 with entry;trivial. }
rewrite Hmap in *. clear Hmap.
assert(Hsh1 : forall partition, StateLib.getSndShadow partition (memory s) =
StateLib.getSndShadow partition
    (add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry.  apply getSndShadowUpdateSh2 with entry;trivial. }
rewrite <- Hsh1 in *. clear Hsh1.
assert(Hor : partition = phyDescChild \/ partition <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor];
subst.
+ unfold propagatedPropertiesAddVaddr in *.
  assert (Hpdeq : sh2Childphy = sh2). 
  { apply getSh2NextEntryIsPPEq with phyDescChild s;trivial.
    intuition. }
    assert (Hsh2eq : pdChildphy = pd). 
  { apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
    intuition. }
    subst pd sh2.
  assert(Hor : StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/ 
         StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va level = false).
  { destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va level);intuition. }
  destruct Hor as [Hor | Hor].
  - assert(Hlastidx : (StateLib.getIndexOfAddr vaChild fstLevel) = 
  (StateLib.getIndexOfAddr va fstLevel)).
    { apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level; trivial.
      unfold fstLevel.
      unfold CLevel.
      case_eq ( lt_dec 0 nbLevel );intros.
      simpl.
      lia.
      assert(0<nbLevel) by apply nbLevelNotZero.
      lia.
      destruct level;simpl; lia. }
  rewrite Hlastidx in *. 
  assert(Htrue : getMappedPage pdChildphy s va = SomeDefault).
  {  apply getMappedPageNotPresent with ptVaChildpd phyDescChild;intuition.
    + subst;trivial.
    + assert(Hget : getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
      unfold getTableAddrRoot in *.
      destruct Hget as(Hi & Hget).
      split;trivial.
      intros tableroot Hpp.
      apply Hget in Hpp.
      destruct Hpp as ( nbL & HnbL & stop & Hstop & Hind).
      exists nbL;split;trivial.
      exists stop;split;trivial.
      rewrite <- Hind.
      apply getIndirectionEq;trivial.
      apply getNbLevelLt.
      symmetry;trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
      rewrite <- HnbL in *. 
      assert(Hlevel : Some level = Some nbL) by trivial.
      inversion Hlevel.
      subst;trivial.
    + repeat rewrite andb_true_iff in Hlegit1.
      rewrite negb_true_iff in *. 
      intuition.
      subst;trivial. }
  rewrite Htrue in *. 
  assert(Hfalse : SomeDefault = SomePage pg) by trivial.
  now contradict Hfalse.
  - (* assert(Hconcl : isAccessibleMappedPageInParent phyDescChild va accessiblePage
    {|
    currentPartition := currentPartition s;
    memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s)
              beqPage beqIndex |} = 
  isAccessibleMappedPageInParent  phyDescChild va accessiblePage s). 
  { unfold isAccessibleMappedPageInParent.
    simpl.
    assert(Hsh2 :  getSndShadow phyDescChild
    (add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
       beqIndex) =  getSndShadow phyDescChild (memory s)).
    apply getSndShadowUpdateSh2 with entry;trivial.
    rewrite Hsh2. clear Hsh2.
    assert(Hsh2child :  nextEntryIsPP phyDescChild sh2idx sh2Childphy s) by intuition.
     rewrite nextEntryIsPPgetSndShadow in *. 
 rewrite Hsh2child. *)
 assert(Hnewgoal :  exists vainparent : vaddr,
      getVirtualAddressSh2 sh2Childphy s va = Some vainparent /\
      beqVAddr defaultVAddr vainparent = false).
 apply H with phyDescChild pg pdChildphy ;trivial.
 destruct  Hnewgoal as (vainparent & Hgoal & Hfalse).
 exists vainparent;split;trivial.
 rewrite <- Hgoal.
  unfold getVirtualAddressSh2.  
    assert (Hlevel : Some level = StateLib.getNbLevel) by intuition.
    rewrite <- Hlevel.
    assert(Hind : getIndirection sh2Childphy va level (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} = getIndirection  sh2Childphy va level (nbLevel - 1)
    s).
    { apply getIndirectionUpdateSh2 with entry;trivial. }
    rewrite Hind.
    case_eq (getIndirection  sh2Childphy va level (nbLevel - 1) s );
    [ intros tbl Htbl | intros Htbl]; trivial.
    case_eq (Nat.eqb defaultPage tbl);trivial.
    intros Htblnotnul.
    simpl. 
    assert(Hdiff : tbl <> ptVaChildsh2 \/ 
         (StateLib.getIndexOfAddr va fstLevel) <> 
         StateLib.getIndexOfAddr vaChild fstLevel).
   {
  unfold consistency in *.
  assert(Hnodup : noDupConfigPagesList s) by intuition.
  apply pageTablesOrIndicesAreDifferent with sh2Childphy sh2Childphy level 
      nbLevel  s;trivial.
  apply rootStructNotNull with phyDescChild s sh2idx;intuition.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
  apply rootStructNotNull with phyDescChild s sh2idx;intuition.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
  unfold noDupConfigPagesList in *.  apply noDupConfigPagesListNoDupGetIndirections with phyDescChild sh2idx;trivial.
  intuition.  unfold noDupConfigPagesList in Hnodup. 
  apply Hnodup ;intuition.
  do 2 right;trivial.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
    apply noDupConfigPagesListNoDupGetIndirections with phyDescChild sh2idx;trivial.
  intuition.  unfold noDupConfigPagesList in Hnodup. 
  apply Hnodup ;intuition.
  do 2 right;trivial.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
  rewrite <- Hor.
  rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
  assert(level = CLevel (nbLevel - 1) ). 
  apply getNbLevelEq;trivial.
  left;split;trivial.
  apply beq_nat_false in Htblnotnul.
  unfold not; intros Htmp;subst;now contradict Htblnotnul.
  assert(Hnotnull : (Nat.eqb defaultPage ptVaChildsh2) = false) by intuition.
  apply beq_nat_false in Hnotnull.
  unfold not; intros Htmp;subst;now contradict Hnotnull.
  apply getIndirectionStopLevelGT  with (nbLevel - 1) ;trivial.
  apply getNbLevelLt;intuition.
  apply getNbLevelEq in Hlevel.
  subst.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel);intros Hl Hli .
  simpl.
  lia.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia.
  subst.
  assert(getTableAddrRoot ptVaChildsh2 sh2idx phyDescChild vaChild s /\
   isVA ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel) s)
   as (Htblroot & Hva) 
  by intuition.
  assert(Hnewgoal : getIndirection sh2Childphy vaChild level (nbLevel -1) s 
  = Some ptVaChildsh2). 
  apply getIndirectionGetTableRoot2 with phyDescChild;trivial.
  rewrite Hlevel;trivial.
  intros.
  split;subst;trivial.
  apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
    apply getNbLevelLt;intuition.
  apply getNbLevelEq in Hlevel.
  subst.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel);intros Hl Hli .
  simpl.
  lia.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia.
 }
 move Hlookup at bottom.
 clear Hind .
apply readVirtualUpdateSh2.
destruct Hdiff.
left;trivial.
right. 
assert(Hidx :  StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild ) by intuition.
rewrite <- Hidx.
trivial. 
+ assert(Hnewgoal :  exists vainparent : vaddr,
      getVirtualAddressSh2 sh2 s va = Some vainparent /\
      beqVAddr defaultVAddr vainparent = false).
 apply H with partition pg pd ;trivial.
 destruct  Hnewgoal as (vainparent & Hgoal & Hfalse).
 exists vainparent;split;trivial.
 rewrite <- Hgoal.
 unfold getVirtualAddressSh2. 
    unfold propagatedPropertiesAddVaddr in *. 
    assert(Hlevel : Some level = StateLib.getNbLevel) by intuition.
    rewrite <- Hlevel.
    assert(Hind : getIndirection sh2 va level (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} = getIndirection  sh2 va level (nbLevel - 1)
    s).
    { apply getIndirectionUpdateSh2 with entry;trivial. }
    rewrite Hind.
    case_eq (getIndirection  sh2 va level (nbLevel - 1) s );
    [ intros tbl Htbl | intros Htbl]; trivial.
    case_eq (Nat.eqb defaultPage tbl);trivial.
    intros Htblnotnul.
    simpl.
    apply readVirtualUpdateSh2;trivial.
    left. 
    assert(Hconfig : configTablesAreDifferent s ) by (
    unfold consistency in *; intuition).
    unfold configTablesAreDifferent in *. 
    assert(Hinconfig1 : In tbl (getConfigPages partition s)).
    { assert (Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
      apply pdSh1Sh2ListExistsNotNull with s partition  in Hpde;trivial.
      destruct Hpde as ((pd1 & Hpd1 & Hpdnotnull) 
        & (sh1 & Hsh1 & Hsh1notnull) & (sh22 & Hsh22 & Hsh2notnull) & 
        (sh3 & Hsh3 & Hsh3notnull)).
      unfold getConfigPages.
      unfold getConfigPagesAux.
      rewrite H2, Hsh1, H3, Hsh3.
      simpl.
      right.
      do 2 (rewrite in_app_iff;
      right).
       rewrite in_app_iff.
      left.
      apply getIndirectionInGetIndirections with va level (nbLevel - 1);trivial.
      apply nbLevelNotZero.
      apply beq_nat_false in Htblnotnul.
      unfold not;intros Hfalse1;subst; now contradict Htblnotnul.
      apply getNbLevelLe;intuition.
      unfold consistency in *.
      apply rootStructNotNull with partition s sh2idx;intuition.
      rewrite nextEntryIsPPgetSndShadow in *;trivial.  }
    assert(Hinconfig2 : In ptVaChildsh2 (getConfigPages phyDescChild s)).
    { assert (Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
      (* apply pdSh1Sh2ListExistsNotNull with s phyDescChild  in Hpde;trivial.
      Focus 2.
      assert(Hchild : In phyDescChild (getChildren (currentPartition s) s) )
      by intuition.
      unfold consistency in *. 
      apply childrenPartitionInPartitionList with (currentPartition s);intuition. 
      subst;trivial. *)
      apply isConfigTableSh2WithVA with vaChild;trivial.
      assert(Hchild : In phyDescChild (getChildren (currentPartition s) s) )
      by intuition.
      unfold consistency in *. 
      apply childrenPartitionInPartitionList with (currentPartition s);intuition. 
      subst;trivial.
      intros;subst;split;intuition.
      intuition. }
    unfold not;intros; subst.
    unfold Lib.disjoint in *.
    contradict Hinconfig2.
    apply Hconfig with partition;trivial.  
    assert(Hchild : In phyDescChild (getChildren (currentPartition s) s) )
      by intuition.
      unfold consistency in *. 
      apply childrenPartitionInPartitionList with (currentPartition s);intuition. 
Qed.

Lemma wellFormedShadowsUpdateSh2 s vaInCurrentPartition table idx entry idxroot: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
wellFormedShadows idxroot s -> 
wellFormedShadows idxroot
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold wellFormedShadows.
intros.
simpl in *.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, StateLib.getPd partition
       (add table idx (VA vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros.
  apply getPdUpdateSh2 with entry;trivial. }
rewrite Hpd in *. clear Hpd.
assert(Hpp : nextEntryIsPP partition idxroot structroot s ). 
rewrite nextEntryIsPPUpdateSh2 with entry;trivial.
eassumption.
trivial.
assert(Hind : forall root, getIndirection root va nbL stop
    {|
    currentPartition := currentPartition s;
    memory := add table idx (VA vaInCurrentPartition) (memory s) beqPage
                beqIndex |} = getIndirection  root va nbL stop
    s).
    { intros. apply getIndirectionUpdateSh2 with entry;trivial. }
assert(Hgoal :  exists indirection2 : page,
      getIndirection structroot va nbL stop s = Some indirection2 /\
      (Nat.eqb defaultPage indirection2) = b). 
{ apply H with partition pdroot indirection1;trivial.
  rewrite <- Hind;trivial. }
destruct Hgoal as (indirection2 & Hind1 & Hindnotnul).
exists indirection2;split;trivial.
rewrite <- Hind1.
apply Hind.
Qed.
Lemma getTableAddrRootUpdateSh2 s vaInCurrentPartition table idx entry  idxroot 
ptDescChild descChild currentPart: 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
getTableAddrRoot ptDescChild idxroot currentPart descChild  s-> 
getTableAddrRoot ptDescChild idxroot currentPart descChild
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VA vaInCurrentPartition) (memory s)
              beqPage beqIndex |}.
Proof.
intros Hlookup.
unfold getTableAddrRoot.
intros Hcond.
destruct Hcond as(Hi & Hcond).
split;trivial.
intros. 
assert(Hpp : nextEntryIsPP currentPart idxroot tableroot s ). 
rewrite nextEntryIsPPUpdateSh2 with entry;trivial.
eassumption.
trivial.
apply Hcond in Hpp.
destruct Hpp as (nbL & HnbL & stop & Hstop & Hind). 
exists nbL. 
split;trivial.
exists stop.
split;trivial. 
rewrite <- Hind.
apply getIndirectionUpdateSh2 with entry;trivial.
Qed.
          
Lemma consistencyUpdateSh2 s  entry (vaInCurrentPartition vaChild: vaddr)  currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level:
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
negb presentDescPhy = false -> 
lookup ptVaChildsh2 idxvaChild (memory s) beqPage beqIndex = Some (VA entry) ->
propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level -> 
consistency  {|
currentPartition := currentPartition s;
memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition)
            (memory s) beqPage beqIndex |}.
Proof.
set (s' := {|
  currentPartition := currentPartition s;
  memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s)
              beqPage beqIndex |} ) in *.
unfold propagatedPropertiesAddVaddr; intros. 
unfold consistency in *.
intuition.
(** partitionDescriptorEntry **)
- apply partitionDescriptorEntryUpdateSh2 with entry;trivial.
(** dataStructurePdSh1Sh2asRoot **)
- apply dataStructurePdSh1Sh2asRootUpdateSh2 with entry;trivial.
(** dataStructurePdSh1Sh2asRoot **)
- apply dataStructurePdSh1Sh2asRootUpdateSh2 with entry;trivial.
(** dataStructurePdSh1Sh2asRoot **)
- apply dataStructurePdSh1Sh2asRootUpdateSh2 with entry;trivial.
(** currentPartitionInPartitionsList **)
- apply currentPartitionInPartitionsListUpdateSh2 with entry;trivial.
(** noDupMappedPagesList **)
- apply noDupMappedPagesListUpdateSh2 with entry;trivial.
(** noDupConfigPagesList **)
- apply noDupConfigPagesListUpdateSh2 with entry ; trivial.
(** parentInPartitionList **)
- apply parentInPartitionListUpdateSh2 with entry ; trivial.
(** accessibleVAIsNotPartitionDescriptor **)
- apply accessibleVAIsNotPartitionDescriptorUpdateSh2 with entry ; trivial.
(** accessibleChildPageIsAccessibleIntoParent **)
- apply accessibleChildPageIsAccessibleIntoParentUpdateSh2 with
    entry vaChild
    currentPart currentShadow descChild idxDescChild ptDescChild
    ptVaInCurPart idxvaInCurPart vainve isnotderiv currentPD
    ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
    phyDescChild pdChildphy ptVaChildpd presentvaChild phyVaChild
    sh2Childphy level;trivial.
  unfold propagatedPropertiesAddVaddr ;intuition.
  unfold consistency in *; intuition.
(** noCycleInPartitionTree **)
- apply noCycleInPartitionTreeUpdateSh2 with entry;trivial.
(** configTablesAreDifferent **)
- apply configTablesAreDifferentUpdateSh2 with entry;trivial.
(** isChild **)
- apply isChildUpdateSh2 with entry;trivial.
(** isPresentNotDefaultIff *)
- apply isPresentNotDefaultIffUpdateSh2 with entry;trivial.
(** physicalPageNotDerived **)
- apply physicalPageNotDerivedUpdateSh2 with entry;trivial.
(** multiplexerWithoutParent *)
- apply multiplexerWithoutParentUpdateSh2 with entry;trivial.
(** isParent **)
- apply isParentUpdateSh2 with entry;trivial.
(** noDupPartitionTree **)
- apply noDupPartitionTreeUpdateSh2 with entry;trivial.
(** wellFormedFstShadow **)
- apply wellFormedFstShadowUpdateSh2 with entry;trivial.
(** wellFormedSndShadow **)
- apply wellFormedSndShadowUpdateSh2 with
    entry vaChild
    currentPart currentShadow descChild idxDescChild ptDescChild
    ptVaInCurPart idxvaInCurPart vainve isnotderiv currentPD
    ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
    phyDescChild pdChildphy ptVaChildpd presentvaChild phyVaChild
    sh2Childphy level;trivial.
  unfold propagatedPropertiesAddVaddr ;intuition.
  unfold consistency in *; intuition.
(** wellFormedShadows *)
- apply wellFormedShadowsUpdateSh2 with entry;trivial.
(** wellFormedShadows *)
- apply wellFormedShadowsUpdateSh2 with entry;trivial.
- apply wellFormedFstShadowIfNoneUpdateSh2 with entry;trivial.
- apply wellFormedFstShadowIfDefaultValuesUpdateSh2 with entry;trivial.
Qed.  
  
Lemma writeVirtualInv (vaInCurrentPartition vaChild: vaddr)  currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level: 
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
negb presentDescPhy = false -> 
{{ fun s : state => propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level }} 
  MAL.writeVirtual ptVaChildsh2 idxvaChild vaInCurrentPartition 
  {{ fun _ s => propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level /\ 
StateLib.readVirtual ptVaChildsh2 idxvaChild s.(memory) = 
                 Some vaInCurrentPartition }}.
Proof.
intros Hlegit Hlegit1.
eapply weaken.
eapply WP.writeVirtual.
simpl;intros.
split. 
(* set (s' := {|
  currentPartition := currentPartition s;
  memory := add ptVaChildsh2 idxvaChild (VA vaInCurrentPartition) (memory s)
              beqPage beqIndex |} ) in *. *)
unfold propagatedPropertiesAddVaddr in *.
assert(Hlookup :exists entry, 
 lookup ptVaChildsh2 idxvaChild (memory s) beqPage beqIndex = Some (VA entry)).
{ assert(Hva : isVA ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel) s) by intuition.

  unfold isVA in *.
  assert(Hidx :  StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild) by intuition.
 clear H.
 subst. 
 destruct(lookup ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel)
          (memory s) beqPage beqIndex);intros; try now contradict Hva.
 destruct v; try now contradict Hva.
 do 2 f_equal.
 exists v;trivial. }
 destruct Hlookup as (entry & Hlookup).
intuition try assumption.
(** partitionsIsolation **)
+ apply partitionsIsolationUpdateSh2 with entry;trivial.
(** kernelDataIsolation **)
+ apply kernelDataIsolationUpdateSh2 with entry;trivial.
(** verticalSharing **)
+ apply verticalSharingUpdateSh2 with entry;trivial. 
(** consistency **)
+ apply consistencyUpdateSh2 with
    entry vaChild
    currentPart currentShadow descChild idxDescChild ptDescChild
    ptVaInCurPart idxvaInCurPart vainve isnotderiv currentPD
    ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
    phyDescChild pdChildphy ptVaChildpd presentvaChild phyVaChild
    sh2Childphy level;trivial.
  unfold propagatedPropertiesAddVaddr ;intuition.
(** Propagated properties **)
+ rewrite <- nextEntryIsPPUpdateSh2;trivial.
  exact Hlookup.
+ apply isVEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply entryPDFlagUpdateSh2 with entry;trivial.
+ apply isVEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply isEntryVAUpdateSh2 with entry;trivial.
+ rewrite <- nextEntryIsPPUpdateSh2;trivial.
  exact Hlookup.
+ apply isPEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply entryUserFlagUpdateSh2 with entry;trivial.
+ apply entryPresentFlagUpdateSh2 with entry;trivial.
+ apply isPEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply entryPresentFlagUpdateSh2 with entry;trivial.
+ apply isEntryPageUpdateSh2  with entry;trivial.
+ assert(Hchildren : forall part, getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add ptVaChildsh2 idxvaChild(VA vaInCurrentPartition) (memory s) beqPage
                 beqIndex |} = getChildren part s).
  { intros; symmetry; apply getChildrenUpdateSh2 with entry;trivial. } 
  rewrite Hchildren in *;trivial.
+ rewrite <- nextEntryIsPPUpdateSh2;trivial.
  exact Hlookup.
+ apply isPEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply entryPresentFlagUpdateSh2 with entry;trivial.
+ apply isEntryPageUpdateSh2  with entry;trivial.
+ rewrite <- nextEntryIsPPUpdateSh2;trivial.
  exact Hlookup.
+ apply isVAUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
(** new property **)
+ unfold StateLib.readVirtual.
  cbn.
  assert (Htrue : beqPairs (ptVaChildsh2, idxvaChild) (ptVaChildsh2, idxvaChild) beqPage
      beqIndex = true). 
  apply beqPairsTrue;split;trivial.
  rewrite Htrue.
  trivial.
Qed.
 
Lemma accessibleChildPageIsAccessibleIntoParentRemoveAddr  s descChild vaChild currentPart level
      idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
      phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
      ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2  vainparent
      currentShadow ptVaInCurPart defautvaddr entry:
      lookup ptVaChildsh2 idxvaChild (memory s) beqPage beqIndex = Some (VA entry) ->
propagatedPropertiesRemoveVaddr s descChild vaChild currentPart level
      idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
      phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
      ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2 vainparent vainparent
      currentShadow ptVaInCurPart
      (StateLib.getIndexOfAddr vainparent fstLevel) false false -> 
accessibleChildPageIsAccessibleIntoParent
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildsh2 idxvaChild (VA defautvaddr) (memory s) beqPage
              beqIndex |}.
Proof.
set (s' := {|
  currentPartition := currentPartition s;
  memory := add ptVaChildsh2 idxvaChild (VA defautvaddr) (memory s)
              beqPage beqIndex |} ).
intros Hlookup.
intros.
unfold propagatedPropertiesRemoveVaddr in *.
unfold consistency in *.
intuition.
subst.
assert (Hcons: accessibleChildPageIsAccessibleIntoParent s) by trivial.
unfold accessibleChildPageIsAccessibleIntoParent in *.
simpl.
intros partition va pd accessiblePage Hpart Hpd Haccess.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer s').
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Haccessmap : forall part, getAccessibleMappedPage part s' va =
getAccessibleMappedPage part s va).
{ intros. apply getAccessibleMappedPageUpdateSh2 with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
assert(Hpdeq :  StateLib.getPd partition (memory s) =
StateLib.getPd partition
    (add ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel)  (VA defautvaddr) (memory s) beqPage beqIndex)).
{ symmetry.  apply getPdUpdateSh2 with entry;trivial. }
rewrite <- Hpdeq in *.
clear Hpdeq.
assert(Hor : partition = phyDescChild \/ partition <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor];
subst.
+ assert (Hpdeq : pdChildphy = pd). 
  { apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
  subst pd.
  assert(Hor: StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/ 
              StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va level = false).
  { destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va level);intuition. }
  destruct Hor as [Hor | Hor].
  -  assert(Htrue: getAccessibleMappedPage pdChildphy s vaChild = NonePage).
 { apply getAccessibleMappedPageNotPresent with ptVaChildpd phyDescChild;trivial. 
    intros;split;subst;trivial. }
   assert(Hmapeq: getAccessibleMappedPage pdChildphy s vaChild = 
   getAccessibleMappedPage pdChildphy s va).
   { apply getAccessibleMappedPageEq with level;trivial.
     symmetry;trivial. }
   rewrite  Haccess in Hmapeq.
   rewrite Htrue in Hmapeq.
   now contradict Hmapeq.
  - assert(Hconcl : isAccessibleMappedPageInParent phyDescChild va accessiblePage
    s' = 
  isAccessibleMappedPageInParent  phyDescChild va accessiblePage s). 
  { unfold isAccessibleMappedPageInParent.
    simpl.
    assert(Hsh2 :  StateLib.getSndShadow phyDescChild
    (add ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel) (VA defautvaddr) (memory s) beqPage
       beqIndex) = StateLib.getSndShadow phyDescChild (memory s)).
    apply getSndShadowUpdateSh2 with entry;trivial.
    rewrite Hsh2. clear Hsh2.
    assert(Hsh2child :  nextEntryIsPP phyDescChild sh2idx sh2Childphy s) by intuition.
     rewrite nextEntryIsPPgetSndShadow in *. 
 rewrite Hsh2child.
 assert(Hsh2virt : getVirtualAddressSh2 sh2Childphy
    s' va = getVirtualAddressSh2 sh2Childphy s va ).
  { unfold getVirtualAddressSh2.  
    assert (Hlevel : Some level = StateLib.getNbLevel) by intuition.
    rewrite <- Hlevel.
    assert(Hind : getIndirection sh2Childphy va level (nbLevel - 1)
    s' = getIndirection  sh2Childphy va level (nbLevel - 1)
    s).
    { apply getIndirectionUpdateSh2 with entry;trivial. }
    rewrite Hind.
    case_eq (getIndirection  sh2Childphy va level (nbLevel - 1) s );
    [ intros tbl Htbl | intros Htbl]; trivial.
    case_eq (Nat.eqb defaultPage tbl);trivial.
    intros Htblnotnul.
    simpl. 
    assert(Hdiff : tbl <> ptVaChildsh2 \/ 
         (StateLib.getIndexOfAddr va fstLevel) <> 
         StateLib.getIndexOfAddr vaChild fstLevel).
   {
  unfold consistency in *.
  assert(Hnodup : noDupConfigPagesList s) by intuition.
 { apply pageTablesOrIndicesAreDifferent with sh2Childphy sh2Childphy level 
      nbLevel  s;trivial.
  apply rootStructNotNull with phyDescChild s sh2idx;intuition.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
  apply rootStructNotNull with phyDescChild s sh2idx;intuition.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
  apply noDupConfigPagesListNoDupGetIndirections with phyDescChild sh2idx;trivial.
  intuition.  (* unfold noDupConfigPagesList in Hnodup. 
  apply Hnodup ;intuition. *)
  do 2 right;trivial.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
    apply noDupConfigPagesListNoDupGetIndirections with phyDescChild sh2idx;trivial.
  intuition. (*  unfold noDupConfigPagesList in Hnodup. 
  apply Hnodup ;intuition. *)
  do 2 right;trivial.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
  rewrite <- Hor.
  rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
  assert(level = CLevel (nbLevel - 1) ). 
  apply getNbLevelEq;trivial.
  left;split;trivial.
  apply beq_nat_false in Htblnotnul.
  unfold not; intros Htmp;subst;now contradict Htblnotnul.
  assert(Hnotnull : (Nat.eqb defaultPage ptVaChildsh2) = false) by intuition.
  apply beq_nat_false in Hnotnull.
  unfold not; intros Htmp;subst;now contradict Hnotnull.
  apply getIndirectionStopLevelGT  with (nbLevel - 1) ;trivial.
  apply getNbLevelLt;intuition.
  apply getNbLevelEq in Hlevel.
  subst.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel);intros Hl Hli .
  simpl.
  lia.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia.
  subst.
  assert(getTableAddrRoot ptVaChildsh2 sh2idx phyDescChild vaChild s /\
   isVA ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel) s)
   as (Htblroot & Hva) 
  by intuition.
  assert(Hnewgoal : getIndirection sh2Childphy vaChild level (nbLevel -1) s 
  = Some ptVaChildsh2). 
  apply getIndirectionGetTableRoot2 with phyDescChild;trivial.
  rewrite Hlevel;trivial.
  intros.
  split;subst;trivial.
  apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
    apply getNbLevelLt;intuition.
  apply getNbLevelEq in Hlevel.
  subst.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel);intros Hl Hli .
  simpl.
  lia.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia.
 } }
 move Hlookup at bottom.
 clear Hind .
apply readVirtualUpdateSh2.
destruct Hdiff.
left;trivial.
right. 
trivial.
 } 
  rewrite Hsh2virt.
  case_eq(getVirtualAddressSh2 sh2Childphy s va );[ intros vaInParent Hvainparent | intros Hvainparent];
  trivial. 
  assert(Hparent : StateLib.getParent phyDescChild
      (add ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel) (VA defautvaddr) (memory s) beqPage
         beqIndex) = StateLib.getParent phyDescChild (memory s)).
  apply getParentUpdateSh2 with entry;trivial.
  rewrite Hparent.
  destruct (StateLib.getParent phyDescChild (memory s) );trivial.
  assert(Hpdeq :  StateLib.getPd p (memory s) =
  StateLib.getPd p
      (add ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel)  (VA defautvaddr) (memory s) beqPage beqIndex)).
  { symmetry.  apply getPdUpdateSh2 with entry;trivial. }
  rewrite <- Hpdeq in *.
  clear Hpdeq.
  destruct (StateLib.getPd p (memory s));trivial.
  assert(Haccessmap : forall part, getAccessibleMappedPage part s' vaInParent =
  getAccessibleMappedPage part s vaInParent).
  { intros. apply getAccessibleMappedPageUpdateSh2 with entry;trivial. }
  rewrite Haccessmap in *. clear Haccessmap.
  trivial. }
  rewrite Hconcl.
  apply Hcons with pdChildphy;trivial.
+ assert  (Htrue : isAccessibleMappedPageInParent partition va accessiblePage
  s' = 
      isAccessibleMappedPageInParent partition va accessiblePage s). 
 { unfold   isAccessibleMappedPageInParent.
   simpl. 
  assert(Hsh2 : StateLib.getSndShadow partition
    (add ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel) (VA defautvaddr) (memory s) beqPage
       beqIndex) = StateLib.getSndShadow partition (memory s)).
  { apply getSndShadowUpdateSh2 with entry;trivial. }
  rewrite Hsh2.
  case_eq (StateLib.getSndShadow partition (memory s));[ intros sh2 Hsh2part | intros Hnone];trivial. 
  assert(Hgetva : getVirtualAddressSh2 sh2
    s' va =
     getVirtualAddressSh2 sh2 s va). 
  { unfold getVirtualAddressSh2. 
    unfold propagatedPropertiesAddVaddr in *. 
    assert(Hlevel : Some level = StateLib.getNbLevel) by intuition.
    rewrite <- Hlevel.
    assert(Hind : getIndirection sh2 va level (nbLevel - 1)
    s' = getIndirection  sh2 va level (nbLevel - 1)
    s).
    { apply getIndirectionUpdateSh2 with entry;trivial. }
    rewrite Hind.
    case_eq (getIndirection  sh2 va level (nbLevel - 1) s );
    [ intros tbl Htbl | intros Htbl]; trivial.
    case_eq (Nat.eqb defaultPage tbl);trivial.
    intros Htblnotnul.
    simpl.
    apply readVirtualUpdateSh2;trivial.
    left. 
    assert(Hconfig : configTablesAreDifferent s ) by (
    unfold consistency in *; intuition).
    unfold configTablesAreDifferent in *. 
    assert(Hinconfig1 : In tbl (getConfigPages partition s)).
    { assert (Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
      apply pdSh1Sh2ListExistsNotNull with s partition  in Hpde;trivial.
      destruct Hpde as ((pd1 & Hpd1 & Hpdnotnull) 
        & (sh1 & Hsh1 & Hsh1notnull) & (sh22 & Hsh22 & Hsh2notnull) & 
        (sh3 & Hsh3 & Hsh3notnull)).
      unfold getConfigPages.
      unfold getConfigPagesAux.
      assert(Hx: StateLib.getPd phyDescChild (memory s) = Some pdChildphy). 
      apply nextEntryIsPPgetPd;trivial. 
      rewrite Hpd, Hsh1, Hsh2part, Hsh3.
      simpl.
      right.
      do 2 (rewrite in_app_iff;
      right).
       rewrite in_app_iff.
      left.
      apply getIndirectionInGetIndirections with va level (nbLevel - 1);trivial.
      apply nbLevelNotZero.
      apply beq_nat_false in Htblnotnul.
      unfold not;intros Hfalse;subst; now contradict Htblnotnul.
      apply getNbLevelLe;intuition.
      unfold consistency in *.
      apply rootStructNotNull with partition s sh2idx;intuition.
      rewrite nextEntryIsPPgetSndShadow in *;trivial.  }
    assert(Hinconfig2 : In ptVaChildsh2 (getConfigPages phyDescChild s)).
    { assert (Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
      (* apply pdSh1Sh2ListExistsNotNull with s phyDescChild  in Hpde;trivial.
      Focus 2.
      assert(Hchild : In phyDescChild (getChildren (currentPartition s) s) )
      by intuition.
      unfold consistency in *. 
      apply childrenPartitionInPartitionList with (currentPartition s);intuition. 
      subst;trivial. *)
      apply isConfigTableSh2WithVA with vaChild;trivial.
      assert(Hchild : In phyDescChild (getChildren (currentPartition s) s) )
      by intuition.
      unfold consistency in *. 
      apply childrenPartitionInPartitionList with (currentPartition s);intuition. 
      subst;trivial.
      intros;subst;split;intuition.
       }
    unfold not;intros; subst.
    unfold Lib.disjoint in *.
    contradict Hinconfig2.
    apply Hconfig with partition;trivial.  
    assert(Hchild : In phyDescChild (getChildren (currentPartition s) s) )
      by intuition.
      unfold consistency in *. 
      apply childrenPartitionInPartitionList with (currentPartition s);intuition. 
  }           
  rewrite Hgetva.
    
  case_eq (getVirtualAddressSh2 sh2 s va);[ intros vainparentx Hvainparent | intros Hnone];trivial. 
  assert(Hparent : StateLib.getParent partition
    (add ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel) (VA defautvaddr) (memory s) beqPage
       beqIndex) = StateLib.getParent partition (memory s)).
  apply getParentUpdateSh2 with entry;trivial.
  rewrite Hparent.
  destruct (StateLib.getParent partition (memory s) );trivial.
  assert(Hpdeq :  StateLib.getPd p (memory s) =
  StateLib.getPd p
      (add ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel)  (VA defautvaddr) (memory s) beqPage beqIndex)).
  { symmetry.  apply getPdUpdateSh2 with entry;trivial. }
  rewrite <- Hpdeq in *.
  clear Hpdeq.
  destruct (StateLib.getPd p (memory s));trivial.
  assert(Haccessmap : forall part, getAccessibleMappedPage part s' vainparentx =
  getAccessibleMappedPage part s vainparentx).
  { intros. apply getAccessibleMappedPageUpdateSh2 with entry;trivial. }
  rewrite Haccessmap in *. clear Haccessmap.
  trivial. }
  rewrite Htrue.
  
  apply Hcons with pd;trivial.   
Qed.

Lemma wellFormedSndShadowRemoveMMUPage  s descChild vaChild currentPart level
      idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
      phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
      ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2  vainparent
      currentShadow ptVaInCurPart defautvaddr entry:
      lookup ptVaChildsh2 idxvaChild (memory s) beqPage beqIndex = Some (VA entry) ->
propagatedPropertiesRemoveVaddr s descChild vaChild currentPart level
      idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
      phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
      ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2 vainparent vainparent
      currentShadow ptVaInCurPart
      (StateLib.getIndexOfAddr vainparent fstLevel) false false -> 
 wellFormedSndShadow s -> 
 wellFormedSndShadow {|
  currentPartition := currentPartition s;
  memory := add ptVaChildsh2 idxvaChild (VA defautvaddr) (memory s) beqPage
              beqIndex |}.
Proof.
set (s' := {|
  currentPartition := currentPartition s;
  memory := add ptVaChildsh2 idxvaChild (VA defautvaddr) (memory s)
              beqPage beqIndex |} ).
intros Hlookup Hcons .
intros.
simpl in *.
unfold propagatedPropertiesRemoveVaddr in *.
unfold consistency in *.
intuition.

unfold wellFormedSndShadow in *.
intros partition Hpartition Hnotmulti va pg pd sh2 Hpdcons Hsh2 Hmapped. 


assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer s').
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, StateLib.getPd partition
       (add ptVaChildsh2 idxvaChild (VA defautvaddr) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros.
  apply getPdUpdateSh2 with entry;trivial. }
rewrite Hpd in *. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 s' va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateSh2 with entry;trivial. }
rewrite Hmap in *. clear Hmap.
assert(Hsh1 : forall partition, StateLib.getSndShadow partition (memory s) =
StateLib.getSndShadow partition
    (add ptVaChildsh2 idxvaChild (VA defautvaddr) (memory s) beqPage beqIndex)).
{ symmetry.  apply getSndShadowUpdateSh2 with entry;trivial. }
rewrite <- Hsh1 in *. clear Hsh1.
assert(Hor : partition = phyDescChild \/ partition <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].

+  subst.
  assert (Hpdeq : sh2Childphy = sh2). 
  { apply getSh2NextEntryIsPPEq with phyDescChild s;subst;trivial. }
    assert (Hsh2eq : pdChildphy = pd). 
  { apply getPdNextEntryIsPPEq with phyDescChild s;subst;trivial. }
    subst pd sh2.
  assert(Hor: StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/ 
              StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va level = false).
  { destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va level);intuition. }
  destruct Hor as [Hor | Hor].
  - (* assert(Hlastidx : (StateLib.getIndexOfAddr vaChild fstLevel) = 
  (StateLib.getIndexOfAddr va fstLevel)).
    { apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level; trivial.
      unfold fstLevel.
      unfold CLevel.
      case_eq ( lt_dec 0 nbLevel );intros.
      simpl.
      lia.
      assert(0<nbLevel) by apply nbLevelNotZero.
      lia.
      destruct level;simpl; lia. }
  rewrite Hlastidx in *.  *)
  assert(Htrue : getMappedPage pdChildphy s vaChild = SomeDefault).
  {  apply getMappedPageNotPresent with ptVaChildpd phyDescChild;intuition.
      subst;trivial. }
  assert(Hmapeq: getMappedPage pdChildphy s vaChild = getMappedPage pdChildphy s va). 
  { apply getMappedPageEq with level;trivial.
    symmetry;trivial. }
    rewrite Htrue in *. 
   rewrite Hmapped in Hmapeq.
   now contradict Hmapeq.
  - assert(Hnewgoal :  exists vainparent : vaddr,
      getVirtualAddressSh2 sh2Childphy s va = Some vainparent /\
      beqVAddr defaultVAddr vainparent = false).
 apply H with phyDescChild pg pdChildphy ;trivial.
 destruct  Hnewgoal as (vainparentx & Hgoal & Hfalse).
 exists vainparentx;split;trivial.
 rewrite <- Hgoal.
  unfold getVirtualAddressSh2.  
    assert (Hlevel : Some level = StateLib.getNbLevel) by intuition.
    rewrite <- Hlevel.
    assert(Hind : getIndirection sh2Childphy va level (nbLevel - 1)
   s' = getIndirection  sh2Childphy va level (nbLevel - 1)
    s).
    { apply getIndirectionUpdateSh2 with entry;trivial. }
    rewrite Hind.
    case_eq (getIndirection  sh2Childphy va level (nbLevel - 1) s );
    [ intros tbl Htbl | intros Htbl]; trivial.
    case_eq (Nat.eqb defaultPage tbl);trivial.
    intros Htblnotnul.
    simpl. 
    assert(Hdiff : tbl <> ptVaChildsh2 \/ 
         (StateLib.getIndexOfAddr va fstLevel) <> 
         StateLib.getIndexOfAddr vaChild fstLevel).
   {
  unfold consistency in *.
  assert(Hnodup : noDupConfigPagesList s) by intuition.
  apply pageTablesOrIndicesAreDifferent with sh2Childphy sh2Childphy level 
      nbLevel  s;trivial.
  apply rootStructNotNull with phyDescChild s sh2idx;intuition.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
  apply rootStructNotNull with phyDescChild s sh2idx;intuition.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
  unfold noDupConfigPagesList in *.  apply noDupConfigPagesListNoDupGetIndirections with phyDescChild sh2idx;trivial.
  intuition. 
  do 2 right;trivial.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
    apply noDupConfigPagesListNoDupGetIndirections with phyDescChild sh2idx;trivial.
  intuition.  
  do 2 right;trivial.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.
  rewrite <- Hor.
  rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
  assert(level = CLevel (nbLevel - 1) ). 
  apply getNbLevelEq;trivial.
  left;split;trivial.
  apply beq_nat_false in Htblnotnul.
  unfold not; intros Htmp;subst;now contradict Htblnotnul.
  assert(Hnotnull : (Nat.eqb defaultPage ptVaChildsh2) = false) by intuition.
  apply beq_nat_false in Hnotnull.
  unfold not; intros Htmp;subst;now contradict Hnotnull.
  apply getIndirectionStopLevelGT  with (nbLevel - 1) ;trivial.
  apply getNbLevelLt;intuition.
  apply getNbLevelEq in Hlevel.
  subst.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel);intros Hl Hli .
  simpl.
  lia.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia.
  subst.
  assert(getTableAddrRoot ptVaChildsh2 sh2idx phyDescChild vaChild s /\
   isVA ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel) s)
   as (Htblroot & Hva) 
  by intuition.
  assert(Hnewgoal : getIndirection sh2Childphy vaChild level (nbLevel -1) s 
  = Some ptVaChildsh2). 
  apply getIndirectionGetTableRoot2 with phyDescChild;trivial.
  rewrite Hlevel;trivial.
  intros.
  split;subst;trivial.
  apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
    apply getNbLevelLt;intuition.
  apply getNbLevelEq in Hlevel.
  subst.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel);intros Hl Hli .
  simpl.
  lia.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia.
 }
 move Hlookup at bottom.
 clear Hind .
apply readVirtualUpdateSh2.
destruct Hdiff.
left;trivial.
right.
trivial.
+ assert(Hnewgoal :  exists vainparent : vaddr,
      getVirtualAddressSh2 sh2 s va = Some vainparent /\
      beqVAddr defaultVAddr vainparent = false).
 apply H with partition pg pd ;trivial.
 destruct  Hnewgoal as (vainparentx & Hgoal & Hfalse).
 exists vainparentx;split;trivial.
 rewrite <- Hgoal.
 unfold getVirtualAddressSh2. 
    unfold propagatedPropertiesAddVaddr in *. 
    assert(Hlevel : Some level = StateLib.getNbLevel) by intuition.
    rewrite <- Hlevel.
    assert(Hind : getIndirection sh2 va level (nbLevel - 1)
   s' = getIndirection  sh2 va level (nbLevel - 1)
    s).
    { apply getIndirectionUpdateSh2 with entry;trivial. }
    rewrite Hind.
    case_eq (getIndirection  sh2 va level (nbLevel - 1) s );
    [ intros tbl Htbl | intros Htbl]; trivial.
    case_eq (Nat.eqb defaultPage tbl);trivial.
    intros Htblnotnul.
    simpl.
    apply readVirtualUpdateSh2;trivial.
    left. 
    assert(Hconfig : configTablesAreDifferent s ) by (
    unfold consistency in *; intuition).
    unfold configTablesAreDifferent in *. 
    assert(Hinconfig1 : In tbl (getConfigPages partition s)).
    { assert (Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
      apply pdSh1Sh2ListExistsNotNull with s partition  in Hpde;trivial.
      destruct Hpde as ((pd1 & Hpd1 & Hpdnotnull) 
        & (sh1 & Hsh1 & Hsh1notnull) & (sh22 & Hsh22 & Hsh2notnull) & 
        (sh3 & Hsh3 & Hsh3notnull)).
      unfold getConfigPages.
      unfold getConfigPagesAux.
      rewrite Hpdcons, Hsh1, Hsh2, Hsh3.
      simpl.
      right.
      do 2 (rewrite in_app_iff;
      right).
       rewrite in_app_iff.
      left.
      apply getIndirectionInGetIndirections with va level (nbLevel - 1);trivial.
      apply nbLevelNotZero.
      apply beq_nat_false in Htblnotnul.
      unfold not;intros Hfalse1;subst; now contradict Htblnotnul.
      apply getNbLevelLe;intuition.
      unfold consistency in *.
      apply rootStructNotNull with partition s sh2idx;intuition.
      rewrite nextEntryIsPPgetSndShadow in *;trivial.  }
    assert(Hinconfig2 : In ptVaChildsh2 (getConfigPages phyDescChild s)).
    { assert (Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
      (* apply pdSh1Sh2ListExistsNotNull with s phyDescChild  in Hpde;trivial.
      Focus 2.
      assert(Hchild : In phyDescChild (getChildren (currentPartition s) s) )
      by intuition.
      unfold consistency in *. 
      apply childrenPartitionInPartitionList with (currentPartition s);intuition. 
      subst;trivial. *)
      apply isConfigTableSh2WithVA with vaChild;trivial.
      assert(Hchild : In phyDescChild (getChildren (currentPartition s) s) )
      by intuition.
      unfold consistency in *. 
      apply childrenPartitionInPartitionList with (currentPartition s);intuition. 
      subst;trivial.
      intros;subst;split;intuition.
 }
    unfold not;intros; subst.
    unfold Lib.disjoint in *.
    contradict Hinconfig2.
    apply Hconfig with partition;trivial.  
    assert(Hchild : In phyDescChild (getChildren (currentPartition s) s) )
      by intuition.
      unfold consistency in *. 
      apply childrenPartitionInPartitionList with (currentPartition s);intuition. 
Qed.

              
Lemma consistencyRemoveVaddr s descChild vaChild currentPart level
      idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
      phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
      ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2  vainparent
      currentShadow ptVaInCurPart defautvaddr entry:
      lookup ptVaChildsh2 idxvaChild (memory s) beqPage beqIndex = Some (VA entry) ->
propagatedPropertiesRemoveVaddr s descChild vaChild currentPart level
      idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
      phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
      ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2 vainparent vainparent
      currentShadow ptVaInCurPart
      (StateLib.getIndexOfAddr vainparent fstLevel) false false -> 
consistency
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildsh2 idxvaChild (VA defautvaddr) (memory s) beqPage
              beqIndex |}.
Proof.
set (s' := {|
  currentPartition := currentPartition s;
  memory := add ptVaChildsh2 idxvaChild (VA defautvaddr) (memory s)
              beqPage beqIndex |} ) in *.
unfold propagatedPropertiesRemoveVaddr; intros. 
unfold consistency in *.
intuition.
(** partitionDescriptorEntry **)
- apply partitionDescriptorEntryUpdateSh2 with entry;trivial.
(** dataStructurePdSh1Sh2asRoot **)
- apply dataStructurePdSh1Sh2asRootUpdateSh2 with entry;trivial.
(** dataStructurePdSh1Sh2asRoot **)
- apply dataStructurePdSh1Sh2asRootUpdateSh2 with entry;trivial.
(** dataStructurePdSh1Sh2asRoot **)
- apply dataStructurePdSh1Sh2asRootUpdateSh2 with entry;trivial.
(** currentPartitionInPartitionsList **)
- apply currentPartitionInPartitionsListUpdateSh2 with entry;trivial.
(** noDupMappedPagesList **)
- apply noDupMappedPagesListUpdateSh2 with entry;trivial.
(** noDupConfigPagesList **)
- apply noDupConfigPagesListUpdateSh2 with entry ; trivial.
(** parentInPartitionList **)
- apply parentInPartitionListUpdateSh2 with entry ; trivial.
(** accessibleVAIsNotPartitionDescriptor **)
- apply accessibleVAIsNotPartitionDescriptorUpdateSh2 with entry ; trivial.
(** accessibleChildPageIsAccessibleIntoParent **)
- apply accessibleChildPageIsAccessibleIntoParentRemoveAddr with
    descChild vaChild currentPart level
    idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
    phyDescChild pdChildphy  ptVaChildpd shadow1Child
    ptVaChildFromSh1 vainve sh2Childphy  vainparent
    currentShadow ptVaInCurPart  entry;trivial.
    unfold propagatedPropertiesRemoveVaddr in *; unfold consistency in *;
    intuition.
(** noCycleInPartitionTree **)
- apply noCycleInPartitionTreeUpdateSh2 with entry;trivial.
(** configTablesAreDifferent **)
- apply configTablesAreDifferentUpdateSh2 with entry;trivial.
(** isChild **)
- apply isChildUpdateSh2 with entry;trivial.
(** isPresentNotDefaultIff *)
- apply isPresentNotDefaultIffUpdateSh2 with entry;trivial.
(** physicalPageNotDerived **)
- apply physicalPageNotDerivedUpdateSh2 with entry;trivial.
(** multiplexerWithoutParent *)
- apply multiplexerWithoutParentUpdateSh2 with entry;trivial.
(** isParent **)
- apply isParentUpdateSh2 with entry;trivial.
(** noDupPartitionTree **)
- apply noDupPartitionTreeUpdateSh2 with entry;trivial.
(** wellFormedFstShadow **)
- apply wellFormedFstShadowUpdateSh2 with entry;trivial.
(** wellFormedSndShadow **)
- apply wellFormedSndShadowRemoveMMUPage with
    descChild vaChild currentPart level
    idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
    phyDescChild pdChildphy  ptVaChildpd shadow1Child
    ptVaChildFromSh1 vainve sh2Childphy  vainparent
    currentShadow ptVaInCurPart  entry;trivial.
    unfold propagatedPropertiesRemoveVaddr in *; unfold consistency in *;
    intuition.
(** wellFormedShadows *)
- apply wellFormedShadowsUpdateSh2 with entry;trivial.
(** wellFormedShadows *)
- apply wellFormedShadowsUpdateSh2 with entry;trivial.
- apply wellFormedFstShadowIfNoneUpdateSh2 with entry;trivial.
- apply wellFormedFstShadowIfDefaultValuesUpdateSh2 with entry;trivial.
Qed.

Lemma writeVirtualRemoveVaddr descChild vaChild currentPart level
     idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
     phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
     ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2 
     currentShadow ptVaInCurPart defautvaddr vainparent idxvainparent:
{{ fun s : state =>
   propagatedPropertiesRemoveVaddr s descChild vaChild currentPart level
     idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
     phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
     ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2 vainparent vainparent
     currentShadow ptVaInCurPart idxvainparent false
     false /\ getPDFlag currentShadow vainparent s = false /\ 
     (exists pagetoremove, getAccessibleMappedPage currentPD s vainparent = SomePage  pagetoremove /\ 
(forall child, In child (getChildren currentPart s) -> ~In  pagetoremove (getMappedPages child s)))}} 
  MAL.writeVirtual ptVaChildsh2 idxvaChild defautvaddr
  {{ fun _ (s : state) =>
   propagatedPropertiesRemoveVaddr s descChild vaChild currentPart level
     idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
     phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
     ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2 vainparent defautvaddr
     currentShadow ptVaInCurPart idxvainparent false
     false /\ getPDFlag currentShadow vainparent s = false /\
     (exists pagetoremove, getAccessibleMappedPage currentPD s vainparent = SomePage  pagetoremove /\ 
(forall child, In child (getChildren currentPart s) -> ~In  pagetoremove (getMappedPages child s))) }}.
Proof.
eapply weaken.
eapply WP.writeVirtual.
simpl;intros.
unfold propagatedPropertiesRemoveVaddr in *.
assert(Hlookup :exists entry, 
 lookup ptVaChildsh2 idxvaChild (memory s) beqPage beqIndex = Some (VA entry)).
{ assert(Hva : isVA ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel) s) by intuition.

  unfold isVA in *.
  assert(Hidx :  StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild) by intuition.
 clear H.
 subst. 
 destruct(lookup ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel)
          (memory s) beqPage beqIndex);intros; try now contradict Hva.
 destruct v; try now contradict Hva.
 do 2 f_equal.
 exists v;trivial. }
 destruct Hlookup as (entry & Hlookup).
intuition try assumption. 
(** partitionsIsolation **)
+ apply partitionsIsolationUpdateSh2 with entry;trivial.
(** kernelDataIsolation **)
+ apply kernelDataIsolationUpdateSh2 with entry;trivial.
(** verticalSharing **)
+ apply verticalSharingUpdateSh2 with entry;trivial. 
(** consistency *)
+ apply consistencyRemoveVaddr with
    descChild vaChild currentPart level
    idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
    phyDescChild pdChildphy  ptVaChildpd shadow1Child
    ptVaChildFromSh1 vainve sh2Childphy  vainparent
    currentShadow ptVaInCurPart  entry;trivial. unfold propagatedPropertiesRemoveVaddr in *; unfold consistency in *;
    intuition.
(** Propagated properties **)
+ rewrite <- nextEntryIsPPUpdateSh2;trivial.
  exact Hlookup.
+ apply isVEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply entryPDFlagUpdateSh2 with entry;trivial.
+ rewrite <- nextEntryIsPPUpdateSh2;trivial.
  exact Hlookup.
+ apply isPEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply entryPresentFlagUpdateSh2 with entry;trivial.
+ apply isEntryPageUpdateSh2  with entry;trivial.
+ assert(Hchildren : forall part, getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add ptVaChildsh2 idxvaChild(VA defautvaddr) (memory s) beqPage
                 beqIndex |} = getChildren part s).
  { intros; symmetry; apply getChildrenUpdateSh2 with entry;trivial. } 
  rewrite Hchildren in *;trivial.
+ rewrite <- nextEntryIsPPUpdateSh2;trivial.
  exact Hlookup.
+ apply isPEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply entryUserFlagUpdateSh2 with entry;trivial.
+ apply entryPresentFlagUpdateSh2 with entry;trivial.
+ rewrite <- nextEntryIsPPUpdateSh2;trivial.
  exact Hlookup.
+ apply isVEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply isEntryVAUpdateSh2 with entry;trivial.
+ rewrite <- nextEntryIsPPUpdateSh2;trivial.
  exact Hlookup.
+ apply isVAUpdateSh2  with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ unfold isVA'.
  simpl.
  assert (Htrue : beqPairs (ptVaChildsh2, idxvaChild) (ptVaChildsh2, idxvaChild) beqPage
      beqIndex = true). 
  apply beqPairsTrue;split;trivial.
  rewrite Htrue.
  trivial.
+ apply isVEUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ assert(Hx :getPDFlag currentShadow vainparent
  s = false ) by trivial.
  rewrite <- Hx. apply getPDFlagUpdateSh2 with entry;trivial.
+ 
 assert(Hchildren : forall part, getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add ptVaChildsh2 idxvaChild(VA defautvaddr) (memory s) beqPage
                 beqIndex |} = getChildren part s).
  { intros; symmetry; apply getChildrenUpdateSh2 with entry;trivial. } 
  rewrite Hchildren in *;trivial.
 assert(Haccess : getAccessibleMappedPage currentPD
    {|
    currentPartition := currentPartition s;
    memory := add ptVaChildsh2 idxvaChild (VA defautvaddr) (memory s) beqPage
                beqIndex |} vainparent =getAccessibleMappedPage currentPD s vainparent).
 apply getAccessibleMappedPageUpdateSh2 with entry;trivial.
 rewrite Haccess.  
  assert(Hmap : forall part, getMappedPages part
        {|
        currentPartition := currentPartition s;
        memory := add ptVaChildsh2 idxvaChild (VA defautvaddr) (memory s)
                    beqPage beqIndex |} =getMappedPages part s).
 apply getMappedPagesUpdateSh2 with entry;trivial.
 assert(Hgoal: exists pagetoremove : page,
       getAccessibleMappedPage currentPD s vainparent = SomePage pagetoremove /\
       (forall child : page,
        In child (getChildren currentPart s) ->
        In pagetoremove (getMappedPages child s) -> False));trivial.
 destruct Hgoal as (x & Hx & Hxx). 
 exists x;split;trivial.
 intros.
 rewrite Hmap in *.
 apply Hxx with child;trivial.
Qed.

