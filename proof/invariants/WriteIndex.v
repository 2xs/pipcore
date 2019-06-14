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
Require Import Model.ADT Core.Internal Isolation Consistency WeakestPreconditions 
Invariants StateLib Model.Hardware  Model.MAL Model.ADT
DependentTypeLemmas Model.Lib InternalLemmas PropagatedProperties.
Require Import Coq.Logic.ProofIrrelevance Omega List Bool Logic.Classical_Prop.

(***************** To move ************************)
(*%%%%%%%%%%%%Consistency%%%%%%%%%%%*)

(*%%%%%%%%%%%%%%%% PropagatedProperties %%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%% InternalLemmas %%%%%%%%%%%%%%%%%%*)
Lemma inGetTrdShadowInConfigPagesAux partition LL table s:
partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
In table (getLLPages LL s (nbPage + 1)) ->
getConfigTablesLinkedList partition (memory s) = Some LL  ->
In table (getConfigPagesAux  partition s).
Proof.
intros Hpde Hgetparts Hconfig Hpd .
 apply pdSh1Sh2ListExistsNotNull with s partition  in Hpde;trivial.
  destruct Hpde as ((pd1 & Hpd1 & Hpdnotnull) 
    & (sh1 & Hsh1 & Hsh1notnull) & (sh22 & Hsh22 & Hsh2notnull) & 
    (sh3 & Hsh3 & Hsh3notnull)).
  unfold getConfigPages.
  unfold getConfigPagesAux.
  rewrite Hpd1, Hsh1, Hsh22, Hpd.
  do 3 (rewrite in_app_iff;
  right);trivial.
Qed.

Lemma inGetTrdShadowInConfigPages partition LL table s:
partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
In table (getLLPages LL s (nbPage + 1)) ->
getConfigTablesLinkedList partition (memory s) = Some LL  ->
In table (getConfigPages  partition s).
Proof.
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPages.
simpl;right.
apply inGetTrdShadowInConfigPagesAux with LL;trivial.
Qed.
Lemma LLtableNotPartition s LLtable partition LLroot :
In LLtable (getLLPages LLroot s (nbPage + 1))->
getConfigTablesLinkedList partition (memory s) = Some LLroot ->
In partition (getPartitions multiplexer s) ->
In LLtable (getConfigPages partition s) ->
configTablesAreDifferent s ->
noDupConfigPagesList s -> 
noDupPartitionTree s ->
partitionDescriptorEntry s ->
~ In LLtable (getPartitions multiplexer s).
Proof.
intros Htrd HLL Hpart Hisconfig Hconfigdiff Hconfignodup Hnoduptree Hpde.
unfold getPartitions.
assert(Hmult : In multiplexer (getPartitions multiplexer s)) by (unfold getPartitions;
destruct nbPage;simpl;left;trivial).
revert Hmult.
generalize multiplexer at 1 3.
generalize (nbPage+1) at 1.
induction n;simpl.
auto.
intros.
apply and_not_or.
split.
+ clear IHn.
  assert(Heqmult: p = partition \/ p <> partition) by apply pageDecOrNot.
  destruct Heqmult as [Heqmult | Heqmult].
  - subst.
    unfold noDupConfigPagesList in *.
    apply Hconfignodup in Hmult.
    unfold getConfigPages in Hmult.
    apply NoDup_cons_iff in Hmult.
    destruct Hmult as (Hi1 & Hi2).
    assert(Hkey:  In LLtable  (getConfigPagesAux partition s)).
    apply inGetTrdShadowInConfigPagesAux with LLroot;trivial.
    unfold not;intros;subst.
    now contradict Hkey.
 - unfold configTablesAreDifferent in *.
   assert(Heqmultt: partition <> p) by intuition.
   clear Heqmult.
   generalize(Hconfigdiff partition p  Hpart Hmult  Heqmultt); clear Hconfigdiff; intros Hconfigdiff.
   unfold Lib.disjoint in Hconfigdiff.
   apply Hconfigdiff in Hisconfig.
   unfold getConfigPages in Hisconfig.
   simpl in *.
   apply not_or_and in Hisconfig.
   intuition.
+ rewrite in_flat_map.
  unfold not;intros.
  destruct H as (x & Hx & Hxx).
  contradict Hxx.
  apply IHn.
  apply childrenPartitionInPartitionList with p;trivial.
Qed.

(**************************************************)

Lemma getConfigTablesLinkedListUpdateLLIndex partition x table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
(* partition<>table -> *)
StateLib.getConfigTablesLinkedList partition
  (add table idx (I x) (memory s) beqPage beqIndex) =
StateLib.getConfigTablesLinkedList partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getConfigTablesLinkedList.
case_eq ( StateLib.Index.succ sh3idx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
case_eq(  beqPairs (table, idx) (partition, i) beqPage beqIndex);intros.
+ apply beqPairsTrue in H0.
  intuition;subst.
  rewrite Hentry;trivial.
+ 
assert(Hmemory : lookup partition i (removeDup table idx (memory s) beqPage beqIndex) 
          beqPage beqIndex =  lookup  partition i (memory s) beqPage beqIndex ).
apply removeDupIdentity ; intuition.
apply beqPairsFalse in H0.
intuition.
rewrite Hmemory.
trivial.
Qed.


Lemma getFstShadowUpdateLLIndex partition x
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
StateLib.getFstShadow partition
  (add table idx (I x) (memory s) beqPage beqIndex) =
StateLib.getFstShadow partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getFstShadow.
case_eq ( StateLib.Index.succ sh1idx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
case_eq(  beqPairs (table, idx) (partition, i) beqPage beqIndex);intros.
+ apply beqPairsTrue in H0.
  intuition;subst.
  rewrite Hentry;trivial.
+ 
assert(Hmemory : lookup partition i (removeDup table idx (memory s) beqPage beqIndex) 
          beqPage beqIndex =  lookup  partition i (memory s) beqPage beqIndex ).
apply removeDupIdentity ; intuition.
apply beqPairsFalse in H0.
intuition.
rewrite Hmemory.
trivial.
Qed.

Lemma getSndShadowUpdateLLIndex partition x
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
StateLib.getSndShadow partition
  (add table idx (I x) (memory s) beqPage beqIndex) =
StateLib.getSndShadow partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getSndShadow.
case_eq ( StateLib.Index.succ sh2idx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
case_eq(  beqPairs (table, idx) (partition, i) beqPage beqIndex);intros.
+ apply beqPairsTrue in H0.
  intuition;subst.
  rewrite Hentry;trivial.
+ 
assert(Hmemory : lookup partition i (removeDup table idx (memory s) beqPage beqIndex) 
          beqPage beqIndex =  lookup  partition i (memory s) beqPage beqIndex ).
apply removeDupIdentity ; intuition.
apply beqPairsFalse in H0.
intuition.
rewrite Hmemory.
trivial.
Qed.

Lemma getPdUpdateLLIndex partition x
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
StateLib.getPd partition
  (add table idx (I x) (memory s) beqPage beqIndex) =
StateLib.getPd partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getPd.
case_eq ( StateLib.Index.succ PDidx ); intros; trivial.
cbn.
unfold StateLib.readPhysical.
cbn.
case_eq(  beqPairs (table, idx) (partition, i) beqPage beqIndex);intros.
+ apply beqPairsTrue in H0.
  intuition;subst.
  rewrite Hentry;trivial.
+ 
assert(Hmemory : lookup partition i (removeDup table idx (memory s) beqPage beqIndex) 
          beqPage beqIndex =  lookup  partition i (memory s) beqPage beqIndex ).
apply removeDupIdentity ; intuition.
apply beqPairsFalse in H0.
intuition.
rewrite Hmemory.
trivial.
Qed.

Lemma getParentUpdateLLIndex partition x
table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
StateLib.getParent partition
  (add table idx (I x) (memory s) beqPage beqIndex) =
StateLib.getParent partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getParent.
case_eq ( StateLib.Index.succ PPRidx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
cbn.
case_eq(  beqPairs (table, idx) (partition, i) beqPage beqIndex);intros.
+ apply beqPairsTrue in H0.
  intuition;subst.
  rewrite Hentry;trivial.
+ 
assert(Hmemory : lookup partition i (removeDup table idx (memory s) beqPage beqIndex) 
          beqPage beqIndex =  lookup  partition i (memory s) beqPage beqIndex ).
apply removeDupIdentity ; intuition.
apply beqPairsFalse in H0.
intuition.
rewrite Hmemory.
trivial.
Qed.



Lemma getTablePagesUpdateLLIndex    table idx entry size p (s : state)  x:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) -> 
getTablePages p size
 {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |} =
getTablePages p size s.
Proof.
revert p .
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx (I x)
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

Lemma getIndirectionsUpdateLLIndex  table idx entry pd (s : state) x:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->  
getIndirections pd
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
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
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}= getTablePages pd tableSize s) as Htablepages.
apply getTablePagesUpdateLLIndex with entry ;trivial.
rewrite Htablepages.
clear Htablepages.
induction (getTablePages pd tableSize s); intros; trivial.
simpl in *.
rewrite IHn. 
f_equal.
apply IHl.
Qed.

Lemma readPhysicalUpdateLLIndex  idx1
table idx (s : state)  p   x entry: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
StateLib.readPhysical p idx1
  (add table idx (I x) (memory s) beqPage beqIndex) =
StateLib.readPhysical p idx1 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPhysical.
cbn.
case_eq(  beqPairs (table, idx) (p, idx1) beqPage beqIndex);intros.
+ apply beqPairsTrue in H.
  intuition;subst.
  rewrite Hentry;trivial.
+ 
assert(Hmemory : lookup p idx1 (removeDup table idx (memory s) beqPage beqIndex) 
          beqPage beqIndex =  lookup  p idx1 (memory s) beqPage beqIndex ).
apply removeDupIdentity ; intuition.
apply beqPairsFalse in H.
intuition.
rewrite Hmemory.
trivial.
Qed.


Lemma getLLPagesUpdateLLIndex table idx p2 s x entry:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |} in 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->          
getLLPages p2 s' (nbPage + 1) = getLLPages p2 s (nbPage + 1).
Proof.
intros.
revert p2.
induction  (nbPage + 1);simpl;trivial.
case_eq( StateLib.getMaxIndex);intros;trivial.
assert(Hreadp: StateLib.readPhysical p2 i (add table idx (I x) (memory s) beqPage beqIndex) =
StateLib.readPhysical p2 i (memory s)).
apply readPhysicalUpdateLLIndex with entry;trivial.
rewrite Hreadp.
destruct(StateLib.readPhysical p2 i (memory s));trivial.
rewrite <- IHn;trivial.
Qed.

Lemma getConfigPagesUpdateLLIndex s x table idx entry part: 
(* part <> table -> *)
(* StateLib.getMaxIndex <> Some idx ->  *) 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
 getConfigPages part {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}  = getConfigPages part s.
Proof.
intros.
unfold getConfigPages. 
f_equal.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s)
              beqPage beqIndex |}) in *.
unfold getConfigPagesAux.
assert(Hgetpd: StateLib.getPd part (memory s') = StateLib.getPd part (memory s)).
{ apply getPdUpdateLLIndex with entry;trivial.   }
rewrite Hgetpd. clear Hgetpd.
case_eq(StateLib.getPd part (memory s));intros; trivial.
assert(Hgetsh1: StateLib.getFstShadow part (memory s') = StateLib.getFstShadow part (memory s)).
{ simpl. apply getFstShadowUpdateLLIndex with entry;trivial.  }
rewrite Hgetsh1. clear Hgetsh1.
case_eq(StateLib.getFstShadow part (memory s));intros; trivial.
assert(Hgetsh2: StateLib.getSndShadow part (memory s') = StateLib.getSndShadow part (memory s)).
{  apply getSndShadowUpdateLLIndex with entry;trivial.    }
rewrite Hgetsh2. clear Hgetsh2.
case_eq(StateLib.getSndShadow part (memory s));intros; trivial.
assert(Hgetconfig: StateLib.getConfigTablesLinkedList part (memory s') =
 StateLib.getConfigTablesLinkedList part (memory s)).
{  apply getConfigTablesLinkedListUpdateLLIndex with entry;trivial.   }
rewrite Hgetconfig. clear Hgetconfig.
case_eq(StateLib.getConfigTablesLinkedList part (memory s));intros; trivial.
simpl.
assert(Hind : forall root, getIndirections root s' = getIndirections root s).
{ intros.  
  apply getIndirectionsUpdateLLIndex with entry;trivial. }
do 3 rewrite Hind.
do 3 f_equal.
apply getLLPagesUpdateLLIndex with entry ;trivial.
Qed.

Lemma getIndirectionUpdateLLIndex sh1 table idx s entry va nbL stop x:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
getIndirection sh1 va nbL stop
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |} =
getIndirection sh1 va nbL stop s .
Proof.
intros Hentry.
revert sh1 nbL.
induction  stop.
+ simpl. trivial.
+ simpl. intros. 
  destruct (StateLib.Level.eqb nbL fstLevel);trivial.
  set (entry0 := (I x)  ) in *.
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
  destruct (defaultPage =? p);trivial.
  destruct ( StateLib.Level.pred nbL );trivial.
Qed.

Lemma readPresentUpdateLLIndex  idx1
table idx (s : state)  p   entry x: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) -> 
StateLib.readPresent p idx1
  (add table idx (I x) (memory s) beqPage beqIndex) =
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

Lemma readAccessibleUpdateLLIndex 
table idx (s : state)  p  idx1 entry x: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) -> 
StateLib.readAccessible p idx1
  (add table idx (I x) (memory s) beqPage beqIndex) =
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

Lemma readPhyEntryUpdateLLIndex 
table idx (s : state)  p  idx1 entry x: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) -> 
StateLib.readPhyEntry p idx1
  (add table idx (I x) (memory s) beqPage beqIndex) =
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

Lemma readVirEntryUpdateLLIndex 
table idx (s : state)  p  idx1 entry x: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) -> 
StateLib.readVirEntry p idx1
  (add table idx (I x) (memory s) beqPage beqIndex) =
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

Lemma readPDflagUpdateLLIndex idx1
table idx (s : state)  p   entry x: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) -> 
StateLib.readPDflag p idx1
    (add table idx (I x) (memory s) beqPage beqIndex) =
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

Lemma getMappedPageUpdateLLIndex root s x table idx va entry:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
getMappedPage root {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}  va = getMappedPage root s va.
Proof.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s) beqPage
              beqIndex |}) in *.
intros Hentry. 
unfold getMappedPage.
destruct(StateLib.getNbLevel);intros;trivial.
assert(Hind : getIndirection root va l (nbLevel - 1) s' =
getIndirection root va l (nbLevel - 1) s).
apply getIndirectionUpdateLLIndex with entry;trivial.
rewrite Hind.  
destruct(getIndirection root va l (nbLevel - 1)  s); intros; trivial.
destruct(defaultPage =? p);trivial.
 assert(Hpresent :    StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
  (memory s) = StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (I x) (memory s) beqPage beqIndex) ).
symmetry.
apply readPresentUpdateLLIndex with entry; trivial.
unfold s'. simpl.
rewrite <- Hpresent.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) ); trivial.
destruct b; trivial.
assert(Heq :StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (I x) (memory s) beqPage beqIndex) =
   StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s) );intros.
apply readPhyEntryUpdateLLIndex  with entry; trivial .
rewrite Heq;trivial.
Qed.

Lemma getAccessibleMappedPageUpdateLLIndex root s x table idx va entry:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
getAccessibleMappedPage root {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}  va = getAccessibleMappedPage root s va.
Proof.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s) beqPage
              beqIndex |}) in *.
intros Hentry. 
unfold getAccessibleMappedPage.
destruct(StateLib.getNbLevel);intros;trivial.
assert(Hind : getIndirection root va l (nbLevel - 1) s' =
getIndirection root va l (nbLevel - 1) s).
apply getIndirectionUpdateLLIndex with entry;trivial.
rewrite Hind.  
destruct(getIndirection root va l (nbLevel - 1)  s); intros; trivial.
destruct(defaultPage =? p);trivial.
 assert(Hpresent :    StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
  (memory s) = StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (I x) (memory s) beqPage beqIndex) ).
symmetry.
apply readPresentUpdateLLIndex with entry; trivial.
unfold s'. simpl.
rewrite <- Hpresent.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) ); trivial.
destruct b; trivial.
assert(Haccess :    StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel)
  (memory s) = StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (I x) (memory s) beqPage beqIndex) ).
symmetry.
apply readAccessibleUpdateLLIndex with entry; trivial.
unfold s'. simpl.
rewrite <- Haccess.
destruct(StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel) (memory s) ); trivial.
destruct b; trivial.
assert(Heq :StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (I x) (memory s) beqPage beqIndex) =
   StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s) );intros.
apply readPhyEntryUpdateLLIndex  with entry; trivial .
rewrite Heq;trivial.
Qed.

Lemma getMappedPagesAuxUpdateLLIndex root s x table idx entry l:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
getMappedPagesAux root l {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |} = 
getMappedPagesAux root l s.
Proof.
intros Hentry.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s) beqPage
              beqIndex |}) in *.
unfold getMappedPagesAux.
f_equal.
unfold getMappedPagesOption.
simpl.
induction l.
simpl;trivial.
simpl. 
rewrite IHl;f_equal.
apply getMappedPageUpdateLLIndex with entry; trivial.
Qed.


Lemma getAccessibleMappedPagesAuxUpdateLLIndex root s x table idx entry l:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
getAccessibleMappedPagesAux root l {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |} = 
getAccessibleMappedPagesAux root l s.
Proof.
intros Hentry.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s) beqPage
              beqIndex |}) in *.
unfold getAccessibleMappedPagesAux.
f_equal.
unfold getAccessibleMappedPagesOption.
simpl.
induction l.
simpl;trivial.
simpl. 
rewrite IHl;f_equal.
apply getAccessibleMappedPageUpdateLLIndex with entry; trivial.
Qed.

Lemma getMappedPagesUpdateLLIndex s x table idx entry part: 
(* part <> table ->  *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
 getMappedPages part {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}  = getMappedPages part s.
Proof.
intros.
unfold getMappedPages.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s)
              beqPage beqIndex |}) in *.
assert(Hgetpd: StateLib.getPd part (memory s') = StateLib.getPd part (memory s)).
{ apply getPdUpdateLLIndex with entry;trivial.  }
rewrite Hgetpd.
case_eq(StateLib.getPd part (memory s));intros; trivial.
apply getMappedPagesAuxUpdateLLIndex with entry;trivial.
Qed.

Lemma getAccessibleMappedPagesUpdateLLIndex s x table idx entry part: 
(* part <> table -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
getAccessibleMappedPages part {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}  = getAccessibleMappedPages part s.
Proof.
intros.
unfold getAccessibleMappedPages.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s)
              beqPage beqIndex |}) in *.
assert(Hgetpd: StateLib.getPd part (memory s') = StateLib.getPd part (memory s)).
{ apply getPdUpdateLLIndex with entry;trivial.  }
rewrite Hgetpd.
case_eq(StateLib.getPd part (memory s));intros; trivial.
apply getAccessibleMappedPagesAuxUpdateLLIndex with entry;trivial.
Qed.

Lemma checkChildUpdateLLIndex s x table idx entry l va part: 
(* part <> table -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
checkChild part l {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |} va = checkChild part l s va.
Proof.
intros Hentry.
unfold checkChild.
simpl.
assert(Hsh1 : getFstShadow part
    (add table idx (I x) (memory s) beqPage beqIndex)=
    getFstShadow part (memory s)). 
{ apply getFstShadowUpdateLLIndex with entry; trivial. }
rewrite Hsh1.
destruct(getFstShadow part (memory s) );trivial.
assert(Hind : getIndirection p va l (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx (I x) (memory s) beqPage
                beqIndex |} = getIndirection p va l (nbLevel - 1)
    s).
apply getIndirectionUpdateLLIndex with entry;trivial.
rewrite Hind.
destruct (getIndirection p va l (nbLevel - 1) s );trivial.
destruct (p0 =? defaultPage);trivial.
assert(Hpdflag :  StateLib.readPDflag p0 (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (I x) (memory s) beqPage beqIndex) =
   StateLib.readPDflag p0 (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
  apply readPDflagUpdateLLIndex with entry;trivial.
rewrite Hpdflag.
trivial.
Qed.

Lemma getPdsVAddrUpdateLLIndex s x table idx entry l part: 
(* part <> table -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
 getPdsVAddr part l getAllVAddrWithOffset0 {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}  = getPdsVAddr part l getAllVAddrWithOffset0 s.
Proof.
intros.
unfold getPdsVAddr.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s)
              beqPage beqIndex |}) in *.
induction getAllVAddrWithOffset0;simpl;trivial.
assert(Hcheckchild: checkChild part l s' a = checkChild part l s a).
{ simpl. apply checkChildUpdateLLIndex with entry;trivial. }
rewrite Hcheckchild;trivial.
case_eq(checkChild part l s a);intros;[
f_equal|];
apply IHl0.
Qed.

Lemma getChildrenUpdateLLIndex s x table idx entry part: 
(* part <> table -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) -> 
getChildren part s = 
getChildren part{|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold getChildren.
set (s' := {|
             currentPartition := currentPartition s;
             memory := add table idx (I x) (memory s)
                         beqPage beqIndex |}) in *.
intros. 
destruct ( StateLib.getNbLevel);trivial.
simpl.
assert(Hpd :  StateLib.getPd part (memory s) =
StateLib.getPd part
    (add table idx (I x) (memory s) beqPage beqIndex)).
{ symmetry. apply getPdUpdateLLIndex with entry;trivial.  }
rewrite <- Hpd.
destruct(StateLib.getPd part (memory s));trivial.
assert(Hpds : getPdsVAddr part l getAllVAddrWithOffset0 s' =
 getPdsVAddr part l getAllVAddrWithOffset0 s).
apply getPdsVAddrUpdateLLIndex with entry;trivial.
rewrite Hpds.
unfold s'.
symmetry.
apply getMappedPagesAuxUpdateLLIndex with entry;trivial.
Qed.

Lemma getPartitionsUpdateLLIndex s x table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) -> 
(* ~In table (getPartitions multiplexer s) -> *)
getPartitions multiplexer s = getPartitions multiplexer{|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}. 
Proof.
intro.
generalize multiplexer at 1 2.
unfold getPartitions.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s)
              beqPage beqIndex |}) in *.
induction (nbPage + 1);simpl;trivial.
intros.
f_equal.
assert(Hchildren: getChildren p s' =getChildren p s).
{ symmetry. apply getChildrenUpdateLLIndex with entry;trivial.
(* apply Logic.Classical_Prop.not_or_and in H0. intuition. *) }
rewrite Hchildren. clear Hchildren.
induction (getChildren p s);simpl;trivial.
simpl in *.
rewrite IHn;trivial.
f_equal.
trivial.
Qed.

Lemma nextEntryIsPPUpdateLLIndex table idx0 partition idx v x entry s :
lookup table idx0 (memory s) beqPage beqIndex = Some (I entry) ->
(* table <> partition -> *)
nextEntryIsPP partition idx v s <-> 
nextEntryIsPP partition idx v
  {|
currentPartition := currentPartition s;
memory := add table idx0 (I x)
            (memory s) beqPage beqIndex |}.
Proof.
intros.
split.
- intros.
unfold nextEntryIsPP in *;
case_eq(StateLib.Index.succ idx ); [intros idxsucc Hidxsucc| intros Hidxsucc];simpl;trivial;intros;
rewrite Hidxsucc in H0;trivial.
case_eq( beqPairs (table, idx0) (partition, idxsucc) beqPage beqIndex);intros.
+
apply beqPairsTrue in H1.
intuition;subst.
rewrite H in H0;trivial.
+ apply beqPairsFalse in H1.
 assert (lookup  partition idxsucc (removeDup table idx0 (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition idxsucc   (memory s) beqPage beqIndex) as Hmemory.
          
apply removeDupIdentity; intuition.
     rewrite Hmemory in *; trivial.
- intros.
unfold nextEntryIsPP in *;
case_eq(StateLib.Index.succ idx ); [intros idxsucc Hidxsucc| intros Hidxsucc];simpl;trivial;intros;
rewrite Hidxsucc in H0;trivial.
simpl in *.
case_eq( beqPairs (table, idx0) (partition, idxsucc) beqPage beqIndex);intros.
+ rewrite H1 in *.
now contradict H0.
+ rewrite H1 in H0.
 apply beqPairsFalse in H1.
 assert (lookup  partition idxsucc (removeDup table idx0 (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition idxsucc   (memory s) beqPage beqIndex) as Hmemory.
          
apply removeDupIdentity; intuition.
     rewrite Hmemory in *; trivial.
Qed.

Lemma isVAUpdateLLIndex idx partition table entry idxroot s x:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
isVA partition idxroot s -> 
isVA partition idxroot
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}.
Proof.
intros.
unfold isVA in *.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) beqPage beqIndex);trivial;intros Hpairs.
apply beqPairsTrue in Hpairs.
intuition;subst.
rewrite H in H0;trivial.
apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition idxroot   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.


Lemma isPEUpdateLLIndex idx partition table  entry idxroot s x:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
isPE partition idxroot s -> 
isPE partition idxroot
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
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

Lemma isVEUpdateLLIndex idx partition table  entry idxroot s x:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
isVE partition idxroot s -> 
isVE partition idxroot
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
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


Lemma entryUserFlagUpdateLLIndex idx ptVaInCurPartpd idxvaInCurPart table 
 entry s x accessiblesrc:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
entryUserFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc s -> 
entryUserFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
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

Lemma entryPresentFlagUpdateLLIndex idx ptVaInCurPartpd idxvaInCurPart table 
 entry s x accessiblesrc:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
entryPresentFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc s -> 
entryPresentFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
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

Lemma entryPDFlagUpdateLLIndex idx ptDescChild table idxDescChild entry s x flag:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
entryPDFlag ptDescChild idxDescChild flag s -> 
entryPDFlag ptDescChild idxDescChild flag
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
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

Lemma isEntryVAUpdateLLIndex idx ptVaInCurPart table idxvaInCurPart entry s  vainve x:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
isEntryVA ptVaInCurPart idxvaInCurPart vainve s -> 
isEntryVA ptVaInCurPart idxvaInCurPart vainve
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
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

Lemma isIndexValueUpdateLLIndex idx ptVaInCurPart table idxvaInCurPart  s  vainve x:
ptVaInCurPart <> table \/ idxvaInCurPart <> idx ->
isIndexValue ptVaInCurPart idxvaInCurPart vainve s -> 
isIndexValue ptVaInCurPart idxvaInCurPart vainve
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold isIndexValue.
cbn.
case_eq (beqPairs (table, idx) (ptVaInCurPart, idxvaInCurPart) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   intuition.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptVaInCurPart idxvaInCurPart (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  ptVaInCurPart idxvaInCurPart  (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed. 

Lemma isIndexValueSameUpdateLLIndex idx table s  x:
isIndexValue table idx  x
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}.
Proof.
unfold isIndexValue.
cbn.
assert (beqPairs (table, idx) (table, idx) beqPage beqIndex = true).
apply beqPairsTrue.
intuition.
rewrite H;trivial.
Qed. 


Lemma isVA'UpdateLLIndex idx ptVaInCurPart table idxvaInCurPart entry s  vainve x:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
isVA' ptVaInCurPart idxvaInCurPart vainve s -> 
isVA' ptVaInCurPart idxvaInCurPart vainve
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold isVA'.
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

Lemma isPP'UpdateLLIndex idx ptVaInCurPart table idxvaInCurPart entry s  vainve x:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
isPP' ptVaInCurPart idxvaInCurPart vainve s -> 
isPP' ptVaInCurPart idxvaInCurPart vainve
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold isPP'.
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

Lemma isEntryPageUpdateLLIndex idx ptVaInCurPart table idxvaInCurPart entry s  vainve x:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
isEntryPage ptVaInCurPart idxvaInCurPart vainve s -> 
isEntryPage ptVaInCurPart idxvaInCurPart vainve
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
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

Lemma partitionsIsolationUpdateLLIndex s x table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
partitionsIsolation s ->
(* ~ In table (getPartitions multiplexer s)  ->
StateLib.getMaxIndex <> Some idx ->  *)
noDupPartitionTree s ->
partitionsIsolation {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup Hisopart.
intros(*  Hkey1 Hkey2 *) Hnodup.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}) in *. 
unfold partitionsIsolation in *. 
intros (* Hisopart *) parent child1 child2 Hparent Hchild1 Hchild2 Hdist.
assert(Hparts : getPartitions multiplexer s = getPartitions multiplexer s').
apply getPartitionsUpdateLLIndex with entry;trivial.
rewrite <- Hparts in *;trivial.  
  assert (Hused :  forall part, getUsedPages part s' = getUsedPages part s). 
  { intros. 
    unfold getUsedPages in *. 
    assert(Hconfig : forall part, getConfigPages part s' = getConfigPages part s).
    { intros.
      apply getConfigPagesUpdateLLIndex with entry;trivial. } 
    rewrite Hconfig in *.
    f_equal.
    assert(Hmap :  forall part, getMappedPages part s' = getMappedPages part s).
    { intros.
      apply getMappedPagesUpdateLLIndex with entry;trivial. } 
    rewrite Hmap in *;trivial. }    
  assert(Hchildren : getChildren parent s = getChildren parent s').
  apply getChildrenUpdateLLIndex with entry;trivial.
  rewrite <- Hchildren in *. clear Hchildren.
  assert( In child1 (getPartitions multiplexer s)).
  apply childrenPartitionInPartitionList with parent;trivial.
  assert( In child2 (getPartitions multiplexer s)).
  apply childrenPartitionInPartitionList with parent;trivial.
  rewrite Hused;trivial.
  rewrite Hused;trivial.
  apply Hisopart with parent;trivial.
Qed.

Lemma kernelDataIsolationUpdateLLIndex s x table idx entry: 
(* StateLib.getMaxIndex <> Some idx -> 
~ In table (getPartitions multiplexer s) -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
kernelDataIsolation s ->
kernelDataIsolation {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}. 
Proof.
(* intros Hkey2.
intro. *)
intros Hlookup.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}) in *. 
unfold kernelDataIsolation in *. 
intros Hkdi partition1 partition2 Hpart1 Hpart2.
assert(Hparts : getPartitions multiplexer s = getPartitions multiplexer s').
apply getPartitionsUpdateLLIndex with entry;trivial.
rewrite <- Hparts in *;trivial. clear Hparts.
assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
{ intros.
apply getConfigPagesUpdateLLIndex with entry;trivial.
 } 
rewrite Hconfig in *. clear Hconfig.
assert(Haccessmap : getAccessibleMappedPages partition1 s' =
getAccessibleMappedPages partition1 s).
{ intros. apply getAccessibleMappedPagesUpdateLLIndex with entry;trivial. }
rewrite Haccessmap in *. 
apply Hkdi;trivial.
Qed.  

Lemma verticalSharingUpdateLLIndex s x table idx entry: 
(* StateLib.getMaxIndex <> Some idx -> 
~ In table (getPartitions multiplexer s) -> *)
noDupPartitionTree s ->
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
verticalSharing s ->
verticalSharing {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}. 
Proof.
(* intros Hkey2. *)
intros (* H *) H0.
intros Hlookup.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}) in *. 
unfold verticalSharing in *.
intros Hvs parent child Hparent Hchild.
assert(Hparts : getPartitions multiplexer s = getPartitions multiplexer s').
apply getPartitionsUpdateLLIndex with entry;trivial.
rewrite <- Hparts in *;trivial. clear Hparts.
assert(Hchildren : getChildren parent s = getChildren parent s').
apply getChildrenUpdateLLIndex with entry;trivial.
rewrite <- Hchildren in *. clear Hchildren.
assert(Hmap :  forall part,  getMappedPages part s' = getMappedPages part s).
{ intros.
  apply getMappedPagesUpdateLLIndex with entry;trivial. } 
  rewrite Hmap in *;trivial.
assert (Hused : forall part,  getUsedPages part s' = getUsedPages part s). 
{ intros. 
  unfold getUsedPages in *. 
  assert(Hconfig : forall part, getConfigPages part s' = getConfigPages part s).
  { intros.
    apply getConfigPagesUpdateLLIndex with entry;trivial. } 
  rewrite Hconfig in *;trivial.
  rewrite Hmap;trivial.  }
assert(In child (getPartitions multiplexer s)) by (apply childrenPartitionInPartitionList with parent;trivial).
rewrite Hused;trivial.
apply Hvs;trivial.
Qed.


Lemma isPPUpdateLLIndex table p idx idx0 x entry s:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
isPP p idx0 s -> 
isPP p idx0 {|
      currentPartition := currentPartition s;
      memory := add table idx (I x) (memory s) beqPage beqIndex |}.
Proof.      
intros.
unfold isPP in *.
simpl.
case_eq (beqPairs  (table, idx) (p, idx0)  beqPage beqIndex);trivial;intros Hpairs.
+  apply beqPairsTrue in Hpairs.
  intuition;subst.
  rewrite H in H0.
  trivial.
+
apply beqPairsFalse in Hpairs.    
assert (lookup p idx0 (removeDup table idx   (memory s) beqPage beqIndex)
       beqPage beqIndex = lookup  p idx0  (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. intuition. }
 rewrite Hmemory. trivial.
Qed.


Lemma dataStructurePdSh1Sh2asRootUpdateLLIndex s x table idx entry idxroot: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
(* ~ In table (getPartitions multiplexer s) -> *)
dataStructurePdSh1Sh2asRoot idxroot s ->
dataStructurePdSh1Sh2asRoot idxroot {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup (* Hkey *) Hds.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}) in *. 
unfold dataStructurePdSh1Sh2asRoot in *.
intros.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer s').
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions.
unfold s' in *.
intros.
rewrite <- nextEntryIsPPUpdateLLIndex in H0; try eassumption.
assert (Hind : getIndirection entry0 va level stop s = Some indirection).
{ rewrite <- H3. symmetry.
  apply getIndirectionUpdateLLIndex with entry; trivial. }
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
  apply isPEUpdateLLIndex with entry; trivial.
+ right.
  destruct Hds as (Hlevel & [(Hve & Hidx) | [(Hva & Hidx) | (Hpe & Hidx)]]).
  split; trivial.
  - left; split; trivial.
    apply isVEUpdateLLIndex with entry; trivial.
  - split; trivial.
    right; left;split; trivial.
    apply isVAUpdateLLIndex with entry; trivial.
  - split;trivial.
    right;right; split; trivial.
    apply isPEUpdateLLIndex with entry; trivial.
Qed.

Lemma partitionDescriptorEntryUpdateLLIndex s x table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
(* ~ In table (getPartitions multiplexer s) -> *)
partitionDescriptorEntry s ->
partitionDescriptorEntry {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup (* Hkey *).
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
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
  simpl;omega.
  unfold sh1idx.
  unfold CIndex.
  case_eq( lt_dec 4 tableSize );intros;
  simpl;omega.
   unfold sh2idx.
  unfold CIndex.
  case_eq( lt_dec 6 tableSize );intros;
  simpl;omega.
   unfold sh3idx.
  unfold CIndex.
  case_eq( lt_dec 8 tableSize );intros;
  simpl;omega.
  unfold PPRidx.
  unfold CIndex.
  case_eq( lt_dec 10 tableSize );intros;
  simpl;omega.
  unfold PRidx.
  unfold CIndex.
  case_eq( lt_dec 0 tableSize );intros;
  simpl;omega. }
assert(Hparts : getPartitions multiplexer s = getPartitions multiplexer s').
apply getPartitionsUpdateLLIndex with entry;trivial.
rewrite <- Hparts in *;trivial. clear Hparts.
assert (HPP : forall p idx, isVA p idx s -> isVA p idx s').
{ intros.
  apply isVAUpdateLLIndex with entry;trivial. }
assert (HPE : forall p idx x, (* table <> p -> *) nextEntryIsPP p idx x s -> 
            nextEntryIsPP   p idx x s').
{ intros.
  apply nextEntryIsPPUpdateLLIndex with entry;trivial. }

assert(Hconcl : idxroot < tableSize - 1 /\
       isVA part idxroot s /\
       (exists entry : page, nextEntryIsPP part idxroot entry s /\ entry <> defaultPage)).
apply Hpde;trivial.
destruct Hconcl as (Hi1 & Hi2 & Hi3).
split;trivial.
split.
apply HPP;trivial.
destruct Hi3 as (entry0 & Hentry & Htrue).
exists entry0;split;trivial.
apply HPE;trivial.
Qed. 

Lemma currentPartitionInPartitionsListUpdateLLIndex s x table idx entry : 
(* ~ In table (getPartitions multiplexer s) -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
currentPartitionInPartitionsList s ->
currentPartitionInPartitionsList {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}. 
Proof.
intro.
intros Hlookup.
unfold currentPartitionInPartitionsList.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (I x) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite<- Hpartitions ;  clear Hpartitions;trivial.
Qed.

Lemma noDupMappedPagesListUpdateLLIndex s x table idx entry : 
(* ~ In table (getPartitions multiplexer s) -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
noDupMappedPagesList s ->
noDupMappedPagesList {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}. 
Proof.
intro (* Hkey *).
intros Hlookup.
unfold noDupMappedPagesList in *.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (I x) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hmap :  forall part,  getMappedPages part {|
     currentPartition := currentPartition s;
     memory := add table idx (I x) (memory s) beqPage
                 beqIndex |}= getMappedPages part s).
{ intros.
  apply getMappedPagesUpdateLLIndex with entry;trivial.
 }
  rewrite Hmap;trivial.
  
  trivial.
apply Hlookup;trivial.
Qed.

Lemma noDupConfigPagesListUpdateLLIndex s x table idx entry : 
(* StateLib.getMaxIndex <> Some idx -> 
~ In table (getPartitions multiplexer s) -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
noDupConfigPagesList s ->
noDupConfigPagesList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s) beqPage
              beqIndex |}. 
Proof.
(* intros Hkey2.
intro Hkey. *)
intros Hlookup.
unfold noDupConfigPagesList.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (I x) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hind :   forall part, getConfigPages part {|
     currentPartition := currentPartition s;
     memory := add table idx (I x) (memory s) beqPage
                 beqIndex |}= getConfigPages part s).
{ intros.
  apply getConfigPagesUpdateLLIndex with entry;trivial. }
  rewrite Hind;trivial.
apply H ;trivial.
Qed. 

Lemma parentInPartitionListUpdateLLIndex s x table idx entry : 
(* ~ In table (getPartitions multiplexer s) -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
parentInPartitionList s ->
parentInPartitionList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s) beqPage
              beqIndex |}. 
Proof.
(* intro Hkey. *)
intros Hlookup.
unfold parentInPartitionList.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (I x) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
apply H with partition;trivial.
rewrite nextEntryIsPPUpdateLLIndex with  entry;trivial.
eassumption;trivial.
trivial.
Qed.


Lemma getPDFlagUpdateLLIndex s x table idx entry sh1 va: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
getPDFlag sh1 va
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s) beqPage
              beqIndex |} = getPDFlag sh1 va s.
Proof.
intros Hentry.
unfold getPDFlag.
simpl.
destruct (StateLib.getNbLevel);trivial.
assert(Hind : getIndirection sh1 va l (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx (I x) (memory s) beqPage
                beqIndex |} = getIndirection  sh1 va l (nbLevel - 1)
    s).
apply getIndirectionUpdateLLIndex with entry;trivial.
rewrite Hind.
destruct (getIndirection  sh1 va l (nbLevel - 1) s );trivial.
destruct (p =? defaultPage);trivial.
assert(Hpdflag :  StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (I x) (memory s) beqPage beqIndex) =
   StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
  apply readPDflagUpdateLLIndex with entry;trivial.
rewrite Hpdflag.
trivial.
Qed. 

Lemma accessibleVAIsNotPartitionDescriptorUpdateLLIndex s x table idx entry : 
(* ~ In table (getPartitions multiplexer s) -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
accessibleVAIsNotPartitionDescriptor s ->
accessibleVAIsNotPartitionDescriptor
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s) beqPage
              beqIndex |}. 
Proof.
(* intro Hkey.
 *) intros Hlookup.
unfold accessibleVAIsNotPartitionDescriptor.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (I x) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Haccessmap : forall part, getAccessibleMappedPage part {|
       currentPartition := currentPartition s;
       memory := add table idx (I x) (memory s) beqPage
                   beqIndex |} va =
getAccessibleMappedPage part s va).
{ intros. apply getAccessibleMappedPageUpdateLLIndex with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
assert(Hpd :  StateLib.getPd partition (memory s) =
StateLib.getPd partition
    (add table idx (I x) (memory s) beqPage beqIndex)).
{ symmetry. apply getPdUpdateLLIndex with entry;trivial. }
rewrite <- Hpd in *.
assert(Hsh1 :  StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (I x) (memory s) beqPage beqIndex)).
{ symmetry. apply getFstShadowUpdateLLIndex with entry;trivial.
}
rewrite <- Hsh1 in *.
rewrite <- H with partition va pd sh1 page;trivial.
apply getPDFlagUpdateLLIndex with entry;trivial.
Qed. 

Lemma readVirtualUpdateLLIndex table1 table2 idx1 idx2  x entry s :
(* table1 <> table2 \/ idx1 <> idx2 ->  *)
lookup table2 idx2 (memory s) beqPage beqIndex = Some (I entry) ->
 StateLib.readVirtual table1 idx1
         (add table2 idx2 (I x) (memory s) beqPage
     beqIndex)  = 
 StateLib.readVirtual table1 idx1 (memory s).
Proof.
unfold StateLib.readVirtual.
cbn.
intros Hentry.
case_eq( beqPairs  (table2, idx2) (table1, idx1) beqPage beqIndex); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex) beqPage beqIndex = 
 lookup table1 idx1 (memory s)  beqPage beqIndex ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.


Lemma wellFormedShadowsUpdateLLIndex s vaInCurrentPartition table idx entry idxroot: 
(* ~ In table (getPartitions multiplexer s) -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I  entry) ->
wellFormedShadows idxroot s -> 
wellFormedShadows idxroot
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
(* intros Hkey.
 *) intros Hlookup.
unfold wellFormedShadows.
intros.
simpl in *.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, (* In partition (getPartitions multiplexer s) 
    -> partition <> table -> *) StateLib.getPd partition
       (add table idx (I  vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros.
  apply getPdUpdateLLIndex with entry;trivial. }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hpp : nextEntryIsPP partition idxroot structroot s ). 
rewrite nextEntryIsPPUpdateLLIndex with entry;trivial.
eassumption. 
trivial.
assert(Hind : forall root, getIndirection root va nbL stop
    {|
    currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                beqIndex |} = getIndirection  root va nbL stop
    s).
    { intros. apply getIndirectionUpdateLLIndex with entry;trivial. }
assert(Hgoal :  exists indirection2 : page,
      getIndirection structroot va nbL stop s = Some indirection2 /\
      (defaultPage =? indirection2) = false). 
{ apply H with partition pdroot indirection1;trivial.
  rewrite <- Hind;trivial. }
destruct Hgoal as (indirection2 & Hind1 & Hindnotnul).
exists indirection2;split;trivial.
rewrite <- Hind1.
apply Hind;trivial.
Qed.

Lemma getTableAddrRootUpdateLLIndex s vaInCurrentPartition table idx entry  idxroot 
ptDescChild descChild currentPart: 
(* table <> currentPart -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
getTableAddrRoot ptDescChild idxroot currentPart descChild  s-> 
getTableAddrRoot ptDescChild idxroot currentPart descChild
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s)
              beqPage beqIndex |}.
Proof.
intros  Hlookup.
unfold getTableAddrRoot.
intros Hcond.
destruct Hcond as(Hi & Hcond).
split;trivial.
intros. 
assert(Hpp : nextEntryIsPP currentPart idxroot tableroot s ). 
rewrite nextEntryIsPPUpdateLLIndex with entry;trivial.
eassumption.
trivial.
trivial.
apply Hcond in Hpp.
destruct Hpp as (nbL & HnbL & stop & Hstop & Hind). 
exists nbL. 
split;trivial.
exists stop.
split;trivial. 
rewrite <- Hind.
apply getIndirectionUpdateLLIndex with entry;trivial.
Qed.

Lemma getAncestorsUpdateLLIndex s x table idx entry partition: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
(* table <> partition ->
~ In table  (getAncestors partition s) -> *)
getAncestors partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I x) (memory s)
              beqPage beqIndex |} =
                      getAncestors partition s.
Proof. 
intros Hlookup.
unfold getAncestors.
simpl.
revert partition. 
induction (nbPage + 1);trivial.
simpl;intros.
assert(Hparent : getParent partition
    (add table idx (I x) (memory s) beqPage
       beqIndex) = getParent partition (memory s)).
{  apply getParentUpdateLLIndex with entry;trivial.
}
rewrite Hparent.
destruct (getParent partition (memory s) );trivial.
f_equal.
simpl in *.
intuition.
Qed.

Lemma noCycleInPartitionTreeUpdateLLIndex s vaInCurrentPartition table idx entry : 
(* ~ In table (getPartitions multiplexer s) -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
parentInPartitionList s ->
isChild s ->
noCycleInPartitionTree s -> 
noCycleInPartitionTree
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
(* intros Hkey. *)
intros Hlookup.
unfold noCycleInPartitionTree.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hancestor :getAncestors partition
          {|
          currentPartition := currentPartition s;
          memory := add table idx (I  vaInCurrentPartition) (memory s)
                      beqPage beqIndex |} =
                      getAncestors partition s).
apply getAncestorsUpdateLLIndex with entry;trivial.
(* contradict Hkey;subst;trivial.
contradict Hkey.
apply ancestorInPartitionTree with partition;trivial. *)
rewrite Hancestor in *.
apply H1;trivial.
Qed.

Lemma configTablesAreDifferentUpdateLLIndex s vaInCurrentPartition table idx entry :
(* StateLib.getMaxIndex <> Some idx -> 
~ In table (getPartitions multiplexer s) -> *)
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
configTablesAreDifferent s -> 
configTablesAreDifferent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
(* intro Hkey2.
intro Hkey.
 *) intros Hlookup.
unfold configTablesAreDifferent.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hconfig : forall part, getConfigPages part {|
          currentPartition := currentPartition s;
          memory := add table idx (I  vaInCurrentPartition) (memory s)
                      beqPage beqIndex |} = getConfigPages part s).
{ intros.
apply getConfigPagesUpdateLLIndex with entry;trivial. } 
rewrite Hconfig in *;trivial. 
rewrite Hconfig in *;trivial.
clear Hconfig.
apply H;trivial.
Qed.

Lemma isChildUpdateLLIndex s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
parentInPartitionList s ->
isChild s -> 
isChild
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
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
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hparent : getParent partition
    (add table idx (I  vaInCurrentPartition) (memory s) beqPage
       beqIndex) = getParent partition (memory s)).
{ apply getParentUpdateLLIndex with entry;trivial. }
assert(Hchildren : forall part,getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |} = getChildren part s).
{ intros.
symmetry.
apply getChildrenUpdateLLIndex with entry;trivial.
 } 
rewrite Hchildren in *.
clear Hchildren.
rewrite  Hparent in *.
apply H0;trivial.
Qed.

Lemma isPresentNotDefaultIffUpdateLLIndex s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
isPresentNotDefaultIff s -> 
isPresentNotDefaultIff
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold isPresentNotDefaultIff.
intros; 
simpl.
 assert(Hpresent :    StateLib.readPresent table0 idx0
  (memory s) = StateLib.readPresent table0 idx0
    (add table idx (I  vaInCurrentPartition) (memory s) beqPage beqIndex) ).
symmetry.
apply readPresentUpdateLLIndex with entry; trivial.
rewrite <- Hpresent.
 assert(Hread :    StateLib.readPhyEntry table0 idx0
  (memory s) = StateLib.readPhyEntry table0 idx0
    (add table idx (I  vaInCurrentPartition) (memory s) beqPage beqIndex) ).
symmetry.
apply readPhyEntryUpdateLLIndex with entry;trivial.
rewrite <- Hread.
apply H.
Qed.

Lemma getVirtualAddressSh1UpdateLLIndex  s vaInCurrentPartition table idx entry p va: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
getVirtualAddressSh1 p s va  =
getVirtualAddressSh1 p {|
    currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va.
Proof.
intros Hlookup.
unfold getVirtualAddressSh1.
destruct (StateLib.getNbLevel);trivial.
assert(Hind : getIndirection p va l (nbLevel - 1)
{|
currentPartition := currentPartition s;
memory := add table idx  (I  vaInCurrentPartition) (memory s) beqPage
            beqIndex |} = getIndirection  p va l  (nbLevel - 1)
s).
{ apply getIndirectionUpdateLLIndex with entry;trivial. }
rewrite Hind.
case_eq (getIndirection  p va l  (nbLevel - 1) s );
[ intros tbl Htbl | intros Htbl]; trivial.
case_eq (defaultPage =? tbl);trivial.
intros Htblnotnul.
simpl.
symmetry.
apply readVirEntryUpdateLLIndex with entry;trivial.
Qed.

Lemma getVirtualAddressSh2UpdateLLIndex  s vaInCurrentPartition table idx entry p va: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
getVirtualAddressSh2 p s va  =
getVirtualAddressSh2 p {|
    currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va.
Proof.
intros Hlookup.
unfold getVirtualAddressSh2.
destruct (StateLib.getNbLevel);trivial.
assert(Hind : getIndirection p va l (nbLevel - 1)
{|
currentPartition := currentPartition s;
memory := add table idx  (I  vaInCurrentPartition) (memory s) beqPage
            beqIndex |} = getIndirection  p va l  (nbLevel - 1)
s).
{ apply getIndirectionUpdateLLIndex with entry;trivial. }
rewrite Hind.
case_eq (getIndirection  p va l  (nbLevel - 1) s );
[ intros tbl Htbl | intros Htbl]; trivial.
case_eq (defaultPage =? tbl);trivial.
intros Htblnotnul.
simpl.
symmetry.
apply readVirtualUpdateLLIndex with entry ;trivial.
Qed.

Lemma isDerivedUpdateLLIndex  s vaInCurrentPartition table idx entry parent va: 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
isDerived parent va s ->  isDerived parent va  {|
       currentPartition := currentPartition s;
       memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                   beqIndex |}
       . 
Proof.
(* intros Hkey Hpart. *)
intros Hlookup.
unfold isDerived.
simpl.
assert(Hsh1 :  StateLib.getFstShadow parent (memory s) =
StateLib.getFstShadow parent
    (add table idx (I  vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry. apply getFstShadowUpdateLLIndex with entry;trivial.
  }
rewrite <- Hsh1 in *.
destruct (getFstShadow parent (memory s));trivial.
assert(Hgetvir1 : getVirtualAddressSh1 p s va  =
getVirtualAddressSh1 p {|
    currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va ).
apply getVirtualAddressSh1UpdateLLIndex with entry;trivial.
rewrite <- Hgetvir1;trivial.
Qed.
 
Lemma physicalPageNotDerivedUpdateLLIndex s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
noDupPartitionTree s ->
physicalPageNotDerived s -> 
physicalPageNotDerived
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
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
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hchildren : forall part,  getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |} = getChildren part s).
{ intros.
symmetry.
apply getChildrenUpdateLLIndex with entry;trivial. } 
rewrite Hchildren in *.
clear Hchildren.
assert(Hpd : forall partition,  StateLib.getPd partition
       (add table idx (I  vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros.
 apply getPdUpdateLLIndex with entry;trivial. }
rewrite Hpd in *. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateLLIndex with entry;trivial. }
rewrite Hmap in *. clear Hmap.
assert(~ isDerived parent va s ). 
unfold not;intros. 
contradict H3.
apply isDerivedUpdateLLIndex with entry;trivial.
apply H0 with  parent va pdParent
child pdChild vaInChild;trivial.
Qed.

Lemma multiplexerWithoutParentUpdateLLIndex s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
multiplexerWithoutParent s -> 
multiplexerWithoutParent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold multiplexerWithoutParent.
intros; 
simpl.

assert(Hparent : getParent multiplexer
    (add table idx (I  vaInCurrentPartition) (memory s) beqPage
       beqIndex) = getParent multiplexer (memory s)).
{ apply getParentUpdateLLIndex with entry;trivial.
   }
rewrite Hparent in *.
trivial.
Qed.

Lemma isParentUpdateLLIndex s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
noDupPartitionTree s ->
isParent s -> 
isParent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold isParent.
intros.
simpl in *. 
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hchildren : forall part,  getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |} = getChildren part s).
{ intros.
symmetry.
apply getChildrenUpdateLLIndex with entry;trivial. } 
rewrite Hchildren in *;trivial.
assert(Hparent : getParent partition
    (add table idx (I  vaInCurrentPartition) (memory s) beqPage
       beqIndex) = getParent partition (memory s)).
{ apply getParentUpdateLLIndex with entry;trivial. }
rewrite Hparent in *;trivial.
apply H0; trivial.
Qed.

Lemma noDupPartitionTreeUpdateLLIndex s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
noDupPartitionTree s -> 
noDupPartitionTree
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
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
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
Qed.
 
Lemma wellFormedFstShadowUpdateLLIndex s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
wellFormedFstShadow s -> 
wellFormedFstShadow
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
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
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, StateLib.getPd partition
       (add table idx (I  vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros. apply getPdUpdateLLIndex with entry;trivial.  }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateLLIndex with entry;trivial. }
rewrite Hmap in *;trivial. clear Hmap.
assert(Hsh1 :  forall partition,  StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (I  vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry. apply getFstShadowUpdateLLIndex with entry;trivial.  }
rewrite <- Hsh1 in *;trivial. clear Hsh1.
assert(Hgetvir1 : getVirtualAddressSh1 sh1 s va  =
getVirtualAddressSh1 sh1 {|
    currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va ).
apply getVirtualAddressSh1UpdateLLIndex with entry;trivial.
rewrite <- Hgetvir1;trivial.
apply H with partition pg pd;trivial.
Qed.

Lemma wellFormedSndShadowUpdateLLIndex s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
wellFormedSndShadow s -> 
wellFormedSndShadow
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold wellFormedSndShadow.
intros.
simpl in *.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition,  StateLib.getPd partition
       (add table idx (I  vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros. apply getPdUpdateLLIndex with entry;trivial.  }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateLLIndex with entry;trivial. }
rewrite Hmap in *;trivial. clear Hmap.
assert(Hsh1 :  forall partition,  StateLib.getSndShadow partition (memory s) =
StateLib.getSndShadow partition
    (add table idx (I  vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry. apply getSndShadowUpdateLLIndex with entry;trivial.  }
rewrite <- Hsh1 in *;trivial. clear Hsh1.
assert(Hgetvir1 : getVirtualAddressSh2 sh2 s va  =
getVirtualAddressSh2 sh2 {|
    currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va ).
apply getVirtualAddressSh2UpdateLLIndex with entry;trivial.
rewrite <- Hgetvir1;trivial.
apply H with partition pg pd;trivial.
Qed.


Lemma wellFormedFstShadowIfNoneUpdateLLIndex s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
wellFormedFstShadowIfNone s -> 
wellFormedFstShadowIfNone
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
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
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, StateLib.getPd partition
       (add table idx (I  vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros. apply getPdUpdateLLIndex with entry;trivial.  }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateLLIndex with entry;trivial. }
rewrite Hmap in *;trivial. clear Hmap.
assert(Hsh1 : forall partition,  StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (I  vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry. apply getFstShadowUpdateLLIndex with entry;trivial.  }
rewrite <- Hsh1 in *;trivial. clear Hsh1.
assert(Hgetvir1 : getPDFlag sh1 va s  =
getPDFlag sh1 va {|
    currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                beqIndex |} ).
symmetry.
apply getPDFlagUpdateLLIndex with entry;trivial.
rewrite <- Hgetvir1;trivial.
assert(Hgetvir2 : getVirtualAddressSh1 sh1 s va =
getVirtualAddressSh1 sh1 {|
    currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va).
apply getVirtualAddressSh1UpdateLLIndex with entry;trivial.
rewrite <- Hgetvir2.
apply H with partition pd;trivial.
Qed.

Lemma wellFormedFstShadowIfDefaultValuesUpdateLLIndex s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
wellFormedFstShadowIfDefaultValues s -> 
wellFormedFstShadowIfDefaultValues
  {|
  currentPartition := currentPartition s;
  memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
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
     memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition,  StateLib.getPd partition
       (add table idx (I  vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros.
  apply getPdUpdateLLIndex with entry;trivial.  }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateLLIndex with entry;trivial. }
rewrite Hmap in *;trivial. clear Hmap.
assert(Hsh1 : forall partition, StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (I  vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry. apply getFstShadowUpdateLLIndex with entry;trivial.  }
rewrite <- Hsh1 in *;trivial. clear Hsh1.
assert(Hgetvir1 : getPDFlag sh1 va s  =
getPDFlag sh1 va {|
    currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                beqIndex |} ).
symmetry.
apply getPDFlagUpdateLLIndex with entry;trivial.
rewrite <- Hgetvir1;trivial.
assert(Hgetvir2 : getVirtualAddressSh1 sh1 s va =
getVirtualAddressSh1 sh1 {|
    currentPartition := currentPartition s;
    memory := add table idx (I  vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va).
apply getVirtualAddressSh1UpdateLLIndex with entry;trivial.
rewrite <- Hgetvir2.
apply H with partition pd;trivial.
Qed.

Lemma isAccessibleMappedPageInParentUpdateSh2 s entry v table idx parent va pg:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) -> 

isAccessibleMappedPageInParent parent va pg  s =
isAccessibleMappedPageInParent parent va pg
   {|
  currentPartition := currentPartition s;
  memory := add table idx (I v) (memory s) beqPage beqIndex |}. 
Proof.
set(s':= {| currentPartition := _ |}).
intros.
unfold isAccessibleMappedPageInParent.
assert(Hsh2s:getSndShadow parent (memory s) =
getSndShadow parent (memory s')).
{ unfold s';simpl;symmetry;
   apply getSndShadowUpdateLLIndex with entry;trivial. }
rewrite <- Hsh2s. 
case_eq(getSndShadow parent (memory s)); [intros sh2 Hsh2|];trivial.
assert(Hgetvir2:  getVirtualAddressSh2 sh2 s va =  getVirtualAddressSh2 sh2 s' va ).
apply getVirtualAddressSh2UpdateLLIndex with entry;trivial.
rewrite <- Hgetvir2.
case_eq(getVirtualAddressSh2 sh2 s va);[intros vaInParent HvaInParent |];trivial.
assert(Hparents:getParent parent (memory s) =
getParent parent (memory s')).
{ unfold s';simpl;symmetry;
   apply getParentUpdateLLIndex with entry;trivial. }
rewrite <- Hparents.
case_eq(   getParent parent (memory s));[intros ancestor Hancestor|];trivial.
assert(Hancestors:StateLib.getPd ancestor (memory s) =
StateLib.getPd ancestor (memory s')).
{ unfold s';simpl;symmetry;
   apply getPdUpdateLLIndex with entry;trivial. }
rewrite <- Hancestors.
case_eq(  StateLib.getPd ancestor (memory s));[intros pd Hpds|];trivial.

assert(Haccess:getAccessibleMappedPage pd s vaInParent =
getAccessibleMappedPage pd s' vaInParent).
{ unfold s';simpl;symmetry;
   apply getAccessibleMappedPageUpdateLLIndex with entry;trivial. }
rewrite <- Haccess;trivial.
Qed.

Lemma accessibleChildPageIsAccessibleIntoParentUpdateSh2 s entry v table nextFFI:
lookup table nextFFI  (memory s) beqPage beqIndex = Some (I entry) ->
parentInPartitionList s ->
isChild s ->
accessibleChildPageIsAccessibleIntoParent s ->
accessibleChildPageIsAccessibleIntoParent
   {|
  currentPartition := currentPartition s;
  memory := add table nextFFI (I v) (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup (* Hkey *).
set(s':= {| currentPartition := _ |}).
unfold accessibleChildPageIsAccessibleIntoParent.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer s').
apply getPartitionsUpdateLLIndex with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Haccessmap : forall part, getAccessibleMappedPage part s' va =
getAccessibleMappedPage part s va).
{ intros. apply getAccessibleMappedPageUpdateLLIndex with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
assert(Hpd :  StateLib.getPd partition (memory s) =
StateLib.getPd partition
   (add table nextFFI (I v) (memory s) beqPage beqIndex)).
{ symmetry.  apply getPdUpdateLLIndex with entry;trivial.
 }
rewrite <- Hpd in *.
rewrite <- H1 with  partition va pd accessiblePage;trivial.
symmetry.
apply isAccessibleMappedPageInParentUpdateSh2 with entry;trivial.
Qed.

Lemma consistencyUpdateLLIndex newLastLLable nextFFI v entry s:
(* StateLib.getMaxIndex <> Some nextFFI ->  *)
lookup newLastLLable nextFFI (memory s) beqPage beqIndex = Some (I entry)->
(* ~ In newLastLLable (getPartitions multiplexer s) -> *)
consistency s -> consistency {|
  currentPartition := currentPartition s;
  memory := add newLastLLable nextFFI (I v) (memory s) beqPage beqIndex |}.
Proof.
intros  Hlookup.
unfold consistency;intuition.
+ apply partitionDescriptorEntryUpdateLLIndex with entry;trivial.
+ apply dataStructurePdSh1Sh2asRootUpdateLLIndex with entry;trivial.
+ apply dataStructurePdSh1Sh2asRootUpdateLLIndex with entry;trivial.
+ apply dataStructurePdSh1Sh2asRootUpdateLLIndex with entry;trivial.
+ apply currentPartitionInPartitionsListUpdateLLIndex with entry;trivial.
+ apply noDupMappedPagesListUpdateLLIndex with entry;trivial.
+ apply noDupConfigPagesListUpdateLLIndex with entry;trivial.
+ apply parentInPartitionListUpdateLLIndex with entry;trivial.
+ apply accessibleVAIsNotPartitionDescriptorUpdateLLIndex with entry;trivial.
+ apply accessibleChildPageIsAccessibleIntoParentUpdateSh2 with entry;trivial.
+ apply noCycleInPartitionTreeUpdateLLIndex with entry;trivial.
+ apply configTablesAreDifferentUpdateLLIndex with entry;trivial.
+ apply isChildUpdateLLIndex with entry;trivial.
+ apply isPresentNotDefaultIffUpdateLLIndex with entry;trivial.
+ apply physicalPageNotDerivedUpdateLLIndex with entry;trivial.
+ apply multiplexerWithoutParentUpdateLLIndex with entry;trivial.
+ apply isParentUpdateLLIndex with entry;trivial.
+ apply noDupPartitionTreeUpdateLLIndex with entry;trivial.
+ apply wellFormedFstShadowUpdateLLIndex with entry;trivial.
+ apply wellFormedSndShadowUpdateLLIndex with entry;trivial.
+ apply wellFormedShadowsUpdateLLIndex with entry;trivial.
+ apply wellFormedShadowsUpdateLLIndex with entry;trivial.
+ apply wellFormedFstShadowIfNoneUpdateLLIndex with entry;trivial.
+ apply wellFormedFstShadowIfDefaultValuesUpdateLLIndex with entry;trivial.
Qed.

Lemma isEntryVAExistsUpdateLLIndex idx ptVaInCurPart table idxvaInCurPart entry s   x:
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->
(exists va : vaddr,
       isEntryVA ptVaInCurPart idxvaInCurPart va s/\
        beqVAddr defaultVAddr va = false)
 -> exists va : vaddr,
isEntryVA ptVaInCurPart idxvaInCurPart va 
  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}/\
        beqVAddr defaultVAddr va = false.
Proof.
intros Hentry.
cbn.
intros.
destruct H as (va & Hva & Hx).
exists va;split;trivial.
apply isEntryVAUpdateLLIndex with entry;trivial.
Qed.

Lemma indirectionDescriptionUpdateLLIndex    l descChildphy x idx table entry
phyPDChild vaToPrepare  idxroot s:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |} in 
lookup table idx (memory s) beqPage beqIndex = Some (I entry) ->

indirectionDescription s descChildphy phyPDChild idxroot vaToPrepare l -> 
indirectionDescription s' descChildphy phyPDChild idxroot vaToPrepare l.
Proof.
intros s' Hlookup  (* Hkey *) Hind.
unfold indirectionDescription in *.
destruct Hind as (tableroot & Hpp & Hnotdef & Hor).
exists tableroot.
split;trivial.
unfold s'.

rewrite <- nextEntryIsPPUpdateLLIndex;trivial.
 eassumption.
split;trivial.
destruct Hor as  [(Hroot & Hl) |(nbL & stop& HnbL & Hstop & Hind & Hnotdefind & Hl)].
left;split;trivial.
right.
exists nbL, stop.
intuition.
rewrite <- Hind.
apply getIndirectionUpdateLLIndex with entry;trivial. 
Qed.

Lemma initPEntryTablePreconditionToPropagatePreparePropertiesUpdateLLIndex pg
 table idx x v0 s:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |} in 
(* StateLib.getMaxIndex <> Some idx -> *)             
lookup table idx (memory s) beqPage beqIndex = Some (I v0) ->
(* ~ In table (getPartitions multiplexer s) -> *)
initPEntryTablePreconditionToPropagatePrepareProperties s pg ->
(* isPartitionFalse ptSh1 (StateLib.getIndexOfAddr vaValue fstLevel)  s ->  *)
initPEntryTablePreconditionToPropagatePrepareProperties s' pg.
Proof.
intros s' (* Hkey2 *) Hlookup (*   *)(* Hnotpart *) (Hgoal & Hnotdef).
unfold initPEntryTablePreconditionToPropagatePrepareProperties.
split;trivial.
intros part Hpart.
assert(Hpartitions: getPartitions multiplexer s' = getPartitions multiplexer s). (* *)
symmetry. apply getPartitionsUpdateLLIndex with v0;trivial.
rewrite Hpartitions in *.
assert(Hconf: getConfigPages part s'= getConfigPages part s).
apply getConfigPagesUpdateLLIndex with v0;trivial.
rewrite Hconf.
apply Hgoal;trivial.
Qed.

Lemma writeAccessibleRecPreparePostconditionUpdateLLIndex desc  pg
 table idx x v0 s:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |} in 
lookup table idx (memory s) beqPage beqIndex = Some (I v0) ->
(* ~ In table (getAncestors desc s) ->
table <> desc -> *)
(* initPEntryTablePreconditionToPropagatePrepareProperties s pg ->  *)         
writeAccessibleRecPreparePostcondition desc pg s ->
writeAccessibleRecPreparePostcondition desc pg s'.
Proof.
intros s' Hlookup (* Hnotpart Hnot  *)Hgoal .
unfold writeAccessibleRecPreparePostcondition in *.
intros part Hpart.
assert(Hances: getAncestors desc s' = getAncestors desc s).
apply getAncestorsUpdateLLIndex with v0;trivial.
rewrite Hances in *;trivial.
assert(Haccess: getAccessibleMappedPages part s' = getAccessibleMappedPages part s). (* *)
 apply getAccessibleMappedPagesUpdateLLIndex with v0;trivial.
rewrite Haccess.
apply Hgoal;trivial.
Qed.

Lemma isWellFormedMMUTablesUpdateLLIndex pg
 table idx x v0 s:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |} in 
lookup table idx (memory s) beqPage beqIndex = Some (I v0) ->
isWellFormedMMUTables pg s -> isWellFormedMMUTables pg s'.
Proof.
intros s' Hlookup Hgoal.
unfold isWellFormedMMUTables in *.
intros.
generalize (Hgoal idx0);clear Hgoal; intros (Hphy & Hpres).
split.
rewrite <- Hphy.
apply readPhyEntryUpdateLLIndex with v0;trivial.
rewrite <- Hpres.
apply readPresentUpdateLLIndex with v0;trivial.
Qed.

Lemma isWellFormedFstShadowTablesUpdateLLIndex  (* pt idx vaValue v0  partition  *)s nbL phySh1addr x table idx v0:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |} in 
lookup table idx (memory s) beqPage beqIndex = Some (I v0) ->
(*initPEntryTablePreconditionToPropagatePrepareProperties s phySh1addr -> 
In partition (getPartitions multiplexer s) -> 
In pt (getConfigPages partition s) ->   *)
isWellFormedFstShadow nbL phySh1addr s-> isWellFormedFstShadow nbL phySh1addr s'.
Proof.
intros s' Hlookup (* (Hnotconfig&Hnotnull) Hpart Hconfig  *)Hgoal.
unfold isWellFormedFstShadow in *.
destruct Hgoal as [(Hl & Hgoal) |(Hl & Hgoal)];[left|right];split;trivial;intros idx0;
generalize (Hgoal idx0);clear Hgoal; intros (Hphy & Hpres);
rewrite <- Hpres;rewrite<-  Hphy;split.
apply readPhyEntryUpdateLLIndex with v0;trivial.
apply readPresentUpdateLLIndex with v0;trivial.
apply readVirEntryUpdateLLIndex with v0;trivial.
apply readPDflagUpdateLLIndex with v0;trivial.
Qed.

Lemma isWellFormedSndShadowTablesUpdateLLIndex s pg idx  v0 l table  x:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |} in 
lookup table idx (memory s) beqPage beqIndex = Some (I v0) ->
isWellFormedSndShadow l pg s -> isWellFormedSndShadow l pg s'.
Proof.
intros s' Hlookup Hgoal.
unfold isWellFormedSndShadow in *.
intros.
destruct Hgoal as [(Hl & Hgoal) |(Hl & Hgoal)];[left|right];split;trivial;intros idx0;
generalize (Hgoal idx0);clear Hgoal;[ intros (Hphy & Hpres)| intros Hphy];
rewrite <- Hphy;[rewrite<-  Hpres;split|].
apply readPhyEntryUpdateLLIndex with v0;trivial.
apply readPresentUpdateLLIndex with v0;trivial.
apply readVirtualUpdateLLIndex with v0;trivial.
Qed.



Lemma insertEntryIntoLLPCUpdateLLIndex s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable
      phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
      descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA
      zeroI lpred newLastLLable  (* (LLDescChild:page) *) entry fstLL LLChildphy  newFFI (minFI minFI' idx:index):
lookup newLastLLable idx (memory s) beqPage beqIndex = Some (I entry) ->
(* StateLib.getMaxIndex <> Some nextFFI ->   *)
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable
      phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
      descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA
      zeroI lpred fstLL LLChildphy newLastLLable minFI->
(exists NbFI : index, isIndexValue newLastLLable (CIndex 1) NbFI {|
  currentPartition := currentPartition s;
  memory := add newLastLLable idx (I newFFI) (memory s) beqPage beqIndex |} /\ NbFI >= minFI') ->
insertEntryIntoLLPC {|
  currentPartition := currentPartition s;
  memory := add newLastLLable idx (I newFFI) (memory s) beqPage beqIndex |} ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable
      phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
      descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA
      zeroI lpred fstLL LLChildphy newLastLLable minFI'.
Proof.
intros Hlookup (* Hkey2 *).
intros.
set(s':=  {|
     currentPartition := _|}).
assert (HtableinLL: In newLastLLable (getLLPages fstLL s (nbPage + 1))).
unfold insertEntryIntoLLPC, propagatedPropertiesPrepare in *;intuition.
assert(HLL: getConfigTablesLinkedList descChildphy (memory s) = Some fstLL).
unfold insertEntryIntoLLPC, propagatedPropertiesPrepare in *;intuition.
assert(Hchildpart:In descChildphy (getPartitions multiplexer s)) by (unfold insertEntryIntoLLPC, 
                        propagatedPropertiesPrepare in *;intuition).
assert(Htableinconfig: In newLastLLable (getConfigPages descChildphy s)).
{ apply inGetTrdShadowInConfigPages with fstLL;trivial.
    unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, consistency in *;intuition. }
assert(Htablenotpart : ~ In newLastLLable (getPartitions multiplexer s)).
{  apply LLtableNotPartition with descChildphy fstLL;trivial;
unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, consistency in *;intuition. }
assert(Hpartitions : getPartitions multiplexer s = getPartitions multiplexer s') by (
    apply getPartitionsUpdateLLIndex with entry; trivial).
assert(Hnotanc: ~ In newLastLLable (getAncestors (currentPartition s) s)). 
{ contradict Htablenotpart.
  apply ancestorInPartitionTree with (currentPartition s);trivial;unfold insertEntryIntoLLPC, 
  propagatedPropertiesPrepare, consistency in *;intuition. }
assert(Hcurpart: In (currentPartition s) (getPartitions multiplexer s)) by
(unfold insertEntryIntoLLPC, 
  propagatedPropertiesPrepare, consistency in *;intuition).
assert(Hnotcurpart: newLastLLable <> currentPartition s) by 
 (contradict Htablenotpart;subst;trivial).
assert(Hnotpartchild: newLastLLable <> descChildphy) by
 (contradict Htablenotpart;subst;trivial).
unfold insertEntryIntoLLPC, propagatedPropertiesPrepare in *;intuition;subst;simpl.
+ apply kernelDataIsolationUpdateLLIndex with entry ;trivial.
+ apply partitionsIsolationUpdateLLIndex with entry;trivial; unfold consistency in *;intuition.
+ apply verticalSharingUpdateLLIndex with entry ;trivial; unfold consistency in *;intuition.
+ apply consistencyUpdateLLIndex with entry;trivial.
+ apply getTableAddrRootUpdateLLIndex with entry;trivial.
+ apply isPEUpdateLLIndex with entry;trivial.
+ apply isEntryVAExistsUpdateLLIndex with entry;trivial.
+ apply getTableAddrRootUpdateLLIndex with entry;trivial.
+ apply isVEUpdateLLIndex   with entry;trivial.
+ apply isEntryPageUpdateLLIndex with entry;trivial.
+ apply entryPresentFlagUpdateLLIndex with entry;trivial.
+ apply entryUserFlagUpdateLLIndex with entry;trivial.
+ apply getTableAddrRootUpdateLLIndex with entry;trivial.
+ apply isPEUpdateLLIndex with entry;trivial.
+ apply isEntryVAExistsUpdateLLIndex with entry;trivial.
+ apply getTableAddrRootUpdateLLIndex with entry;trivial.
+ apply isVEUpdateLLIndex   with entry;trivial.
+ apply isEntryVAExistsUpdateLLIndex with entry;trivial.
+ apply getTableAddrRootUpdateLLIndex with entry;trivial.
+ apply isVEUpdateLLIndex   with entry;trivial.
+ apply isEntryPageUpdateLLIndex with entry;trivial.
+ apply entryPresentFlagUpdateLLIndex with entry;trivial.
+ apply entryUserFlagUpdateLLIndex with entry;trivial.
+ apply getTableAddrRootUpdateLLIndex with entry;trivial.
+ apply isPEUpdateLLIndex with entry;trivial.
+ apply entryUserFlagUpdateLLIndex with entry;trivial.
+ apply entryPresentFlagUpdateLLIndex with entry;trivial.
+ apply isEntryPageUpdateLLIndex with entry;trivial.
+ apply isEntryPageUpdateLLIndex with entry;trivial.
+ unfold s'. rewrite <- nextEntryIsPPUpdateLLIndex with entry;trivial.
+ unfold s'. rewrite <- nextEntryIsPPUpdateLLIndex with entry;trivial.
+ unfold s'. rewrite <- nextEntryIsPPUpdateLLIndex with entry;trivial.
+ rewrite <- Hpartitions ;trivial.
+ unfold indirectionDescriptionAll in *;intuition;
  apply indirectionDescriptionUpdateLLIndex with entry;trivial.
+ unfold initPEntryTablePreconditionToPropagatePreparePropertiesAll in *;
  intuition; apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateLLIndex
  with entry;trivial.
+  assert(Hconf: getConfigTablesLinkedList descChildphy (memory s) = Some fstLL) by trivial.
  rewrite <- Hconf.
   apply getConfigTablesLinkedListUpdateLLIndex with entry;trivial.
+ assert(Hconf: getLLPages fstLL s (nbPage + 1) = getLLPages fstLL s' (nbPage + 1)).
  symmetry.
  apply getLLPagesUpdateLLIndex with entry;trivial.
  rewrite <- Hconf;trivial.
+ assert(Hconf: getLLPages fstLL s (nbPage + 1) = getLLPages fstLL s' (nbPage + 1)).
  symmetry.
  apply getLLPagesUpdateLLIndex with entry;trivial.
  rewrite <- Hconf;trivial.
(* + assert(exists NbFI : index, isIndexValue newLastLLable (CIndex 1) NbFI s /\ NbFI >= minFI) as (nbFI & Hnbfi & Hnbfi1) by trivial.
assert(idx=(CIndex 1) \/ idx<>(CIndex 1)) as [Hor|Hor] by admit.
subst.
* 
  exists nbFI.
  
  split;trivial.
  apply isIndexValueSameUpdateLLIndex.
  admit. (** newFFI >= minFI **)
  exists nbFI.
  split;trivial.
  apply isIndexValueUpdateLLIndex;trivial.
  right.
  intuition. *)
+ unfold writeAccessibleRecPreparePostconditionAll in *;intuition;
  apply writeAccessibleRecPreparePostconditionUpdateLLIndex with entry;trivial.
+ unfold isWellFormedTables in *; intuition.
  apply isWellFormedMMUTablesUpdateLLIndex with entry;trivial.
  apply isWellFormedFstShadowTablesUpdateLLIndex with entry;trivial.
  apply isWellFormedSndShadowTablesUpdateLLIndex with entry;trivial.
+ apply isEntryVAUpdateLLIndex with entry;trivial.
+ apply isEntryVAUpdateLLIndex with entry;trivial.
+ apply isEntryVAUpdateLLIndex with entry;trivial.  
Qed.

Lemma isPP'SameValueUpdateLLIndex  newLastLLable nextFFI phyMMUaddr s:
isPP' newLastLLable nextFFI phyMMUaddr
  {|
  currentPartition := currentPartition s;
  memory := add newLastLLable nextFFI (PP phyMMUaddr) (memory s) beqPage beqIndex |}.
Proof.
unfold isPP'.
simpl.
assert(Hbeqtrue:beqPairs (newLastLLable, nextFFI) (newLastLLable, nextFFI) beqPage beqIndex=true)by 
 (apply beqPairsTrue;split;trivial).
rewrite Hbeqtrue;trivial.
Qed.
 