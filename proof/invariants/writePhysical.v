(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2021)                *)
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
Require Import Coq.Logic.ProofIrrelevance Lia List Bool Logic.Classical_Prop Compare_dec.

(***************** To move ************************)
(*%%%%%%%%%%%%Consistency%%%%%%%%%%%*)

(*%%%%%%%%%%%%%%%% PropagatedProperties %%%%%%%%%%%%%%%%%%*)
(*%%%%%%%%%%%%%%%% InternalLemmas %%%%%%%%%%%%%%%%%%*)
Lemma inGetTrdShadowInConfigPagesAux partition LL table s:
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
In table (getLLPages LL s (nbPage + 1)) ->
StateLib.getConfigTablesLinkedList partition (memory s) = Some LL  ->
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
In partition (getPartitions pageRootPartition s) ->
In table (getLLPages LL s (nbPage + 1)) ->
StateLib.getConfigTablesLinkedList partition (memory s) = Some LL  ->
In table (getConfigPages  partition s).
Proof.
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPages.
simpl;right.
apply inGetTrdShadowInConfigPagesAux with LL;trivial.
Qed.
Lemma LLtableNotPartition s LLtable partition LLroot :
In LLtable (getLLPages LLroot s (nbPage + 1))->
StateLib.getConfigTablesLinkedList partition (memory s) = Some LLroot ->
In partition (getPartitions pageRootPartition s) ->
In LLtable (getConfigPages partition s) ->
configTablesAreDifferent s ->
noDupConfigPagesList s -> 
noDupPartitionTree s ->
partitionDescriptorEntry s ->
~ In LLtable (getPartitions pageRootPartition s).
Proof.
intros Htrd HLL Hpart Hisconfig Hconfigdiff Hconfignodup Hnoduptree Hpde.
unfold getPartitions.
assert(Hmult : In pageRootPartition (getPartitions pageRootPartition s)) by (unfold getPartitions;
destruct nbPage;simpl;left;trivial).
revert Hmult.
generalize pageRootPartition at 1 3.
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

Lemma getConfigTablesLinkedListUpdateLLCouplePPVA partition x table idx (s : state) entry :
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
partition<>table ->
StateLib.getConfigTablesLinkedList partition
  (add table idx (PP x) (memory s) pageEq idxEq) =
StateLib.getConfigTablesLinkedList partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getConfigTablesLinkedList.
case_eq ( StateLib.Index.succ idxShadow3 ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
assert(Hfalse : beqPairs (table, idx) (partition, i) pageEq idxEq = false).
apply beqPairsFalse; intuition.
rewrite Hfalse.
assert(Hmemory : lookup partition i (removeDup table idx (memory s) pageEq idxEq) 
          pageEq idxEq =  lookup  partition i (memory s) pageEq idxEq ).
apply removeDupIdentity ; intuition.
rewrite Hmemory.
trivial.
Qed.


Lemma getFstShadowUpdateLLCouplePPVA partition x
table idx (s : state) entry :
partition<>table ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
StateLib.getFstShadow partition
  (add table idx (PP x) (memory s) pageEq idxEq) =
StateLib.getFstShadow partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getFstShadow.
case_eq ( StateLib.Index.succ idxShadow1 ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
assert(Hfalse : beqPairs (table, idx) (partition, i) pageEq idxEq = false).
apply beqPairsFalse; intuition.
rewrite Hfalse.
assert(Hmemory : lookup partition i (removeDup table idx (memory s) pageEq idxEq) 
          pageEq idxEq =  lookup  partition i (memory s) pageEq idxEq ).
apply removeDupIdentity ; intuition.
rewrite Hmemory.
trivial.
Qed.

Lemma getSndShadowUpdateLLCouplePPVA partition x
table idx (s : state) entry :
partition<>table ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
StateLib.getSndShadow partition
  (add table idx (PP x) (memory s) pageEq idxEq) =
StateLib.getSndShadow partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getSndShadow.
case_eq ( StateLib.Index.succ idxShadow2 ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
assert(Hfalse : beqPairs (table, idx) (partition, i) pageEq idxEq = false).
apply beqPairsFalse; intuition.
rewrite Hfalse.
assert(Hmemory : lookup partition i (removeDup table idx (memory s) pageEq idxEq) 
          pageEq idxEq =  lookup  partition i (memory s) pageEq idxEq ).
apply removeDupIdentity ; intuition.
rewrite Hmemory.
trivial.
Qed.

Lemma getPdUpdateLLCouplePPVA partition x
table idx (s : state) entry :
partition<>table ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
StateLib.getPd partition
  (add table idx (PP x) (memory s) pageEq idxEq) =
StateLib.getPd partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getPd.
case_eq ( StateLib.Index.succ idxPageDir ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
assert(Hfalse : beqPairs (table, idx) (partition, i) pageEq idxEq = false).
apply beqPairsFalse; intuition.
rewrite Hfalse.
assert(Hmemory : lookup partition i (removeDup table idx (memory s) pageEq idxEq) 
          pageEq idxEq =  lookup  partition i (memory s) pageEq idxEq ).
apply removeDupIdentity ; intuition.
rewrite Hmemory.
trivial.
Qed.

Lemma getParentUpdateLLCouplePPVA partition x
table idx (s : state) entry :
partition<>table ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
StateLib.getParent partition
  (add table idx (PP x) (memory s) pageEq idxEq) =
StateLib.getParent partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getParent.
case_eq ( StateLib.Index.succ idxParentDesc ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
assert(Hfalse : beqPairs (table, idx) (partition, i) pageEq idxEq = false).
apply beqPairsFalse; intuition.
rewrite Hfalse.
assert(Hmemory : lookup partition i (removeDup table idx (memory s) pageEq idxEq) 
          pageEq idxEq =  lookup  partition i (memory s) pageEq idxEq ).
apply removeDupIdentity ; intuition.
rewrite Hmemory.
trivial.
Qed.



Lemma getTablePagesUpdateLLCouplePPVA    table idx entry size p (s : state)  x:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) -> 
getTablePages p size
 {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} =
getTablePages p size s.
Proof.
revert p .
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}).
induction size;
intros;  trivial.
simpl.
case_eq(beqPairs (table, idx) (p, CIndex size) pageEq idxEq);intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
  subst.
  rewrite H.
  apply IHsize;trivial.
+ apply beqPairsFalse in Hpairs.
  assert (lookup   p (CIndex size) (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  p (CIndex size) (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. subst.  intuition. }
  rewrite  Hmemory. 
  destruct (lookup p (CIndex size) (memory s) pageEq idxEq); 
  [ |apply IHsize; trivial].
  destruct v; try apply IHsize; trivial.
  apply IHsize with p in H.
  rewrite H.
  reflexivity.
Qed.

Lemma getIndirectionsUpdateLLCouplePPVA  table idx entry pd (s : state) x:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->  
getIndirections pd
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}  =
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
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}= getTablePages pd tableSize s) as Htablepages.
apply getTablePagesUpdateLLCouplePPVA with entry ;trivial.
rewrite Htablepages.
clear Htablepages.
induction (getTablePages pd tableSize s); intros; trivial.
simpl in *.
rewrite IHn. 
f_equal.
apply IHl.
Qed.

Lemma readPhysicalUpdateLLCouplePPVA  idx1
table idx (s : state)  p   x: 
table <> p \/ idx <> idx1 ->
StateLib.readPhysical p idx1
  (add table idx (PP x) (memory s) pageEq idxEq) =
StateLib.readPhysical p idx1 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPhysical.
cbn.
assert(beqPairs (table, idx) (p, idx1) pageEq idxEq= false).
apply beqPairsFalse;trivial.
rewrite H.
assert(Hmemory : lookup p idx1 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup p idx1 (memory s) pageEq idxEq ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.


Lemma getLLPagesUpdateLLCouplePPVA table idx p2 s x :
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} in 
StateLib.getMaxIndex <> Some idx ->            
getLLPages p2 s' (nbPage + 1) = getLLPages p2 s (nbPage + 1).
Proof.
intros.
revert p2.
induction  (nbPage + 1);simpl;trivial.
case_eq( StateLib.getMaxIndex);intros;trivial.
assert(Hreadp: StateLib.readPhysical p2 i (add table idx (PP x) (memory s) pageEq idxEq) =
StateLib.readPhysical p2 i (memory s)).
apply readPhysicalUpdateLLCouplePPVA.
right.
contradict H;subst;trivial.
rewrite Hreadp.
destruct(StateLib.readPhysical p2 i (memory s));trivial.
rewrite <- IHn;trivial.
Qed.

Lemma getConfigPagesUpdateLLCouplePPVA s x table idx entry part: 
part <> table ->
StateLib.getMaxIndex <> Some idx ->  
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
 getConfigPages part {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}  = getConfigPages part s.
Proof.
intros.
unfold getConfigPages. 
f_equal.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s)
              pageEq idxEq |}) in *.
unfold getConfigPagesAux.
assert(Hgetpd: StateLib.getPd part (memory s') = StateLib.getPd part (memory s)).
{ apply getPdUpdateLLCouplePPVA with entry;trivial.   }
rewrite Hgetpd. clear Hgetpd.
case_eq(StateLib.getPd part (memory s));intros; trivial.
assert(Hgetsh1: StateLib.getFstShadow part (memory s') = StateLib.getFstShadow part (memory s)).
{ simpl. apply getFstShadowUpdateLLCouplePPVA with entry;trivial.  }
rewrite Hgetsh1. clear Hgetsh1.
case_eq(StateLib.getFstShadow part (memory s));intros; trivial.
assert(Hgetsh2: StateLib.getSndShadow part (memory s') = StateLib.getSndShadow part (memory s)).
{  apply getSndShadowUpdateLLCouplePPVA with entry;trivial.    }
rewrite Hgetsh2. clear Hgetsh2.
case_eq(StateLib.getSndShadow part (memory s));intros; trivial.
assert(Hgetconfig: StateLib.getConfigTablesLinkedList part (memory s') =
 StateLib.getConfigTablesLinkedList part (memory s)).
{  apply getConfigTablesLinkedListUpdateLLCouplePPVA with entry;trivial.   }
rewrite Hgetconfig. clear Hgetconfig.
case_eq(StateLib.getConfigTablesLinkedList part (memory s));intros; trivial.
simpl.
assert(Hind : forall root, getIndirections root s' = getIndirections root s).
{ intros.  
  apply getIndirectionsUpdateLLCouplePPVA with entry;trivial. }
do 3 rewrite Hind.
do 3 f_equal.
apply getLLPagesUpdateLLCouplePPVA ;trivial.
Qed.

Lemma getIndirectionUpdateLLCouplePPVA sh1 table idx s entry va nbL stop x:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
getIndirection sh1 va nbL stop
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} =
getIndirection sh1 va nbL stop s .
Proof.
intros Hentry.
revert sh1 nbL.
induction  stop.
+ simpl. trivial.
+ simpl. intros. 
  destruct (levelEq nbL levelMin);trivial.
  set (entry0 := (PP x)  ) in *.
  simpl.
  assert ( StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr va nbL)
                  (add table idx entry0 (memory s) pageEq idxEq) = 
           StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr va nbL) (memory s)) as HreadPhyEnt.
  { unfold StateLib.readPhyEntry.
    cbn.  
    case_eq ( beqPairs (table, idx) (sh1, StateLib.getIndexOfAddr va nbL) pageEq idxEq);trivial;intros Hpairs.
    + apply beqPairsTrue in Hpairs.
    
      destruct Hpairs as (Htable & Hidx).  subst.
      rewrite Hentry. 
      cbn. trivial.
    + apply beqPairsFalse in Hpairs.
      assert (lookup sh1 (StateLib.getIndexOfAddr va nbL)
                 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
              lookup sh1 (StateLib.getIndexOfAddr va nbL) (memory s) pageEq idxEq) as Hmemory.
        { apply removeDupIdentity. subst.  intuition. }
      rewrite Hmemory. reflexivity.
   } 
  rewrite HreadPhyEnt.
  destruct (StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr va nbL) (memory s) );trivial.
  destruct (Nat.eqb pageDefault p);trivial.
  destruct ( StateLib.Level.pred nbL );trivial.
Qed.

Lemma readPresentUpdateLLCouplePPVA  idx1
table idx (s : state)  p   entry x: 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) -> 
StateLib.readPresent p idx1
  (add table idx (PP x) (memory s) pageEq idxEq) =
StateLib.readPresent p idx1 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPresent.
cbn.
case_eq( beqPairs (table, idx) (p, idx1) pageEq idxEq); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx1 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup p idx1 (memory s) pageEq idxEq ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readAccessibleUpdateLLCouplePPVA 
table idx (s : state)  p  idx1 entry x: 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) -> 
StateLib.readAccessible p idx1
  (add table idx (PP x) (memory s) pageEq idxEq) =
StateLib.readAccessible p idx1 (memory s).
Proof.
intros Hentry.
unfold StateLib.readAccessible.
cbn.
case_eq( beqPairs (table, idx) (p, idx1) pageEq idxEq); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx1 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup p idx1 (memory s) pageEq idxEq ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readPhyEntryUpdateLLCouplePPVA 
table idx (s : state)  p  idx1 entry x: 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) -> 
StateLib.readPhyEntry p idx1
  (add table idx (PP x) (memory s) pageEq idxEq) =
StateLib.readPhyEntry p idx1 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPhyEntry.
cbn.
case_eq( beqPairs (table, idx) (p, idx1) pageEq idxEq); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx1 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup p idx1 (memory s) pageEq idxEq ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readVirEntryUpdateLLCouplePPVA 
table idx (s : state)  p  idx1 entry x: 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) -> 
StateLib.readVirEntry p idx1
  (add table idx (PP x) (memory s) pageEq idxEq) =
StateLib.readVirEntry p idx1 (memory s).
Proof.
intros Hentry.
unfold StateLib.readVirEntry.
cbn.
case_eq( beqPairs (table, idx) (p, idx1) pageEq idxEq); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx1 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup p idx1 (memory s) pageEq idxEq ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readPDflagUpdateLLCouplePPVA idx1
table idx (s : state)  p   entry x: 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) -> 
StateLib.readPDflag p idx1
    (add table idx (PP x) (memory s) pageEq idxEq) =
   StateLib.readPDflag p idx1 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPDflag.
cbn.
case_eq( beqPairs (table, idx) (p, idx1) pageEq idxEq); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx1 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup p idx1 (memory s) pageEq idxEq ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma getMappedPageUpdateLLCouplePPVA root s x table idx va entry:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
getMappedPage root {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}  va = getMappedPage root s va.
Proof.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) pageEq
              idxEq |}) in *.
intros Hentry. 
unfold getMappedPage.
destruct(StateLib.getNbLevel);intros;trivial.
assert(Hind : getIndirection root va l (nbLevel - 1) s' =
getIndirection root va l (nbLevel - 1) s).
apply getIndirectionUpdateLLCouplePPVA with entry;trivial.
rewrite Hind.  
destruct(getIndirection root va l (nbLevel - 1)  s); intros; trivial.
destruct(Nat.eqb pageDefault p);trivial.
 assert(Hpresent :    StateLib.readPresent p (StateLib.getIndexOfAddr va levelMin)
  (memory s) = StateLib.readPresent p (StateLib.getIndexOfAddr va levelMin)
    (add table idx (PP x) (memory s) pageEq idxEq) ).
symmetry.
apply readPresentUpdateLLCouplePPVA with entry; trivial.
unfold s'. simpl.
rewrite <- Hpresent.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va levelMin) (memory s) ); trivial.
destruct b; trivial.
assert(Heq :StateLib.readPhyEntry p (StateLib.getIndexOfAddr va levelMin)
    (add table idx (PP x) (memory s) pageEq idxEq) =
   StateLib.readPhyEntry p (StateLib.getIndexOfAddr va levelMin) (memory s) );intros.
apply readPhyEntryUpdateLLCouplePPVA  with entry; trivial .
rewrite Heq;trivial.
Qed.

Lemma getAccessibleMappedPageUpdateLLCouplePPVA root s x table idx va entry:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
getAccessibleMappedPage root {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}  va = getAccessibleMappedPage root s va.
Proof.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) pageEq
              idxEq |}) in *.
intros Hentry. 
unfold getAccessibleMappedPage.
destruct(StateLib.getNbLevel);intros;trivial.
assert(Hind : getIndirection root va l (nbLevel - 1) s' =
getIndirection root va l (nbLevel - 1) s).
apply getIndirectionUpdateLLCouplePPVA with entry;trivial.
rewrite Hind.  
destruct(getIndirection root va l (nbLevel - 1)  s); intros; trivial.
destruct(Nat.eqb pageDefault p);trivial.
 assert(Hpresent :    StateLib.readPresent p (StateLib.getIndexOfAddr va levelMin)
  (memory s) = StateLib.readPresent p (StateLib.getIndexOfAddr va levelMin)
    (add table idx (PP x) (memory s) pageEq idxEq) ).
symmetry.
apply readPresentUpdateLLCouplePPVA with entry; trivial.
unfold s'. simpl.
rewrite <- Hpresent.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va levelMin) (memory s) ); trivial.
destruct b; trivial.
assert(Haccess :    StateLib.readAccessible p (StateLib.getIndexOfAddr va levelMin)
  (memory s) = StateLib.readAccessible p (StateLib.getIndexOfAddr va levelMin)
    (add table idx (PP x) (memory s) pageEq idxEq) ).
symmetry.
apply readAccessibleUpdateLLCouplePPVA with entry; trivial.
unfold s'. simpl.
rewrite <- Haccess.
destruct(StateLib.readAccessible p (StateLib.getIndexOfAddr va levelMin) (memory s) ); trivial.
destruct b; trivial.
assert(Heq :StateLib.readPhyEntry p (StateLib.getIndexOfAddr va levelMin)
    (add table idx (PP x) (memory s) pageEq idxEq) =
   StateLib.readPhyEntry p (StateLib.getIndexOfAddr va levelMin) (memory s) );intros.
apply readPhyEntryUpdateLLCouplePPVA  with entry; trivial .
rewrite Heq;trivial.
Qed.

Lemma getMappedPagesAuxUpdateLLCouplePPVA root s x table idx entry l:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
getMappedPagesAux root l {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} = 
getMappedPagesAux root l s.
Proof.
intros Hentry.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) pageEq
              idxEq |}) in *.
unfold getMappedPagesAux.
f_equal.
unfold getMappedPagesOption.
simpl.
induction l.
simpl;trivial.
simpl. 
rewrite IHl;f_equal.
apply getMappedPageUpdateLLCouplePPVA with entry; trivial.
Qed.


Lemma getAccessibleMappedPagesAuxUpdateLLCouplePPVA root s x table idx entry l:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
getAccessibleMappedPagesAux root l {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} = 
getAccessibleMappedPagesAux root l s.
Proof.
intros Hentry.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) pageEq
              idxEq |}) in *.
unfold getAccessibleMappedPagesAux.
f_equal.
unfold getAccessibleMappedPagesOption.
simpl.
induction l.
simpl;trivial.
simpl. 
rewrite IHl;f_equal.
apply getAccessibleMappedPageUpdateLLCouplePPVA with entry; trivial.
Qed.

Lemma getMappedPagesUpdateLLCouplePPVA s x table idx entry part: 
part <> table -> 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
 getMappedPages part {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}  = getMappedPages part s.
Proof.
intros.
unfold getMappedPages.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s)
              pageEq idxEq |}) in *.
assert(Hgetpd: StateLib.getPd part (memory s') = StateLib.getPd part (memory s)).
{ apply getPdUpdateLLCouplePPVA with entry;trivial.  }
rewrite Hgetpd.
case_eq(StateLib.getPd part (memory s));intros; trivial.
apply getMappedPagesAuxUpdateLLCouplePPVA with entry;trivial.
Qed.

Lemma getAccessibleMappedPagesUpdateLLCouplePPVA s x table idx entry part: 
part <> table ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
getAccessibleMappedPages part {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}  = getAccessibleMappedPages part s.
Proof.
intros.
unfold getAccessibleMappedPages.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s)
              pageEq idxEq |}) in *.
assert(Hgetpd: StateLib.getPd part (memory s') = StateLib.getPd part (memory s)).
{ apply getPdUpdateLLCouplePPVA with entry;trivial.  }
rewrite Hgetpd.
case_eq(StateLib.getPd part (memory s));intros; trivial.
apply getAccessibleMappedPagesAuxUpdateLLCouplePPVA with entry;trivial.
Qed.

Lemma checkChildUpdateLLCouplePPVA s x table idx entry l va part: 
part <> table ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
checkChild part l {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} va = checkChild part l s va.
Proof.
intro.
intros Hentry.
unfold checkChild.
simpl.
assert(Hsh1 : StateLib.getFstShadow part
    (add table idx (PP x) (memory s) pageEq idxEq)=
    StateLib.getFstShadow part (memory s)). 
{ apply getFstShadowUpdateLLCouplePPVA with entry; trivial. }
rewrite Hsh1.
destruct(StateLib.getFstShadow part (memory s) );trivial.
assert(Hind : getIndirection p va l (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx (PP x) (memory s) pageEq
                idxEq |} = getIndirection p va l (nbLevel - 1)
    s).
apply getIndirectionUpdateLLCouplePPVA with entry;trivial.
rewrite Hind.
destruct (getIndirection p va l (nbLevel - 1) s );trivial.
destruct (Nat.eqb p0 pageDefault);trivial.
assert(Hpdflag :  StateLib.readPDflag p0 (StateLib.getIndexOfAddr va levelMin)
    (add table idx (PP x) (memory s) pageEq idxEq) =
   StateLib.readPDflag p0 (StateLib.getIndexOfAddr va levelMin) (memory s)). 
  apply readPDflagUpdateLLCouplePPVA with entry;trivial.
rewrite Hpdflag.
trivial.
Qed.

Lemma getPdsVAddrUpdateLLCouplePPVA s x table idx entry l part: 
part <> table ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
 getPdsVAddr part l getAllVAddrWithOffset0 {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}  = getPdsVAddr part l getAllVAddrWithOffset0 s.
Proof.
intros.
unfold getPdsVAddr.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s)
              pageEq idxEq |}) in *.
induction getAllVAddrWithOffset0;simpl;trivial.
assert(Hcheckchild: checkChild part l s' a = checkChild part l s a).
{ simpl. apply checkChildUpdateLLCouplePPVA with entry;trivial. }
rewrite Hcheckchild;trivial.
case_eq(checkChild part l s a);intros;[
f_equal|];
apply IHl0.
Qed.

Lemma getChildrenUpdateLLCouplePPVA s x table idx entry part: 
part <> table ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) -> 
getChildren part s = 
getChildren part{|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}.
Proof.
intro.
intros Hentry.
unfold getChildren.
set (s' := {|
             currentPartition := currentPartition s;
             memory := add table idx (PP x) (memory s)
                         pageEq idxEq |}) in *.
intros. 
destruct ( StateLib.getNbLevel);trivial.
simpl.
assert(Hpd :  StateLib.getPd part (memory s) =
StateLib.getPd part
    (add table idx (PP x) (memory s) pageEq idxEq)).
{ symmetry. apply getPdUpdateLLCouplePPVA with entry;trivial.  }
rewrite <- Hpd.
destruct(StateLib.getPd part (memory s));trivial.
assert(Hpds : getPdsVAddr part l getAllVAddrWithOffset0 s' =
 getPdsVAddr part l getAllVAddrWithOffset0 s).
apply getPdsVAddrUpdateLLCouplePPVA with entry;trivial.
rewrite Hpds.
unfold s'.
symmetry.
apply getMappedPagesAuxUpdateLLCouplePPVA with entry;trivial.
Qed.

Lemma getPartitionsUpdateLLCouplePPVA s x table idx entry: 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) -> 
~In table (getPartitions pageRootPartition s) ->
getPartitions pageRootPartition s = getPartitions pageRootPartition{|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}. 
Proof.
intro.
generalize pageRootPartition at 1 2 3.
unfold getPartitions.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s)
              pageEq idxEq |}) in *.
induction (nbPage + 1);simpl;trivial.
intros.
f_equal.
assert(Hchildren: getChildren p s' =getChildren p s).
{ symmetry. apply getChildrenUpdateLLCouplePPVA with entry;trivial.
apply Logic.Classical_Prop.not_or_and in H0. intuition. }
rewrite Hchildren. clear Hchildren.
apply Logic.Classical_Prop.not_or_and in H0.
destruct H0.
induction (getChildren p s);simpl;trivial.
simpl in *.
rewrite in_app_iff in H1.
apply not_or_and in H1;intuition.
rewrite IHn;trivial.
f_equal.
trivial.
Qed.

Lemma nextEntryIsPPUpdateLLCouplePPVA table idx0 partition idx v x entry s :
lookup table idx0 (memory s) pageEq idxEq = Some (PP entry) ->
table <> partition ->
nextEntryIsPP partition idx v s <-> 
nextEntryIsPP partition idx v
  {|
currentPartition := currentPartition s;
memory := add table idx0 (PP x)
            (memory s) pageEq idxEq |}.
Proof.
intros;
unfold nextEntryIsPP in *;
case_eq(StateLib.Index.succ idx ); [intros idxsucc Hidxsucc| intros Hidxsucc];simpl;split;trivial;intros;
assert(Hbeqfalse:  beqPairs (table, idx0) (partition, idxsucc) pageEq idxEq = false) by
(apply beqPairsFalse;left;trivial);trivial;
rewrite Hbeqfalse in *;
 assert (lookup  partition idxsucc (removeDup table idx0 (memory s) pageEq idxEq)
           pageEq idxEq = lookup  partition idxsucc   (memory s) pageEq idxEq) as Hmemory by
(apply removeDupIdentity; intuition);
     rewrite Hmemory in *; trivial.
Qed.

Lemma isVAUpdateLLCouplePPVA idx partition table entry idxroot s x:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
isVA partition idxroot s -> 
isVA partition idxroot
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}.
Proof.
intros.
unfold isVA in *.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) pageEq idxEq);trivial;intros Hpairs.
apply beqPairsTrue in Hpairs.
intuition;subst.
rewrite H in H0;trivial.
apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  partition idxroot   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.


Lemma isPEUpdateLLCouplePPVA idx partition table  entry idxroot s x:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
isPE partition idxroot s -> 
isPE partition idxroot
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}.
Proof.
intros Hentry.
unfold isPE.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  partition idxroot   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma isVEUpdateLLCouplePPVA idx partition table  entry idxroot s x:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
isVE partition idxroot s -> 
isVE partition idxroot
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}.
Proof.
intros Hentry.
unfold isVE.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  partition idxroot   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.


Lemma entryUserFlagUpdateLLCouplePPVA idx ptVaInCurPartpd idxvaInCurPart table 
 entry s x accessiblesrc:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
entryUserFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc s -> 
entryUserFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}.
Proof.
intros Hentry.
unfold entryUserFlag.
cbn.
case_eq (beqPairs (table, idx) (ptVaInCurPartpd, idxvaInCurPart) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptVaInCurPartpd idxvaInCurPart (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  ptVaInCurPartpd idxvaInCurPart   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma entryPresentFlagUpdateLLCouplePPVA idx ptVaInCurPartpd idxvaInCurPart table 
 entry s x accessiblesrc:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
entryPresentFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc s -> 
entryPresentFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}.
Proof.
intros Hentry.
unfold entryPresentFlag.
cbn.
case_eq (beqPairs (table, idx) (ptVaInCurPartpd, idxvaInCurPart) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptVaInCurPartpd idxvaInCurPart (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  ptVaInCurPartpd idxvaInCurPart   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma entryPDFlagUpdateLLCouplePPVA idx ptDescChild table idxDescChild entry s x flag:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
entryPDFlag ptDescChild idxDescChild flag s -> 
entryPDFlag ptDescChild idxDescChild flag
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}.
Proof.
intros Hentry.
unfold entryPDFlag.
cbn.
case_eq (beqPairs (table, idx) (ptDescChild, idxDescChild) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptDescChild idxDescChild (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  ptDescChild idxDescChild   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma isEntryVAUpdateLLCouplePPVA idx ptVaInCurPart table idxvaInCurPart entry s  vainve x:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
isEntryVA ptVaInCurPart idxvaInCurPart vainve s -> 
isEntryVA ptVaInCurPart idxvaInCurPart vainve
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}.
Proof.
intros Hentry.
unfold isEntryVA.
cbn.
case_eq (beqPairs (table, idx) (ptVaInCurPart, idxvaInCurPart) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptVaInCurPart idxvaInCurPart (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  ptVaInCurPart idxvaInCurPart  (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma isIndexValueUpdateLLCouplePPVA idx ptVaInCurPart table idxvaInCurPart entry s  vainve x:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
isIndexValue ptVaInCurPart idxvaInCurPart vainve s -> 
isIndexValue ptVaInCurPart idxvaInCurPart vainve
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}.
Proof.
intros Hentry.
unfold isIndexValue.
cbn.
case_eq (beqPairs (table, idx) (ptVaInCurPart, idxvaInCurPart) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptVaInCurPart idxvaInCurPart (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  ptVaInCurPart idxvaInCurPart  (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma isVA'UpdateLLCouplePPVA idx ptVaInCurPart table idxvaInCurPart entry s  vainve x:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
isVA' ptVaInCurPart idxvaInCurPart vainve s -> 
isVA' ptVaInCurPart idxvaInCurPart vainve
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}.
Proof.
intros Hentry.
unfold isVA'.
cbn.
case_eq (beqPairs (table, idx) (ptVaInCurPart, idxvaInCurPart) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptVaInCurPart idxvaInCurPart (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  ptVaInCurPart idxvaInCurPart  (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.


Lemma isEntryPageUpdateLLCouplePPVA idx ptVaInCurPart table idxvaInCurPart entry s  vainve x:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
isEntryPage ptVaInCurPart idxvaInCurPart vainve s -> 
isEntryPage ptVaInCurPart idxvaInCurPart vainve
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}.
Proof.
intros Hentry.
unfold isEntryPage.
cbn.
case_eq (beqPairs (table, idx) (ptVaInCurPart, idxvaInCurPart) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptVaInCurPart idxvaInCurPart (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  ptVaInCurPart idxvaInCurPart  (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma partitionsIsolationUpdateLLCouplePPVA s x table idx entry: 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
partitionsIsolation s ->
~ In table (getPartitions pageRootPartition s)  ->
StateLib.getMaxIndex <> Some idx -> 
noDupPartitionTree s ->
partitionsIsolation {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}. 
Proof.
intros Hlookup Hisopart.
intros Hkey1 Hkey2 Hnodup.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}) in *. 
unfold partitionsIsolation in *. 
intros (* Hisopart *) parent child1 child2 Hparent Hchild1 Hchild2 Hdist.
assert(Hparts : getPartitions pageRootPartition s = getPartitions pageRootPartition s').
apply getPartitionsUpdateLLCouplePPVA with entry;trivial.
rewrite <- Hparts in *;trivial.  
  assert (Hused :  forall part, In part (getPartitions pageRootPartition s) 
    -> part <> table -> getUsedPages part s' = getUsedPages part s). 
  { intros. 
    unfold getUsedPages in *. 
    assert(Hconfig : forall part, In part (getPartitions pageRootPartition s) 
    -> part <> table -> getConfigPages part s' = getConfigPages part s).
    { intros.
      apply getConfigPagesUpdateLLCouplePPVA with entry;trivial. } 
    rewrite Hconfig in *.
    f_equal.
    assert(Hmap :  forall part, In part (getPartitions pageRootPartition s) 
    -> part <> table -> getMappedPages part s' = getMappedPages part s).
    { intros.
      apply getMappedPagesUpdateLLCouplePPVA with entry;trivial. } 
    rewrite Hmap in *;trivial. trivial. trivial. }    
  assert(Hchildren : getChildren parent s = getChildren parent s').
  apply getChildrenUpdateLLCouplePPVA with entry;trivial.
  contradict Hkey1;subst;trivial.
  rewrite <- Hchildren in *. clear Hchildren.
  assert( In child1 (getPartitions pageRootPartition s)).
  apply childrenPartitionInPartitionList with parent;trivial.
  assert( In child2 (getPartitions pageRootPartition s)).
  apply childrenPartitionInPartitionList with parent;trivial.
  rewrite Hused;trivial.
  rewrite Hused;trivial.
  apply Hisopart with parent;trivial.
  contradict H0;subst;trivial.
  contradict H;subst;trivial.
Qed.

Lemma kernelDataIsolationUpdateLLCouplePPVA s x table idx entry: 
StateLib.getMaxIndex <> Some idx -> 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
kernelDataIsolation s ->
kernelDataIsolation {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}. 
Proof.
intros Hkey2.
intro.
intros Hlookup.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}) in *. 
unfold kernelDataIsolation in *. 
intros Hkdi partition1 partition2 Hpart1 Hpart2.
assert(Hparts : getPartitions pageRootPartition s = getPartitions pageRootPartition s').
apply getPartitionsUpdateLLCouplePPVA with entry;trivial.
rewrite <- Hparts in *;trivial. clear Hparts.
assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
{ intros.
apply getConfigPagesUpdateLLCouplePPVA with entry;trivial. contradict H;subst;trivial. } 
rewrite Hconfig in *. clear Hconfig.
assert(Haccessmap : getAccessibleMappedPages partition1 s' =
getAccessibleMappedPages partition1 s).
{ intros. apply getAccessibleMappedPagesUpdateLLCouplePPVA with entry;trivial.
contradict H;subst;trivial. }
rewrite Haccessmap in *. 
apply Hkdi;trivial.
Qed.  

Lemma verticalSharingUpdateLLCouplePPVA s x table idx entry: 
StateLib.getMaxIndex <> Some idx -> 
~ In table (getPartitions pageRootPartition s) ->
noDupPartitionTree s ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
verticalSharing s ->
verticalSharing {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}. 
Proof.
intros Hkey2.
intros H H0.
intros Hlookup.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}) in *. 
unfold verticalSharing in *.
intros Hvs parent child Hparent Hchild.
assert(Hparts : getPartitions pageRootPartition s = getPartitions pageRootPartition s').
apply getPartitionsUpdateLLCouplePPVA with entry;trivial.
rewrite <- Hparts in *;trivial. clear Hparts.
assert(Hchildren : getChildren parent s = getChildren parent s').
apply getChildrenUpdateLLCouplePPVA with entry;trivial.
contradict H;subst;trivial.
rewrite <- Hchildren in *. clear Hchildren.
assert(Hmap :  forall part, In part (getPartitions pageRootPartition s) 
    -> part <> table -> getMappedPages part s' = getMappedPages part s).
{ intros.
  apply getMappedPagesUpdateLLCouplePPVA with entry;trivial. } 
  rewrite Hmap in *;trivial.
assert (Hused : forall part, In part (getPartitions pageRootPartition s) 
    -> part <> table -> getUsedPages part s' = getUsedPages part s). 
{ intros. 
  unfold getUsedPages in *. 
  assert(Hconfig : forall part, In part (getPartitions pageRootPartition s) 
    -> part <> table -> getConfigPages part s' = getConfigPages part s).
  { intros.
    apply getConfigPagesUpdateLLCouplePPVA with entry;trivial. } 
  rewrite Hconfig in *;trivial.
  rewrite Hmap;trivial.  }
assert(In child (getPartitions pageRootPartition s)) by (apply childrenPartitionInPartitionList with parent;trivial).
rewrite Hused;trivial.
apply Hvs;trivial.
contradict H;subst;trivial.
contradict H;subst;trivial.
Qed.


Lemma isPPUpdateLLCouplePPVA table p idx idx0 x entry s:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
isPP p idx0 s -> 
isPP p idx0 {|
      currentPartition := currentPartition s;
      memory := add table idx (PP x) (memory s) pageEq idxEq |}.
Proof.      
intros.
unfold isPP in *.
simpl.
case_eq (beqPairs  (table, idx) (p, idx0)  pageEq idxEq);trivial;intros Hpairs.
apply beqPairsFalse in Hpairs.    
assert (lookup p idx0 (removeDup table idx   (memory s) pageEq idxEq)
       pageEq idxEq = lookup  p idx0  (memory s) pageEq idxEq) as Hmemory.
{ apply removeDupIdentity. intuition. }
 rewrite Hmemory. trivial.
Qed.


Lemma dataStructurePdSh1Sh2asRootUpdateLLCouplePPVA s x table idx entry idxroot: 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
~ In table (getPartitions pageRootPartition s) ->
dataStructurePdSh1Sh2asRoot idxroot s ->
dataStructurePdSh1Sh2asRoot idxroot {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}. 
Proof.
intros Hlookup Hkey Hds.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}) in *. 
unfold dataStructurePdSh1Sh2asRoot in *.
intros.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition s').
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions.
unfold s' in *.
intros.
rewrite <- nextEntryIsPPUpdateLLCouplePPVA in H0; try eassumption.
assert (Hind : getIndirection entry0 va level stop s = Some indirection).
{ rewrite <- H3. symmetry.
  apply getIndirectionUpdateLLCouplePPVA with entry; trivial. }
clear H3.
assert(Hdss :indirection = pageDefault \/
      (stop < level /\ isPE indirection idx0 s \/
       stop >= level /\
       (isVE indirection idx0 s /\ idxroot = idxShadow1 \/
        isVA indirection idx0 s /\ idxroot = idxShadow2 \/ isPE indirection idx0 s /\ idxroot = idxPageDir)) /\
      indirection <> pageDefault).
apply Hds with partition entry0 va; trivial.
clear Hds.
destruct Hdss as [Hds | Hds];[left;trivial|].
right.
destruct Hds as (Hds & Hnotnull); split; trivial.
destruct Hds as [(Hlt & Hpe) | Hds].
+ left; split; trivial.
  apply isPEUpdateLLCouplePPVA with entry; trivial.
+ right.
  destruct Hds as (Hlevel & [(Hve & Hidx) | [(Hva & Hidx) | (Hpe & Hidx)]]).
  split; trivial.
  - left; split; trivial.
    apply isVEUpdateLLCouplePPVA with entry; trivial.
  - split; trivial.
    right; left;split; trivial.
    apply isVAUpdateLLCouplePPVA with entry; trivial.
  - split;trivial.
    right;right; split; trivial.
    apply isPEUpdateLLCouplePPVA with entry; trivial.
+ contradict Hkey;subst;trivial.
Qed.

Lemma partitionDescriptorEntryUpdateLLCouplePPVA s x table idx entry: 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
~ In table (getPartitions pageRootPartition s) ->
partitionDescriptorEntry s ->
partitionDescriptorEntry {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}. 
Proof.
intros Hlookup Hkey.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}) in *. 
unfold partitionDescriptorEntry in *. 
intros Hpde part Hpart idxroot Hidxroot.
assert(Hidx : idxroot < tableSize - 1 ).
{ assert(tableSizeLowerBound < tableSize).
  apply tableSizeBigEnough.
  unfold tableSizeLowerBound in *.
  intuition subst.
  unfold idxPageDir.
  unfold CIndex.
  case_eq( lt_dec 2 tableSize );intros;
  simpl;lia.
  unfold idxShadow1.
  unfold CIndex.
  case_eq( lt_dec 4 tableSize );intros;
  simpl;lia.
   unfold idxShadow2.
  unfold CIndex.
  case_eq( lt_dec 6 tableSize );intros;
  simpl;lia.
   unfold idxShadow3.
  unfold CIndex.
  case_eq( lt_dec 8 tableSize );intros;
  simpl;lia.
  unfold idxParentDesc.
  unfold CIndex.
  case_eq( lt_dec 10 tableSize );intros;
  simpl;lia.
  unfold idxPartDesc.
  unfold CIndex.
  case_eq( lt_dec 0 tableSize );intros;
  simpl;lia. }
assert(Hparts : getPartitions pageRootPartition s = getPartitions pageRootPartition s').
apply getPartitionsUpdateLLCouplePPVA with entry;trivial.
rewrite <- Hparts in *;trivial. clear Hparts.
assert (HPP : forall p idx, isVA p idx s -> isVA p idx s').
{ intros.
  apply isVAUpdateLLCouplePPVA with entry;trivial. }
assert (HPE : forall p idx x, table <> p -> nextEntryIsPP p idx x s -> 
            nextEntryIsPP   p idx x s').
{ intros.
  apply nextEntryIsPPUpdateLLCouplePPVA with entry;trivial. }

assert(Hconcl : idxroot < tableSize - 1 /\
       isVA part idxroot s /\
       (exists entry : page, nextEntryIsPP part idxroot entry s /\ entry <> pageDefault)).
apply Hpde;trivial.
destruct Hconcl as (Hi1 & Hi2 & Hi3).
split;trivial.
split.
apply HPP;trivial.
destruct Hi3 as (entry0 & Hentry & Htrue).
exists entry0;split;trivial.
apply HPE;trivial.
contradict Hkey;subst;trivial.
Qed. 

Lemma currentPartitionInPartitionsListUpdateLLCouplePPVA s x table idx entry : 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
currentPartitionInPartitionsList s ->
currentPartitionInPartitionsList {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}. 
Proof.
intro.
intros Hlookup.
unfold currentPartitionInPartitionsList.
intros; 
simpl.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP x) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions;trivial.
Qed.

Lemma noDupMappedPagesListUpdateLLCouplePPVA s x table idx entry : 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
noDupMappedPagesList s ->
noDupMappedPagesList {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}. 
Proof.
intro Hkey.
intros Hlookup.
unfold noDupMappedPagesList.
intros; 
simpl.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP x) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hmap :  forall part, In part (getPartitions pageRootPartition s) 
    -> part <> table -> getMappedPages part {|
     currentPartition := currentPartition s;
     memory := add table idx (PP x) (memory s) pageEq
                 idxEq |}= getMappedPages part s).
{ intros.
  apply getMappedPagesUpdateLLCouplePPVA with entry;trivial.
 }
  rewrite Hmap;trivial.
apply H;trivial.
  contradict Hkey;subst;trivial.
Qed.

Lemma noDupConfigPagesListUpdateLLCouplePPVA s x table idx entry : 
StateLib.getMaxIndex <> Some idx -> 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
noDupConfigPagesList s ->
noDupConfigPagesList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) pageEq
              idxEq |}. 
Proof.
intros Hkey2.
intro Hkey.
intros Hlookup.
unfold noDupConfigPagesList.
intros; 
simpl.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP x) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hind :   forall part, In part (getPartitions pageRootPartition s) 
    -> part <> table ->  getConfigPages part {|
     currentPartition := currentPartition s;
     memory := add table idx (PP x) (memory s) pageEq
                 idxEq |}= getConfigPages part s).
{ intros.
  apply getConfigPagesUpdateLLCouplePPVA with entry;trivial. }
  rewrite Hind;trivial.
apply H ;trivial.
contradict Hkey;subst;trivial.
Qed. 

Lemma parentInPartitionListUpdateLLCouplePPVA s x table idx entry : 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
parentInPartitionList s ->
parentInPartitionList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) pageEq
              idxEq |}. 
Proof.
intro Hkey.
intros Hlookup.
unfold parentInPartitionList.
intros; 
simpl.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP x) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
apply H with partition;trivial.
rewrite nextEntryIsPPUpdateLLCouplePPVA with  entry;trivial.
eassumption;trivial.
trivial.
contradict Hkey;subst;trivial.
Qed.


Lemma getPDFlagUpdateLLCouplePPVA s x table idx entry sh1 va: 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
getPDFlag sh1 va
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) pageEq
              idxEq |} = getPDFlag sh1 va s.
Proof.
intros Hentry.
unfold getPDFlag.
simpl.
destruct (StateLib.getNbLevel);trivial.
assert(Hind : getIndirection sh1 va l (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx (PP x) (memory s) pageEq
                idxEq |} = getIndirection  sh1 va l (nbLevel - 1)
    s).
apply getIndirectionUpdateLLCouplePPVA with entry;trivial.
rewrite Hind.
destruct (getIndirection  sh1 va l (nbLevel - 1) s );trivial.
destruct (Nat.eqb p pageDefault);trivial.
assert(Hpdflag :  StateLib.readPDflag p (StateLib.getIndexOfAddr va levelMin)
    (add table idx (PP x) (memory s) pageEq idxEq) =
   StateLib.readPDflag p (StateLib.getIndexOfAddr va levelMin) (memory s)). 
  apply readPDflagUpdateLLCouplePPVA with entry;trivial.
rewrite Hpdflag.
trivial.
Qed. 

Lemma accessibleVAIsNotPartitionDescriptorUpdateLLCouplePPVA s x table idx entry : 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
accessibleVAIsNotPartitionDescriptor s ->
accessibleVAIsNotPartitionDescriptor
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) pageEq
              idxEq |}. 
Proof.
intro Hkey.
intros Hlookup.
unfold accessibleVAIsNotPartitionDescriptor.
intros; 
simpl.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP x) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Haccessmap : forall part, getAccessibleMappedPage part {|
       currentPartition := currentPartition s;
       memory := add table idx (PP x) (memory s) pageEq
                   idxEq |} va =
getAccessibleMappedPage part s va).
{ intros. apply getAccessibleMappedPageUpdateLLCouplePPVA with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
assert(Hpd :  StateLib.getPd partition (memory s) =
StateLib.getPd partition
    (add table idx (PP x) (memory s) pageEq idxEq)).
{ symmetry. apply getPdUpdateLLCouplePPVA with entry;trivial. 
contradict Hkey;subst;trivial.  }
rewrite <- Hpd in *.
assert(Hsh1 :  StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (PP x) (memory s) pageEq idxEq)).
{ symmetry. apply getFstShadowUpdateLLCouplePPVA with entry;trivial.
contradict Hkey;subst;trivial.  }
rewrite <- Hsh1 in *.
rewrite <- H with partition va pd sh1 page;trivial.
apply getPDFlagUpdateLLCouplePPVA with entry;trivial.
Qed. 

Lemma readVirtualUpdateLLCouplePPVA table1 table2 idx1 idx2  x entry s :
(* table1 <> table2 \/ idx1 <> idx2 ->  *)
lookup table2 idx2 (memory s) pageEq idxEq = Some (PP entry) ->
 StateLib.readVirtual table1 idx1
         (add table2 idx2 (PP x) (memory s) pageEq
     idxEq)  = 
 StateLib.readVirtual table1 idx1 (memory s).
Proof.
unfold StateLib.readVirtual.
cbn.
intros Hentry.
case_eq( beqPairs  (table2, idx2) (table1, idx1) pageEq idxEq); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq) pageEq idxEq = 
 lookup table1 idx1 (memory s)  pageEq idxEq ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.


Lemma wellFormedShadowsUpdateLLCouplePPVA s vaInCurrentPartition table idx entry idxroot: 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP  entry) ->
wellFormedShadows idxroot s -> 
wellFormedShadows idxroot
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP  vaInCurrentPartition) (memory s) pageEq
              idxEq |}.
Proof.
intros Hkey.
intros Hlookup.
unfold wellFormedShadows.
intros.
simpl in *.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP  vaInCurrentPartition) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, In partition (getPartitions pageRootPartition s) 
    -> partition <> table -> StateLib.getPd partition
       (add table idx (PP  vaInCurrentPartition) (memory s) pageEq idxEq)
       =  StateLib.getPd partition (memory s)).
{ intros.
  apply getPdUpdateLLCouplePPVA with entry;trivial. }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hpp : nextEntryIsPP partition idxroot structroot s ). 
rewrite nextEntryIsPPUpdateLLCouplePPVA with entry;trivial.
eassumption. 
trivial.
contradict Hkey;subst;trivial.
assert(Hind : forall root, getIndirection root va nbL stop
    {|
    currentPartition := currentPartition s;
    memory := add table idx (PP  vaInCurrentPartition) (memory s) pageEq
                idxEq |} = getIndirection  root va nbL stop
    s).
    { intros. apply getIndirectionUpdateLLCouplePPVA with entry;trivial. }
assert(Hgoal :  exists indirection2 : page,
      getIndirection structroot va nbL stop s = Some indirection2 /\
      (Nat.eqb pageDefault indirection2) = b). 
{ apply H with partition pdroot indirection1;trivial.
  rewrite <- Hind;trivial. }
destruct Hgoal as (indirection2 & Hind1 & Hindnotnul).
exists indirection2;split;trivial.
rewrite <- Hind1.
apply Hind;trivial.
contradict Hkey;subst;trivial.
Qed.

Lemma getTableAddrRootUpdateLLCouplePPVA s vaInCurrentPartition table idx entry  idxroot 
ptDescChild descChild currentPart: 
table <> currentPart ->
lookup table idx (memory s) pageEq idxEq = Some (PP  entry) ->
getTableAddrRoot ptDescChild idxroot currentPart descChild  s-> 
getTableAddrRoot ptDescChild idxroot currentPart descChild
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP  vaInCurrentPartition) (memory s)
              pageEq idxEq |}.
Proof.
intros Hkey Hlookup.
unfold getTableAddrRoot.
intros Hcond.
destruct Hcond as(Hi & Hcond).
split;trivial.
intros. 
assert(Hpp : nextEntryIsPP currentPart idxroot tableroot s ). 
rewrite nextEntryIsPPUpdateLLCouplePPVA with entry;trivial.
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
apply getIndirectionUpdateLLCouplePPVA with entry;trivial.
Qed.

Lemma getAncestorsUpdateLLCouplePPVA s x table idx entry partition: 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
table <> partition ->
~ In table  (getAncestors partition s) ->
getAncestors partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s)
              pageEq idxEq |} =
                      getAncestors partition s.
Proof. 
intros Hlookup.
unfold getAncestors.
simpl.
revert partition. 
induction (nbPage + 1);trivial.
simpl;intros.
assert(Hparent : StateLib.getParent partition
    (add table idx (PP x) (memory s) pageEq
       idxEq) = StateLib.getParent partition (memory s)).
{  apply getParentUpdateLLCouplePPVA with entry;trivial.
intuition. }
rewrite Hparent.
destruct (StateLib.getParent partition (memory s) );trivial.
f_equal.
simpl in *.
apply not_or_and in H0.
intuition.
Qed.

Lemma noCycleInPartitionTreeUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP  entry) ->
parentInPartitionList s ->
isChild s ->
noCycleInPartitionTree s -> 
noCycleInPartitionTree
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP  vaInCurrentPartition) (memory s) pageEq
              idxEq |}.
Proof.
intros Hkey.
intros Hlookup.
unfold noCycleInPartitionTree.
intros; 
simpl.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP  vaInCurrentPartition) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hancestor :getAncestors partition
          {|
          currentPartition := currentPartition s;
          memory := add table idx (PP  vaInCurrentPartition) (memory s)
                      pageEq idxEq |} =
                      getAncestors partition s).
apply getAncestorsUpdateLLCouplePPVA with entry;trivial.
contradict Hkey;subst;trivial.
contradict Hkey.
apply ancestorInPartitionTree with partition;trivial.
rewrite Hancestor in *.
apply H1;trivial.
Qed.

Lemma configTablesAreDifferentUpdateLLCouplePPVA s vaInCurrentPartition table idx entry :
StateLib.getMaxIndex <> Some idx -> 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP  entry) ->
configTablesAreDifferent s -> 
configTablesAreDifferent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
              idxEq |}.
Proof.
intro Hkey2.
intro Hkey.
intros Hlookup.
unfold configTablesAreDifferent.
intros; 
simpl.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hconfig : forall part, In part (getPartitions pageRootPartition s) 
    -> part <> table -> getConfigPages part {|
          currentPartition := currentPartition s;
          memory := add table idx (PP vaInCurrentPartition) (memory s)
                      pageEq idxEq |} = getConfigPages part s).
{ intros.
apply getConfigPagesUpdateLLCouplePPVA with entry;trivial. } 
rewrite Hconfig in *;trivial. 
rewrite Hconfig in *;trivial.
clear Hconfig.
apply H;trivial.
contradict Hkey;subst;trivial.
contradict Hkey;subst;trivial.
Qed.

Lemma isChildUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
parentInPartitionList s ->
isChild s -> 
isChild
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
              idxEq |}.
Proof.
intro Hkey.
intros Hlookup.
unfold isChild.
intros; 
simpl.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hparent : StateLib.getParent partition
    (add table idx (PP vaInCurrentPartition) (memory s) pageEq
       idxEq) = StateLib.getParent partition (memory s)).
{ apply getParentUpdateLLCouplePPVA with entry;trivial. contradict Hkey;subst;trivial.  }
assert(Hchildren : forall part, In part (getPartitions pageRootPartition s) 
    -> part <> table -> getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                 idxEq |} = getChildren part s).
{ intros.
symmetry.
apply getChildrenUpdateLLCouplePPVA with entry;trivial.
 } 
rewrite Hchildren in *.
clear Hchildren.
rewrite  Hparent in *.
apply H0;trivial.
unfold parentInPartitionList in *.
apply H with partition;trivial.
apply nextEntryIsPPgetParent;trivial.
rewrite <- Hparent;trivial.
contradict Hkey;subst;trivial.
unfold parentInPartitionList in *.
apply H with partition;trivial.
apply nextEntryIsPPgetParent;trivial.
rewrite <- Hparent;trivial.
Qed.

Lemma isPresentNotDefaultIffUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
isPresentNotDefaultIff s -> 
isPresentNotDefaultIff
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
              idxEq |}.
Proof.
intros Hlookup.
unfold isPresentNotDefaultIff.
intros; 
simpl.
 assert(Hpresent :    StateLib.readPresent table0 idx0
  (memory s) = StateLib.readPresent table0 idx0
    (add table idx (PP vaInCurrentPartition) (memory s) pageEq idxEq) ).
symmetry.
apply readPresentUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpresent.
 assert(Hread :    StateLib.readPhyEntry table0 idx0
  (memory s) = StateLib.readPhyEntry table0 idx0
    (add table idx (PP vaInCurrentPartition) (memory s) pageEq idxEq) ).
symmetry.
apply readPhyEntryUpdateLLCouplePPVA with entry;trivial.
rewrite <- Hread.
apply H.
Qed.

Lemma getVirtualAddressSh1UpdateLLCouplePPVA  s vaInCurrentPartition table idx entry p va: 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
getVirtualAddressSh1 p s va  =
getVirtualAddressSh1 p {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                idxEq |} va.
Proof.
intros Hlookup.
unfold getVirtualAddressSh1.
destruct (StateLib.getNbLevel);trivial.
assert(Hind : getIndirection p va l (nbLevel - 1)
{|
currentPartition := currentPartition s;
memory := add table idx  (PP vaInCurrentPartition) (memory s) pageEq
            idxEq |} = getIndirection  p va l  (nbLevel - 1)
s).
{ apply getIndirectionUpdateLLCouplePPVA with entry;trivial. }
rewrite Hind.
case_eq (getIndirection  p va l  (nbLevel - 1) s );
[ intros tbl Htbl | intros Htbl]; trivial.
case_eq (Nat.eqb pageDefault tbl);trivial.
intros Htblnotnul.
simpl.
symmetry.
apply readVirEntryUpdateLLCouplePPVA with entry;trivial.
Qed.

Lemma getVirtualAddressSh2UpdateLLCouplePPVA  s vaInCurrentPartition table idx entry p va: 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
getVirtualAddressSh2 p s va  =
getVirtualAddressSh2 p {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                idxEq |} va.
Proof.
intros Hlookup.
unfold getVirtualAddressSh2.
destruct (StateLib.getNbLevel);trivial.
assert(Hind : getIndirection p va l (nbLevel - 1)
{|
currentPartition := currentPartition s;
memory := add table idx  (PP vaInCurrentPartition) (memory s) pageEq
            idxEq |} = getIndirection  p va l  (nbLevel - 1)
s).
{ apply getIndirectionUpdateLLCouplePPVA with entry;trivial. }
rewrite Hind.
case_eq (getIndirection  p va l  (nbLevel - 1) s );
[ intros tbl Htbl | intros Htbl]; trivial.
case_eq (Nat.eqb pageDefault tbl);trivial.
intros Htblnotnul.
simpl.
symmetry.
apply readVirtualUpdateLLCouplePPVA with entry ;trivial.
Qed.

Lemma isDerivedUpdateLLCouplePPVA  s vaInCurrentPartition table idx entry parent va: 
~ In table (getPartitions pageRootPartition s) ->
In parent (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
isDerived parent va s ->  isDerived parent va  {|
       currentPartition := currentPartition s;
       memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                   idxEq |}
       . 
Proof.
intros Hkey Hpart.
intros Hlookup.
unfold isDerived.
simpl.
assert(Hsh1 :  StateLib.getFstShadow parent (memory s) =
StateLib.getFstShadow parent
    (add table idx (PP vaInCurrentPartition) (memory s) pageEq idxEq)).
{ symmetry. apply getFstShadowUpdateLLCouplePPVA with entry;trivial.
contradict Hkey;subst;trivial.   }
rewrite <- Hsh1 in *.
destruct (StateLib.getFstShadow parent (memory s));trivial.
assert(Hgetvir1 : getVirtualAddressSh1 p s va  =
getVirtualAddressSh1 p {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                idxEq |} va ).
apply getVirtualAddressSh1UpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir1;trivial.
Qed.
 
Lemma physicalPageNotDerivedUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
noDupPartitionTree s ->
physicalPageNotDerived s -> 
physicalPageNotDerived
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
              idxEq |}.
Proof.
intro Hkey.
intros Hlookup.
unfold physicalPageNotDerived.
intros; 
simpl.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hchildren : forall part, In part (getPartitions pageRootPartition s) 
    -> part <> table -> getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                 idxEq |} = getChildren part s).
{ intros.
symmetry.
apply getChildrenUpdateLLCouplePPVA with entry;trivial. } 
rewrite Hchildren in *.
clear Hchildren.
assert(Hpd : forall partition, In partition (getPartitions pageRootPartition s) 
    -> partition <> table -> StateLib.getPd partition
       (add table idx (PP vaInCurrentPartition) (memory s) pageEq idxEq)
       =  StateLib.getPd partition (memory s)).
{ intros.
 apply getPdUpdateLLCouplePPVA with entry;trivial. }
rewrite Hpd in *. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
             idxEq |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateLLCouplePPVA with entry;trivial. }
rewrite Hmap in *. clear Hmap.
assert(~ isDerived parent va s ). 
unfold not;intros. 
contradict H3.
apply isDerivedUpdateLLCouplePPVA with entry;trivial.
apply H0 with  parent va pdParent
child pdChild vaInChild;trivial.
trivial.
contradict Hkey;subst;trivial.
apply childrenPartitionInPartitionList with parent;trivial.
contradict Hkey;subst;trivial.
apply childrenPartitionInPartitionList with parent;trivial.
trivial.
contradict Hkey;subst;trivial.
Qed.

Lemma multiplexerWithoutParentUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
~ In table (getPartitions pageRootPartition s) ->
multiplexerWithoutParent s -> 
multiplexerWithoutParent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
              idxEq |}.
Proof.
intros Hlookup.
unfold multiplexerWithoutParent.
intros; 
simpl.

assert(Hparent : StateLib.getParent pageRootPartition
    (add table idx (PP vaInCurrentPartition) (memory s) pageEq
       idxEq) = StateLib.getParent pageRootPartition (memory s)).
{ apply getParentUpdateLLCouplePPVA with entry;trivial. 
  unfold getPartitions in *.
  destruct nbPage;simpl in *;  apply not_or_and in H;  intuition.
   }
rewrite Hparent in *.
trivial.
Qed.

Lemma isParentUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
noDupPartitionTree s ->
isParent s -> 
isParent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
              idxEq |}.
Proof.
intro Hkey.
intros Hlookup.
unfold isParent.
intros.
simpl in *. 
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hchildren : forall part, In part (getPartitions pageRootPartition s) 
    -> part <> table -> getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                 idxEq |} = getChildren part s).
{ intros.
symmetry.
apply getChildrenUpdateLLCouplePPVA with entry;trivial. } 
rewrite Hchildren in *;trivial.
assert(Hparent : StateLib.getParent partition
    (add table idx (PP vaInCurrentPartition) (memory s) pageEq
       idxEq) = StateLib.getParent partition (memory s)).
{ apply getParentUpdateLLCouplePPVA with entry;trivial.
assert(Hpart: In partition (getPartitions pageRootPartition s)).
apply childrenPartitionInPartitionList with parent;trivial.
contradict Hkey;subst;trivial. }
rewrite Hparent in *;trivial.
apply H0; trivial.
contradict Hkey;subst;trivial.
Qed.

Lemma noDupPartitionTreeUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
noDupPartitionTree s -> 
noDupPartitionTree
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
              idxEq |}.
Proof.
intro Hkey.
intros Hlookup.
unfold noDupPartitionTree.
intros.
simpl in *.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
Qed.
 
Lemma wellFormedFstShadowUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
wellFormedFstShadow s -> 
wellFormedFstShadow
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
              idxEq |}.
Proof.
intro Hkey.
intros Hlookup.
unfold wellFormedFstShadow.
intros.
simpl in *.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, In partition (getPartitions pageRootPartition s) 
    -> partition <> table -> StateLib.getPd partition
       (add table idx (PP vaInCurrentPartition) (memory s) pageEq idxEq)
       =  StateLib.getPd partition (memory s)).
{ intros. apply getPdUpdateLLCouplePPVA with entry;trivial.  }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
             idxEq |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateLLCouplePPVA with entry;trivial. }
rewrite Hmap in *;trivial. clear Hmap.
assert(Hsh1 :  forall partition, In partition (getPartitions pageRootPartition s) 
    -> partition <> table -> StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (PP vaInCurrentPartition) (memory s) pageEq idxEq)).
{ symmetry. apply getFstShadowUpdateLLCouplePPVA with entry;trivial.  }
rewrite <- Hsh1 in *;trivial. clear Hsh1.
assert(Hgetvir1 : getVirtualAddressSh1 sh1 s va  =
getVirtualAddressSh1 sh1 {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                idxEq |} va ).
apply getVirtualAddressSh1UpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir1;trivial.
apply H with partition pg pd;trivial.
contradict Hkey;subst;trivial.
contradict Hkey;subst;trivial.
Qed.

Lemma wellFormedSndShadowUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
wellFormedSndShadow s -> 
wellFormedSndShadow
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
              idxEq |}.
Proof.
intro Hkey.
intros Hlookup.
unfold wellFormedSndShadow.
intros.
simpl in *.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, In partition (getPartitions pageRootPartition s) 
    -> partition <> table -> StateLib.getPd partition
       (add table idx (PP vaInCurrentPartition) (memory s) pageEq idxEq)
       =  StateLib.getPd partition (memory s)).
{ intros. apply getPdUpdateLLCouplePPVA with entry;trivial.  }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
             idxEq |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateLLCouplePPVA with entry;trivial. }
rewrite Hmap in *;trivial. clear Hmap.
assert(Hsh1 :  forall partition, In partition (getPartitions pageRootPartition s) 
    -> partition <> table -> StateLib.getSndShadow partition (memory s) =
StateLib.getSndShadow partition
    (add table idx (PP vaInCurrentPartition) (memory s) pageEq idxEq)).
{ symmetry. apply getSndShadowUpdateLLCouplePPVA with entry;trivial.  }
rewrite <- Hsh1 in *;trivial. clear Hsh1.
assert(Hgetvir1 : getVirtualAddressSh2 sh2 s va  =
getVirtualAddressSh2 sh2 {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                idxEq |} va ).
apply getVirtualAddressSh2UpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir1;trivial.
apply H with partition pg pd;trivial.
contradict Hkey;subst;trivial.
contradict Hkey;subst;trivial.
Qed.


Lemma wellFormedFstShadowIfNoneUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
wellFormedFstShadowIfNone s -> 
wellFormedFstShadowIfNone
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
              idxEq |}.
Proof.
intro Hkey.
intros Hlookup.
unfold wellFormedFstShadowIfNone.
intros.
simpl in *.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, In partition (getPartitions pageRootPartition s) 
    -> partition <> table -> StateLib.getPd partition
       (add table idx (PP vaInCurrentPartition) (memory s) pageEq idxEq)
       =  StateLib.getPd partition (memory s)).
{ intros. apply getPdUpdateLLCouplePPVA with entry;trivial.  }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
             idxEq |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateLLCouplePPVA with entry;trivial. }
rewrite Hmap in *;trivial. clear Hmap.
assert(Hsh1 : forall partition, In partition (getPartitions pageRootPartition s) 
    -> partition <> table -> StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (PP vaInCurrentPartition) (memory s) pageEq idxEq)).
{ symmetry. apply getFstShadowUpdateLLCouplePPVA with entry;trivial.  }
rewrite <- Hsh1 in *;trivial. clear Hsh1.
assert(Hgetvir1 : getPDFlag sh1 va s  =
getPDFlag sh1 va {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                idxEq |} ).
symmetry.
apply getPDFlagUpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir1;trivial.
assert(Hgetvir2 : getVirtualAddressSh1 sh1 s va =
getVirtualAddressSh1 sh1 {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                idxEq |} va).
apply getVirtualAddressSh1UpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir2.
apply H with partition pd;trivial.
contradict Hkey;subst;trivial.
contradict Hkey;subst;trivial.
Qed.

Lemma wellFormedFstShadowIfDefaultValuesUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions pageRootPartition s) ->
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
wellFormedFstShadowIfDefaultValues s -> 
wellFormedFstShadowIfDefaultValues
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
              idxEq |}.
Proof.
intro Hkey.
intros Hlookup.
unfold wellFormedFstShadowIfDefaultValues.
intros.
simpl in *.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                 idxEq |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, In partition (getPartitions pageRootPartition s) 
    -> partition <> table -> StateLib.getPd partition
       (add table idx (PP vaInCurrentPartition) (memory s) pageEq idxEq)
       =  StateLib.getPd partition (memory s)).
{ intros.
  apply getPdUpdateLLCouplePPVA with entry;trivial.  }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
             idxEq |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateLLCouplePPVA with entry;trivial. }
rewrite Hmap in *;trivial. clear Hmap.
assert(Hsh1 : forall partition, In partition (getPartitions pageRootPartition s) 
    -> partition <> table -> StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (PP vaInCurrentPartition) (memory s) pageEq idxEq)).
{ symmetry. apply getFstShadowUpdateLLCouplePPVA with entry;trivial.  }
rewrite <- Hsh1 in *;trivial. clear Hsh1.
assert(Hgetvir1 : getPDFlag sh1 va s  =
getPDFlag sh1 va {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                idxEq |} ).
symmetry.
apply getPDFlagUpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir1;trivial.
assert(Hgetvir2 : getVirtualAddressSh1 sh1 s va =
getVirtualAddressSh1 sh1 {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) pageEq
                idxEq |} va).
apply getVirtualAddressSh1UpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir2.
apply H with partition pd;trivial.
contradict Hkey;subst;trivial.
contradict Hkey;subst;trivial.
Qed.

Lemma isAccessibleMappedPageInParentUpdateSh2 s entry v table idx parent va pg:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) -> 
~In table (getAncestors parent s) ->
parent <> table ->
isAccessibleMappedPageInParent parent va pg  s =
isAccessibleMappedPageInParent parent va pg
   {|
  currentPartition := currentPartition s;
  memory := add table idx (PP v) (memory s) pageEq idxEq |}. 
Proof.
set(s':= {| currentPartition := _ |}).
intros.
unfold isAccessibleMappedPageInParent.
assert(Hsh2s: StateLib.getSndShadow parent (memory s) =
StateLib.getSndShadow parent (memory s')).
{ unfold s';simpl;symmetry;
   apply getSndShadowUpdateLLCouplePPVA with entry;trivial. }
rewrite <- Hsh2s. 
case_eq(StateLib.getSndShadow parent (memory s)); [intros sh2 Hsh2|];trivial.
assert(Hgetvir2:  getVirtualAddressSh2 sh2 s va =  getVirtualAddressSh2 sh2 s' va ).
apply getVirtualAddressSh2UpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir2.
case_eq(getVirtualAddressSh2 sh2 s va);[intros vaInParent HvaInParent |];trivial.
assert(Hparents: StateLib.getParent parent (memory s) =
StateLib.getParent parent (memory s')).
{ unfold s';simpl;symmetry;
   apply getParentUpdateLLCouplePPVA with entry;trivial. }
rewrite <- Hparents.
case_eq(StateLib.getParent parent (memory s));[intros ancestor Hancestor|];trivial.
assert(Hancestors:StateLib.getPd ancestor (memory s) =
StateLib.getPd ancestor (memory s')).
{ unfold s';simpl;symmetry;
   apply getPdUpdateLLCouplePPVA with entry;trivial.
   contradict H0.
   unfold getAncestors.
   subst table.
   destruct nbPage;simpl;rewrite Hancestor;simpl;left;trivial. }
rewrite <- Hancestors.
case_eq(  StateLib.getPd ancestor (memory s));[intros pd Hpds|];trivial.

assert(Haccess:getAccessibleMappedPage pd s vaInParent =
getAccessibleMappedPage pd s' vaInParent).
{ unfold s';simpl;symmetry;
   apply getAccessibleMappedPageUpdateLLCouplePPVA with entry;trivial. }
rewrite <- Haccess;trivial.
Qed.

Lemma accessibleChildPageIsAccessibleIntoParentUpdateSh2 s entry v table nextFFI:
lookup table nextFFI  (memory s) pageEq idxEq = Some (PP entry) ->
~ In table (getPartitions pageRootPartition s) ->
parentInPartitionList s ->
isChild s ->
accessibleChildPageIsAccessibleIntoParent s ->
accessibleChildPageIsAccessibleIntoParent
   {|
  currentPartition := currentPartition s;
  memory := add table nextFFI (PP v) (memory s) pageEq idxEq |}. 
Proof.
intros Hlookup Hkey.
set(s':= {| currentPartition := _ |}).
unfold accessibleChildPageIsAccessibleIntoParent.
intros; 
simpl.
assert(Hpartitions : getPartitions pageRootPartition
    s = 
getPartitions pageRootPartition s').
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Haccessmap : forall part, getAccessibleMappedPage part s' va =
getAccessibleMappedPage part s va).
{ intros. apply getAccessibleMappedPageUpdateLLCouplePPVA with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
assert(Hpd :  StateLib.getPd partition (memory s) =
StateLib.getPd partition
   (add table nextFFI (PP v) (memory s) pageEq idxEq)).
{ symmetry.  apply getPdUpdateLLCouplePPVA with entry;trivial.
contradict Hkey;subst;trivial.
 }
rewrite <- Hpd in *.
rewrite <- H1 with  partition va pd accessiblePage;trivial.
symmetry.
apply isAccessibleMappedPageInParentUpdateSh2 with entry;trivial.
contradict Hkey.
apply ancestorInPartitionTree with partition;trivial.
contradict Hkey;subst;trivial.
Qed.

Lemma consistencyUpdateLLCouplePPVA newLastLLable nextFFI v entry s:
StateLib.getMaxIndex <> Some nextFFI -> 
lookup newLastLLable nextFFI (memory s) pageEq idxEq = Some (PP entry)->
~ In newLastLLable (getPartitions pageRootPartition s) ->
consistency s -> consistency {|
  currentPartition := currentPartition s;
  memory := add newLastLLable nextFFI (PP v) (memory s) pageEq idxEq |}.
Proof.
intros Hkey2 Hlookup.
unfold consistency;intuition.
+ apply partitionDescriptorEntryUpdateLLCouplePPVA with entry;trivial.
+ apply dataStructurePdSh1Sh2asRootUpdateLLCouplePPVA with entry;trivial.
+ apply dataStructurePdSh1Sh2asRootUpdateLLCouplePPVA with entry;trivial.
+ apply dataStructurePdSh1Sh2asRootUpdateLLCouplePPVA with entry;trivial.
+ apply currentPartitionInPartitionsListUpdateLLCouplePPVA with entry;trivial.
+ apply noDupMappedPagesListUpdateLLCouplePPVA with entry;trivial.
+ apply noDupConfigPagesListUpdateLLCouplePPVA with entry;trivial.
+ apply parentInPartitionListUpdateLLCouplePPVA with entry;trivial.
+ apply accessibleVAIsNotPartitionDescriptorUpdateLLCouplePPVA with entry;trivial.
+ apply accessibleChildPageIsAccessibleIntoParentUpdateSh2 with entry;trivial.
+ apply noCycleInPartitionTreeUpdateLLCouplePPVA with entry;trivial.
+ apply configTablesAreDifferentUpdateLLCouplePPVA with entry;trivial.
+ apply isChildUpdateLLCouplePPVA with entry;trivial.
+ apply isPresentNotDefaultIffUpdateLLCouplePPVA with entry;trivial.
+ apply physicalPageNotDerivedUpdateLLCouplePPVA with entry;trivial.
+ apply multiplexerWithoutParentUpdateLLCouplePPVA with entry;trivial.
+ apply isParentUpdateLLCouplePPVA with entry;trivial.
+ apply noDupPartitionTreeUpdateLLCouplePPVA with entry;trivial.
+ apply wellFormedFstShadowUpdateLLCouplePPVA with entry;trivial.
+ apply wellFormedSndShadowUpdateLLCouplePPVA with entry;trivial.
+ apply wellFormedShadowsUpdateLLCouplePPVA with entry;trivial.
+ apply wellFormedShadowsUpdateLLCouplePPVA with entry;trivial.
+ apply wellFormedFstShadowIfNoneUpdateLLCouplePPVA with entry;trivial.
+ apply wellFormedFstShadowIfDefaultValuesUpdateLLCouplePPVA with entry;trivial.
Qed.

Lemma isEntryVAExistsUpdateLLCouplePPVA idx ptVaInCurPart table idxvaInCurPart entry s   x:
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
(exists va : vaddr,
       isEntryVA ptVaInCurPart idxvaInCurPart va s/\
        vaddrEq vaddrDefault va = false)
 -> exists va : vaddr,
isEntryVA ptVaInCurPart idxvaInCurPart va 
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |}/\
        vaddrEq vaddrDefault va = false.
Proof.
intros Hentry.
cbn.
intros.
destruct H as (va & Hva & Hx).
exists va;split;trivial.
apply isEntryVAUpdateLLCouplePPVA with entry;trivial.
Qed.
Lemma indirectionDescriptionUpdateLLCouplePPVA    l descChildphy x idx table entry
phyPDChild vaToPrepare  idxroot s:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} in 
lookup table idx (memory s) pageEq idxEq = Some (PP entry) ->
table <> descChildphy ->
indirectionDescription s descChildphy phyPDChild idxroot vaToPrepare l -> 
indirectionDescription s' descChildphy phyPDChild idxroot vaToPrepare l.
Proof.
intros s' Hlookup  Hkey Hind.
unfold indirectionDescription in *.
destruct Hind as (tableroot & Hpp & Hnotdef & Hor).
exists tableroot.
split;trivial.
unfold s'.

rewrite <- nextEntryIsPPUpdateLLCouplePPVA;trivial.
 eassumption.
split;trivial.
destruct Hor as  [(Hroot & Hl) |(nbL & stop& HnbL & Hstop & Hind & Hnotdefind & Hl)].
left;split;trivial.
right.
exists nbL, stop.
intuition.
rewrite <- Hind.
apply getIndirectionUpdateLLCouplePPVA with entry;trivial. 
Qed.

Lemma initPEntryTablePreconditionToPropagatePreparePropertiesUpdateLLCouplePPVA pg
 table idx x v0 s:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} in 
StateLib.getMaxIndex <> Some idx ->             
lookup table idx (memory s) pageEq idxEq = Some (PP v0) ->
~ In table (getPartitions pageRootPartition s) ->
initPEntryTablePreconditionToPropagatePrepareProperties s pg ->
(* isPartitionFalse ptSh1 (StateLib.getIndexOfAddr vaValue fstLevel)  s ->  *)
initPEntryTablePreconditionToPropagatePrepareProperties s' pg.
Proof.
intros s' Hkey2 Hlookup (*   *)Hnotpart (Hgoal & Hnotdef).
unfold initPEntryTablePreconditionToPropagatePrepareProperties.
split;trivial.
intros part Hpart.
assert(Hpartitions: getPartitions pageRootPartition s' = getPartitions pageRootPartition s). (* *)
symmetry. apply getPartitionsUpdateLLCouplePPVA with v0;trivial.
rewrite Hpartitions in *.
assert(Hconf: getConfigPages part s'= getConfigPages part s).
apply getConfigPagesUpdateLLCouplePPVA with v0;trivial.
contradict Hnotpart;subst;trivial.
rewrite Hconf.
apply Hgoal;trivial.
Qed.

Lemma writeAccessibleRecPreparePostconditionUpdateLLCouplePPVA desc  pg
 table idx x v0 s:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} in 
lookup table idx (memory s) pageEq idxEq = Some (PP v0) ->
~ In table (getAncestors desc s) ->
table <> desc ->
(* initPEntryTablePreconditionToPropagatePrepareProperties s pg ->  *)         
writeAccessibleRecPreparePostcondition desc pg s ->
writeAccessibleRecPreparePostcondition desc pg s'.
Proof.
intros s' Hlookup Hnotpart Hnot Hgoal .
unfold writeAccessibleRecPreparePostcondition in *.
intros part Hpart.
assert(Hances: getAncestors desc s' = getAncestors desc s).
apply getAncestorsUpdateLLCouplePPVA with v0;trivial.
rewrite Hances in *;trivial.
assert(Haccess: getAccessibleMappedPages part s' = getAccessibleMappedPages part s). (* *)
 apply getAccessibleMappedPagesUpdateLLCouplePPVA with v0;trivial.
contradict Hnotpart;subst;trivial.
rewrite Haccess.
apply Hgoal;trivial.
Qed.

Lemma isWellFormedMMUTablesUpdateLLCouplePPVA pg
 table idx x v0 s:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} in 
lookup table idx (memory s) pageEq idxEq = Some (PP v0) ->
isWellFormedMMUTables pg s -> isWellFormedMMUTables pg s'.
Proof.
intros s' Hlookup Hgoal.
unfold isWellFormedMMUTables in *.
intros.
generalize (Hgoal idx0);clear Hgoal; intros (Hphy & Hpres).
split.
rewrite <- Hphy.
apply readPhyEntryUpdateLLCouplePPVA with v0;trivial.
rewrite <- Hpres.
apply readPresentUpdateLLCouplePPVA with v0;trivial.
Qed.

Lemma isWellFormedFstShadowTablesUpdateLLCouplePPVA  (* pt idx vaValue v0  partition  *)s nbL phySh1addr x table idx v0:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} in 
lookup table idx (memory s) pageEq idxEq = Some (PP v0) ->
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
apply readPhyEntryUpdateLLCouplePPVA with v0;trivial.
apply readPresentUpdateLLCouplePPVA with v0;trivial.
apply readVirEntryUpdateLLCouplePPVA with v0;trivial.
apply readPDflagUpdateLLCouplePPVA with v0;trivial.
Qed.

Lemma isWellFormedSndShadowTablesUpdateLLCouplePPVA s pg idx  v0 l table  x:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} in 
lookup table idx (memory s) pageEq idxEq = Some (PP v0) ->
isWellFormedSndShadow l pg s -> isWellFormedSndShadow l pg s'.
Proof.
intros s' Hlookup Hgoal.
unfold isWellFormedSndShadow in *.
intros.
destruct Hgoal as [(Hl & Hgoal) |(Hl & Hgoal)];[left|right];split;trivial;intros idx0;
generalize (Hgoal idx0);clear Hgoal;[ intros (Hphy & Hpres)| intros Hphy];
rewrite <- Hphy;[rewrite<-  Hpres;split|].
apply readPhyEntryUpdateLLCouplePPVA with v0;trivial.
apply readPresentUpdateLLCouplePPVA with v0;trivial.
apply readVirtualUpdateLLCouplePPVA with v0;trivial.
Qed.

Lemma newIndirectionsAreNotAccessibleUpdateLLCouplePPVA phyMMUaddr phySh1addr phySh2addr
 table idx x v0 s:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} in            
lookup table idx (memory s) pageEq idxEq = Some (PP v0) ->
~ In table (getPartitions pageRootPartition s) ->
newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr ->
newIndirectionsAreNotAccessible s' phyMMUaddr phySh1addr phySh2addr.
Proof.
intros s'  Hlookup (*   *)Hnotpart Hgoal.
unfold newIndirectionsAreNotAccessible in *.
intros * Hi Hii.
assert(Hpartitions: getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
symmetry. apply getPartitionsUpdateLLCouplePPVA with v0;trivial.
rewrite Hpartitions in *.
assert(Haccess: getAccessibleMappedPages parts s' = getAccessibleMappedPages parts s). (* *)
 apply getAccessibleMappedPagesUpdateLLCouplePPVA with v0;trivial.
contradict Hnotpart;subst;trivial.
rewrite Haccess.
apply Hgoal;trivial.
Qed.

Lemma newIndirectionsAreNotMappedInChildrenUpdateLLCouplePPVA currentPart newIndirection 
 table idx x v0 s:
let s':= {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) pageEq idxEq |} in    
noDupPartitionTree s ->                
In currentPart (getPartitions pageRootPartition s)->                  
lookup table idx (memory s) pageEq idxEq = Some (PP v0) ->
~ In table (getPartitions pageRootPartition s) ->
newIndirectionsAreNotMappedInChildren s currentPart newIndirection->
newIndirectionsAreNotMappedInChildren s' currentPart newIndirection.
Proof.
intros s' Hndup Hpart Hlookup (*   *)Hnotpart Hgoal.
unfold newIndirectionsAreNotMappedInChildren in *.
intros * Hi.
assert(Hpartitions: getChildren currentPart s' = getChildren currentPart s).
symmetry. apply getChildrenUpdateLLCouplePPVA with v0;trivial.
unfold not;intros;subst.
contradiction.
rewrite Hpartitions in *.
assert(Haccess: getMappedPages child s' = getMappedPages child s). (* *)
 apply getMappedPagesUpdateLLCouplePPVA with v0;trivial.
unfold not;intros;subst.
assert( In table  (getPartitions pageRootPartition s)). 
apply childrenPartitionInPartitionList with currentPart;trivial.
contradiction.
rewrite Haccess.
apply Hgoal;trivial.
Qed.


Lemma insertEntryIntoLLPCUpdateLLCouplePPVA s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable
      phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
      descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA
      zeroI lpred newLastLLable nextFFI (* (LLDescChild:page) *) entry fstLL LLChildphy minFI indMMUToPreparebool:
lookup newLastLLable nextFFI (memory s) pageEq idxEq = Some (PP entry) ->
StateLib.getMaxIndex <> Some nextFFI ->  
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable
      phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
      descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA
      zeroI lpred fstLL LLChildphy newLastLLable minFI indMMUToPreparebool->
insertEntryIntoLLPC {|
  currentPartition := currentPartition s;
  memory := add newLastLLable nextFFI (PP phyMMUaddr) (memory s) pageEq idxEq |} ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable
      phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
      descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA
      zeroI lpred fstLL LLChildphy newLastLLable minFI indMMUToPreparebool.
Proof.
intros Hlookup Hkey2.
intros.
set(s':=  {|
     currentPartition := _|}).
assert (HtableinLL: In newLastLLable (getLLPages fstLL s (nbPage + 1))).
unfold insertEntryIntoLLPC, propagatedPropertiesPrepare in *;intuition.
assert(HLL: StateLib.getConfigTablesLinkedList descChildphy (memory s) = Some fstLL).
unfold insertEntryIntoLLPC, propagatedPropertiesPrepare in *;intuition.
assert(Hchildpart:In descChildphy (getPartitions pageRootPartition s)) by (unfold insertEntryIntoLLPC, 
                        propagatedPropertiesPrepare in *;intuition).
assert(Htableinconfig: In newLastLLable (getConfigPages descChildphy s)).
{ apply inGetTrdShadowInConfigPages with fstLL;trivial.
    unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, consistency in *;intuition. }
assert(Htablenotpart : ~ In newLastLLable (getPartitions pageRootPartition s)).
{  apply LLtableNotPartition with descChildphy fstLL;trivial;
unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, consistency in *;intuition. }
assert(Hpartitions : getPartitions pageRootPartition s = getPartitions pageRootPartition s') by (
    eapply getPartitionsUpdateLLCouplePPVA with entry; trivial).    
assert(Hchildren : getChildren currentPart s = getChildren currentPart s'). 
{ apply getChildrenUpdateLLCouplePPVA with entry; trivial.
  unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, consistency in *.
  assert(Hi: In currentPart (getPartitions pageRootPartition s)).
  { intuition;subst;trivial. }
  unfold not;intros;subst.
  now contradict Hi. }
assert(Hnotanc: ~ In newLastLLable (getAncestors (currentPartition s) s)). 
{ contradict Htablenotpart.
  apply ancestorInPartitionTree with (currentPartition s);trivial;unfold insertEntryIntoLLPC, 
  propagatedPropertiesPrepare, consistency in *;intuition. }
assert(Hcurpart: In (currentPartition s) (getPartitions pageRootPartition s)) by
(unfold insertEntryIntoLLPC, 
  propagatedPropertiesPrepare, consistency in *;intuition).
assert(Hnotcurpart: newLastLLable <> currentPartition s) by 
 (contradict Htablenotpart;subst;trivial).
assert(Hnotpartchild: newLastLLable <> descChildphy) by
 (contradict Htablenotpart;subst;trivial).
unfold insertEntryIntoLLPC, propagatedPropertiesPrepare in *;intuition;subst;simpl.
+ apply kernelDataIsolationUpdateLLCouplePPVA with entry ;trivial.
+ apply partitionsIsolationUpdateLLCouplePPVA with entry;trivial; unfold consistency in *;intuition.
+ apply verticalSharingUpdateLLCouplePPVA with entry ;trivial; unfold consistency in *;intuition.
+ apply consistencyUpdateLLCouplePPVA with entry;trivial.
+ apply getTableAddrRootUpdateLLCouplePPVA with entry;trivial.
+ apply isPEUpdateLLCouplePPVA with entry;trivial.
+ apply isEntryVAExistsUpdateLLCouplePPVA with entry;trivial.
+ apply getTableAddrRootUpdateLLCouplePPVA with entry;trivial.
+ apply isVEUpdateLLCouplePPVA   with entry;trivial.
+ apply isEntryPageUpdateLLCouplePPVA with entry;trivial.
+ apply entryPresentFlagUpdateLLCouplePPVA with entry;trivial.
+ apply entryUserFlagUpdateLLCouplePPVA with entry;trivial.
+ apply getTableAddrRootUpdateLLCouplePPVA with entry;trivial.
+ apply isPEUpdateLLCouplePPVA with entry;trivial.
+ apply isEntryVAExistsUpdateLLCouplePPVA with entry;trivial.
+ apply getTableAddrRootUpdateLLCouplePPVA with entry;trivial.
+ apply isVEUpdateLLCouplePPVA   with entry;trivial.
+ apply isEntryVAExistsUpdateLLCouplePPVA with entry;trivial.
+ apply getTableAddrRootUpdateLLCouplePPVA with entry;trivial.
+ apply isVEUpdateLLCouplePPVA   with entry;trivial.
+ apply isEntryPageUpdateLLCouplePPVA with entry;trivial.
+ apply entryPresentFlagUpdateLLCouplePPVA with entry;trivial.
+ apply entryUserFlagUpdateLLCouplePPVA with entry;trivial.
+ apply getTableAddrRootUpdateLLCouplePPVA with entry;trivial.
+ apply isPEUpdateLLCouplePPVA with entry;trivial.
+ apply entryUserFlagUpdateLLCouplePPVA with entry;trivial.
+ apply entryPresentFlagUpdateLLCouplePPVA with entry;trivial.
+ apply isEntryPageUpdateLLCouplePPVA with entry;trivial.
+ apply isEntryPageUpdateLLCouplePPVA with entry;trivial.
+ unfold s'. rewrite <- nextEntryIsPPUpdateLLCouplePPVA with entry;trivial.
+ unfold s'. rewrite <- nextEntryIsPPUpdateLLCouplePPVA with entry;trivial.
+ unfold s'. rewrite <- nextEntryIsPPUpdateLLCouplePPVA with entry;trivial.
+ rewrite <- Hpartitions ;trivial.
+ rewrite <- Hchildren;trivial.
+ unfold indirectionDescriptionAll in *;intuition;
  apply indirectionDescriptionUpdateLLCouplePPVA with entry;trivial.
+ unfold initPEntryTablePreconditionToPropagatePreparePropertiesAll in *;
  intuition; apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateLLCouplePPVA
  with entry;trivial.
+  assert(Hconf: StateLib.getConfigTablesLinkedList descChildphy (memory s) = Some fstLL) by trivial.
  rewrite <- Hconf.
   apply getConfigTablesLinkedListUpdateLLCouplePPVA with entry;trivial.
  intuition.   
+ assert(Hconf: getLLPages fstLL s (nbPage + 1) = getLLPages fstLL s' (nbPage + 1)).
  symmetry.
  apply getLLPagesUpdateLLCouplePPVA;trivial.
  rewrite <- Hconf;trivial.
+ assert(Hconf: getLLPages fstLL s (nbPage + 1) = getLLPages fstLL s' (nbPage + 1)).
  symmetry.
  apply getLLPagesUpdateLLCouplePPVA;trivial.
  rewrite <- Hconf;trivial.
+ assert(exists NbFI : index, isIndexValue newLastLLable (CIndex 1) NbFI s /\ NbFI >= minFI) as (x & Hx & Hx1) by trivial.
  exists x;split;trivial.
  apply isIndexValueUpdateLLCouplePPVA with entry;trivial.
+ unfold writeAccessibleRecPreparePostconditionAll in *;intuition;
  apply writeAccessibleRecPreparePostconditionUpdateLLCouplePPVA with entry;trivial.
+ unfold isWellFormedTables in *; intuition.
  apply isWellFormedMMUTablesUpdateLLCouplePPVA with entry;trivial.
  apply isWellFormedFstShadowTablesUpdateLLCouplePPVA with entry;trivial.
  apply isWellFormedSndShadowTablesUpdateLLCouplePPVA with entry;trivial.
+ apply newIndirectionsAreNotAccessibleUpdateLLCouplePPVA with entry;trivial.
+ unfold newIndirectionsAreNotMappedInChildrenAll in *;intuition.
  apply newIndirectionsAreNotMappedInChildrenUpdateLLCouplePPVA with entry;trivial.
  unfold consistency in *;intuition.
  apply newIndirectionsAreNotMappedInChildrenUpdateLLCouplePPVA with entry;trivial.
  unfold consistency in *;intuition.
  apply newIndirectionsAreNotMappedInChildrenUpdateLLCouplePPVA with entry;trivial.
  unfold consistency in *;intuition.    
+ apply isEntryVAUpdateLLCouplePPVA with entry;trivial.
+ apply isEntryVAUpdateLLCouplePPVA with entry;trivial.
+ apply isEntryVAUpdateLLCouplePPVA with entry;trivial.  
Qed.

Lemma isPP'SameValueUpdateLLCouplePPVA  newLastLLable nextFFI phyMMUaddr s:
isPP' newLastLLable nextFFI phyMMUaddr
  {|
  currentPartition := currentPartition s;
  memory := add newLastLLable nextFFI (PP phyMMUaddr) (memory s) pageEq idxEq |}.
Proof.
unfold isPP'.
simpl.
assert(Hbeqtrue:beqPairs (newLastLLable, nextFFI) (newLastLLable, nextFFI) pageEq idxEq=true)by 
 (apply beqPairsTrue;split;trivial).
rewrite Hbeqtrue;trivial.
Qed.
 
