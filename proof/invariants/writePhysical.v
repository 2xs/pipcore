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

(*
Lemma readVirtualUpdateLLCouplePPVA table1 table2 idx1 idx2  vaInCurrentPartition s :
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
*)

Lemma getConfigTablesLinkedListUpdateLLCouplePPVA partition x table idx (s : state) entry :
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
partition<>table ->
StateLib.getConfigTablesLinkedList partition
  (add table idx (PP x) (memory s) beqPage beqIndex) =
StateLib.getConfigTablesLinkedList partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getConfigTablesLinkedList.
case_eq ( StateLib.Index.succ sh3idx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
assert(Hfalse : beqPairs (table, idx) (partition, i) beqPage beqIndex = false).
apply beqPairsFalse; intuition.
rewrite Hfalse.
assert(Hmemory : lookup partition i (removeDup table idx (memory s) beqPage beqIndex) 
          beqPage beqIndex =  lookup  partition i (memory s) beqPage beqIndex ).
apply removeDupIdentity ; intuition.
rewrite Hmemory.
trivial.
Qed.


Lemma getFstShadowUpdateLLCouplePPVA partition x
table idx (s : state) entry :
partition<>table ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
StateLib.getFstShadow partition
  (add table idx (PP x) (memory s) beqPage beqIndex) =
StateLib.getFstShadow partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getFstShadow.
case_eq ( StateLib.Index.succ sh1idx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
assert(Hfalse : beqPairs (table, idx) (partition, i) beqPage beqIndex = false).
apply beqPairsFalse; intuition.
rewrite Hfalse.
assert(Hmemory : lookup partition i (removeDup table idx (memory s) beqPage beqIndex) 
          beqPage beqIndex =  lookup  partition i (memory s) beqPage beqIndex ).
apply removeDupIdentity ; intuition.
rewrite Hmemory.
trivial.
Qed.

Lemma getSndShadowUpdateLLCouplePPVA partition x
table idx (s : state) entry :
partition<>table ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
StateLib.getSndShadow partition
  (add table idx (PP x) (memory s) beqPage beqIndex) =
StateLib.getSndShadow partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getSndShadow.
case_eq ( StateLib.Index.succ sh2idx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
assert(Hfalse : beqPairs (table, idx) (partition, i) beqPage beqIndex = false).
apply beqPairsFalse; intuition.
rewrite Hfalse.
assert(Hmemory : lookup partition i (removeDup table idx (memory s) beqPage beqIndex) 
          beqPage beqIndex =  lookup  partition i (memory s) beqPage beqIndex ).
apply removeDupIdentity ; intuition.
rewrite Hmemory.
trivial.
Qed.

Lemma getPdUpdateLLCouplePPVA partition x
table idx (s : state) entry :
partition<>table ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
StateLib.getPd partition
  (add table idx (PP x) (memory s) beqPage beqIndex) =
StateLib.getPd partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getPd.
case_eq ( StateLib.Index.succ PDidx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
assert(Hfalse : beqPairs (table, idx) (partition, i) beqPage beqIndex = false).
apply beqPairsFalse; intuition.
rewrite Hfalse.
assert(Hmemory : lookup partition i (removeDup table idx (memory s) beqPage beqIndex) 
          beqPage beqIndex =  lookup  partition i (memory s) beqPage beqIndex ).
apply removeDupIdentity ; intuition.
rewrite Hmemory.
trivial.
Qed.

Lemma getParentUpdateLLCouplePPVA partition x
table idx (s : state) entry :
partition<>table ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
StateLib.getParent partition
  (add table idx (PP x) (memory s) beqPage beqIndex) =
StateLib.getParent partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getParent.
case_eq ( StateLib.Index.succ PPRidx ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn.
assert(Hfalse : beqPairs (table, idx) (partition, i) beqPage beqIndex = false).
apply beqPairsFalse; intuition.
rewrite Hfalse.
assert(Hmemory : lookup partition i (removeDup table idx (memory s) beqPage beqIndex) 
          beqPage beqIndex =  lookup  partition i (memory s) beqPage beqIndex ).
apply removeDupIdentity ; intuition.
rewrite Hmemory.
trivial.
Qed.



Lemma getTablePagesUpdateLLCouplePPVA    table idx entry size p (s : state)  x:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) -> 
getTablePages p size
 {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |} =
getTablePages p size s.
Proof.
revert p .
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
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

Lemma getIndirectionsUpdateLLCouplePPVA  table idx entry pd (s : state) x:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->  
getIndirections pd
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
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
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}= getTablePages pd tableSize s) as Htablepages.
apply getTablePagesUpdateLLCouplePPVA with entry ;trivial.
rewrite Htablepages.
clear Htablepages.
induction (getTablePages pd tableSize s); intros; trivial.
simpl in *.
rewrite IHn. 
f_equal.
apply IHl.
Qed.

Lemma getConfigPagesUpdateLLCouplePPVA s x table idx entry part: 
part <> table ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
 getConfigPages part {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}  = getConfigPages part s.
Proof.
intros.
unfold getConfigPages. 
f_equal.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s)
              beqPage beqIndex |}) in *.
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
admit.
Admitted.


Lemma getIndirectionUpdateLLCouplePPVA sh1 table idx s entry va nbL stop x:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
getIndirection sh1 va nbL stop
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |} =
getIndirection sh1 va nbL stop s .
Proof.
intros Hentry.
revert sh1 nbL.
induction  stop.
+ simpl. trivial.
+ simpl. intros. 
  destruct (StateLib.Level.eqb nbL fstLevel);trivial.
  set (entry0 := (PP x)  ) in *.
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

Lemma readPresentUpdateLLCouplePPVA  idx1
table idx (s : state)  p   entry x: 
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) -> 
StateLib.readPresent p idx1
  (add table idx (PP x) (memory s) beqPage beqIndex) =
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

Lemma readAccessibleUpdateLLCouplePPVA 
table idx (s : state)  p  idx1 entry x: 
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) -> 
StateLib.readAccessible p idx1
  (add table idx (PP x) (memory s) beqPage beqIndex) =
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

Lemma readPhyEntryUpdateLLCouplePPVA 
table idx (s : state)  p  idx1 entry x: 
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) -> 
StateLib.readPhyEntry p idx1
  (add table idx (PP x) (memory s) beqPage beqIndex) =
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

Lemma readVirEntryUpdateLLCouplePPVA 
table idx (s : state)  p  idx1 entry x: 
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) -> 
StateLib.readVirEntry p idx1
  (add table idx (PP x) (memory s) beqPage beqIndex) =
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

Lemma readPDflagUpdateLLCouplePPVA idx1
table idx (s : state)  p   entry x: 
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) -> 
StateLib.readPDflag p idx1
    (add table idx (PP x) (memory s) beqPage beqIndex) =
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

Lemma getMappedPageUpdateLLCouplePPVA root s x table idx va entry:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
getMappedPage root {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}  va = getMappedPage root s va.
Proof.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) beqPage
              beqIndex |}) in *.
intros Hentry. 
unfold getMappedPage.
destruct(StateLib.getNbLevel);intros;trivial.
assert(Hind : getIndirection root va l (nbLevel - 1) s' =
getIndirection root va l (nbLevel - 1) s).
apply getIndirectionUpdateLLCouplePPVA with entry;trivial.
rewrite Hind.  
destruct(getIndirection root va l (nbLevel - 1)  s); intros; trivial.
destruct(defaultPage =? p);trivial.
 assert(Hpresent :    StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
  (memory s) = StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (PP x) (memory s) beqPage beqIndex) ).
symmetry.
apply readPresentUpdateLLCouplePPVA with entry; trivial.
unfold s'. simpl.
rewrite <- Hpresent.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) ); trivial.
destruct b; trivial.
assert(Heq :StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (PP x) (memory s) beqPage beqIndex) =
   StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s) );intros.
apply readPhyEntryUpdateLLCouplePPVA  with entry; trivial .
rewrite Heq;trivial.
Qed.

Lemma getAccessibleMappedPageUpdateLLCouplePPVA root s x table idx va entry:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
getAccessibleMappedPage root {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}  va = getAccessibleMappedPage root s va.
Proof.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) beqPage
              beqIndex |}) in *.
intros Hentry. 
unfold getAccessibleMappedPage.
destruct(StateLib.getNbLevel);intros;trivial.
assert(Hind : getIndirection root va l (nbLevel - 1) s' =
getIndirection root va l (nbLevel - 1) s).
apply getIndirectionUpdateLLCouplePPVA with entry;trivial.
rewrite Hind.  
destruct(getIndirection root va l (nbLevel - 1)  s); intros; trivial.
destruct(defaultPage =? p);trivial.
 assert(Hpresent :    StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
  (memory s) = StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (PP x) (memory s) beqPage beqIndex) ).
symmetry.
apply readPresentUpdateLLCouplePPVA with entry; trivial.
unfold s'. simpl.
rewrite <- Hpresent.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) ); trivial.
destruct b; trivial.
assert(Haccess :    StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel)
  (memory s) = StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (PP x) (memory s) beqPage beqIndex) ).
symmetry.
apply readAccessibleUpdateLLCouplePPVA with entry; trivial.
unfold s'. simpl.
rewrite <- Haccess.
destruct(StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel) (memory s) ); trivial.
destruct b; trivial.
assert(Heq :StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (PP x) (memory s) beqPage beqIndex) =
   StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s) );intros.
apply readPhyEntryUpdateLLCouplePPVA  with entry; trivial .
rewrite Heq;trivial.
Qed.

Lemma getMappedPagesAuxUpdateLLCouplePPVA root s x table idx entry l:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
getMappedPagesAux root l {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |} = 
getMappedPagesAux root l s.
Proof.
intros Hentry.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) beqPage
              beqIndex |}) in *.
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
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
getAccessibleMappedPagesAux root l {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |} = 
getAccessibleMappedPagesAux root l s.
Proof.
intros Hentry.
set (s':= {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) beqPage
              beqIndex |}) in *.
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
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
 getMappedPages part {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}  = getMappedPages part s.
Proof.
intros.
unfold getMappedPages.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s)
              beqPage beqIndex |}) in *.
assert(Hgetpd: StateLib.getPd part (memory s') = StateLib.getPd part (memory s)).
{ apply getPdUpdateLLCouplePPVA with entry;trivial.  }
rewrite Hgetpd.
case_eq(StateLib.getPd part (memory s));intros; trivial.
apply getMappedPagesAuxUpdateLLCouplePPVA with entry;trivial.
Qed.

Lemma getAccessibleMappedPagesUpdateLLCouplePPVA s x table idx entry part: 
part <> table ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
getAccessibleMappedPages part {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}  = getAccessibleMappedPages part s.
Proof.
intros.
unfold getAccessibleMappedPages.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s)
              beqPage beqIndex |}) in *.
assert(Hgetpd: StateLib.getPd part (memory s') = StateLib.getPd part (memory s)).
{ apply getPdUpdateLLCouplePPVA with entry;trivial.  }
rewrite Hgetpd.
case_eq(StateLib.getPd part (memory s));intros; trivial.
apply getAccessibleMappedPagesAuxUpdateLLCouplePPVA with entry;trivial.
Qed.

Lemma checkChildUpdateLLCouplePPVA s x table idx entry l va part: 
part <> table ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
checkChild part l {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |} va = checkChild part l s va.
Proof.
intro.
intros Hentry.
unfold checkChild.
simpl.
assert(Hsh1 : getFstShadow part
    (add table idx (PP x) (memory s) beqPage beqIndex)=
    getFstShadow part (memory s)). 
{ apply getFstShadowUpdateLLCouplePPVA with entry; trivial. }
rewrite Hsh1.
destruct(getFstShadow part (memory s) );trivial.
assert(Hind : getIndirection p va l (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx (PP x) (memory s) beqPage
                beqIndex |} = getIndirection p va l (nbLevel - 1)
    s).
apply getIndirectionUpdateLLCouplePPVA with entry;trivial.
rewrite Hind.
destruct (getIndirection p va l (nbLevel - 1) s );trivial.
destruct (p0 =? defaultPage);trivial.
assert(Hpdflag :  StateLib.readPDflag p0 (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (PP x) (memory s) beqPage beqIndex) =
   StateLib.readPDflag p0 (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
  apply readPDflagUpdateLLCouplePPVA with entry;trivial.
rewrite Hpdflag.
trivial.
Qed.

Lemma getPdsVAddrUpdateLLCouplePPVA s x table idx entry l part: 
part <> table ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
 getPdsVAddr part l getAllVAddrWithOffset0 {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}  = getPdsVAddr part l getAllVAddrWithOffset0 s.
Proof.
intros.
unfold getPdsVAddr.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s)
              beqPage beqIndex |}) in *.
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
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) -> 
getChildren part s = 
getChildren part{|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}.
Proof.
intro.
intros Hentry.
unfold getChildren.
set (s' := {|
             currentPartition := currentPartition s;
             memory := add table idx (PP x) (memory s)
                         beqPage beqIndex |}) in *.
intros. 
destruct ( StateLib.getNbLevel);trivial.
simpl.
assert(Hpd :  StateLib.getPd part (memory s) =
StateLib.getPd part
    (add table idx (PP x) (memory s) beqPage beqIndex)).
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
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) -> 
~In table (getPartitions multiplexer s) ->
getPartitions multiplexer s = getPartitions multiplexer{|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}. 
Proof.
intro.
generalize multiplexer at 1 2 3.
unfold getPartitions.
set(s':=  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s)
              beqPage beqIndex |}) in *.
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

Lemma isVAUpdateLLCouplePPVA idx partition table entry idxroot s x:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
isVA partition idxroot s -> 
isVA partition idxroot
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
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


Lemma isPEUpdateLLCouplePPVA idx partition table  entry idxroot s x:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
isPE partition idxroot s -> 
isPE partition idxroot
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
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

Lemma isVEUpdateLLCouplePPVA idx partition table  entry idxroot s x:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
isVE partition idxroot s -> 
isVE partition idxroot
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
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


Lemma entryUserFlagUpdateLLCouplePPVA idx ptVaInCurPartpd idxvaInCurPart table 
 entry s x accessiblesrc:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
entryUserFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc s -> 
entryUserFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
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

Lemma entryPresentFlagUpdateLLCouplePPVA idx ptVaInCurPartpd idxvaInCurPart table 
 entry s x accessiblesrc:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
entryPresentFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc s -> 
entryPresentFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
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

Lemma entryPDFlagUpdateLLCouplePPVA idx ptDescChild table idxDescChild entry s x flag:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
entryPDFlag ptDescChild idxDescChild flag s -> 
entryPDFlag ptDescChild idxDescChild flag
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
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

Lemma isEntryVAUpdateLLCouplePPVA idx ptVaInCurPart table idxvaInCurPart entry s  vainve x:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
isEntryVA ptVaInCurPart idxvaInCurPart vainve s -> 
isEntryVA ptVaInCurPart idxvaInCurPart vainve
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
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

Lemma isEntryPageUpdateLLCouplePPVA idx ptVaInCurPart table idxvaInCurPart entry s  vainve x:
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
isEntryPage ptVaInCurPart idxvaInCurPart vainve s -> 
isEntryPage ptVaInCurPart idxvaInCurPart vainve
  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
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

Lemma partitionsIsolationUpdateLLCouplePPVA s x table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
partitionsIsolation s ->
~ In table (getPartitions multiplexer s)  ->
noDupPartitionTree s ->
partitionsIsolation {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup Hisopart.
intros.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}) in *. 
unfold partitionsIsolation in *. 
intros (* Hisopart *) parent child1 child2 Hparent Hchild1 Hchild2 Hdist.
assert(Hparts : getPartitions multiplexer s = getPartitions multiplexer s').
apply getPartitionsUpdateLLCouplePPVA with entry;trivial.
rewrite <- Hparts in *;trivial.  
  assert (Hused :  forall part, In part (getPartitions multiplexer s) 
    -> part <> table -> getUsedPages part s' = getUsedPages part s). 
  { intros. 
    unfold getUsedPages in *. 
    assert(Hconfig : forall part, In part (getPartitions multiplexer s) 
    -> part <> table -> getConfigPages part s' = getConfigPages part s).
    { intros.
      apply getConfigPagesUpdateLLCouplePPVA with entry;trivial. } 
    rewrite Hconfig in *.
    f_equal.
    assert(Hmap :  forall part, In part (getPartitions multiplexer s) 
    -> part <> table -> getMappedPages part s' = getMappedPages part s).
    { intros.
      apply getMappedPagesUpdateLLCouplePPVA with entry;trivial. } 
    rewrite Hmap in *;trivial. trivial. trivial. }    
  assert(Hchildren : getChildren parent s = getChildren parent s').
  apply getChildrenUpdateLLCouplePPVA with entry;trivial.
  contradict H;subst;trivial.
  rewrite <- Hchildren in *. clear Hchildren.
  assert( In child1 (getPartitions multiplexer s)).
  apply childrenPartitionInPartitionList with parent;trivial.
  assert( In child2 (getPartitions multiplexer s)).
  apply childrenPartitionInPartitionList with parent;trivial.
  rewrite Hused;trivial.
  rewrite Hused;trivial.
  apply Hisopart with parent;trivial.
  contradict H2;subst;trivial.
  contradict H1;subst;trivial.
Qed.

Lemma kernelDataIsolationUpdateLLCouplePPVA s x table idx entry: 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
kernelDataIsolation s ->
kernelDataIsolation {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}. 
Proof.
intro.
intros Hlookup.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}) in *. 
unfold kernelDataIsolation in *. 
intros Hkdi partition1 partition2 Hpart1 Hpart2.
assert(Hparts : getPartitions multiplexer s = getPartitions multiplexer s').
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
~ In table (getPartitions multiplexer s) ->
noDupPartitionTree s ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
verticalSharing s ->
verticalSharing {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}. 
Proof.
intros H H0.
intros Hlookup.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}) in *. 
unfold verticalSharing in *.
intros Hvs parent child Hparent Hchild.
assert(Hparts : getPartitions multiplexer s = getPartitions multiplexer s').
apply getPartitionsUpdateLLCouplePPVA with entry;trivial.
rewrite <- Hparts in *;trivial. clear Hparts.
assert(Hchildren : getChildren parent s = getChildren parent s').
apply getChildrenUpdateLLCouplePPVA with entry;trivial.
contradict H;subst;trivial.
rewrite <- Hchildren in *. clear Hchildren.
assert(Hmap :  forall part, In part (getPartitions multiplexer s) 
    -> part <> table -> getMappedPages part s' = getMappedPages part s).
{ intros.
  apply getMappedPagesUpdateLLCouplePPVA with entry;trivial. } 
  rewrite Hmap in *;trivial.
assert (Hused : forall part, In part (getPartitions multiplexer s) 
    -> part <> table -> getUsedPages part s' = getUsedPages part s). 
{ intros. 
  unfold getUsedPages in *. 
  assert(Hconfig : forall part, In part (getPartitions multiplexer s) 
    -> part <> table -> getConfigPages part s' = getConfigPages part s).
  { intros.
    apply getConfigPagesUpdateLLCouplePPVA with entry;trivial. } 
  rewrite Hconfig in *;trivial.
  rewrite Hmap;trivial.  }
assert(In child (getPartitions multiplexer s)) by (apply childrenPartitionInPartitionList with parent;trivial).
rewrite Hused;trivial.
apply Hvs;trivial.
contradict H;subst;trivial.
contradict H;subst;trivial.
Qed.

Lemma partitionDescriptorEntryUpdateLLCouplePPVA s x table idx entry: 
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
~ In table (getPartitions multiplexer s) ->
partitionDescriptorEntry s ->
partitionDescriptorEntry {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup Hkey.
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
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
apply getPartitionsUpdateLLCouplePPVA with entry;trivial.
rewrite <- Hparts in *;trivial. clear Hparts.
assert (HPP : forall p idx, isPP p idx s -> isPP p idx s').
{ intros.
 (*  apply  isPPUpdateLLCouplePPVA with entry;trivial. *) admit. }
assert (HPE : forall p idx x, nextEntryIsPP p idx x s -> 
            nextEntryIsPP   p idx x s').
{ intros. admit. }
admit. (*
assert(Hconcl : idxroot < tableSize - 1 /\
       isPP part idxroot s /\
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
Qed. *)
Admitted.


Lemma currentPartitionInPartitionsListUpdateLLCouplePPVA s x table idx entry : 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
currentPartitionInPartitionsList s ->
currentPartitionInPartitionsList {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
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
     memory := add table idx (PP x) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions;trivial.
Qed.

Lemma noDupMappedPagesListUpdateLLCouplePPVA s x table idx entry : 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
noDupMappedPagesList s ->
noDupMappedPagesList {|
currentPartition := currentPartition s;
memory := add table idx (PP x)
            (memory s) beqPage beqIndex |}. 
Proof.
intro Hkey.
intros Hlookup.
unfold noDupMappedPagesList.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP x) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hmap :  forall part, In part (getPartitions multiplexer s) 
    -> part <> table -> getMappedPages part {|
     currentPartition := currentPartition s;
     memory := add table idx (PP x) (memory s) beqPage
                 beqIndex |}= getMappedPages part s).
{ intros.
  apply getMappedPagesUpdateLLCouplePPVA with entry;trivial.
 }
  rewrite Hmap;trivial.
apply H;trivial.
  contradict Hkey;subst;trivial.
Qed.

Lemma noDupConfigPagesListUpdateLLCouplePPVA s x table idx entry : 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
noDupConfigPagesList s ->
noDupConfigPagesList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) beqPage
              beqIndex |}. 
Proof.
intro Hkey.
intros Hlookup.
unfold noDupConfigPagesList.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP x) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hind :   forall part, In part (getPartitions multiplexer s) 
    -> part <> table ->  getConfigPages part {|
     currentPartition := currentPartition s;
     memory := add table idx (PP x) (memory s) beqPage
                 beqIndex |}= getConfigPages part s).
{ intros.
  apply getConfigPagesUpdateLLCouplePPVA with entry;trivial. }
  rewrite Hind;trivial.
apply H ;trivial.
contradict Hkey;subst;trivial.
Qed. 

Lemma parentInPartitionListUpdateLLCouplePPVA s x table idx entry : 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
parentInPartitionList s ->
parentInPartitionList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) beqPage
              beqIndex |}. 
Proof.
intro Hkey.
intros Hlookup.
unfold parentInPartitionList.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP x) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
apply H with partition;trivial.
admit. (* 
rewrite nextEntryIsPPUpdateLLCouplePPVA with entry;trivial.
eapply H1.
eapply Hlookup. *)
Admitted. 

Lemma getPDFlagUpdateLLCouplePPVA s x table idx entry sh1 va: 
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
getPDFlag sh1 va
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) beqPage
              beqIndex |} = getPDFlag sh1 va s.
Proof.
intros Hentry.
unfold getPDFlag.
simpl.
destruct (StateLib.getNbLevel);trivial.
assert(Hind : getIndirection sh1 va l (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx (PP x) (memory s) beqPage
                beqIndex |} = getIndirection  sh1 va l (nbLevel - 1)
    s).
apply getIndirectionUpdateLLCouplePPVA with entry;trivial.
rewrite Hind.
destruct (getIndirection  sh1 va l (nbLevel - 1) s );trivial.
destruct (p =? defaultPage);trivial.
assert(Hpdflag :  StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel)
    (add table idx (PP x) (memory s) beqPage beqIndex) =
   StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
  apply readPDflagUpdateLLCouplePPVA with entry;trivial.
rewrite Hpdflag.
trivial.
Qed. 

Lemma accessibleVAIsNotPartitionDescriptorUpdateLLCouplePPVA s x table idx entry : 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
accessibleVAIsNotPartitionDescriptor s ->
accessibleVAIsNotPartitionDescriptor
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s) beqPage
              beqIndex |}. 
Proof.
intro Hkey.
intros Hlookup.
unfold accessibleVAIsNotPartitionDescriptor.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP x) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Haccessmap : forall part, getAccessibleMappedPage part {|
       currentPartition := currentPartition s;
       memory := add table idx (PP x) (memory s) beqPage
                   beqIndex |} va =
getAccessibleMappedPage part s va).
{ intros. apply getAccessibleMappedPageUpdateLLCouplePPVA with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
assert(Hpd :  StateLib.getPd partition (memory s) =
StateLib.getPd partition
    (add table idx (PP x) (memory s) beqPage beqIndex)).
{ symmetry. apply getPdUpdateLLCouplePPVA with entry;trivial. 
contradict Hkey;subst;trivial.  }
rewrite <- Hpd in *.
assert(Hsh1 :  StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (PP x) (memory s) beqPage beqIndex)).
{ symmetry. apply getFstShadowUpdateLLCouplePPVA with entry;trivial.
contradict Hkey;subst;trivial.  }
rewrite <- Hsh1 in *.
rewrite <- H with partition va pd sh1 page;trivial.
apply getPDFlagUpdateLLCouplePPVA with entry;trivial.
Qed. 

Lemma readVirtualUpdateLLCouplePPVA table1 table2 idx1 idx2  x s :
table1 <> table2 \/ idx1 <> idx2 -> 
 StateLib.readVirtual table1 idx1
         (add table2 idx2 (PP x) (memory s) beqPage
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


Lemma wellFormedShadowsUpdateLLCouplePPVA s vaInCurrentPartition table idx entry idxroot: 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP  entry) ->
wellFormedShadows idxroot s -> 
wellFormedShadows idxroot
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP  vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hkey.
intros Hlookup.
unfold wellFormedShadows.
intros.
simpl in *.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, In partition (getPartitions multiplexer s) 
    -> partition <> table -> StateLib.getPd partition
       (add table idx (PP  vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros.
  apply getPdUpdateLLCouplePPVA with entry;trivial. }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hpp : nextEntryIsPP partition idxroot structroot s ). 
(* rewrite nextEntryIsPPUpdateLLCouplePPVA with entry;trivial.
eassumption. *) 
trivial.
admit.
assert(Hind : forall root, getIndirection root va nbL stop
    {|
    currentPartition := currentPartition s;
    memory := add table idx (PP  vaInCurrentPartition) (memory s) beqPage
                beqIndex |} = getIndirection  root va nbL stop
    s).
    { intros. apply getIndirectionUpdateLLCouplePPVA with entry;trivial. }
assert(Hgoal :  exists indirection2 : page,
      getIndirection structroot va nbL stop s = Some indirection2 /\
      (defaultPage =? indirection2) = false). 
{ apply H with partition pdroot indirection1;trivial.
  rewrite <- Hind;trivial. }
destruct Hgoal as (indirection2 & Hind1 & Hindnotnul).
exists indirection2;split;trivial.
rewrite <- Hind1.
apply Hind;trivial.
contradict Hkey;subst;trivial.
Admitted.

Lemma getTableAddrRootUpdateLLCouplePPVA s vaInCurrentPartition table idx entry  idxroot 
ptDescChild descChild currentPart: 
lookup table idx (memory s) beqPage beqIndex = Some (PP  entry) ->
getTableAddrRoot ptDescChild idxroot currentPart descChild  s-> 
getTableAddrRoot ptDescChild idxroot currentPart descChild
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP  vaInCurrentPartition) (memory s)
              beqPage beqIndex |}.
Proof.
intros Hlookup.
unfold getTableAddrRoot.
intros Hcond.
destruct Hcond as(Hi & Hcond).
split;trivial.
intros. 
assert(Hpp : nextEntryIsPP currentPart idxroot tableroot s ). 
(* rewrite nextEntryIsPPUpdateLLCouplePPVA with entry;trivial. *) admit.
(* eassumption. *)
trivial.
apply Hcond in Hpp.
destruct Hpp as (nbL & HnbL & stop & Hstop & Hind). 
exists nbL. 
split;trivial.
exists stop.
split;trivial. 
rewrite <- Hind.
apply getIndirectionUpdateLLCouplePPVA with entry;trivial.
Admitted.

Lemma getAncestorsUpdateLLCouplePPVA s x table idx entry partition: 
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
table <> partition ->
~ In table  (getAncestors partition s) ->
getAncestors partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP x) (memory s)
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
    (add table idx (PP x) (memory s) beqPage
       beqIndex) = getParent partition (memory s)).
{  apply getParentUpdateLLCouplePPVA with entry;trivial.
intuition. }
rewrite Hparent.
destruct (getParent partition (memory s) );trivial.
f_equal.
simpl in *.
apply not_or_and in H0.
intuition.
Qed.

Lemma noCycleInPartitionTreeUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP  entry) ->
parentInPartitionList s ->
isChild s ->
noCycleInPartitionTree s -> 
noCycleInPartitionTree
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP  vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hkey.
intros Hlookup.
unfold noCycleInPartitionTree.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP  vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hancestor :getAncestors partition
          {|
          currentPartition := currentPartition s;
          memory := add table idx (PP  vaInCurrentPartition) (memory s)
                      beqPage beqIndex |} =
                      getAncestors partition s).
apply getAncestorsUpdateLLCouplePPVA with entry;trivial.
contradict Hkey;subst;trivial.
contradict Hkey.
apply ancestorInPartitionTree with partition;trivial.
rewrite Hancestor in *.
apply H1;trivial.
Qed.

Lemma configTablesAreDifferentUpdateLLCouplePPVA s vaInCurrentPartition table idx entry :
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP  entry) ->
configTablesAreDifferent s -> 
configTablesAreDifferent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intro Hkey.
intros Hlookup.
unfold configTablesAreDifferent.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hconfig : forall part, In part (getPartitions multiplexer s) 
    -> part <> table -> getConfigPages part {|
          currentPartition := currentPartition s;
          memory := add table idx (PP vaInCurrentPartition) (memory s)
                      beqPage beqIndex |} = getConfigPages part s).
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
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
parentInPartitionList s ->
isChild s -> 
isChild
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intro Hkey.
intros Hlookup.
unfold isChild.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hparent : getParent partition
    (add table idx (PP vaInCurrentPartition) (memory s) beqPage
       beqIndex) = getParent partition (memory s)).
{ apply getParentUpdateLLCouplePPVA with entry;trivial. contradict Hkey;subst;trivial.  }
assert(Hchildren : forall part, In part (getPartitions multiplexer s) 
    -> part <> table -> getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                 beqIndex |} = getChildren part s).
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
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
isPresentNotDefaultIff s -> 
isPresentNotDefaultIff
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold isPresentNotDefaultIff.
intros; 
simpl.
 assert(Hpresent :    StateLib.readPresent table0 idx0
  (memory s) = StateLib.readPresent table0 idx0
    (add table idx (PP vaInCurrentPartition) (memory s) beqPage beqIndex) ).
symmetry.
apply readPresentUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpresent.
 assert(Hread :    StateLib.readPhyEntry table0 idx0
  (memory s) = StateLib.readPhyEntry table0 idx0
    (add table idx (PP vaInCurrentPartition) (memory s) beqPage beqIndex) ).
symmetry.
apply readPhyEntryUpdateLLCouplePPVA with entry;trivial.
rewrite <- Hread.
apply H.
Qed.

Lemma getVirtualAddressSh1UpdateLLCouplePPVA  s vaInCurrentPartition table idx entry p va: 
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
getVirtualAddressSh1 p s va  =
getVirtualAddressSh1 p {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va.
Proof.
intros Hlookup.
unfold getVirtualAddressSh1.
destruct (StateLib.getNbLevel);trivial.
assert(Hind : getIndirection p va l (nbLevel - 1)
{|
currentPartition := currentPartition s;
memory := add table idx  (PP vaInCurrentPartition) (memory s) beqPage
            beqIndex |} = getIndirection  p va l  (nbLevel - 1)
s).
{ apply getIndirectionUpdateLLCouplePPVA with entry;trivial. }
rewrite Hind.
case_eq (getIndirection  p va l  (nbLevel - 1) s );
[ intros tbl Htbl | intros Htbl]; trivial.
case_eq (defaultPage =? tbl);trivial.
intros Htblnotnul.
simpl.
symmetry.
apply readVirEntryUpdateLLCouplePPVA with entry;trivial.
Qed.
                
Lemma isDerivedUpdateLLCouplePPVA  s vaInCurrentPartition table idx entry parent va: 
~ In table (getPartitions multiplexer s) ->
In parent (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
isDerived parent va s ->  isDerived parent va  {|
       currentPartition := currentPartition s;
       memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                   beqIndex |}
       . 
Proof.
intros Hkey Hpart.
intros Hlookup.
unfold isDerived.
simpl.
assert(Hsh1 :  StateLib.getFstShadow parent (memory s) =
StateLib.getFstShadow parent
    (add table idx (PP vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry. apply getFstShadowUpdateLLCouplePPVA with entry;trivial.
contradict Hkey;subst;trivial.   }
rewrite <- Hsh1 in *.
destruct (getFstShadow parent (memory s));trivial.
assert(Hgetvir1 : getVirtualAddressSh1 p s va  =
getVirtualAddressSh1 p {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va ).
apply getVirtualAddressSh1UpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir1;trivial.
Qed.
 
Lemma physicalPageNotDerivedUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
noDupPartitionTree s ->
physicalPageNotDerived s -> 
physicalPageNotDerived
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intro Hkey.
intros Hlookup.
unfold physicalPageNotDerived.
intros; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hchildren : forall part, In part (getPartitions multiplexer s) 
    -> part <> table -> getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                 beqIndex |} = getChildren part s).
{ intros.
symmetry.
apply getChildrenUpdateLLCouplePPVA with entry;trivial. } 
rewrite Hchildren in *.
clear Hchildren.
assert(Hpd : forall partition, In partition (getPartitions multiplexer s) 
    -> partition <> table -> StateLib.getPd partition
       (add table idx (PP vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros.
 apply getPdUpdateLLCouplePPVA with entry;trivial. }
rewrite Hpd in *. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
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
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
~ In table (getPartitions multiplexer s) ->
multiplexerWithoutParent s -> 
multiplexerWithoutParent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intros Hlookup.
unfold multiplexerWithoutParent.
intros; 
simpl.

assert(Hparent : getParent multiplexer
    (add table idx (PP vaInCurrentPartition) (memory s) beqPage
       beqIndex) = getParent multiplexer (memory s)).
{ apply getParentUpdateLLCouplePPVA with entry;trivial. 
  unfold getPartitions in *.
  destruct nbPage;simpl in *;  apply not_or_and in H;  intuition.
   }
rewrite Hparent in *.
trivial.
Qed.

Lemma isParentUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
noDupPartitionTree s ->
isParent s -> 
isParent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intro Hkey.
intros Hlookup.
unfold isParent.
intros.
simpl in *. 
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Hchildren : forall part, In part (getPartitions multiplexer s) 
    -> part <> table -> getChildren part
     {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                 beqIndex |} = getChildren part s).
{ intros.
symmetry.
apply getChildrenUpdateLLCouplePPVA with entry;trivial. } 
rewrite Hchildren in *;trivial.
assert(Hparent : getParent partition
    (add table idx (PP vaInCurrentPartition) (memory s) beqPage
       beqIndex) = getParent partition (memory s)).
{ apply getParentUpdateLLCouplePPVA with entry;trivial.
assert(Hpart: In partition (getPartitions multiplexer s)).
apply childrenPartitionInPartitionList with parent;trivial.
contradict Hkey;subst;trivial. }
rewrite Hparent in *;trivial.
apply H0; trivial.
contradict Hkey;subst;trivial.
Qed.

Lemma noDupPartitionTreeUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
noDupPartitionTree s -> 
noDupPartitionTree
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intro Hkey.
intros Hlookup.
unfold noDupPartitionTree.
intros.
simpl in *.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
Qed.
 
Lemma wellFormedFstShadowUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
wellFormedFstShadow s -> 
wellFormedFstShadow
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intro Hkey.
intros Hlookup.
unfold wellFormedFstShadow.
intros.
simpl in *.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, In partition (getPartitions multiplexer s) 
    -> partition <> table -> StateLib.getPd partition
       (add table idx (PP vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros. apply getPdUpdateLLCouplePPVA with entry;trivial.  }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateLLCouplePPVA with entry;trivial. }
rewrite Hmap in *;trivial. clear Hmap.
assert(Hsh1 :  forall partition, In partition (getPartitions multiplexer s) 
    -> partition <> table -> StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (PP vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry. apply getFstShadowUpdateLLCouplePPVA with entry;trivial.  }
rewrite <- Hsh1 in *;trivial. clear Hsh1.
assert(Hgetvir1 : getVirtualAddressSh1 sh1 s va  =
getVirtualAddressSh1 sh1 {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va ).
apply getVirtualAddressSh1UpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir1;trivial.
apply H with partition pg pd;trivial.
contradict Hkey;subst;trivial.
contradict Hkey;subst;trivial.
Qed.

Lemma wellFormedFstShadowIfNoneUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
wellFormedFstShadowIfNone s -> 
wellFormedFstShadowIfNone
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intro Hkey.
intros Hlookup.
unfold wellFormedFstShadowIfNone.
intros.
simpl in *.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, In partition (getPartitions multiplexer s) 
    -> partition <> table -> StateLib.getPd partition
       (add table idx (PP vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros. apply getPdUpdateLLCouplePPVA with entry;trivial.  }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateLLCouplePPVA with entry;trivial. }
rewrite Hmap in *;trivial. clear Hmap.
assert(Hsh1 : forall partition, In partition (getPartitions multiplexer s) 
    -> partition <> table -> StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (PP vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry. apply getFstShadowUpdateLLCouplePPVA with entry;trivial.  }
rewrite <- Hsh1 in *;trivial. clear Hsh1.
assert(Hgetvir1 : getPDFlag sh1 va s  =
getPDFlag sh1 va {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                beqIndex |} ).
symmetry.
apply getPDFlagUpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir1;trivial.
assert(Hgetvir2 : getVirtualAddressSh1 sh1 s va =
getVirtualAddressSh1 sh1 {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va).
apply getVirtualAddressSh1UpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir2.
apply H with partition pd;trivial.
contradict Hkey;subst;trivial.
contradict Hkey;subst;trivial.
Qed.

Lemma wellFormedFstShadowIfDefaultValuesUpdateLLCouplePPVA s vaInCurrentPartition table idx entry : 
~ In table (getPartitions multiplexer s) ->
lookup table idx (memory s) beqPage beqIndex = Some (PP entry) ->
wellFormedFstShadowIfDefaultValues s -> 
wellFormedFstShadowIfDefaultValues
  {|
  currentPartition := currentPartition s;
  memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
              beqIndex |}.
Proof.
intro Hkey.
intros Hlookup.
unfold wellFormedFstShadowIfDefaultValues.
intros.
simpl in *.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer {|
     currentPartition := currentPartition s;
     memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                 beqIndex |}).
apply getPartitionsUpdateLLCouplePPVA with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Hpd : forall partition, In partition (getPartitions multiplexer s) 
    -> partition <> table -> StateLib.getPd partition
       (add table idx (PP vaInCurrentPartition) (memory s) beqPage beqIndex)
       =  StateLib.getPd partition (memory s)).
{ intros.
  apply getPdUpdateLLCouplePPVA with entry;trivial.  }
rewrite Hpd in *;trivial. clear Hpd.
assert(Hmap : forall pd va,  getMappedPage pd
 {| currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
             beqIndex |} va = getMappedPage pd s va ).
{ intros. apply getMappedPageUpdateLLCouplePPVA with entry;trivial. }
rewrite Hmap in *;trivial. clear Hmap.
assert(Hsh1 : forall partition, In partition (getPartitions multiplexer s) 
    -> partition <> table -> StateLib.getFstShadow partition (memory s) =
StateLib.getFstShadow partition
    (add table idx (PP vaInCurrentPartition) (memory s) beqPage beqIndex)).
{ symmetry. apply getFstShadowUpdateLLCouplePPVA with entry;trivial.  }
rewrite <- Hsh1 in *;trivial. clear Hsh1.
assert(Hgetvir1 : getPDFlag sh1 va s  =
getPDFlag sh1 va {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                beqIndex |} ).
symmetry.
apply getPDFlagUpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir1;trivial.
assert(Hgetvir2 : getVirtualAddressSh1 sh1 s va =
getVirtualAddressSh1 sh1 {|
    currentPartition := currentPartition s;
    memory := add table idx (PP vaInCurrentPartition) (memory s) beqPage
                beqIndex |} va).
apply getVirtualAddressSh1UpdateLLCouplePPVA with entry;trivial.
rewrite <- Hgetvir2.
apply H with partition pd;trivial.
contradict Hkey;subst;trivial.
contradict Hkey;subst;trivial.
Qed.


