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
    This file contains required lemmas to prove that updating the first shadow 
    structure preserves isolation and consistency properties  *)

Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Internal.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.InternalLemmas
               Pip.Proof.Isolation Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Invariants PropagatedProperties UpdateMappedPageContent.
Require Import Coq.Logic.ProofIrrelevance Lia List Bool EqNat Compare_dec.

Lemma getPdAddDerivation partition (descChild : vaddr) 
table idx (s : state) entry flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->
StateLib.getPd partition
  (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) =
StateLib.getPd partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getPd.
case_eq ( StateLib.Index.succ idxPageDir ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  partition i   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma getFstShadowAddDerivation partition (descChild : vaddr) 
table idx (s : state) entry flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->
StateLib.getFstShadow partition
  (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) =
StateLib.getFstShadow partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getFstShadow.
case_eq ( StateLib.Index.succ idxShadow1 ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  partition i   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma getSndShadowAddDerivation child (descChild : vaddr) 
table idx (s : state) entry flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
StateLib.getSndShadow child
  (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) =
StateLib.getSndShadow child (memory s).
Proof.
intros Hentry.
unfold StateLib.getSndShadow.
case_eq ( StateLib.Index.succ idxShadow2 ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (child, i) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  child i (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  child i   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma getParentAddDerivation partition (descChild : vaddr) 
table idx (s : state) entry flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->
StateLib.getParent partition
  (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) =
StateLib.getParent partition (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.getParent.
case_eq ( StateLib.Index.succ idxParentDesc ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  partition i   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma getConfigTablesLinkedListAddDerivation child (descChild : vaddr) 
table idx (s : state) entry flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
StateLib.getConfigTablesLinkedList child
  (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) =
StateLib.getConfigTablesLinkedList child (memory s).
Proof.
intros Hentry.
unfold StateLib.getConfigTablesLinkedList.
case_eq ( StateLib.Index.succ idxShadow3 ); intros; trivial.
cbn.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (child, i) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  child i (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  child i   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma getIndirectionAddDerivation sh1 table idx descChild s entry va nbL stop flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->
getIndirection sh1 va nbL stop
  {|  currentPartition := currentPartition s;
      memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} =
getIndirection sh1 va nbL stop s .
Proof.
intros Hentry.
revert sh1 nbL.
induction  stop.
+ simpl. trivial.
+ simpl. intros. 
  destruct (levelEq nbL levelMin);trivial.
  set (entry0 := (VE {| pd := flag; va := descChild |})  ) in *.
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

Lemma readPDflagAddDerivation table1 table2 idx1 idx2 newEntry s: 
table1 <> table2 \/ idx1 <> idx2 -> 
StateLib.readPDflag table1 idx1
  (add table2 idx2 (VE newEntry) (memory s) pageEq idxEq) =
StateLib.readPDflag table1 idx1(memory s).
Proof.     
intros Hnoteq.
unfold StateLib.readPDflag. cbn. 
case_eq ( beqPairs (table2, idx2) (table1, idx1) pageEq idxEq);intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
   contradict Hnoteq. intuition.
+ intros.
  apply beqPairsFalse in Hpairs.
  assert (lookup table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq) pageEq idxEq
   = lookup table1 idx1 (memory s) pageEq idxEq) as Hmemory.
  { apply removeDupIdentity. intuition. }
  rewrite Hmemory. reflexivity.
Qed. 

Lemma readVirEntryAddDerivation table1 table2 idx1 idx2 newEntry s: 
table1 <> table2 \/ idx1 <> idx2 -> 
StateLib.readVirEntry table1 idx1
  (add table2 idx2 (VE newEntry) (memory s) pageEq idxEq) =
StateLib.readVirEntry table1 idx1(memory s).
Proof.     
intros Hnoteq.
unfold StateLib.readVirEntry. cbn. 
case_eq ( beqPairs (table2, idx2) (table1, idx1) pageEq idxEq);intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
   contradict Hnoteq. intuition.
+ intros.
  apply beqPairsFalse in Hpairs.
  assert (lookup table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq) pageEq idxEq
   = lookup table1 idx1 (memory s) pageEq idxEq) as Hmemory.
  { apply removeDupIdentity. intuition. }
  rewrite Hmemory. reflexivity.
Qed. 

Lemma checkChildAddDerivation (descChild : vaddr) 
table idx (s : state) partition nbL va entry : 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
checkChild partition nbL
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |} va =
checkChild partition nbL s va.
Proof.
intros  Hreadpdflag Hentry.
unfold checkChild.
set (s' :=  {| currentPartition := currentPartition s;
               memory := add table idx (VE {| pd := false; va := descChild |}) 
                            (memory s) pageEq idxEq |}) in *.
assert( StateLib.getFstShadow partition (memory s')= StateLib.getFstShadow partition (memory s) ) as Hfstsh.
{ apply getFstShadowAddDerivation with entry;trivial. }
rewrite Hfstsh.
case_eq(StateLib.getFstShadow partition (memory s));trivial.
intros sh1 Hsh1.
assert (StateLib.getIndirection sh1 va nbL (nbLevel - 1)  s' = 
          getIndirection sh1 va nbL (nbLevel - 1)  s) as Hindeq.
{ apply getIndirectionAddDerivation with entry;trivial. }
rewrite Hindeq.
case_eq (StateLib.getIndirection sh1 va nbL (nbLevel - 1) s);trivial.
intros sh1LastEntry Hsh1LastEntry.
case_eq (Nat.eqb sh1LastEntry pageDefault) ; intros; trivial.
assert (StateLib.readPDflag sh1LastEntry (StateLib.getIndexOfAddr va levelMin) (memory s')  = 
        StateLib.readPDflag sh1LastEntry (StateLib.getIndexOfAddr va levelMin) (memory s)) as Hpdflag. 
{ unfold s';cbn.
  unfold StateLib.readPDflag in *.
  cbn.
  case_eq(beqPairs (table, idx) (sh1LastEntry, StateLib.getIndexOfAddr va levelMin)
         pageEq idxEq); intros; cbn.
  + apply beqPairsTrue in H0.
    destruct H0.
    subst.
    destruct Hreadpdflag.
    
    symmetry; assumption.
    rewrite Hentry in H0.
    now contradict H0.
  + apply beqPairsFalse in H0.
    assert(Hmemory: lookup sh1LastEntry (StateLib.getIndexOfAddr va levelMin)
                   (removeDup table idx (memory s) pageEq idxEq)pageEq idxEq = 
                   lookup sh1LastEntry (StateLib.getIndexOfAddr va levelMin) (memory s) 
                   pageEq idxEq ).
    { apply removeDupIdentity;intuition. }
    rewrite Hmemory;trivial. }
rewrite Hpdflag.
reflexivity. 
Qed.

Lemma getPdsVAddrAddDerivation (descChild : vaddr) 
table idx (s : state) partition nbL entry :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
getPdsVAddr partition nbL getAllVAddrWithOffset0
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |})
   (memory s) pageEq idxEq |} =
getPdsVAddr partition nbL getAllVAddrWithOffset0 s.
Proof.
unfold getPdsVAddr.
induction getAllVAddrWithOffset0.
simpl; trivial.
intros.
simpl. 
set (s' :=  {|
    currentPartition := currentPartition s;
    memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}) in *.
assert (StateLib.checkChild partition nbL s' a =
        StateLib.checkChild partition nbL s a) as HpartRef.
unfold s'.

apply checkChildAddDerivation with entry ;trivial; trivial.
rewrite HpartRef.
rewrite IHl; trivial.
Qed.  
Lemma readPresentAddDerivation (descChild : vaddr) 
table idx (s : state)  p idx2  entry flag: 
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
 StateLib.readPresent p idx2
    (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) =
     StateLib.readPresent p idx2 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPresent.
cbn.
case_eq( beqPairs (table, idx) (p, idx2) pageEq idxEq); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx2 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup p idx2 (memory s) pageEq idxEq ); intros.
 { apply removeDupIdentity ; intuition. }
 rewrite Hmemory; reflexivity. 
Qed.

Lemma readAccessibleAddDerivation (descChild : vaddr) 
table idx (s : state)  p idx2  entry flag: 
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
 StateLib.readAccessible p idx2
    (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) =
     StateLib.readAccessible p idx2 (memory s).
Proof.
intros Hentry.
unfold StateLib.readAccessible.
cbn.
case_eq( beqPairs (table, idx) (p, idx2) pageEq idxEq); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx2 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup p idx2 (memory s) pageEq idxEq ); intros.
 { apply removeDupIdentity ; intuition. }
 rewrite Hmemory; reflexivity. 
Qed.

Lemma readPhyEntryAddDerivation (descChild : vaddr) 
table idx (s : state)  p idx2  entry flag: 
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
StateLib.readPhyEntry p idx2
  (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) =
StateLib.readPhyEntry p idx2 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPhyEntry.
cbn.
case_eq( beqPairs (table, idx) (p, idx2) pageEq idxEq); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx2 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup p idx2 (memory s) pageEq idxEq ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readPhysicalAddDerivation (descChild : vaddr) 
table idx (s : state)  p idx2  entry flag: 
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
StateLib.readPhysical p idx2
  (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) =
StateLib.readPhysical p idx2 (memory s).
Proof.
intros Hentry.
unfold StateLib.readPhysical.
cbn.
case_eq( beqPairs (table, idx) (p, idx2) pageEq idxEq); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx2 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup p idx2 (memory s) pageEq idxEq ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readVirtualAddDerivation (descChild : vaddr) 
table idx (s : state)  p idx2  entry flag: 
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
StateLib.readVirtual p idx2
  (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) =
StateLib.readVirtual p idx2 (memory s).
Proof.
intros Hentry.
unfold StateLib.readVirtual.
cbn.
case_eq( beqPairs (table, idx) (p, idx2) pageEq idxEq); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx2 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup p idx2 (memory s) pageEq idxEq ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma readIndexAddDerivation (descChild : vaddr) 
table idx (s : state)  p idx2  entry: 
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
StateLib.readIndex p idx2
  (add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq) =
StateLib.readIndex p idx2 (memory s).
Proof.
intros Hentry.
unfold StateLib.readIndex.
cbn.
case_eq( beqPairs (table, idx) (p, idx2) pageEq idxEq); intros.
apply beqPairsTrue in H.
destruct H; subst.
rewrite Hentry; trivial.
apply beqPairsFalse in H.
assert(Hmemory : lookup p idx2 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup p idx2 (memory s) pageEq idxEq ); intros.
 { apply removeDupIdentity ; intuition. }
rewrite Hmemory; reflexivity.
Qed.

Lemma  getMappedPageAddDerivation (descChild : vaddr) 
table idx (s : state)  va pd entry flag: 
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
getMappedPage pd
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} va =
getMappedPage pd s va.
Proof.
intros Hentry.
unfold getMappedPage.
destruct( StateLib.getNbLevel ); intros; trivial.
cbn.
assert(Hind : getIndirection pd va l (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} =
    getIndirection pd va l (nbLevel - 1) s).
apply getIndirectionAddDerivation with entry; trivial.
rewrite Hind.  
destruct(getIndirection pd va l (nbLevel - 1) s); intros; trivial.
destruct(Nat.eqb pageDefault p);trivial.
 assert(Hpresent :   StateLib.readPresent p (StateLib.getIndexOfAddr va levelMin)
    (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) =
     StateLib.readPresent p (StateLib.getIndexOfAddr va levelMin) (memory s)).
apply readPresentAddDerivation with entry; trivial.
rewrite Hpresent.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va levelMin) (memory s) ); trivial.
destruct b; trivial.
assert(Heq : StateLib.readPhyEntry p (StateLib.getIndexOfAddr va levelMin)
    (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq
       idxEq)=StateLib.readPhyEntry p (StateLib.getIndexOfAddr va levelMin) (memory s)).
       
apply readPhyEntryAddDerivation with entry; trivial .
rewrite Heq;trivial.
Qed.

Lemma getMappedPagesAuxAddDerivation (descChild : vaddr) 
table idx (s : state)  listVa pd entry flag: 
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
getMappedPagesAux pd listVa
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) 
              (memory s) pageEq idxEq |} =
getMappedPagesAux pd listVa s.
Proof.
unfold getMappedPagesAux.
intros Hentry. 
f_equal.
unfold  getMappedPagesOption.
induction listVa.
simpl. trivial.
simpl.
rewrite IHlistVa.
f_equal. 
apply getMappedPageAddDerivation with entry; trivial.
Qed.

Lemma getMappedPagesAddDerivation child (descChild : vaddr) 
table idx (s : state)  entry flag: 
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
getMappedPages child
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} =
getMappedPages child s.
Proof.
intros Hentry.
unfold getMappedPages.
assert(Hpd :  StateLib.getPd child
    (memory
       {|
       currentPartition := currentPartition s;
       memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |}) =
       StateLib.getPd child (memory s)).
apply getPdAddDerivation with entry; trivial.
rewrite Hpd.
destruct (StateLib.getPd child (memory s)); trivial.
apply getMappedPagesAuxAddDerivation with entry;trivial.
Qed.

Lemma getChildrenAddDerivation partition (descChild : vaddr) 
table idx entry (s : state):
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
getChildren partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) pageEq idxEq |} = getChildren partition s.
Proof.
intros Hentry Hreadpdflag.
unfold getChildren.
set (entry0 := (VE {| pd := false; va := descChild |}) ) in *. 
set (s' :={| currentPartition := currentPartition s;
             memory := add table idx entry0 (memory s) pageEq idxEq |}) in *.
destruct StateLib.getNbLevel;trivial.
assert(StateLib.getPd partition (memory s') =
         StateLib.getPd partition (memory s)) as HgetPd.
         unfold s'.
apply getPdAddDerivation with entry;trivial.
rewrite HgetPd.
destruct (StateLib.getPd partition (memory s));trivial.
assert (getPdsVAddr partition l getAllVAddrWithOffset0 s' = 
            getPdsVAddr partition l getAllVAddrWithOffset0 s) as HgetPdsVa.
            unfold s'.
 { apply getPdsVAddrAddDerivation with entry;trivial. }
rewrite HgetPdsVa.
unfold s' , entry0.
apply getMappedPagesAuxAddDerivation with entry;trivial.
Qed.

Lemma getPartitionAuxAddDerivation partition (descChild : vaddr) 
table idx entry (s : state):
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
getPartitionAux partition 
    {| currentPartition := currentPartition s;
       memory := add table idx (VE {| pd := false; va := descChild |}) 
                      (memory s) pageEq idxEq |} (nbPage+1) =
getPartitionAux partition s (nbPage+1). 
Proof.
intros Hentry Hreadpdflag.
revert partition.
induction (nbPage+1).
now cbn.
simpl.
set (s' :=   {| currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                      (memory s) pageEq idxEq |}) in *.
intros. f_equal.
assert (getChildren partition s = getChildren partition s') as Hchildren.
unfold s'. symmetry.
apply getChildrenAddDerivation with entry;trivial. 
rewrite <- Hchildren.
simpl.
clear Hchildren.
induction  (getChildren partition s).
 simpl. trivial.
 simpl.
 f_equal.
 apply IHn.
 apply IHl.
Qed.

Lemma getPartitionsAddDerivation (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) -> 
getPartitions pageRootPartition
          {|
          currentPartition := currentPartition s;
          memory := add table idx (VE {| pd := false; va := descChild |}) 
                      (memory s) pageEq idxEq |} =
getPartitions pageRootPartition s.
Proof.
intros Hentry Hreadpdflag.
unfold getPartitions.
apply getPartitionAuxAddDerivation with entry;trivial.
Qed.

Lemma getTablePagesAddDerivation   (descChild : vaddr) table idx entry size p (s : state) flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
getTablePages p size
 {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |}=
getTablePages p size s.
Proof.
revert p .
set (s' :=   {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |}).
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

Lemma getIndirectionsAddDerivation  (descChild : vaddr) table idx entry pd (s : state) flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->  
getIndirections pd
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} =
getIndirections pd s.
Proof.
intros Hentry.
unfold getIndirections.
revert pd.
induction nbLevel.
simpl. trivial. simpl.
intros. f_equal.
    assert (getTablePages pd tableSize   {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} = getTablePages pd tableSize s) as Htablepages.
apply getTablePagesAddDerivation with entry ;trivial.
rewrite Htablepages.
clear Htablepages.
induction (getTablePages pd tableSize s); intros; trivial.
simpl in *.
rewrite IHn. 
f_equal.
apply IHl.
Qed.

Lemma getConfigTablesLinkedListsAddDerivation sh3  (descChild : vaddr) table idx entry
 (s : state) flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
getLLPages sh3
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} (nbPage+1) =
getLLPages sh3 s (nbPage+1).
Proof.
revert sh3.
induction (nbPage+1);trivial.
intros. simpl.
 set (s' :=   {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} ) in *.
destruct (StateLib.getMaxIndex);trivial.
assert(HreadPhyEnt :  StateLib.readPhysical sh3 i
    (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) = 
    StateLib.readPhysical sh3 i (memory s) ).
apply readPhysicalAddDerivation with entry;trivial.
rewrite HreadPhyEnt.
destruct (StateLib.readPhysical sh3 i (memory s));trivial.
destruct (Nat.eqb p pageDefault) ;trivial.
f_equal.
apply IHn; trivial.
Qed. 

Lemma getConfigPagesAuxAddDerivation child (descChild : vaddr) table idx entry (s : state) flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
getConfigPagesAux child
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} =
getConfigPagesAux child s.
Proof.
intros Hentry.
unfold getConfigPagesAux.
cbn.

assert (StateLib.getPd child  (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) = StateLib.getPd child (memory s) ) as HgetPd.
apply getPdAddDerivation with entry ;trivial.
unfold getConfigPagesAux in *.
rewrite HgetPd.
destruct (StateLib.getPd child (memory s)) as [ pd|] ;trivial.
assert (StateLib.getFstShadow child  (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) = StateLib.getFstShadow child (memory s)) as Hsh1.
apply getFstShadowAddDerivation with entry ;trivial.
rewrite Hsh1.
destruct  (StateLib.getFstShadow child (memory s))as [ sh1|]  ;trivial.
assert (StateLib.getSndShadow child  (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) = StateLib.getSndShadow child (memory s)) as Hsh2.
apply getSndShadowAddDerivation with entry ;trivial.
rewrite Hsh2.
destruct  (StateLib.getSndShadow child (memory s))as [ sh2|]  ;trivial.
assert (StateLib.getConfigTablesLinkedList child   (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq)= StateLib.getConfigTablesLinkedList child (memory s)) as Hsh3.
apply getConfigTablesLinkedListAddDerivation with entry; trivial.
rewrite Hsh3.
destruct  (StateLib.getConfigTablesLinkedList child (memory s)) as [ sh3|] ;trivial.
assert (getIndirections pd   {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |}  = getIndirections pd s) as Hind.
apply getIndirectionsAddDerivation with entry ; trivial.
rewrite Hind; clear Hind.
assert (forall sh1, getIndirections sh1  {|
        currentPartition := currentPartition s;
        memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} = getIndirections sh1 s) as Hind.
intros. 
apply getIndirectionsAddDerivation with entry; trivial.
rewrite Hind.
rewrite Hind.
do 3 f_equal.
apply getConfigTablesLinkedListsAddDerivation with entry; trivial.
Qed.

Lemma getConfigPagesAddDerivation child (descChild : vaddr) table idx entry (s : state) flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
getConfigPages child
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} =
getConfigPages child s.
Proof.
intros Hentry.
unfold getConfigPages; f_equal.
apply getConfigPagesAuxAddDerivation with entry; trivial.
Qed.

Lemma getUsedPagesAddDerivation child (descChild : vaddr) table idx entry (s : state) flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
getUsedPages child
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} =
getUsedPages child s.
Proof.
intros Hentry.
unfold getUsedPages.
f_equal.
apply getConfigPagesAddDerivation with entry; trivial.
apply getMappedPagesAddDerivation with entry; trivial.
Qed.

Lemma partitionsIsolationUpdtateSh1Structure (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None )->  
partitionsIsolation s -> 
partitionsIsolation
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) pageEq idxEq |}.
Proof.
intros.
unfold partitionsIsolation in *.
assert(Hpartitions : getPartitions pageRootPartition
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |} = 
getPartitions pageRootPartition s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions.
intros.
assert(Hchildren :getChildren parent
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |} =
     getChildren parent s) .
apply getChildrenAddDerivation with entry; trivial.
rewrite Hchildren in *.
clear Hchildren.
assert(Husedpages : forall child,  getUsedPages child
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |} = 
getUsedPages child s).
intros.
apply getUsedPagesAddDerivation with entry; trivial.
rewrite Husedpages.
rewrite Husedpages.
apply H1 with parent; trivial.
Qed.
Lemma getAccessibleMappedPageAddDerivation pd (descChild : vaddr) table idx entry va (s : state)
flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
getAccessibleMappedPage pd
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} va =
getAccessibleMappedPage pd s va.
Proof.
intros Hentry.
set(s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} ).
  
unfold getAccessibleMappedPage.
destruct( StateLib.getNbLevel ); intros; trivial.
cbn.
assert(Hind : getIndirection pd va l (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} =
    getIndirection pd va l (nbLevel - 1) s).
apply getIndirectionAddDerivation with entry; trivial.
unfold s'.
rewrite Hind.  
destruct(getIndirection pd va l (nbLevel - 1) s); intros; trivial.
destruct(Nat.eqb pageDefault p);trivial.
 assert(Hpresent :   StateLib.readPresent p (StateLib.getIndexOfAddr va levelMin)
    (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) =
     StateLib.readPresent p (StateLib.getIndexOfAddr va levelMin) (memory s)).
apply readPresentAddDerivation with entry; trivial.
rewrite Hpresent.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va levelMin) (memory s) ); trivial.
destruct b; trivial.
assert( Hacc : StateLib.readAccessible p (StateLib.getIndexOfAddr va levelMin)
    (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) = 
    StateLib.readAccessible p (StateLib.getIndexOfAddr va levelMin) (memory s) ).
apply readAccessibleAddDerivation with entry;trivial.
rewrite Hacc.
destruct (StateLib.readAccessible p (StateLib.getIndexOfAddr va levelMin) (memory s) ); trivial.
destruct b; trivial.
assert(Heq : StateLib.readPhyEntry p (StateLib.getIndexOfAddr va levelMin)
    (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq
       idxEq)=StateLib.readPhyEntry p (StateLib.getIndexOfAddr va levelMin) (memory s)).
       
apply readPhyEntryAddDerivation with entry; trivial .
rewrite Heq;trivial.
Qed.

Lemma getAccessibleMappedPagesAuxAddDerivation  (descChild : vaddr) table idx entry pd (s : state)
flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
getAccessibleMappedPagesAux pd getAllVAddrWithOffset0
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} =
getAccessibleMappedPagesAux pd getAllVAddrWithOffset0 s.
Proof.
unfold getAccessibleMappedPagesAux.
intros Hentry.
unfold  getAccessibleMappedPagesOption.
f_equal.
revert pd.
induction getAllVAddrWithOffset0; simpl; trivial.
intros.
set(s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} ).
f_equal.
apply getAccessibleMappedPageAddDerivation with entry;trivial.
apply IHl.
Qed.

Lemma getAccessibleMappedPagesAddDerivation partition (descChild : vaddr) table idx entry
 (s : state) flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
getAccessibleMappedPages partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |} =
getAccessibleMappedPages partition s.
Proof.
intros Hentry.
unfold getAccessibleMappedPages.
assert(HgetPd : StateLib.getPd partition
    (add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq) =
StateLib.getPd partition (memory s) ).
apply getPdAddDerivation with entry; trivial.
simpl.
rewrite HgetPd.
case_eq(StateLib.getPd partition (memory s) ); intros;trivial.
apply getAccessibleMappedPagesAuxAddDerivation with entry; trivial.
Qed.

Lemma  kernelDataIsolationUpdtateSh1Structure (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
 kernelDataIsolation s -> 
 kernelDataIsolation 
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) pageEq idxEq |}.
Proof.
unfold kernelDataIsolation.
intros.
assert(Hconfig : getConfigPages partition2  {|
                         currentPartition := currentPartition s;
                         memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |} =
                     getConfigPages partition2 s ).
apply getConfigPagesAddDerivation with entry;trivial.
rewrite Hconfig.
assert(Hpartitions : getPartitions pageRootPartition
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |} = 
getPartitions pageRootPartition s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *.
clear Hconfig Hpartitions.
assert(getAccessibleMappedPages partition1
             {| currentPartition := currentPartition s;
                memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |} = 
         getAccessibleMappedPages partition1 s).
apply getAccessibleMappedPagesAddDerivation with entry; trivial.
rewrite H4.
apply H1; trivial.
Qed.

Lemma verticalSharingUpdtateSh1Structure (descChild : vaddr) table idx entry (s : state):
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) -> 
verticalSharing s -> 
verticalSharing
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) pageEq idxEq |}.
Proof.
unfold verticalSharing.
intros.
assert(Hpartitions : getPartitions pageRootPartition
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) pageEq idxEq |} = 
getPartitions pageRootPartition s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions.
assert(Hchildren : getChildren parent
          {|
          currentPartition := currentPartition s;
          memory := add table idx (VE {| pd := false; va := descChild |}) 
                      (memory s) pageEq idxEq |} = 
         getChildren parent s).
apply getChildrenAddDerivation with entry;trivial.
rewrite Hchildren in *; clear Hchildren.
assert(Hused : getUsedPages child
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                 (memory s) pageEq idxEq |} =
       getUsedPages child s).
apply getUsedPagesAddDerivation with entry; trivial.
rewrite Hused in *; clear Hused.
assert (Hmapped : getMappedPages parent
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                 (memory s) pageEq idxEq |}=
         getMappedPages parent s).
apply getMappedPagesAddDerivation with entry;trivial.
rewrite Hmapped;clear Hmapped.
apply H1;trivial.
Qed.

Lemma isVAAddDerivation idx partition table descChild entry idxroot s flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->
isVA partition idxroot s -> 
isVA partition idxroot
  {| currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := flag; va := descChild |}) 
     (memory s) pageEq idxEq |}.
Proof.
intros Hentry.
unfold isVA.
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

Lemma isPEAddDerivation idx partition table descChild entry idxroot s flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->
isPE partition idxroot s -> 
isPE partition idxroot
  {| currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := flag; va := descChild |}) 
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

Lemma isVEAddDerivation idx partition table descChild entry idxroot s flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->
isVE partition idxroot s -> 
isVE partition idxroot
  {| currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := flag; va := descChild |}) 
     (memory s) pageEq idxEq |}.
Proof.
intros Hentry.
unfold isVE.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) pageEq idxEq);trivial;intros Hpairs.
apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  partition idxroot   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma nextEntryIsPPAddDerivation idx partition table descChild entry idxroot PPentry s flag:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->
nextEntryIsPP partition idxroot PPentry s <-> 
nextEntryIsPP partition idxroot PPentry
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
split;intros Hentry;
unfold nextEntryIsPP in *;
cbn;
destruct ( StateLib.Index.succ idxroot); trivial.
- case_eq (beqPairs (table, idx) (partition, i) pageEq idxEq);trivial;intros Hpairs.
   + apply beqPairsTrue in Hpairs.
     destruct Hpairs as (Htable & Hidx).  subst.      
     rewrite H in *.
     trivial.
   + apply beqPairsFalse in Hpairs.
     assert (lookup  partition i (removeDup table idx (memory s) pageEq idxEq)
             pageEq idxEq = lookup  partition i   (memory s) pageEq idxEq) as Hmemory.
     { apply removeDupIdentity. intuition. }
       rewrite Hmemory. trivial.
- cbn in *.
  case_eq (beqPairs (table, idx) (partition, i) pageEq idxEq);trivial;intros Hpairs.
  + rewrite Hpairs in *; now contradict Hentry.
  + rewrite Hpairs in *.
    assert (lookup  partition i (removeDup table idx (memory s) pageEq idxEq)
           pageEq idxEq = lookup  partition i   (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity.  apply beqPairsFalse in Hpairs. intuition. }
     rewrite Hmemory in *. trivial.     
Qed. 

Lemma partitionDescriptorEntryAddDerivation idx table descChild entry s:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) -> 
partitionDescriptorEntry s -> 
partitionDescriptorEntry
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}  .
Proof.
intros Hentry Hpdflag.
unfold partitionDescriptorEntry.
intros.
assert(Hpartitions : getPartitions pageRootPartition
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) pageEq idxEq |} = 
getPartitions pageRootPartition s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions.
assert(Hpde : idxroot < tableSize - 1 /\
              isVA partition idxroot s /\
              (exists entry : page, nextEntryIsPP partition idxroot entry s /\ 
                                    entry <> pageDefault)).
apply H; trivial.
destruct Hpde as (Hidxlt & Hva & Hpp).
split; trivial.
split.
apply isVAAddDerivation with entry; trivial.
destruct Hpp as (PPentry & Hpp & Hnotnull).
exists PPentry; split;trivial.
apply nextEntryIsPPAddDerivation with entry; trivial.
Qed.

Lemma dataStructurePdSh1Sh2asRootAddDerivation descChild idxroot s table idx entry :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
dataStructurePdSh1Sh2asRoot idxroot s ->
dataStructurePdSh1Sh2asRoot  idxroot
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros Hentry Hpdflag Hds.
unfold dataStructurePdSh1Sh2asRoot in *.
assert(Hpartitions : getPartitions pageRootPartition
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) pageEq idxEq |} = 
getPartitions pageRootPartition s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions.
intros.
rewrite <- nextEntryIsPPAddDerivation in H0; try eassumption.
assert (Hind : getIndirection entry0 va level stop s = Some indirection).
{ rewrite <- H3. symmetry.
  apply getIndirectionAddDerivation with entry; trivial. }
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
  apply isPEAddDerivation with entry; trivial.
+ right.
  destruct Hds as (Hlevel & [(Hve & Hidx) | [(Hva & Hidx) | (Hpe & Hidx)]]).
  split; trivial.
  - left; split; trivial.
    apply isVEAddDerivation with entry; trivial.
  - split; trivial.
    right; left;split; trivial.
    apply isVAAddDerivation with entry; trivial.
  - split;trivial.
    right;right; split; trivial.
    apply isPEAddDerivation with entry; trivial.
Qed.

Lemma currentPartitionInPartitionsListAddDerivation  descChild s table idx entry :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
currentPartitionInPartitionsList s ->
currentPartitionInPartitionsList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros Hentry Hpdflag Hcurpart.
unfold currentPartitionInPartitionsList in *.
cbn.
assert(Hpartitions : getPartitions pageRootPartition
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) pageEq idxEq |} = 
getPartitions pageRootPartition s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions; trivial.
Qed.

Lemma noDupMappedPagesListAddDerivation descChild s table idx entry :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
noDupMappedPagesList s ->
noDupMappedPagesList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros Hentry Hpdflag.
unfold noDupMappedPagesList.
intros.
assert(Hpartitions : getPartitions pageRootPartition
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) pageEq idxEq |} = 
getPartitions pageRootPartition s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions; trivial.
assert (Hmapped : getMappedPages partition
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                 (memory s) pageEq idxEq |}=
         getMappedPages partition s).
apply getMappedPagesAddDerivation with entry;trivial.
rewrite Hmapped;clear Hmapped.
apply H;trivial.
Qed.

Lemma noDupConfigPagesListAddDerivation descChild s table idx entry :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
noDupConfigPagesList s ->
noDupConfigPagesList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros Hentry Hpdflag.
unfold noDupConfigPagesList.
intros.
assert(Hpartitions : getPartitions pageRootPartition
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) pageEq idxEq |} = 
getPartitions pageRootPartition s).
apply getPartitionsAddDerivation with entry; trivial.

rewrite Hpartitions in *; clear Hpartitions; trivial.
assert ( getConfigPages partition
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |})
                 (memory s) pageEq idxEq |} = getConfigPages partition
     s) as Hind. 
apply getConfigPagesAddDerivation with entry; trivial.
rewrite Hind.
apply H ; trivial.
Qed.

Lemma parentInPartitionListAddDerivation descChild s table idx entry :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
parentInPartitionList s ->
parentInPartitionList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros Hentry Hpdflag.
unfold parentInPartitionList.
intros.
assert(Hpartitions : getPartitions pageRootPartition
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) pageEq idxEq |} = 
getPartitions pageRootPartition s).
apply getPartitionsAddDerivation with entry; trivial.
rewrite Hpartitions in *; clear Hpartitions; trivial.
rewrite <- nextEntryIsPPAddDerivation with entry in H1; trivial.
apply H with partition; trivial.
Qed.

Lemma getPDFlagAddDerivation sh1 va descChild table idx entry s:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) ->
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
getPDFlag sh1 va
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
  (memory s) pageEq idxEq |} = getPDFlag sh1 va s.
Proof.
intros Hentry;
unfold getPDFlag.
case_eq( StateLib.getNbLevel);intros;trivial.
assert(Hind :getIndirection sh1 va l (nbLevel - 1)
          {|
          currentPartition := currentPartition s;
          memory := add table idx (VE {| pd := false; va := descChild |}) 
          (memory s) pageEq idxEq |} = 
      getIndirection sh1 va l (nbLevel - 1) s).
apply getIndirectionAddDerivation with entry;trivial.
rewrite Hind;clear Hind.
case_eq( getIndirection sh1 va l (nbLevel - 1) s);intros;trivial.
case_eq(Nat.eqb p pageDefault);intros;trivial.
cbn.

assert(StateLib.readPDflag p (StateLib.getIndexOfAddr va levelMin)
    (add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq) = 
    StateLib.readPDflag p (StateLib.getIndexOfAddr va levelMin) (memory s) ).
{ unfold StateLib.readPDflag in *.
cbn.
case_eq(beqPairs (table, idx) (p, StateLib.getIndexOfAddr va levelMin) pageEq idxEq);
intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs.
  subst.
  rewrite Hentry in *.
  cbn.
  destruct H0;
  symmetry. assumption.
  now contradict H0.
+ apply beqPairsFalse in Hpairs.
  assert(Hmemory: lookup p (StateLib.getIndexOfAddr va levelMin) (removeDup table idx (memory s) pageEq idxEq)
    pageEq idxEq = lookup p (StateLib.getIndexOfAddr va levelMin) (memory s) pageEq idxEq).
    apply removeDupIdentity;intuition.
   rewrite Hmemory.
   trivial. }
   rewrite H3;trivial.
Qed.

Lemma accessibleVAIsNotPartitionDescriptorAddDerivation descChild s table idx entry :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
accessibleVAIsNotPartitionDescriptor s -> 
accessibleVAIsNotPartitionDescriptor
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros Hentry Hpdflag.
unfold accessibleVAIsNotPartitionDescriptor.
intros.
assert(Hpd : StateLib.getPd partition
        (memory
           {|
           currentPartition := currentPartition s;
           memory := add table idx (VE {| pd := false; va := descChild |})
            (memory s) pageEq idxEq |}) =
       StateLib.getPd partition (memory s)).
apply getPdAddDerivation with entry;trivial.
rewrite Hpd in *;clear Hpd.
assert(Hsh1 : StateLib.getFstShadow partition
        (memory
           {|
           currentPartition := currentPartition s;
           memory := add table idx (VE {| pd := false; va := descChild |})
            (memory s) pageEq idxEq |}) =
       StateLib.getFstShadow partition (memory s)).
apply getFstShadowAddDerivation with entry;trivial.
rewrite Hsh1 in *;clear Hsh1.
assert(Haccess : getAccessibleMappedPage pd
                  {|
                  currentPartition := currentPartition s;
                  memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) pageEq idxEq |} va =
                getAccessibleMappedPage pd s va).
apply getAccessibleMappedPageAddDerivation with entry ;trivial.
rewrite Haccess in *;clear Haccess.
assert(Hpart : getPartitions pageRootPartition
                  {|
                  currentPartition := currentPartition s;
                  memory := add table idx (VE {| pd := false; va := descChild |}) 
                  (memory s) pageEq idxEq |} = getPartitions pageRootPartition s).
apply getPartitionsAddDerivation with entry;trivial.
rewrite Hpart in *;clear Hpart.
assert(getPDFlag sh1 va
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |} 
  = getPDFlag sh1 va s).
apply getPDFlagAddDerivation with entry;trivial.
rewrite H4.
apply H with partition pd page;trivial.
Qed.

Lemma getVirtualAddressSh2AddDerivation sh2 s descChild table idx va entry flag:
  lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
getVirtualAddressSh2 sh2 s va =
getVirtualAddressSh2 sh2
    {|
    currentPartition := currentPartition s;
    memory := add table idx (VE {| pd := flag; va := descChild |}) 
    (memory s) pageEq idxEq |} va.
Proof.
intros.
unfold getVirtualAddressSh2.
case_eq(StateLib.getNbLevel);trivial.
intros nbL HnbL.
symmetry in HnbL. 
simpl.
rewrite  getIndirectionAddDerivation with 
sh2 table idx descChild s entry va  nbL (nbLevel -1) flag;
trivial.
case_eq( getIndirection sh2 va nbL (nbLevel - 1) s);trivial.
intros lastIndirection Hind.
simpl.
case_eq(Nat.eqb pageDefault lastIndirection);intros;trivial.
symmetry. 
apply readVirtualAddDerivation with entry;trivial.
Qed.

Lemma isAccessibleMappedPageInParentAddDerivattion partition (* nbL *) entry va flag
 accessiblePage table idx descChild s:
  lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
isAccessibleMappedPageInParent partition va accessiblePage s =
isAccessibleMappedPageInParent partition va accessiblePage
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := flag; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
unfold isAccessibleMappedPageInParent.
simpl.
intros.
rewrite  getSndShadowAddDerivation with partition descChild table idx s entry flag;trivial.
case_eq (StateLib.getSndShadow partition (memory s));trivial.
intros sh2 Hsh2.
rewrite <- getVirtualAddressSh2AddDerivation with sh2 s descChild table idx va entry flag;trivial.
case_eq(getVirtualAddressSh2 sh2 s va);trivial.
intros vaInParent HvaInParent.
rewrite getParentAddDerivation with  partition descChild table idx s entry flag;trivial.
case_eq(StateLib.getParent partition (memory s));trivial.
intros parent Hparent.
rewrite getPdAddDerivation with  parent descChild table idx s entry flag;trivial.
case_eq(StateLib.getPd parent (memory s) );trivial.
intros pdParent HpdParent.
rewrite <- getAccessibleMappedPageAddDerivation  with 
pdParent descChild table idx entry vaInParent s flag;trivial.

Qed.

Lemma accessibleChildPageIsAccessibleIntoParentAddDerivation
 (descChild : vaddr) table idx entry (s : state): 
( StateLib.readPDflag table idx (memory s) = Some false \/
StateLib.readPDflag table idx (memory s) = None)-> 
 lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
accessibleChildPageIsAccessibleIntoParent s -> 
accessibleChildPageIsAccessibleIntoParent
{|
currentPartition := currentPartition s;
memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros Hpdflag Hlookup Haccess .
set (s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
   (memory s) pageEq idxEq |}) in *.   
unfold accessibleChildPageIsAccessibleIntoParent.
intros  partition va pd  accessiblePage.
intros Hpart Hpd HaccessPage.
unfold s'.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
simpl in *.
rewrite getPdAddDerivation with partition descChild table idx s  entry false in Hpd ; trivial.
unfold s' in *.
rewrite getAccessibleMappedPageAddDerivation  
with pd descChild table idx entry va s false in HaccessPage;trivial. 

rewrite <- isAccessibleMappedPageInParentAddDerivattion with partition entry
va false accessiblePage table idx descChild s ;trivial.
unfold accessibleChildPageIsAccessibleIntoParent in *.
apply Haccess with pd;trivial.
Qed.

Lemma getAncestorsAddDerivation partition table idx descChild entry s :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
getAncestors partition
{|
currentPartition := currentPartition s;
memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |} =
getAncestors partition s.
Proof.
intros.
unfold getAncestors.
simpl.
revert partition.
induction  (nbPage + 1) ;
simpl;intros;trivial.
simpl.
assert(Hparent : StateLib.getParent partition
(add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq) =
StateLib.getParent partition
(memory s)).
apply getParentAddDerivation with entry ;trivial.

rewrite Hparent in *.
destruct (StateLib.getParent partition (memory s));trivial.
f_equal.
apply IHn;trivial.
Qed.

Lemma noCycleInPartitionTreeUpdtateSh1Structure s descChild table idx  entry:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/
StateLib.readPDflag table idx (memory s) = None) -> 
noCycleInPartitionTree s -> 
noCycleInPartitionTree {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) pageEq idxEq |}.
Proof.
intros Hlookup Hflag.
unfold noCycleInPartitionTree.
intros.
simpl in *.
set(s':= {|
          currentPartition := currentPartition s;
          memory := add table idx (VE {| pd := false; va := descChild |}) 
          (memory s) pageEq idxEq |}) in *.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
assert(Hparent : getAncestors partition s' =
       getAncestors partition s).
       unfold s'.
       apply getAncestorsAddDerivation with entry;trivial.
       rewrite Hparent in *.
apply H;trivial.
Qed.

Lemma configTablesAreDifferentUpdtateSh1Structure s descChild table idx  entry:
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/
StateLib.readPDflag table idx (memory s) = None) -> 
configTablesAreDifferent s -> 
configTablesAreDifferent {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) pageEq idxEq |}.
Proof.
intros Hlookup Hflag.
unfold configTablesAreDifferent.
intros.
set(s':= {|
          currentPartition := currentPartition s;
          memory := add table idx (VE {| pd := false; va := descChild |}) 
          (memory s) pageEq idxEq |}) in *.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
simpl in *.
assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
apply getConfigPagesAddDerivation with entry;trivial.
rewrite Hconfig; clear Hconfig.
assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
apply getConfigPagesAddDerivation with entry;trivial.
rewrite Hconfig; clear Hconfig.
apply H;trivial.
Qed.
Lemma isChildUpdtateSh1Structure table idx  entry descChild s :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/
StateLib.readPDflag table idx (memory s) = None) -> 
isChild s -> 
isChild
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros.
unfold isChild in *.
intros.
simpl in *.
set(s':= {|
          currentPartition := currentPartition s;
          memory := add table idx (VE {| pd := false; va := descChild |}) 
          (memory s) pageEq idxEq |}) in *.
assert(Hchildren : 
getChildren parent s' 
   = getChildren parent s).
apply getChildrenAddDerivation with entry;trivial.
rewrite Hchildren in *;clear Hchildren.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
assert(Hparent : StateLib.getParent partition
       (add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq) =
       StateLib.getParent partition (memory s)).
       
apply getParentAddDerivation with entry ;trivial.
rewrite Hparent in *.
apply H1;trivial.
Qed. 

 Lemma isPresentNotDefaultIffAddDerivation  table idx descChild s :
 isPresentNotDefaultIff s -> 
isPresentNotDefaultIff
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros.
unfold isPresentNotDefaultIff in *.
simpl.
intros table0 idx0.
unfold StateLib.readPresent.
unfold StateLib.readPhyEntry.
simpl. 
case_eq(beqPairs  (table, idx) (table0, idx0) pageEq idxEq); 
intros * Haa.
split;
intros * Hi;
now contradict Hi.
assert(lookup table0 idx0 (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq
= lookup table0 idx0  (memory s) pageEq idxEq).
apply removeDupIdentity.
apply beqPairsFalse in Haa.
intuition.
rewrite H0.
unfold StateLib.readPresent in *.
unfold StateLib.readPhyEntry in *.
trivial.
Qed. 

Lemma physicalPageNotDerivedAddDerivation table idx descChild entry s :
vaddrEq vaddrDefault descChild = false -> 
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/ 
StateLib.readPDflag table idx (memory s) = None) ->
physicalPageNotDerived s ->
physicalPageNotDerived
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
    (memory s) pageEq idxEq |}.
Proof.
intros  Hvanotnull Hlookup Hpdflag Hcons.
unfold physicalPageNotDerived in *.
simpl in *.
intros parent va  pdParent pageParent.
intros Hparts HgetpdParent Hderiv Hmapparent child pdChild vaInChild pageChild
Hgetchildren Hpdchild Hmapchild.
set(s':= {|
          currentPartition := currentPartition s;
          memory := add table idx (VE {| pd := false; va := descChild |}) 
          (memory s) pageEq idxEq |}) in *.
assert(Hpartitions : getPartitions pageRootPartition s = getPartitions pageRootPartition s').
symmetry.
apply getPartitionsAddDerivation with entry ;trivial.
rewrite Hpartitions in *.
assert(Hchildren : 
getChildren parent s' 
   = getChildren parent s).
apply getChildrenAddDerivation with entry;trivial.
rewrite Hchildren in *;clear Hchildren.
rewrite getPdAddDerivation with parent descChild table idx s  entry false in HgetpdParent ; trivial.
rewrite getPdAddDerivation with child descChild table idx s  entry false in Hpdchild ; trivial.
assert(Hmapped : forall pd v,  getMappedPage pd
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |} v =
getMappedPage pd s v).
intros.
apply getMappedPageAddDerivation with entry; trivial.
rewrite Hmapped in *. clear Hmapped.
apply Hcons with parent va pdParent child pdChild vaInChild;trivial.
unfold isDerived in *.
unfold s' in *;simpl in *.
rewrite getFstShadowAddDerivation with parent descChild table idx s entry false
 in Hderiv;trivial.
 case_eq (StateLib.getFstShadow parent (memory s) );[intros sh1parent Hsh1parent | intros Hsh1parent];
 rewrite Hsh1parent in *;trivial.
 unfold not; intros Hgetvirt;
 contradict Hderiv.
 unfold getVirtualAddressSh1 in *.
case_eq(StateLib.getNbLevel);[intros nbL HnbL | intros HnbL];
 rewrite HnbL in *;trivial.
 rewrite getIndirectionAddDerivation with sh1parent table  idx  descChild s 
 entry va nbL (nbLevel -1) false;
 trivial.
case_eq( StateLib.getIndirection sh1parent va nbL (nbLevel - 1) s); 
[intros ind Hind | intros Hind];
 rewrite Hind in *;trivial.
 destruct(Nat.eqb pageDefault ind);trivial.
 simpl.
 unfold StateLib.readVirEntry in *.
 simpl in *.
 case_eq(  beqPairs (table, idx) (ind, StateLib.getIndexOfAddr va levelMin) 
 pageEq idxEq);intros Hpairs .
 simpl.
 trivial.
 assert(lookup ind (StateLib.getIndexOfAddr va levelMin)
      (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup ind (StateLib.getIndexOfAddr va levelMin) (memory s) pageEq idxEq).
 apply removeDupIdentity.
 apply beqPairsFalse in Hpairs.
 intuition.
 rewrite H;trivial.
Qed.

Lemma multiplexerWithoutParentUpdtateSh1Structure table idx  entry descChild s :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/
StateLib.readPDflag table idx (memory s) = None) -> 
multiplexerWithoutParent s -> 
multiplexerWithoutParent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros.
unfold multiplexerWithoutParent in *.
intros.
simpl in *.
assert(Hparent : StateLib.getParent pageRootPartition
       (add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq) =
       StateLib.getParent pageRootPartition (memory s)).       
apply getParentAddDerivation with entry ;trivial.
rewrite Hparent in *.
apply H1;trivial.
Qed. 

Lemma isParentUpdtateSh1Structure table idx  entry descChild s :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/
StateLib.readPDflag table idx (memory s) = None) -> 
isParent s -> 
isParent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros.
unfold isParent in *.
intros.
simpl in *.
set(s':= {|  currentPartition := _ |}) in *.
assert(Hchildren : 
getChildren parent s' 
   = getChildren parent s).
apply getChildrenAddDerivation with entry;trivial.
rewrite Hchildren in *;clear Hchildren.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
assert(Hparent : StateLib.getParent partition
       (add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq) =
       StateLib.getParent partition (memory s)).
       
apply getParentAddDerivation with entry ;trivial.
rewrite Hparent in *.
apply H1;trivial.
Qed. 

Lemma noDupPartitionTreeUpdtateSh1Structure table idx  entry descChild s :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/
StateLib.readPDflag table idx (memory s) = None) -> 
noDupPartitionTree s -> 
noDupPartitionTree
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros.
unfold noDupPartitionTree in *.
intros.
simpl in *.
set(s':= {|  currentPartition := _ |}) in *.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
trivial.
Qed. 

Lemma wellFormedFstShadowUpdtateSh1Structure table idx  entry descChild s :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/
StateLib.readPDflag table idx (memory s) = None) -> 
wellFormedFstShadow s -> 
wellFormedFstShadow
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros Hlookup Hor Hwell.
unfold wellFormedFstShadow in *.
intros.
simpl in *.
set(s':= {|  currentPartition := _ |}) in *.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
rewrite getPdAddDerivation with partition descChild table idx s  entry false in * ; trivial.
rewrite getFstShadowAddDerivation with partition descChild table idx s entry false
 in *;trivial.
assert(Hmapped : forall pd va,  getMappedPage pd s' va =
getMappedPage pd s va).
intros.
apply getMappedPageAddDerivation with entry; trivial.
rewrite Hmapped in *. clear Hmapped.
assert(Hsh1 :  exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va = Some vainparent).
apply  Hwell with partition pg pd;trivial.
destruct Hsh1 as (vainparent & Hvainpatent).
clear Hwell.
 unfold getVirtualAddressSh1 in *.
case_eq(StateLib.getNbLevel);[intros nbL HnbL | intros HnbL];
 rewrite HnbL in *;trivial. 
+ unfold s'. rewrite getIndirectionAddDerivation with sh1 table  idx  descChild s 
 entry va nbL (nbLevel -1) false;
 trivial.
case_eq( getIndirection sh1 va nbL (nbLevel - 1) s); 
[intros ind Hind | intros Hind];
 rewrite Hind in *;trivial.
 destruct(Nat.eqb pageDefault ind);trivial.
 now contradict Hvainpatent.
 simpl.
 unfold StateLib.readVirEntry in *.
 simpl in *.
 case_eq(  beqPairs (table, idx) (ind, StateLib.getIndexOfAddr va levelMin) 
 pageEq idxEq);intros Hpairs .
 simpl. exists descChild;trivial.
 assert(lookup ind (StateLib.getIndexOfAddr va levelMin)
      (removeDup table idx (memory s) pageEq idxEq) pageEq idxEq = 
 lookup ind (StateLib.getIndexOfAddr va levelMin) (memory s) pageEq idxEq).
 apply removeDupIdentity.
 apply beqPairsFalse in Hpairs.
 clear Hor.
 intuition.
rewrite H3;trivial.
exists vainparent;trivial.
now contradict Hvainpatent.
+ now contradict Hvainpatent.
Qed. 

Lemma wellFormedSndShadowUpdtateSh1Structure table idx  entry descChild s :
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/
StateLib.readPDflag table idx (memory s) = None) -> 
wellFormedSndShadow s -> 
wellFormedSndShadow
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros Hlookup Hor Hwell.
unfold wellFormedSndShadow in *.
intros.
simpl in *.
set(s':= {|  currentPartition := _ |}) in *.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
rewrite getPdAddDerivation with partition descChild table idx s  entry false in * ; trivial.
rewrite getSndShadowAddDerivation with partition descChild table idx s entry false
 in *;trivial.
assert(Hmapped : forall pd va,  getMappedPage pd s' va =
getMappedPage pd s va).
intros.
apply getMappedPageAddDerivation with entry; trivial.
rewrite Hmapped in *. clear Hmapped.
assert(exists vainparent : vaddr,
          getVirtualAddressSh2 sh2 s va = Some vainparent /\ 
          vaddrEq vaddrDefault vainparent = false).
apply Hwell with partition  pg pd ;trivial.
destruct H4 as (vainparent & Hvainpatent & Hnotnull).
rewrite  getVirtualAddressSh2AddDerivation with sh2 s descChild table idx va entry false
in * ;trivial.
exists vainparent;split;trivial.
Qed.

Lemma wellFormedShadowsUpdtateSh1Structure table idx  entry descChild idxroot s :
(idxroot = idxShadow1 \/ idxroot = idxShadow2) -> 
lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag table idx (memory s) = Some false \/
StateLib.readPDflag table idx (memory s) = None) -> 
wellFormedShadows idxroot s -> 
wellFormedShadows idxroot
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros Hor1 Hlookup Hor Hwell.
unfold wellFormedShadows in *.
intros.
simpl in *.
set(s':= {|  currentPartition := _ |}) in *.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
rewrite getPdAddDerivation with partition descChild table idx s  entry false in * ; trivial.
assert(HppS : nextEntryIsPP partition idxroot structroot s).
{ destruct Hor1; subst.
  rewrite nextEntryIsPPgetFstShadow in *.    
  rewrite <- getFstShadowAddDerivation with partition descChild table idx s entry false
  in *;trivial.
  rewrite nextEntryIsPPgetSndShadow in *.    
  rewrite <- getSndShadowAddDerivation with partition descChild table idx s entry false
  in *;trivial. }
unfold s'. rewrite getIndirectionAddDerivation with structroot table  idx  descChild s 
 entry va nbL stop false;
trivial. unfold s' in *. 
rewrite  getIndirectionAddDerivation with pdroot table  idx  descChild s 
entry va nbL stop false in *;
trivial.
apply Hwell with partition pdroot indirection1;trivial.
Qed.

Lemma wellFormedFstShadowIfNoneUpdtateSh1Structure  entry  s vaInCurrentPartition vaChild currentPart
     currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
     idxvaInCurPart vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap
     ptDescChildpd idxDescChild1 presentDescPhy phyDescChild pdChildphy
     ptVaChildpd idxvaChild presentvaChild phyVaChild sh2Childphy
     ptVaChildsh2 level  :

lookup ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) = Some false \/
StateLib.readPDflag ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) = None) -> 
wellFormedFstShadowIfNone s -> 
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 

 propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
     currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
     idxvaInCurPart vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap
     ptDescChildpd idxDescChild1 presentDescPhy phyDescChild pdChildphy
     ptVaChildpd idxvaChild presentvaChild phyVaChild sh2Childphy
     ptVaChildsh2 level -> 
   StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
   Some vaInCurrentPartition 
   -> 
wellFormedFstShadowIfNone
{|
      currentPartition := currentPartition s;
      memory := add ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin)
                  (VE {| pd := false; va := descChild |}) (memory s) pageEq
                  idxEq |} .
Proof.

intros Hlookup Hor Hwell.
intros Hlegit.
unfold wellFormedFstShadowIfNone in *.
intros.
simpl in *.
set(s':= {|  currentPartition := _ |}) in *.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
rewrite getPdAddDerivation with partition descChild ptVaInCurPart  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) s  entry false in * ; trivial.
rewrite getFstShadowAddDerivation with partition descChild ptVaInCurPart  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) s entry false
 in *;trivial.
assert(Hmapped : forall pd va,  getMappedPage pd s' va =
getMappedPage pd s va).
intros.
apply getMappedPageAddDerivation with entry; trivial.
rewrite Hmapped in *. clear Hmapped.
 unfold propagatedPropertiesAddVaddr in * .
assert(Hcurpart : In currentPart (getPartitions pageRootPartition s)).
{
  clear Hor.
  intuition.
  subst.
  unfold consistency in *.
  assert(Hcur : currentPartitionInPartitionsList s) by intuition.
  apply Hcur;trivial. }
   assert(Hpde : partitionDescriptorEntry s ).
   { unfold consistency in *.
     intuition. }
  assert(Hnodup : noDupConfigPagesList s).
  {  clear Hor.
  intuition.
  subst.
  unfold consistency in *. intuition. }    
assert(Horparts : currentPart = partition \/ currentPart <> partition) by apply
pageDecOrNot.
unfold propagatedPropertiesAddVaddr in *.
assert(Hlevel :  Some level = StateLib.getNbLevel  ) by intuition.
destruct Horparts as [Horparts | Horparts].
- assert(Horvar: false = StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInCurrentPartition level \/ 
                true = StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInCurrentPartition level).
  { destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInCurrentPartition level);trivial.
    right;trivial. left;trivial. }
 destruct Horvar as [Horvar | Horvar].
 + assert( getPDFlag sh1 va s' =getPDFlag sh1 va s /\
getVirtualAddressSh1 sh1 s' va = getVirtualAddressSh1 sh1 s va) as(HgetPdflag & Hgetvirt). 
{ unfold getPDFlag.
  unfold getVirtualAddressSh1.
  rewrite <- Hlevel.
  assert(Hind :getIndirection sh1 va level (nbLevel - 1) s'
  =getIndirection sh1 va level (nbLevel - 1) s).
  apply getIndirectionAddDerivation with entry;trivial.
  rewrite Hind. clear Hind.
  case_eq(getIndirection sh1 va level (nbLevel - 1) s);
  [intros ind Hind | intros Hind];[|split;trivial].
  
  case_eq(Nat.eqb ind pageDefault);intros Heqind.
  assert(Hbof :  (Nat.eqb pageDefault ind) = true).
  apply NPeano.Nat.eqb_eq.
  apply beq_nat_true in Heqind.
  subst;trivial.
  destruct pageDefault;destruct ind;simpl in *;subst;trivial.
  rewrite Hbof.
  split;trivial.
assert(Hnotsameind : ind <> ptVaInCurPart \/ (StateLib.getIndexOfAddr va levelMin) <>
(StateLib.getIndexOfAddr vaInCurrentPartition levelMin) ).
{ apply pageTablesOrIndicesAreDifferent with sh1 sh1 level nbLevel s;trivial.
apply sh1PartNotNull with currentPart s;trivial.
apply nextEntryIsPPgetFstShadow;subst;trivial.
apply sh1PartNotNull with currentPart s;trivial.
apply nextEntryIsPPgetFstShadow;subst;trivial.
  apply noDupConfigPagesListNoDupGetIndirections with currentPart idxShadow1;trivial.
  intuition.
  right;left;trivial.
  apply nextEntryIsPPgetFstShadow;subst;trivial.
    unfold noDupConfigPagesList in Hnodup. 
      apply noDupConfigPagesListNoDupGetIndirections with currentPart idxShadow1;trivial.
  intuition.
  right;left;trivial.
  apply nextEntryIsPPgetFstShadow;subst;trivial.
    unfold noDupConfigPagesList in Hnodup. 
  rewrite Horvar.
  rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
  left;split;trivial.
  apply getNbLevelEq;trivial.
  apply beq_nat_false in Heqind.
  unfold not; intros Htmp;subst;now contradict Heqind.
  assert(Hnotnull : (Nat.eqb pageDefault ptVaInCurPart) = false) by intuition.
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
assert(Haux :getIndirection sh1 vaInCurrentPartition level (nbLevel -1) s = Some ptVaInCurPart). 
  apply getIndirectionGetTableRoot with partition;trivial.
  rewrite Hlevel;trivial.
  intros.
  split;subst;trivial.
  intuition;subst;trivial.
  intuition.
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

  
  assert(Hreadpd :  StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readPDflagAddDerivation;trivial.
    
    rewrite Hreadpd;trivial.
  assert(Hreadvir :  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readVirEntryAddDerivation;trivial.
  rewrite Hreadvir. split; trivial.  }
 rewrite HgetPdflag.
 rewrite Hgetvirt.
 apply Hwell with partition pd;trivial.
 + subst partition.
 assert(Heqmap : getMappedPage pd s va = getMappedPage pd s vaInCurrentPartition).
  apply getMappedPageEq with level;trivial.
  symmetry;trivial.
  symmetry;trivial.
  assert(currentPD = pd). 
  { clear Hor.  apply getPdNextEntryIsPPEq with currentPart s;intuition. }
  subst pd.
  assert(Hmykey : getMappedPage currentPD s vaInCurrentPartition = SomePage phyVaChild). 
  { clear Hor.  apply getMappedPageGetTableRoot with ptVaInCurPartpd currentPart;intuition;
  subst;trivial.
  repeat rewrite andb_true_iff in Hlegit;intuition;subst;trivial. }
  rewrite Heqmap in *.
  rewrite Hmykey in *.
  now contradict H4.
  
- 

assert( getPDFlag sh1 va s' =getPDFlag sh1 va s /\
getVirtualAddressSh1 sh1 s' va = getVirtualAddressSh1 sh1 s va) as(HgetPdflag & Hgetvirt). 
{ unfold getPDFlag.
  unfold getVirtualAddressSh1.
  rewrite <- Hlevel.
  assert(Hind :getIndirection sh1 va level (nbLevel - 1) s'
  =getIndirection sh1 va level (nbLevel - 1) s).
  apply getIndirectionAddDerivation with entry;trivial.
  rewrite Hind. clear Hind.
  case_eq(getIndirection sh1 va level (nbLevel - 1) s);
  [intros ind Hind | intros Hind];[|split;trivial].
  
  case_eq(Nat.eqb ind pageDefault);intros Heqind.
  assert(Hbof :  (Nat.eqb pageDefault ind) = true).
  apply NPeano.Nat.eqb_eq.
  apply beq_nat_true in Heqind.
  subst;trivial.
  destruct pageDefault;destruct ind;simpl in *;subst;trivial.
  rewrite Hbof.
  split;trivial.
assert(Hnotsameind : ind <> ptVaInCurPart).
  {
  assert(Hdist : Lib.disjoint (getConfigPages currentPart s) (getConfigPages partition s)).
  { assert(Hconfdif : configTablesAreDifferent s).
    unfold consistency in *.
    intuition. 
    apply Hconfdif;trivial. }
  assert(Hin1 : In ind (getConfigPages partition s)).
  { unfold getConfigPages.
    simpl.
    right.
    apply inGetIndirectionsAuxInConfigPagesSh1 with sh1;trivial.
    apply getIndirectionInGetIndirections with va level (nbLevel - 1);trivial. 
    apply nbLevelNotZero.
    apply beq_nat_false in Heqind.
    trivial.
    unfold not;intros;subst; now contradict Heqind.
    apply getNbLevelLe;trivial.
    apply sh1PartNotNull with partition s;trivial.
    apply nextEntryIsPPgetFstShadow;trivial. }
  assert(Hin2 : In ptVaInCurPart (getConfigPages currentPart s)).
  { apply isConfigTableSh1WithVE with vaInCurrentPartition;trivial.
    intros;subst;split;intuition.
    intuition. }
    unfold  Lib.disjoint in *.
    unfold not in Hdist.
    unfold not;intros Hfalse.
    apply Hdist with  ptVaInCurPart;trivial.
    subst;trivial. }
  
  assert(Hreadpd :  StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readPDflagAddDerivation;trivial.
  left. 
  
    trivial.
    
    rewrite Hreadpd;trivial.
  assert(Hreadvir :  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readVirEntryAddDerivation;trivial.
  left;trivial.
  rewrite Hreadvir. split; trivial.  }
 rewrite HgetPdflag.
 rewrite Hgetvirt.
 apply Hwell with partition pd;trivial. 
 
Qed.
Lemma wellFormedFstShadowIfDefaultValuesUpdtateSh1Structure  entry  s vaInCurrentPartition vaChild currentPart
     currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
     idxvaInCurPart vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap
     ptDescChildpd idxDescChild1 presentDescPhy phyDescChild pdChildphy
     ptVaChildpd idxvaChild presentvaChild phyVaChild sh2Childphy
     ptVaChildsh2 level  :

 lookup ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) = Some false \/
StateLib.readPDflag ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) = None) -> 
wellFormedFstShadowIfDefaultValues s -> 
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 

 propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
     currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
     idxvaInCurPart vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap
     ptDescChildpd idxDescChild1 presentDescPhy phyDescChild pdChildphy
     ptVaChildpd idxvaChild presentvaChild phyVaChild sh2Childphy
     ptVaChildsh2 level -> 
   StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
   Some vaInCurrentPartition 
   -> 
wellFormedFstShadowIfDefaultValues
{|
      currentPartition := currentPartition s;
      memory := add ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin)
                  (VE {| pd := false; va := descChild |}) (memory s) pageEq
                  idxEq |} .
Proof.

intros Hlookup Hor Hwell.
intros Hlegit.
unfold wellFormedFstShadowIfDefaultValues in *.
intros.
simpl in *.
set(s':= {|  currentPartition := _ |}) in *.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
rewrite getPdAddDerivation with partition descChild ptVaInCurPart  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) s  entry false in * ; trivial.
rewrite getFstShadowAddDerivation with partition descChild ptVaInCurPart  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) s entry false
 in *;trivial.
assert(Hmapped : forall pd va,  getMappedPage pd s' va =
getMappedPage pd s va).
intros.
apply getMappedPageAddDerivation with entry; trivial.
rewrite Hmapped in *. clear Hmapped.
 unfold propagatedPropertiesAddVaddr in * .
assert(Hcurpart : In currentPart (getPartitions pageRootPartition s)).
{
  clear Hor.
  intuition.
  subst.
  unfold consistency in *.
  assert(Hcur : currentPartitionInPartitionsList s) by intuition.
  apply Hcur;trivial. }
   assert(Hpde : partitionDescriptorEntry s ).
   { unfold consistency in *.
     intuition. }
  assert(Hnodup : noDupConfigPagesList s).
  {  clear Hor.
  intuition.
  subst.
  unfold consistency in *. intuition. }    
assert(Horparts : currentPart = partition \/ currentPart <> partition) by apply
pageDecOrNot.
unfold propagatedPropertiesAddVaddr in *.
assert(Hlevel :  Some level = StateLib.getNbLevel  ) by intuition.
destruct Horparts as [Horparts | Horparts].
- assert(Horvar: false = StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInCurrentPartition level \/ 
                true = StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInCurrentPartition level).
  { destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInCurrentPartition level);trivial.
    right;trivial. left;trivial. }
 destruct Horvar as [Horvar | Horvar].
 + assert( getPDFlag sh1 va s' =getPDFlag sh1 va s /\
getVirtualAddressSh1 sh1 s' va = getVirtualAddressSh1 sh1 s va) as(HgetPdflag & Hgetvirt). 
{ unfold getPDFlag.
  unfold getVirtualAddressSh1.
  rewrite <- Hlevel.
  assert(Hind :getIndirection sh1 va level (nbLevel - 1) s'
  =getIndirection sh1 va level (nbLevel - 1) s).
  apply getIndirectionAddDerivation with entry;trivial.
  rewrite Hind. clear Hind.
  case_eq(getIndirection sh1 va level (nbLevel - 1) s);
  [intros ind Hind | intros Hind];[|split;trivial].
  
  case_eq(Nat.eqb ind pageDefault);intros Heqind.
  assert(Hbof :  (Nat.eqb pageDefault ind) = true).
  apply NPeano.Nat.eqb_eq.
  apply beq_nat_true in Heqind.
  subst;trivial.
  destruct pageDefault;destruct ind;simpl in *;subst;trivial.
  rewrite Hbof.
  split;trivial.
assert(Hnotsameind : ind <> ptVaInCurPart \/ (StateLib.getIndexOfAddr va levelMin) <>
(StateLib.getIndexOfAddr vaInCurrentPartition levelMin) ).
{ apply pageTablesOrIndicesAreDifferent with sh1 sh1 level nbLevel s;trivial.
apply sh1PartNotNull with currentPart s;trivial.
apply nextEntryIsPPgetFstShadow;subst;trivial.
apply sh1PartNotNull with currentPart s;trivial.
apply nextEntryIsPPgetFstShadow;subst;trivial.
  apply noDupConfigPagesListNoDupGetIndirections with currentPart idxShadow1;trivial.
  intuition.
  right;left;trivial.
  apply nextEntryIsPPgetFstShadow;subst;trivial.
    unfold noDupConfigPagesList in Hnodup. 
      apply noDupConfigPagesListNoDupGetIndirections with currentPart idxShadow1;trivial.
  intuition.
  right;left;trivial.
  apply nextEntryIsPPgetFstShadow;subst;trivial.
    unfold noDupConfigPagesList in Hnodup. 
  rewrite Horvar.
  rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
  left;split;trivial.
  apply getNbLevelEq;trivial.
  apply beq_nat_false in Heqind.
  unfold not; intros Htmp;subst;now contradict Heqind.
  assert(Hnotnull : (Nat.eqb pageDefault ptVaInCurPart) = false) by intuition.
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
assert(Haux :getIndirection sh1 vaInCurrentPartition level (nbLevel -1) s = Some ptVaInCurPart). 
  apply getIndirectionGetTableRoot with partition;trivial.
  rewrite Hlevel;trivial.
  intros.
  split;subst;trivial.
  intuition;subst;trivial.
  intuition.
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

  
  assert(Hreadpd :  StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readPDflagAddDerivation;trivial.
    
    rewrite Hreadpd;trivial.
  assert(Hreadvir :  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readVirEntryAddDerivation;trivial.
  rewrite Hreadvir. split; trivial.  }
 rewrite HgetPdflag.
 rewrite Hgetvirt.
 apply Hwell with partition pd;trivial.
 + subst partition.
 assert(Heqmap : getMappedPage pd s va = getMappedPage pd s vaInCurrentPartition).
  apply getMappedPageEq with level;trivial.
  symmetry;trivial.
  symmetry;trivial.
  assert(currentPD = pd). 
  { clear Hor.  apply getPdNextEntryIsPPEq with currentPart s;intuition. }
  subst pd.
  assert(Hmykey : getMappedPage currentPD s vaInCurrentPartition = SomePage phyVaChild). 
  { clear Hor.  apply getMappedPageGetTableRoot with ptVaInCurPartpd currentPart;intuition;
  subst;trivial.
  repeat rewrite andb_true_iff in Hlegit;intuition;subst;trivial. }
  rewrite Heqmap in *.
  rewrite Hmykey in *.
  now contradict H4.
  
- 

assert( getPDFlag sh1 va s' =getPDFlag sh1 va s /\
getVirtualAddressSh1 sh1 s' va = getVirtualAddressSh1 sh1 s va) as(HgetPdflag & Hgetvirt). 
{ unfold getPDFlag.
  unfold getVirtualAddressSh1.
  rewrite <- Hlevel.
  assert(Hind :getIndirection sh1 va level (nbLevel - 1) s'
  =getIndirection sh1 va level (nbLevel - 1) s).
  apply getIndirectionAddDerivation with entry;trivial.
  rewrite Hind. clear Hind.
  case_eq(getIndirection sh1 va level (nbLevel - 1) s);
  [intros ind Hind | intros Hind];[|split;trivial].
  
  case_eq(Nat.eqb ind pageDefault);intros Heqind.
  assert(Hbof :  (Nat.eqb pageDefault ind) = true).
  apply NPeano.Nat.eqb_eq.
  apply beq_nat_true in Heqind.
  subst;trivial.
  destruct pageDefault;destruct ind;simpl in *;subst;trivial.
  rewrite Hbof.
  split;trivial.
assert(Hnotsameind : ind <> ptVaInCurPart).
  {
  assert(Hdist : Lib.disjoint (getConfigPages currentPart s) (getConfigPages partition s)).
  { assert(Hconfdif : configTablesAreDifferent s).
    unfold consistency in *.
    intuition. 
    apply Hconfdif;trivial. }
  assert(Hin1 : In ind (getConfigPages partition s)).
  { unfold getConfigPages.
    simpl.
    right.
    apply inGetIndirectionsAuxInConfigPagesSh1 with sh1;trivial.
    apply getIndirectionInGetIndirections with va level (nbLevel - 1);trivial. 
    apply nbLevelNotZero.
    apply beq_nat_false in Heqind.
    trivial.
    unfold not;intros;subst; now contradict Heqind.
    apply getNbLevelLe;trivial.
    apply sh1PartNotNull with partition s;trivial.
    apply nextEntryIsPPgetFstShadow;trivial. }
  assert(Hin2 : In ptVaInCurPart (getConfigPages currentPart s)).
  { apply isConfigTableSh1WithVE with vaInCurrentPartition;trivial.
    intros;subst;split;intuition.
    intuition. }
    unfold  Lib.disjoint in *.
    unfold not in Hdist.
    unfold not;intros Hfalse.
    apply Hdist with  ptVaInCurPart;trivial.
    subst;trivial. }
  
  assert(Hreadpd :  StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readPDflagAddDerivation;trivial.
  left. 
  
    trivial.
    
    rewrite Hreadpd;trivial.
  assert(Hreadvir :  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readVirEntryAddDerivation;trivial.
  left;trivial.
  rewrite Hreadvir. split; trivial.  }
 rewrite HgetPdflag.
 rewrite Hgetvirt.
 apply Hwell with partition pd;trivial. 
 
Qed.
Lemma wellFormedFstShadowIfNoneUpdtateSh1StructureX  entry  s vaInCurrentPartition  
      descChild   ptVaInCurPart
           presentmap
         
         
      level  (phyVaChild ptVaInCurPartpd currentPD: page):

lookup ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) = Some false \/
StateLib.readPDflag ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) = None) -> 
wellFormedFstShadowIfNone s -> 
configTablesAreDifferent s -> 
presentmap = true -> 
  Some level = StateLib.getNbLevel -> 
  currentPartitionInPartitionsList s -> 
partitionDescriptorEntry s -> 
noDupConfigPagesList s -> 
(Nat.eqb pageDefault ptVaInCurPart) = false -> 
isVE ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) s -> 
getTableAddrRoot ptVaInCurPart idxShadow1 (currentPartition s)
  vaInCurrentPartition s  -> 
nextEntryIsPP (currentPartition s) idxPageDir currentPD s -> 
isPE ptVaInCurPartpd (StateLib.getIndexOfAddr vaInCurrentPartition levelMin)
  s ->
getTableAddrRoot ptVaInCurPartpd idxPageDir (currentPartition s)
  vaInCurrentPartition s -> 
(Nat.eqb pageDefault ptVaInCurPartpd) = false -> 
isEntryPage ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) phyVaChild s -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) true s -> 
wellFormedFstShadowIfNone
{|
      currentPartition := currentPartition s;
      memory := add ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin)
                  (VE {| pd := false; va := descChild |}) (memory s) pageEq
                  idxEq |} .
Proof.
intros Hlookup Hor Hwell Hconfdif Hlegit Hlevel Hcur Hpde Hnodup Hnotnull.
unfold wellFormedFstShadowIfNone in *.
intros.

simpl in *.
set(s':= {|  currentPartition := _ |}) in *.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
rewrite getPdAddDerivation with partition descChild ptVaInCurPart  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) s  entry false in * ; trivial.
rewrite getFstShadowAddDerivation with partition descChild ptVaInCurPart  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) s entry false
 in *;trivial.
assert(Hmapped : forall pd va,  getMappedPage pd s' va =
getMappedPage pd s va).
intros.
apply getMappedPageAddDerivation with entry; trivial.
rewrite Hmapped in *. clear Hmapped.
 unfold propagatedPropertiesAddVaddr in * .
assert(Hcurpart : In (currentPartition s) (getPartitions pageRootPartition s)).
{
  clear Hor.
  intuition. }    
assert(Horparts : (currentPartition s) = partition \/ (currentPartition s) <> partition) by apply
pageDecOrNot.
(* unfold propagatedPropertiesAddVaddr in *. *)
destruct Horparts as [Horparts | Horparts].
- assert(Horvar: false = StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInCurrentPartition level \/ 
                true = StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInCurrentPartition level).
  { destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInCurrentPartition level);trivial.
    right;trivial. left;trivial. }
 destruct Horvar as [Horvar | Horvar].
 + assert( getPDFlag sh1 va s' =getPDFlag sh1 va s /\
getVirtualAddressSh1 sh1 s' va = getVirtualAddressSh1 sh1 s va) as(HgetPdflag & Hgetvirt). 
{ unfold getPDFlag.
  unfold getVirtualAddressSh1.
  rewrite <- Hlevel.
  assert(Hind :getIndirection sh1 va level (nbLevel - 1) s'
  =getIndirection sh1 va level (nbLevel - 1) s).
  apply getIndirectionAddDerivation with entry;trivial.
  rewrite Hind. clear Hind.
  case_eq(getIndirection sh1 va level (nbLevel - 1) s);
  [intros ind Hind | intros Hind];[|split;trivial].
  
  case_eq(Nat.eqb ind pageDefault);intros Heqind.
  assert(Hbof :  (Nat.eqb pageDefault ind) = true).
  apply NPeano.Nat.eqb_eq.
  apply beq_nat_true in Heqind.
  subst;trivial.
  destruct pageDefault;destruct ind;simpl in *;subst;trivial.
  rewrite Hbof.
  split;trivial.

assert(Hnotsameind : ind <> ptVaInCurPart \/ (StateLib.getIndexOfAddr va levelMin) <>
(StateLib.getIndexOfAddr vaInCurrentPartition levelMin) ).
{ apply pageTablesOrIndicesAreDifferent with sh1 sh1 level nbLevel s;trivial.
apply sh1PartNotNull with (currentPartition s) s;trivial.
apply nextEntryIsPPgetFstShadow;subst;trivial.
apply sh1PartNotNull with (currentPartition s) s;trivial.
apply nextEntryIsPPgetFstShadow;subst;trivial.
  apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) idxShadow1;trivial.
  intuition.
  right;left;trivial.
  apply nextEntryIsPPgetFstShadow;subst;trivial.
    unfold noDupConfigPagesList in Hnodup. 
      apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) idxShadow1;trivial.
  intuition.
  right;left;trivial.
  apply nextEntryIsPPgetFstShadow;subst;trivial.
    unfold noDupConfigPagesList in Hnodup. 
  rewrite Horvar.
  rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
  left;split;trivial.
  apply getNbLevelEq;trivial.
  apply beq_nat_false in Heqind.
  unfold not; intros Htmp;subst;now contradict Heqind.
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
assert(Haux :getIndirection sh1 vaInCurrentPartition level (nbLevel -1) s = Some ptVaInCurPart). 
  apply getIndirectionGetTableRoot with (currentPartition s);trivial.
  rewrite Hlevel;trivial.
  intros.
  split;subst;trivial.
  clear Hor.
  intuition;subst;trivial.
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

  
  assert(Hreadpd :  StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readPDflagAddDerivation;trivial.
    
    rewrite Hreadpd;trivial.
  assert(Hreadvir :  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readVirEntryAddDerivation;trivial.
  rewrite Hreadvir. split; trivial.  }
 rewrite HgetPdflag.
 rewrite Hgetvirt.
 apply Hwell with partition pd;trivial.
 + subst partition.
 assert(Heqmap : getMappedPage pd s va = getMappedPage pd s vaInCurrentPartition).
  apply getMappedPageEq with level;trivial.
  symmetry;trivial.
  symmetry;trivial.
   assert(currentPD = pd). 
  { clear Hor.  apply getPdNextEntryIsPPEq with (currentPartition s) s;intuition. }
  subst pd. 
  assert(Hmykey : getMappedPage currentPD s vaInCurrentPartition = SomePage phyVaChild). 
  { clear Hor.  apply getMappedPageGetTableRoot with ptVaInCurPartpd (currentPartition s);intuition;
  subst;trivial.  }
  rewrite Heqmap in *.
  rewrite Hmykey in *.
  now contradict H4.
  
- 

assert( getPDFlag sh1 va s' =getPDFlag sh1 va s /\
getVirtualAddressSh1 sh1 s' va = getVirtualAddressSh1 sh1 s va) as(HgetPdflag & Hgetvirt). 
{ unfold getPDFlag.
  unfold getVirtualAddressSh1.
  rewrite <- Hlevel.
  assert(Hind :getIndirection sh1 va level (nbLevel - 1) s'
  =getIndirection sh1 va level (nbLevel - 1) s).
  apply getIndirectionAddDerivation with entry;trivial.
  rewrite Hind. clear Hind.
  case_eq(getIndirection sh1 va level (nbLevel - 1) s);
  [intros ind Hind | intros Hind];[|split;trivial].
  
  case_eq(Nat.eqb ind pageDefault);intros Heqind.
  assert(Hbof :  (Nat.eqb pageDefault ind) = true).
  apply NPeano.Nat.eqb_eq.
  apply beq_nat_true in Heqind.
  subst;trivial.
  destruct pageDefault;destruct ind;simpl in *;subst;trivial.
  rewrite Hbof.
  split;trivial.
assert(Hnotsameind : ind <> ptVaInCurPart).
  {
  assert(Hdist : Lib.disjoint (getConfigPages (currentPartition s) s) (getConfigPages partition s)).
  {
    apply Hconfdif;trivial. }
  assert(Hin1 : In ind (getConfigPages partition s)).
  { unfold getConfigPages.
    simpl.
    right.
    apply inGetIndirectionsAuxInConfigPagesSh1 with sh1;trivial.
    apply getIndirectionInGetIndirections with va level (nbLevel - 1);trivial. 
    apply nbLevelNotZero.
    apply beq_nat_false in Heqind.
    trivial.
    unfold not;intros;subst; now contradict Heqind.
    apply getNbLevelLe;trivial.
    apply sh1PartNotNull with partition s;trivial.
    apply nextEntryIsPPgetFstShadow;trivial. }
  assert(Hin2 : In ptVaInCurPart (getConfigPages (currentPartition s) s)).
  { apply isConfigTableSh1WithVE with vaInCurrentPartition;trivial.
    intros;subst;split;intuition. }
    unfold  Lib.disjoint in *.
    unfold not in Hdist.
    unfold not;intros Hfalse.
    apply Hdist with  ptVaInCurPart;trivial.
    subst;trivial. }
  
  assert(Hreadpd :  StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readPDflagAddDerivation;trivial.
  left. 
  
    trivial.
    
    rewrite Hreadpd;trivial.
  assert(Hreadvir :  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readVirEntryAddDerivation;trivial.
  left;trivial.
  rewrite Hreadvir. split; trivial.  }
 rewrite HgetPdflag.
 rewrite Hgetvirt.
 apply Hwell with partition pd;trivial.
 
Qed.

Lemma wellFormedFstShadowIfDefaultValuesUpdtateSh1StructureX  entry  s vaInCurrentPartition  
      descChild   ptVaInCurPart
           presentmap
         
         
      level  (phyVaChild ptVaInCurPartpd currentPD: page):

lookup ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) = Some false \/
StateLib.readPDflag ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) = None) -> 
wellFormedFstShadowIfDefaultValues s -> 
configTablesAreDifferent s -> 
presentmap = true -> 
  Some level = StateLib.getNbLevel -> 
  currentPartitionInPartitionsList s -> 
partitionDescriptorEntry s -> 
noDupConfigPagesList s -> 
(Nat.eqb pageDefault ptVaInCurPart) = false -> 
isVE ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) s -> 
getTableAddrRoot ptVaInCurPart idxShadow1 (currentPartition s)
  vaInCurrentPartition s  -> 
nextEntryIsPP (currentPartition s) idxPageDir currentPD s -> 
isPE ptVaInCurPartpd (StateLib.getIndexOfAddr vaInCurrentPartition levelMin)
  s ->
getTableAddrRoot ptVaInCurPartpd idxPageDir (currentPartition s)
  vaInCurrentPartition s -> 
(Nat.eqb pageDefault ptVaInCurPartpd) = false -> 
isEntryPage ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) phyVaChild s -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) true s -> 
wellFormedFstShadowIfDefaultValues
{|
      currentPartition := currentPartition s;
      memory := add ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin)
                  (VE {| pd := false; va := descChild |}) (memory s) pageEq
                  idxEq |} .
Proof.
intros Hlookup Hor Hwell Hconfdif Hlegit Hlevel Hcur Hpde Hnodup Hnotnull.
unfold wellFormedFstShadowIfDefaultValues in *.
intros.

simpl in *.
set(s':= {|  currentPartition := _ |}) in *.
assert(Hgetparts : getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
{ apply getPartitionsAddDerivation with entry; trivial. }
rewrite Hgetparts in *.
clear Hgetparts.
rewrite getPdAddDerivation with partition descChild ptVaInCurPart  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) s  entry false in * ; trivial.
rewrite getFstShadowAddDerivation with partition descChild ptVaInCurPart  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) s entry false
 in *;trivial.
assert(Hmapped : forall pd va,  getMappedPage pd s' va =
getMappedPage pd s va).
intros.
apply getMappedPageAddDerivation with entry; trivial.
rewrite Hmapped in *. clear Hmapped.
 unfold propagatedPropertiesAddVaddr in * .
assert(Hcurpart : In (currentPartition s) (getPartitions pageRootPartition s)).
{
  clear Hor.
  intuition. }    
assert(Horparts : (currentPartition s) = partition \/ (currentPartition s) <> partition) by apply
pageDecOrNot.
(* unfold propagatedPropertiesAddVaddr in *. *)
destruct Horparts as [Horparts | Horparts].
- assert(Horvar: false = StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInCurrentPartition level \/ 
                true = StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInCurrentPartition level).
  { destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInCurrentPartition level);trivial.
    right;trivial. left;trivial. }
 destruct Horvar as [Horvar | Horvar].
 + assert( getPDFlag sh1 va s' =getPDFlag sh1 va s /\
getVirtualAddressSh1 sh1 s' va = getVirtualAddressSh1 sh1 s va) as(HgetPdflag & Hgetvirt). 
{ unfold getPDFlag.
  unfold getVirtualAddressSh1.
  rewrite <- Hlevel.
  assert(Hind :getIndirection sh1 va level (nbLevel - 1) s'
  =getIndirection sh1 va level (nbLevel - 1) s).
  apply getIndirectionAddDerivation with entry;trivial.
  rewrite Hind. clear Hind.
  case_eq(getIndirection sh1 va level (nbLevel - 1) s);
  [intros ind Hind | intros Hind];[|split;trivial].
  
  case_eq(Nat.eqb ind pageDefault);intros Heqind.
  assert(Hbof :  (Nat.eqb pageDefault ind) = true).
  apply NPeano.Nat.eqb_eq.
  apply beq_nat_true in Heqind.
  subst;trivial.
  destruct pageDefault;destruct ind;simpl in *;subst;trivial.
  rewrite Hbof.
  split;trivial.

assert(Hnotsameind : ind <> ptVaInCurPart \/ (StateLib.getIndexOfAddr va levelMin) <>
(StateLib.getIndexOfAddr vaInCurrentPartition levelMin) ).
{ apply pageTablesOrIndicesAreDifferent with sh1 sh1 level nbLevel s;trivial.
apply sh1PartNotNull with (currentPartition s) s;trivial.
apply nextEntryIsPPgetFstShadow;subst;trivial.
apply sh1PartNotNull with (currentPartition s) s;trivial.
apply nextEntryIsPPgetFstShadow;subst;trivial.
  apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) idxShadow1;trivial.
  intuition.
  right;left;trivial.
  apply nextEntryIsPPgetFstShadow;subst;trivial.
    unfold noDupConfigPagesList in Hnodup. 
      apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) idxShadow1;trivial.
  intuition.
  right;left;trivial.
  apply nextEntryIsPPgetFstShadow;subst;trivial.
    unfold noDupConfigPagesList in Hnodup. 
  rewrite Horvar.
  rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
  left;split;trivial.
  apply getNbLevelEq;trivial.
  apply beq_nat_false in Heqind.
  unfold not; intros Htmp;subst;now contradict Heqind.
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
assert(Haux :getIndirection sh1 vaInCurrentPartition level (nbLevel -1) s = Some ptVaInCurPart). 
  apply getIndirectionGetTableRoot with (currentPartition s);trivial.
  rewrite Hlevel;trivial.
  intros.
  split;subst;trivial.
  clear Hor.
  intuition;subst;trivial.
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

  
  assert(Hreadpd :  StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readPDflagAddDerivation;trivial.
    
    rewrite Hreadpd;trivial.
  assert(Hreadvir :  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readVirEntryAddDerivation;trivial.
  rewrite Hreadvir. split; trivial.  }
 rewrite HgetPdflag.
 rewrite Hgetvirt.
 apply Hwell with partition pd;trivial.
 + subst partition.
 assert(Heqmap : getMappedPage pd s va = getMappedPage pd s vaInCurrentPartition).
  apply getMappedPageEq with level;trivial.
  symmetry;trivial.
  symmetry;trivial.
   assert(currentPD = pd). 
  { clear Hor.  apply getPdNextEntryIsPPEq with (currentPartition s) s;intuition. }
  subst pd. 
  assert(Hmykey : getMappedPage currentPD s vaInCurrentPartition = SomePage phyVaChild). 
  { clear Hor.  apply getMappedPageGetTableRoot with ptVaInCurPartpd (currentPartition s);intuition;
  subst;trivial.  }
  rewrite Heqmap in *.
  rewrite Hmykey in *.
  now contradict H4.
  
- 

assert( getPDFlag sh1 va s' =getPDFlag sh1 va s /\
getVirtualAddressSh1 sh1 s' va = getVirtualAddressSh1 sh1 s va) as(HgetPdflag & Hgetvirt). 
{ unfold getPDFlag.
  unfold getVirtualAddressSh1.
  rewrite <- Hlevel.
  assert(Hind :getIndirection sh1 va level (nbLevel - 1) s'
  =getIndirection sh1 va level (nbLevel - 1) s).
  apply getIndirectionAddDerivation with entry;trivial.
  rewrite Hind. clear Hind.
  case_eq(getIndirection sh1 va level (nbLevel - 1) s);
  [intros ind Hind | intros Hind];[|split;trivial].
  
  case_eq(Nat.eqb ind pageDefault);intros Heqind.
  assert(Hbof :  (Nat.eqb pageDefault ind) = true).
  apply NPeano.Nat.eqb_eq.
  apply beq_nat_true in Heqind.
  subst;trivial.
  destruct pageDefault;destruct ind;simpl in *;subst;trivial.
  rewrite Hbof.
  split;trivial.
assert(Hnotsameind : ind <> ptVaInCurPart).
  {
  assert(Hdist : Lib.disjoint (getConfigPages (currentPartition s) s) (getConfigPages partition s)).
  {
    apply Hconfdif;trivial. }
  assert(Hin1 : In ind (getConfigPages partition s)).
  { unfold getConfigPages.
    simpl.
    right.
    apply inGetIndirectionsAuxInConfigPagesSh1 with sh1;trivial.
    apply getIndirectionInGetIndirections with va level (nbLevel - 1);trivial. 
    apply nbLevelNotZero.
    apply beq_nat_false in Heqind.
    trivial.
    unfold not;intros;subst; now contradict Heqind.
    apply getNbLevelLe;trivial.
    apply sh1PartNotNull with partition s;trivial.
    apply nextEntryIsPPgetFstShadow;trivial. }
  assert(Hin2 : In ptVaInCurPart (getConfigPages (currentPartition s) s)).
  { apply isConfigTableSh1WithVE with vaInCurrentPartition;trivial.
    intros;subst;split;intuition. }
    unfold  Lib.disjoint in *.
    unfold not in Hdist.
    unfold not;intros Hfalse.
    apply Hdist with  ptVaInCurPart;trivial.
    subst;trivial. }
  
  assert(Hreadpd :  StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readPDflag ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readPDflagAddDerivation;trivial.
  left. 
  
    trivial.
    
    rewrite Hreadpd;trivial.
  assert(Hreadvir :  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readVirEntryAddDerivation;trivial.
  left;trivial.
  rewrite Hreadvir. split; trivial.  }
 rewrite HgetPdflag.
 rewrite Hgetvirt.
 apply Hwell with partition pd;trivial.
 
Qed.

Lemma consistencyUpdtateSh1Structure entry  s vaInCurrentPartition  
      descChild   ptVaInCurPart
           presentmap
         
         
      level  (phyVaChild ptVaInCurPartpd currentPD: page):
vaddrEq vaddrDefault descChild = false -> 
lookup ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) pageEq idxEq = Some (VE entry) -> 
(StateLib.readPDflag ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) = Some false \/
StateLib.readPDflag ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s) = None) -> 
 wellFormedFstShadowIfNone s  ->
wellFormedFstShadowIfDefaultValues s -> 
configTablesAreDifferent s -> 
presentmap = true -> 
  Some level = StateLib.getNbLevel -> 
  currentPartitionInPartitionsList s -> 
partitionDescriptorEntry s -> 
noDupConfigPagesList s -> 
(Nat.eqb pageDefault ptVaInCurPart) = false -> 
isVE ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) s -> 
getTableAddrRoot ptVaInCurPart idxShadow1 (currentPartition s)
  vaInCurrentPartition s  -> 
nextEntryIsPP (currentPartition s) idxPageDir currentPD s -> 
isPE ptVaInCurPartpd (StateLib.getIndexOfAddr vaInCurrentPartition levelMin)
  s ->
getTableAddrRoot ptVaInCurPartpd idxPageDir (currentPartition s)
  vaInCurrentPartition s -> 
(Nat.eqb pageDefault ptVaInCurPartpd) = false -> 
isEntryPage ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) phyVaChild s -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) true s -> 
consistency s -> 
consistency
  {|
  currentPartition := currentPartition s;
  memory := add ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) 
  (VE {| pd := false; va := descChild |}) 
              (memory s) pageEq idxEq |}.
Proof.
(* dataStructurePdSh1Sh2asRootintros. *)
unfold consistency in *.
split.
apply partitionDescriptorEntryAddDerivation with entry; intuition.
split.
apply dataStructurePdSh1Sh2asRootAddDerivation with entry; intuition.
split.
apply dataStructurePdSh1Sh2asRootAddDerivation with entry; intuition.
split.
apply dataStructurePdSh1Sh2asRootAddDerivation with entry; intuition.
split.
apply currentPartitionInPartitionsListAddDerivation with entry; intuition.
split.
apply noDupMappedPagesListAddDerivation with entry; intuition.
split.
apply noDupConfigPagesListAddDerivation with entry; intuition.
split.
apply parentInPartitionListAddDerivation with entry; intuition.
split.
apply accessibleVAIsNotPartitionDescriptorAddDerivation with entry; intuition.
split.
apply accessibleChildPageIsAccessibleIntoParentAddDerivation with entry;intuition.
split.
apply noCycleInPartitionTreeUpdtateSh1Structure with entry;intuition.
split.
apply configTablesAreDifferentUpdtateSh1Structure with entry ;intuition.
split.
apply isChildUpdtateSh1Structure with entry ;intuition.
split.
apply isPresentNotDefaultIffAddDerivation ;intuition.
split. 
apply physicalPageNotDerivedAddDerivation with entry;intuition.
split.
apply multiplexerWithoutParentUpdtateSh1Structure with entry;intuition.
split.
apply isParentUpdtateSh1Structure with entry;intuition.
split.
apply noDupPartitionTreeUpdtateSh1Structure with entry;intuition.
split.
apply wellFormedFstShadowUpdtateSh1Structure with entry ;intuition.
split.
apply wellFormedSndShadowUpdtateSh1Structure with entry;intuition.
split.
apply wellFormedShadowsUpdtateSh1Structure with entry;intuition.
split.
apply wellFormedShadowsUpdtateSh1Structure with entry;intuition.
split.
intuition.
split. 
apply  wellFormedFstShadowIfNoneUpdtateSh1StructureX  with entry presentmap level
phyVaChild ptVaInCurPartpd currentPD;trivial.
apply  wellFormedFstShadowIfDefaultValuesUpdtateSh1StructureX  with entry presentmap level
phyVaChild ptVaInCurPartpd currentPD;trivial.
Qed.



Lemma getTableRootAddDerivation table1 idx1 table2 idx2 partition   
va idxVa (descChild : vaddr) entry (s : state) f :
lookup table2 idx2 (memory s) pageEq idxEq = Some (VE entry) ->
StateLib.getIndexOfAddr va levelMin = idxVa ->
(forall idx : index,
      StateLib.getIndexOfAddr va levelMin = idx ->
      f table1 idx s /\ getTableAddrRoot table1 idx1 partition va s) -> 
getTableAddrRoot table1 idx1 partition va
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2 (VE {| pd := false; va := descChild |}) 
              (memory s) pageEq idxEq |}.
Proof.
intros Hentry Hidxva (* Hpp *) Htableroot .
apply Htableroot in Hidxva.
destruct Hidxva as (Hpe & Hget).
clear Htableroot.
unfold getTableAddrRoot in *.
destruct Hget as (Hor & Hget).
split ;trivial; clear Hor.
intros tableroot Hpp.
rewrite <- nextEntryIsPPAddDerivation with entry in Hpp; trivial.
apply Hget in Hpp.
destruct Hpp as (nbL & Hnbl & stop & Hstop & Hgetind).
exists nbL;split; trivial.
exists stop; split;trivial.
rewrite <- Hgetind.
apply getIndirectionAddDerivation with entry; trivial.
Qed.

Lemma entryPresentFlagAddDerivation table1 idx1 table2 idx2   flag
 (descChild : vaddr) entry (s : state):
lookup table2 idx2 (memory s) pageEq idxEq = Some (VE entry) -> 
entryPresentFlag table1 idx1 flag s ->
entryPresentFlag table1 idx1 flag
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2 (VE {| pd := false; va := descChild |}) 
              (memory s) pageEq idxEq |}.
Proof.
intros Hentry Hep.
unfold entryPresentFlag in *.
cbn.
case_eq (beqPairs (table2, idx2) (table1, idx1) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry in *.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  table1 idx1 (removeDup table2 idx2(memory s) pageEq idxEq)
           pageEq idxEq = lookup  table1 idx1  (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma isEntryVAAddDerivation table1 idx1 table2 idx2 va 
 (descChild : vaddr) (s : state):
table1 <> table2 \/ idx1 <> idx2 -> 
isEntryVA table1 idx1 va s -> 
isEntryVA table1 idx1 va
    {|
    currentPartition := currentPartition s;
    memory := add table2 idx2 (VE {| pd := false; va := descChild |}) 
                (memory s) pageEq idxEq |} .
Proof.
intros Hentry Hva.
unfold isEntryVA in *.
cbn.
assert(Hfalse : beqPairs (table2, idx2) (table1, idx1) pageEq idxEq = false).
apply beqPairsFalse; intuition.

rewrite Hfalse.
assert (lookup  table1 idx1 (removeDup table2 idx2(memory s) pageEq idxEq)
           pageEq idxEq = lookup  table1 idx1  (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.


Lemma isEntryPageAddDerivation table1 idx1 table2 idx2  addr
 (descChild : vaddr) entry (s : state):
lookup table2 idx2 (memory s) pageEq idxEq = Some (VE entry) -> 
isEntryPage table1 idx1 addr s ->
isEntryPage table1 idx1 addr 
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2 (VE {| pd := false; va := descChild |}) 
              (memory s) pageEq idxEq |}.
Proof.
intros Hentry Hep.
unfold isEntryPage in *.
cbn.
case_eq (beqPairs (table2, idx2) (table1, idx1) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry in *.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  table1 idx1 (removeDup table2 idx2(memory s) pageEq idxEq)
           pageEq idxEq = lookup  table1 idx1  (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma entryUserFlagAddDerivation table1 idx1 table2 idx2   flag
 (descChild : vaddr) entry (s : state):
lookup table2 idx2 (memory s) pageEq idxEq = Some (VE entry) -> 
entryUserFlag table1 idx1 flag s ->
entryUserFlag table1 idx1 flag
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2 (VE {| pd := false; va := descChild |}) 
              (memory s) pageEq idxEq |}.
Proof.
intros Hentry Heu.
unfold entryUserFlag in *.
cbn.
case_eq (beqPairs (table2, idx2) (table1, idx1) pageEq idxEq);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry in *.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  table1 idx1 (removeDup table2 idx2(memory s) pageEq idxEq)
           pageEq idxEq = lookup  table1 idx1  (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma isPartitionFalseAddDerivation table idx descChild s :
isPartitionFalse table idx 
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := descChild |}) 
              (memory s) pageEq idxEq |}.
Proof.
unfold isPartitionFalse.
cbn.
left.
unfold StateLib.readPDflag.
cbn.
assert(Htrue : beqPairs (table, idx) (table, idx) pageEq idxEq = true).
apply beqPairsTrue;split;trivial.
rewrite Htrue.
cbn;trivial.
Qed.

Lemma isEntryVASameValue table1 table2 idx1 idx2 vaValue  s : 
isEntryVA table1 idx1 vaValue s ->
isEntryVA table1 idx1 vaValue
{| currentPartition := currentPartition s;
   memory := add table2 idx2 (VE {| pd := false; va := vaValue |}) 
            (memory s) pageEq idxEq |}.
Proof.
unfold isEntryVA.
cbn.
case_eq(beqPairs (table2, idx2) (table1, idx1) pageEq idxEq);
intros * Hpairs;simpl;trivial.
assert(lookup table1 idx1 (removeDup table2 idx2 (memory s) pageEq idxEq) 
pageEq idxEq = lookup table1 idx1 (memory s) pageEq idxEq ).
apply beqPairsFalse in Hpairs.
apply removeDupIdentity;intuition.
rewrite H.
trivial. 
Qed.
Lemma checkChildTrueSameValue a nbL s entry descChild ptRefChildFromSh1
currentPart:
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild levelMin) (memory s) pageEq idxEq =
Some (VE entry) -> 
checkChild currentPart nbL s a = true -> 
checkChild currentPart nbL {|
currentPartition := currentPartition s;
memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild levelMin)
    (VE {| pd := true; va := va entry |}) (memory s) pageEq idxEq |} a = true. 
Proof.
set(s' := {|
currentPartition := currentPartition s;
memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild levelMin) (VE {| pd := true; va := va entry |})
(memory s) pageEq idxEq |} ) in*. 
intros Hlookup Hi.
unfold checkChild in *.
assert(Hsh1S : StateLib.getFstShadow currentPart (memory s') =
  StateLib.getFstShadow currentPart (memory s))by (
apply getFstShadowAddDerivation with entry;trivial). 
rewrite Hsh1S . clear Hsh1S.
case_eq (StateLib.getFstShadow currentPart (memory s) );[intros sh1 Hsh1 |
intros Hsh1]; 
rewrite Hsh1 in *;trivial.
assert(HindS: getIndirection sh1 a nbL (nbLevel - 1) s' =
getIndirection sh1 a nbL (nbLevel - 1) s) by (
apply getIndirectionAddDerivation with entry;trivial).
rewrite HindS in *;clear HindS. 
case_eq(StateLib.getIndirection sh1 a nbL (nbLevel - 1) s);
[ intros ind Hind| intros Hind];rewrite Hind in *;trivial.
case_eq (Nat.eqb ind pageDefault);intros Hindnotnil;
rewrite Hindnotnil in *;trivial.
unfold StateLib.readPDflag in *.
simpl in *. 
case_eq ( beqPairs (ptRefChildFromSh1, StateLib.getIndexOfAddr descChild levelMin)
(ind, StateLib.getIndexOfAddr a levelMin) pageEq idxEq);
intros Hpairs;
simpl;trivial.
apply beqPairsFalse in Hpairs.
assert(Hmemory : lookup ind (StateLib.getIndexOfAddr a levelMin) (memory s) pageEq idxEq =
lookup ind (StateLib.getIndexOfAddr a levelMin)
(removeDup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild levelMin) (memory s) pageEq idxEq) pageEq
idxEq).
rewrite removeDupIdentity;trivial.
intuition.
rewrite <- Hmemory.
trivial.
Qed.
    
        

Lemma writeVirEntryAddVaddr vaInCurrentPartition vaChild currentPart
     currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
     idxvaInCurPart vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc
     presentmap
     ptDescChildpd idxDescChild1 presentDescPhy phyDescChild pdChildphy
     ptVaChildpd idxvaChild presentvaChild phyVaChild sh2Childphy
     ptVaChildsh2 level :
     isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
negb presentDescPhy = false -> 
{{ fun s : state =>
   propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
     currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
     idxvaInCurPart vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap
     ptDescChildpd idxDescChild1 presentDescPhy phyDescChild pdChildphy
     ptVaChildpd idxvaChild presentvaChild phyVaChild sh2Childphy
     ptVaChildsh2 level /\
   StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
   Some vaInCurrentPartition }} 
  MAL.writeVirEntry ptVaInCurPart idxvaInCurPart descChild 
  {{ fun _ s => propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
     currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
     idxvaInCurPart descChild (negb isnotderiv) currentPD ptVaInCurPartpd accessiblesrc presentmap
     ptDescChildpd idxDescChild1 presentDescPhy phyDescChild pdChildphy
     ptVaChildpd idxvaChild presentvaChild phyVaChild sh2Childphy
     ptVaChildsh2 level /\
   StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
   Some vaInCurrentPartition /\
(*    StateLib.readVirEntry ptVaInCurPart idxvaInCurPart (memory s) = Some descChild /\ *)
   isPartitionFalse ptVaInCurPart idxvaInCurPart s /\
   (forall child : page, (* child <> phyDescChild ->  *)
    In child (getChildren currentPart s) -> ~ In phyVaChild (getMappedPages child s))
   }}.
Proof.
intros Hlegit Hlegit1.
eapply weaken.
eapply WP.writeVirEntry.
intros;simpl.
unfold propagatedPropertiesAddVaddr in *.
assert(Hlegitbis : isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true) by trivial.
repeat rewrite andb_true_iff in Hlegit. 
assert(Hparts : In currentPart (getPartitions pageRootPartition s)).
{ intuition. subst.
  unfold consistency in *.
  unfold currentPartitionInPartitionsList in *.
  intuition. }
assert(Hcursh1 :(exists entry : page,
        nextEntryIsPP currentPart idxShadow1 entry s /\ entry <> pageDefault)).
{ assert(Hpde: partitionDescriptorEntry s) by (unfold consistency in *;intuition).
  apply Hpde;intuition.  }
destruct Hcursh1 as (currentShadow1 & Hcursh1 & Hsh1notnul).
(** use physicalPageNotDerived and isChild  to get a contradiction *)
assert(HderivShadow1 : ~ isDerived currentPart vaInCurrentPartition s ).
{ unfold not;intros Hgoal.
  intuition. subst.
  contradict Hgoal. apply vaNotDerived with ptVaInCurPart;trivial. 
  exists vainve;split;trivial. 
  intros. 
  subst;split;trivial. }
assert(Hsh1 : forall child, In child (getChildren currentPart s) ->
              ~ In phyVaChild (getMappedPages child s)).
{ intros.
  unfold not;intros Hgoal.
  intuition. subst.
  contradict Hgoal.
  
   apply phyNotDerived  with (currentPartition s) currentPD vaInCurrentPartition 
  ptVaInCurPartpd;intuition;subst; trivial. }
assert(Hlookup :exists entry, 
 lookup ptVaInCurPart idxvaInCurPart (memory s) pageEq idxEq = Some (VE entry)).
{ assert(Hva : isVE ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) s) by intuition.
  unfold isVE in *.
  assert(Hidx :  StateLib.getIndexOfAddr vaInCurrentPartition levelMin = idxvaInCurPart) by intuition.
 subst. 
 destruct(lookup ptVaInCurPart
          (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) (memory s)
          );intros; try now contradict Hva.
 destruct v; try now contradict Hva.
 do 2 f_equal.
 exists v;trivial. }
destruct Hlookup as(v0 & Hlookup).
assert (Hreadflag : isPartitionFalse ptVaInCurPart idxvaInCurPart s ).
{ unfold isPartitionFalse.
unfold consistency in *. 
assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
unfold accessibleVAIsNotPartitionDescriptor in *.
assert (Hflag : getPDFlag currentShadow1 vaInCurrentPartition s = false).
{ apply Haccessva with currentPart currentPD phyVaChild.
  unfold consistency in *.
  unfold currentPartitionInPartitionsList in *.
  intuition.
  apply nextEntryIsPPgetPd; intuition.
  apply nextEntryIsPPgetFstShadow;intuition.
  intuition;subst.  
  apply isAccessibleMappedPage2  with (currentPartition s) ptVaInCurPartpd;trivial.
  intros;subst.
  split;trivial. }
apply getPDFlagReadPDflag with currentShadow1 vaInCurrentPartition currentPart;trivial.
intuition.
apply PeanoNat.Nat.eqb_neq.
assert(Hfalsepge : (Nat.eqb pageDefault ptVaInCurPart) = false) by trivial.
apply beq_nat_false in Hfalsepge.
unfold not;intros Hfalse'.
rewrite Hfalse' in Hfalsepge.    
now contradict Hfalsepge.
intuition.
intuition.
intuition.
subst;trivial. }
set (s' := {| currentPartition := _ |}) in *. 
assert(Hpartitions : getPartitions pageRootPartition s' = 
                    getPartitions pageRootPartition s).    
apply getPartitionsAddDerivation with v0;trivial.
assert(Hconfig :forall partition,  getConfigPagesAux partition s'
 = getConfigPagesAux partition s).
{ intros.
  apply getConfigPagesAuxAddDerivation with v0;trivial. }
assert(Hreadflag1 : StateLib.readPDflag ptDescChild idxDescChild
          (add ptVaInCurPart idxvaInCurPart (VE {| pd := false; va := descChild |})        
            (memory s) pageEq idxEq) = StateLib.readPDflag ptDescChild 
            idxDescChild                  (memory s)).
{ intuition. apply  readPDflagAddDerivation.
  apply toApplyPageTablesOrIndicesAreDifferent with descChild vaInCurrentPartition currentPart 
    currentShadow1 idxShadow1 level isVE  s;trivial.
  - right;left;trivial.
  - subst.
    assert(Hor: false = StateLib.checkVAddrsEqualityWOOffset nbLevel descChild vaInCurrentPartition level \/ 
                true = StateLib.checkVAddrsEqualityWOOffset nbLevel descChild vaInCurrentPartition level).
    { destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel descChild vaInCurrentPartition level);trivial.
      right;trivial. left;trivial. }
    destruct Hor as [Hor | Hor].
    trivial.
    assert(Hmyfalse : getMappedPage currentPD s descChild = getMappedPage currentPD s vaInCurrentPartition ).
    apply getMappedPageEq with level;trivial.
    intuition.
    intuition.
    assert(Hconfigchild : In phyDescChild (getConfigPages phyDescChild s)).
    { unfold getConfigPages. simpl;left;trivial. }
    assert (Haccessible: In phyVaChild (getAccessibleMappedPages (currentPartition s) s)).
    { apply physicalPageIsAccessible with
      ptVaInCurPartpd vaInCurrentPartition
    (StateLib.getIndexOfAddr vaInCurrentPartition levelMin) true level true currentPD;trivial.
    intros;subst;split;trivial. }
    assert(Hmap1 : getMappedPage currentPD s descChild = SomePage phyDescChild). 
    { apply getMappedPageGetTableRoot with ptDescChildpd (currentPartition s);trivial.
      intros;subst;split;trivial.
      apply negb_false_iff in Hlegit1.
      subst;trivial. }
    assert(Hmap2 : getMappedPage currentPD s vaInCurrentPartition = SomePage phyVaChild).
    { apply getMappedPageGetTableRoot with ptVaInCurPartpd (currentPartition s);trivial.
      intros;subst;split;trivial. }
    assert(Hkdi : kernelDataIsolation s) by trivial.
    unfold kernelDataIsolation in *.
    assert(Hmyfalse2 : phyDescChild <> phyVaChild). 
    unfold not; intros Hfalse.
    unfold Lib.disjoint in *.
    contradict Hconfigchild. 
    apply Hkdi with (currentPartition s);trivial.
    apply childrenPartitionInPartitionList with (currentPartition s); trivial.
    unfold consistency in *.
    intuition.
    subst;trivial.
    rewrite Hmap2 in *.
    rewrite Hmap1 in *.
    inversion Hmyfalse. 
    subst;now contradict Hmyfalse2.
  - intros;subst;split;trivial.
  - intros;subst;split;trivial. }
intuition.
(** partitionsIsolation **)
+ apply partitionsIsolationUpdtateSh1Structure with v0; trivial.
(** kernelDataIsolation **)
+ apply kernelDataIsolationUpdtateSh1Structure with v0; trivial.
(** VerticalSharing **)
+ apply verticalSharingUpdtateSh1Structure with v0; trivial.
(** consistency **)
+ subst idxvaInCurPart. unfold s'. 
 
   
 apply consistencyUpdtateSh1Structure with v0 presentmap level
phyVaChild ptVaInCurPartpd currentPD;subst;trivial.

unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
 (* beqVAddr defaultVAddr descChild = false*)
+ apply nextEntryIsPPAddDerivation with v0; trivial.
+ apply isVEAddDerivation with v0; trivial.
+ apply getTableRootAddDerivation with idxDescChild v0 isVE;trivial;intros;split;
  subst;trivial.
+ assert (HisPart : isPartitionFalse  ptVaInCurPart idxvaInCurPart s) by trivial.
  unfold isPartitionFalse in *.
  simpl in *.

  assert(Htrue : entryPDFlag ptDescChild idxDescChild true s) by trivial.
  unfold entryPDFlag in *.
  unfold StateLib.readPDflag in *. 
  simpl in *. 
  case_eq(lookup ptDescChild idxDescChild (memory s) pageEq idxEq);
  [intros look Hlook | intros Hlook];rewrite Hlook in *;try now contradict Htrue.
  destruct look;try now contradict Htrue.
  subst.   clear HisPart.
  destruct (beqPairs
                   (ptVaInCurPart,
                   StateLib.getIndexOfAddr vaInCurrentPartition levelMin)
                   (ptDescChild, StateLib.getIndexOfAddr descChild levelMin)
                   pageEq idxEq);trivial.
                   simpl.
  simpl in *.
  inversion Hreadflag1 as [Hii].
  rewrite <- Htrue in *.
  subst. now contradict Hii.
  destruct ( lookup ptDescChild
                 (StateLib.getIndexOfAddr descChild levelMin)
                 (removeDup ptVaInCurPart
                    (StateLib.getIndexOfAddr vaInCurrentPartition levelMin)
                    (memory s) pageEq idxEq) pageEq idxEq);
  try now contradict Hreadflag1.
  destruct v1;try now contradict Hreadflag1.
  inversion Hreadflag1 as [Hii].
  rewrite <- Htrue in *.
  rewrite Hii;trivial.
+ apply isVEAddDerivation with v0;trivial.
+ apply getTableRootAddDerivation with idxvaInCurPart v0 isVE;trivial;intros;split;
  subst;trivial.
+ unfold isEntryVA.
  cbn.
  assert(Hpairs :  beqPairs (ptVaInCurPart, idxvaInCurPart) (ptVaInCurPart, idxvaInCurPart)
      pageEq idxEq = true). 
  apply beqPairsTrue;split;trivial.
  rewrite Hpairs.
  simpl;trivial.
+ subst. trivial. (* beqVAddr defaultVAddr descChild = false*)
+ apply nextEntryIsPPAddDerivation with v0; trivial.
+ apply isPEAddDerivation with v0;trivial.
+ apply getTableRootAddDerivation with idxvaInCurPart v0 isPE;trivial;intros;split; 
  subst;trivial.
+ apply entryUserFlagAddDerivation with v0;trivial.
+ apply entryPresentFlagAddDerivation with v0;trivial.
+ apply isPEAddDerivation with v0;trivial.
+ apply getTableRootAddDerivation with idxDescChild1 v0 isPE;trivial;intros;split; 
  subst;trivial.
+ apply entryPresentFlagAddDerivation with v0;trivial.
+ apply isEntryPageAddDerivation with v0;trivial.
+ assert(In phyDescChild (getChildren (currentPartition s) s)) by trivial.
  assert(Hchildren : getChildren (currentPartition s) s = getChildren (currentPartition s') s'). 
  symmetry. unfold s'. apply getChildrenAddDerivation with v0;trivial.
  rewrite <- Hchildren;trivial.
+ apply nextEntryIsPPAddDerivation with v0; trivial.
+ apply isPEAddDerivation with v0;trivial.
+ apply getTableRootAddDerivation with idxvaChild v0 isPE;trivial;intros;split; 
  subst;trivial.
+ apply entryPresentFlagAddDerivation with v0;trivial.
+ apply isEntryPageAddDerivation with v0;trivial. 
+ apply nextEntryIsPPAddDerivation with v0; trivial.
+ apply isVAAddDerivation with v0;trivial.
+ apply getTableRootAddDerivation with idxvaChild v0 isVA;trivial;intros;split; 
  subst;trivial.
+ assert(Htrue : StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
     Some vaInCurrentPartition)
     by trivial.
  rewrite <-Htrue.
  apply readVirtualAddDerivation with v0;trivial.
+ unfold    isPartitionFalse.
  left.
  unfold StateLib.readPDflag; cbn. 
  assert(Hpairs :  beqPairs (ptVaInCurPart, idxvaInCurPart) (ptVaInCurPart, idxvaInCurPart)
      pageEq idxEq = true). 
  apply beqPairsTrue;split;trivial.
  rewrite Hpairs.
  simpl;trivial.
+ assert(Hnew : In phyVaChild (getMappedPages child s')) by trivial.
  contradict Hnew.
  assert(Hmaps : getMappedPages child s' = getMappedPages child s).
  apply getMappedPagesAddDerivation with v0;trivial.
  rewrite Hmaps in *.
  unfold not;intros.
  apply Hsh1 with child;trivial.
  assert(Hchildren : getChildren currentPart s = getChildren currentPart s').
  symmetry.
  apply getChildrenAddDerivation with v0;trivial.
  rewrite Hchildren in *;trivial.
Qed.
   
   
   


Lemma writeVirEntryPD     
pdChild currentPart currentPD level ptRefChild descChild idxRefChild 
 ptPDChild idxPDChild   ptSh1Child shadow1 idxSh1
  ptSh2Child shadow2 idxSh2   ptConfigPagesList 
idxConfigPagesList  
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2
derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild zero nullv idxPR idxPD idxSH1 idxSH2
idxSH3 idxPPR        
 :derivedRefChild && derivedPDChild && derivedSh1Child && derivedSh2Child && derivedRefChildListSh1 = true -> 
vaddrEq vaddrDefault descChild = false -> {{ fun s : state =>
   propagatedProperties false false false false pdChild currentPart currentPD level ptRefChild
            descChild idxRefChild true ptPDChild idxPDChild true ptSh1Child shadow1 idxSh1 true
            ptSh2Child shadow2 idxSh2 true ptConfigPagesList idxConfigPagesList true currentShadow1
            ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1
            derivedSh1Child childSh2 derivedSh2Child childListSh1 derivedRefChildListSh1 list
            phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
          newPropagatedProperties s zero nullv idxPR idxPD idxSH1 idxSH2
idxSH3 idxPPR  currentPart  level phyPDChild phySh1Child phySh2Child 
phyConfigPagesList phyDescChild  }} 
  MAL.writeVirEntry ptPDChildSh1 idxPDChild descChild {{ fun _ (s : state) =>
  propagatedProperties false false false false pdChild currentPart currentPD level ptRefChild
            descChild idxRefChild true ptPDChild idxPDChild true ptSh1Child shadow1 idxSh1 true
            ptSh2Child shadow2 idxSh2 true ptConfigPagesList idxConfigPagesList true currentShadow1
            ptRefChildFromSh1 derivedRefChild ptPDChildSh1 false ptSh1ChildFromSh1
            derivedSh1Child childSh2 derivedSh2Child childListSh1 derivedRefChildListSh1 list
            phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
          newPropagatedProperties s zero nullv idxPR idxPD idxSH1 idxSH2
idxSH3 idxPPR  currentPart  level phyPDChild phySh1Child phySh2Child 
phyConfigPagesList phyDescChild /\


    (forall child : page,
     In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) /\
    (forall child : page,
     In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) /\
    (forall child : page,
     In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) /\
    (forall child : page,
     In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) /\
    (forall child : page,
     In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) /\
   isEntryVA ptPDChildSh1 idxPDChild descChild s }}.
Proof. intros Hderiv Hnotdef.  
    eapply weaken.
    eapply WP.writeVirEntry.
    simpl; intros.
    set(s' :=  {|
  currentPartition := _ |} ) in *.
unfold propagatedProperties in *.
unfold newPropagatedProperties in *. 
repeat rewrite andb_true_iff in Hderiv. 
assert(Hparts : In currentPart (getPartitions pageRootPartition s)).
{ intuition. subst.
  unfold consistency in *.
  unfold currentPartitionInPartitionsList in *.
  intuition. }
repeat rewrite andb_true_iff in H.
(** use physicalPageNotDerived and isChild  to get a contradiction *)
assert(HderivShadow1 : ~ isDerived currentPart shadow1 s ).
{ unfold not;intros Hgoal.
  intuition. subst.
  contradict Hgoal.
  apply vaNotDerived with ptSh1ChildFromSh1;trivial. }
assert(Hsh1 : forall child, In child (getChildren currentPart s) ->
              ~ In phySh1Child (getMappedPages child s)).
{ intros.
  unfold not;intros Hgoal.
  intuition. subst.
  contradict Hgoal.
  apply phyNotDerived  with (currentPartition s) currentPD shadow1 ptSh1Child; trivial. }
assert(HderivPD : ~ isDerived currentPart pdChild s ).
{ unfold not;intros Hgoal.
  intuition. subst.
  contradict Hgoal.
  apply vaNotDerived with ptPDChildSh1 ;trivial. }
assert(HPD : forall child, In child (getChildren currentPart s) ->
     ~ In phyPDChild (getMappedPages child s)).
{ intros.
  unfold not;intros Hgoal.
  intuition. subst.
  contradict Hgoal.
  apply phyNotDerived  with (currentPartition s) currentPD pdChild ptPDChild ; trivial. }
assert(Hderivshadow2 : ~ isDerived currentPart shadow2 s ).
{ unfold not;intros Hgoal.
  intuition. subst.
  contradict Hgoal.
  apply vaNotDerived with childSh2 ;trivial. }
assert(Hsh2 : forall child, In child (getChildren currentPart s) ->
     ~ In phySh2Child (getMappedPages child s)).
{ intros.
  unfold not;intros Hgoal.
  intuition. subst.
  contradict Hgoal.
  apply phyNotDerived  with (currentPartition s) currentPD shadow2 ptSh2Child ; trivial. }
assert(Hderivlist : ~ isDerived currentPart list s ).
{ unfold not;intros Hgoal.
  intuition. subst.
  contradict Hgoal.
  apply vaNotDerived with childListSh1 ;trivial. }
assert(Hlist : forall child, In child (getChildren currentPart s) ->
     ~ In phyConfigPagesList (getMappedPages child s)).
{ intros.
  unfold not;intros Hgoal.
  intuition. subst.
  contradict Hgoal.
  apply phyNotDerived  with (currentPartition s) currentPD list ptConfigPagesList ; trivial. }
assert(Hderivdesc : ~ isDerived currentPart descChild s ).
{ unfold not;intros Hgoal.
  intuition. subst.
  contradict Hgoal.
  apply vaNotDerived with ptRefChildFromSh1 ;trivial. }
assert(Hdesc : forall child, In child (getChildren currentPart s) ->
     ~ In phyDescChild (getMappedPages child s)).
{ intros.
  unfold not;intros Hgoal.
  intuition. subst.
  contradict Hgoal.
  apply phyNotDerived  with (currentPartition s) currentPD descChild ptRefChild ; trivial. }
        
(*    assert(Hderiv := conj (conj ( conj ( conj Hdesc HPD ) Hsh1) Hsh2) Hlist).
    destruct H0 as (H0 & Hnew).
    do 57 rewrite <- and_assoc in H0.
    destruct H0 as (H0 & Hsplit).
    destruct H0 as (H0 & Hfalse). 

    assert (Hpost := conj (conj ( conj ( conj (conj (conj (conj H0 Hsplit)  Hnew) Hdesc) HPD ) Hsh1) Hsh2) Hlist).
    try repeat rewrite and_assoc in Hpost. 
    clear H0 Hfalse Hnew Hsplit.
    pattern s in Hpost.
    match type of Hpost with 
    |?HT s => instantiate (1 := fun tt s => HT s /\ 
                                isEntryVA ptPDChildSh1 idxPDChild descChild s)
    end. *)
simpl in *.
unfold propagatedProperties in *.
assert(Hget : forall idx : index,
              StateLib.getIndexOfAddr pdChild levelMin = idx ->
              isVE ptPDChildSh1 idx s /\ 
              getTableAddrRoot ptPDChildSh1 idxShadow1 currentPart pdChild s)
  by intuition.
assert (Hve :isVE ptPDChildSh1 idxPDChild s).
apply Hget.
intuition.
unfold isVE in Hve.
case_eq( lookup ptPDChildSh1 idxPDChild (memory s) pageEq idxEq);
intros; rewrite H0 in *; try now contradict Hve.
case_eq v ; intros;rewrite H1 in *; try now contradict Hve.
assert(Hpartitions : getPartitions pageRootPartition
        {|
        currentPartition := currentPartition s;
        memory := add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |})
                    (memory s) pageEq idxEq |} = 
                    getPartitions pageRootPartition
        s).
apply getPartitionsAddDerivation with v0;trivial.
unfold isPartitionFalse in *.
intuition.
assert(Hconfig :forall partition,  getConfigPagesAux partition
        {|
        currentPartition := currentPartition s;
        memory := add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |}) 
                    (memory s) pageEq idxEq |} = getConfigPagesAux partition s).
{ intros.
  apply getConfigPagesAuxAddDerivation with v0;trivial. }
    split. 
    do 3 rewrite <- and_assoc .
    split.
    (** partitionsIsolation **)
    do 2 rewrite and_assoc.
    split.
    assert (Hiso : partitionsIsolation s) by intuition.
    apply partitionsIsolationUpdtateSh1Structure with v0; trivial.
    assert(Hispart : isPartitionFalse ptPDChildSh1 idxPDChild s ) by intuition.
    unfold isPartitionFalse in *.
    assumption.
    (** kernelDataIsolation **)
    split.
    assert (Hkdi : kernelDataIsolation s) by intuition.
    apply kernelDataIsolationUpdtateSh1Structure with v0; trivial.
    assert(Hispart : isPartitionFalse ptPDChildSh1 idxPDChild s ) by intuition.
    unfold isPartitionFalse in *.
    assumption.
    (** VerticalSharing **)
    split.
    assert (Hvs : verticalSharing s) by intuition.
    apply verticalSharingUpdtateSh1Structure with v0; trivial.
    assert(Hispart : isPartitionFalse ptPDChildSh1 idxPDChild s ) by intuition.
    unfold isPartitionFalse in *.
    assumption.
    (** consistency **)
    assert (Hcons : consistency s ) by intuition.
    intuition.
    subst idxPDChild.
    assert(Hroot : forall idx : index,
      StateLib.getIndexOfAddr pdChild levelMin = idx ->
      isPE ptPDChild idx s /\
      getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s) by trivial.
    destruct Hroot with (StateLib.getIndexOfAddr pdChild levelMin)
    as (Hi1 & Hi2);trivial.
   assert(Hroot1 :forall idx : index,
      StateLib.getIndexOfAddr pdChild levelMin = idx ->
      isVE ptPDChildSh1 idx s /\
      getTableAddrRoot ptPDChildSh1 idxShadow1 currentPart pdChild s) by trivial.
    destruct Hroot1 with (StateLib.getIndexOfAddr pdChild levelMin)
    as (Hii1 & Hii2);trivial.
    
 apply consistencyUpdtateSh1Structure with v0 true level
phyPDChild ptPDChild currentPD;subst;trivial.

unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.

assert(Hispart : isPartitionFalse ptPDChildSh1 idxPDChild s ) by intuition.


    (** Propagate properties **)
    { 
     unfold s' in *. 
     intuition try trivial. 
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isPEAddDerivation with v0; trivial. 
      assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s)
      by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isPE ; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild levelMin = idx ->
                    isPE ptPDChild idx s /\ 
                    getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s ) by
       intuition.
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr shadow1 levelMin = idx ->
                  isPE ptSh1Child idx s /\ 
                  getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr shadow2 levelMin = idx ->
      isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child idxPageDir currentPart shadow2 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr list levelMin = idx ->
      isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList idxPageDir currentPart list s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr descChild levelMin = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 idxShadow1 currentPart descChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
         vaddrEq vaddrDefault va = derivedRefChild ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild
      pdChild   currentPart
      currentShadow1 idxShadow1 level isVE s ;trivial.
      right;left; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr pdChild levelMin = idx ->
       isVE ptPDChildSh1 idx s /\
       getTableAddrRoot ptPDChildSh1 idxShadow1 currentPart pdChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isVE; trivial.
    +    unfold isEntryVA.
    cbn.
    assert(Htrue : beqPairs (ptPDChildSh1, idxPDChild) (ptPDChildSh1, idxPDChild)
           pageEq idxEq = true).
    { apply beqPairsTrue.
      split; trivial. }
    rewrite Htrue.
    cbn;trivial.
    exists descChild;split;trivial. 
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow1 levelMin = idx ->
       isVE ptSh1ChildFromSh1 idx s /\
       getTableAddrRoot ptSh1ChildFromSh1 idxShadow1 currentPart shadow1 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA ptSh1ChildFromSh1 idxSh1  va s /\ 
         vaddrEq vaddrDefault va = derivedSh1Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1
      pdChild   currentPart
      currentShadow1 idxShadow1 level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow2 levelMin = idx ->
       isVE childSh2 idx s /\
       getTableAddrRoot childSh2 idxShadow1 currentPart shadow2 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA childSh2 idxSh2  va s /\ 
         vaddrEq vaddrDefault va = derivedSh2Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2
      pdChild   currentPart
      currentShadow1 idxShadow1 level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr list levelMin = idx ->
       isVE childListSh1 idx s /\
       getTableAddrRoot childListSh1 idxShadow1 currentPart list s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA  childListSh1 idxConfigPagesList  va s /\ 
         vaddrEq vaddrDefault va = derivedRefChildListSh1 ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with list
      pdChild   currentPart
      currentShadow1 idxShadow1 level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    
    +   rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial. 
      right;trivial.
    +  assert (HisPart : isPartitionFalse ptSh1ChildFromSh1 idxSh1 s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptSh1ChildFromSh1 idxSh1
                (add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag ptSh1ChildFromSh1 
                idxSh1 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1 pdChild currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.
    + assert (HisPart : isPartitionFalse childSh2 idxSh2 s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childSh2 idxSh2
                (add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag childSh2 idxSh2
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2 pdChild currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    + assert (HisPart : isPartitionFalse childListSh1 idxConfigPagesList s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childListSh1 idxConfigPagesList
                (add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag childListSh1
                 idxConfigPagesList
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with list pdChild currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    +  assert (HisPart : isPartitionFalse ptRefChildFromSh1 idxRefChild s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptRefChildFromSh1 idxRefChild
                (add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag ptRefChildFromSh1
                 idxRefChild  (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild pdChild currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
    + apply isPartitionFalseAddDerivation. }
    intuition try trivial.
    + 
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phyPDChild (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phySh1Child (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + 
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phySh2Child (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + 
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phyConfigPagesList (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    +
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phyDescChild (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + apply isWellFormedSndShadowUpdateMappedPageData;trivial. 
      unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse.
      apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 pdChild idxPDChild s ;
      trivial.
      right;left;trivial.
      unfold consistency in *.
      intuition.
    + apply isWellFormedFstShadowUpdateMappedPageData;trivial. 
      unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse.
      apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 pdChild idxPDChild s ;
      trivial.
      right;left;trivial.
      unfold consistency in *.
      intuition.
    + assert(Hii : forall idx : index,
      StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\
      StateLib.readPresent phyPDChild idx (memory s) = Some false)  by intuition.
      destruct Hii with idx as (Hi & _).
      rewrite <- Hi.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hii : forall idx : index,
      StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\
      StateLib.readPresent phyPDChild idx (memory s) = Some false)  by intuition.
      destruct Hii with idx as (_ & Hi).
      rewrite <- Hi.
      apply readPresentAddDerivation with v0;trivial.
    + assert(initConfigPagesListPostCondition phyConfigPagesList s) as (Hi1 & Hi2 & Hi3 & Hi4) by intuition.
      unfold initConfigPagesListPostCondition.
      split. 
      rewrite <- Hi1.
      apply readPhysicalAddDerivation with v0; trivial.
      split.
      rewrite <- Hi2.
      apply readVirtualAddDerivation with v0; trivial.
      split.
      intros idx Ha1 Ha2 Ha3.
      generalize (Hi3 idx Ha1 Ha2 Ha3);clear Hi3;intros Hi3.
      destruct Hi3 as (idxValue & Hi3).
      exists idxValue.
      rewrite <-Hi3.
      apply readIndexAddDerivation with v0; trivial.
      intros. 
      rewrite <- Hi4 with idx;trivial.
      apply readVirtualAddDerivation with v0; trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial. 
    + unfold s' in *.  rewrite getChildrenAddDerivation with  currentPart descChild
        ptPDChildSh1 idxPDChild v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        ptPDChildSh1 idxPDChild s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phyDescChild (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
   +     unfold s' in *.  rewrite getChildrenAddDerivation with  currentPart descChild
       ptPDChildSh1 idxPDChild v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        ptPDChildSh1 idxPDChild s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phyPDChild (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
    +     unfold s' in *.  rewrite getChildrenAddDerivation with  currentPart descChild
       ptPDChildSh1 idxPDChild v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        ptPDChildSh1 idxPDChild  s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phySh1Child  (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
    +     unfold s' in *.  rewrite getChildrenAddDerivation with  currentPart descChild
       ptPDChildSh1 idxPDChild v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        ptPDChildSh1 idxPDChild s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phySh2Child (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
     +     unfold s' in *.  rewrite getChildrenAddDerivation with  currentPart descChild
        ptPDChildSh1 idxPDChild v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        ptPDChildSh1 idxPDChild s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phyConfigPagesList(getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
    +
(** New property to propagate **)
    unfold isEntryVA.
    cbn.
    assert(Htrue : beqPairs (ptPDChildSh1, idxPDChild) (ptPDChildSh1, idxPDChild)
           pageEq idxEq = true).
    { apply beqPairsTrue.
      split; trivial. }
    rewrite Htrue.
    cbn;trivial.
Qed.

Lemma writeVirEntrySh1 pdChild currentPart currentPD level ptRefChild descChild idxRefChild 
 ptPDChild idxPDChild   ptSh1Child shadow1 idxSh1
  ptSh2Child shadow2 idxSh2   ptConfigPagesList 
idxConfigPagesList  
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2
derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild zero nullv idxPR idxPD idxSH1 idxSH2
idxSH3 idxPPR        
 :derivedRefChild && derivedPDChild && derivedSh1Child && derivedSh2Child && derivedRefChildListSh1 = true -> 
vaddrEq vaddrDefault descChild = false ->
{{ fun s : state =>
   propagatedProperties false false false false pdChild currentPart currentPD level
     ptRefChild descChild idxRefChild true ptPDChild idxPDChild true ptSh1Child
     shadow1 idxSh1 true ptSh2Child shadow2 idxSh2 true ptConfigPagesList
     idxConfigPagesList true currentShadow1 ptRefChildFromSh1 derivedRefChild
     ptPDChildSh1 false ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child
     childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child
     phyConfigPagesList phyDescChild s /\
   newPropagatedProperties s zero nullv idxPR idxPD idxSH1 idxSH2 idxSH3 idxPPR
     currentPart level phyPDChild phySh1Child phySh2Child phyConfigPagesList
     phyDescChild /\
   (forall child : page,
    In child (getChildren currentPart s) ->
    ~ In phyDescChild (getMappedPages child s)) /\
   (forall child : page,
    In child (getChildren currentPart s) ->
    ~ In phyPDChild (getMappedPages child s)) /\
   (forall child : page,
    In child (getChildren currentPart s) ->
    ~ In phySh1Child (getMappedPages child s)) /\
   (forall child : page,
    In child (getChildren currentPart s) ->
    ~ In phySh2Child (getMappedPages child s)) /\
   (forall child : page,
    In child (getChildren currentPart s) ->
    ~ In phyConfigPagesList (getMappedPages child s)) /\
   isEntryVA ptPDChildSh1 idxPDChild descChild s }} 
  MAL.writeVirEntry ptSh1ChildFromSh1 idxSh1 descChild {{  fun _ (s : state) =>
   propagatedProperties false false false false pdChild currentPart currentPD level
     ptRefChild descChild idxRefChild true ptPDChild idxPDChild true ptSh1Child
     shadow1 idxSh1 true ptSh2Child shadow2 idxSh2 true ptConfigPagesList
     idxConfigPagesList true currentShadow1 ptRefChildFromSh1 derivedRefChild
     ptPDChildSh1 false ptSh1ChildFromSh1 false childSh2 derivedSh2Child
     childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child
     phyConfigPagesList phyDescChild s /\
   newPropagatedProperties s zero nullv idxPR idxPD idxSH1 idxSH2 idxSH3 idxPPR
     currentPart level phyPDChild phySh1Child phySh2Child phyConfigPagesList
     phyDescChild /\
   (forall child : page,
    In child (getChildren currentPart s) ->
    ~ In phyDescChild (getMappedPages child s)) /\
   (forall child : page,
    In child (getChildren currentPart s) ->
    ~ In phyPDChild (getMappedPages child s)) /\
   (forall child : page,
    In child (getChildren currentPart s) ->
    ~ In phySh1Child (getMappedPages child s)) /\
   (forall child : page,
    In child (getChildren currentPart s) ->
    ~ In phySh2Child (getMappedPages child s)) /\
   (forall child : page,
    In child (getChildren currentPart s) ->
    ~ In phyConfigPagesList (getMappedPages child s)) /\
   isEntryVA ptPDChildSh1 idxPDChild descChild s /\  isEntryVA  ptSh1ChildFromSh1 idxSh1 descChild  s}}.
Proof.
intros Hderivation Hpost.
    eapply weaken.
    eapply WP.writeVirEntry.
    simpl; intros.
(*     destruct H0 as (H0 & Hnew).
    unfold propagatedProperties in *. 
    do 60 rewrite <- and_assoc in H0.
    destruct H0 as (H0 & Hsplit).
    destruct H0 as (H0 & Hfalse). 
    assert (Hpost := conj (conj H0 Hsplit)  Hnew).
    try repeat rewrite and_assoc in Hpost. 
    clear H0 Hfalse Hnew Hsplit.      
    pattern s in Hpost.
    match type of Hpost with 
    |?HT s => instantiate (1 := fun tt s => HT s /\ 
                                isEntryVA ptSh1ChildFromSh1 idxSh1 descChild s)
    end. *)
    simpl in *.
    unfold propagatedProperties in *.
    assert(Hget : forall idx : index,
                  StateLib.getIndexOfAddr shadow1 levelMin = idx ->
                  isVE ptSh1ChildFromSh1 idx s /\ 
                  getTableAddrRoot ptSh1ChildFromSh1 idxShadow1 currentPart shadow1 s)
      by intuition.
    assert (Hve :isVE ptSh1ChildFromSh1 idxSh1 s).
    apply Hget.
    intuition.
    unfold isVE in Hve.
    case_eq( lookup ptSh1ChildFromSh1 idxSh1 (memory s) pageEq idxEq);
    intros; rewrite H0 in *; try now contradict Hve.
    case_eq v ; intros;rewrite H1 in *; try now contradict Hve.
    assert(Hpartitions : getPartitions pageRootPartition
            {|
            currentPartition := currentPartition s;
            memory := add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |})
                        (memory s) pageEq idxEq |} = 
                        getPartitions pageRootPartition
            s).
    apply getPartitionsAddDerivation with v0;trivial.
    unfold isPartitionFalse in *.
    intuition.
    subst.
    split.
    do 3 rewrite <- and_assoc .
    assert(Hispart : isPartitionFalse ptSh1ChildFromSh1 idxSh1 s ) by intuition.
    subst.
    split.
    (** partitionsIsolation **)
    do 2 rewrite and_assoc.
    split.
    assert (Hiso : partitionsIsolation s) by intuition.
    apply partitionsIsolationUpdtateSh1Structure with v0; trivial.
    (** kernelDataIsolation **)
    split.
    assert (Hkdi : kernelDataIsolation s) by intuition.
    apply kernelDataIsolationUpdtateSh1Structure with v0; trivial.
    (** VerticalSharing **)
    split.
    assert (Hvs : verticalSharing s) by intuition.
    apply verticalSharingUpdtateSh1Structure with v0; trivial.   
    (** consistency **)
    assert (Hcons : consistency s ) by intuition.
    intuition.
    subst idxSh1.
    assert(Hroot : forall idx : index,
      StateLib.getIndexOfAddr shadow1 levelMin = idx ->
      isPE ptSh1Child idx s /\
      getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s) by trivial.
    destruct Hroot with (StateLib.getIndexOfAddr shadow1 levelMin)
    as (Hi1 & Hi2);trivial.
   assert(Hroot1 :forall idx : index,
      StateLib.getIndexOfAddr shadow1 levelMin = idx ->
      isVE ptSh1ChildFromSh1 idx s /\
      getTableAddrRoot ptSh1ChildFromSh1 idxShadow1 currentPart shadow1 s) by trivial.
    destruct Hroot1 with (StateLib.getIndexOfAddr shadow1 levelMin)
    as (Hii1 & Hii2);trivial.
    
 apply consistencyUpdtateSh1Structure with v0 true level
phySh1Child ptSh1Child currentPD;subst;trivial.

unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.



    (** Propagate properties **)
    { assert(Hconfig :forall partition,  getConfigPagesAux partition
            {|
            currentPartition := currentPartition s;
            memory := add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |}) 
                        (memory s) pageEq idxEq |} = getConfigPagesAux partition s).
      { intros.
        apply getConfigPagesAuxAddDerivation with v0;trivial. }
     intuition try trivial. 
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isPEAddDerivation with v0; trivial. 
      assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s)
      by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isPE ; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild levelMin = idx ->
                    isPE ptPDChild idx s /\ 
                    getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s ) by
       intuition.
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr shadow1 levelMin = idx ->
                  isPE ptSh1Child idx s /\ 
                  getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr shadow2 levelMin = idx ->
      isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child idxPageDir currentPart shadow2 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr list levelMin = idx ->
      isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList idxPageDir currentPart list s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr descChild levelMin = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 idxShadow1 currentPart descChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
         vaddrEq vaddrDefault va = derivedRefChild ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild
      shadow1   currentPart
      currentShadow1 idxShadow1 level isVE s ;trivial.
      right;left; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr pdChild levelMin = idx ->
       isVE ptPDChildSh1 idx s /\
       getTableAddrRoot ptPDChildSh1 idxShadow1 currentPart pdChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isVE; trivial.
    
    + exists descChild.
      split;trivial.
      apply isEntryVASameValue;trivial. 
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow1 levelMin = idx ->
       isVE ptSh1ChildFromSh1 idx s /\
       getTableAddrRoot ptSh1ChildFromSh1 idxShadow1 currentPart shadow1 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isVE; trivial.
(*     + assert (Hi : exists va : vaddr,
         isEntryVA ptSh1ChildFromSh1 idxSh1  va s /\ 
         beqVAddr defaultVAddr va = derivedSh1Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1
      pdChild   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial. *)
    + (** New property to propagate **)
      unfold isEntryVA.
      cbn.
      assert(Htrue : beqPairs (ptSh1ChildFromSh1, idxSh1) (ptSh1ChildFromSh1, idxSh1) 
      pageEq idxEq = true).
      { apply beqPairsTrue.
        split; trivial. }
      rewrite Htrue.
      cbn;trivial.
      exists descChild ; split;trivial. 
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow2 levelMin = idx ->
       isVE childSh2 idx s /\
       getTableAddrRoot childSh2 idxShadow1 currentPart shadow2 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA childSh2 idxSh2  va s /\ 
         vaddrEq vaddrDefault va = derivedSh2Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2
      shadow1   currentPart
      currentShadow1 idxShadow1 level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr list levelMin = idx ->
       isVE childListSh1 idx s /\
       getTableAddrRoot childListSh1 idxShadow1 currentPart list s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA  childListSh1 idxConfigPagesList  va s /\ 
         vaddrEq vaddrDefault va = derivedRefChildListSh1 ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with list
      shadow1   currentPart
      currentShadow1 idxShadow1 level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.

    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      rewrite <- Hconfig.
      unfold getConfigPages in *.
      simpl in *. trivial.
(*     + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial. 
      right;trivial. *)
    + apply isPartitionFalseAddDerivation.
(*     +  assert (HisPart : isPartitionFalse ptSh1ChildFromSh1 idxSh1 s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptSh1ChildFromSh1 idxSh1
                (add ptPDChildSh1 idxPDChild (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag ptSh1ChildFromSh1 
                idxSh1 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1 pdChild currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial. *)
    + assert (HisPart : isPartitionFalse childSh2 idxSh2 s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childSh2 idxSh2
                (add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag childSh2 idxSh2
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2 shadow1 currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    + assert (HisPart : isPartitionFalse childListSh1 idxConfigPagesList s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childListSh1 idxConfigPagesList
                (add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag childListSh1
                 idxConfigPagesList
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with list shadow1 currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    +  assert (HisPart : isPartitionFalse ptRefChildFromSh1 idxRefChild s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptRefChildFromSh1 idxRefChild
                (add ptSh1ChildFromSh1 idxSh1(VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag ptRefChildFromSh1
                 idxRefChild  (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild shadow1 currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
   +  assert (HisPart : isPartitionFalse ptPDChildSh1 idxPDChild s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptPDChildSh1 idxPDChild
                (add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag ptPDChildSh1 idxPDChild
                 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with pdChild shadow1 currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial. }
  { unfold newPropagatedProperties in *.
    intuition try trivial. 
     
    +  set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phyPDChild (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phySh1Child (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phySh2Child (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phyConfigPagesList (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phyDescChild (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial.  *)
    + apply isWellFormedSndShadowUpdateMappedPageData;trivial. 
      unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse.
      apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 shadow1 idxSh1 s ;
      trivial.
      right;left;trivial.
      subst.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
    + apply isWellFormedFstShadowUpdateMappedPageData;trivial. 
      unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse.
      apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 shadow1 idxSh1 s ;
      trivial.
      right;left;trivial.
      subst.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      unfold consistency in *.
      intuition.
    + assert(Hii : forall idx : index,
      StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\
      StateLib.readPresent phyPDChild idx (memory s) = Some false)  by intuition.
      destruct Hii with idx as (Hi & _).
      rewrite <- Hi.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hii : forall idx : index,
      StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\
      StateLib.readPresent phyPDChild idx (memory s) = Some false)  by intuition.
      destruct Hii with idx as (_ & Hi).
      rewrite <- Hi.
      apply readPresentAddDerivation with v0;trivial.
    + assert(initConfigPagesListPostCondition phyConfigPagesList s) as (Hi1 & Hi2 & Hi3 & Hi4) by intuition.
      unfold initConfigPagesListPostCondition.
      split. 
      rewrite <- Hi1.
      apply readPhysicalAddDerivation with v0; trivial.
      split.
      rewrite <- Hi2.
      apply readVirtualAddDerivation with v0; trivial.
      split.
      intros idx Ha1 Ha2 Ha3.
      generalize (Hi3 idx Ha1 Ha2 Ha3);clear Hi3;intros Hi3.
      destruct Hi3 as (idxValue & Hi3).
      exists idxValue.
      rewrite <-Hi3.
      apply readIndexAddDerivation with v0; trivial.
      intros. 
      rewrite <- Hi4 with idx;trivial.
      apply readVirtualAddDerivation with v0; trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + rewrite getChildrenAddDerivation with  currentPart descChild
        ptSh1ChildFromSh1 idxSh1 v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        ptSh1ChildFromSh1 idxSh1 s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phyDescChild (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
    + rewrite getChildrenAddDerivation with  currentPart descChild
       ptSh1ChildFromSh1 idxSh1 v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        ptSh1ChildFromSh1 idxSh1 s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phyPDChild (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
    + rewrite getChildrenAddDerivation with  currentPart descChild
       ptSh1ChildFromSh1 idxSh1 v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        ptSh1ChildFromSh1 idxSh1  s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phySh1Child  (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
    + rewrite getChildrenAddDerivation with  currentPart descChild
       ptSh1ChildFromSh1 idxSh1 v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        ptSh1ChildFromSh1 idxSh1 s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phySh2Child (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
     + rewrite getChildrenAddDerivation with  currentPart descChild
        ptSh1ChildFromSh1 idxSh1 v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
       ptSh1ChildFromSh1 idxSh1 s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phyConfigPagesList(getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial. 
    +
       apply isEntryVASameValue;trivial.
    + (** New property to propagate **)
      unfold isEntryVA.
      cbn.
      assert(Htrue : beqPairs (ptSh1ChildFromSh1, idxSh1) (ptSh1ChildFromSh1, idxSh1) 
      pageEq idxEq = true).
      { apply beqPairsTrue.
        split; trivial. }
      rewrite Htrue.
      cbn;trivial. }
Qed.

Lemma writeVirEntrySh2     
pdChild currentPart currentPD level ptRefChild descChild idxRefChild 
 ptPDChild idxPDChild   ptSh1Child shadow1 idxSh1
  ptSh2Child shadow2 idxSh2   ptConfigPagesList 
idxConfigPagesList  
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2
derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild zero nullv idxPR idxPD idxSH1 idxSH2
idxSH3 idxPPR        
 :derivedRefChild && derivedPDChild && derivedSh1Child && derivedSh2Child && derivedRefChildListSh1 = true -> 
vaddrEq vaddrDefault descChild = false ->
{{ fun s : state =>
   propagatedProperties false false false false pdChild currentPart currentPD level ptRefChild descChild idxRefChild true ptPDChild idxPDChild
     true ptSh1Child shadow1 idxSh1 true ptSh2Child shadow2 idxSh2 true ptConfigPagesList idxConfigPagesList true currentShadow1
     ptRefChildFromSh1 derivedRefChild ptPDChildSh1 false ptSh1ChildFromSh1 false childSh2 derivedSh2Child childListSh1 derivedRefChildListSh1
     list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
   newPropagatedProperties s zero nullv idxPR idxPD idxSH1 idxSH2 idxSH3 idxPPR currentPart level phyPDChild phySh1Child phySh2Child
     phyConfigPagesList phyDescChild /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) /\
   isEntryVA ptPDChildSh1 idxPDChild descChild s /\ isEntryVA ptSh1ChildFromSh1 idxSh1 descChild s }} 
  MAL.writeVirEntry childSh2 idxSh2 descChild 
  {{  fun _ (s : state) =>
   propagatedProperties false false false false pdChild currentPart currentPD level ptRefChild descChild idxRefChild true ptPDChild idxPDChild
     true ptSh1Child shadow1 idxSh1 true ptSh2Child shadow2 idxSh2 true ptConfigPagesList idxConfigPagesList true currentShadow1
     ptRefChildFromSh1 derivedRefChild ptPDChildSh1 false ptSh1ChildFromSh1 false childSh2 false childListSh1 derivedRefChildListSh1
     list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
   newPropagatedProperties s zero nullv idxPR idxPD idxSH1 idxSH2 idxSH3 idxPPR currentPart level phyPDChild phySh1Child phySh2Child
     phyConfigPagesList phyDescChild /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) /\
   isEntryVA ptPDChildSh1 idxPDChild descChild s /\ isEntryVA ptSh1ChildFromSh1 idxSh1 descChild s /\
   isEntryVA childSh2 idxSh2 descChild s }}.
  Proof.  
intros Hderived Hpost. 
    eapply weaken.
    eapply WP.writeVirEntry.
    simpl; intros.
(*     destruct H0 as (H0 & Hnew).
    unfold propagatedProperties in H0.
    do 60 rewrite <- and_assoc in H0.
    destruct H0 as (H0 & Hsplit).
    destruct H0 as (H0 & Hfalse). 
    assert (Hpost := conj (conj H0 Hsplit)  Hnew).
    try repeat rewrite and_assoc in Hpost. 
    clear H0 Hfalse Hnew Hsplit.      
    pattern s in Hpost.
    match type of Hpost with 
    |?HT s => instantiate (1 := fun tt s => HT s /\ 
                                isEntryVA childSh2 idxSh2 descChild s)
    end.
    simpl in *.
    split.  *)
    unfold propagatedProperties in *.
    assert(Hget : forall idx : index,
                  StateLib.getIndexOfAddr shadow2 levelMin = idx ->
                  isVE childSh2 idx s /\ 
                  getTableAddrRoot childSh2 idxShadow1 currentPart shadow2 s)
      by intuition.
    assert (Hve :isVE childSh2 idxSh2  s).
    apply Hget.
    intuition.
    unfold isVE in Hve.
    case_eq( lookup childSh2 idxSh2  (memory s) pageEq idxEq);
    intros; rewrite H0 in *; try now contradict Hve.
    case_eq v ; intros;rewrite H1 in *; try now contradict Hve.
    assert(Hpartitions : getPartitions pageRootPartition
            {|
            currentPartition := currentPartition s;
            memory := add childSh2 idxSh2  (VE {| pd := false; va := descChild |})
                        (memory s) pageEq idxEq |} = 
                        getPartitions pageRootPartition
            s).
    apply getPartitionsAddDerivation with v0;trivial.
    unfold isPartitionFalse in *.
    intuition.


    assert(Hispart : isPartitionFalse childSh2 idxSh2  s ) by intuition.
    assert(Hconfig :forall partition,  getConfigPagesAux partition
            {|
            currentPartition := currentPartition s;
            memory := add childSh2 idxSh2  (VE {| pd := false; va := descChild |}) 
                        (memory s) pageEq idxEq |} = getConfigPagesAux partition s).
      { intros.
        apply getConfigPagesAuxAddDerivation with v0;trivial. }
    split.    
    (** partitionsIsolation **)
(*     do 2 rewrite and_assoc. *)
    split. 
    assert (Hiso : partitionsIsolation s) by intuition.
    apply partitionsIsolationUpdtateSh1Structure with v0; trivial.
    (** kernelDataIsolation **)
    split.
    assert (Hkdi : kernelDataIsolation s) by intuition.
    apply kernelDataIsolationUpdtateSh1Structure with v0; trivial.
    (** VerticalSharing **)
    split.
    assert (Hvs : verticalSharing s) by intuition.
    apply verticalSharingUpdtateSh1Structure with v0; trivial.
    split.
        (** consistency **)
    assert (Hcons : consistency s ) by intuition.
    intuition.
    subst idxSh2.
    assert(Hroot : forall idx : index,
      StateLib.getIndexOfAddr shadow2 levelMin = idx ->
      isPE ptSh2Child idx s /\
      getTableAddrRoot ptSh2Child idxPageDir currentPart shadow2 s) by trivial.
    destruct Hroot with (StateLib.getIndexOfAddr shadow2 levelMin)
    as (Hi1 & Hi2);trivial.
   assert(Hroot1 :forall idx : index,
      StateLib.getIndexOfAddr shadow2 levelMin = idx ->
      isVE childSh2 idx s /\
      getTableAddrRoot childSh2 idxShadow1 currentPart shadow2 s) by trivial.
    destruct Hroot1 with (StateLib.getIndexOfAddr shadow2 levelMin)
    as (Hii1 & Hii2);trivial.
    
 apply consistencyUpdtateSh1Structure with v0 true level
phySh2Child ptSh2Child currentPD;subst;trivial.

unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.

    (** Propagate properties **)
    { 
     intuition try trivial. 
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isPEAddDerivation with v0; trivial. 
      assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s)
      by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isPE ; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild levelMin = idx ->
                    isPE ptPDChild idx s /\ 
                    getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s ) by
       intuition.
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr shadow1 levelMin = idx ->
                  isPE ptSh1Child idx s /\ 
                  getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr shadow2 levelMin = idx ->
      isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child idxPageDir currentPart shadow2 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr list levelMin = idx ->
      isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList idxPageDir currentPart list s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr descChild levelMin = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 idxShadow1 currentPart descChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
         vaddrEq vaddrDefault va = derivedRefChild ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild
      shadow2   currentPart
      currentShadow1 idxShadow1 level isVE s ;trivial.
      right;left; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr pdChild levelMin = idx ->
       isVE ptPDChildSh1 idx s /\
       getTableAddrRoot ptPDChildSh1 idxShadow1 currentPart pdChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isVE; trivial.
    + exists descChild.
      split;trivial.
      apply isEntryVASameValue;trivial. 
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow1 levelMin = idx ->
       isVE ptSh1ChildFromSh1 idx s /\
       getTableAddrRoot ptSh1ChildFromSh1 idxShadow1 currentPart shadow1 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isVE; trivial.
(*     + assert (Hi : exists va : vaddr,
         isEntryVA ptSh1ChildFromSh1 idxSh1  va s /\ 
         beqVAddr defaultVAddr va = derivedSh1Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1
      pdChild   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial. *)
     + exists descChild.
      split;trivial.
      apply isEntryVASameValue;trivial. 
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow2 levelMin = idx ->
       isVE childSh2 idx s /\
       getTableAddrRoot childSh2 idxShadow1 currentPart shadow2 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isVE; trivial. 
(** New property to propagate **)
    + unfold isEntryVA.
      cbn.
      assert(Htrue : beqPairs (childSh2, idxSh2) (childSh2, idxSh2) pageEq idxEq
        = true).
      { apply beqPairsTrue.
        split; trivial. }
      rewrite Htrue.
      cbn;trivial.
      exists descChild;split;trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr list levelMin = idx ->
       isVE childListSh1 idx s /\
       getTableAddrRoot childListSh1 idxShadow1 currentPart list s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA  childListSh1 idxConfigPagesList  va s /\ 
         vaddrEq vaddrDefault va = derivedRefChildListSh1 ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with list
      shadow2   currentPart
      currentShadow1 idxShadow1 level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *. 
      unfold getConfigPages in *. 
      rewrite Hconfig in *.
      simpl in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
   +  assert (HisPart : isPartitionFalse ptSh1ChildFromSh1 idxSh1 s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptSh1ChildFromSh1 idxSh1
                (add childSh2 idxSh2 (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag ptSh1ChildFromSh1 
                idxSh1 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1 shadow2 currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
    + apply isPartitionFalseAddDerivation. 
(*     + assert (HisPart : isPartitionFalse childSh2 idxSh2 s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childSh2 idxSh2
                (add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag childSh2 idxSh2
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2 shadow1 currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial. *)
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    + assert (HisPart : isPartitionFalse childListSh1 idxConfigPagesList s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childListSh1 idxConfigPagesList
                (add childSh2 idxSh2 (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag childListSh1
                 idxConfigPagesList
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with list shadow2 currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    +  assert (HisPart : isPartitionFalse ptRefChildFromSh1 idxRefChild s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptRefChildFromSh1 idxRefChild
                (add childSh2 idxSh2 (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag ptRefChildFromSh1
                 idxRefChild  (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild shadow2 currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
   +  assert (HisPart : isPartitionFalse ptPDChildSh1 idxPDChild s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptPDChildSh1 idxPDChild
                (add childSh2 idxSh2 (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag ptPDChildSh1 idxPDChild
                 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with pdChild shadow2 currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial. }
  { unfold newPropagatedProperties in *.
    intuition try trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phyPDChild (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phySh1Child (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phySh2Child (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phyConfigPagesList (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phyDescChild (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.  
      
    + apply isWellFormedSndShadowUpdateMappedPageData;trivial. 
      unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse.
      apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 shadow2 idxSh2 s ;
      trivial.
      right;left;trivial.
      subst.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
    + apply isWellFormedFstShadowUpdateMappedPageData;trivial. 
      unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse.
      apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 shadow2 idxSh2 s ;
      trivial.
      right;left;trivial.
      subst.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      unfold consistency in *.
      intuition.
    + assert(Hii : forall idx : index,
      StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\
      StateLib.readPresent phyPDChild idx (memory s) = Some false)  by intuition.
      destruct Hii with idx as (Hi & _).
      rewrite <- Hi.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hii : forall idx : index,
      StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\
      StateLib.readPresent phyPDChild idx (memory s) = Some false)  by intuition.
      destruct Hii with idx as (_ & Hi).
      rewrite <- Hi.
      apply readPresentAddDerivation with v0;trivial.
    + assert(initConfigPagesListPostCondition phyConfigPagesList s) as (Hi1 & Hi2 & Hi3 & Hi4) by intuition.
      unfold initConfigPagesListPostCondition.
      split. 
      rewrite <- Hi1.
      apply readPhysicalAddDerivation with v0; trivial.
      split.
      rewrite <- Hi2.
      apply readVirtualAddDerivation with v0; trivial.
      split.
      intros idx Ha1 Ha2 Ha3.
      generalize (Hi3 idx Ha1 Ha2 Ha3);clear Hi3;intros Hi3.
      destruct Hi3 as (idxValue & Hi3).
      exists idxValue.
      rewrite <-Hi3.
      apply readIndexAddDerivation with v0; trivial.
      intros. 
      rewrite <- Hi4 with idx;trivial.
      apply readVirtualAddDerivation with v0; trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + rewrite getChildrenAddDerivation with  currentPart descChild
        childSh2 idxSh2 v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        childSh2 idxSh2 s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phyDescChild (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
   + rewrite getChildrenAddDerivation with  currentPart descChild
       childSh2 idxSh2 v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        childSh2 idxSh2 s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phyPDChild (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
    + rewrite getChildrenAddDerivation with  currentPart descChild
       childSh2 idxSh2 v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        childSh2 idxSh2  s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phySh1Child  (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
    + rewrite getChildrenAddDerivation with  currentPart descChild
       childSh2 idxSh2 v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        childSh2 idxSh2 s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phySh2Child (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
     + rewrite getChildrenAddDerivation with  currentPart descChild
        childSh2 idxSh2 v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        childSh2 idxSh2 s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phyConfigPagesList(getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
    + apply isEntryVASameValue;trivial.
    + apply isEntryVASameValue;trivial.
    +      
(** New property to propagate **)
    unfold isEntryVA.
    cbn.
    assert(Htrue : beqPairs (childSh2, idxSh2) (childSh2, idxSh2) pageEq idxEq
 = true).
    { apply beqPairsTrue.
      split; trivial. }
    rewrite Htrue.
    cbn;trivial. }
Qed.

Lemma writeVirEntryList     
pdChild currentPart currentPD level ptRefChild descChild idxRefChild 
 ptPDChild idxPDChild   ptSh1Child shadow1 idxSh1
  ptSh2Child shadow2 idxSh2   ptConfigPagesList 
idxConfigPagesList  
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2
derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild zero nullv idxPR idxPD idxSH1 idxSH2
idxSH3 idxPPR        
 :derivedRefChild && derivedPDChild && derivedSh1Child && derivedSh2Child && derivedRefChildListSh1 = true -> 
vaddrEq vaddrDefault descChild = false ->
{{ fun s : state =>
   propagatedProperties false false false false pdChild currentPart currentPD level ptRefChild descChild idxRefChild true ptPDChild
     idxPDChild true ptSh1Child shadow1 idxSh1 true ptSh2Child shadow2 idxSh2 true ptConfigPagesList idxConfigPagesList true currentShadow1
     ptRefChildFromSh1 derivedRefChild ptPDChildSh1 false ptSh1ChildFromSh1 false childSh2 false childListSh1 derivedRefChildListSh1 list
     phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
   newPropagatedProperties s zero nullv idxPR idxPD idxSH1 idxSH2 idxSH3 idxPPR currentPart level phyPDChild phySh1Child phySh2Child
     phyConfigPagesList phyDescChild /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) /\
   isEntryVA ptPDChildSh1 idxPDChild descChild s /\ isEntryVA ptSh1ChildFromSh1 idxSh1 descChild s /\ isEntryVA childSh2 idxSh2 descChild s }} 
  MAL.writeVirEntry childListSh1 idxConfigPagesList descChild {{fun _ (s : state) =>
   propagatedProperties false false false false pdChild currentPart currentPD level ptRefChild descChild idxRefChild true ptPDChild
     idxPDChild true ptSh1Child shadow1 idxSh1 true ptSh2Child shadow2 idxSh2 true ptConfigPagesList idxConfigPagesList true currentShadow1
     ptRefChildFromSh1 derivedRefChild ptPDChildSh1 false ptSh1ChildFromSh1 false childSh2 false childListSh1 false list
     phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
   newPropagatedProperties s zero nullv idxPR idxPD idxSH1 idxSH2 idxSH3 idxPPR currentPart level phyPDChild phySh1Child phySh2Child
     phyConfigPagesList phyDescChild /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) /\
   (forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) /\
   isEntryVA ptPDChildSh1 idxPDChild descChild s /\ 
   isEntryVA ptSh1ChildFromSh1 idxSh1 descChild s /\ 
   isEntryVA childSh2 idxSh2 descChild s /\
   isEntryVA childListSh1 idxConfigPagesList descChild s }} .
 Proof.
  intros Hderived Hpost.
  eapply weaken.
  eapply WP.writeVirEntry.
    simpl; intros.
  unfold propagatedProperties in *.
  assert(Hget : forall idx : index,
          StateLib.getIndexOfAddr list levelMin = idx ->
          isVE childListSh1 idx s /\ 
          getTableAddrRoot childListSh1 idxShadow1 currentPart list s)
  by intuition.
  assert (Hve :isVE childListSh1 idxConfigPagesList  s).
  apply Hget.
    intuition.
    unfold isVE in Hve.
    case_eq( lookup childListSh1 idxConfigPagesList  (memory s) pageEq idxEq);
    intros; rewrite H0 in *; try now contradict Hve.
    case_eq v ; intros;rewrite H1 in *; try now contradict Hve.
    assert(Hpartitions : getPartitions pageRootPartition
            {|
            currentPartition := currentPartition s;
            memory := add childListSh1 idxConfigPagesList  (VE {| pd := false; va := descChild |})
                        (memory s) pageEq idxEq |} = 
                        getPartitions pageRootPartition
            s).
    apply getPartitionsAddDerivation with v0;trivial.
    unfold isPartitionFalse in *.
    intuition.
    assert(Hconfig :forall partition,  getConfigPagesAux partition
            {|
            currentPartition := currentPartition s;
            memory := add childListSh1 idxConfigPagesList (VE {| pd := false; va := descChild |}) 
                        (memory s) pageEq idxEq |} = getConfigPagesAux partition s).
      { intros.
        apply getConfigPagesAuxAddDerivation with v0;trivial. }
    assert(Hispart : isPartitionFalse childListSh1 idxConfigPagesList  s ) by intuition.
    split.    
    (** partitionsIsolation **)
(*     do 3 rewrite and_assoc. *)
    split.
    assert (Hiso : partitionsIsolation s) by intuition.
    apply partitionsIsolationUpdtateSh1Structure with v0; trivial.
    (** kernelDataIsolation **)
    split.
    assert (Hkdi : kernelDataIsolation s) by intuition.
    apply kernelDataIsolationUpdtateSh1Structure with v0; trivial.
    (** VerticalSharing **)
    split.
    assert (Hvs : verticalSharing s) by intuition.
    apply verticalSharingUpdtateSh1Structure with v0; trivial.
    (** consistency **)
    split.
    assert (Hcons : consistency s ) by intuition.
    intuition.
    subst idxConfigPagesList.
    assert(Hroot : forall idx : index,
      StateLib.getIndexOfAddr list levelMin = idx ->
      isPE ptConfigPagesList idx s /\
      getTableAddrRoot ptConfigPagesList idxPageDir currentPart list s) by trivial.
    destruct Hroot with (StateLib.getIndexOfAddr list levelMin)
    as (Hi1 & Hi2);trivial.
   assert(Hroot1 :forall idx : index,
       StateLib.getIndexOfAddr list levelMin = idx ->
       isVE childListSh1 idx s /\
       getTableAddrRoot childListSh1 idxShadow1 currentPart list s) by trivial.
    destruct Hroot1 with (StateLib.getIndexOfAddr list levelMin)
    as (Hii1 & Hii2);trivial.
    
 apply consistencyUpdtateSh1Structure with v0 true level
phyConfigPagesList ptConfigPagesList currentPD;subst;trivial.

unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
unfold consistency in *;intuition.
    (** Propagate properties **)
    { 
     intuition try trivial. 
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isPEAddDerivation with v0; trivial. 
      assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s)
      by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isPE ; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild levelMin = idx ->
                    isPE ptPDChild idx s /\ 
                    getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s ) by
       intuition.
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
                  StateLib.getIndexOfAddr shadow1 levelMin = idx ->
                  isPE ptSh1Child idx s /\ 
                  getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr shadow2 levelMin = idx ->
      isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child idxPageDir currentPart shadow2 s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + assert(Hi : forall idx : index,
      StateLib.getIndexOfAddr list levelMin = idx ->
      isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList idxPageDir currentPart list s ) by
       intuition. 
      apply isPEAddDerivation with v0; trivial.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isPE; trivial.
    + apply entryPresentFlagAddDerivation with v0; trivial.
    + apply entryUserFlagAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr descChild levelMin = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 idxShadow1 currentPart descChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxRefChild v0 isVE; trivial.
    + assert (Hi : exists va : vaddr,
         isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
         vaddrEq vaddrDefault va = derivedRefChild ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild
      list   currentPart
      currentShadow1 idxShadow1 level isVE s ;trivial.
      right;left; trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr pdChild levelMin = idx ->
       isVE ptPDChildSh1 idx s /\
       getTableAddrRoot ptPDChildSh1 idxShadow1 currentPart pdChild s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxPDChild v0 isVE; trivial.
    + exists descChild;split;trivial.
      apply isEntryVASameValue;trivial.
    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow1 levelMin = idx ->
       isVE ptSh1ChildFromSh1 idx s /\
       getTableAddrRoot ptSh1ChildFromSh1 idxShadow1 currentPart shadow1 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh1 v0 isVE; trivial.
(*     + assert (Hi : exists va : vaddr,
         isEntryVA ptSh1ChildFromSh1 idxSh1  va s /\ 
         beqVAddr defaultVAddr va = derivedSh1Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1
      pdChild   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial. *)
    + exists descChild;split;trivial.
      apply isEntryVASameValue;trivial.

    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr shadow2 levelMin = idx ->
       isVE childSh2 idx s /\
       getTableAddrRoot childSh2 idxShadow1 currentPart shadow2 s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxSh2 v0 isVE; trivial.
(*     + assert (Hi : exists va : vaddr,
         isEntryVA childSh2 idxSh2  va s /\ 
         beqVAddr defaultVAddr va = derivedSh2Child ) by intuition.
      destruct Hi as (va & Hva & Hderiv).
      exists va;split;trivial.
      apply isEntryVAAddDerivation; trivial.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2
      shadow1   currentPart
      currentShadow1 sh1idx level isVE s ;trivial.
      right;left; trivial.
      rewrite checkVAddrsEqualityWOOffsetPermut ;trivial. *)
    + exists descChild;split;trivial.
      apply isEntryVASameValue;trivial.

    + apply isVEAddDerivation with v0; trivial. 
      assert (Hi : forall idx : index,
       StateLib.getIndexOfAddr list levelMin = idx ->
       isVE childListSh1 idx s /\
       getTableAddrRoot childListSh1 idxShadow1 currentPart list s) by intuition.
      apply Hi; trivial.
    + apply getTableRootAddDerivation with idxConfigPagesList v0 isVE; trivial.
(** New property to propagate **)
    + exists descChild;split;trivial.
     unfold isEntryVA.
    cbn.
    assert(Htrue : beqPairs (childListSh1, idxConfigPagesList) (childListSh1, idxConfigPagesList)
     pageEq idxEq
 = true).
    { apply beqPairsTrue.
      split; trivial. }
    rewrite Htrue.
    cbn;trivial. 
    + apply isEntryPageAddDerivation with v0; trivial.    
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      left;trivial.
    + generalize (Hconfig partition);clear Hconfig; intros Hconfig.
      rewrite Hconfig in *; clear Hconfig.
      rewrite Hpartitions in *;clear Hpartitions.
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
      right;trivial.
    + apply isEntryPageAddDerivation with v0; trivial.
    + rewrite Hpartitions in *.
      unfold getConfigPages in *.
      simpl in *.
      rewrite Hconfig in *.   
      assert(Hi : forall partition : page,
      In partition (getPartitions pageRootPartition s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by intuition.
      apply Hi with partition;trivial.
   +  assert (HisPart : isPartitionFalse ptSh1ChildFromSh1 idxSh1 s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptSh1ChildFromSh1 idxSh1
                (add childListSh1 idxConfigPagesList (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag ptSh1ChildFromSh1 
                idxSh1 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow1 list currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
   + assert (HisPart : isPartitionFalse childSh2 idxSh2 s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childSh2 idxSh2
                (add childListSh1 idxConfigPagesList (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag childSh2 idxSh2
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with shadow2 list currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial. 
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    + apply isPartitionFalseAddDerivation.
    (* assert (HisPart : isPartitionFalse childListSh1 idxConfigPagesList s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag childListSh1 idxConfigPagesList
                (add childSh2 idxSh2 (VE {| pd := false; va := descChild |})        
                (memory s) beqPage beqIndex) = StateLib.readPDflag childListSh1
                 idxConfigPagesList
                (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with list shadow2 currentPart 
            currentShadow1 sh1idx level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
     rewrite Hreadflag;trivial.*)
(*     + apply entryUserFlagAddDerivation with v0;trivial. *)
    +  assert (HisPart : isPartitionFalse ptRefChildFromSh1 idxRefChild s) by trivial.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptRefChildFromSh1 idxRefChild
                (add childListSh1 idxConfigPagesList (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag ptRefChildFromSh1
                 idxRefChild  (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with descChild list currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial.
   +  assert (HisPart : isPartitionFalse ptPDChildSh1 idxPDChild s) by intuition.
       unfold isPartitionFalse in *.
       simpl in *.
       assert(Hreadflag : StateLib.readPDflag ptPDChildSh1 idxPDChild
                (add childListSh1 idxConfigPagesList (VE {| pd := false; va := descChild |})        
                (memory s) pageEq idxEq) = StateLib.readPDflag ptPDChildSh1 idxPDChild
                 (memory s)).
      apply  readPDflagAddDerivation.
      apply toApplyPageTablesOrIndicesAreDifferent with pdChild list currentPart 
            currentShadow1 idxShadow1 level isVE  s;trivial.
     right;left;trivial.
     subst.
     rewrite Hreadflag;trivial. }
   { unfold newPropagatedProperties in *. 
     intuition try trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phyPDChild (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phySh1Child (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phySh2Child (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phyConfigPagesList (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + set (s' := {| currentPartition := _ |})  in *.
      assert(Haccess : getAccessibleMappedPages partition s' =
      getAccessibleMappedPages partition s).
      apply getAccessibleMappedPagesAddDerivation with v0;trivial.
      rewrite Haccess in *.   
      assert(Htrue : forall partition : page,
        In partition (getAncestors currentPart s) ->
        In phyDescChild (getAccessibleMappedPages partition s) -> False) by trivial.
      apply Htrue  with partition.
      assert(Hanc : getAncestors currentPart s' = getAncestors currentPart s) by (
        apply getAncestorsAddDerivation with v0;trivial).
      rewrite <- Hanc;trivial.
      trivial.
    + apply isWellFormedSndShadowUpdateMappedPageData;trivial. 
      unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse.
      apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 list idxConfigPagesList s ;
      trivial.
      right;left;trivial.
      subst.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
    + apply isWellFormedFstShadowUpdateMappedPageData;trivial. 
      unfold not;intros Hfalse;symmetry in Hfalse;contradict Hfalse.
      apply mappedPageIsNotPTable with currentPart currentShadow1 isVE idxShadow1 list idxConfigPagesList s ;
      trivial.
      right;left;trivial.
      subst.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      unfold consistency in *.
      intuition.
    + assert(Hii : forall idx : index,
      StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\
      StateLib.readPresent phyPDChild idx (memory s) = Some false)  by intuition.
      destruct Hii with idx as (Hi & _).
      rewrite <- Hi.
      apply readPhyEntryAddDerivation with v0;trivial.
    + assert(Hii : forall idx : index,
      StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\
      StateLib.readPresent phyPDChild idx (memory s) = Some false)  by intuition.
      destruct Hii with idx as (_ & Hi).
      rewrite <- Hi.
      apply readPresentAddDerivation with v0;trivial.
    + assert(initConfigPagesListPostCondition phyConfigPagesList s) as (Hi1 & Hi2 & Hi3 & Hi4) by intuition.
      unfold initConfigPagesListPostCondition.
      split. 
      rewrite <- Hi1.
      apply readPhysicalAddDerivation with v0; trivial.
      split.
      rewrite <- Hi2.
      apply readVirtualAddDerivation with v0; trivial.
      split.
      intros idx Ha1 Ha2 Ha3.
      generalize (Hi3 idx Ha1 Ha2 Ha3);clear Hi3;intros Hi3.
      destruct Hi3 as (idxValue & Hi3).
      exists idxValue.
      rewrite <-Hi3.
      apply readIndexAddDerivation with v0; trivial.
      intros. 
      rewrite <- Hi4 with idx;trivial.
      apply readVirtualAddDerivation with v0; trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + apply isVAAddDerivation with v0;trivial.
    + apply nextEntryIsPPAddDerivation with v0;trivial.
    + rewrite getChildrenAddDerivation with  currentPart descChild
        childListSh1 idxConfigPagesList v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        childListSh1 idxConfigPagesList s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phyDescChild (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
   + rewrite getChildrenAddDerivation with  currentPart descChild
       childListSh1 idxConfigPagesList v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        childListSh1 idxConfigPagesList s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phyPDChild (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
    + rewrite getChildrenAddDerivation with  currentPart descChild
       childListSh1 idxConfigPagesList v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        childListSh1 idxConfigPagesList  s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phySh1Child  (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
    + rewrite getChildrenAddDerivation with  currentPart descChild
       childListSh1 idxConfigPagesList v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        childListSh1 idxConfigPagesList s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phySh2Child (getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
     + rewrite getChildrenAddDerivation with  currentPart descChild
        childListSh1 idxConfigPagesList v0 s in *;trivial.       
       rewrite getMappedPagesAddDerivation with child descChild
        childListSh1 idxConfigPagesList s  v0 false in *;trivial.
       assert(Hgoal : forall child : page,
       In child (getChildren currentPart s) -> In phyConfigPagesList(getMappedPages child s) -> False) by trivial.
       apply Hgoal with child ;trivial.
    + apply isEntryVASameValue;trivial.
    + apply isEntryVASameValue;trivial.
    + apply isEntryVASameValue;trivial.
    +
(** New property to propagate **)
    unfold isEntryVA.
    cbn.
    assert(Htrue : beqPairs (childListSh1, idxConfigPagesList) (childListSh1, idxConfigPagesList)
     pageEq idxEq
 = true).
    { apply beqPairsTrue.
      split; trivial. }
    rewrite Htrue.
    cbn;trivial. 
    }
Qed.
Lemma physicalPageNotDerivedRemoveVaddr    
entry s descChild vaChild currentPart level
     idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
     phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
     ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2 vainparent defautvaddr
     currentShadow ptVaInCurPart:
 propagatedPropertiesRemoveVaddr s descChild vaChild currentPart level
     idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
     phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
     ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2 vainparent defautvaddr
     currentShadow ptVaInCurPart (StateLib.getIndexOfAddr vainparent levelMin) false
     false  -> 
isPartitionFalse ptVaInCurPart
       (StateLib.getIndexOfAddr vainparent levelMin) s -> 
lookup ptVaInCurPart (StateLib.getIndexOfAddr vainparent levelMin)
            (memory s) pageEq idxEq = Some (VE entry)  
->  getPDFlag currentShadow vainparent s = false -> 
   (exists pagetoremove : page,
      getAccessibleMappedPage currentPD s vainparent = SomePage pagetoremove /\
      (forall child : page,
       In child (getChildren currentPart s) ->
       ~ In pagetoremove (getMappedPages child s))) -> 
(* ~ isDerived (currentPartition s) vainparent s ->  *)
physicalPageNotDerived s ->
physicalPageNotDerived
  {|
  currentPartition := currentPartition s;
  memory := add ptVaInCurPart (StateLib.getIndexOfAddr vainparent levelMin)
              (VE {| pd := false; va := defautvaddr |}) (memory s) pageEq
              idxEq |}.

Proof.

set(s':= {|
  currentPartition := currentPartition s;
  memory := add ptVaInCurPart (StateLib.getIndexOfAddr vainparent levelMin)
              (VE {| pd := false; va := defautvaddr |}) (memory s) pageEq
              idxEq |}
) in *.
intros Hprops Hnotpart Hlookup (* Hnotderived *) Hnew1 Hnew2 Hcons .
unfold propagatedPropertiesRemoveVaddr in *. intuition.
  subst.
  
unfold consistency in *;intuition. 
unfold physicalPageNotDerived in *.
intros parent va  pdParent pageParent.
intros Hparts HgetpdParent Hderiv Hmapparent child pdChild vaInChild pageChild
Hgetchildren Hpdchild Hmapchild.
assert(Hpartitions : getPartitions pageRootPartition s = getPartitions pageRootPartition s').
symmetry.
apply getPartitionsAddDerivation with entry ;trivial.
rewrite Hpartitions in *.
assert(Hchildren : 
getChildren parent s' 
   = getChildren parent s).
apply getChildrenAddDerivation with entry;trivial.
rewrite Hchildren in *;clear Hchildren.
assert(Hgetpd: StateLib.getPd parent (memory s') =
StateLib.getPd parent (memory s)). 
apply getPdAddDerivation with entry;trivial.
rewrite Hgetpd in *.
assert(Hgetpdchild: StateLib.getPd child (memory s') =
StateLib.getPd child (memory s)). 
apply getPdAddDerivation with entry;trivial.
rewrite Hgetpdchild in *. clear Hgetpdchild. clear Hgetpd.
assert(Hmapped : forall pd v,  getMappedPage pd
  s' v =
getMappedPage pd s v).
intros.
apply getMappedPageAddDerivation with entry; trivial.
rewrite Hmapped in *. clear Hmapped.
assert (Hnewmapp : getMappedPage pdChildphy s vaChild = SomeDefault).
{ 
   apply getMappedPageNotPresent with ptVaChildpd phyDescChild;trivial.
   intros;split; subst;trivial. }
assert(Hor1:  
((currentPartition s) = parent \/ (currentPartition s) <> parent)) by apply pageDecOrNot.
destruct Hor1 as [Hor1| Hor1].
+ subst.
  assert(Hor2 : StateLib.checkVAddrsEqualityWOOffset nbLevel vainparent va level = true \/
                StateLib.checkVAddrsEqualityWOOffset nbLevel vainparent va level = false ).
  { destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel vainparent va level);intuition. }
  destruct Hor2 as [Hor2 | Hor2].
  - assert(Hnewprop: exists pagetoremove, 
  getAccessibleMappedPage currentPD s vainparent = SomePage  pagetoremove /\ 
(forall child, In child (getChildren (currentPartition s) s) -> 
~In  pagetoremove (getMappedPages child s)))by trivial.
  destruct Hnewprop as (pg & Hpg & Hg1 ).
  assert(pdParent = currentPD).
  apply getPdNextEntryIsPPEq with (currentPartition s) s;trivial.
  apply nextEntryIsPPgetPd;trivial.
  apply nextEntryIsPPgetPd;trivial.
  subst pdParent.
  assert(Hpgmap: getMappedPage currentPD s vainparent = SomePage pg).
  apply accessiblePAgeIsMapped;trivial.
  assert(Hmapeq:  getMappedPage currentPD s vainparent =
   getMappedPage currentPD s va).
   apply getMappedPageEq with level;trivial.
   symmetry;trivial.
   rewrite Hmapparent in Hmapeq.
   rewrite Hpgmap in Hmapeq.
   inversion Hmapeq.
   subst.
  unfold not;intros;subst.
  assert(Hgetchildreneq:In phyDescChild (getChildren (currentPartition s) s));
  trivial.
  generalize(Hg1 child Hgetchildren);clear Hg1;intros Hg1.
  contradict Hg1.
  unfold getMappedPages.
  rewrite Hpdchild.
  unfold getMappedPagesAux.
  apply filterOptionInIff.
  unfold getMappedPagesOption.
  apply in_map_iff.
  assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaInChild va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).
exists va1;split;trivial.
rewrite <- Hmapchild.
symmetry.
apply getMappedPageEq with level.
symmetry;trivial.
rewrite <- Hva11.
f_equal.
apply getNbLevelEq;trivial.
 - apply Hcons with (currentPartition s) va pdParent child pdChild vaInChild;trivial.
   
unfold isDerived in *.
unfold s' in *;simpl in *.
clear s'.
assert(Hgetsh1: StateLib.getFstShadow (currentPartition s) (add ptVaInCurPart (StateLib.getIndexOfAddr vainparent levelMin)
                (VE {| pd := false; va := defautvaddr |}) (memory s) pageEq
                idxEq)=
StateLib.getFstShadow (currentPartition s) (memory s)). 
apply getFstShadowAddDerivation with entry;trivial.
rewrite Hgetsh1 in *. clear Hgetsh1.
(* set(s':= {|
  currentPartition := _ |}
) in *. *)
 case_eq (StateLib.getFstShadow (currentPartition s) (memory s) );[intros sh1parent Hsh1parent | intros Hsh1parent];
 rewrite Hsh1parent in *;trivial.
 unfold not; intros Hgetvirt;
 contradict Hderiv.

 unfold getVirtualAddressSh1 in *.
 assert(Hlevel:  StateLib.getNbLevel = Some level ) by (symmetry;trivial).
 rewrite Hlevel in *.

 rewrite getIndirectionAddDerivation with sh1parent ptVaInCurPart
             (StateLib.getIndexOfAddr vainparent levelMin)  defautvaddr s 
 entry va level (nbLevel -1) false;
 trivial.
case_eq( getIndirection sh1parent va level (nbLevel - 1) s); 
[intros ind Hind | intros Hind];
 rewrite Hind in *;trivial.
 case_eq(Nat.eqb pageDefault ind);intros Heqind;rewrite Heqind in *;trivial.
 simpl.
 unfold StateLib.readVirEntry in *.
 simpl in *.
unfold consistency in *. 
intuition.
 assert(Hnotsameind : ind <> ptVaInCurPart \/ (StateLib.getIndexOfAddr va levelMin) <>
(StateLib.getIndexOfAddr vainparent levelMin) ).
{ apply pageTablesOrIndicesAreDifferent with sh1parent sh1parent level nbLevel s;trivial.
apply sh1PartNotNull with (currentPartition s) s;trivial.
apply nextEntryIsPPgetFstShadow;subst;trivial.
apply sh1PartNotNull with (currentPartition s) s;trivial.
apply nextEntryIsPPgetFstShadow;subst;trivial.
  apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) idxShadow1;trivial.
  intuition.
  right;left;trivial.
  apply nextEntryIsPPgetFstShadow;subst;trivial.
      apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) idxShadow1;trivial.
  intuition.
  right;left;trivial.
  apply nextEntryIsPPgetFstShadow;subst;trivial.
  rewrite <- Hor2.
  rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
  left;split;trivial.
  apply getNbLevelEq;trivial.
  symmetry;trivial.
  apply beq_nat_false in Heqind.
  unfold not; intros Htmp;subst;now contradict Heqind.
  assert(Hnotnull : (Nat.eqb pageDefault ptVaInCurPart) = false) by trivial.
  apply beq_nat_false in Hnotnull.
  unfold not; intros Htmp;subst;now contradict Hnotnull.
  apply getIndirectionStopLevelGT  with (nbLevel - 1) ;trivial.
  apply getNbLevelLt;intuition.
  rewrite nbLevelEq.
    symmetry. rewrite <- getNbLevelEq with level;trivial.
    symmetry;trivial.
assert(Haux :getIndirection sh1parent vainparent level (nbLevel -1) s = Some ptVaInCurPart). 
  apply getIndirectionGetTableRoot with (currentPartition s);trivial.

  intros.
  split;subst;trivial.
  apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
    apply getNbLevelLt;intuition.
  rewrite nbLevelEq.
    symmetry. rewrite <- getNbLevelEq with level;trivial.
    symmetry;trivial. }
  
(*   assert(Hreadpd :  StateLib.readPDflag ind (StateLib.getIndexOfAddr va fstLevel) (memory  {|
              currentPartition := currentPartition s;
              memory := add ptVaInCurPart
                          (StateLib.getIndexOfAddr vainparent fstLevel)
                          (VE {| pd := false; va := defautvaddr |})
                          (memory s) beqPage beqIndex |})
  = StateLib.readPDflag ind (StateLib.getIndexOfAddr va fstLevel) (memory s)).
  apply readPDflagAddDerivation;trivial.
    
    rewrite Hreadpd;trivial.
  assert(Hreadvir :  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va fstLevel) (memory s')
  = StateLib.readVirEntry ind (StateLib.getIndexOfAddr va fstLevel) (memory s)).
  apply readVirEntryAddDerivation;trivial.
  rewrite Hreadvir. split; trivial.  }
 rewrite HgetPdflag.
 rewrite Hgetvirt.
 apply Hwell with partition pd;trivial. *)
 assert(Htrue: beqPairs (ptVaInCurPart, StateLib.getIndexOfAddr vainparent levelMin)
        (ind, StateLib.getIndexOfAddr va levelMin) pageEq idxEq = false).
 apply beqPairsFalse;intuition.
 rewrite Htrue in *.
 
 
 assert (lookup ind (StateLib.getIndexOfAddr va levelMin)
 (removeDup ptVaInCurPart (StateLib.getIndexOfAddr vainparent levelMin)(memory s) pageEq idxEq)
           pageEq idxEq = lookup  ind (StateLib.getIndexOfAddr va levelMin) (memory s) pageEq idxEq) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
     
     + apply Hcons with parent va pdParent child pdChild vaInChild;trivial.
     unfold isDerived in *.
     assert(Hgetsh1: StateLib.getFstShadow parent (add ptVaInCurPart (StateLib.getIndexOfAddr vainparent levelMin)
                (VE {| pd := false; va := defautvaddr |}) (memory s) pageEq
                idxEq)=
StateLib.getFstShadow parent (memory s)). 
apply getFstShadowAddDerivation with entry;trivial.
unfold s' in *. simpl in *.
rewrite Hgetsh1 in *. clear Hgetsh1.
(* set(s':= {|
  currentPartition := _ |}
) in *. *)
 case_eq (StateLib.getFstShadow parent (memory s) );[intros sh1parent Hsh1parent | intros Hsh1parent];
 rewrite Hsh1parent in *;trivial.
 unfold not; intros Hgetvirt;
 contradict Hderiv.

 unfold getVirtualAddressSh1 in *.
 assert(Hlevel:  StateLib.getNbLevel = Some level ) by (symmetry;trivial).
 rewrite Hlevel in *.

(*  rewrite getIndirectionAddDerivation with sh1parent ptVaInCurPart
             (StateLib.getIndexOfAddr vainparent fstLevel)  defautvaddr s 
 entry va level (nbLevel -1) false;
 trivial.
case_eq( getIndirection sh1parent va level (nbLevel - 1) s); 
[intros ind Hind | intros Hind];
 rewrite Hind in *;trivial.
 case_eq(Nat.eqb defaultPage ind);intros Heqind;rewrite Heqind in *;trivial.
 simpl.
 unfold StateLib.readVirEntry in *.
 simpl in *.
unfold consistency in *. 
intuition.
 *)


  assert(Hind :getIndirection sh1parent va level (nbLevel - 1)  {|
      currentPartition := currentPartition s;
      memory := add ptVaInCurPart
                  (StateLib.getIndexOfAddr vainparent levelMin)
                  (VE {| pd := false; va := defautvaddr |}) (memory s)
                  pageEq idxEq |}
  =getIndirection sh1parent va level (nbLevel - 1) s).
  apply getIndirectionAddDerivation with entry;trivial.
  rewrite Hind. clear Hind.
  case_eq(getIndirection sh1parent va level (nbLevel - 1) s);
  [intros ind Hind | intros Hind]; rewrite Hind in *;
  trivial. 
  
  case_eq(Nat.eqb ind pageDefault);intros Heqind.
  assert(Hbof :  (Nat.eqb pageDefault ind) = true).
  { apply NPeano.Nat.eqb_eq.
  apply beq_nat_true in Heqind.
  subst;trivial.
  destruct pageDefault;destruct ind;simpl in *;subst;trivial. }
  rewrite Hbof in *;trivial.
  assert(Hconfdif: configTablesAreDifferent s ) by (unfold consistency in *;intuition).
assert(Hnotsameind : ind <> ptVaInCurPart).
  {
  assert(Hdist : Lib.disjoint (getConfigPages (currentPartition s) s)
   (getConfigPages parent s)).
  {  intuition.
  rewrite <- Hpartitions in *.
    apply Hconfdif;trivial. }
  assert(Hin1 : In ind (getConfigPages parent s)).
  { unfold getConfigPages.
    simpl.
    right.
    apply inGetIndirectionsAuxInConfigPagesSh1 with sh1parent;trivial.
    rewrite Hpartitions in *;trivial.
    apply getIndirectionInGetIndirections with va level (nbLevel - 1);trivial. 
    apply nbLevelNotZero.
    
    apply beq_nat_false in Heqind.
    trivial.
    unfold not;intros;subst; now contradict Heqind.
    apply getNbLevelLe;trivial.
    symmetry;trivial.
    apply sh1PartNotNull with parent s;trivial.
     rewrite Hpartitions in *;trivial.
    apply nextEntryIsPPgetFstShadow;trivial. }
  assert(Hin2 : In ptVaInCurPart (getConfigPages (currentPartition s) s)).
  { apply isConfigTableSh1WithVE with vainparent;trivial.
    intros;subst;split;intuition. }
    unfold  Lib.disjoint in *.
    unfold not in Hdist.
    unfold not;intros Hfalse.
    apply Hdist with  ptVaInCurPart;trivial.
    subst;trivial. }
    
     assert(Hbof :  (Nat.eqb pageDefault ind) = false).
  { apply PeanoNat.Nat.eqb_neq.
  apply beq_nat_false in Heqind.
  subst;trivial.
  destruct pageDefault;destruct ind;simpl in *;subst;trivial.
  unfold not;intros;subst. now contradict Heqind. }
  rewrite Hbof in *.
  simpl.
  
  assert(Hreadpd :  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s')
  = StateLib.readVirEntry ind (StateLib.getIndexOfAddr va levelMin) (memory s)).
  apply readVirEntryAddDerivation;trivial.
  left. 
  
    trivial.
    unfold s' in *.
    simpl in *.
    rewrite Hreadpd .
    trivial.
    

Qed. 


Lemma consistencyRemoveVaddr s descChild vaChild currentPart level
     idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
     phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
     ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2 vainparent defautvaddr
     currentShadow ptVaInCurPart idxvainparent: 
(StateLib.getIndexOfAddr vainparent levelMin) = idxvainparent -> 
isPartitionFalse ptVaInCurPart
              (StateLib.getIndexOfAddr vainparent levelMin) s -> 
   propagatedPropertiesRemoveVaddr s descChild vaChild currentPart level
     idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
     phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
     ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2 vainparent defautvaddr
     currentShadow ptVaInCurPart (StateLib.getIndexOfAddr vainparent levelMin) false
     false ->
     getPDFlag currentShadow vainparent s = false ->
   (exists pagetoremove : page,
      getAccessibleMappedPage currentPD s vainparent = SomePage pagetoremove /\
      (forall child : page,
       In child (getChildren currentPart s) ->
       ~ In pagetoremove (getMappedPages child s)))
       -> 
consistency
  {|
  currentPartition := currentPartition s;
  memory := add ptVaInCurPart (StateLib.getIndexOfAddr vainparent levelMin)
              (VE {| pd := false; va := defautvaddr |}) (memory s) pageEq
              idxEq |}. 
Proof.
intros;subst.
unfold propagatedPropertiesRemoveVaddr in *.
intuition.
subst.
assert(Hlookup :exists entry, 
 lookup ptVaInCurPart (StateLib.getIndexOfAddr vainparent levelMin) 
 (memory s) pageEq idxEq = Some (VE entry)).
{ assert(Hva : isVE ptVaInCurPart (StateLib.getIndexOfAddr vainparent levelMin) s) by intuition.

  unfold isVE in *.

 destruct(lookup ptVaInCurPart (StateLib.getIndexOfAddr vainparent levelMin)
          (memory s) pageEq idxEq);intros; try now contradict Hva.
 destruct v; try now contradict Hva.
 do 2 f_equal.
 exists v;trivial. }
 destruct Hlookup as (entry & Hlookup).
unfold consistency in *;intuition.
+ apply partitionDescriptorEntryAddDerivation with entry; intuition.
+ apply dataStructurePdSh1Sh2asRootAddDerivation with entry; intuition.
+ apply dataStructurePdSh1Sh2asRootAddDerivation with entry; intuition.
+ apply dataStructurePdSh1Sh2asRootAddDerivation with entry; intuition.
+ apply currentPartitionInPartitionsListAddDerivation with entry; intuition.
+ apply noDupMappedPagesListAddDerivation with entry; intuition.
+ apply noDupConfigPagesListAddDerivation with entry; intuition.
+ apply parentInPartitionListAddDerivation with entry; intuition.
+ apply accessibleVAIsNotPartitionDescriptorAddDerivation with entry; intuition.
+ apply accessibleChildPageIsAccessibleIntoParentAddDerivation with entry;intuition.
+ apply noCycleInPartitionTreeUpdtateSh1Structure with entry;intuition.
+ apply configTablesAreDifferentUpdtateSh1Structure with entry ;intuition.
+ apply isChildUpdtateSh1Structure with entry ;intuition.
+ apply isPresentNotDefaultIffAddDerivation ;intuition.
+ apply physicalPageNotDerivedRemoveVaddr with entry descChild
vaChild (currentPartition s) level (StateLib.getIndexOfAddr descChild levelMin) ptDescChild currentPD
ptDescChildFromPD (StateLib.getIndexOfAddr descChild levelMin) phyDescChild pdChildphy 
(StateLib.getIndexOfAddr vaChild levelMin)
ptVaChildpd shadow1Child ptVaChildFromSh1 vainve sh2Childphy
ptVaChildsh2 currentShadow;trivial. unfold propagatedPropertiesRemoveVaddr in *. 
unfold consistency in *.
intuition.  
+ apply multiplexerWithoutParentUpdtateSh1Structure with entry;intuition.
+ apply isParentUpdtateSh1Structure with entry;intuition.
+ apply noDupPartitionTreeUpdtateSh1Structure with entry;intuition.
+ apply wellFormedFstShadowUpdtateSh1Structure with entry ;intuition.
+ apply wellFormedSndShadowUpdtateSh1Structure with entry;intuition.
+ apply wellFormedShadowsUpdtateSh1Structure with entry;intuition.
+ apply wellFormedShadowsUpdtateSh1Structure with entry;intuition.
+ assert (Hprop: exists pagetoremove : page,
       getAccessibleMappedPage currentPD s vainparent = SomePage pagetoremove /\
       (forall child : page,
        In child (getChildren (currentPartition s) s) ->
        In pagetoremove (getMappedPages child s) -> False)) by trivial.
  destruct Hprop as (x & Hx & Hxx).
  rewrite nextEntryIsPPgetFstShadow in *.
  assert(Hsh1cur: StateLib.getFstShadow (currentPartition s) (memory s) = Some currentShadow);trivial.
  unfold getAccessibleMappedPage in Hx.
  assert(Hlevel :  Some level = StateLib.getNbLevel) by trivial.
  rewrite <- Hlevel in *.
  case_eq(StateLib.getIndirection currentPD vainparent level (nbLevel - 1) s);
  [intros ind Hind| intros Hind];rewrite Hind in *; try now contradict Hx.
  case_eq(Nat.eqb pageDefault ind);intros Hdef;rewrite Hdef in *;try now contradict Hx.
  case_eq( StateLib.readPresent ind (StateLib.getIndexOfAddr vainparent levelMin) (memory s));[intros pres Hpres|intros Hpres]; rewrite Hpres in *;try now contradict Hx.
  case_eq pres;intros;subst;try now contradict Hx.
  case_eq(  StateLib.readAccessible ind
         (StateLib.getIndexOfAddr vainparent levelMin) (memory s));[intros access Haccess|intros Haccess]; rewrite Haccess in *;try now contradict Hx.
  case_eq access;intros;subst;try now contradict Hx. 
  case_eq(  StateLib.readPhyEntry ind
         (StateLib.getIndexOfAddr vainparent levelMin) (memory s));[intros read Hread|intros Hread]; rewrite Hread in *;try now contradict Hx.
  inversion Hx;subst.
 
(*   
 assert( Hpde: partitionDescriptorEntry s) by trivial.
 unfold partitionDescriptorEntry in *.
 assert(Hsh1cur:     (exists entry : page,
          nextEntryIsPP (currentPartition s) sh1idx entry s /\ entry <> defaultPage)).
   apply Hpde;trivial.
   right;left;trivial.
  destruct Hsh1cur as currentShadow1 *)
unfold StateLib.readPhyEntry in Hread.
case_eq(lookup ind (StateLib.getIndexOfAddr vainparent levelMin) (memory s)
            pageEq idxEq);[intros v Hlookupread|intros Hlookupread]; rewrite Hlookupread in *;try now contradict Hread.
destruct v;try now contradict Hread.
inversion Hread.
subst.
apply  wellFormedFstShadowIfNoneUpdtateSh1StructureX  with entry true level
(pa p) ind currentPD;trivial.
unfold isPE.
rewrite Hlookupread;trivial.
unfold getTableAddrRoot.
split.
left;trivial.
intros.
exists level;split;trivial.
exists (level+1).
split;trivial.
assert(tableroot=currentPD).
apply getPdNextEntryIsPPEq with (currentPartition s) s;trivial.
apply nextEntryIsPPgetPd;trivial.
subst tableroot.

apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
lia.
 rewrite nbLevelEq.
    symmetry. rewrite <- getNbLevelEq with level;trivial.
 unfold isEntryPage.
 rewrite Hlookupread;trivial.
 unfold entryPresentFlag.
 unfold StateLib.readPresent in Hpres.
 rewrite Hlookupread in Hpres.
 rewrite Hlookupread.
 inversion Hpres.
 subst;trivial.
+ assert (Hprop: exists pagetoremove : page,
       getAccessibleMappedPage currentPD s vainparent = SomePage pagetoremove /\
       (forall child : page,
        In child (getChildren (currentPartition s) s) ->
        In pagetoremove (getMappedPages child s) -> False)) by trivial.
  destruct Hprop as (x & Hx & Hxx).
  rewrite nextEntryIsPPgetFstShadow in *.
  assert(Hsh1cur: StateLib.getFstShadow (currentPartition s) (memory s) = Some currentShadow);trivial.
  unfold getAccessibleMappedPage in Hx.
  assert(Hlevel :  Some level = StateLib.getNbLevel) by trivial.
  rewrite <- Hlevel in *.
  case_eq(StateLib.getIndirection currentPD vainparent level (nbLevel - 1) s);
  [intros ind Hind| intros Hind];rewrite Hind in *; try now contradict Hx.
  case_eq(Nat.eqb pageDefault ind);intros Hdef;rewrite Hdef in *;try now contradict Hx.
  case_eq( StateLib.readPresent ind (StateLib.getIndexOfAddr vainparent levelMin) (memory s));[intros pres Hpres|intros Hpres]; rewrite Hpres in *;try now contradict Hx.
  case_eq pres;intros;subst;try now contradict Hx.
  case_eq(  StateLib.readAccessible ind
         (StateLib.getIndexOfAddr vainparent levelMin) (memory s));[intros access Haccess|intros Haccess]; rewrite Haccess in *;try now contradict Hx.
  case_eq access;intros;subst;try now contradict Hx. 
  case_eq(  StateLib.readPhyEntry ind
         (StateLib.getIndexOfAddr vainparent levelMin) (memory s));[intros read Hread|intros Hread]; rewrite Hread in *;try now contradict Hx.
  inversion Hx;subst.
 
(*   
 assert( Hpde: partitionDescriptorEntry s) by trivial.
 unfold partitionDescriptorEntry in *.
 assert(Hsh1cur:     (exists entry : page,
          nextEntryIsPP (currentPartition s) sh1idx entry s /\ entry <> defaultPage)).
   apply Hpde;trivial.
   right;left;trivial.
  destruct Hsh1cur as currentShadow1 *)
unfold StateLib.readPhyEntry in Hread.
case_eq(lookup ind (StateLib.getIndexOfAddr vainparent levelMin) (memory s)
            pageEq idxEq);[intros v Hlookupread|intros Hlookupread]; rewrite Hlookupread in *;try now contradict Hread.
destruct v;try now contradict Hread.
inversion Hread.
subst.
apply  wellFormedFstShadowIfDefaultValuesUpdtateSh1StructureX  with entry true level
(pa p) ind currentPD;trivial.
unfold isPE.
rewrite Hlookupread;trivial.
unfold getTableAddrRoot.
split.
left;trivial.
intros.
exists level;split;trivial.
exists (level+1).
split;trivial.
assert(tableroot=currentPD).
apply getPdNextEntryIsPPEq with (currentPartition s) s;trivial.
apply nextEntryIsPPgetPd;trivial.
subst tableroot.

apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
lia.
 rewrite nbLevelEq.
    symmetry. rewrite <- getNbLevelEq with level;trivial.
 unfold isEntryPage.
 rewrite Hlookupread;trivial.
 unfold entryPresentFlag.
 unfold StateLib.readPresent in Hpres.
 rewrite Hlookupread in Hpres.
 rewrite Hlookupread.
 inversion Hpres.
 subst;trivial.
Qed.


Lemma writeVirEntryRemoveVaddr  descChild vaChild currentPart level
     idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
     phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
     ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2 vainparent defautvaddr
     currentShadow ptVaInCurPart idxvainparent: 

{{ fun s : state =>
   propagatedPropertiesRemoveVaddr s descChild vaChild currentPart level
     idxDescChild ptDescChild currentPD ptDescChildFromPD idxDescChild1
     phyDescChild pdChildphy idxvaChild ptVaChildpd shadow1Child
     ptVaChildFromSh1 vainve sh2Childphy ptVaChildsh2 vainparent defautvaddr
     currentShadow ptVaInCurPart idxvainparent false
     false /\  getPDFlag currentShadow vainparent s = false /\
   (exists pagetoremove : page,
      getAccessibleMappedPage currentPD s vainparent = SomePage pagetoremove /\
      (forall child : page,
       In child (getChildren currentPart s) ->
       ~ In pagetoremove (getMappedPages child s)))}} 
  MAL.writeVirEntry ptVaInCurPart idxvainparent defautvaddr {{ fun (_ : unit) (s : state) =>
                       partitionsIsolation s /\
                       kernelDataIsolation s /\
                       verticalSharing s /\ consistency s }}.
Proof.
intros.
subst.
eapply weaken.
eapply WP.writeVirEntry.
simpl;intros.
unfold propagatedPropertiesRemoveVaddr in *.
assert (Hve :isVE ptVaInCurPart idxvainparent s)
  by (intuition;subst;trivial).
unfold isVE in Hve.
case_eq( lookup ptVaInCurPart idxvainparent (memory s) pageEq idxEq);
intros; rewrite H0 in *; try now contradict Hve.
case_eq v ; intros;rewrite H1 in *; try now contradict Hve.
subst.
assert(Hparts : In currentPart (getPartitions pageRootPartition s)).
{ intuition. subst.
  unfold consistency in *.
  unfold currentPartitionInPartitionsList in *.
  intuition. }
assert(Hcursh1 :(exists entry : page,
        nextEntryIsPP currentPart idxShadow1 entry s /\ entry <> pageDefault)).
{ assert(Hpde: partitionDescriptorEntry s) by (unfold consistency in *;intuition).
  apply Hpde;intuition.   }
destruct Hcursh1 as (currentShadow1 & Hcursh1 & Hsh1notnul). 
assert (Hreadflag : isPartitionFalse ptVaInCurPart (StateLib.getIndexOfAddr vainparent levelMin) s ).
{ unfold isPartitionFalse.
unfold consistency in *. 
assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
unfold accessibleVAIsNotPartitionDescriptor in *.

assert (Hflag : getPDFlag currentShadow vainparent s = false).
intuition;subst.
 trivial.
apply getPDFlagReadPDflag  with currentShadow vainparent currentPart; trivial.
intuition.  
apply PeanoNat.Nat.eqb_neq.
assert(Hfalsepge : (Nat.eqb pageDefault ptVaInCurPart) = false) by trivial.
apply beq_nat_false in Hfalsepge.
unfold not;intros Hfalse'.
rewrite Hfalse' in Hfalsepge.    
now contradict Hfalsepge.
intuition.
intuition.
intuition.
subst;trivial. }
assert(StateLib.getIndexOfAddr vainparent levelMin = idxvainparent) by
intuition.
subst.
intuition try assumption. 
+ apply partitionsIsolationUpdtateSh1Structure with v0; trivial.
+ apply kernelDataIsolationUpdtateSh1Structure with v0;trivial.
+ apply verticalSharingUpdtateSh1Structure with v0;trivial.
+ apply consistencyRemoveVaddr with descChild
vaChild (currentPartition s) level (StateLib.getIndexOfAddr descChild levelMin) ptDescChild currentPD
ptDescChildFromPD (StateLib.getIndexOfAddr descChild levelMin) phyDescChild pdChildphy 
(StateLib.getIndexOfAddr vaChild levelMin)
ptVaChildpd shadow1Child ptVaChildFromSh1 vainve sh2Childphy
ptVaChildsh2 currentShadow (StateLib.getIndexOfAddr vainparent levelMin);trivial.

unfold propagatedPropertiesRemoveVaddr. 
subst.
intuition.
unfold not.
subst. 
trivial. 
Qed. 



Lemma isPartitionFalseAddDerivationNotEq childSh2 idxSh2 ( ptSh1ChildFromSh1:page) idxSh1 descChild (shadow2 shadow1: vaddr) ( currentShadow1:page) (l:level) s: 
isPartitionFalse childSh2 idxSh2 s ->
(Nat.eqb pageDefault childSh2) = false ->
(Nat.eqb pageDefault ptSh1ChildFromSh1) = false ->
consistency s ->
StateLib.getIndexOfAddr shadow2 levelMin = idxSh2 ->
StateLib.getIndexOfAddr shadow1 levelMin = idxSh1 ->
false = StateLib.checkVAddrsEqualityWOOffset nbLevel shadow1 shadow2 l ->
isVE childSh2 (StateLib.getIndexOfAddr shadow2 levelMin) s->
getTableAddrRoot childSh2 idxShadow1 (currentPartition s) shadow2 s ->
isVE ptSh1ChildFromSh1 (StateLib.getIndexOfAddr shadow1 levelMin) s ->
getTableAddrRoot ptSh1ChildFromSh1 idxShadow1 (currentPartition s) shadow1 s ->
nextEntryIsPP (currentPartition s) idxShadow1 currentShadow1 s ->
Some l = StateLib.getNbLevel ->
isPartitionFalse childSh2 idxSh2
  {|
  currentPartition := currentPartition s;
  memory := add ptSh1ChildFromSh1 idxSh1
              (VE {| pd := false;
                     va := descChild |}) (memory s) pageEq idxEq |}.
Proof.
intros ispart.
intros.
unfold isPartitionFalse in *.
simpl in *.
assert(Hreadflag : StateLib.readPDflag childSh2 idxSh2
  (add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |})        
  (memory s) pageEq idxEq) = StateLib.readPDflag childSh2 idxSh2
  (memory s)).
apply  readPDflagAddDerivation.
eapply toApplyPageTablesOrIndicesAreDifferent with shadow2 shadow1 (currentPartition s) 
currentShadow1 idxShadow1 l isVE  s;trivial.
right;left;trivial.
subst.
rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
intros;split;subst;trivial.
intros;split;subst;trivial.
rewrite Hreadflag;trivial.
Qed.
Lemma indirectionDescriptionAddDerivation ptSh1 vaValue flag l descChildphy 
phyPDChild vaToPrepare v0 idxroot s:
let s':= {|
      currentPartition := currentPartition s;
      memory := add ptSh1 (StateLib.getIndexOfAddr vaValue levelMin) 
              (VE {| pd := flag; va := vaValue |}) (memory s) pageEq idxEq |} in 
 lookup ptSh1 (StateLib.getIndexOfAddr vaValue levelMin)
            (memory s) pageEq idxEq = Some (VE v0) -> 
indirectionDescription s descChildphy phyPDChild idxroot vaToPrepare l -> 
indirectionDescription s' descChildphy phyPDChild idxroot vaToPrepare l.
Proof.
intros s' Hlookup Hind.
unfold indirectionDescription in *.
destruct Hind as (tableroot & Hpp & Hnotdef & Hor).
exists tableroot.
split;trivial.
unfold s'.
rewrite <- nextEntryIsPPAddDerivation;trivial. eassumption.
split;trivial.
destruct Hor as  [(Hroot & Hl) |(nbL & stop& HnbL & Hstop & Hind & Hnotdefind & Hl)].
left;split;trivial.
right.
exists nbL, stop.
intuition.
rewrite <- Hind.
apply getIndirectionAddDerivation with v0;trivial. 
Qed.

Lemma initPEntryTablePreconditionToPropagatePreparePropertiesAddDerivation pg
ptSh1 vaValue  v0  s:
let s':= {|
      currentPartition := currentPartition s;
      memory := add ptSh1 (StateLib.getIndexOfAddr vaValue levelMin) 
              (VE {| pd := false; va := vaValue |}) (memory s) pageEq idxEq |} in 
 lookup ptSh1 (StateLib.getIndexOfAddr vaValue levelMin)
            (memory s) pageEq idxEq = Some (VE v0) -> 
initPEntryTablePreconditionToPropagatePrepareProperties s pg ->
isPartitionFalse ptSh1 (StateLib.getIndexOfAddr vaValue levelMin)  s -> 
initPEntryTablePreconditionToPropagatePrepareProperties s' pg.
Proof.
intros s' Hlookup (Hgoal & Hnotdef) Hnotpart.
unfold initPEntryTablePreconditionToPropagatePrepareProperties.
split;trivial.
intros part Hpart.
assert(Hpartitions: getPartitions pageRootPartition s' = getPartitions pageRootPartition s). (* *)
 apply getPartitionsAddDerivation with v0;trivial.
assert(Hconf: getConfigPages part s'= getConfigPages part s).
apply getConfigPagesAddDerivation with v0;trivial.
rewrite Hconf.
apply Hgoal.
rewrite <- Hpartitions;trivial.
Qed.

Lemma writeAccessibleRecPreparePostconditionAddDerivation desc pg idx
ptSh1 vaValue  v0  s:
let s':= {|
      currentPartition := currentPartition s;
      memory := add ptSh1 idx
              (VE {| pd := false; va := vaValue |}) (memory s) pageEq idxEq |} in 
 lookup ptSh1 idx
            (memory s) pageEq idxEq = Some (VE v0) -> 
(* isPartitionFalse ptSh1 (StateLib.getIndexOfAddr vaValue fstLevel)  s -> *)            
writeAccessibleRecPreparePostcondition desc pg s ->
writeAccessibleRecPreparePostcondition desc pg s'.
Proof.
intros s' Hlookup Hgoal (*Hnotpart*).
unfold writeAccessibleRecPreparePostcondition in *.
intros part Hpart.
assert(Haccess: getAccessibleMappedPages part s' = getAccessibleMappedPages part s). (* *)
 apply getAccessibleMappedPagesAddDerivation with v0;trivial.
rewrite Haccess.
apply Hgoal.
assert(Hances: getAncestors desc s' = getAncestors desc s).
apply getAncestorsAddDerivation with v0;trivial.
rewrite <- Hances;trivial.
Qed.

Lemma isWellFormedMMUTablesAddDerivation s pg pt idx vaValue v0:
let s':= {|
  currentPartition := currentPartition s;
  memory := add pt idx (VE {| pd := false; va := vaValue |}) (memory s) pageEq idxEq |} in 
  lookup pt idx (memory s) pageEq idxEq = Some (VE v0) -> 
isWellFormedMMUTables pg s -> isWellFormedMMUTables pg s'.
Proof.
intros s' Hlookup Hgoal.
unfold isWellFormedMMUTables in *.
intros.
generalize (Hgoal idx0);clear Hgoal; intros (Hphy & Hpres).
split.
rewrite <- Hphy.
apply readPhyEntryAddDerivation with v0;trivial.
rewrite <- Hpres.
apply readPresentAddDerivation with v0;trivial.
Qed.

Lemma isWellFormedFstShadowTablesAddDerivation s phySh1addr pt idx vaValue v0 nbL partition:
let s':= {|
  currentPartition := currentPartition s;
  memory := add pt idx (VE {| pd := false; va := vaValue |}) (memory s) pageEq idxEq |} in 
  lookup pt idx (memory s) pageEq idxEq = Some (VE v0) -> 
initPEntryTablePreconditionToPropagatePrepareProperties s phySh1addr -> 
In partition (getPartitions pageRootPartition s) -> 
In pt (getConfigPages partition s) ->  
isWellFormedFstShadow nbL phySh1addr s-> isWellFormedFstShadow nbL phySh1addr s'.
Proof.
intros s' Hlookup (Hnotconfig&Hnotnull) Hpart Hconfig Hgoal.
unfold isWellFormedFstShadow in *.
destruct Hgoal as [(Hl & Hgoal) |(Hl & Hgoal)];[left|right];split;trivial;intros idx0;
generalize (Hgoal idx0);clear Hgoal; intros (Hphy & Hpres);
rewrite <- Hpres;rewrite<-  Hphy;split.
apply readPhyEntryAddDerivation with v0;trivial.
apply readPresentAddDerivation with v0;trivial.
apply readVirEntryAddDerivation.
unfold initPEntryTablePreconditionToPropagatePrepareProperties in *.
left.
apply Hnotconfig in Hpart.
unfold not;intros;subst.
now contradict Hconfig.
apply readPDflagAddDerivation.
unfold initPEntryTablePreconditionToPropagatePrepareProperties in *.
left.
apply Hnotconfig in Hpart.
unfold not;intros;subst.
now contradict Hconfig.
Qed.
Lemma isWellFormedSndShadowTablesAddDerivation s pg pt idx vaValue v0 l:
let s':= {|
  currentPartition := currentPartition s;
  memory := add pt idx (VE {| pd := false; va := vaValue |}) (memory s) pageEq idxEq |} in 
  lookup pt idx (memory s) pageEq idxEq = Some (VE v0) -> 
isWellFormedSndShadow l pg s -> isWellFormedSndShadow l pg s'.
Proof.
intros s' Hlookup Hgoal.
unfold isWellFormedSndShadow in *.
intros.
destruct Hgoal as [(Hl & Hgoal) |(Hl & Hgoal)];[left|right];split;trivial;intros idx0;
generalize (Hgoal idx0);clear Hgoal;[ intros (Hphy & Hpres)| intros Hphy];
rewrite <- Hphy;[rewrite<-  Hpres;split|].
apply readPhyEntryAddDerivation with v0;trivial.
apply readPresentAddDerivation with v0;trivial.
apply readVirtualAddDerivation with v0;trivial.
Qed.
   
Lemma newIndirectionsAreNotAccessibleAddDerivation s pt idx vaValue v0 phyMMUaddr phySh1addr phySh2addr: 
let s':= {|
  currentPartition := currentPartition s;
  memory := add pt idx (VE {| pd := false; va := vaValue |}) (memory s) pageEq idxEq |} in 
  lookup pt idx (memory s) pageEq idxEq = Some (VE v0) -> 
isPartitionFalse pt idx s -> 
 newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr -> 
 newIndirectionsAreNotAccessible s' phyMMUaddr phySh1addr phySh2addr.
Proof.
intros s' Hlookup Hpart Hgoal.
unfold newIndirectionsAreNotAccessible in *.
intros.
assert(Haccess: getAccessibleMappedPages parts s' =getAccessibleMappedPages parts s).
apply getAccessibleMappedPagesAddDerivation with v0;trivial.
rewrite Haccess.
apply Hgoal;trivial.
assert(Hparts: getPartitions pageRootPartition s' = getPartitions pageRootPartition s).
apply getPartitionsAddDerivation with v0;trivial.
rewrite <- Hparts;trivial.
Qed.
