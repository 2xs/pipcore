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
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Internal.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.InternalLemmas
               Pip.Proof.Isolation Pip.Proof.Lib Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Invariants GetTableAddr PropagatedProperties.
Import List.ListNotations Coq.Logic.ProofIrrelevance Lia List Compare_dec EqNat.

Lemma getPdUpdateUserFlag ( partition : page) entry s table idx flag:
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->
StateLib.getPd partition
  (add table idx
     (PE
        {|
        read := read entry;
        write := write entry;
        exec := exec entry;
        present := present entry;
        user := flag;
        pa := pa entry |}) (memory s) beqPage beqIndex) = StateLib.getPd partition (memory s).
Proof.
simpl. 
intros Hentry. 
unfold StateLib.getPd. destruct(StateLib.Index.succ PDidx).
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry. 
   cbn. trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
 + trivial.
Qed. 

Lemma getFstShadowUpdateUserFlag partition table idx flag s entry: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getFstShadow partition
  (add table idx
     (PE
         {|
        read := read entry;
        write := write entry;
        exec := exec entry;
        present := present entry;
        user := flag;
        pa := pa entry |}) (memory s) beqPage beqIndex) =
StateLib.getFstShadow partition (memory s). 
Proof.
intro Hentry.
cbn.
unfold StateLib.getFstShadow. 
case_eq (StateLib.Index.succ sh1idx);trivial.
intros.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex); intros Hpairs.
   + apply beqPairsTrue in Hpairs.
     destruct Hpairs as (Htable & Hidx).  subst.
     rewrite Hentry. 
     cbn. trivial.
   + apply beqPairsFalse in Hpairs.
     assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
                beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
     { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity. 
Qed. 
Lemma getSndShadowUpdateUserFlag partition table idx flag s entry: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getSndShadow partition
  (add table idx
     (PE
        {|
        read := read entry;
        write := write entry;
        exec := exec entry;
        present := present entry;
        user := flag;
        pa := pa entry |}) (memory s) beqPage beqIndex) =
StateLib.getSndShadow partition (memory s). 
Proof.
intro Hentry.
cbn.
unfold StateLib.getSndShadow. 
case_eq (StateLib.Index.succ sh2idx);trivial.
intros.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex); intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry. 
   cbn. trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
            beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity. intuition. }
   rewrite Hmemory. reflexivity. 
Qed.


Lemma getConfigTablesLinkedListUpdateUserFlag partition table idx flag s entry: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getConfigTablesLinkedList partition
  (add table idx
     (PE
        {|
        read := read entry;
        write := write entry;
        exec := exec entry;
        present := present entry;
        user := flag;
        pa := pa entry |}) (memory s) beqPage beqIndex) =
StateLib.getConfigTablesLinkedList partition (memory s). 
Proof.
intro Hentry.
cbn.
unfold StateLib.getConfigTablesLinkedList. 
case_eq (StateLib.Index.succ sh3idx);trivial.
intros.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex); intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry. 
   cbn. trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
            beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity. intuition. }
   rewrite Hmemory. reflexivity. 
Qed.
Lemma getParentUpdateUserFlag ( partition : page) entry s table idx flag:
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->
StateLib.getParent partition
  (add table idx
     (PE
        {|
        read := read entry;
        write := write entry;
        exec := exec entry;
        present := present entry;
        user := flag;
        pa := pa entry |}) (memory s) beqPage beqIndex) = StateLib.getParent partition (memory s).
Proof. 
simpl.
intros Hentry. 
unfold StateLib.getParent. destruct(StateLib.Index.succ PPRidx).
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry. 
   cbn. trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
 + trivial.
Qed. 

Lemma getIndirectionUpdateUserFlag p table idx flag s entry a l stop:
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->
getIndirection p a l stop
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} =
getIndirection p a l stop s .
Proof.
intros Hentry.
revert p l.
induction  stop.
+ simpl. trivial.
+ simpl. intros. 
  destruct (StateLib.Level.eqb l fstLevel);trivial.
  set (entry0 := (PE
  {|
  read := read entry;
  write := write entry;
  exec := exec entry;
  present := present entry;
  user := flag;
  pa := pa entry |}) ) in *.
  simpl.
  assert (StateLib.readPhyEntry p (StateLib.getIndexOfAddr a l) (add table idx entry0 (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry p (StateLib.getIndexOfAddr a l) (memory s)) as HreadPhyEnt.
  { unfold StateLib.readPhyEntry.
    cbn.  
    case_eq ( beqPairs (table, idx) (p, (StateLib.getIndexOfAddr a l)) beqPage beqIndex);trivial;intros Hpairs.
    + apply beqPairsTrue in Hpairs.
      destruct Hpairs as (Htable & Hidx).  subst.
      rewrite Hentry. 
      cbn. trivial.
    + apply beqPairsFalse in Hpairs.
      assert (lookup  p (StateLib.getIndexOfAddr a l) (removeDup table idx (memory s) beqPage beqIndex)
                beqPage beqIndex = lookup  p (StateLib.getIndexOfAddr a l)   (memory s) beqPage beqIndex) as Hmemory.
        { apply removeDupIdentity. subst.  intuition. }
      rewrite Hmemory. reflexivity.
   } 
  rewrite HreadPhyEnt.
  destruct (StateLib.readPhyEntry p (StateLib.getIndexOfAddr a l) (memory s));trivial.
  destruct (Nat.eqb defaultPage p0);trivial.
  destruct ( StateLib.Level.pred l );trivial.
Qed.
Lemma readPDflagUpdateUserFlag s entry flag idx table pg i: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
 StateLib.readPDflag pg i
  (add table idx
     (PE
        {|
        read := read entry;
        write := write entry;
        exec := exec entry;
        present := present entry;
        user := flag;
        pa := pa entry |}) (memory s) beqPage beqIndex) = StateLib.readPDflag pg i (memory s).
Proof.     
intros Hentry.
unfold StateLib.readPDflag. cbn. 
case_eq ( beqPairs (table, idx) (pg, i) beqPage beqIndex);intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).  subst.
  rewrite Hentry. 
  cbn. trivial.
+ intros.
  apply beqPairsFalse in Hpairs.
  assert (lookup  pg i  (removeDup table idx (memory s) beqPage beqIndex)
                beqPage beqIndex = lookup  pg i  (memory s) beqPage beqIndex) as Hmemory.
  { apply removeDupIdentity. intuition. }
  rewrite Hmemory. reflexivity.
Qed. 
Lemma readVirtualUpdateUserFlag s entry flag idx table pg i: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
 StateLib.readVirtual pg i
  (add table idx
     (PE
        {|
        read := read entry;
        write := write entry;
        exec := exec entry;
        present := present entry;
        user := flag;
        pa := pa entry |}) (memory s) beqPage beqIndex) = StateLib.readVirtual pg i (memory s).
Proof.     
intros Hentry.
unfold StateLib.readVirtual. cbn. 
case_eq ( beqPairs (table, idx) (pg, i) beqPage beqIndex);intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).  subst.
  rewrite Hentry. 
  cbn. trivial.
+ intros.
  apply beqPairsFalse in Hpairs.
  assert (lookup  pg i  (removeDup table idx (memory s) beqPage beqIndex)
                beqPage beqIndex = lookup  pg i  (memory s) beqPage beqIndex) as Hmemory.
  { apply removeDupIdentity. intuition. }
  rewrite Hmemory. reflexivity.
Qed. 
Lemma readPhyEntryUpdateUserFlag s entry flag idx table pg i: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
 StateLib.readPhyEntry pg i
  (add table idx
     (PE
        {|
        read := read entry;
        write := write entry;
        exec := exec entry;
        present := present entry;
        user := flag;
        pa := pa entry |}) (memory s) beqPage beqIndex) = StateLib.readPhyEntry pg i (memory s).
Proof.     
intros Hentry.
unfold StateLib.readPhyEntry.
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx
       (PE
          {|
          read := read entry;
          write := write entry;
          exec := exec entry;
          present := present entry;
          user := flag;
          pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
cbn. 
case_eq ( beqPairs (table, idx) (pg, i) beqPage beqIndex);intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).  subst.
  rewrite Hentry. 
  cbn. trivial.
+ intros.
  apply beqPairsFalse in Hpairs.
  assert (lookup  pg i  (removeDup table idx (memory s) beqPage beqIndex)
          beqPage beqIndex = lookup  pg i  (memory s) beqPage beqIndex) as Hmemory.
  { apply removeDupIdentity. intuition. }
  rewrite Hmemory. reflexivity.
Qed.

Lemma readPhysicalUpdateUserFlag s entry flag idx table pg i: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
 StateLib.readPhysical pg i
  (add table idx
     (PE
        {|
        read := read entry;
        write := write entry;
        exec := exec entry;
        present := present entry;
        user := flag;
        pa := pa entry |}) (memory s) beqPage beqIndex) = StateLib.readPhysical pg i (memory s).
Proof.     
intros Hentry.
unfold StateLib.readPhysical.
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx
       (PE
          {|
          read := read entry;
          write := write entry;
          exec := exec entry;
          present := present entry;
          user := flag;
          pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
cbn. 
case_eq ( beqPairs (table, idx) (pg, i) beqPage beqIndex);intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).  subst.
  rewrite Hentry. 
  cbn. trivial.
+ intros.
  apply beqPairsFalse in Hpairs.
  assert (lookup  pg i  (removeDup table idx (memory s) beqPage beqIndex)
          beqPage beqIndex = lookup  pg i  (memory s) beqPage beqIndex) as Hmemory.
  { apply removeDupIdentity. intuition. }
  rewrite Hmemory. reflexivity.
Qed.

Lemma readVirEntryUpdateUserFlag p table idx idx1 s entry flag:
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.readVirEntry p idx1 (memory s) =
StateLib.readVirEntry p idx1
(add table idx
 (PE
    {|
    read := read entry;
    write := write entry;
    exec := exec entry;
    present := present entry;
    user := flag;
    pa := pa entry |}) (memory s) beqPage beqIndex).
Proof.
intros Hentry.
unfold StateLib.readVirEntry.
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx
       (PE
          {|
          read := read entry;
          write := write entry;
          exec := exec entry;
          present := present entry;
          user := flag;
          pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
cbn. 
case_eq ( beqPairs (table, idx) (p, idx1)  beqPage beqIndex);intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).  subst.
  rewrite Hentry. 
  cbn. trivial.
+ intros.
  apply beqPairsFalse in Hpairs.
  assert (lookup p idx1 (removeDup table idx (memory s) beqPage beqIndex)
          beqPage beqIndex = lookup  p idx1   (memory s) beqPage beqIndex) as Hmemory.
  { apply removeDupIdentity. intuition. }
  rewrite Hmemory. reflexivity.
Qed.


Lemma readAccessibleUpdateUserFlag table1 table2 idx1 idx2 entry flag s :
table1 <> table2 \/ idx1 <> idx2 -> 
 StateLib.readAccessible table1 idx1
         (add table2 idx2
            (PE
               {|
               read := read entry;
               write := write entry;
               exec := exec entry;
               present := present entry;
               user := flag;
               pa := pa entry |}) (memory s) beqPage beqIndex) = 
 StateLib.readAccessible table1 idx1 (memory s).
Proof.
unfold StateLib.readAccessible.
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

Lemma checkChildUpdateUserFlag partition l s a table idx entry flag: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.checkChild partition l
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
               read := read entry;
               write := write entry;
               exec := exec entry;
               present := present entry;
               user := flag;
               pa := pa entry |}) (memory s) beqPage beqIndex |} a =
StateLib.checkChild partition l s a.
Proof. 
unfold StateLib.checkChild.
intros Hentry.
set (s' :=   {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                  {|
               read := read entry;
               write := write entry;
               exec := exec entry;
               present := present entry;
               user := flag;
               pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
assert( StateLib.getFstShadow partition (memory s')= StateLib.getFstShadow partition (memory s) ) as Hfstsh.
apply getFstShadowUpdateUserFlag ;trivial.
rewrite Hfstsh. 
case_eq (StateLib.getFstShadow partition (memory s));trivial.
+ intros.  
intros.
    assert (getIndirection p a l (nbLevel - 1)  s' = getIndirection p a l (nbLevel - 1)  s) as Hind.
    { apply getIndirectionUpdateUserFlag;trivial. }
  rewrite Hind.
  destruct (getIndirection p a l (nbLevel - 1) s).
  assert (StateLib.readPDflag p0 (StateLib.getIndexOfAddr a fstLevel) (memory s') = 
  StateLib.readPDflag p0 (StateLib.getIndexOfAddr a fstLevel) (memory s)) as Hpdflag.
  apply readPDflagUpdateUserFlag;trivial. 
  rewrite Hpdflag. reflexivity. trivial.
Qed.
Lemma getPdsVAddrUpdateUserFlag (partition : page) l  s entry table idx flag: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
getPdsVAddr partition l getAllVAddrWithOffset0
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                  {|
               read := read entry;
               write := write entry;
               exec := exec entry;
               present := present entry;
               user := flag;
               pa := pa entry |}) (memory s) beqPage beqIndex |} =
getPdsVAddr partition l getAllVAddrWithOffset0 s.
Proof.
intros Hentry.  
unfold getPdsVAddr.
induction getAllVAddrWithOffset0. simpl. trivial.
simpl. 
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx
       (PE
           {|
               read := read entry;
               write := write entry;
               exec := exec entry;
               present := present entry;
               user := flag;
               pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
assert (StateLib.checkChild partition l s' a =
        StateLib.checkChild partition l s a) as HpartRef.
apply checkChildUpdateUserFlag ;trivial.
rewrite HpartRef.
rewrite IHl0. reflexivity.
Qed.
Lemma getMappedPageUpdateUserFlag p a s table idx flag entry : 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->       
getMappedPage p
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} a = getMappedPage p s a.
Proof.
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx
       (PE
          {|
          read := read entry;
          write := write entry;
          exec := exec entry;
          present := present entry;
          user := flag;
          pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
          intros Hentry. 
unfold getMappedPage. destruct StateLib.getNbLevel;trivial.
assert(getIndirection p a l (nbLevel - 1) s' =
        getIndirection p a l (nbLevel - 1) s)as Hind.
apply getIndirectionUpdateUserFlag;trivial. 
rewrite Hind.
destruct (getIndirection p a l (nbLevel - 1) s);trivial.
assert(StateLib.readPresent p0 (StateLib.getIndexOfAddr a fstLevel) (memory s')  = 
StateLib.readPresent p0 (StateLib.getIndexOfAddr a fstLevel) (memory s) ) as HreadP.
{ unfold StateLib.readPresent. cbn. 
  case_eq ( beqPairs (table, idx) (p0, (StateLib.getIndexOfAddr a fstLevel)) beqPage beqIndex);trivial;intros Hpairs.
    + apply beqPairsTrue in Hpairs.
    destruct Hpairs as (Htable & Hidx).  subst.
    rewrite Hentry. 
    cbn. trivial.
    + apply beqPairsFalse in Hpairs.
      assert (lookup  p0 (StateLib.getIndexOfAddr a fstLevel) (removeDup table idx (memory s) beqPage beqIndex)
      beqPage beqIndex = lookup  p0 (StateLib.getIndexOfAddr a fstLevel)  (memory s) beqPage beqIndex) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory. reflexivity.      }
rewrite HreadP.
destruct (StateLib.readPresent p0 (StateLib.getIndexOfAddr a fstLevel) (memory s));trivial.
cbn. 
unfold StateLib.readPhyEntry.
cbn.  
case_eq ( beqPairs (table, idx) (p0, (StateLib.getIndexOfAddr a fstLevel)) beqPage beqIndex);trivial;intros Hpairs.
  + apply beqPairsTrue in Hpairs.
    destruct Hpairs as (Htable & Hidx).  subst.
    rewrite Hentry. 
    cbn. trivial.
  + apply beqPairsFalse in Hpairs.
    assert (lookup  p0 (StateLib.getIndexOfAddr a fstLevel) (removeDup table idx (memory s) beqPage beqIndex)
            beqPage beqIndex = lookup  p0 (StateLib.getIndexOfAddr a fstLevel)  (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity. subst.  intuition. }
    rewrite Hmemory. reflexivity.
Qed.
(*
Lemma getAccessibleMappedPageUpdateUserFalse p a s table idx entry : 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->       
getAccessibleMappedPage p
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} a = getAccessibleMappedPage p s a.
Proof.
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx
       (PE
          {|
          read := read entry;
          write := write entry;
          exec := exec entry;
          present := present entry;
          user := false;
          pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
          intros Hentry. 
unfold getAccessibleMappedPage.
destruct StateLib.getNbLevel;trivial.
assert(getIndirection p a l (nbLevel - 1) s' =
        getIndirection p a l (nbLevel - 1) s)as Hind.
apply getIndirectionUpdateUserFlag;trivial. 
rewrite Hind.
destruct (getIndirection p a l (nbLevel - 1) s);trivial.
assert(StateLib.readPresent p0 (StateLib.getIndexOfAddr a fstLevel) (memory s')  = 
StateLib.readPresent p0 (StateLib.getIndexOfAddr a fstLevel) (memory s) ) as HreadP.
{ unfold StateLib.readPresent. cbn. 
  case_eq ( beqPairs (table, idx) (p0, (StateLib.getIndexOfAddr a fstLevel)) beqPage beqIndex);trivial;intros Hpairs.
    + apply beqPairsTrue in Hpairs.
    destruct Hpairs as (Htable & Hidx).  subst.
    rewrite Hentry. 
    cbn. trivial.
    + apply beqPairsFalse in Hpairs.
      assert (lookup  p0 (StateLib.getIndexOfAddr a fstLevel) (removeDup table idx (memory s) beqPage beqIndex)
      beqPage beqIndex = lookup  p0 (StateLib.getIndexOfAddr a fstLevel)  (memory s) beqPage beqIndex) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory. reflexivity.      }
rewrite HreadP.
destruct (StateLib.readPresent p0 (StateLib.getIndexOfAddr a fstLevel) (memory s));trivial.
destruct b; trivial.
unfold StateLib.readAccessible.

unfold StateLib.readPhyEntry.
cbn.  
case_eq ( beqPairs (table, idx) (p0, (StateLib.getIndexOfAddr a fstLevel)) beqPage beqIndex);trivial;intros Hpairs.
  + apply beqPairsTrue in Hpairs.
    destruct Hpairs as (Htable & Hidx).  subst.
    rewrite Hentry. 
    cbn. trivial.
  + apply beqPairsFalse in Hpairs.
    assert (lookup  p0 (StateLib.getIndexOfAddr a fstLevel) (removeDup table idx (memory s) beqPage beqIndex)
            beqPage beqIndex = lookup  p0 (StateLib.getIndexOfAddr a fstLevel)  (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity. subst.  intuition. }
    rewrite Hmemory. reflexivity.
Qed.
 *)
Lemma getMappedPagesAuxUpdateUserFlag  p l s entry flag table idx : 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->    
   getMappedPagesAux p l
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} =
getMappedPagesAux p l s.
Proof.
unfold getMappedPagesAux.
intros Hentry. 
f_equal.
unfold  getMappedPagesOption.
induction l.
simpl. trivial.
simpl.
rewrite IHl.
f_equal.
apply getMappedPageUpdateUserFlag;trivial.
Qed.

Lemma readPresentUpdateUserFlag  p s entry table idx idx1 flag: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->
StateLib.readPresent p idx1
  (add table idx
     (PE
        {|
        read := read entry;
        write := write entry;
        exec := exec entry;
        present := present entry;
        user := flag;
        pa := pa entry |}) (memory s) beqPage beqIndex) = StateLib.readPresent p idx1 (memory s).
Proof.
simpl.
intros Hentry.
unfold StateLib.readPresent. cbn. 
  case_eq ( beqPairs (table, idx) (p, idx1) beqPage beqIndex);trivial;intros Hpairs.
    + apply beqPairsTrue in Hpairs.
    destruct Hpairs as (Htable & Hidx).  subst.
    rewrite Hentry. 
    cbn. trivial.
    + apply beqPairsFalse in Hpairs.
      assert (lookup  p idx1 (removeDup table idx (memory s) beqPage beqIndex)
      beqPage beqIndex = lookup  p idx1  (memory s) beqPage beqIndex) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory. reflexivity.
Qed.


Lemma entryUserFlagUpdateUserFlagRandomValue table1 table2 idx1 idx2 flag entry accessibleflag s : 
(table2 <> table1 \/ idx2 <> idx1) -> 
lookup table1 idx1(memory s) beqPage beqIndex = Some (PE entry) ->
entryUserFlag table2 idx2 accessibleflag s -> 
entryUserFlag table2 idx2 accessibleflag
{|
currentPartition := currentPartition s;
memory := add table1 idx1
    (PE
       {|
       read := read entry;
       write := write entry;
       exec := exec entry;
       present := present entry;
       user := flag;
       pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hnoteq Hlookup Huser.
unfold entryUserFlag in *.
cbn in *.
case_eq (beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex ); intros Hpairs.
{  apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
   subst. rewrite Hlookup in Huser. cbn.
   contradict Hnoteq. intuition. }
{ apply beqPairsFalse in Hpairs.
  assert (lookup  table2 idx2  (removeDup table1 idx1 (memory s) beqPage beqIndex)
  beqPage beqIndex = lookup  table2 idx2 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory. assumption. }
Qed.

(*Lemma getIndirectionRetDefaultLtNbLevel :
assert( (p <> table1 \/  lastidx = idx1) \/ (p = table1 /\ lastidx = idx1) ).
*)
Lemma getAccessibleMappedPagesAuxUpdateUserFlag  (partition: page) l s entry table1 idx1 : 
lookup table1 idx1 (memory s) beqPage beqIndex = Some (PE entry) ->  
incl (getAccessibleMappedPagesAux partition l {|
  currentPartition := currentPartition s;
  memory := add table1 idx1
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |})
     (getAccessibleMappedPagesAux partition l s).
Proof.
unfold getAccessibleMappedPagesAux.
intros Hentry.
unfold  getAccessibleMappedPagesOption.
unfold incl.
intros table2 Hin.
apply filterOptionInIff.
apply filterOptionInIff in Hin.
apply in_map_iff.
apply in_map_iff in Hin.
destruct Hin as (va & HgetAcc & Hin).
exists va. split; trivial.
set(s' := {|
  currentPartition := currentPartition s;
  memory := add table1 idx1
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
unfold getAccessibleMappedPage in *.
destruct (StateLib.getNbLevel); [ | now contradict HgetAcc].
assert(getIndirection partition va l0 (nbLevel - 1) s' = getIndirection partition va l0 (nbLevel - 1) s) as 
Hget.
apply getIndirectionUpdateUserFlag; trivial.
set(lastidx := (StateLib.getIndexOfAddr va fstLevel)) in *.
rewrite Hget in HgetAcc.
destruct (getIndirection partition va l0 (nbLevel - 1) s); [| now contradict HgetAcc].
assert(StateLib.readPresent p lastidx (memory s')  = 
StateLib.readPresent p lastidx (memory s) ) as HreadP.
apply readPresentUpdateUserFlag; trivial.
rewrite HreadP in HgetAcc.
destruct(Nat.eqb defaultPage p); try now contradict HgetAcc.
destruct (StateLib.readPresent p lastidx (memory s));
[| now contradict Hget].
destruct b;[| now contradict HgetAcc].
assert( p <> table1 \/  p = table1). 
{ destruct p.
     destruct table1. simpl in *.
     assert(p = p0 \/ p <> p0) by lia.
     destruct H.
     right.
     simpl.
     subst.
     f_equal.
     apply proof_irrelevance.
     left.
     unfold not.
     intros.
     inversion H0. lia. }
destruct H.
+   assert( StateLib.readAccessible p lastidx (memory s') =  StateLib.readAccessible p lastidx  (memory s)) as Hacc.
{ unfold s'.
unfold StateLib.readAccessible.
simpl.  
subst.
   case_eq (beqPairs (table1, idx1) (p, lastidx) beqPage beqIndex ); intros Hpairs.
{  apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
   subst. now contradict H. }
{ apply beqPairsFalse in Hpairs.
subst. 
assert( lookup p lastidx (removeDup table1 idx1 (memory s) beqPage beqIndex) beqPage beqIndex  = 
lookup p lastidx (memory s) beqPage beqIndex).
apply removeDupIdentity. subst. destruct Hpairs. left; trivial. right. unfold not; intros. 
rewrite  H1 in H0.  now contradict H0.
rewrite H0. trivial.  } }
simpl.

rewrite <- Hacc. 
    case_eq (StateLib.readAccessible p lastidx (memory s')); intros; subst.
    case_eq b; intros; subst;
    rewrite H0 in HgetAcc; trivial.
    rewrite <- HgetAcc.
    symmetry.
    simpl.
   rewrite readPhyEntryUpdateUserFlag; trivial.
    rewrite H0 in HgetAcc; trivial.
+ subst. 
   assert (lastidx <> idx1 \/ lastidx = idx1 ).
   { destruct lastidx.
     destruct idx1. simpl in *.
     assert(i = i0 \/ i <> i0) by lia.
     destruct H.
     right.
     simpl.
     subst.
     f_equal.
     apply proof_irrelevance.
     left.
     unfold not.
     intros.
     inversion H0. lia. }
   destruct H.
   - assert( StateLib.readAccessible table1 lastidx (memory s') =  StateLib.readAccessible table1    lastidx  (memory s)) as Hacc.
   unfold StateLib.readAccessible.
   assert(lookup table1 lastidx (memory s') beqPage beqIndex  = lookup table1 lastidx (memory s) beqPage beqIndex ). 
   { unfold s'.
    
   case_eq(lookup table1 lastidx (memory s') beqPage beqIndex ); intros. simpl.
   case_eq (beqPairs (table1, idx1) (table1, lastidx) beqPage beqIndex ); intros Hpairs.
{  apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
   subst. now contradict H. }
{ apply beqPairsFalse in Hpairs.
apply removeDupIdentity. subst. destruct Hpairs. left; trivial. right. unfold not; intros. 
rewrite  H2 in H1. now contradict H1.  }
simpl.
unfold StateLib.readAccessible  in HgetAcc.
rewrite H0 in HgetAcc.
now contradict HgetAcc. }
rewrite H0. trivial. 
    rewrite Hacc in HgetAcc. 
    case_eq (StateLib.readAccessible table1 lastidx (memory s)); intros; subst.
    case_eq b; intros; subst;
    rewrite H0 in HgetAcc; trivial.
    rewrite <- HgetAcc.
    symmetry.
    simpl.
    rewrite readPhyEntryUpdateUserFlag; trivial.
    rewrite H0 in HgetAcc; trivial.
  - subst lastidx.
    assert(StateLib.readAccessible table1 idx1 (memory s') = Some false).
    unfold s'.
    unfold StateLib.readAccessible.
    simpl.
    assert(beqPairs (table1, idx1) (table1, idx1) beqPage beqIndex = true).
    apply beqPairsTrue.
    split; trivial.
    rewrite H0; simpl; trivial.
    subst.
    rewrite H0 in HgetAcc.
    now contradict HgetAcc.
Qed.

Lemma getChildrenUpdateFlagUser (partition : page) s entry table idx flag: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->  
getChildren partition
     {|
     currentPartition := currentPartition s;
     memory := add table idx
                 (PE
                     {|
               read := read entry;
               write := write entry;
               exec := exec entry;
               present := present entry;
               user := flag;
               pa := pa entry |}) (memory s) beqPage beqIndex |} = getChildren partition s.
Proof.
intros Hentry. 
unfold getChildren.
set (entry0 := (PE  {|
               read := read entry;
               write := write entry;
               exec := exec entry;
               present := present entry;
               user := flag;
               pa := pa entry |}) ) in *. 
set (s' := {|
          currentPartition := currentPartition s;
          memory := add table idx entry0 (memory s) beqPage beqIndex |}) in *.
destruct StateLib.getNbLevel;trivial.
assert(StateLib.getPd partition (memory s') =
         StateLib.getPd partition (memory s)) as HgetPd.
apply getPdUpdateUserFlag ;trivial.
rewrite HgetPd.
destruct (StateLib.getPd partition (memory s));trivial.
assert (getPdsVAddr partition l getAllVAddrWithOffset0 s' = 
            getPdsVAddr partition l getAllVAddrWithOffset0 s) as HgetPdsVa.
    { apply getPdsVAddrUpdateUserFlag;trivial. }
rewrite HgetPdsVa.
apply getMappedPagesAuxUpdateUserFlag;trivial.
Qed.


Lemma getPartitionAuxUpdateUserFlag l s entry  table idx flag: 
 lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
 getPartitionAux l {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                  {|
               read := read entry;
               write := write entry;
               exec := exec entry;
               present := present entry;
               user := flag;
               pa := pa entry |}) (memory s) beqPage beqIndex |} (nbPage+1) =
getPartitionAux l s (nbPage+1). 
Proof. 
intros Hentry.
revert l.
induction (nbPage+1).
now cbn.
simpl.
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx
       (PE
           {|
               read := read entry;
               write := write entry;
               exec := exec entry;
               present := present entry;
               user := flag;
               pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
          intros. f_equal.
assert (getChildren l s = getChildren l s') as Hchildren.
unfold s'. symmetry.
apply getChildrenUpdateFlagUser;trivial. 
rewrite <- Hchildren.
simpl.
clear Hchildren.
induction  (getChildren l s).
 simpl. trivial.
 simpl.
 f_equal.
 apply IHn.
 apply IHl0.
Qed.

Lemma getPartitionsUpdateUserFlag partition table idx s flag  entry:
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->  
getPartitions partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} =
getPartitions partition s. 
Proof.
unfold getPartitions.
intros Hentry.

apply getPartitionAuxUpdateUserFlag;trivial.
Qed.

Lemma getTablePagesUpdateUserFlag table idx flag entry p s size: 
 lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
getTablePages p size
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} = getTablePages p size s.
Proof.
revert p table idx.
induction size;
intros;  trivial.
simpl.
case_eq(beqPairs (table, idx) (p, CIndex size) beqPage beqIndex);intros Hpairs.
+ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
  subst.
  rewrite H. cbn. 
  destruct (Nat.eqb (pa entry) defaultPage);
  generalize (IHsize p p (CIndex size) H);clear IHsize; intros IHsize;
  rewrite IHsize;trivial.
+ apply beqPairsFalse in Hpairs.
  assert (lookup   p (CIndex size) (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  p (CIndex size) (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. subst.  intuition. }
  rewrite  Hmemory. 
  destruct (lookup p (CIndex size) (memory s) beqPage beqIndex); [
  | generalize (IHsize p table idx );clear IHsize; intros IHsize;
  apply IHsize;trivial ].
  destruct v; try (destruct (Nat.eqb (pa p0) defaultPage); assumption);
  generalize (IHsize p table idx H);clear IHsize; intros IHsize;
  rewrite IHsize;trivial .
Qed.

Lemma getIndirectionsUpdateUserFlag l table idx entry flag s  level: 
 lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
 getIndirectionsAux l {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} level =
getIndirectionsAux l s level. 

Proof.
intros Hentry.
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx
       (PE
          {|
          read := read entry;
          write := write entry;
          exec := exec entry;
          present := present entry;
          user := flag;
          pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
revert l.
induction level.
simpl. trivial. simpl.
intros. f_equal.
    assert (getTablePages l tableSize s' = getTablePages l tableSize s) as Htablepages.
  apply getTablePagesUpdateUserFlag;trivial. 
  rewrite Htablepages.
  clear Htablepages.
  induction (getTablePages l tableSize s); intros; trivial.
  simpl in *.
   rewrite IHl0. 
   f_equal.
   apply IHlevel.
   Qed.

Lemma getConfigTablesLinkedListsUpdateUserFlag s sh3 flag table idx entry :
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
getLLPages sh3
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} (nbPage+1) =
getLLPages sh3 s (nbPage+1).
Proof.
revert sh3.
induction (nbPage+1);trivial.
intros. simpl.
 set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx
       (PE
          {|
          read := read entry;
          write := write entry;
          exec := exec entry;
          present := present entry;
          user := flag;
          pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
destruct (StateLib.getMaxIndex);trivial.
rewrite readPhysicalUpdateUserFlag;trivial.
destruct (StateLib.readPhysical sh3 i (memory s));trivial.
destruct (Nat.eqb p defaultPage) ;trivial.
f_equal.
generalize (IHn p);clear IHn ; intros IHn;apply IHn.
assumption.

Qed. 
 Lemma lookupPEUpdateUserFlag s entry table idx indirection idx0 flag : 
forall pe1, lookup indirection idx0 (memory s) beqPage beqIndex = Some (PE pe1) ->
exists pe2, 
          lookup indirection idx0  (add table idx
       (PE
          {|
          read := read entry;
          write := write entry;
          exec := exec entry;
          present := present entry;
          user := flag;
          pa := pa entry |}) (memory s) beqPage beqIndex)beqPage beqIndex  = Some (PE pe2).
Proof.
intros . cbn. 
case_eq(beqPairs (table, idx)  (indirection, idx0) beqPage beqIndex);intros Hpairs.
+ apply beqPairsTrue in Hpairs. destruct Hpairs as (Htable & Hidx).
  subst. eexists. reflexivity.
+ apply beqPairsFalse in Hpairs.
  assert (lookup  indirection idx0 (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  indirection idx0  (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. subst.  intuition. }
  eexists.
  rewrite  Hmemory. eassumption.
Qed.
Lemma getConfigPagesUpdateUserFlag partition s entry flag table idx : 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
getConfigPages partition {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} = 
getConfigPages partition s . 
Proof.
unfold getConfigPages.
set (s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
intros. 
assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
apply getPdUpdateUserFlag;trivial.
unfold getConfigPagesAux in *.
rewrite HgetPd.
destruct (StateLib.getPd partition (memory s)) as [ pd|] ;trivial.
assert (StateLib.getFstShadow partition (memory s') = StateLib.getFstShadow partition (memory s)) as Hsh1.
apply getFstShadowUpdateUserFlag;trivial.
rewrite Hsh1.
destruct  (StateLib.getFstShadow partition (memory s))as [ sh1|]  ;trivial.
assert (StateLib.getSndShadow partition (memory s') = StateLib.getSndShadow partition (memory s)) as Hsh2.
apply getSndShadowUpdateUserFlag;trivial.
rewrite Hsh2.
destruct  (StateLib.getSndShadow partition (memory s))as [ sh2|]  ;trivial.
assert (StateLib.getConfigTablesLinkedList partition (memory s') = StateLib.getConfigTablesLinkedList partition (memory s)) as Hsh3.
apply getConfigTablesLinkedListUpdateUserFlag;trivial.
rewrite Hsh3.
destruct  (StateLib.getConfigTablesLinkedList partition (memory s)) as [ sh3|] ;trivial.
assert (getIndirections pd s' = getIndirections pd s) as Hind.
apply getIndirectionsUpdateUserFlag ; trivial.
rewrite Hind; clear Hind.
assert (getIndirections sh1 s' = getIndirections sh1 s) as Hind.
apply getIndirectionsUpdateUserFlag ; trivial.
rewrite Hind; clear Hind.
assert (getIndirections sh2 s' = getIndirections sh2 s) as Hind.
apply getIndirectionsUpdateUserFlag ; trivial.
rewrite Hind; clear Hind.
unfold s'.
rewrite getConfigTablesLinkedListsUpdateUserFlag; trivial.
Qed.

Lemma initPEntryTablePreconditionToPropagatePreparePropertiesUpdateUserFlag userPage
 s entry flag table idx : 
let s':= {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}  in
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
initPEntryTablePreconditionToPropagatePrepareProperties s userPage -> 
initPEntryTablePreconditionToPropagatePrepareProperties s' userPage.
Proof.
intros s' Hlookup (Hconf & Hfalse).
unfold initPEntryTablePreconditionToPropagatePrepareProperties in *.
split;trivial.
intros part Hpart.
unfold s' in Hpart.
rewrite getPartitionsUpdateUserFlag in Hpart;trivial.
unfold s'.
rewrite getConfigPagesUpdateUserFlag;trivial.
apply Hconf;trivial.
Qed.

Lemma getMappedPagesUpdateUserFlag partition s entry flag table idx : 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
getMappedPages partition  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}  = getMappedPages partition s.
Proof.
intros. 
set (s' := {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} ) in *.
unfold getMappedPages. 
assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
apply getPdUpdateUserFlag;trivial.
rewrite HgetPd.
destruct (StateLib.getPd partition (memory s)) ;trivial.
apply getMappedPagesAuxUpdateUserFlag;trivial.
Qed.
 
Lemma getAccessibleMappedPagesUpdateUserFlagFalse partition s entry table idx : 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
incl (getAccessibleMappedPages partition  {|
          currentPartition := currentPartition s;
          memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) 
    (getAccessibleMappedPages partition s).
Proof.
intros. 
set (s' := {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} ) in *.
unfold getAccessibleMappedPages. 
assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
apply getPdUpdateUserFlag;trivial.
rewrite HgetPd.
destruct (StateLib.getPd partition (memory s)) ;trivial.
apply getAccessibleMappedPagesAuxUpdateUserFlag;trivial.
unfold incl.
intros.
trivial. 

Qed.


Lemma getUsedPagesUpdateUserFlag partition s entry flag table idx : 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
getUsedPages partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} = getUsedPages partition s.
Proof.  
intros Hentry.
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx
       (PE
          {|
          read := read entry;
          write := write entry;
          exec := exec entry;
          present := present entry;
          user := flag;
          pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
unfold getUsedPages. 
f_equal.  
assert (getConfigPages partition s' = 
getConfigPages partition s) as Hinds.
apply getConfigPagesUpdateUserFlag; trivial.
rewrite Hinds. trivial.
assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
apply getMappedPagesUpdateUserFlag; trivial.
rewrite Hmaps;trivial.
Qed.

Lemma partitionDescriptorEntryUpdateUserFlag s table idx entry flag : 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
partitionDescriptorEntry s ->
partitionDescriptorEntry {| currentPartition := currentPartition s;
                    memory := add table idx
                                         (PE
                                             {|
                                             read := read entry;
                                             write := write entry;
                                             exec := exec entry;
                                             present := present entry;
                                             user := flag;
                                             pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hentry Hprentry. 
unfold partitionDescriptorEntry in *.
intros partition Hpart  idxtable Htmp.
rewrite getPartitionsUpdateUserFlag in Hpart.
generalize (Hprentry partition Hpart); clear Hprentry; intros Hprentry.
apply Hprentry in Htmp.
clear Hprentry.
rename Htmp into Hprentry.
destruct Hprentry as (Hidx & Hva & Hpp).
repeat split;trivial.
* clear Hpp.
  unfold isVA in *;cbn in *.

  case_eq ( beqPairs (table, idx) (partition, idxtable) beqPage beqIndex);trivial;intros Hpairs.
  apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidxtable).  subst.
  rewrite Hentry in Hva.
  inversion Hva.
  apply beqPairsFalse in Hpairs.
                assert (lookup  partition idxtable(removeDup table idx (memory s) beqPage beqIndex)
                        beqPage beqIndex = lookup partition idxtable  (memory s) beqPage beqIndex) as Hmemory.
                { apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory. assumption.
* intros.
  destruct Hpp as (page1 & Hpp & Hnotnul). 
  exists page1.
  split;trivial.
  unfold nextEntryIsPP in *;cbn in *.
  destruct(  StateLib.Index.succ idxtable );[ | now contradict Hpp].  

  case_eq ( beqPairs (table, idx) (partition, i) beqPage beqIndex);trivial;intros Hpairs.
  + apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidxtable).  subst.
  rewrite Hentry in Hpp. now contradict Hpp.
  +
  apply beqPairsFalse in Hpairs.
  assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
          beqPage beqIndex = lookup partition i  (memory s) beqPage beqIndex) as Hmemory.
  { apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory. assumption.
   * assumption.
Qed.

Lemma dataStructurePdSh1Sh2asRootUpdateUserFlag idxtable idx table entry flag s:  
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->
dataStructurePdSh1Sh2asRoot idxtable s -> 
dataStructurePdSh1Sh2asRoot idxtable
{|
currentPartition := currentPartition s;
memory := add table idx
            (PE
               {|
               read := read entry;
               write := write entry;
               exec := exec entry;
               present := present entry;
               user := flag;
               pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hentry Hind.
unfold dataStructurePdSh1Sh2asRoot in *.
intros.  
set (entry1 := (PE
                {|
                read := read entry;
                write := write entry;
                exec := exec entry;
                present := present entry;
                user := flag;
                pa := pa entry |}) ) in *.
                
set(s' :=  {| currentPartition := currentPartition s;
            memory := add table idx entry1 (memory s) beqPage beqIndex |}) in *.
assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
apply getPartitionsUpdateUserFlag;trivial.
rewrite HgetPart in H. 
assert (nextEntryIsPP partition idxtable entry0 s' ->
      nextEntryIsPP partition idxtable entry0 s) as Hlookup.
      { unfold s'. intros . unfold entry1 in H4. cbn in H4. 
        unfold nextEntryIsPP in *.
        cbn in *. 
        destruct ( StateLib.Index.succ idxtable);[|now contradict H4].
        case_eq(beqPairs (table, idx) (partition, i) beqPage beqIndex);intros H6.
        rewrite H6 in H4.
        inversion H4.
        rewrite H6 in H4.
        apply beqPairsFalse in H6.
        assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
                        beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
        { apply removeDupIdentity. subst.  intuition. }
        rewrite <- Hmemory. assumption. }
apply Hlookup in H0. 
intros. 
assert (True) as HTrue;trivial.
assert (getIndirection entry0 va level stop s' = Some indirection -> 
getIndirection entry0 va level stop s = Some indirection) as Hindirection.
{ intros. 
  rewrite <- H4. 
  symmetry.
  apply getIndirectionUpdateUserFlag  ;trivial. } 
apply Hindirection in H3.
generalize (Hind partition H entry0  H0 va HTrue level stop H2 indirection idx0 H3);clear Hind; intros Hind.
clear Hindirection HTrue  Hlookup HgetPart.
destruct Hind as [ Hind | Hind].
left. assumption.
right.
destruct Hind as (Hind & Hnotnull). 
split;trivial.
destruct Hind as [(Hlevel & Hind) | (Hlevel & Hind)].
+ left. split. assumption.
  unfold isPE in *. cbn in *.
  case_eq(beqPairs (table, idx)  (indirection, idx0) beqPage beqIndex);intros Hpairs.
  - unfold entry1. trivial.
  - apply beqPairsFalse in Hpairs. subst.
    assert (lookup  indirection idx0 (removeDup table idx (memory s) beqPage beqIndex)
                        beqPage beqIndex = lookup  indirection idx0  (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity. subst.  intuition. }
             rewrite  Hmemory. assumption.
+ right. split; trivial. 
  destruct Hind as [Hvalue | [Hvalue |(Hvalue & Hidxpd)]].
  - left.
    unfold isVE in *.
    cbn.
    case_eq(beqPairs (table, idx)  (indirection, idx0) beqPage beqIndex);intros Hpairs.
    * apply beqPairsTrue in Hpairs. destruct Hpairs as (Htable & Hindx).
      subst. rewrite Hentry in Hvalue. now contradict Hvalue.
    * apply beqPairsFalse in Hpairs.
      assert (lookup  indirection idx0 (removeDup table idx (memory s) beqPage beqIndex)
                        beqPage beqIndex = lookup  indirection idx0  (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity. subst.  intuition. }
             rewrite  Hmemory. assumption.
  - right. left.
    unfold isVA in *.
    cbn.
    case_eq(beqPairs (table, idx)  (indirection, idx0) beqPage beqIndex);intros Hpairs.
    * apply beqPairsTrue in Hpairs. destruct Hpairs as (Htable & Hindx).
      subst. rewrite Hentry in Hvalue. now contradict Hvalue.
    * apply beqPairsFalse in Hpairs.
      assert (lookup  indirection idx0 (removeDup table idx (memory s) beqPage beqIndex)
                        beqPage beqIndex = lookup  indirection idx0  (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity. subst.  intuition. }
             rewrite  Hmemory. assumption.
  - right. right. split;trivial.  unfold isPE in *. cbn in *.
  case_eq(beqPairs (table, idx)  (indirection, idx0) beqPage beqIndex);intros Hpairs.
   * unfold entry1. trivial.
   * apply beqPairsFalse in Hpairs.
    assert (lookup  indirection idx0 (removeDup table idx (memory s) beqPage beqIndex)
                        beqPage beqIndex = lookup  indirection idx0  (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity. subst.  intuition. }
             rewrite  Hmemory. assumption.
Qed.    

Lemma isPPUpdateUserFlag table idx table1 idx1 flag res s (entry : Pentry): 
lookup table1 idx1  (memory s) beqPage beqIndex = Some (PE entry) ->
isPP' table idx res s -> isPP' table idx res
{|
currentPartition := currentPartition s;
memory := add table1 idx1 
      (PE
         {|
         read := read entry;
         write := write entry;
         exec := exec entry;
         present := present entry;
         user := flag;
         pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hlookup HPP.
unfold isPP' in *.
cbn.
case_eq (beqPairs (table1, idx1) (table, idx) beqPage beqIndex);intros Hpairs.
{ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
  subst.
  rewrite Hlookup in HPP. now contradict HPP. }
{ apply beqPairsFalse in Hpairs.
  assert (lookup  table idx  (removeDup table1 idx1 (memory s) beqPage beqIndex)
                beqPage beqIndex = lookup  table idx (memory s) beqPage beqIndex) as Hmemory.
  { apply removeDupIdentity. subst.  intuition. }
  rewrite  Hmemory. assumption. }
Qed.

Lemma nextEntryIsPPUpdateUserFlag table idx table1 idx1 flag res s (entry : Pentry) : 
lookup table1 idx1  (memory s) beqPage beqIndex = Some (PE entry) ->
nextEntryIsPP table idx res s -> nextEntryIsPP table idx res 
{|
currentPartition := currentPartition s;
memory := add table1 idx1 
      (PE
         {|
         read := read entry;
         write := write entry;
         exec := exec entry;
         present := present entry;
         user := flag;
         pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hlookup Hroot.
unfold nextEntryIsPP in *.

destruct (StateLib.Index.succ idx);[|now contradict Hroot].
cbn in *.
 
case_eq (beqPairs (table1, idx1) (table, i) beqPage beqIndex);intros Hpairs.
{ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
  subst.
  rewrite Hlookup in Hroot. now contradict Hroot. }
{ apply beqPairsFalse in Hpairs.
  assert (lookup  table i  (removeDup table1 idx1 (memory s) beqPage beqIndex)
                beqPage beqIndex = lookup  table i (memory s) beqPage beqIndex) as Hmemory.
  { apply removeDupIdentity. subst.  intuition. }
  rewrite  Hmemory. assumption. }
Qed.

Lemma nextEntryIsPPUpdateUserFlag' table idx table1 idx1 flag res s (entry : Pentry) : 
nextEntryIsPP table idx res 
{|
currentPartition := currentPartition s;
memory := add table1 idx1 
      (PE
         {|
         read := read entry;
         write := write entry;
         exec := exec entry;
         present := present entry;
         user := flag;
         pa := pa entry |}) (memory s) beqPage beqIndex |} -> nextEntryIsPP table idx res s .
Proof.
intros Hroot.
unfold nextEntryIsPP in *.
destruct (StateLib.Index.succ idx);[|now contradict Hroot].
cbn in *.
case_eq (beqPairs (table1, idx1) (table, i) beqPage beqIndex);intros Hpairs.
{ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
  subst.
  assert ( beqPairs (table, i) (table, i) beqPage beqIndex = true).
  apply beqPairsTrue. split;trivial.
  rewrite H in Hroot. now contradict Hroot. }
{ apply beqPairsFalse in Hpairs.
  assert( beqPairs (table1, idx1) (table, i)  beqPage beqIndex = false).
  apply beqPairsFalse in Hpairs. assumption.
  rewrite H in Hroot.

  assert (lookup  table i  (removeDup table1 idx1 (memory s) beqPage beqIndex)
                beqPage beqIndex = lookup  table i (memory s) beqPage beqIndex) as Hmemory.
  { apply removeDupIdentity. subst.  intuition. }
  rewrite  Hmemory in Hroot. assumption. }
Qed.

Lemma isPEUpdateUserFlag table idx table1 idx1 s entry flag :   
lookup table1 idx1 (memory s) beqPage beqIndex = Some (PE entry) -> 
isPE table idx s -> 
isPE table idx
{|
currentPartition := currentPartition s;
memory := add table1 idx1
  (PE
     {|
     read := read entry;
     write := write entry;
     exec := exec entry;
     present := present entry;
     user := flag;
     pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hlookup HPE.
unfold isPE in *.
cbn.
case_eq (beqPairs (table1, idx1) (table, idx) beqPage beqIndex);intros Hpairs.
{ trivial. }
{ apply beqPairsFalse in Hpairs.
assert (lookup  table idx  (removeDup table1 idx1 (memory s) beqPage beqIndex)
    beqPage beqIndex = lookup  table idx (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. assumption. }
Qed.

Lemma entryPresentFlagUpdateUserFlag table idx table1 idx1 flag entry s presentflag: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
entryPresentFlag table1 idx1 presentflag s -> 
entryPresentFlag table1 idx1 presentflag
{|
currentPartition := currentPartition s;
memory := add table idx
        (PE
         {|
         read := read entry;
         write := write entry;
         exec := exec entry;
         present := present entry;
         user := flag;
         pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hlookup HPres.
unfold entryPresentFlag in *.
cbn. 
case_eq (beqPairs (table1, idx1) (table, idx) beqPage beqIndex);intros Hpairs.
{ apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
  subst.
  rewrite Hlookup in HPres.
  assert  (beqPairs (table, idx) (table, idx) beqPage beqIndex = true) as Htrue.
  apply beqPairsTrue. split;trivial.
  rewrite Htrue;cbn. assumption. }
  { apply beqPairsFalse in Hpairs.
    assert (lookup  table1 idx1  (removeDup table idx (memory s) beqPage beqIndex)
    beqPage beqIndex = lookup  table1 idx1 (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory.
  assert  (beqPairs (table, idx) (table1, idx1) beqPage beqIndex = false) as Hfalse.
  apply beqPairsFalse; intuition.
  rewrite Hfalse.
  assumption. } 
Qed.


Lemma isVEUpdateUserFlag table1 table2 idx1 idx2 flag entry s : 
lookup table1 idx1 (memory s) beqPage beqIndex =
Some (PE entry) -> 
isVE table2 idx2 s ->
isVE table2 idx2
{|
currentPartition := currentPartition s;
memory := add table1 idx1
(PE
 {|
 read := read entry;
 write := write entry;
 exec := exec entry;
 present := present entry;
 user := flag;
 pa := pa entry |}) (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup Hve.
unfold isVE in *.
cbn in *.
case_eq (beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex ); intros Hpairs.
{  apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
   subst. rewrite Hlookup in Hve. trivial. }
{ apply beqPairsFalse in Hpairs.
  assert (lookup  table2 idx2  (removeDup table1 idx1 (memory s) beqPage beqIndex)
  beqPage beqIndex = lookup  table2 idx2 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory. assumption. }
Qed.

Lemma isVAUpdateUserFlag table1 table2 idx1 idx2 flag entry s : 
lookup table1 idx1 (memory s) beqPage beqIndex =
Some (PE entry) -> 
isVA table2 idx2 s ->
isVA table2 idx2
{|
currentPartition := currentPartition s;
memory := add table1 idx1
(PE
 {|
 read := read entry;
 write := write entry;
 exec := exec entry;
 present := present entry;
 user := flag;
 pa := pa entry |}) (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup Hve.
unfold isVA in *.
cbn in *.
case_eq (beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex ); intros Hpairs.
{  apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
   subst. rewrite Hlookup in Hve. trivial. }
{ apply beqPairsFalse in Hpairs.
  assert (lookup  table2 idx2  (removeDup table1 idx1 (memory s) beqPage beqIndex)
  beqPage beqIndex = lookup  table2 idx2 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory. assumption. }
Qed. 

Lemma isVA'UpdateUserFlag table1 table2 idx1 idx2 flag entry s va: 
lookup table1 idx1 (memory s) beqPage beqIndex =
Some (PE entry) -> 
isVA' table2 idx2 va s ->
isVA' table2 idx2 va
{|
currentPartition := currentPartition s;
memory := add table1 idx1
(PE
 {|
 read := read entry;
 write := write entry;
 exec := exec entry;
 present := present entry;
 user := flag;
 pa := pa entry |}) (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup Hve.
unfold isVA' in *.
cbn in *.
case_eq (beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex ); intros Hpairs.
{  apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
   subst. rewrite Hlookup in Hve. trivial. }
{ apply beqPairsFalse in Hpairs.
  assert (lookup  table2 idx2  (removeDup table1 idx1 (memory s) beqPage beqIndex)
  beqPage beqIndex = lookup  table2 idx2 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory. assumption. }
Qed.

Lemma isVAUserUpdateUserFlag table1 table2 idx1 idx2 flag entry s va: 
lookup table1 idx1 (memory s) beqPage beqIndex =
Some (PE entry) -> 
isVAUser table2 idx2 va s ->
isVAUser table2 idx2 va
{|
currentPartition := currentPartition s;
memory := add table1 idx1
(PE
 {|
 read := read entry;
 write := write entry;
 exec := exec entry;
 present := present entry;
 user := flag;
 pa := pa entry |}) (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup Hve.
unfold isVAUser in *.
cbn in *.
case_eq (beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex ); intros Hpairs.
{  apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
   subst. rewrite Hlookup in Hve. trivial. }
{ apply beqPairsFalse in Hpairs.
  assert (lookup  table2 idx2  (removeDup table1 idx1 (memory s) beqPage beqIndex)
  beqPage beqIndex = lookup  table2 idx2 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory. assumption. }
Qed.

Lemma isEntryVAUpdateUserFlag  table1 idx1 table2 idx2 derived entry flag s : 
lookup table1 idx1 (memory s) beqPage beqIndex =
Some (PE entry) -> 
isEntryVA table2 idx2 derived s -> 
isEntryVA table2 idx2 derived
{|
currentPartition := currentPartition s;
memory := add table1 idx1
    (PE
       {|
       read := read entry;
       write := write entry;
       exec := exec entry;
       present := present entry;
       user := flag;
       pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hlookup Hve.
unfold isEntryVA in *.
cbn in *.
case_eq (beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex ); intros Hpairs.
{  apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
   subst. rewrite Hlookup in Hve. trivial. }
{ apply beqPairsFalse in Hpairs.
  assert (lookup  table2 idx2  (removeDup table1 idx1 (memory s) beqPage beqIndex)
  beqPage beqIndex = lookup  table2 idx2 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory. assumption. }

Qed.
Lemma getIndirectionsNoDupUpdateUserFlag s entry flag table idx : 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
noDupConfigPagesList s -> 
noDupConfigPagesList
{|
currentPartition := currentPartition s;
memory := add table idx
        (PE
           {|
           read := read entry;
           write := write entry;
           exec := exec entry;
           present := present entry;
           user := flag;
           pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hread Hnodup.
unfold noDupConfigPagesList in *.

intros.  
set (s' := {|
 currentPartition := currentPartition s;
 memory := add table idx
             (PE
                {|
                read := read entry;
                write := write entry;
                exec := exec entry;
                present := present entry;
                user := flag;
                pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
                assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
apply getPartitionsUpdateUserFlag;trivial.
assert (getConfigPages partition s' = getConfigPages partition s) as Hind.
apply getConfigPagesUpdateUserFlag ; trivial.
rewrite Hind; trivial.
apply Hnodup;trivial.
rewrite <- HgetPart;trivial.
Qed.

Lemma entryUserFlagUpdateUserFlagSameValue table1 table2 idx1 idx2 flag entry s  :
entryUserFlag table1 idx1 flag s->
 entryUserFlag table1 idx1 flag
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hentry. 
unfold entryUserFlag.
cbn.
case_eq (beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex); intros Hpairs.
 + cbn. trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup table1 idx1 (removeDup table2 idx2  (memory s) beqPage beqIndex) beqPage
    beqIndex = lookup  table1 idx1 (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity. intuition. }
   rewrite Hmemory. 
   intuition.
Qed.

Lemma isEntryPageUpdateUserFlag table1 table2 idx1 idx2 phy entry s :
lookup table2 idx2 (memory s) beqPage beqIndex = Some (PE entry) -> 
isEntryPage table1 idx1 phy s -> 
isEntryPage table1 idx1 phy
{|
currentPartition := currentPartition s;
memory := add table2 idx2
         (PE
               {|
               read := read entry;
               write := write entry;
               exec := exec entry;
               present := present entry;
               user := false;
               pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hlookup Hentry. unfold isEntryPage in *.
cbn.
case_eq (beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex); intros Hpairs.
+ cbn. apply beqPairsTrue in Hpairs. destruct Hpairs. subst. 
  rewrite Hlookup in Hentry. 
  trivial.
+ apply beqPairsFalse in Hpairs.
 assert (lookup table1 idx1 (removeDup table2 idx2  (memory s) beqPage beqIndex) beqPage
  beqIndex = lookup  table1 idx1 (memory s) beqPage beqIndex) as Hmemory.
  { apply removeDupIdentity. intuition. }
 rewrite Hmemory. assumption. 
Qed.

Lemma getAncestorsUpdateUserFlag partition table idx s flag  entry:
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->  
getAncestors partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} =
getAncestors partition s.
Proof.
intros Hentry.
unfold getAncestors in *.
revert partition.
induction (nbPage +1).
simpl; trivial.
simpl.
intros.
unfold StateLib.getParent.
case_eq (StateLib.Index.succ PPRidx);trivial.
intros.
unfold StateLib.readPhysical. 
cbn. 
case_eq (beqPairs (table, idx) (partition, i) beqPage beqIndex); intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry. 
   cbn. trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  partition i (removeDup table idx (memory s) beqPage beqIndex)
            beqPage beqIndex = lookup  partition i   (memory s) beqPage beqIndex) as Hmemory.
    { apply removeDupIdentity. intuition. }
   rewrite Hmemory.
   destruct (lookup partition i (memory s) beqPage beqIndex); trivial.
   destruct v; trivial.
   f_equal.
   apply IHn.
Qed.
Lemma getAccessibleMappedPageUpdateUserFlagDiffrentPartitions pd s va1 entry va2 (table : page) 
partition0 partition :
partitionDescriptorEntry s -> 
(Nat.eqb defaultPage table) = false ->
In partition0 (getPartitions multiplexer s) ->
getTableAddrRoot table PDidx partition0 va2 s -> 
In partition (getPartitions multiplexer s) -> 
StateLib.getPd partition (memory s) = Some pd -> 
partition <> partition0 -> 
disjoint (getConfigPages partition0 s) (getConfigPages partition s) -> 
lookup table (StateLib.getIndexOfAddr va2 fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
getAccessibleMappedPage pd s va1 =
getAccessibleMappedPage pd
{|
currentPartition := currentPartition s;
memory := add table (StateLib.getIndexOfAddr va2 fstLevel)
            (PE
               {|
               read := read entry;
               write := write entry;
               exec := exec entry;
               present := present entry;
               user := false;
               pa := pa entry |}) (memory s) beqPage beqIndex |} va1.
Proof.
intros Hpde (*Hndup *) Htablenotnull Hpart0 Hroot0 (* Hpd0 *)  Hpart
Hpd  (* Hfst *) Hdiff Hdis  Hlookup . 
                 Proof.
                
   unfold getAccessibleMappedPage.
  case_eq ( StateLib.getNbLevel );intros;trivial.
  simpl.
  set(s' := {|
    currentPartition := currentPartition s;
    memory := add table (StateLib.getIndexOfAddr va2 fstLevel)
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
  assert(Hind : getIndirection pd va1 l (nbLevel - 1) s' = 
                getIndirection pd va1 l (nbLevel - 1) s).
  { apply getIndirectionUpdateUserFlag;trivial. }
  rewrite Hind;clear Hind.
  case_eq( getIndirection pd va1 l (nbLevel - 1) s); intros;trivial.
  case_eq(Nat.eqb defaultPage p);intros;trivial.
  unfold s'.
  rewrite readPresentUpdateUserFlag;trivial.
  simpl.
  case_eq( StateLib.readPresent p (StateLib.getIndexOfAddr va1 fstLevel) (memory s) );
  intros;trivial.
  case_eq b;intros;trivial.
  set(memory' := (add table (StateLib.getIndexOfAddr va2 fstLevel)
       (PE
          {|
          read := read entry;
          write := write entry;
          exec := exec entry;
          present := present entry;
          user := false;
          pa := pa entry |}) (memory s) beqPage beqIndex)) in *.
   assert(StateLib.readAccessible p (StateLib.getIndexOfAddr va1 fstLevel) memory'  = 
   StateLib.readAccessible p (StateLib.getIndexOfAddr va1 fstLevel) (memory s)).
   { unfold StateLib.readAccessible.
    cbn.
    assert (table <> p \/ StateLib.getIndexOfAddr va2 fstLevel <> StateLib.getIndexOfAddr va1 fstLevel).
    { left.
    unfold getConfigPages in *.
    unfold disjoint in *.
    simpl in *.
    generalize(Hdis table); clear Hdis;intros Hconfig.
    assert (          ~ (partition = table \/ In table (getConfigPagesAux partition s))).
    {
    apply Hconfig;right.
    unfold getConfigPagesAux.
    case_eq(StateLib.getPd partition0 (memory s));trivial;
    intros * Hpd0.
    case_eq(StateLib.getFstShadow partition0 (memory s) );trivial.
    case_eq(StateLib.getSndShadow partition0 (memory s) );trivial.
    case_eq(StateLib.getConfigTablesLinkedList partition0 (memory s) );trivial.
    intros.
    simpl.
    (* right *)
    apply in_app_iff.
    left.
    assert(getIndirection p0 va2 l nbLevel s = Some table).
    { unfold getTableAddrRoot in *.
      destruct Hroot0 as (_ & HH7).
      rewrite <- nextEntryIsPPgetPd in Hpd0.
      generalize (HH7 p0 Hpd0 );clear HH7; intros HH7.
      destruct HH7 as (nbL & Hnbl & stop & Hstop & Hind).
      assert(stop = nbLevel ).
      { apply getNbLevelEq in Hnbl.
        subst.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl.
        lia.
        assert (0< nbLevel) by apply nbLevelNotZero.
        lia. }
      rewrite <- Hnbl in *.
      inversion H.
      subst.
      rewrite <- H7.
      assumption. }    
    apply getIndirectionInGetIndirections with va2 l nbLevel;trivial.
    simpl.
    assert(0<nbLevel) by apply nbLevelNotZero.
    lia.
    unfold not;intros;subst.
    apply beq_nat_false in Htablenotnull.
    now contradict Htablenotnull.
    symmetry in H.
    apply getNbLevelEq in H.
    subst.
    lia.
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP partition0 PDidx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    left;trivial.
    destruct Hentrypd as (entrypd & Hpp & Hnotnul).
    assert(entrypd = p0).
    apply getPdNextEntryIsPPEq with partition0 s;trivial.
    subst.
    assumption.
    intros.
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP partition0 sh3idx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    do 3 right;left;trivial.
    destruct Hentrypd as (entrypd & Hpp & Hnotnul).
    apply nextEntryIsPPgetConfigList in Hpp.
    subst.
    rewrite H4 in Hpp.
    now contradict Hpp.
    intros.
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP partition0 sh2idx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    do 2 right;left;trivial.
    destruct Hentrypd as (entrypd & Hpp & Hnotnul).
    apply nextEntryIsPPgetSndShadow in Hpp.
    rewrite H4 in Hpp.
    now contradict Hpp.
    intros.
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP partition0 sh1idx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    right;left;trivial.
    destruct Hentrypd as (entrypd & Hpp & Hnotnul).
    apply nextEntryIsPPgetFstShadow in Hpp.
    rewrite H4 in Hpp.
    now contradict Hpp.
        unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP partition0 PDidx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    left;trivial.
    destruct Hentrypd as (entrypd & Hpp & Hnotnul).
    apply nextEntryIsPPgetPd in Hpp.
    rewrite Hpd0 in Hpp.
    now contradict Hpp. }
    clear Hconfig.
    apply Classical_Prop.not_or_and in H4.
    destruct H4 as (_ & Hconfig).
    assert (In p (getConfigPagesAux partition s)).
    unfold getConfigPagesAux.
    rewrite Hpd.
    case_eq(StateLib.getFstShadow partition (memory s) );trivial.
    case_eq(StateLib.getSndShadow partition (memory s) );trivial.
    case_eq(StateLib.getConfigTablesLinkedList partition (memory s) );trivial.
    intros.
    simpl.
    (* ri *)
 apply in_app_iff.
    left.
      unfold getIndirections.
    apply getIndirectionInGetIndirections with va1 l (nbLevel-1);trivial.
    simpl.
    assert(0<nbLevel) by apply nbLevelNotZero.
    lia.
    unfold not;intros;subst.
    apply beq_nat_false in H1.
    now contradict H1.
    symmetry in H.
    apply getNbLevelEq in H.
    subst.
    lia.
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP partition PDidx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    left;trivial.
    destruct Hentrypd as (entrypd & Hpp & Hnotnul).
    assert(entrypd = pd).
    apply getPdNextEntryIsPPEq with partition s;trivial.
    subst.
    assumption.
    intros.
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP partition sh3idx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    do 3 right;left;trivial.
    destruct Hentrypd as (entrypd & Hpp & Hnotnul).
    apply nextEntryIsPPgetConfigList in Hpp.
    rewrite H4 in Hpp.
    now contradict Hpp.
    intros.
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP partition sh2idx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    do 2 right;left;trivial.
    destruct Hentrypd as (entrypd & Hpp & Hnotnul).
    apply nextEntryIsPPgetSndShadow in Hpp.
    rewrite H4 in Hpp.
    now contradict Hpp.
    intros.
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP partition sh1idx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    right;left;trivial.
    destruct Hentrypd as (entrypd & Hpp & Hnotnul).
    apply nextEntryIsPPgetFstShadow in Hpp.
    rewrite H4 in Hpp.
    now contradict Hpp.
    unfold not;intros;subst. now contradict Hconfig. }
    assert( Hpairs : beqPairs (table, StateLib.getIndexOfAddr va2 fstLevel) (p, StateLib.getIndexOfAddr va1 fstLevel) 
    beqPage beqIndex = false).
    apply beqPairsFalse;trivial.
    rewrite Hpairs.
    assert(Hmemory :  lookup p (StateLib.getIndexOfAddr va1 fstLevel)
    (removeDup table (StateLib.getIndexOfAddr va2 fstLevel) (memory s) beqPage beqIndex) beqPage
    beqIndex = lookup p (StateLib.getIndexOfAddr va1 fstLevel) (memory s) beqPage beqIndex ).
    apply removeDupIdentity ; intuition.
    rewrite Hmemory;trivial. }
    rewrite H4.
    destruct(StateLib.readAccessible p (StateLib.getIndexOfAddr va1 fstLevel) (memory s) );trivial.
    unfold memory'.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    Qed.

Lemma isAccessibleMappedPageInParentTrue descParent va phypage ancestor vaInAncestor entry  ptvaInAncestor s ptsh2  
pdAncestor (* sh2 *): 
accessibleChildPageIsAccessibleIntoParent s -> 
parentInPartitionList s -> 
partitionDescriptorEntry s -> 
isAccessibleMappedPageInParent descParent va phypage s = true -> 
nextEntryIsPP descParent PPRidx ancestor s -> 
(forall idx : index,
StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s)
->
(forall idx : index,
StateLib.getIndexOfAddr va fstLevel = idx ->
isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) -> 
isVA' ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s -> 
lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
(* nextEntryIsPP descParent sh2idx sh2 s ->  *)
 In descParent (getPartitions MALInternal.multiplexer s) -> 
 (Nat.eqb defaultPage ptvaInAncestor) = false  -> 
 nextEntryIsPP ancestor PDidx pdAncestor s -> 
 (Nat.eqb defaultPage ptsh2) = false  -> 
isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s = true.
Proof.
intros  Haccess Hparent Hpde  Haccessinparent Hpp1 Hx1 Hx2 Hva1 Hlookup
 (* Hsh2 *) Hparentpart Hnotnull Hpp Hptsh2notnull.
unfold accessibleChildPageIsAccessibleIntoParent in *.
unfold isAccessibleMappedPageInParent in Haccessinparent.
case_eq(StateLib.getSndShadow descParent (memory s)); [intros sh2 Hsh2 | intros Hsh2];
rewrite Hsh2 in *; try now contradict Haccessinparent.
assert(Hva : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
{ unfold getVirtualAddressSh2.
  destruct Hx2 with (StateLib.getIndexOfAddr va fstLevel)
  as (Hpe2 & Hroot2);trivial.
  clear Hx2.
  unfold getTableAddrRoot in Hroot2.
  destruct Hroot2 as (_ & Htableroot).
  assert(Hppsh2 : nextEntryIsPP descParent sh2idx sh2 s ).
  apply nextEntryIsPPgetSndShadow;trivial.
  apply Htableroot in Hppsh2.
  destruct Hppsh2 as (nbL & HnbL & stop & Hstop & Hind ).
  rewrite <- HnbL.
  subst.
  assert(Hnewind :getIndirection sh2 va nbL (nbLevel - 1) s = Some ptsh2).
  apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
  lia.
  apply getNbLevelEq in HnbL.
  subst.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel);
  intros;simpl;trivial.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia.
  rewrite Hnewind.
  rewrite Hptsh2notnull.
  unfold StateLib.readVirtual.
  unfold isVA' in *.
  destruct( lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex );
  try now contradict Hva1.
  destruct v;try now contradict Hva1.
  f_equal;trivial. }
rewrite Hva in *.
rewrite nextEntryIsPPgetParent in * .
rewrite Hpp1 in Haccessinparent.
rewrite nextEntryIsPPgetPd in *.
rewrite Hpp in Haccessinparent.
case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor);
[intros accessiblepage Haccessiblepage |intros Haccessiblepage |intros Haccessiblepage]; rewrite Haccessiblepage in *;
try now contradict Haccessiblepage.
apply Haccess with pdAncestor;trivial.
unfold parentInPartitionList in *.
apply Hparent with descParent;trivial.
clear Haccess.
rewrite nextEntryIsPPgetParent in *;trivial.
unfold getAccessibleMappedPage in *.
destruct Hx1 with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
as (Hpe1 & Hroot1);trivial.
clear Hx1.
unfold getTableAddrRoot in Hroot1.
destruct Hroot1 as (_ & Htableroot).
rewrite <- nextEntryIsPPgetPd in *.
apply Htableroot in Hpp.
destruct Hpp as (nbL & HnbL & stop & Hstop & Hind ).
rewrite <- HnbL in *.
subst.
assert(Hnewind :getIndirection  pdAncestor vaInAncestor nbL (nbLevel - 1) s  = 
Some ptvaInAncestor).
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
lia.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel);
intros;simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
rewrite Hnewind in *.
clear Htableroot.
rewrite Hnotnull in *.
destruct(StateLib.readPresent ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
  (memory s));
try now contradict Haccessiblepage.
destruct b;try now contradict Haccessiblepage.
destruct(StateLib.readAccessible ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
  (memory s));try now contradict Haccessiblepage.
destruct b;try now contradict Haccessiblepage.
unfold StateLib.readPhyEntry in *.
rewrite Hlookup in *.
trivial.
Qed.

Lemma accessibleVAIsNotPartitionDescriptorUpdateUserFlag level (table : page)  s partition0  
pd0 va2 entry:
Some level = StateLib.getNbLevel -> 
partitionDescriptorEntry s -> 
noDupConfigPagesList s -> 
(Nat.eqb defaultPage table) = false ->
lookup table (StateLib.getIndexOfAddr va2 fstLevel) 
    (memory s) beqPage beqIndex = Some (PE entry) -> 
In partition0 (getPartitions multiplexer s) ->
getTableAddrRoot table PDidx partition0 va2 s -> 
StateLib.getPd partition0 (memory s) = Some pd0 -> 
getAccessibleMappedPage pd0 s va2  = SomePage (pa entry) -> 
accessibleVAIsNotPartitionDescriptor s -> 
accessibleVAIsNotPartitionDescriptor
  {|
  currentPartition := currentPartition s;
  memory := add table (StateLib.getIndexOfAddr va2 fstLevel)
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
set(s' :=  {|
  currentPartition := currentPartition s;
  memory := add table (StateLib.getIndexOfAddr va2 fstLevel)
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} ) in *.
intros Hlevel Hpde Hnodup Htablenotnull Hentry Htableroot Hpart1 Hpd1 Haccess1 Hispart1.
unfold accessibleVAIsNotPartitionDescriptor in *.
intros partition va1 pd sh1 page .
intros.


assert (Hpd : StateLib.getPd partition (memory s') = 
              StateLib.getPd partition (memory s) ).
apply getPdUpdateUserFlag;trivial.
rewrite Hpd in *;clear Hpd.
assert (StateLib.getFstShadow partition (memory s') = 
        StateLib.getFstShadow partition (memory s)) as Hsh1.
apply getFstShadowUpdateUserFlag;trivial.
rewrite Hsh1 in *;clear Hsh1.
assert(getPartitions multiplexer s = 
        getPartitions multiplexer s').
symmetry.
apply getPartitionsUpdateUserFlag;trivial.
rewrite H3 in *;clear H3.
assert (getPDFlag sh1 va1 s' = getPDFlag sh1 va1 s).
{ unfold getPDFlag.
  destruct ( StateLib.getNbLevel); trivial.
  unfold s'.
  rewrite getIndirectionUpdateUserFlag;trivial.
  destruct (getIndirection sh1 va1 l (nbLevel - 1) s );trivial.
  destruct (Nat.eqb p defaultPage);trivial.
  simpl.
  rewrite readPDflagUpdateUserFlag;trivial. }
rewrite H3;clear H3.
unfold s' in *.
assert(Hisaccessible :  getAccessibleMappedPage pd
                  {|
                  currentPartition := currentPartition s;
                  memory := add table (StateLib.getIndexOfAddr va2 fstLevel)
                              (PE
                                 {|
                                 read := read entry;
                                 write := write entry;
                                 exec := exec entry;
                                 present := present entry;
                                 user := false;
                                 pa := pa entry |}) (memory s) beqPage beqIndex |} va1 = 
                                 getAccessibleMappedPage pd s va1).
{
unfold getAccessibleMappedPage in H2.
unfold getAccessibleMappedPage.

simpl in *.
rewrite <- Hlevel in *.
rewrite getIndirectionUpdateUserFlag in *;trivial.
case_eq (getIndirection pd va1 level (nbLevel - 1) s );intros * Hgetind;
rewrite Hgetind in *;trivial.
destruct(Nat.eqb defaultPage p);trivial.
rewrite readPresentUpdateUserFlag in *;trivial.
destruct (StateLib.readPresent p (StateLib.getIndexOfAddr va1 fstLevel) (memory s) );
trivial.
destruct b;trivial.
case_eq(StateLib.readAccessible p (StateLib.getIndexOfAddr va1 fstLevel)
                    (add table (StateLib.getIndexOfAddr va2 fstLevel)
                       (PE
                          {|
                          read := read entry;
                          write := write entry;
                          exec := exec entry;
                          present := present entry;
                          user := false;
                          pa := pa entry |}) (memory s) beqPage beqIndex));intros * Hisaccess;
rewrite Hisaccess in *.
+ destruct b;try now contradict H2.
rewrite readPhyEntryUpdateUserFlag in *;trivial.
rewrite H2.
unfold StateLib.readAccessible in *.
simpl in *. 
case_eq( beqPairs (table, StateLib.getIndexOfAddr va2 fstLevel)
                  (p, StateLib.getIndexOfAddr va1 fstLevel) beqPage beqIndex);intros * Hpairs.
 - rewrite Hpairs in Hisaccess.
  simpl in *.
  now contradict Hisaccess.
 - rewrite Hpairs in Hisaccess.
   apply beqPairsFalse in Hpairs.
   assert(Hremove : lookup p (StateLib.getIndexOfAddr va1 fstLevel)
                (removeDup table (StateLib.getIndexOfAddr va2 fstLevel) (memory s) beqPage beqIndex)
                beqPage beqIndex =
          lookup p (StateLib.getIndexOfAddr va1 fstLevel) (memory s) beqPage beqIndex).
          apply removeDupIdentity;intuition.
    rewrite Hremove in *.
    rewrite Hisaccess;trivial.
 + now contradict H2. }
 rewrite Hisaccessible in *.
rewrite getPartitionsUpdateUserFlag in *;trivial.
apply Hispart1 with partition pd page ;trivial.

Qed.


Lemma getVirtualAddressSh2UpdateUserFlag p va entry table vatable s flag:
lookup table (StateLib.getIndexOfAddr vatable fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
getVirtualAddressSh2 p s va =
getVirtualAddressSh2 p
    {|
    currentPartition := currentPartition s;
    memory := add table (StateLib.getIndexOfAddr vatable fstLevel)
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := flag;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} va.
Proof.
unfold getVirtualAddressSh2.
intros Hentry.
case_eq(StateLib.getNbLevel);trivial.
intros nbL HnbL.
rewrite getIndirectionUpdateUserFlag;trivial.
case_eq(getIndirection p va nbL (nbLevel - 1) s);trivial.
intros tbl Hget.
simpl.
rewrite readVirtualUpdateUserFlag;trivial.
Qed.

 Lemma getAccessibleMappedPageUpdateUserFlagDiffrentVaddrs pdAncestor ptvaInAncestor
  vaInAncestor vaInParent flag entry level ancestor s:
  StateLib.checkVAddrsEqualityWOOffset nbLevel vaInAncestor vaInParent level = false -> 
  noDupConfigPagesList s-> 
  In ancestor (getPartitions multiplexer s) -> 
  partitionDescriptorEntry s -> 
    StateLib.getPd ancestor (memory s) = Some pdAncestor -> 
  Some level = StateLib.getNbLevel -> 
  lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) (memory s) beqPage beqIndex =
Some (PE entry) -> 
(Nat.eqb defaultPage ptvaInAncestor) = false -> 
getIndirection pdAncestor vaInAncestor level (level + 1) s = Some ptvaInAncestor -> 
  getAccessibleMappedPage pdAncestor
  {|
  currentPartition := currentPartition s;
  memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := flag;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} vaInParent =
getAccessibleMappedPage pdAncestor s vaInParent.
Proof.
intros Hvas Hnodupconfig Hancespart Hpde HpdAncestor Hlevel Hlookup Hdefault Hind. 
unfold getAccessibleMappedPage.
simpl in *.
rewrite <- Hlevel in *.
rewrite getIndirectionUpdateUserFlag in *;trivial.
case_eq (getIndirection pdAncestor vaInParent level (nbLevel - 1) s ); [intros tbl Hgetind |];
trivial.
case_eq(Nat.eqb defaultPage tbl);trivial.
intros Hnotnull.
rewrite readPresentUpdateUserFlag ;trivial.
destruct (StateLib.readPresent tbl (StateLib.getIndexOfAddr vaInParent fstLevel) 
(memory s) );
trivial.
destruct b;trivial.
assert( ptvaInAncestor  <> tbl \/(StateLib.getIndexOfAddr vaInAncestor  fstLevel) <>
 (StateLib.getIndexOfAddr vaInParent fstLevel)  ).
{ assert(pdAncestor <> defaultPage).
  { unfold partitionDescriptorEntry in *.
    assert(Hexist : (exists entry : page, nextEntryIsPP ancestor PDidx entry s /\ 
     entry <> defaultPage)).
    apply Hpde;trivial.
    left;trivial.
    destruct Hexist as (entrypdAncestor & Hppancestor & Hpdancesnotnull).
    assert(entrypdAncestor = pdAncestor).
    apply getPdNextEntryIsPPEq with ancestor s ;trivial.
    subst.
    trivial. }
  assert( NoDup (getIndirections pdAncestor s)).
  { apply noDupConfigPagesListNoDupGetIndirections with ancestor PDidx;trivial.
     unfold noDupConfigPagesList in *.
    apply Hnodupconfig ;trivial.
    left;trivial.
    rewrite nextEntryIsPPgetPd in *;trivial. }
  apply pageTablesOrIndicesAreDifferent with pdAncestor pdAncestor level nbLevel
    s;trivial.
  left;split;trivial.
  apply getNbLevelEq in Hlevel.
  subst;trivial.
  apply beq_nat_false in Hdefault.
  unfold not; intros Htmp;subst;now contradict Hdefault.
  apply beq_nat_false in Hnotnull.
  unfold not; intros Htmp;subst;now contradict Hnotnull.
  assert(nbLevel = level+1).
  apply getNbLevelEq in Hlevel.
  subst;trivial.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel);intros .
  simpl.
  lia.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia.
  rewrite H1;assumption.
  apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
  apply getNbLevelEq in Hlevel.
  subst.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel);intros .
  simpl.
  lia.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia.
  apply getNbLevelEq in Hlevel.
  subst.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel);intros .
  simpl.
  lia.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia. }  
assert(Htrue : StateLib.readAccessible tbl (StateLib.getIndexOfAddr vaInParent fstLevel)
    (add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
       (PE
          {|
          read := read entry;
          write := write entry;
          exec := exec entry;
          present := present entry;
          user := flag;
          pa := pa entry |}) (memory s) beqPage beqIndex) = 
          StateLib.readAccessible tbl (StateLib.getIndexOfAddr vaInParent fstLevel) 
          (memory s)).
apply readAccessibleUpdateUserFlag.
intuition.
rewrite Htrue.
rewrite readPhyEntryUpdateUserFlag;trivial. 
Qed.

Lemma accessibleChildPageIsAccessibleIntoParentUpdateUserFlagFlase 
s level ancestor pdAncestor ptvaInAncestor vaInAncestor entry
vaInDescParent ptsh2 descParent pt:
isChild s-> 
configTablesAreDifferent s ->
partitionsIsolation s -> 
parentInPartitionList s -> 
 partitionDescriptorEntry s ->
noDupMappedPagesList s -> 
noDupConfigPagesList s -> 
In descParent (getPartitions multiplexer s) -> 
(forall idx : index,
     StateLib.getIndexOfAddr vaInDescParent fstLevel = idx ->
     isPE pt idx s /\ getTableAddrRoot pt PDidx descParent vaInDescParent s) -> 
nextEntryIsPP descParent PPRidx ancestor s -> 
entryPresentFlag pt (StateLib.getIndexOfAddr vaInDescParent fstLevel) true s -> 
entryUserFlag pt (StateLib.getIndexOfAddr vaInDescParent fstLevel) false s -> 
isEntryPage pt (StateLib.getIndexOfAddr vaInDescParent fstLevel) (pa entry) s -> 
 (forall idx : index,
      StateLib.getIndexOfAddr vaInDescParent fstLevel = idx ->
      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent vaInDescParent s )-> 
isVA' ptsh2 (StateLib.getIndexOfAddr vaInDescParent fstLevel) vaInAncestor s -> 
(Nat.eqb defaultPage pt) = false ->

Some level = StateLib.getNbLevel -> 
lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
(memory s) beqPage beqIndex = Some (PE entry) -> 
nextEntryIsPP ancestor PDidx pdAncestor s ->
(forall idx : index,
 StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
 isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) ->
(Nat.eqb defaultPage ptvaInAncestor) = false ->
In ancestor (getPartitions multiplexer s) -> 
accessibleChildPageIsAccessibleIntoParent s -> 
accessibleChildPageIsAccessibleIntoParent
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
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hchildren Hdisjointconfig Hisoparts Hparentispart Hpde Hnodup Hnodupconfig HdescParentpart Hgetpt Hppdesc Hpresent Huser 
Hentrypage Hgetptsh2 HvaInAncestor Hptnotnull. 
intros Hlevel Hlookup Hpp Hget Hdefault Hispart1 Haccess.
unfold accessibleChildPageIsAccessibleIntoParent in *.
simpl.
intros partition va pd accessiblePage.
intros Hparts Hpd Haccessinpart.
rewrite getPartitionsUpdateUserFlag in *;trivial.
rewrite getPdUpdateUserFlag in *;trivial.
assert(Hisaccessible :  getAccessibleMappedPage pd
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
                                 pa := pa entry |}) (memory s) beqPage beqIndex |} va = 
                                 getAccessibleMappedPage pd s va).
{
unfold getAccessibleMappedPage in Haccessinpart.
unfold getAccessibleMappedPage.
simpl in *.
rewrite <- Hlevel in *.
rewrite getIndirectionUpdateUserFlag in *;trivial.
case_eq (getIndirection pd va level (nbLevel - 1) s );intros * Hgetind;
rewrite Hgetind in *;trivial.
destruct(Nat.eqb defaultPage p);trivial.
rewrite readPresentUpdateUserFlag in *;trivial.
destruct (StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) );
trivial.
destruct b;trivial.
case_eq(StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel)
                    (add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                       (PE
                          {|
                          read := read entry;
                          write := write entry;
                          exec := exec entry;
                          present := present entry;
                          user := false;
                          pa := pa entry |}) (memory s) beqPage beqIndex));intros * Hisaccess;
rewrite Hisaccess in *.
+ destruct b;try now contradict Haccessinpart.
rewrite readPhyEntryUpdateUserFlag in *;trivial.
rewrite Haccessinpart.
unfold StateLib.readAccessible in *.
simpl in *. 
case_eq( beqPairs (ptvaInAncestor, StateLib.getIndexOfAddr vaInAncestor fstLevel)
                  (p, StateLib.getIndexOfAddr va fstLevel) beqPage beqIndex);intros * Hpairs.
 - rewrite Hpairs in Hisaccess.
  simpl in *.
  now contradict Hisaccess.
 - rewrite Hpairs in Hisaccess.
   apply beqPairsFalse in Hpairs.
   assert(Hremove : lookup p (StateLib.getIndexOfAddr va fstLevel)
                (removeDup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
                   (memory s) beqPage beqIndex) beqPage beqIndex =
          lookup p (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex).
          apply removeDupIdentity;intuition.
    rewrite Hremove in *.
    rewrite Hisaccess;trivial.
+ now contradict Haccessinpart. }
rewrite Hisaccessible in *.
assert(Hgoal : isAccessibleMappedPageInParent partition va accessiblePage s = true).
{ apply Haccess with pd;trivial. }
clear Hisaccessible.
clear Haccess.
unfold isAccessibleMappedPageInParent in *.
simpl in *.
rewrite getSndShadowUpdateUserFlag;trivial.
case_eq(StateLib.getSndShadow partition (memory s)); [intros sh2 Hsh2 | intros Hsh2];
rewrite Hsh2 in *;
try now contradict Hgoal.
rewrite <- getVirtualAddressSh2UpdateUserFlag;trivial.
rewrite getParentUpdateUserFlag;trivial.
case_eq(StateLib.getVirtualAddressSh2 sh2 s va); [intros vaInParent HvaInparent | intros HvaInparent]; 
rewrite HvaInparent in *;try now contradict Hgoal.
case_eq(StateLib.getParent partition (memory s));trivial;
[intros parent Hparent | intros Hparent];rewrite Hparent in *;  try now contradict Hgoal.
rewrite getPdUpdateUserFlag;trivial.
case_eq(StateLib.getPd parent (memory s));[intros pdParent Hpdparent| intros Hpdparent];
 rewrite Hpdparent in *;
try now contradict Hgoal.
case_eq( getAccessibleMappedPage pdParent s vaInParent ); 
[intros phypage HvaInparentIsAcces|intros HvaInparentIsAcces |intros HvaInparentIsAcces] ; rewrite HvaInparentIsAcces in *;
try now contradict Hgoal.
apply beq_nat_true in Hgoal.
rewrite Hgoal in *.
assert(Hparteq : parent = ancestor \/ parent <> ancestor).
{ destruct ancestor as (ancestor & Hi1); 
  destruct parent as (parent & Hi2).
  assert(Hor : parent = ancestor \/ parent <> ancestor) by lia.
  destruct Hor.
  subst.
  left;f_equal;apply proof_irrelevance; trivial.
  right.
  unfold not.
  intros Hor.
  inversion Hor.
  lia. }
destruct Hparteq as [Hparteq| Hparteq].
+ subst.
  assert(pdParent = pdAncestor).
  rewrite getPdNextEntryIsPPEq with ancestor pdAncestor pdParent s ;trivial.
  subst.
  destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
  as (Hpe & Hgetptancestor);
  trivial.
  unfold getTableAddrRoot in Hgetptancestor.
  destruct Hgetptancestor as (_ & Hgetptancestor).
  apply Hgetptancestor in Hpp.
  clear Hgetptancestor.
  destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
  assert(Hvas : StateLib.checkVAddrsEqualityWOOffset nbLevel vaInAncestor vaInParent level = true \/ 
                StateLib.checkVAddrsEqualityWOOffset nbLevel vaInAncestor vaInParent level = false). 
  { destruct ( StateLib.checkVAddrsEqualityWOOffset nbLevel vaInAncestor vaInParent level);intuition. }
  destruct Hvas as  [Hvaseq | Hvasnoteq];subst.
  - assert(Hlastidx : (StateLib.getIndexOfAddr vaInAncestor fstLevel) = (StateLib.getIndexOfAddr vaInParent fstLevel)).
    { apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level; trivial.
      unfold fstLevel.
      unfold CLevel.
      case_eq ( lt_dec 0 nbLevel );intros.
      simpl.
      lia.
      assert(0<nbLevel) by apply nbLevelNotZero.
      lia.
      destruct level;simpl; lia. }
      assert(phypage = (pa entry)).
    { unfold getAccessibleMappedPage in HvaInparentIsAcces.
    rewrite <- HnbL in *; try now contradict HvaInparentIsAcces.
    assert(getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s =
          getIndirection pdAncestor vaInParent nbL (nbLevel - 1) s );trivial.
    { apply getIndirectionEq;trivial.
      destruct nbL;simpl; lia.
      inversion Hlevel.
      subst;trivial. }
    rewrite <- H in *.
    assert(Hind2 : getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s = Some ptvaInAncestor).
    apply getIndirectionStopLevelGT2 with (nbL +1);trivial;try lia.
    apply getNbLevelEq in HnbL.
    subst.
    unfold CLevel.
    case_eq((lt_dec (nbLevel - 1) nbLevel));intros;simpl;trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    lia.
    rewrite Hind2 in *.
    rewrite Hdefault in *.
    rewrite <- Hlastidx in *.
    unfold StateLib.readPresent in *.
    rewrite Hlookup in *.
    case_eq(present entry);intros * Hpres; rewrite Hpres in *; try now contradict
    HvaInparentIsAcces.
    case_eq(StateLib.readAccessible ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                         (memory s)); intros * Haccess; rewrite Haccess in *; try now contradict 
                         HvaInparentIsAcces.
    destruct b;try now contradict HvaInparentIsAcces.
    unfold StateLib.readPhyEntry in *.
    rewrite Hlookup in *.
    inversion HvaInparentIsAcces;trivial. }
    subst.
    destruct Hgetpt with (StateLib.getIndexOfAddr vaInDescParent fstLevel)
    as (Hvedesc & Hgetdesc) ;
    trivial. clear Hgetpt Hget.
    unfold getTableAddrRoot in Hgetdesc.
    destruct Hgetdesc as (_ & Hgetdesc).
    assert(Hexist :(exists entry : page, nextEntryIsPP  descParent PDidx  entry s /\
      entry <> defaultPage)).
    { unfold partitionDescriptorEntry in *.
      apply Hpde;trivial.
      left;trivial. }
    destruct Hexist as (pdDesc & HpdDesc & Hpddescnotnul).
    destruct Hgetdesc with pdDesc as (nbL1 & HnbL1 & stop1 & Hstop1 & Hinddesc);trivial.
    clear Hgetdesc.
    assert(Heqchildren : descParent = partition \/ descParent <> partition).
    { destruct descParent as (descParent & Hi1); 
      destruct partition as (partition & Hi2).
      assert(Hor : descParent = partition \/ descParent <> partition) by lia.
      destruct Hor.
      subst.
      left;f_equal;apply proof_irrelevance; trivial.
      right.
      unfold not.
      intros Hor.
      inversion Hor.
      lia. }
    destruct Heqchildren as [Heqchildren| Heqchildren].
    * (** In this case we have a contradiction because the same physical 
    page phypage is accessible and not accessible at the same time **)
      subst. 
      assert(pdDesc = pd).
       { rewrite getPdNextEntryIsPPEq with partition pdDesc pd s;trivial. }
      subst. 
      (** vaInDescParent = va : because the same phypage is mapped once into 
      the same partition**)
      unfold getAccessibleMappedPage in Haccessinpart.
      rewrite <- HnbL1 in *.
      assert(Hinddesc1 : getIndirection pd vaInDescParent nbL1 (nbLevel -1) s = 
      Some pt).
      apply getIndirectionStopLevelGT2 with (nbL1 +1);trivial;try lia.
      apply getNbLevelEq in HnbL1.
      subst.
      unfold CLevel.
      case_eq((lt_dec (nbLevel - 1) nbLevel));intros;simpl;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      lia.
      clear Hinddesc.
      case_eq(getIndirection pd va nbL1 (nbLevel - 1) s ); intros * Hindpart;
      rewrite Hindpart in *; try now contradict Haccessinpart.
      case_eq (Nat.eqb defaultPage p); intros * Hnotnul; rewrite Hnotnul in *; 
      try now contradict Haccessinpart.
      case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) )
      ;intros * Hpres;rewrite Hpres in *; try now contradict Haccessinpart.
      case_eq b;intros * Hispres; rewrite Hispres in *;try now contradict Haccessinpart.
      case_eq(StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel) (memory s));
      intros * HFalse ;rewrite HFalse in *;try now contradict Haccessinpart.
      case_eq b0;intros * HisFalse ; rewrite HisFalse in *; try now contradict Haccessinpart.
      subst.
   
      (* assert(vaInDescParent = va).
      {   apply eqMappedPagesEqVaddrs with accessiblePage pd s. *)
         assert(Heqaux : getMappedPage pd s vaInDescParent = SomePage accessiblePage). 
          { unfold getMappedPage.
            rewrite <- HnbL1.
            rewrite Hinddesc1.
            rewrite Hptnotnull.
            unfold entryPresentFlag in *.
            unfold StateLib.readPresent.
            destruct (lookup pt (StateLib.getIndexOfAddr vaInDescParent fstLevel) 
            (memory s) beqPage beqIndex); try now contradict  Hpresent.
            destruct v;try now contradict Hpresent.
            subst.
            rewrite <- Hpresent;trivial.
            unfold isEntryPage, StateLib.readPhyEntry in *.
            destruct (lookup pt (StateLib.getIndexOfAddr vaInDescParent fstLevel)
             (memory s) beqPage beqIndex); try now contradict  Hentrypage.
            destruct v;try now contradict Hentrypage.
            subst.
            f_equal.
            destruct accessiblePage;
            destruct (pa p1);
            destruct (pa entry); simpl in *;subst;trivial.
            inversion Hentrypage.
            subst.
            f_equal;apply proof_irrelevance. }
(*         + apply AllVAddrAll;trivial. *)
         assert(Heqaux1 : getMappedPage pd s va = SomePage accessiblePage ). 
          { unfold getMappedPage.
            rewrite <- HnbL1.
            rewrite Hindpart.
            rewrite Hnotnul.
            rewrite Hpres.
            assumption. }
           inversion Hlevel;subst;trivial.
         inversion HnbL;subst;trivial.

       assert(Hor : StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInDescParent nbL1 = false \/
                    StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInDescParent nbL1 = true).
       { destruct  (StateLib.checkVAddrsEqualityWOOffset nbLevel va vaInDescParent nbL1).
          right;trivial.
          left;trivial. }
       destruct Hor as [Hor | Hor].
       { assert(accessiblePage <> accessiblePage).
         apply twoMappedPagesAreDifferent with  va vaInDescParent pd nbL1 s;trivial.
         unfold noDupMappedPagesList in *.  
         apply Hnodup in Hparts. 
         unfold getMappedPages in Hparts.
          rewrite nextEntryIsPPgetPd in *.
          rewrite Hpd in *.
         unfold getMappedPagesAux in *.
         unfold getMappedPagesOption in *;trivial.
         symmetry;trivial.
         now contradict H.  }
           
       assert(getIndirection pd vaInDescParent nbL1 (nbLevel - 1) s =
        getIndirection pd va nbL1 (nbLevel - 1) s).
        apply getIndirectionEq;trivial.
        apply getNbLevelLt;trivial. 
        
         symmetry;trivial.
         rewrite <- Hor;apply checkVAddrsEqualityWOOffsetPermut.
      unfold noDupConfigPagesList in *. 
      subst. trivial.
      rewrite H in *.
      rewrite Hindpart in Hinddesc1.
      inversion Hinddesc1.
      subst.
      unfold entryUserFlag, StateLib.readAccessible  in *.
      assert(Haux1 : (StateLib.getIndexOfAddr vaInDescParent fstLevel) =
      (StateLib.getIndexOfAddr va fstLevel)).
      symmetry.
      apply checkVAddrsEqualityWOOffsetTrue' with nbLevel nbL1;trivial.
      apply fstLevelLe;trivial.
      apply getNbLevelLt;symmetry;trivial.
      rewrite Haux1 in *.
      destruct (lookup pt (StateLib.getIndexOfAddr va
      fstLevel) (memory s) beqPage beqIndex ); try now contradict Huser.
      destruct v;try now contradict Huser.
      inversion HFalse.
      destruct ( user p);subst.
      now contradict Huser.
      now contradict H1.
    * (**  In this case we have a contradiction because the same physical 
           page phypage is mapped into two different children *)  
      assert(In (pa entry) (getMappedPages descParent s)).
      subst.
      apply inGetMappedPagesGetIndirection with  vaInDescParent pdDesc 
      pt nbL1  ;trivial.
      assert(In accessiblePage (getMappedPages partition s)).
      apply accessibleMappedPagesInMappedPages.
      unfold getAccessibleMappedPages.
      rewrite Hpd.
      unfold getAccessibleMappedPagesAux.
      apply filterOptionInIff.
      unfold getAccessibleMappedPagesOption.
      apply in_map_iff.
      assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
      StateLib.checkVAddrsEqualityWOOffset nbLevel va va1 ( CLevel (nbLevel -1) ) = true )
      by apply AllVAddrWithOffset0.
      destruct Heqvars as (va1 & Hva1 & Hva11).  
      exists va1.
      split;trivial.
      rewrite <- Haccessinpart;trivial.
      apply getAccessibleMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
      apply getNbLevelEqOption.
      rewrite <- Hva11;apply checkVAddrsEqualityWOOffsetPermut.
      move Hisoparts at bottom.
      unfold partitionsIsolation in *.
      assert(In partition (getChildren ancestor s)).
      unfold isChild in *.
      apply Hchildren;trivial.      
      assert(In descParent (getChildren ancestor s)) .
      unfold isChild in *.
      apply Hchildren;trivial.
      apply nextEntryIsPPgetParent;trivial.
      assert( disjoint (getUsedPages partition s) (getUsedPages  descParent s)).
      apply Hisoparts with ancestor;trivial.
      intuition.
      apply disjointUsedPagesDisjointMappedPages in H3.
      unfold disjoint in *.
      assert(~ In accessiblePage (getMappedPages descParent s)).
      apply H3.
      assumption.
      assert(In  accessiblePage (getMappedPages descParent s)).
      move Hgoal at bottom.
      destruct accessiblePage; destruct (pa entry).
      simpl in *.
      subst.
      assert(Hp = Hp0) by apply proof_irrelevance.
      subst.
      trivial.
      now contradict H4.
  - (** The same partition but with diffrent virtual adresses **)
    assert(vaInAncestor <>vaInParent  ).
    apply  checkVAddrsEqualityWOOffsetEqFalse with  level level;trivial.
    symmetry;trivial.
    assert(getAccessibleMappedPage pdAncestor
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
                   pa := pa entry |}) (memory s) beqPage beqIndex |} vaInParent = 
          getAccessibleMappedPage pdAncestor s vaInParent).
    apply getAccessibleMappedPageUpdateUserFlagDiffrentVaddrs with level ancestor;trivial.
    rewrite <- HnbL in Hlevel.
    inversion Hlevel.
    subst.
    trivial.
    rewrite H0.
    rewrite HvaInparentIsAcces.
    apply NPeano.Nat.eqb_eq;trivial.
 (** Keep me please ! **)
+ (** Diffrent partitions *)
  rewrite <- getAccessibleMappedPageUpdateUserFlagDiffrentPartitions with
  pdParent s vaInParent entry vaInAncestor ptvaInAncestor ancestor
  parent;trivial. 
  rewrite HvaInparentIsAcces;trivial.
  apply PeanoNat.Nat.eqb_eq;trivial.
  destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
  ;trivial.
  unfold parentInPartitionList in *.
  apply Hparentispart with partition;trivial.
  rewrite nextEntryIsPPgetParent in *;trivial.  
  unfold configTablesAreDifferent in *.
  apply Hdisjointconfig;trivial.
  unfold parentInPartitionList in Hparentispart.
  apply Hparentispart with partition;trivial.
  rewrite nextEntryIsPPgetParent in *;trivial.
  unfold not;intros Hfalse.
  subst.
  now contradict Hparteq.
Qed.
Lemma accessibleChildPageIsAccessibleIntoParentUpdate (ptSh1Child ptSh1ChildFromSh1: page)  shadow1 entry  curpart  currentPD level s :
isChild s -> 
physicalPageNotDerived s -> 
configTablesAreDifferent s ->
noDupConfigPagesList s ->
noDupMappedPagesList s ->
partitionDescriptorEntry s ->
parentInPartitionList s -> 
Some level = StateLib.getNbLevel ->  
(Nat.eqb defaultPage ptSh1Child) = false -> 
lookup ptSh1Child (StateLib.getIndexOfAddr shadow1 fstLevel) (memory s) beqPage beqIndex =
Some (PE entry) ->
StateLib.getPd curpart (memory s) = Some currentPD -> 
In curpart (getPartitions multiplexer s) ->
( forall idx : index,
      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
      isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx curpart shadow1 s
) -> 
entryPresentFlag ptSh1Child (StateLib.getIndexOfAddr shadow1 fstLevel) true s -> 
(forall idx : index,
      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
      isVE ptSh1ChildFromSh1 idx s /\
      getTableAddrRoot ptSh1ChildFromSh1 sh1idx curpart shadow1 s )-> 
(exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 (StateLib.getIndexOfAddr shadow1 fstLevel) va s /\
        beqVAddr defaultVAddr va = true )-> 
(Nat.eqb defaultPage ptSh1ChildFromSh1) = false -> 
accessibleChildPageIsAccessibleIntoParent s -> 
accessibleChildPageIsAccessibleIntoParent
  {|
  currentPartition := currentPartition s;
  memory := add ptSh1Child (StateLib.getIndexOfAddr shadow1 fstLevel)
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
unfold accessibleChildPageIsAccessibleIntoParent.
intros HisChild Hderivation Hdisjointconfig Hnodupconfig Hnodupmapped Hpde Hparentispart Hlevel Hdefault
 Hlookup Hcurpd Hcurpart Hget Hpresent
 Hi Hii Hptfromsh1notnull  Haccess partition va pd accessiblePage.
intros Hparts Hpd Haccessinpart.
rewrite getPartitionsUpdateUserFlag in *;trivial.
simpl in *.
rewrite getPdUpdateUserFlag in *;trivial.

assert(Hisaccessible :  getAccessibleMappedPage pd
                  {|
                  currentPartition := currentPartition s;
                  memory := add ptSh1Child (StateLib.getIndexOfAddr shadow1 fstLevel)
                              (PE
                                 {|
                                 read := read entry;
                                 write := write entry;
                                 exec := exec entry;
                                 present := present entry;
                                 user := false;
                                 pa := pa entry |}) (memory s) beqPage beqIndex |} va = 
                                 getAccessibleMappedPage pd s va).
{
unfold getAccessibleMappedPage in Haccessinpart.
unfold getAccessibleMappedPage.
simpl in *.
rewrite <- Hlevel in *.
rewrite getIndirectionUpdateUserFlag in *;trivial.
case_eq (getIndirection pd va level (nbLevel - 1) s );intros * Hgetind;
rewrite Hgetind in *;trivial.
destruct(Nat.eqb defaultPage p);trivial.
rewrite readPresentUpdateUserFlag in *;trivial.
destruct (StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) );
trivial.
destruct b;trivial.
case_eq(StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel)
                    (add ptSh1Child (StateLib.getIndexOfAddr shadow1  fstLevel)
                       (PE
                          {|
                          read := read entry;
                          write := write entry;
                          exec := exec entry;
                          present := present entry;
                          user := false;
                          pa := pa entry |}) (memory s) beqPage beqIndex));intros * Hisaccess;
rewrite Hisaccess in *.
+ destruct b;try now contradict Haccessinpart.
rewrite readPhyEntryUpdateUserFlag in *;trivial.
rewrite Haccessinpart.
unfold StateLib.readAccessible in *.
simpl in *. 
case_eq( beqPairs (ptSh1Child, StateLib.getIndexOfAddr shadow1 fstLevel)
                  (p, StateLib.getIndexOfAddr va fstLevel) beqPage beqIndex);intros * Hpairs.
 - rewrite Hpairs in Hisaccess.
  simpl in *.
  now contradict Hisaccess.
 - rewrite Hpairs in Hisaccess.
   apply beqPairsFalse in Hpairs.
   assert(Hremove : lookup p (StateLib.getIndexOfAddr va fstLevel)
                (removeDup ptSh1Child (StateLib.getIndexOfAddr shadow1 fstLevel) 
                   (memory s) beqPage beqIndex) beqPage beqIndex =
          lookup p (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex).
          apply removeDupIdentity;intuition.
    rewrite Hremove in *.
    rewrite Hisaccess;trivial.
+ now contradict Haccessinpart. }
rewrite Hisaccessible in *.
set (s' :=  {|
  currentPartition := currentPartition s;
  memory := add ptSh1Child (StateLib.getIndexOfAddr shadow1 fstLevel)
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} ) in *.
assert(Hgoal: isAccessibleMappedPageInParent partition va accessiblePage s = true).
{
apply Haccess with pd ;trivial. }
unfold isAccessibleMappedPageInParent in *.
simpl in *.
rewrite getSndShadowUpdateUserFlag;trivial.
case_eq(StateLib.getSndShadow partition (memory s)); [intros sh2 Hsh2 | intros Hsh2];
rewrite Hsh2 in *;
try now contradict Hgoal.
unfold s'.
rewrite <- getVirtualAddressSh2UpdateUserFlag;trivial.
rewrite getParentUpdateUserFlag;trivial.
case_eq( getVirtualAddressSh2 sh2 s va); [intros vaInParent HvaInparent | intros HvaInparent]; 
rewrite HvaInparent in *;try now contradict Hgoal.
case_eq(StateLib.getParent partition (memory s));trivial;
[intros parent Hparent | intros Hparent];rewrite Hparent in *;  try now contradict Hgoal.
rewrite getPdUpdateUserFlag;trivial.
case_eq(StateLib.getPd parent (memory s));[intros pdParent Hpdparent| intros Hpdparent];
 rewrite Hpdparent in *;
try now contradict Hgoal.
case_eq( getAccessibleMappedPage pdParent s vaInParent ); 
[intros phypage HvaInparentIsAcces|intros HvaInparentIsAcces |intros HvaInparentIsAcces] ; rewrite HvaInparentIsAcces in *;
try now contradict Hgoal.
apply beq_nat_true in Hgoal.
rewrite Hgoal in *.
assert(Hparteq : parent = curpart \/ parent <> curpart).
{ destruct curpart as (ancestor & Hi1); 
  destruct parent as (parent & Hi2).
  assert(Hor : parent = ancestor \/ parent <> ancestor) by lia.
  destruct Hor.
  subst.
  left;f_equal;apply proof_irrelevance; trivial.
  right.
  unfold not.
  intros Hor.
  inversion Hor.
  lia. }
destruct Hparteq as [Hparteq| Hparteq].
 + (** The Same partitions *) 
   subst.
  assert(pdParent = currentPD).
  rewrite getPdNextEntryIsPPEq with curpart currentPD pdParent s ;trivial.
  apply nextEntryIsPPgetPd;trivial.
  subst.
  destruct Hget with (StateLib.getIndexOfAddr shadow1 fstLevel)
  as (Hpe & Hgetptancestor);
  trivial.
  unfold getTableAddrRoot in Hgetptancestor.
  destruct Hgetptancestor as (_ & Hgetptancestor).  
  rewrite <- nextEntryIsPPgetPd in *.
  apply Hgetptancestor in Hcurpd.
  clear Hgetptancestor.
  destruct Hcurpd as (nbL & HnbL & stop & Hstop & Hind).  
  assert(Hvas : StateLib.checkVAddrsEqualityWOOffset nbLevel shadow1 vaInParent level = true \/ 
                StateLib.checkVAddrsEqualityWOOffset nbLevel shadow1 vaInParent level = false). 
  {   destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel shadow1 vaInParent level);intuition. }
  destruct Hvas as  [Hvaseq | Hvasnoteq];subst.
  - (** The same virtual addresses into the same partition  : here we have a contradiction because 
         shadow1 is not derived into currentPart, in another words the associated physical address 
         "pa entry" is not mapped in any child. 
         But in our case : partition is a curpart's child and there is a virtual address va which map the
         physical page "accessiblePage"  into partition
         we prove that accessiblePage is equal to "pa entry" and using a new consistency property we prove that
         we have a contradiction *)

  assert(Hlastidx : (StateLib.getIndexOfAddr shadow1 fstLevel) =
   (StateLib.getIndexOfAddr vaInParent fstLevel)).
    { apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level; trivial.
      unfold fstLevel.
      unfold CLevel.
      case_eq ( lt_dec 0 nbLevel );intros.
      simpl.
      lia.
      assert(0<nbLevel) by apply nbLevelNotZero.
      lia.
      destruct level;simpl; lia. }
      assert(phypage = (pa entry)).
    { unfold getAccessibleMappedPage in HvaInparentIsAcces.
    rewrite <- HnbL in *; try now contradict HvaInparentIsAcces.
    assert(getIndirection currentPD shadow1 nbL (nbLevel - 1) s =
          getIndirection currentPD vaInParent nbL (nbLevel - 1) s );trivial.
    { apply getIndirectionEq;trivial.
      destruct nbL;simpl; lia.
      inversion Hlevel.
      subst;trivial. }
    rewrite <- H in *.
    assert(Hind2 : getIndirection currentPD shadow1 nbL (nbLevel - 1) s = Some ptSh1Child ).
    apply getIndirectionStopLevelGT2 with (nbL +1);trivial;try lia.
    apply getNbLevelEq in HnbL.
    subst.
    unfold CLevel.
    case_eq((lt_dec (nbLevel - 1) nbLevel));intros;simpl;trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    lia.
    rewrite Hind2 in *.
    rewrite Hdefault in *.
    rewrite <- Hlastidx in *.
    unfold StateLib.readPresent in *.
    rewrite Hlookup in *.
    case_eq(present entry);intros * Hpres; rewrite Hpres in *; try now contradict
    HvaInparentIsAcces.
    
    case_eq(StateLib.readAccessible  ptSh1Child (StateLib.getIndexOfAddr shadow1 fstLevel)
                         (memory s)); intros * Haccessflag; rewrite Haccessflag in *; try now contradict 
                         HvaInparentIsAcces.
    destruct b;try now contradict HvaInparentIsAcces.
    unfold StateLib.readPhyEntry in *.
    rewrite Hlookup in *.
    inversion HvaInparentIsAcces;trivial. }
        subst.
        clear Haccess.
        (** use physicalPageNotDerived and isChild  to get a contradiction *)
        assert(HderivShadow1 : ~ isDerived curpart shadow1 s ).
        { destruct Hi with (StateLib.getIndexOfAddr shadow1 fstLevel) as 
        (Hve & Hgetve);trivial.

        clear Hi.
        destruct Hii as (va0 & Hvae & Hveq).
        unfold isDerived.
        unfold getTableAddrRoot in *.
        destruct Hgetve as (_ & Hgetve).
        assert(Hcursh1 :(exists entry : page, nextEntryIsPP curpart sh1idx entry s /\ entry <> defaultPage)).
        unfold partitionDescriptorEntry in *.
        apply Hpde;trivial.
        right;left;trivial.
        destruct Hcursh1 as (cursh1 & Hcursh1 & Hsh1notnull).
        rewrite nextEntryIsPPgetFstShadow in *.
        rewrite Hcursh1.
        rewrite <- nextEntryIsPPgetFstShadow in *.        
        apply Hgetve in Hcursh1.
        destruct Hcursh1 as (l & Hl & stop & Hstop & Hgetva).
        clear Hgetve.
        unfold getVirtualAddressSh1.
        rewrite <- Hl.
        subst.
        assert(Hgetind : getIndirection cursh1 shadow1 l (nbLevel - 1) s  = Some ptSh1ChildFromSh1).
        apply getIndirectionStopLevelGT2 with (l+1);trivial.
        lia.
        apply getNbLevelEq in Hl.
        subst.
        apply nbLevelEq.
        rewrite Hgetind.
        rewrite Hptfromsh1notnull.
        unfold  isEntryVA in *.
        unfold isVE in *.
        unfold StateLib.readVirEntry.
        case_eq(lookup ptSh1ChildFromSh1 (StateLib.getIndexOfAddr shadow1 fstLevel) 
          (memory s) beqPage beqIndex);intros * Hlookupsh1;rewrite Hlookupsh1 in *; 
          try now contradict Hve.
        case_eq v;intros * Hvsh1;rewrite Hvsh1 in *; 
          try now contradict Hve.
          subst.
          unfold not;intros.
          rewrite H in Hveq.
          now contradict Hveq. }
           unfold physicalPageNotDerived in *.
         assert(accessiblePage <> accessiblePage).
         apply Hderivation with curpart shadow1 currentPD partition pd va;
         trivial.
         apply nextEntryIsPPgetPd;trivial.
         apply accessiblePAgeIsMapped;trivial.
         subst.
         assert(getAccessibleMappedPage currentPD s shadow1 =
                     SomePage (pa entry)).
         rewrite <- HvaInparentIsAcces.
         apply getAccessibleMappedPageEq with level;trivial.
         symmetry;trivial.
         rewrite  H.
         f_equal.
         symmetry.
         destruct accessiblePage.
         destruct (pa entry).
         simpl in *.
         subst.
         f_equal.
         apply proof_irrelevance.
         
         unfold isChild in *.
         apply HisChild;trivial.
         apply nextEntryIsPPgetPd;trivial.
         apply accessiblePAgeIsMapped;trivial.
         now contradict H.
   - (** The same partition but with diffrent virtual adresses **)
    assert(shadow1 <>vaInParent  ).
    apply  checkVAddrsEqualityWOOffsetEqFalse with  level level;trivial.
    symmetry;trivial.
    assert(getAccessibleMappedPage currentPD
    {|
    currentPartition := currentPartition s;
    memory := add ptSh1Child (StateLib.getIndexOfAddr shadow1 fstLevel)
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |} vaInParent = 
          getAccessibleMappedPage currentPD s vaInParent).
    apply getAccessibleMappedPageUpdateUserFlagDiffrentVaddrs with level curpart;trivial.
    rewrite nextEntryIsPPgetPd in *;trivial.
    rewrite <- HnbL in Hlevel.
    inversion Hlevel.
    subst.
    trivial.
    rewrite H0.
    rewrite HvaInparentIsAcces.
    apply NPeano.Nat.eqb_eq;trivial.
 (** Keep me please ! **)
+ (** Diffrent partitions *)
  rewrite <- getAccessibleMappedPageUpdateUserFlagDiffrentPartitions with
  pdParent s vaInParent entry shadow1 ptSh1Child curpart
  parent;trivial. 
  rewrite HvaInparentIsAcces;trivial.
  apply PeanoNat.Nat.eqb_eq;trivial.
  destruct Hget with (StateLib.getIndexOfAddr shadow1 fstLevel)
  ;trivial.
  unfold parentInPartitionList in *.
  apply Hparentispart with partition;trivial.
  rewrite nextEntryIsPPgetParent in *;trivial.
  unfold configTablesAreDifferent in *.
  apply Hdisjointconfig;trivial.
  unfold parentInPartitionList in Hparentispart.
  apply Hparentispart with partition;trivial.
  rewrite nextEntryIsPPgetParent in *;trivial.
  unfold not;intros Hfalse.
  subst.
  now contradict Hparteq. 
  Qed. 
(* Qed.
 *)
Lemma isAncestorUpdateUserFlag currentPart descParent table idx entry s :
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->  
isAncestor currentPart descParent s-> 
isAncestor currentPart descParent
  {|
  currentPartition := currentPartition s;
  memory := add table idx 
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |} .
Proof.
intros Hlookup Hprop.
unfold isAncestor in *.
destruct Hprop.
left;trivial.
right.
unfold getAncestors in *.
revert  currentPart H.
induction (nbPage + 1);
simpl in *;trivial.
intros.
rewrite getParentUpdateUserFlag;trivial.
case_eq(StateLib.getParent currentPart (memory s));intros;rewrite H0 in *;try now contradict
H. simpl in *.
destruct H. 
left;trivial.
right.
apply IHn;trivial.
Qed.

Lemma getVirtualAddressSh1UpdateUserFlag p table idx va  entry s flag :
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
getVirtualAddressSh1 p s va =
getVirtualAddressSh1 p
{|
currentPartition := currentPartition s;
memory := add table idx
          (PE
             {|
             read := read entry;
             write := write entry;
             exec := exec entry;
             present := present entry;
             user := flag;
             pa := pa entry |}) (memory s) beqPage beqIndex |} va.
Proof.
intros.
unfold getVirtualAddressSh1.
simpl.
destruct (StateLib.getNbLevel );trivial.
rewrite getIndirectionUpdateUserFlag;trivial.
destruct(getIndirection p va l (nbLevel - 1) s );trivial.
rewrite readVirEntryUpdateUserFlag with p0  table idx   (StateLib.getIndexOfAddr va fstLevel)  s entry  flag;trivial.
Qed.

Lemma getPDFlagUpdateUserFlag p table idx va  entry s flag :
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
getPDFlag p va s =
getPDFlag p va
{|
currentPartition := currentPartition s;
memory := add table idx
          (PE
             {|
             read := read entry;
             write := write entry;
             exec := exec entry;
             present := present entry;
             user := flag;
             pa := pa entry |}) (memory s) beqPage beqIndex |} .
Proof.
intros.
unfold getPDFlag.
simpl.
destruct (StateLib.getNbLevel );trivial.
rewrite getIndirectionUpdateUserFlag;trivial.
destruct(getIndirection p va l (nbLevel - 1) s );trivial.
rewrite readPDflagUpdateUserFlag;trivial.
Qed.

Lemma isDerivedUpdateUserFlag parent va  table idx entry s  flag:
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->
isDerived parent va s -> 
isDerived parent va  {|
 currentPartition := currentPartition s;
 memory := add table idx
             (PE
                {|
                read := read entry;
                write := write entry;
                exec := exec entry;
                present := present entry;
                user := flag;
                pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
unfold isDerived;simpl;intros.
rewrite getFstShadowUpdateUserFlag;trivial.
destruct (StateLib.getFstShadow parent (memory s) ); try now contradict H0.
rewrite <- getVirtualAddressSh1UpdateUserFlag with p table idx va entry s flag;trivial.
Qed.

Lemma physicalPageNotDerivedUpdateUserFlag entry table idx s flag :
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
physicalPageNotDerived s -> 
physicalPageNotDerived
{|
currentPartition := currentPartition s;
memory := add table idx 
        (PE
           {|
           read := read entry;
           write := write entry;
           exec := exec entry;
           present := present entry;
           user := flag;
           pa := pa entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros.
unfold physicalPageNotDerived in *.
intros;simpl in *.
rewrite getMappedPageUpdateUserFlag  in *;trivial.
rewrite getPdUpdateUserFlag in *;trivial.
rewrite getChildrenUpdateFlagUser in *;trivial.
rewrite getPartitionsUpdateUserFlag in *;trivial.

apply H0 with parent va pdParent child pdChild vaInChild;trivial.
unfold not;intros.
apply H3.
apply isDerivedUpdateUserFlag;trivial.
Qed.
