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
    This file contains required lemmas to prove the [writeAccessible] invariant *)
Require Import Core.Internal Isolation Consistency WeakestPreconditions 
Invariants StateLib Model.Hardware Model.ADT DependentTypeLemmas
GetTableAddr Model.MAL Model.Lib Lib InternalLemmas.
Require Import Coq.Logic.ProofIrrelevance Omega List.
Import List.ListNotations.

Lemma getPdUpdateUserFlag ( partition : page) entry s table idx flag:
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getPd partition
  (memory
     {| currentPartition := currentPartition s;
        memory := add table idx (PE {| read := read entry;
                                       write := write entry;
                                       exec := exec entry;
                                       present := present entry;
                                       user := flag;
                                       pa := pa entry |}) (memory s) beqPage beqIndex |}) =
StateLib.getPd partition (memory s).
Proof. 
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
  destruct (defaultPage =? p0);trivial.
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
apply getFstShadowUpdateUserFlag;trivial.
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
getPdsVAddr partition l getAllVAddr
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
getPdsVAddr partition l getAllVAddr s.
Proof.
intros Hentry.  
unfold getPdsVAddr.
induction getAllVAddr. simpl. trivial.
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

(* Lemma getAccessibleMappedPageUpdateUserFlag p a s table idx entry : 
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
                 user := false;
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
Qed.  *)

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

Lemma readPresentUpdateUserFlag  p s entry table idx idx1: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.readPresent p idx1 (memory {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |})  = 
StateLib.readPresent p idx1 (memory s).
Proof.
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
destruct (StateLib.readPresent p lastidx (memory s));
[| now contradict Hget].
destruct b;[| now contradict HgetAcc].
assert( p <> table1 \/  p = table1). 
{ destruct p.
     destruct table1. simpl in *.
     assert(p = p0 \/ p <> p0) by omega.
     destruct H.
     right.
     simpl.
     subst.
     f_equal.
     apply proof_irrelevance.
     left.
     unfold not.
     intros.
     inversion H0. omega. }
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
    apply readPhyEntryUpdateUserFlag; trivial.
    rewrite H0 in HgetAcc; trivial.
+ subst. 
   assert (lastidx <> idx1 \/ lastidx = idx1 ).
   { destruct lastidx.
     destruct idx1. simpl in *.
     assert(i = i0 \/ i <> i0) by omega.
     destruct H.
     right.
     simpl.
     subst.
     f_equal.
     apply proof_irrelevance.
     left.
     unfold not.
     intros.
     inversion H0. omega. }
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
    apply readPhyEntryUpdateUserFlag; trivial.
    rewrite H0 in HgetAcc; trivial.
  - subst. rewrite H in *. clear H.
    assert(StateLib.readAccessible table1 idx1 (memory s') = Some false).
    unfold s'.
    unfold StateLib.readAccessible.
    simpl.
    assert(beqPairs (table1, idx1) (table1, idx1) beqPage beqIndex = true).
    apply beqPairsTrue.
    split; trivial.
    rewrite H; simpl; trivial.   
    rewrite H in HgetAcc.
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
set (entry0 := (PE {|
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
apply getPdUpdateUserFlag;trivial.
rewrite HgetPd.
destruct (StateLib.getPd partition (memory s));trivial.
assert (getPdsVAddr partition l getAllVAddr s' = 
            getPdsVAddr partition l getAllVAddr s) as HgetPdsVa.
    { apply getPdsVAddrUpdateUserFlag;trivial. }
rewrite HgetPdsVa.
f_equal.
apply getMappedPagesAuxUpdateUserFlag;trivial.
Qed.


Lemma getPartitionAuxUpdateUserFlag l s entry flag table idx : 
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
  destruct (pa entry =? defaultPage );
  generalize (IHsize p p (CIndex size) H);clear IHsize; intros IHsize;
  rewrite IHsize;trivial.
+ apply beqPairsFalse in Hpairs.
  assert (lookup   p (CIndex size) (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  p (CIndex size) (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. subst.  intuition. }
  rewrite  Hmemory. 
  destruct (lookup p (CIndex size) (memory s) beqPage beqIndex); [ 
  destruct v;  [
  destruct (pa p0 =? defaultPage ); trivial | | | | ];
  generalize (IHsize p table idx H);clear IHsize; intros IHsize;
  rewrite IHsize;trivial | generalize (IHsize p table idx );clear IHsize; intros IHsize;
  apply IHsize;trivial ].
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
getTrdShadows sh3
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
                 pa := pa entry |}) (memory s) beqPage beqIndex |} nbPage =
getTrdShadows sh3 s nbPage.
Proof.
revert sh3.
induction nbPage;trivial.
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
rewrite readPhyEntryUpdateUserFlag;trivial.
destruct (StateLib.readPhyEntry sh3 i (memory s));trivial.
destruct (p =? defaultPage) ;trivial.
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
rewrite HgetPart in H0.
apply nextEntryIsPPUpdateUserFlag' in H1.
generalize (Hnodup idxroot H partition H0  root H1); clear Hnodup; intros Hnodup. 
assert (getIndirections root s' = getIndirections root s) as Hind.
apply getIndirectionsUpdateUserFlag ; trivial.
rewrite Hind; trivial.
Qed.

Lemma readPhyEntryInGetIndirectionsAux s root n: 
forall page1,page1 <> defaultPage -> 
In page1 (getTablePages root tableSize s) -> 
n> 1 -> 
In page1 (getIndirectionsAux root s n)  .
Proof.
intros. 
destruct n;
intros; simpl in *.  now contradict H1.
simpl in *. right.
apply in_flat_map.
exists page1.
split; trivial.
destruct n.  omega. simpl.
left. trivial.     
Qed.

Lemma nodupLevelMinus1 root s (n0 : nat) idx: 
forall p , p<> defaultPage -> 
StateLib.readPhyEntry root idx (memory s) = Some p -> 
NoDup (getIndirectionsAux root s n0 ) ->
 n0 <= nbLevel  -> 
NoDup (getIndirectionsAux p s (n0 - 1)).
Proof.
intros p Hnotnull Hread Hnodup Hnbl.
destruct n0;simpl in *; trivial.
rewrite NPeano.Nat.sub_0_r.
apply NoDup_cons_iff in Hnodup.
destruct Hnodup as (_ & Hnodup).
assert (In p (getTablePages root tableSize s)) as HIn.
apply readPhyEntryInGetTablePages with idx; trivial.
destruct idx. simpl in *; trivial.
assert (idx = (CIndex idx)) as Hidx.
symmetry. 
apply CIndexEq.
rewrite <- Hidx. assumption.
induction (getTablePages root tableSize s).
now contradict HIn.
simpl in *.
apply NoDupSplit in Hnodup.
destruct HIn;
destruct Hnodup;
subst; trivial.
apply IHl;trivial.
Qed.
(* Lemma checkVAddrsEqualityWOOffset_exists va1 va2 level bound:
StateLib.checkVAddrsEqualityWOOffset va1 va2 level bound = false -> 
bound <= level ->  
exists levelstop : level ,  levelstop <= level /\ levelstop >= CLevel (level - bound) /\  
StateLib.getIndexOfAddr va1 levelstop <>
StateLib.getIndexOfAddr va2 levelstop .
Proof. 
intros. 
Admitted. *)

Lemma inclGetIndirectionsAuxMinus1 n root idx p s: 
StateLib.readPhyEntry root idx (memory s) = Some p -> 
(defaultPage =? p) = false -> 
n> 1 -> 
incl (getIndirectionsAux p s (n - 1)) (getIndirectionsAux root s n).
Proof.
intros Hread Hnotnull Hn. 
unfold incl.              
intros.
set(k := n -1) in *.
replace n with (S k); [ | unfold k; omega].
simpl.              
assert (In p (getTablePages root tableSize s)) as Htbl. 
apply readPhyEntryInGetTablePages with idx; trivial.
destruct idx; simpl in *; trivial.
apply beq_nat_false in Hnotnull. unfold not. intros.
contradict Hnotnull.
rewrite H0. trivial.
assert (idx = (CIndex idx)) as Hidx'.
symmetry. apply CIndexEq. rewrite <- Hidx'.
assumption. right.
induction ((getTablePages root tableSize s)).
now contradict Htbl.
simpl in *.
destruct Htbl; subst;
apply in_app_iff. left;trivial.
right. 

apply IHl;trivial.
Qed.

Lemma notInFlatMapNotInGetIndirection k l ( p0: page) s x: 
In p0 l -> 
~ In x (flat_map (fun p : page => getIndirectionsAux p s k) l) -> 
~ In x (getIndirectionsAux p0 s k).
Proof.
revert  p0 x k.
induction l; simpl in *; intros; [ 
now contradict H |].
destruct H; subst.
+ unfold not. intros. apply H0.
  apply in_app_iff. left. assumption.
+ apply IHl; trivial.
  unfold not.
  intros. apply H0.
  apply in_app_iff. right. assumption. 
Qed.

Lemma disjointGetIndirectionsAuxMiddle n (p p0 : page) root (idx1 idx2 : index) s:
p0 <> p -> 
n > 1 -> 
(defaultPage =? p) = false -> 
(defaultPage =? p0) = false -> 
NoDup (getIndirectionsAux root s n) -> 
StateLib.readPhyEntry root idx1 (memory s) = Some p0 -> 
StateLib.readPhyEntry root idx2 (memory s) = Some p ->
disjoint (getIndirectionsAux p s (n - 1)) (getIndirectionsAux p0 s (n - 1)).
Proof. 
unfold disjoint.
intros Hp0p Hn Hnotnull1 Hnotnull2 Hnodup Hreadp0 Hreadp x Hxp.        
set(k := n -1) in *.
assert(n = S k) as Hk.
unfold k in *.  omega.          
rewrite Hk in Hnodup. simpl in *.
apply  NoDup_cons_iff in Hnodup.
destruct Hnodup as (Hnoduproot & Hnodup2).
assert ( In p0  (getTablePages root tableSize s)) as Hp0root.
apply readPhyEntryInGetTablePages with idx1; trivial.
destruct idx1. simpl in *. trivial.
apply beq_nat_false in Hnotnull2.
unfold not;intros; apply Hnotnull2; clear Hk; subst;trivial.
assert(CIndex idx1 =  idx1) as Hcidx.
apply CIndexEq.
rewrite Hcidx; trivial. 
assert ( In p  (getTablePages root tableSize s)) as Hproot. 
apply readPhyEntryInGetTablePages with idx2; trivial.
destruct idx2. simpl in *. trivial.
apply beq_nat_false in Hnotnull1. 
unfold not;intros; apply Hnotnull1;
clear Hk; subst;trivial.
assert(CIndex idx2 =  idx2) as Hcidx.
apply CIndexEq. rewrite Hcidx. trivial.
move Hnodup2 at bottom.
clear Hnoduproot Hk.
induction (getTablePages root tableSize s);  [ 
now contradict Hproot | ].
simpl in *.
destruct Hproot as [Hproot | Hproot];
destruct Hp0root as [Hp0root | Hp0root]; subst.
+ subst. now contradict Hp0p.
+ apply NoDupSplitInclIff in Hnodup2. 
  destruct Hnodup2 as ((Hnodup1 & Hnodup2) & Hdisjoint).
  unfold disjoint in Hdisjoint. subst. clear IHl.
  generalize (Hdisjoint x Hxp);clear Hdisjoint; intros Hdisjoint.
  apply notInFlatMapNotInGetIndirection with l; trivial.
+ apply NoDupSplitInclIff in Hnodup2. 
  destruct Hnodup2 as ((Hnodup1 & Hnodup2) & Hdisjoint).
  unfold disjoint in Hdisjoint. subst.
  unfold not. intros Hxp0. contradict Hxp.
  generalize (Hdisjoint x Hxp0);clear Hdisjoint; intros Hdisjoint.
  apply notInFlatMapNotInGetIndirection with l; trivial.
+ apply IHl; trivial. 
  apply NoDupSplit in Hnodup2.
  destruct Hnodup2. assumption.
Qed.

Lemma getIndirectionInGetIndirectionAuxMinus1 table (p: page) s n va1 pred n1 (level1 : level):
level1> 0 -> 
(defaultPage =? p) = false ->  
level1 <= CLevel (n -1) -> 
StateLib.Level.pred level1 = Some pred -> 
table <> defaultPage -> 
n <= nbLevel -> 
n > 1 -> 
getIndirection p va1 pred n1 s = Some table -> 
In table (getIndirectionsAux p s (n - 1)). 
Proof.
intros Hfstlevel Hnotnull Hlevel Hpred Hnotnullt Hnbl Hn Hind.
apply getIndirectionInGetIndirections 
with va1 pred n1;trivial;  try omega.
  - apply levelPredMinus1 in Hpred; trivial.
    unfold CLevel in Hpred. 
    case_eq(lt_dec (level1 - 1) nbLevel ); intros l Hl0;  
    rewrite Hl0 in Hpred.
    simpl in *.
    inversion Hpred. subst.
    simpl in *.
    
    (* clear  Htableroot2 Htableroot1  
    Hread2  Hread1 HNoDup2 HNoDup1
    Hnull1 Hnull2 Hnotnull2 Hnotnull1 Hroot2 Hroot1. *)
    unfold CLevel in *.
    destruct level1.
    simpl in *. 
    
    case_eq (lt_dec (n - 1) nbLevel); 
    intros ii Hii;  rewrite Hii in *.
    simpl in *.
    case_eq (lt_dec (n - 1 - 1) nbLevel);
    intros.
    simpl in *. omega. omega.  
    case_eq (lt_dec (n - 1 - 1) nbLevel);
    intros.
    simpl in *. omega. omega.
    destruct level1. 
    simpl in *. omega. 
    unfold StateLib.Level.eqb.
    unfold CLevel. 
    case_eq(lt_dec (n - 1) nbLevel ); intros;
    simpl in *.
    unfold fstLevel. unfold CLevel.
    case_eq(lt_dec 0 nbLevel).
    intros. simpl.
    apply NPeano.Nat.eqb_neq. omega.
    intros. assert (0 < nbLevel) by apply nbLevelNotZero.
    omega. omega.
  - apply beq_nat_false in Hnotnull. unfold not. intros.
    apply Hnotnull. subst. trivial. 
Qed.
    
Lemma getTablePagesNoDup root (p p0 : page) idx1 idx2    s:
idx1 < tableSize -> idx2 < tableSize ->
NoDup (getTablePages root tableSize s) -> 
StateLib.readPhyEntry root (CIndex idx1) (memory s) = Some p0 -> 
StateLib.readPhyEntry root (CIndex idx2) (memory s) = Some p -> 
(idx1 =? idx2) = false ->
(p =? defaultPage) = false -> 
(p0 =? defaultPage) = false -> 
p0 <> p.
Proof.
assert (H: tableSize <= tableSize) by omega; revert H.
generalize tableSize at 1 3 4 5  .
induction n.
+ intros. now contradict H0.
+ intros. simpl in *.
  apply beq_nat_false in H5. 
  assert(Hdec : (idx1 = n /\ idx2 <> n) \/ 
          (idx2 = n /\ idx1 <> n) \/ 
          (idx1 <> n /\ idx2 <> n)). omega.
  destruct Hdec as [(Hdec1 & Hdec2) | [(Hdec1 & Hdec2) |(Hdec1 & Hdec2)]];
  subst.
  * unfold StateLib.readPhyEntry in H3. intros.
    case_eq (lookup root (CIndex n) (memory s) beqPage beqIndex); 
    [ intros v Hv'| intros Hv'] ; rewrite Hv' in  *; [ | now contradict H3 ];
    destruct v; try now contradict H3. inversion H3. subst.
    subst.  clear IHn H3. rewrite H7 in H2.
    apply NoDupSplitInclIff in H2.
    destruct H2 as ( (_ & _) & H2).
    unfold disjoint in H2.
    assert (In p (getTablePages root n s)).
    apply readPhyEntryInGetTablePages with idx2; trivial.
    omega. omega. 
    unfold not. intros. subst. apply beq_nat_false in H6.
    now contradict H6.
    apply H2 in H3. unfold not. intros.
    contradict H3. simpl in *. left. assumption.
  * unfold StateLib.readPhyEntry in H4. intros.
    case_eq (lookup root (CIndex n) (memory s) beqPage beqIndex); 
    [ intros v Hv'| intros Hv'] ; rewrite Hv' in  *; [ | now contradict H4 ];
    destruct v; try now contradict H4. inversion H4. subst.
    subst.  clear IHn H4. rewrite H6 in H2.
    apply NoDupSplitInclIff in H2.
    destruct H2 as ( (_ & _) & H2).
    unfold disjoint in H2.
    assert (In p0 (getTablePages root n s)).
    apply readPhyEntryInGetTablePages with idx1; trivial.
    omega. omega. 
    unfold not. intros. subst. apply beq_nat_false in H7.
    now contradict H7.
    apply H2 in H4. unfold not. intros.
    contradict H4. simpl in *. left. rewrite H8. trivial.
  *  case_eq (lookup root (CIndex n) (memory s) beqPage beqIndex); 
    [ intros v Hv'| intros Hv'] ; rewrite Hv' in  *;
    
    [ |
    apply IHn; trivial;try omega;
    apply Nat.eqb_neq; trivial ].
    destruct v; [ | apply IHn;  trivial;try omega;
    apply Nat.eqb_neq; trivial |
    apply IHn;  trivial;try omega;
    apply Nat.eqb_neq; trivial | apply IHn;  trivial;try omega;
    apply Nat.eqb_neq; trivial | apply IHn;  trivial;try omega;
    apply Nat.eqb_neq; trivial].
    case_eq(pa p1 =? defaultPage); intros Hnull; rewrite Hnull in *.
    { apply IHn; trivial; try omega. apply Nat.eqb_neq; trivial. }
    {
    apply NoDupSplitInclIff in H2.
    destruct H2 as ( (H2 & _) &  _).
    apply IHn; trivial; try omega. apply Nat.eqb_neq; trivial. }
Qed.

Lemma getTablePagesNoDupFlatMap s n k root: 
n > 0 -> 
NoDup
(flat_map (fun p : page => getIndirectionsAux p s n)
(getTablePages root k s)) -> 
NoDup (getTablePages root k s).
Proof. 
induction (getTablePages root k s).
simpl in *. trivial.
simpl.
intros Hn H.
apply NoDup_cons_iff.
apply NoDupSplitInclIff in H.
destruct H as((H1 & H2) & H3).
split.
unfold disjoint in *.
generalize (H3 a ); clear H3; intros H3.
assert (~ In a (flat_map (fun p : page => getIndirectionsAux p s n) l)).
apply H3; trivial.
destruct n. simpl in *. omega.
simpl. left. trivial.
unfold not. contradict H.
apply in_flat_map. exists a.
split. assumption. destruct n; simpl. now contradict Hn.
left. trivial.  
apply IHl; trivial.
Qed. 
                  

Lemma pageTablesOrIndicesAreDifferent (root1 root2 table1 table2 : page ) 
(va1 va2 : vaddr) (level1 : level)  (stop : nat)  s:
root1 <> defaultPage -> root2 <> defaultPage -> 
NoDup (getIndirections root1 s) ->
NoDup (getIndirections root2 s) -> 
StateLib.checkVAddrsEqualityWOOffset stop va1 va2 level1 = false -> 
( (level1 = CLevel (nbLevel -1) /\ root1 = root2) \/ (level1 < CLevel (nbLevel -1) /\(
(disjoint (getIndirections root1 s) (getIndirections root2 s)/\ root1 <> root2) \/ root1 = root2  )) )-> 
table1 <> defaultPage -> 
table2 <> defaultPage -> 
(* stop > 0 ->  *)
getIndirection root1 va1 level1 stop s = Some table1-> 
getIndirection root2 va2 level1 stop s = Some table2 -> 
table1 <> table2 \/ StateLib.getIndexOfAddr va1 fstLevel <> StateLib.getIndexOfAddr va2 fstLevel.
Proof.
intros Hroot1 Hroot2 HNoDup1 HNoDup2 Hvas  Hlevel 
Hnotnull1 Hnotnull2  (* Hstop *) Htableroot1    Htableroot2.
assert (StateLib.Level.eqb level1 fstLevel = true \/ StateLib.Level.eqb level1 fstLevel = false).
{ unfold StateLib.Level.eqb.
        rewrite NPeano.Nat.eqb_eq.  rewrite NPeano.Nat.eqb_neq.
        omega. }
assert(StateLib.getIndexOfAddr va1 fstLevel <> StateLib.getIndexOfAddr va2 fstLevel \/ 
StateLib.getIndexOfAddr va1 fstLevel = StateLib.getIndexOfAddr va2 fstLevel).
{ destruct (StateLib.getIndexOfAddr va1 fstLevel), (StateLib.getIndexOfAddr va2 fstLevel ) .
  assert (i = i0 \/ i<> i0). omega.
  destruct H0. subst.
  assert(Hi = Hi0) by apply proof_irrelevance. subst.
  right. reflexivity. left. trivial.
  unfold not. intros. apply H0.
  clear H0. inversion H1. trivial. }
destruct H0; [right; assumption |].
destruct H.
+ destruct stop. simpl in *.
 now contradict Hvas.
  simpl in Hvas. right.
  rewrite H in Hvas.
  apply beq_nat_false in Hvas.
  apply levelEqBEqNatTrue in H. subst. unfold not.
  intros. contradict Hvas. rewrite H. reflexivity.
+ clear H.
  revert HNoDup1 HNoDup2 Hvas Hlevel Hnotnull1 Hnotnull2 
  Htableroot1 (* Hstop *) Htableroot2 H0 Hroot1 Hroot2 .
  revert root1 root2 table1 table2 level1 va1 va2.
  assert (Hs :stop <= stop). omega. revert Hs.  
  generalize stop at 1 3 4 5 .
  intros.
  destruct stop0.
  simpl in *.
  now contradict Hvas.
  assert (nbLevel <= nbLevel) as Hnbl by omega.
  revert Hnbl.
  revert HNoDup1 HNoDup2 Hvas Hlevel Hnotnull1 Hnotnull2 
  Htableroot1 (* Hstop *) Htableroot2 H0 Hs Hroot1 Hroot2 (* Hroot12 *).
  revert root1 root2 table1 table2 level1 va1 va2 stop.
  unfold getIndirections.
  generalize nbLevel at 1 2 3 4 5 6 7. 
  induction (S stop0).
  intros. simpl in *. now contradict Hvas.
  intros.
  simpl in *.
  case_eq (StateLib.Level.eqb level1 fstLevel); intros . rewrite H in *.
  - contradict Hvas. 
    apply levelEqBEqNatTrue in H. subst.
    unfold not.
    intros. apply beq_nat_false in H.  contradict H. rewrite H0. reflexivity.
  - rewrite H in *.
    clear H. 
    case_eq (StateLib.readPhyEntry root1 (StateLib.getIndexOfAddr va1 level1) (memory s)) ;
    [intros p Hread1 | intros Hread1];
    rewrite Hread1 in *; [ | inversion Htableroot1].   
    case_eq (StateLib.readPhyEntry root2 (StateLib.getIndexOfAddr va2 level1) (memory s) );
    [intros p0 Hread2 | intros Hread2];
    rewrite Hread2 in *; [ | inversion Htableroot2].
    case_eq (defaultPage =? p); intros Hnull1;
    rewrite Hnull1 in *.
    inversion Htableroot1.
    subst. now contradict Hnotnull1.
    case_eq (defaultPage =? p0); intros Hnull2;
    rewrite Hnull2 in *.
    inversion Htableroot2.
    subst. now contradict Hnotnull2.
    case_eq(StateLib.Level.pred level1); [intros pred Hpred | intros Hpred];  rewrite Hpred in *; 
    [ | inversion Htableroot1].     
    case_eq (StateLib.getIndexOfAddr va1 level1 =? StateLib.getIndexOfAddr va2 level1);
            intros Hidx;
            rewrite Hidx in Hvas; trivial. 
    * generalize (IHn (n0 -1) p p0 table1 table2 pred va1 va2 stop); clear IHn; intros IHn.
      assert (StateLib.Level.eqb level1 fstLevel = true \/ StateLib.Level.eqb level1 fstLevel = false).
      { unfold StateLib.Level.eqb.
        rewrite NPeano.Nat.eqb_eq.  rewrite NPeano.Nat.eqb_neq.
        omega. }
      destruct H.
      { apply levelEqBEqNatTrue in H. subst.
        unfold StateLib.Level.pred in Hpred.
        unfold fstLevel in Hpred.
        unfold CLevel in Hpred.
        case_eq (lt_dec 0 nbLevel ); intros;
        rewrite H in Hpred; [simpl in *;inversion Hpred |
        assert (0 < nbLevel) by apply nbLevelNotZero;
        now contradict H1]. }
      { apply IHn;trivial; try omega; clear IHn.
        + apply nodupLevelMinus1  with root1 (StateLib.getIndexOfAddr va1 level1); trivial.
          apply beq_nat_false in Hnull1.
          unfold not. intros.
          contradict Hnull1. subst. trivial.
        + apply nodupLevelMinus1  with root2 (StateLib.getIndexOfAddr va2 level1); trivial.
          apply beq_nat_false in Hnull2.
          unfold not. intros.
          contradict Hnull2. subst. trivial.
        + destruct Hlevel as [(Hlevel& Hroot) | Hlevel ].
          - left. 
            split.
            apply levelPredMinus1 in Hpred; trivial.
            unfold CLevel in Hpred. 
            case_eq(lt_dec (level1 - 1) nbLevel ); intros;
            rewrite H1 in Hpred.
            destruct level1. simpl in *.
            destruct pred.
            inversion Hpred. subst.
            apply levelEqBEqNatFalse0 in H.
            simpl in *.
            clear Htableroot2 Htableroot1 Hvas Hidx
            Hread2  Hread1 HNoDup2 HNoDup1
            Hnull1 Hnull2 Hnotnull2 Hnotnull1 Hroot2 Hroot1.
            unfold CLevel in *.
            case_eq (lt_dec (n0 - 1) nbLevel); 
            intros; rewrite H2 in *.
            simpl in *.
            case_eq (lt_dec (n0 - 1 - 1) nbLevel);
            intros.
            inversion Hlevel. subst.
            assert(Hl0 = ADT.CLevel_obligation_1 (n0 - 1 - 1) l2 ) by apply proof_irrelevance.
            subst. reflexivity. 
            simpl in *. omega. omega.
            destruct level1.
            simpl in *.
            omega.
            subst.
            apply beq_nat_true in Hidx.
            destruct (StateLib.getIndexOfAddr va2 (CLevel (n0 - 1))).
            destruct (StateLib.getIndexOfAddr va1 (CLevel (n0 - 1))).
            simpl in *.
            subst. assert (Hi = Hi0) by apply proof_irrelevance.
            subst. rewrite Hread1 in Hread2.
            inversion Hread2. trivial.
          - destruct Hlevel as (Hlevellt &  [(Hlevel & Hll) | Hlevel ]).
            * right. split.
              { apply levelPredMinus1 in Hpred; trivial.
                unfold CLevel in Hpred. 
                case_eq(lt_dec (level1 - 1) nbLevel ); intros;
                rewrite H1 in Hpred.
                destruct level1. simpl in *.
                inversion Hpred. subst.
                apply levelEqBEqNatFalse0 in H.
                simpl in *.
                clear H2 Htableroot2 Htableroot1 Hvas Hidx
                Hread2  Hread1 Hlevel HNoDup2 HNoDup1 H0 
                Hnull1 Hnull2 Hnotnull2 Hnotnull1 Hroot2 Hroot1.
                unfold CLevel in *.
                case_eq (lt_dec (n0 - 1) nbLevel); 
                intros; rewrite H0 in *.
                simpl in *.
                case_eq (lt_dec (n0 - 1 - 1) nbLevel);
                intros.
                simpl in *.
                  
                  omega. omega.  
                case_eq (lt_dec (n0 - 1 - 1) nbLevel);
                intros.
                simpl in *. omega. omega.
                destruct level1. simpl in *. omega. }
              { assert (n0 <= 1 \/ n0 > 1) as Hn0. omega.
                destruct Hn0.
                apply levelEqBEqNatFalse0 in H.
                assert (CLevel
                (n0 - 1) > 1).
                omega.
                contradict H1.
                unfold CLevel in Hlevellt, H2.
                case_eq ( lt_dec (n0 - 1) nbLevel); intros;  rewrite H1 in *;
                simpl in *. omega.
                apply le_lt_or_eq in Hnbl.
                destruct Hnbl.
                omega.
                assert (n0 > 0).
                assert (0 < nbLevel) by apply nbLevelNotZero.
                omega.
                omega.
                left. split. 
                apply inclDisjoint with (getIndirectionsAux root1 s n0) (getIndirectionsAux root2 s n0); trivial.
                apply inclGetIndirectionsAuxMinus1 with (StateLib.getIndexOfAddr va1 level1); trivial.
                apply inclGetIndirectionsAuxMinus1 with (StateLib.getIndexOfAddr va2 level1); trivial.
                assert (In p (getIndirectionsAux root1 s n0) ) as Hp.
                apply readPhyEntryInGetIndirectionsAux; trivial.
                apply beq_nat_false in Hnull1. unfold not. contradict Hnull1.
                subst. trivial. 
                apply readPhyEntryInGetTablePages with (StateLib.getIndexOfAddr va1 level1); trivial.
                destruct (StateLib.getIndexOfAddr va1 level1 ); simpl in *; trivial.
                apply beq_nat_false in Hnull1. unfold not. contradict Hnull1.
                subst. trivial.
                assert ((StateLib.getIndexOfAddr va1 level1) = (CIndex (StateLib.getIndexOfAddr va1 level1))).
                symmetry. apply CIndexEq. rewrite <- H2. assumption.
                generalize(Hlevel p  Hp); intros Hpage0.
                assert (In p0 (getIndirectionsAux root2 s n0) ) as Hp0.
                apply readPhyEntryInGetIndirectionsAux; trivial.
                apply beq_nat_false in Hnull2. unfold not. contradict Hnull2.
                subst. trivial. 
                apply readPhyEntryInGetTablePages with (StateLib.getIndexOfAddr va2 level1); trivial.
                destruct (StateLib.getIndexOfAddr va2 level1 ); simpl in *; trivial.
                apply beq_nat_false in Hnull2. unfold not. contradict Hnull2.
                subst. trivial.
                assert ((StateLib.getIndexOfAddr va2 level1) = (CIndex (StateLib.getIndexOfAddr va2 level1))) as Hcidx.
                symmetry. apply CIndexEq. rewrite <- Hcidx. assumption.
                destruct (getIndirectionsAux root2 s n0). simpl in *. now contradict Hp0.
                simpl in *. unfold not in *.
                intros. apply Hpage0.
                destruct Hp0. subst. left. trivial.
                subst.
                right; trivial. }
            * right. split.
              apply levelPredMinus1 in Hpred; trivial.
              unfold CLevel in Hpred. 
              case_eq(lt_dec (level1 - 1) nbLevel ); intros;
              rewrite H1 in Hpred.
              destruct level1. simpl in *.
              inversion Hpred. subst.
              apply levelEqBEqNatFalse0 in H.
              simpl in *.
              clear H2 Htableroot2 Htableroot1 Hvas Hidx
              Hread2  Hread1 HNoDup2 HNoDup1 H0 
              Hnull1 Hnull2 Hnotnull2 Hnotnull1 Hroot2 Hroot1.
              unfold CLevel in *.
              case_eq (lt_dec (n0 - 1) nbLevel); 
              intros; rewrite H0 in *.
              simpl in *.
              case_eq (lt_dec (n0 - 1 - 1) nbLevel);
              intros.
              simpl in *. omega. omega.  
              case_eq (lt_dec (n0 - 1 - 1) nbLevel);
              intros;
              simpl in *. contradict H0. omega. omega.
              destruct level1. simpl in *. omega.
              right. 
              subst.
              apply beq_nat_true in Hidx.
              destruct (StateLib.getIndexOfAddr va2 level1).
              destruct (StateLib.getIndexOfAddr va1 level1).
              simpl in *.
              subst. assert (Hi = Hi0) by apply proof_irrelevance.
              subst. rewrite Hread1 in Hread2.
              inversion Hread2. trivial.  
        + apply beq_nat_false in Hnull1.
          unfold not. intros.
          contradict Hnull1. subst. trivial.
        + apply beq_nat_false in Hnull2.
          unfold not. intros.
          contradict Hnull2. subst. trivial. }
    * clear IHn. 
      left. clear stop0 stop (* Hstop *) Hs Hvas . 
      destruct Hlevel as [(Hlevel& Hroot) | (Hlevel& [(Hroot & Heq) | Hroot] ) ]; subst.
      { assert (n0 <= 1 \/ n0 > 1) as Hn0. omega.
        destruct Hn0 as [Hn0 | Hn0].
        + assert(n0 = 0 \/ n0 =1) as Hn01. omega.
          destruct Hn01;subst;  simpl in *;
          unfold StateLib.Level.pred in *; [
          case_eq(gt_dec (CLevel 0) 0 ); intros g Hnb0;rewrite Hnb0 in Hpred;
          [ | now contradict Hpred];
          unfold CLevel in g |]. 
          case_eq (lt_dec 0 nbLevel); intros nbl0 Hnbl0;
          [ |
          assert(0 < nbLevel) by apply nbLevelNotZero; omega].
          clear Hpred Hnb0. 
          rewrite Hnbl0 in *; simpl in *.  now contradict g.
          case_eq(gt_dec (CLevel 0) 0 ); intros g Hnb0;rewrite Hnb0 in Hpred;
          [ | 
          now contradict Hpred].
          unfold CLevel in g.
          case_eq (lt_dec 0 nbLevel); intros nbl0 Hnbl0; [ |
          assert(0 < nbLevel) by apply nbLevelNotZero; omega].
          clear Hpred Hnb0. 
          rewrite Hnbl0 in *; simpl in *.  now contradict g.
       + assert( p0 <> p).
          { apply getTablePagesNoDup with root2 (StateLib.getIndexOfAddr va2 (CLevel (n0 - 1)))
          (StateLib.getIndexOfAddr va1 (CLevel (n0 - 1))) s; trivial.  
          destruct (StateLib.getIndexOfAddr va2 (CLevel (n0 - 1))). simpl in *; trivial.
          destruct (StateLib.getIndexOfAddr va1 (CLevel (n0 - 1))). simpl in *; trivial.
          destruct n0; [now contradict Hn0 |].
          simpl in HNoDup2. apply NoDup_cons_iff in HNoDup2.
          destruct HNoDup2 as (_ & HNoDup2).
          apply getTablePagesNoDupFlatMap  with n0; trivial. omega.
          assert (H :(CIndex (StateLib.getIndexOfAddr va2 (CLevel (n0 - 1)))) =
          (StateLib.getIndexOfAddr va2 (CLevel (n0 - 1)))).
          apply CIndexEq. rewrite H; trivial. 
          assert (H2 :(CIndex (StateLib.getIndexOfAddr va1 (CLevel (n0 - 1)))) =
          (StateLib.getIndexOfAddr va1 (CLevel (n0 - 1)))).
          apply CIndexEq. rewrite H2. trivial.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in Hidx.
          apply beq_nat_false in Hidx. now contradict Hidx.
          apply beq_nat_false in Hnull1.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *.
          now contradict Hnull1.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *.
          apply beq_nat_false in Hnull2. now contradict Hnull2. }
        assert( disjoint (getIndirectionsAux p s (n0 -1)) 
       (getIndirectionsAux p0 s (n0 -1))) as Hdisjoint.
         apply disjointGetIndirectionsAuxMiddle with root2
         (StateLib.getIndexOfAddr va2 (CLevel (n0 - 1)))
         (StateLib.getIndexOfAddr va1 (CLevel (n0 - 1))) ; trivial. 
         assert (In table1 (getIndirectionsAux  p s (n0 -1))) as Htbl1p.
         apply getIndirectionInGetIndirectionAuxMinus1 with va1 pred n (CLevel (n0 - 1)); trivial.
         unfold CLevel.
         case_eq( lt_dec (n0 - 1) nbLevel). intros. simpl.
         omega.
         intros.
         contradict H1. omega.
         assert (In table2 (getIndirectionsAux  p0 s (n0 -1))) as Htb2p0.
         apply getIndirectionInGetIndirectionAuxMinus1 with va2 pred n (CLevel (n0 - 1)); trivial.
         unfold CLevel.
         case_eq( lt_dec (n0 - 1) nbLevel). intros. simpl.
         omega.
         intros.
         contradict H1. omega.
         unfold disjoint in *.
         apply Hdisjoint in Htbl1p.
         unfold not. intros.
         apply Htbl1p. subst.
         assumption. }
      { assert (n0 <= 1 \/ n0 > 1) as Hn0. omega.
        destruct Hn0 as [Hn0 | Hn0].
        + assert(n0 = 0 \/ n0 =1) as Hn01. omega.
          destruct Hn01;subst;  simpl in *;
          destruct level1; simpl in *;
          unfold CLevel in Hlevel; 
          case_eq ( lt_dec 0 nbLevel); intros; rewrite H in *;
          simpl in *; omega.
        +  assert (level1 > 0). 
             {unfold StateLib.Level.pred in *.
         case_eq (  gt_dec level1 0) ; intros;
         rewrite H in *.
         inversion Hpred.
         destruct pred.
         destruct level1. simpl in *.
         inversion H2. omega.
         inversion Hpred.
         }
        assert (In table1 (getIndirectionsAux  p s (n0 -1))) as Htbl1p.
         apply getIndirectionInGetIndirectionAuxMinus1 with va1 pred n level1; trivial.
         omega.
          assert (In table2 (getIndirectionsAux  p0 s (n0 -1))) as Htbl2p0.
         apply getIndirectionInGetIndirectionAuxMinus1 with va2 pred n level1; trivial.
          omega.

          apply inclGetIndirectionsAuxMinus1 with n0 root1 (StateLib.getIndexOfAddr va1 level1)
           p s in Hread1; trivial.
           apply inclGetIndirectionsAuxMinus1 with n0 root2 (StateLib.getIndexOfAddr va2 level1)
           p0 s in Hread2; trivial. 
           unfold incl, disjoint in *.
           apply Hread1 in Htbl1p.
           apply Hread2 in Htbl2p0.
           apply Hroot in Htbl1p.
           unfold not. intros.
           apply Htbl1p. subst.
           assumption.   
            }
        { assert (n0 <= 1 \/ n0 > 1) as Hn0. omega.
        destruct Hn0 as [Hn0 | Hn0].
        + assert(n0 = 0 \/ n0 =1) as Hn01. omega.
        destruct Hn01;subst;  simpl in *;
          destruct level1; simpl in *;
          unfold CLevel in Hlevel; 
          case_eq ( lt_dec 0 nbLevel); intros; rewrite H in *;
          simpl in *; omega.
          
       + assert( p0 <> p).
         { apply getTablePagesNoDup with root2 (StateLib.getIndexOfAddr va2 level1)
          (StateLib.getIndexOfAddr va1 level1) s; trivial.  
          destruct (StateLib.getIndexOfAddr va2 level1). simpl in *; trivial.
          destruct (StateLib.getIndexOfAddr va1 level1). simpl in *; trivial.
          destruct n0; [now contradict Hn0 |].
          simpl in HNoDup2. apply NoDup_cons_iff in HNoDup2.
          destruct HNoDup2 as (_ & HNoDup2).
          apply getTablePagesNoDupFlatMap  with n0; trivial. omega.
          assert (H :(CIndex (StateLib.getIndexOfAddr va2 level1)) =
          (StateLib.getIndexOfAddr va2 level1)).
          apply CIndexEq. rewrite H; trivial. 
          assert (H2 :(CIndex (StateLib.getIndexOfAddr va1 level1)) =
          (StateLib.getIndexOfAddr va1 level1)).
          apply CIndexEq. rewrite H2. trivial.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in Hidx.
          apply beq_nat_false in Hidx. now contradict Hidx.
          apply beq_nat_false in Hnull1.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *.
          now contradict Hnull1.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *.
          apply beq_nat_false in Hnull2. now contradict Hnull2. }
      assert( disjoint (getIndirectionsAux p s (n0 -1)) 
       (getIndirectionsAux p0 s (n0 -1))) as Hdisjoint.
         apply disjointGetIndirectionsAuxMiddle with root2
         (StateLib.getIndexOfAddr va2 level1)
         (StateLib.getIndexOfAddr va1 level1) ; trivial.
         assert (In table1 (getIndirectionsAux  p s (n0 -1))) as Htbl1p.
         apply getIndirectionInGetIndirectionAuxMinus1 with va1 pred n level1; trivial.
         unfold StateLib.Level.pred in *.
         case_eq (  gt_dec level1 0) ; intros;
         rewrite H1 in *.
         inversion Hpred.
         destruct pred.
         destruct level1. simpl in *.
         inversion H3. omega.
         inversion Hpred.
         omega.
         assert (In table2 (getIndirectionsAux  p0 s (n0 -1))) as Htb2p0.
         apply getIndirectionInGetIndirectionAuxMinus1 with va2 pred n level1; trivial.
         unfold StateLib.Level.pred in *.
         case_eq (  gt_dec level1 0) ; intros;
         rewrite H1 in *.
         inversion Hpred.
         destruct pred.
         destruct level1. simpl in *.
         inversion H3. omega.
         inversion Hpred.
         omega.
         unfold disjoint in *.
         apply Hdisjoint in Htbl1p.
         unfold not. intros.
         apply Htbl1p. subst.
         assumption. }
Qed. 
Lemma toApplyPageTablesOrIndicesAreDifferent idx1 idx2 va1 va2 (table1 table2 : page) 
currentPart currentPD level1 s: 
(defaultPage =? table1) = false -> (defaultPage =? table2) = false -> 
false = StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 level1 -> 
currentPart = currentPartition s -> 
consistency s -> 
StateLib.getIndexOfAddr va1 fstLevel = idx1 -> 
StateLib.getIndexOfAddr va2 fstLevel = idx2 -> 
(forall idx : index,
StateLib.getIndexOfAddr va1 fstLevel = idx ->
isPE table1 idx s /\ getTableAddrRoot table1 PDidx currentPart va1 s) -> 
(forall idx : index,
StateLib.getIndexOfAddr va2 fstLevel = idx ->
isPE table2 idx s /\ getTableAddrRoot table2 PDidx currentPart va2 s) -> 
nextEntryIsPP currentPart PDidx currentPD s -> 
Some level1 = StateLib.getNbLevel -> 
table1 <> table2 \/ idx1 <> idx2. 
Proof. 
 intros Hnotnull1 Hnotnull2 Hvas Hcurpart Hcons Hva1 Hva2 Htable1 Htable2 Hroot Hlevel.              
 rewrite <- Hva1.
  rewrite <- Hva2.
  apply Htable1 in Hva1.
  apply Htable2 in Hva2.
  unfold getTableAddrRoot in *.
  destruct Hva1 as (Hpe1 &_ & Htableroot1). 
  destruct Hva2 as (Hpe2 &_ & Htableroot2).
  generalize (Htableroot1 currentPD Hroot); clear Htableroot1;intros Htableroot1.
  generalize (Htableroot2 currentPD Hroot); clear Htableroot2;intros Htableroot2.
  destruct Htableroot1 as (nbl1 & Hnbl1 & stop1 & Hstop1 & Hind1). 
  destruct Htableroot2 as (nbl2 & Hnbl2 & stop2 & Hstop2 & Hind2).
  rewrite <- Hlevel in Hnbl1.
  inversion Hnbl1 as [Hi0]. 
  rewrite <- Hlevel in Hnbl2.
  inversion Hnbl2 as [Hi1 ].
  rewrite Hi1 in Hind2.
  rewrite Hi0 in Hind1.  
  rewrite Hi1 in Hstop2.
  rewrite Hi0 in Hstop1.
  rewrite <- Hstop2 in Hstop1.
  rewrite Hstop1 in Hind1.
  clear Hstop1 Hnbl2 Hnbl1 .
   apply  pageTablesOrIndicesAreDifferent with currentPD currentPD  
  level1 stop2 s; trivial. 
            unfold consistency in *.
  destruct Hcons.
  unfold partitionDescriptorEntry in *.
  assert (currentPartitionInPartitionsList s ) as Hpr by intuition.
  unfold currentPartitionInPartitionsList in *.
  subst.
  generalize (H  (currentPartition s)  Hpr); clear H; intros H.
  assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/ PDidx = sh3idx
  \/  PDidx   = PPRidx \/  PDidx   = PRidx) as Hpd 
  by auto.
  apply H in Hpd.
  destruct Hpd as (_ & _ & Hpd).
  destruct Hpd as (pd & Hrootpd & Hnotnul).
  move Hroot at bottom.
  move Hrootpd  at bottom.
  move Hnotnul at bottom.
  unfold nextEntryIsPP in Hroot , Hrootpd.
  destruct (StateLib.Index.succ PDidx).
  subst. 
  destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex); [
  | now contradict Hroot].
  destruct v; [  
  now contradict Hroot| now contradict Hroot | | now contradict Hroot | now contradict Hroot].
  subst. assumption. now contradict Hroot.
  unfold consistency in *.
  destruct Hcons.
  unfold partitionDescriptorEntry in *.
  assert (currentPartitionInPartitionsList s ) as Hpr by intuition.
  unfold currentPartitionInPartitionsList in *.
  subst.
  generalize (H  (currentPartition s)  Hpr); clear H; intros H.
  assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/ PDidx = sh3idx 
  \/ PDidx  = PPRidx \/ PDidx  = PRidx)  as Hpd 
  by auto.
  apply H in Hpd.
  destruct Hpd as (_ & _ & Hpd).
  destruct Hpd as (pd & Hrootpd & Hnotnul).
  move Hroot at bottom.
  move Hrootpd  at bottom.
  move Hnotnul at bottom.
  unfold nextEntryIsPP in Hroot , Hrootpd.
  destruct (StateLib.Index.succ PDidx).
  subst.
  destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex); [
  | now contradict Hroot].
  destruct v; [  
   now contradict Hroot| now contradict Hroot | | now contradict Hroot |
    now contradict Hroot].
  subst. assumption.
  now contradict Hroot.
  unfold consistency in Hcons.
  unfold noDupConfigPagesList in Hcons.
  unfold currentPartitionInPartitionsList in Hcons.
  destruct Hcons as (_ & _& _& _& Hcurprt & _ & Hdup). subst.
  apply Hdup with PDidx (currentPartition s); trivial. left. trivial.
  unfold consistency in Hcons.
  unfold noDupConfigPagesList in Hcons.
  unfold currentPartitionInPartitionsList in Hcons.
  destruct Hcons as (_ & _& _& _& Hcurprt & _ & Hdup). subst.
  apply Hdup with PDidx (currentPartition s); trivial. left. trivial.
  move Hlevel at bottom.
  unfold StateLib.getNbLevel in Hlevel.
   case_eq (gt_dec nbLevel 0 ); intros;
  rewrite H in Hlevel.
  rewrite Hstop2.
  inversion Hlevel.
  rewrite H1 in *. simpl.
  symmetry. assert( (nbLevel - 1 + 1)  = nbLevel).
  omega. rewrite H0.
  assumption.
  now contradict H.
  left. split.
  unfold StateLib.getNbLevel in *.
  move Hlevel at bottom.
  unfold CLevel.
  case_eq (gt_dec nbLevel 0); intros.
  rewrite H in Hlevel.
  inversion Hlevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel ); intros.
  subst.
  assert(MAL.getNbLevel_obligation_1 g  =  ADT.CLevel_obligation_1 (nbLevel - 1) l)
  by apply proof_irrelevance.
  rewrite H1. reflexivity. omega.
  assert (0 < nbLevel) by apply nbLevelNotZero. omega.
  trivial. 
  apply beq_nat_false in Hnotnull1.
  unfold not. intros.
  contradict Hnotnull1. subst. trivial.
  apply beq_nat_false in Hnotnull2.
  unfold not. intros.
  contradict Hnotnull2. subst. trivial.
Qed.

Lemma checkVAddrsEqualityWOOffsetPermut va1 va2 level1 : 
  StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 level1 = 
  StateLib.checkVAddrsEqualityWOOffset nbLevel va2 va1 level1. 
Proof.
  revert va1 va2 level1.
  induction nbLevel.
  simpl. trivial.
  simpl. intros.
  case_eq (StateLib.Level.eqb level1 fstLevel); intros.
  apply NPeano.Nat.eqb_sym.
  case_eq(StateLib.Level.pred level1);
  intros; trivial. 
  rewrite  NPeano.Nat.eqb_sym.
  case_eq (StateLib.getIndexOfAddr va2 level1 =? StateLib.getIndexOfAddr va1 level1); intros; trivial.
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
unfold getParent.
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