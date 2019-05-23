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
    This file contains the invariant of [createPartition]. 
    We prove that this PIP service preserves the isolation property *)
Require Import  Model.ADT Model.Hardware Core.Services Isolation
Consistency Invariants WeakestPreconditions Model.Lib StateLib
Model.MAL Lib InternalLemmas DependentTypeLemmas PropagatedProperties
Classical_Prop.
 Require Import Omega Bool  Coq.Logic.ProofIrrelevance List.
 Import List.ListNotations.

Lemma getPdMapMMUPage ( partition : page) entry s table idx phyVaChild r w e:
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->
StateLib.getPd partition
  (add table idx
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex ) = StateLib.getPd partition (memory s).
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

Lemma getFstShadowMapMMUPage partition table idx phyVaChild r w e s entry: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getFstShadow partition
  (add table idx
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex) =
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
 
Lemma getSndShadowMapMMUPage partition table idx phyVaChild r w e s entry: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getSndShadow partition
  (add table idx
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex) =
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


Lemma getConfigTablesLinkedListMapMMUPage partition table idx phyVaChild r w e s entry: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getConfigTablesLinkedList partition
  (add table idx
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex) =
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

Lemma getParentMapMMUPage ( partition : page) entry s table idx phyVaChild w r e:
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->
getParent partition
  (add table idx
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex) = getParent partition (memory s).
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
(* 
Lemma getIndirectionMapMMUPage p table idx phyVaChild r w e s entry a l stop:
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->
getIndirection p a l stop
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} =
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
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) ) in *.
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
Qed. *)

Lemma readPDflagMapMMUPage s entry phyVaChild r w e idx table pg i: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
 StateLib.readPDflag pg i
  (add table idx
     (PE
        {| read := r;
           write := w;
           exec := e;
           present := true;
           user := true;
           pa := phyVaChild |}) (memory s) beqPage beqIndex) = StateLib.readPDflag pg i (memory s).
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
 
Lemma readVirtualMapMMUPage s entry phyVaChild r w e idx table pg i: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
 StateLib.readVirtual pg i
  (add table idx
     (PE
        {| read := r;
           write := w;
           exec := e;
           present := true;
           user := true;
           pa := phyVaChild |}) (memory s) beqPage beqIndex) = StateLib.readVirtual pg i (memory s).
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
 Lemma nextEntryIsPPMapMMUPage table idx table1 idx1 phyVaChild r w e res s (entry : Pentry) : 
lookup table1 idx1  (memory s) beqPage beqIndex = Some (PE entry) ->
nextEntryIsPP table idx res s -> nextEntryIsPP table idx res 
{|
currentPartition := currentPartition s;
memory := add table1 idx1 
      (PE
         {| read := r;
           write := w;
           exec := e;
           present := true;
           user := true;
           pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
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

(* Lemma readPhyEntryMapMMUPage s entry phyVaChild r w e idx table pg i: 
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
Qed. *)

Lemma isVAMapMMUPage table1 table2 idx1 idx2 phyVaChild e r w entry s : 
lookup table1 idx1 (memory s) beqPage beqIndex =
Some (PE entry) -> 
isVA table2 idx2 s ->
isVA table2 idx2
{|
currentPartition := currentPartition s;
memory := add table1 idx1
 (PE {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}. 
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
Lemma isVEMapMMUPage table1 table2 idx1 idx2 phyVaChild e r w entry s : 
lookup table1 idx1 (memory s) beqPage beqIndex =
Some (PE entry) -> 
isVE table2 idx2 s ->
isVE table2 idx2
{|
currentPartition := currentPartition s;
memory := add table1 idx1
 (PE {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}. 
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

Lemma readPhysicalMapMMUPage s entry phyVaChild r w e idx table pg i: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
 StateLib.readPhysical pg i
  (add table idx
     (PE
        {| read := r;
           write := w;
           exec := e;
           present := true;
           user := true;
           pa := phyVaChild |}) (memory s) beqPage beqIndex) = StateLib.readPhysical pg i (memory s).
Proof.     
intros Hentry.
unfold StateLib.readPhysical.
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

Lemma readVirEntryMapMMUPage p table idx idx1 s entry phyVaChild r w e :
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.readVirEntry p idx1 (memory s) =
StateLib.readVirEntry p idx1
(add table idx
 (PE
    {| read := r;
           write := w;
           exec := e;
           present := true;
           user := true;
           pa := phyVaChild |}) (memory s) beqPage beqIndex).
Proof.
intros Hentry.
unfold StateLib.readVirEntry.
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


Lemma readAccessibleMapMMUPage table1 table2 idx1 idx2  phyVaChild r w e s :
table1 <> table2 \/ idx1 <> idx2 -> 
 StateLib.readAccessible table1 idx1
           (add table2 idx2
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex) = 
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
Lemma readPhyEntryMapMMUPage table1 table2 idx1 idx2  entry phyVaChild
r w e s : 
(table2 <> table1 \/ idx2 <> idx1) -> 
lookup table1 idx1(memory s) beqPage beqIndex = Some (PE entry) ->
StateLib.readPhyEntry table2 idx2 (memory s) = 
StateLib.readPhyEntry table2 idx2 
( add table1 idx1
    (PE
       {|
                   read := r;
                   write := w;
                   exec := e;
                   present := true;
                   user := true;
                   pa := phyVaChild |}) (memory s) beqPage beqIndex ).
Proof.
intros Hnoteq Hlookup .
unfold StateLib.readPhyEntry  in *.
cbn in *.
case_eq (beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex ); intros Hpairs.
{  apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
   subst. intuition. }
{ apply beqPairsFalse in Hpairs.
  assert (lookup  table2 idx2  (removeDup table1 idx1 (memory s) beqPage beqIndex)
  beqPage beqIndex = lookup  table2 idx2 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory. reflexivity. }
Qed.

   Lemma getIndirectionMapMMUPage1 s a (phyVaChild ptVaChildpd pd:page) e r w idxvaChild  entry level :  
   (forall (stop : nat) (tbl : page),
 getIndirection pd a level stop s = Some tbl ->
 (defaultPage =? tbl) = false -> tbl <> ptVaChildpd) ->
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) ->
pd <> defaultPage ->
getIndirection pd a level (nbLevel - 1) s =
getIndirection pd a level (nbLevel - 1) {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
                     Proof. 
                     
                     
   revert pd level.
   induction (nbLevel - 1).
   simpl;trivial.
   simpl in *.
   intros pd level  Hmykey Hlookup Hpdnotnull.
    case_eq( StateLib.Level.eqb level fstLevel);intros;trivial.
    assert(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a level)
    (add ptVaChildpd idxvaChild
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a level)
    (memory s)). symmetry.
    apply readPhyEntryMapMMUPage with entry;trivial.
    left.
    generalize (Hmykey 0 pd);clear Hmykey;intros Hmykey. 
    simpl in *. 
    apply Hmykey;trivial.
    apply NPeano.Nat.eqb_neq.
    unfold not;intros.
    subst.
    destruct defaultPage;destruct pd;simpl in *;subst.
    contradict Hpdnotnull.
    f_equal. apply  proof_irrelevance.
    rewrite H0.
    case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a level) (memory s));intros;trivial.
    case_eq(defaultPage =? p);intros;trivial.
    case_eq(StateLib.Level.pred level );intros;trivial.
    apply IHn;trivial.
    intros.
    apply Hmykey with (S stop).
    simpl.    
      
     rewrite H3 in *.
     rewrite H.
     rewrite H1.
     rewrite H2;trivial.
     trivial.
     apply beq_nat_false in H2.
     unfold not;intros.
     subst. now contradict H2.
     Qed.
   Lemma getIndirectionMapMMUPage11 s a (phyVaChild ptVaChildpd pd:page) e r w idxvaChild  entry level stop1:  
   (forall (stop : nat) (tbl : page),
 getIndirection pd a level stop s = Some tbl ->
 (defaultPage =? tbl) = false -> tbl <> ptVaChildpd) ->
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) ->
pd <> defaultPage ->
getIndirection pd a level stop1 s =
getIndirection pd a level stop1 {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
                     Proof. 
                     
                     
   revert pd level.
   induction stop1.
   simpl;trivial.
   simpl in *.
   intros pd level  Hmykey Hlookup Hpdnotnull.
    case_eq( StateLib.Level.eqb level fstLevel);intros;trivial.
    assert(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a level)
    (add ptVaChildpd idxvaChild
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a level)
    (memory s)). symmetry.
    apply readPhyEntryMapMMUPage with entry;trivial.
    left.
    generalize (Hmykey 0 pd);clear Hmykey;intros Hmykey. 
    simpl in *. 
    apply Hmykey;trivial.
    apply NPeano.Nat.eqb_neq.
    unfold not;intros.
    subst.
    destruct defaultPage;destruct pd;simpl in *;subst.
    contradict Hpdnotnull.
    f_equal. apply  proof_irrelevance.
    rewrite H0.
    case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a level) (memory s));intros;trivial.
    case_eq(defaultPage =? p);intros;trivial.
    case_eq(StateLib.Level.pred level );intros;trivial.
    apply IHstop1;trivial.
    intros.
    apply Hmykey with (S stop).
    simpl.    
      
     rewrite H3 in *.
     rewrite H.
     rewrite H1.
     rewrite H2;trivial.
     trivial.
     apply beq_nat_false in H2.
     unfold not;intros.
     subst. now contradict H2.
     Qed.

Lemma checkChildMapMMUPage  a s ptVaChildpd idxvaChild phyVaChild r w e  pdChildphy
presentvaChild vaChild phyDescChild level entry:
noDupConfigPagesList s -> 
partitionDescriptorEntry s -> 
configTablesAreDifferent s -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
Some level = StateLib.getNbLevel ->
forall part, In part (getPartitions multiplexer s) -> 
checkChild part level s a =
checkChild part level {|
     currentPartition := currentPartition s;
     memory := add ptVaChildpd idxvaChild
                 (PE
                    {|
                    read := r;
                    write := w;
                    exec := e;
                    present := true;
                    user := true;
                    pa := phyVaChild |}) (memory s) beqPage beqIndex |} a.
Proof.
intros Hnodup2 Hpde Hnodupconfg Hlookup Hnotpresent Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild Hlevel part Hpart.
unfold checkChild.
simpl.
assert(Hgetsh1 : forall part, getFstShadow part (memory s) =
 getFstShadow part
    (add ptVaChildpd idxvaChild
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex)).
{ intros. symmetry.
  apply getFstShadowMapMMUPage with entry;trivial. }
rewrite <- Hgetsh1. clear Hgetsh1.
case_eq(getFstShadow part (memory s));[intros sh1 Hsh1 | intros Hsh1];trivial.

assert(Hind : getIndirection sh1 a level (nbLevel - 1) s  = 
getIndirection sh1 a level (nbLevel - 1) {|
    currentPartition := currentPartition s;
    memory := add ptVaChildpd idxvaChild
                (PE
                   {|
                   read := r;
                   write := w;
                   exec := e;
                   present := true;
                   user := true;
                   pa := phyVaChild |}) (memory s) beqPage beqIndex |}).
{                   
 assert(Htrue : getMappedPage pdChildphy s vaChild = SomeDefault).
  {  apply getMappedPageNotPresent with ptVaChildpd phyDescChild;intuition.
    + subst;trivial.
    + apply negb_true_iff in Hnotpresent.
      subst;trivial. } 
                   
unfold getTableAddrRoot in *. 
destruct Htblroot as (_ & Hroot).
assert(Hparts : part = phyDescChild \/ part <> phyDescChild) by apply pageDecOrNot.
destruct Hparts as [Hparts | Hparts];subst.
+ unfold noDupConfigPagesList in *. 
apply getIndirectionMapMMUPage1 with entry;trivial.
- intros. 
  assert(Hdisjoint: disjoint (getIndirections pdChildphy s) (getIndirections sh1 s)). 
  apply Hnodup2 in Hpart.
  unfold getConfigPages in *.
  apply NoDup_cons_iff in Hpart as(_ & Hpart).
  unfold getConfigPagesAux in *.
  rewrite nextEntryIsPPgetPd in *. 
  rewrite Hpdchild in Hpart.
  rewrite Hsh1 in *.
  case_eq (getSndShadow phyDescChild (memory s));[intros sh2 Hsh2 | intros Hsh2] ;
  rewrite Hsh2 in *.
  case_eq (getConfigTablesLinkedList phyDescChild (memory s));[intros ll Hll| intros Hll] ;
  rewrite Hll in *.
  rewrite NoDupSplitInclIff in Hpart.
  destruct Hpart as (Hpart1 & Hpart2).
  clear Hnodup2.
  unfold disjoint in *. 
  intros x Hdis1.
   
  apply Hpart2 in Hdis1.
  intuition.
  clear Hnodup2.
  assert(False).
  apply getConfigTablesRootNotNone with phyDescChild s;trivial.
  intuition.
  assert(False).
  apply sh2PartNotNone with phyDescChild s;trivial.
  intuition.
  assert(Hin1 : In  ptVaChildpd (getIndirections pdChildphy s)). 
  unfold getIndirections.
  assert(Hpdchild1 : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Hroot in Hpdchild.
  destruct Hpdchild as (nbL & HnbL & stop1 & Hstop & Hind).
   apply getIndirectionInGetIndirections with vaChild nbL stop1;trivial.
  assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in Hdefaut.
  unfold not;intros;subst.
  now contradict Hdefaut.
  apply getNbLevelLe in HnbL;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
  assert(Hin2 : In  tbl (getIndirections sh1 s)). 
  unfold getIndirections.
  apply getIndirectionInGetIndirections with a level stop;trivial.
   assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in H0.
  unfold not;intros;subst.
  now contradict H0.
  apply getNbLevelLe in Hlevel;trivial.
  
  apply sh1PartNotNull with phyDescChild s;trivial.
  apply nextEntryIsPPgetFstShadow ;trivial.
  unfold not;intros.
  subst.
  unfold disjoint in *.
  unfold not in *.
  apply Hdisjoint with ptVaChildpd;trivial.

-   apply sh1PartNotNull with phyDescChild s;trivial.
  apply nextEntryIsPPgetFstShadow ;trivial. 
+ apply getIndirectionMapMMUPage1 with entry;trivial.
  intros.
  assert(configTablesAreDifferent s ) by trivial.
  assert(In tbl (getConfigPages part s)).
  unfold getConfigPages.
  simpl.
  right.
  apply inGetIndirectionsAuxInConfigPagesSh1 with sh1;trivial.
  apply getIndirectionInGetIndirections with a level stop;trivial.
   assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in H0.
  unfold not;intros;subst.
  now contradict H0.
  apply getNbLevelLe in Hlevel;trivial.
  apply sh1PartNotNull with part s;trivial.
  apply nextEntryIsPPgetFstShadow ;trivial. 
  assert(In ptVaChildpd (getConfigPages phyDescChild s)).
  unfold getConfigPages.
  simpl.
  right.
  apply inGetIndirectionsAuxInConfigPagesPD with pdChildphy;trivial.
  
  unfold getIndirections.
  assert(Hpdchild1 : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Hroot in Hpdchild.
  destruct Hpdchild as (nbL & HnbL & stop1 & Hstop & Hind).
   apply getIndirectionInGetIndirections with vaChild nbL stop1;trivial.
  assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in Hdefaut.
  unfold not;intros;subst.
  now contradict Hdefaut.
  apply getNbLevelLe in HnbL;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
 apply nextEntryIsPPgetPd;trivial.
  unfold configTablesAreDifferent in *.
  unfold disjoint in *.
  unfold not in *.
  intros. 
  subst. 
  apply H1 with part phyDescChild ptVaChildpd;trivial.
  apply sh1PartNotNull with part s;trivial.
  apply nextEntryIsPPgetFstShadow;trivial. }

+ rewrite <- Hind. clear Hind.
case_eq(getIndirection sh1 a level (nbLevel - 1) s);intros;trivial.
assert(Hpdflag : StateLib.readPDflag p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPDflag p (StateLib.getIndexOfAddr a fstLevel)
      (add ptVaChildpd idxvaChild
         (PE
            {|
            read := r;
            write := w;
            exec := e;
            present := true;
            user := true;
            pa := phyVaChild |}) (memory s) beqPage beqIndex)).
            symmetry. 
            apply readPDflagMapMMUPage with entry;trivial.
rewrite Hpdflag.
trivial.                    
Qed.

Lemma getPdsVAddrMapMMUPage   s ptVaChildpd idxvaChild phyVaChild r w e  pdChildphy
presentvaChild vaChild phyDescChild level entry:
noDupConfigPagesList s -> 
partitionDescriptorEntry s ->
configTablesAreDifferent s -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
Some level = StateLib.getNbLevel -> 
forall part, In part (getPartitions multiplexer s) -> 
getPdsVAddr part level getAllVAddrWithOffset0 s = getPdsVAddr part level getAllVAddrWithOffset0
     {|
     currentPartition := currentPartition s;
     memory := add ptVaChildpd idxvaChild
                 (PE
                    {|
                    read := r;
                    write := w;
                    exec := e;
                    present := true;
                    user := true;
                    pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hnodup Hpde Hconfigdiff Hlookup Hnotpresent Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild Hlevel.
unfold getPdsVAddr.
induction getAllVAddrWithOffset0;simpl;trivial.
intros.
assert(Hcheck :  checkChild part level
    {|
    currentPartition := currentPartition s;
    memory := add ptVaChildpd idxvaChild
                (PE
                   {|
                   read := r;
                   write := w;
                   exec := e;
                   present := true;
                   user := true;
                   pa := phyVaChild |}) (memory s) beqPage beqIndex |} a =
                   checkChild part level s a). 
  symmetry. apply checkChildMapMMUPage  with pdChildphy
presentvaChild vaChild phyDescChild entry;trivial.
case_eq(checkChild part level s a);intros.
rewrite Hcheck.
case_eq(checkChild part level s a);intros.
f_equal.
apply IHl;trivial. 
rewrite H1 in *.
now contradict H0.
rewrite Hcheck;trivial.
rewrite H0.
apply IHl;trivial.
Qed.

Lemma isPEMapMMUPage table idx table1 idx1 s entry phyVaChild r w e :   
lookup table1 idx1 (memory s) beqPage beqIndex = Some (PE entry) -> 
isPE table idx s -> 
isPE table idx
{|
    currentPartition := currentPartition s;
    memory := add table1 idx1
                (PE
                   {|
                   read := r;
                   write := w;
                   exec := e;
                   present := true;
                   user := true;
                   pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
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

Lemma nextEntryIsPPMapMMUPage' table idx table1 idx1 phyVaChild r w e res s (entry : Pentry) : 
nextEntryIsPP table idx res 
{|
currentPartition := currentPartition s;
memory := add table1 idx1 
      (PE
          {|
                   read := r;
                   write := w;
                   exec := e;
                   present := true;
                   user := true;
                   pa := phyVaChild |}) (memory s) beqPage beqIndex |} -> nextEntryIsPP table idx res s .
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


Lemma readPresentMapMMUPage table1 table2 idx1 idx2  entry phyVaChild
r w e s : 
(table2 <> table1 \/ idx2 <> idx1) -> 
lookup table1 idx1(memory s) beqPage beqIndex = Some (PE entry) ->
StateLib.readPresent table2 idx2 (memory s) = 
StateLib.readPresent table2 idx2 
( add table1 idx1
    (PE
       {|
                   read := r;
                   write := w;
                   exec := e;
                   present := true;
                   user := true;
                   pa := phyVaChild |}) (memory s) beqPage beqIndex ).
Proof.
intros Hnoteq Hlookup .
unfold StateLib.readPresent  in *.
cbn in *.
case_eq (beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex ); intros Hpairs.
{  apply beqPairsTrue in Hpairs.
  destruct Hpairs as (Htable & Hidx).
   subst. intuition. }
{ apply beqPairsFalse in Hpairs.
  assert (lookup  table2 idx2  (removeDup table1 idx1 (memory s) beqPage beqIndex)
  beqPage beqIndex = lookup  table2 idx2 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
  rewrite Hmemory. reflexivity. }
Qed.
 Lemma getIndirectionMapMMUPage 
  s ptVaChildpd phyVaChild r w e pdChildphy vaChild entry nbL:
  


  StateLib.readPhyEntry ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  (memory s) = Some defaultPage -> 
StateLib.readPhyEntry ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  (add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex ) = Some phyVaChild ->
lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s)
  beqPage beqIndex = Some (PE entry) ->
getIndirection pdChildphy vaChild nbL (nbL + 1) s = Some ptVaChildpd ->
 (defaultPage =? ptVaChildpd) = false  -> 
getIndirection pdChildphy vaChild nbL (nbL + 1) {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} = Some ptVaChildpd
. Proof. 
  revert pdChildphy. generalize nbL at 1 3.
  induction (nbL + 1);simpl;
(*   intros;trivial. *)
  intros nbL0 pdChildphy Htrue1 Htrue2 Hlookup Hind1;trivial.
  destruct (StateLib.Level.eqb nbL0 fstLevel);intros;trivial.
  - case_eq( StateLib.readPhyEntry pdChildphy
            (StateLib.getIndexOfAddr vaChild nbL0) (memory s));intros.
  * rewrite H0 in *. 
  case_eq(defaultPage =? p);intros.
  rewrite H1 in *.
  apply beq_nat_false in H. 
  inversion Hind1;subst.
  now contradict H.
  rewrite H1 in *. 

  assert(StateLib.readPhyEntry pdChildphy (StateLib.getIndexOfAddr vaChild nbL0)
    (add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pdChildphy (StateLib.getIndexOfAddr vaChild nbL0)
    (memory s)).
 clear Hind1 IHn.
 assert(Hor : (pdChildphy <>  ptVaChildpd \/ (StateLib.getIndexOfAddr vaChild fstLevel) <> 
 (StateLib.getIndexOfAddr vaChild nbL0)) \/ ( pdChildphy =  ptVaChildpd /\
 (StateLib.getIndexOfAddr vaChild fstLevel) = 
 (StateLib.getIndexOfAddr vaChild nbL0))). 
 { clear. assert((pdChildphy = ptVaChildpd /\
StateLib.getIndexOfAddr vaChild fstLevel =
StateLib.getIndexOfAddr vaChild nbL0 ) \/  
~ (pdChildphy = ptVaChildpd /\
StateLib.getIndexOfAddr vaChild fstLevel =
StateLib.getIndexOfAddr vaChild nbL0 )).
apply Classical_Prop.classic. 
destruct H. 
right;trivial.
left.
apply not_and_or;trivial. }
 
 destruct Hor.
 symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 intuition.
 destruct H2;subst.
 rewrite H3 in *; clear H3.

       
 rewrite  Htrue1 in H0.
  apply beq_nat_false in H1. 
  inversion H0;subst.
  now contradict H1.
 rewrite H2.
  
 case_eq(StateLib.readPhyEntry pdChildphy
            (StateLib.getIndexOfAddr vaChild nbL0) (memory s));intros;
            rewrite H3 in *;try now contradict H.
            inversion H0.
            subst.
            rewrite H1. 
 case_eq(StateLib.Level.pred nbL0);intros; 
 rewrite H4 in *.
 apply IHn;trivial. 
 now contradict Hind1.            
* rewrite H0 in *. now contradict Hind1. 
Qed.

Lemma getIndirectionMapMMUPage3 
  s ptVaChildpd phyVaChild r w e pdChildphy vaChild entry nbL stop:
  


  StateLib.readPhyEntry ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  (memory s) = Some defaultPage -> 
StateLib.readPhyEntry ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  (add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex ) = Some phyVaChild ->
lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s)
  beqPage beqIndex = Some (PE entry) ->
getIndirection pdChildphy vaChild nbL stop s = Some ptVaChildpd ->
 (defaultPage =? ptVaChildpd) = false  -> 
getIndirection pdChildphy vaChild nbL stop {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} = Some ptVaChildpd
. Proof. 
  revert pdChildphy. generalize nbL at 1 2.
  induction stop;simpl;
(*   intros;trivial. *)
  intros nbL0 pdChildphy Htrue1 Htrue2 Hlookup Hind1;trivial.
  destruct (StateLib.Level.eqb nbL0 fstLevel);intros;trivial.
  - case_eq( StateLib.readPhyEntry pdChildphy
            (StateLib.getIndexOfAddr vaChild nbL0) (memory s));intros.
  * rewrite H0 in *. 
  case_eq(defaultPage =? p);intros.
  rewrite H1 in *.
  apply beq_nat_false in H. 
  inversion Hind1;subst.
  now contradict H.
  rewrite H1 in *. 

  assert(StateLib.readPhyEntry pdChildphy (StateLib.getIndexOfAddr vaChild nbL0)
    (add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pdChildphy (StateLib.getIndexOfAddr vaChild nbL0)
    (memory s)).
 clear Hind1 IHstop.
 assert(Hor : (pdChildphy <>  ptVaChildpd \/ (StateLib.getIndexOfAddr vaChild fstLevel) <> 
 (StateLib.getIndexOfAddr vaChild nbL0)) \/ ( pdChildphy =  ptVaChildpd /\
 (StateLib.getIndexOfAddr vaChild fstLevel) = 
 (StateLib.getIndexOfAddr vaChild nbL0))). 
 { clear. assert((pdChildphy = ptVaChildpd /\
StateLib.getIndexOfAddr vaChild fstLevel =
StateLib.getIndexOfAddr vaChild nbL0 ) \/  
~ (pdChildphy = ptVaChildpd /\
StateLib.getIndexOfAddr vaChild fstLevel =
StateLib.getIndexOfAddr vaChild nbL0 )).
apply Classical_Prop.classic. 
destruct H. 
right;trivial.
left.
apply not_and_or;trivial. }
 
 destruct Hor.
 symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 intuition.
 destruct H2;subst.
 rewrite H3 in *; clear H3.

       
 rewrite  Htrue1 in H0.
  apply beq_nat_false in H1. 
  inversion H0;subst.
  now contradict H1.
 rewrite H2.
  
 case_eq(StateLib.readPhyEntry pdChildphy
            (StateLib.getIndexOfAddr vaChild nbL0) (memory s));intros;
            rewrite H3 in *;try now contradict H.
            inversion H0.
            subst.
            rewrite H1. 
 case_eq(StateLib.Level.pred nbL0);intros; 
 rewrite H4 in *.
 apply IHstop;trivial. 
 now contradict Hind1.            
* rewrite H0 in *. now contradict Hind1. 
Qed.


Lemma getPDFlagGetPdsVAddr sh1Childphy vaChild phyDescChild level s:
 nextEntryIsPP phyDescChild sh1idx sh1Childphy s -> 
  getPDFlag sh1Childphy vaChild s = false -> 
  StateLib.getNbLevel = Some level -> 
  getFstShadow phyDescChild (memory s) = Some sh1Childphy -> 
  ~ In vaChild (getPdsVAddr phyDescChild level getAllVAddrWithOffset0 s).
Proof. 

unfold getPDFlag.
unfold getPdsVAddr.
rewrite filter_In.
intros Hpp Hpdflag Hlevel Hsh1 .
apply or_not_and.
right.
unfold not;intros.
unfold checkChild in *.
rewrite Hlevel in *.
rewrite Hsh1 in *.
rewrite Hpdflag in *.
now contradict H. 
Qed.




       Lemma getIndirectionMapMMUPage2 s ptVaChildpd idxvaChild phyVaChild r w e  
  pdChildphy currentPart va p
presentvaChild vaChild phyDescChild level entry:
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
pdChildphy <> defaultPage -> 
getIndirection pdChildphy vaChild level (nbLevel - 1) s =
            Some ptVaChildpd -> 
   getIndirection pdChildphy va level (nbLevel - 1) s = Some p -> 
getIndirection pdChildphy va level (nbLevel - 1)s'= Some p.
Proof.
intros s' Hpde Hpresdef Hnodupconf Hconfigdiff Hparts Haccess Hlookup Hlevel 
 Hnotpresent Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild Hpdchildnotnull Hindchild  H.
{ assert(forall stop tbl,
    stop < level  -> 
    getIndirection pdChildphy va level stop s = Some tbl -> 
    (defaultPage =? tbl) = false ->
      tbl <> ptVaChildpd ). 
    { assert(Hnodup : NoDup (getIndirections pdChildphy s)).
      { apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
        unfold noDupConfigPagesList in *. 
        apply Hnodupconf ;trivial.
        left;trivial. }
      intros. 
      
      
      
      assert(~In ptVaChildpd (getIndirectionsAux pdChildphy s (stop+1))). 
      { assert(~In ptVaChildpd (getIndirectionsAux pdChildphy s (nbLevel-1))). 
    {  assert(0<nbLevel) by apply nbLevelNotZero.
      assert(nbLevel - 1 + 1 = nbLevel) by omega.
    
 
 assert(Hprevious : exists prevtab,
      getIndirection pdChildphy vaChild level (nbLevel - 2) s =
            Some prevtab /\prevtab <> defaultPage /\  StateLib.readPhyEntry prevtab
  (StateLib.getIndexOfAddr vaChild (CLevel (level- ((nbLevel - 1) - 1)))) (memory s) =
Some ptVaChildpd). 
{   revert Hindchild   Hdefaut  (*  H0 *).


  assert(Hstooo : level > (nbLevel - 1 -1)).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    unfold CLevel in H0.
    rewrite H5 in *.
    simpl in *.
    
    omega.
    omega. } 

  
  assert(Htpp : 0 < nbLevel -1).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    unfold CLevel in H0.
    rewrite H5 in *.
    simpl in *.
    
    omega.
    omega.
    
     } 
  assert(Hnotdef : pdChildphy <> defaultPage) by intuition. 
  revert Hstooo Htpp Hnotdef.
  clear. 
  replace (nbLevel -2) with (nbLevel -1 -1) by omega.  
  revert pdChildphy level ptVaChildpd.
  induction (nbLevel-1);simpl.
  intros.
  omega.
  intros. 
  case_eq(StateLib.Level.eqb level fstLevel);intros;
  rewrite H in *.
  apply levelEqBEqNatTrue0 in H. 
  omega.
   case_eq(StateLib.readPhyEntry pdChildphy
                (StateLib.getIndexOfAddr vaChild level) (memory s));intros;
    rewrite H0 in *;try now contradict Hindchild.
    case_eq(defaultPage =? p);intros;rewrite H1 in *.
    apply beq_nat_false in Hdefaut.
    inversion Hindchild.
    subst.
    now contradict Hdefaut.
    case_eq(StateLib.Level.pred level );intros;rewrite H2 in *.
    + replace (n-0) with n by omega.
    assert(Hooo : n = 0 \/ 0 < n) by omega.
    destruct Hooo.
    *
    subst. 
    simpl in *. 
    exists  pdChildphy;split;trivial.
    inversion Hindchild. 
    subst. 
    rewrite <- H0.
    split.  trivial. 
    f_equal.
    f_equal.
    rewrite <- minus_n_O.
    apply CLevelIdentity1.
    * assert(Hii : l > n - 1  ) .
    apply levelPredMinus1 in H2.
    subst.
   unfold CLevel.
    case_eq( lt_dec (level - 1) nbLevel );intros.
    simpl.
    omega.
    destruct level.
    simpl in *.
    omega.
    trivial.
    assert(Hi1 : p <> defaultPage).
    apply beq_nat_false in H1.
    intuition.
    subst.
    now contradict H1. 
      generalize(IHn p l ptVaChildpd Hii H3 Hi1 Hindchild Hdefaut
       );clear IHn ; intros iHn .
       destruct iHn as (prevtab & Hindprev & Hdef & Hread).
       exists prevtab;split;trivial.
       intros.
       assert(Hs :S(n-1) = n) by omega.
       rewrite <- Hs.
       simpl.
       rewrite H.
       rewrite H0. 
       rewrite H1.
       rewrite H2;trivial.
       split;trivial.
       rewrite <- Hread.
       f_equal.
       f_equal.
       f_equal.
apply levelPredMinus1 in H2.
rewrite H2.
unfold CLevel.
case_eq(lt_dec (level - 1) nbLevel);intros. 
simpl. 
omega.
destruct level. 
simpl in *.
omega.
trivial.
+ assert(Hnotnone : StateLib.Level.pred level <> None).
apply levelPredNone;trivial. now contradict Hnotnone.  }
destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev). 
       apply getIndirectionInGetIndirections2 with prevtab vaChild level;
      simpl; subst;
      trivial.
      omega.
      simpl.
      rewrite <- Hprevtable.
      f_equal.
      omega.
      rewrite H4. 
      unfold getIndirections in *;trivial.

(*       symmetry in Hlevel.
      apply getNbLevelEq in Hlevel.
      rewrite Hlevel in *.
      unfold CLevel in H0. 
      assert (0<nbLevel) by apply nbLevelNotZero.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros;
      rewrite H6 in *.
      simpl in *.
      omega.
      omega.
      omega. *)
      apply beq_nat_false in Hdefaut.
      unfold not;intros;subst.
      now contradict Hdefaut. 
      move Hlevel at bottom.
      symmetry in Hlevel.

      apply getNbLevelEq in Hlevel.
      rewrite Hlevel.
      unfold CLevel. 
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros. 
      simpl. 
      omega.
      omega.
      
      
      }
      unfold not;intros. contradict H3.
      assert(Hincl : incl (getIndirectionsAux pdChildphy s (stop + 1))
      (getIndirectionsAux pdChildphy s (nbLevel - 1))).
      apply inclGetIndirectionsAuxLe;trivial.
      symmetry in Hlevel.
      apply getNbLevelEq in Hlevel.
      subst.
      unfold CLevel in H0.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      rewrite H3 in *. 
      simpl in *. omega.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      unfold incl in *. 
      apply Hincl;trivial.
      }
     
      assert(In tbl (getIndirectionsAux pdChildphy s (stop+1))). 
      { apply getIndirectionInGetIndirections1 with va level;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      assert(level < nbLevel).
      apply getNbLevelLt;trivial.
      
      omega.
      apply beq_nat_false in H2.
      unfold not;intros;subst. 
      now contradict H2.  }
      unfold not;intros.
      subst.
      now contradict H4. 

     } 
     
     
    assert(Hlevel1 :  level <= CLevel (nbLevel - 1) ).
    apply getNbLevelLe;trivial.
    symmetry;trivial.
    rewrite <- H. 
    clear Hlevel. 
    
    revert H0 Hlevel1 Hlookup Hpdchildnotnull.
    clear.
    generalize level at 1 2 3 4 5  as l.
    revert pdChildphy. 
  induction (nbLevel - 1);simpl; intros;trivial.
  case_eq( StateLib.Level.eqb l fstLevel);intros;trivial.
   assert(StateLib.readPhyEntry pdChildphy (StateLib.getIndexOfAddr va l)
    (add ptVaChildpd idxvaChild
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pdChildphy (StateLib.getIndexOfAddr va l)
    (memory s)). symmetry.
    apply readPhyEntryMapMMUPage with entry;trivial.
    left.
    generalize (H0 0 pdChildphy);clear H0;intros H0. 
    simpl in *. 
    apply H0. 
    apply levelEqBEqNatFalse0;trivial. reflexivity.
    apply NPeano.Nat.eqb_neq.
    intuition.
    subst.
    apply Hpdchildnotnull.
    destruct defaultPage;destruct pdChildphy.
    simpl in *.
    subst.
    f_equal.
    apply proof_irrelevance.
    rewrite H1.
    case_eq( StateLib.readPhyEntry pdChildphy (StateLib.getIndexOfAddr va l)
    (memory s));intros;trivial.
    case_eq(defaultPage =? p);intros;trivial.
    case_eq(StateLib.Level.pred l );intros;trivial.
    apply IHn;trivial.
    intros.
    apply H0 with (S stop).
    simpl.
     apply levelPredMinus1 in H4;trivial.
     rewrite H4 in *.
       unfold CLevel in H5.
   case_eq(lt_dec (l - 1) nbLevel);intros.
   rewrite H8 in *. 
   simpl in *.
   omega.
   destruct l. 
   simpl in *.
   omega.
   simpl.
    rewrite H4.
    rewrite H.
    rewrite H2.
    rewrite H3.
    trivial.
    trivial.
    move    Hlevel1 at bottom.
    trivial.
    apply levelPredMinus1 in H4;trivial.
    rewrite H4.
    unfold CLevel.
    unfold CLevel in Hlevel1.
   case_eq(lt_dec (l - 1) nbLevel);intros.
   simpl.
   case_eq(lt_dec (S n) nbLevel);intros;
   rewrite H6 in *.
   simpl in *. 
   case_eq(lt_dec n nbLevel);intros. 
   simpl.
   omega.
   omega.
   case_eq(lt_dec n nbLevel);intros. 
   simpl.
   omega.
   omega.
   destruct l. 
   simpl in *.
   omega.
   apply beq_nat_false in H3. 
   unfold not;intros;subst. now contradict H3. }
   Qed. 
      Lemma getIndirectionNoneMapMMUPage2 s ptVaChildpd idxvaChild phyVaChild r w e  
  pdChildphy currentPart va 
presentvaChild vaChild phyDescChild level entry:
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
pdChildphy <> defaultPage -> 
getIndirection pdChildphy vaChild level (nbLevel - 1) s =
            Some ptVaChildpd -> 
   getIndirection pdChildphy va level (nbLevel - 1) s =  None -> 
getIndirection pdChildphy va level (nbLevel - 1)s'= None.
Proof.
intros s' Hpde Hpresdef Hnodupconf Hconfigdiff Hparts Haccess Hlookup Hlevel 
 Hnotpresent Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild Hpdchildnotnull Hindchild  H.
{ assert(forall stop tbl,
    stop < level  -> 
    getIndirection pdChildphy va level stop s = Some tbl -> 
    (defaultPage =? tbl) = false ->
      tbl <> ptVaChildpd ). 
    { assert(Hnodup : NoDup (getIndirections pdChildphy s)).
      { apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
        apply Hnodupconf ;trivial.
        left;trivial. }
      intros. 
      
      
      
      assert(~In ptVaChildpd (getIndirectionsAux pdChildphy s (stop+1))). 
      { assert(~In ptVaChildpd (getIndirectionsAux pdChildphy s (nbLevel-1))). 
    {  assert(0<nbLevel) by apply nbLevelNotZero.
      assert(nbLevel - 1 + 1 = nbLevel) by omega.
    
 
 assert(Hprevious : exists prevtab,
      getIndirection pdChildphy vaChild level (nbLevel - 2) s =
            Some prevtab /\prevtab <> defaultPage /\  StateLib.readPhyEntry prevtab
  (StateLib.getIndexOfAddr vaChild (CLevel (level- ((nbLevel - 1) - 1)))) (memory s) =
Some ptVaChildpd). 
{   revert Hindchild   Hdefaut  (*  H0 *).


  assert(Hstooo : level > (nbLevel - 1 -1)).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    unfold CLevel in H0.
    rewrite H5 in *.
    simpl in *.
    
    omega.
    omega. } 

  
  assert(Htpp : 0 < nbLevel -1).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    unfold CLevel in H0.
    rewrite H5 in *.
    simpl in *.
    
    omega.
    omega.
    
     } 
  assert(Hnotdef : pdChildphy <> defaultPage) by intuition. 
  revert Hstooo Htpp Hnotdef.
  clear. 
  replace (nbLevel -2) with (nbLevel -1 -1) by omega.  
  revert pdChildphy level ptVaChildpd.
  induction (nbLevel-1);simpl.
  intros.
  omega.
  intros. 
  case_eq(StateLib.Level.eqb level fstLevel);intros;
  rewrite H in *.
  apply levelEqBEqNatTrue0 in H. 
  omega.
   case_eq(StateLib.readPhyEntry pdChildphy
                (StateLib.getIndexOfAddr vaChild level) (memory s));intros;
    rewrite H0 in *;try now contradict Hindchild.
    case_eq(defaultPage =? p);intros;rewrite H1 in *.
    apply beq_nat_false in Hdefaut.
    inversion Hindchild.
    subst.
    now contradict Hdefaut.
    case_eq(StateLib.Level.pred level );intros;rewrite H2 in *.
    + replace (n-0) with n by omega.
    assert(Hooo : n = 0 \/ 0 < n) by omega.
    destruct Hooo.
    *
    subst. 
    simpl in *. 
    exists  pdChildphy;split;trivial.
    inversion Hindchild. 
    subst. 
    rewrite <- H0.
    split.  trivial. 
    f_equal.
    f_equal.
    rewrite <- minus_n_O.
    apply CLevelIdentity1.
    * assert(Hii : l > n - 1  ) .
    apply levelPredMinus1 in H2.
    subst.
   unfold CLevel.
    case_eq( lt_dec (level - 1) nbLevel );intros.
    simpl.
    omega.
    destruct level.
    simpl in *.
    omega.
    trivial.
    assert(Hi1 : p <> defaultPage).
    apply beq_nat_false in H1.
    intuition.
    subst.
    now contradict H1. 
      generalize(IHn p l ptVaChildpd Hii H3 Hi1 Hindchild Hdefaut
       );clear IHn ; intros iHn .
       destruct iHn as (prevtab & Hindprev & Hdef & Hread).
       exists prevtab;split;trivial.
       intros.
       assert(Hs :S(n-1) = n) by omega.
       rewrite <- Hs.
       simpl.
       rewrite H.
       rewrite H0. 
       rewrite H1.
       rewrite H2;trivial.
       split;trivial.
       rewrite <- Hread.
       f_equal.
       f_equal.
       f_equal.
apply levelPredMinus1 in H2.
rewrite H2.
unfold CLevel.
case_eq(lt_dec (level - 1) nbLevel);intros. 
simpl. 
omega.
destruct level. 
simpl in *.
omega.
trivial.
+ assert(Hnotnone : StateLib.Level.pred level <> None).
apply levelPredNone;trivial. now contradict Hnotnone.  }
destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev). 
       apply getIndirectionInGetIndirections2 with prevtab vaChild level;
      simpl; subst;
      trivial.
      omega.
      simpl.
      rewrite <- Hprevtable.
      f_equal.
      omega.
      rewrite H4. 
      unfold getIndirections in *;trivial.

(*       symmetry in Hlevel.
      apply getNbLevelEq in Hlevel.
      rewrite Hlevel in *.
      unfold CLevel in H0. 
      assert (0<nbLevel) by apply nbLevelNotZero.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros;
      rewrite H6 in *.
      simpl in *.
      omega.
      omega.
      omega. *)
      apply beq_nat_false in Hdefaut.
      unfold not;intros;subst.
      now contradict Hdefaut. 
      move Hlevel at bottom.
      symmetry in Hlevel.

      apply getNbLevelEq in Hlevel.
      rewrite Hlevel.
      unfold CLevel. 
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros. 
      simpl. 
      omega.
      omega.
      
      
      }
      unfold not;intros. contradict H3.
      assert(Hincl : incl (getIndirectionsAux pdChildphy s (stop + 1))
      (getIndirectionsAux pdChildphy s (nbLevel - 1))).
      apply inclGetIndirectionsAuxLe;trivial.
      symmetry in Hlevel.
      apply getNbLevelEq in Hlevel.
      subst.
      unfold CLevel in H0.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      rewrite H3 in *. 
      simpl in *. omega.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      unfold incl in *. 
      apply Hincl;trivial.
      }
     
      assert(In tbl (getIndirectionsAux pdChildphy s (stop+1))). 
      { apply getIndirectionInGetIndirections1 with va level;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      assert(level < nbLevel).
      apply getNbLevelLt;trivial.
      
      omega.
      apply beq_nat_false in H2.
      unfold not;intros;subst. 
      now contradict H2.  }
      unfold not;intros.
      subst.
      now contradict H4. 

     } 
     
     
    assert(Hlevel1 :  level <= CLevel (nbLevel - 1) ).
    apply getNbLevelLe;trivial.
    symmetry;trivial.
    rewrite <- H. 
    clear Hlevel. 
    
    revert H0 Hlevel1 Hlookup Hpdchildnotnull.
    clear.
    generalize level at 1 2 3 4 5  as l.
    revert pdChildphy. 
  induction (nbLevel - 1);simpl; intros;trivial.
  case_eq( StateLib.Level.eqb l fstLevel);intros;trivial.
   assert(StateLib.readPhyEntry pdChildphy (StateLib.getIndexOfAddr va l)
    (add ptVaChildpd idxvaChild
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pdChildphy (StateLib.getIndexOfAddr va l)
    (memory s)). symmetry.
    apply readPhyEntryMapMMUPage with entry;trivial.
    left.
    generalize (H0 0 pdChildphy);clear H0;intros H0. 
    simpl in *. 
    apply H0. 
    apply levelEqBEqNatFalse0;trivial. reflexivity.
    apply NPeano.Nat.eqb_neq.
    intuition.
    subst.
    apply Hpdchildnotnull.
    destruct defaultPage;destruct pdChildphy.
    simpl in *.
    subst.
    f_equal.
    apply proof_irrelevance.
    rewrite H1.
    case_eq( StateLib.readPhyEntry pdChildphy (StateLib.getIndexOfAddr va l)
    (memory s));intros;trivial.
    case_eq(defaultPage =? p);intros;trivial.
    case_eq(StateLib.Level.pred l );intros;trivial.
    apply IHn;trivial.
    intros.
    apply H0 with (S stop).
    simpl.
     apply levelPredMinus1 in H4;trivial.
     rewrite H4 in *.
       unfold CLevel in H5.
   case_eq(lt_dec (l - 1) nbLevel);intros.
   rewrite H8 in *. 
   simpl in *.
   omega.
   destruct l. 
   simpl in *.
   omega.
   simpl.
    rewrite H4.
    rewrite H.
    rewrite H2.
    rewrite H3.
    trivial.
    trivial.
    move    Hlevel1 at bottom.
    trivial.
    apply levelPredMinus1 in H4;trivial.
    rewrite H4.
    unfold CLevel.
    unfold CLevel in Hlevel1.
   case_eq(lt_dec (l - 1) nbLevel);intros.
   simpl.
   case_eq(lt_dec (S n) nbLevel);intros;
   rewrite H6 in *.
   simpl in *. 
   case_eq(lt_dec n nbLevel);intros. 
   simpl.
   omega.
   omega.
   case_eq(lt_dec n nbLevel);intros. 
   simpl.
   omega.
   omega.
   destruct l. 
   simpl in *.
   omega.
   apply beq_nat_false in H3. 
   unfold not;intros;subst. now contradict H3. }
   Qed.

Lemma getChildrenMapMMUPage1 s ptVaChildpd idxvaChild phyVaChild r w e  pdChildphy currentPart
presentvaChild vaChild phyDescChild level entry:
  wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues s->  
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
forall part, In part (getPartitions multiplexer s) -> 

forall child,
In child (getChildren part s) ->
 In child (getChildren part {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}).
Proof.
intros Hnewcons Hnewcons2 Hpde Hpresdef Hnodupconf Hconfigdiff Hparts Haccess Hlookup Hlevel  Hnotpresent Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild  part Hpart child Hchild.
unfold getChildren in *.
rewrite Hlevel in *.
simpl. 
set(s' :=  {|
         currentPartition := _ |}) in *.
assert(Hgetpd : forall partition, StateLib.getPd partition
  (add ptVaChildpd idxvaChild(PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) 
     (memory s) beqPage beqIndex ) = StateLib.getPd partition (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
intros. 
rewrite Hgetpd in *. clear Hgetpd.
case_eq(StateLib.getPd part (memory s) );[intros pd Hpd |intros Hpd];
rewrite Hpd in *;
trivial.
assert(Hpds : getPdsVAddr part level getAllVAddrWithOffset0 s =
getPdsVAddr part level getAllVAddrWithOffset0 s').
apply getPdsVAddrMapMMUPage with  pdChildphy
presentvaChild vaChild phyDescChild entry;trivial.
symmetry;trivial.
rewrite <- Hpds in *.
unfold getMappedPagesAux in *. 
rewrite filterOptionInIff in *.
unfold getMappedPagesOption in *.
assert(Htrue : getMappedPage pdChildphy s vaChild = SomeDefault).
{ apply getMappedPageNotPresent with ptVaChildpd phyDescChild;intuition.
  + subst;trivial.
  + apply negb_true_iff in Hnotpresent.
    subst;trivial. } 
assert(Hpdchildnotnull : pdChildphy <> defaultPage). 
{ 
apply pdPartNotNull with phyDescChild s;trivial.
}        
assert(Hor : part = phyDescChild \/ part <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor]; subst.
+ assert(Hpdeq : pd = pdChildphy). 
  { symmetry. apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
  subst.
  rewrite in_map_iff in *.
  destruct Hchild as (va & Hmapva & Hpdva).
  
  exists va;split;trivial.
  assert (Hnewpres : entryPresentFlag ptVaChildpd
                    (StateLib.getIndexOfAddr vaChild fstLevel) true s').
  { unfold s'. 
    unfold entryPresentFlag.
    cbn.
    assert(Hpairs :  beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
        (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
        beqIndex = true).
    { apply beqPairsTrue; split;trivial. }
   rewrite Hpairs;simpl;trivial. }
  assert(HnewEntry : isEntryPage ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) phyVaChild
    s').
   { unfold s'. 
    unfold isEntryPage.
    cbn.
    assert(Hpairs :  beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
        (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
        beqIndex = true).
    { apply beqPairsTrue; split;trivial. }
   rewrite Hpairs;simpl;trivial. }

assert (Hnewmap : getMappedPage pdChildphy s' vaChild = SomePage phyVaChild).
{
 
  apply getMappedPageGetTableRoot with ptVaChildpd phyDescChild;
  trivial;fold s'. 
  + intros. 
  split. 
  apply isPEMapMMUPage with entry;trivial.
  subst;trivial.
  move Htblroot at bottom.
  unfold getTableAddrRoot in *.
  destruct Htblroot as (Hidxs & Htblroot).
  split;trivial.
  intros.
  apply Htblroot in Hpdchild;clear Htblroot.
  move Hpdchild at bottom.
  destruct Hpdchild as (nbL & HnbL & stop & Hstop & Hind1).
  exists nbL ; split ; trivial.
  exists stop;split;trivial.
  assert(tableroot = pdChildphy). 
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  phyVaChild r w  e;trivial.
  subst .
  revert Hind1.
  assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
                  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some defaultPage).
  { assert(Hcons1 : isPresentNotDefaultIff s) by trivial.
    apply Hcons1.
    apply negb_true_iff in Hnotpresent.
    subst. 
    move Hentrypresent at bottom.
    unfold entryPresentFlag in *. 
    unfold StateLib.readPresent. 
    rewrite Hlookup in *.
    f_equal.
    rewrite Hentrypresent. trivial. }
  assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
                  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some phyVaChild).
  { unfold StateLib.readPhyEntry. 
    cbn.
    assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
      beqIndex = true); intros.
    rewrite <- beqPairsTrue;split;trivial.
    rewrite Hpairs.
    simpl;trivial. }
  revert Htrue1 Htrue2 Hlookup Hdefaut.
  clear.
 
intros. apply getIndirectionMapMMUPage with entry;trivial.
  +  apply nextEntryIsPPMapMMUPage with entry;trivial. 
  }
  
unfold wellFormedFstShadowIfDefaultValues in *. 
  assert(Hentrysh1 : (exists entry : page,
   nextEntryIsPP phyDescChild sh1idx entry s /\ entry <> defaultPage)). 
 apply Hpde;trivial.
 right;left;trivial.
 destruct Hentrysh1 as (sh1Childphy & Hsh1child & Hsh1notnull).
 assert(Hpdflag : getPDFlag sh1Childphy vaChild s = false). 
 { apply Hnewcons2 with phyDescChild pdChildphy;trivial.
   apply nextEntryIsPPgetFstShadow;trivial. }
   assert(Hvachildnotpart : ~ In vaChild (getPdsVAddr phyDescChild level getAllVAddr s)).
  { 
    apply getPDFlagGetPdsVAddr' with sh1Childphy;trivial. 
      apply nextEntryIsPPgetFstShadow;trivial. }
    assert(Hor :checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaChild va level = false).
  { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild va level);intuition. }
  destruct Hor as [Hor | Hor].
  - assert (Hinpds : In vaChild (getPdsVAddr phyDescChild level getAllVAddr s)). 
    { apply checkVAddrsEqualityWOOffsetTrue1 with va;trivial.
       move Hpdva at bottom.
       unfold getPdsVAddr in *.
       apply filter_In in Hpdva as (Hiva & Hiv2).
       apply filter_In.
       split;trivial.
       apply AllVAddrAll. } 
  now contradict Hinpds.
  -   
  assert(Hindchild : getIndirection pdChildphy vaChild level (nbLevel - 1) s =
  Some ptVaChildpd). 
  { apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
    intros;split;trivial.
    subst;trivial. }
  
  rewrite <- Hmapva.
  unfold getMappedPage.
  rewrite Hlevel.
  
   case_eq(getIndirection pdChildphy va level (nbLevel - 1) s );intros.
   


*  assert( getIndirection pdChildphy va level (nbLevel - 1) s' = Some p). 
apply getIndirectionMapMMUPage2
with  currentPart
presentvaChild vaChild phyDescChild entry;trivial.
  rewrite H0.
   case_eq(defaultPage =? p);intros;trivial.  
   assert(ptVaChildpd <> p \/ (StateLib.getIndexOfAddr vaChild fstLevel) <> 
  (StateLib.getIndexOfAddr va fstLevel)).
   apply pageTablesOrIndicesAreDifferent with pdChildphy pdChildphy
    level nbLevel s;trivial.
    apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
        apply Hnodupconf ;trivial.
unfold noDupConfigPagesList in *.
left;trivial.
apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
        apply Hnodupconf ;trivial.
unfold noDupConfigPagesList in *.
left;trivial. left.
  split;trivial.
  apply getNbLevelEq.
  symmetry;trivial.
    apply beq_nat_false in Hdefaut.
    unfold not;intros;subst;now contradict Hdefaut.
  apply beq_nat_false in H1.
  unfold not;intros;subst;trivial.
  now contradict H1.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 assert(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s)
 = StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s')). 
 apply readPresentMapMMUPage with entry;trivial.
 intuition.
 rewrite <- H3.
 case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s));intros.
 destruct b;trivial.
 symmetry.
 assert(Heq : StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s')=
  StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s)).
  symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 intuition.
 rewrite Heq.
 trivial.
 trivial.
  *  assert( getIndirection pdChildphy va level (nbLevel - 1) s' = None). 
  apply getIndirectionNoneMapMMUPage2 with currentPart
presentvaChild vaChild phyDescChild entry;trivial.
   rewrite H0.
   trivial.
   + rewrite in_map_iff in *.
  destruct Hchild as (va & Hmapva & Hpdva).
  exists va;split;trivial.
rewrite <- Hmapva.
{
  unfold getMappedPage.
  rewrite Hlevel.
  unfold configTablesAreDifferent in *.
  assert(Hconfigpart : forall ind stop,  
  getIndirection pd va level stop s = Some ind ->
  ind <> defaultPage -> 
  In ind (getIndirectionsAux pd s (nbLevel))).
  { intros.
    apply getIndirectionInGetIndirections with va level stop;trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    omega.
    symmetry in Hlevel.
    apply getNbLevelEq in Hlevel.
    subst.
    omega.  
  unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP part PDidx entry s /\ entry <> defaultPage)).
        apply Hpde;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pd).
apply getPdNextEntryIsPPEq  with part s;trivial.
subst;trivial. }
assert(Hconfig : forall ind, In ind (getIndirectionsAux pd s nbLevel) -> 
In ind (getConfigPages part s)).
intros.
unfold getConfigPages.
simpl. right.   
apply inGetIndirectionsAuxInConfigPagesPD with pd;trivial.
assert(Hi : forall ind stop,  
  getIndirection pd va level stop s = Some ind ->
  ind <> defaultPage -> In ind (getConfigPages part s)). 
  { intros. apply Hconfig.
    apply Hconfigpart with stop;trivial. }
assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
apply isConfigTable  with vaChild;trivial.
intros. split. 
subst;trivial.
subst;trivial.
assert(Hmykey : forall stop tbl,
    getIndirection pd va level stop s = Some tbl -> 
    (defaultPage =? tbl) = false ->
      tbl <> ptVaChildpd ).
{ intros. 
  unfold not;intros.
  subst.
  assert(Hmykey2 :  disjoint (getConfigPages part s)
                (getConfigPages phyDescChild s)).
  { apply Hconfigdiff;trivial. }
  unfold disjoint in *.
  unfold not in Hmykey2.
  apply Hmykey2 with ptVaChildpd;trivial.
  apply Hi with stop;trivial.
  apply beq_nat_false in Hdefaut.
  intuition.
  subst.
  now contradict Hdefaut. }
assert(Hmykey3 : getIndirection pd va level (nbLevel - 1) s = 
getIndirection pd va level (nbLevel - 1) s').
{ 
   assert(Hpdnotnull : pd <> defaultPage). 
{ unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP part PDidx entry s /\ entry <> defaultPage)).
        apply Hpde;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pd).
apply getPdNextEntryIsPPEq  with part s;trivial.
subst;trivial. } 
revert Hmykey Hlookup Hpdnotnull.

   clear.
   revert pd level.
   induction (nbLevel - 1).
   simpl;trivial.
   simpl in *. 
   intros.
    case_eq( StateLib.Level.eqb level fstLevel);intros;trivial.
    assert(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va level)
    (add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va level)
    (memory s)). symmetry.
    apply readPhyEntryMapMMUPage with entry;trivial.
    left.
    generalize (Hmykey 0 pd);clear Hmykey;intros Hmykey. 
    simpl in *. 
    apply Hmykey;trivial.
    apply NPeano.Nat.eqb_neq.
    unfold not;intros.
    subst.
    destruct defaultPage;destruct pd;simpl in *;subst.
    contradict Hpdnotnull.
    f_equal. apply  proof_irrelevance.
    rewrite H0.
    case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va level) (memory s));intros;trivial.
    case_eq(defaultPage =? p);intros;trivial.
    case_eq(StateLib.Level.pred level );intros;trivial.
    apply IHn;trivial.
    intros.
    apply Hmykey with (S stop).
    simpl.    
      
     rewrite H3 in *.
     rewrite H.
     rewrite H1.
     rewrite H2;trivial.
     trivial.
     apply beq_nat_false in H2.
     unfold not;intros.
     subst. now contradict H2.  }
rewrite <- Hmykey3.
 case_eq( getIndirection pd va level (nbLevel - 1) s);intros. 
 case_eq( defaultPage =? p);intros;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) =
 StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s')).
 simpl. 
 apply readPresentMapMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hpres.
 assert(Hread :StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s) =
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s')).
 simpl. 
 apply readPhyEntryMapMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hread.
 trivial.
 trivial. } 
Qed.

Lemma getChildrenMapMMUPage s ptVaChildpd idxvaChild phyVaChild r w e  pdChildphy currentPart
presentvaChild vaChild phyDescChild level entry:
  wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
forall part, In part (getPartitions multiplexer s) -> 

forall child,
In child (getChildren part {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}) ->
 In child (getChildren part s).
Proof.
intros Hnewcons Hnewcons2 Hpde Hpresdef Hnodupconf Hconfigdiff Hparts Haccess Hlookup Hlevel  Hnotpresent Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild  part Hpart child Hchild.
unfold getChildren in *.
rewrite Hlevel in *.
simpl. 
set(s' :=  {|
         currentPartition := _ |}) in *.
assert(Hgetpd : forall partition, StateLib.getPd partition
  (add ptVaChildpd idxvaChild(PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) 
     (memory s) beqPage beqIndex ) = StateLib.getPd partition (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
intros. 
rewrite Hgetpd in *. clear Hgetpd.
case_eq(StateLib.getPd part (memory s) );[intros pd Hpd |intros Hpd];
rewrite Hpd in *;
trivial.
assert(Hpds : getPdsVAddr part level getAllVAddrWithOffset0 s =
getPdsVAddr part level getAllVAddrWithOffset0 s').
apply getPdsVAddrMapMMUPage with  pdChildphy
presentvaChild vaChild phyDescChild entry;trivial.
symmetry;trivial.
rewrite <- Hpds in *.
unfold getMappedPagesAux in *. 
rewrite filterOptionInIff in *.
unfold getMappedPagesOption in *.
assert(Htrue : getMappedPage pdChildphy s vaChild = SomeDefault).
{ apply getMappedPageNotPresent with ptVaChildpd phyDescChild;intuition.
  + subst;trivial.
  + apply negb_true_iff in Hnotpresent.
    subst;trivial. } 
assert(Hpdchildnotnull : pdChildphy <> defaultPage). 
{ 
apply pdPartNotNull with phyDescChild s;trivial.
}        
assert(Hor : part = phyDescChild \/ part <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor]; subst.
+ assert(Hpdeq : pd = pdChildphy). 
  { symmetry. apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
  subst.
  rewrite in_map_iff in *.
  destruct Hchild as (va & Hmapva & Hpdva).
  exists va;split;trivial.
  assert (Hnewpres : entryPresentFlag ptVaChildpd
                    (StateLib.getIndexOfAddr vaChild fstLevel) true s').
  { unfold s'. 
    unfold entryPresentFlag.
    cbn.
    assert(Hpairs :  beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
        (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
        beqIndex = true).
    { apply beqPairsTrue; split;trivial. }
   rewrite Hpairs;simpl;trivial. }
  assert(HnewEntry : isEntryPage ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) phyVaChild
    s').
   { unfold s'. 
    unfold isEntryPage.
    cbn.
    assert(Hpairs :  beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
        (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
        beqIndex = true).
    { apply beqPairsTrue; split;trivial. }
   rewrite Hpairs;simpl;trivial. }

assert (Hnewmap : getMappedPage pdChildphy s' vaChild = SomePage phyVaChild).
{
 
  apply getMappedPageGetTableRoot with ptVaChildpd phyDescChild;
  trivial;fold s'. 
  + intros. 
  split. 
  apply isPEMapMMUPage with entry;trivial.
  subst;trivial.
  move Htblroot at bottom.
  unfold getTableAddrRoot in *.
  destruct Htblroot as (Hidxs & Htblroot).
  split;trivial.
  intros.
  apply Htblroot in Hpdchild;clear Htblroot.
  move Hpdchild at bottom.
  destruct Hpdchild as (nbL & HnbL & stop & Hstop & Hind1).
  exists nbL ; split ; trivial.
  exists stop;split;trivial.
  assert(tableroot = pdChildphy). 
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  phyVaChild r w  e;trivial.
  subst .
  revert Hind1.
  assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
                  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some defaultPage).
  { assert(Hcons1 : isPresentNotDefaultIff s) by trivial.
    apply Hcons1.
    apply negb_true_iff in Hnotpresent.
    subst. 
    move Hentrypresent at bottom.
    unfold entryPresentFlag in *. 
    unfold StateLib.readPresent. 
    rewrite Hlookup in *.
    f_equal.
    rewrite Hentrypresent. trivial. }
  assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
                  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some phyVaChild).
  { unfold StateLib.readPhyEntry. 
    cbn.
    assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
      beqIndex = true); intros.
    rewrite <- beqPairsTrue;split;trivial.
    rewrite Hpairs.
    simpl;trivial. }
  revert Htrue1 Htrue2 Hlookup Hdefaut.
  clear.
 
intros. apply getIndirectionMapMMUPage with entry;trivial.
  +  apply nextEntryIsPPMapMMUPage with entry;trivial. 
  }
  unfold wellFormedFstShadowIfDefaultValues in *.
  
  assert(Hentrysh1 : (exists entry : page,
   nextEntryIsPP phyDescChild sh1idx entry s /\ entry <> defaultPage)). 
 apply Hpde;trivial.
 right;left;trivial.
 destruct Hentrysh1 as (sh1Childphy & Hsh1child & Hsh1notnull).
 assert(Hpdflag : getPDFlag sh1Childphy vaChild s = false). 
 { apply Hnewcons2 with phyDescChild pdChildphy;trivial.
   apply nextEntryIsPPgetFstShadow;trivial. }
   assert(Hvachildnotpart : ~ In vaChild (getPdsVAddr phyDescChild level getAllVAddr s)).
  {  
  apply getPDFlagGetPdsVAddr' with sh1Childphy;trivial.
  apply nextEntryIsPPgetFstShadow;trivial. }
    assert(Hor :checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaChild va level = false).
  { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild va level);intuition. }
  destruct Hor as [Hor | Hor].
  - 
  assert (Hinpds : In vaChild (getPdsVAddr phyDescChild level getAllVAddr s)). 
    { 
     
 apply checkVAddrsEqualityWOOffsetTrue1 with va;trivial.
 move Hpdva at bottom.
       unfold getPdsVAddr in *.
       apply filter_In in Hpdva as (Hiva & Hiv2).
       apply filter_In.
       split;trivial.
       apply AllVAddrAll. } 
  now contradict Hinpds.
  -   
  assert(Hindchild : getIndirection pdChildphy vaChild level (nbLevel - 1) s =
  Some ptVaChildpd). 
  { apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
    intros;split;trivial.
    subst;trivial. }
  
  rewrite <- Hmapva.
  unfold getMappedPage.
  rewrite Hlevel.
  
   case_eq(getIndirection pdChildphy va level (nbLevel - 1) s );intros.
   
*  assert( getIndirection pdChildphy va level (nbLevel - 1) s' = Some p). 
apply getIndirectionMapMMUPage2
with  currentPart
presentvaChild vaChild phyDescChild entry;trivial.
  rewrite H0.
   case_eq(defaultPage =? p);intros;trivial.  
   assert(ptVaChildpd <> p \/ (StateLib.getIndexOfAddr vaChild fstLevel) <> 
  (StateLib.getIndexOfAddr va fstLevel)).
   apply pageTablesOrIndicesAreDifferent with pdChildphy pdChildphy
    level nbLevel s;trivial.
    apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
        apply Hnodupconf ;trivial.
unfold noDupConfigPagesList in *.
left;trivial.
apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
        apply Hnodupconf ;trivial.
unfold noDupConfigPagesList in *.
left;trivial.  left.
  split;trivial.
  apply getNbLevelEq.
  symmetry;trivial.
    apply beq_nat_false in Hdefaut.
    unfold not;intros;subst;now contradict Hdefaut.
  apply beq_nat_false in H1.
  unfold not;intros;subst;trivial.
  now contradict H1.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 assert(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s)
 = StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s')). 
 apply readPresentMapMMUPage with entry;trivial.
 intuition.
 rewrite <- H3.
 case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s));intros.
 destruct b;trivial.
 assert(Heq : StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s')=
  StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s)).
  symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 intuition.
 rewrite Heq.
 trivial.
 trivial.
  *  assert( getIndirection pdChildphy va level (nbLevel - 1) s' = None). 
  apply getIndirectionNoneMapMMUPage2 with currentPart
presentvaChild vaChild phyDescChild entry;trivial.
   rewrite H0.
   trivial.
   + rewrite in_map_iff in *.
  destruct Hchild as (va & Hmapva & Hpdva).
  exists va;split;trivial.
rewrite <- Hmapva.
{
  unfold getMappedPage.
  rewrite Hlevel.
  unfold configTablesAreDifferent in *.
  assert(Hconfigpart : forall ind stop,  
  getIndirection pd va level stop s = Some ind ->
  ind <> defaultPage -> 
  In ind (getIndirectionsAux pd s (nbLevel))).
  { intros.
    apply getIndirectionInGetIndirections with va level stop;trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    omega.
    symmetry in Hlevel.
    apply getNbLevelEq in Hlevel.
    subst.
    omega.  
  unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP part PDidx entry s /\ entry <> defaultPage)).
        apply Hpde;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pd).
apply getPdNextEntryIsPPEq  with part s;trivial.
subst;trivial. }
assert(Hconfig : forall ind, In ind (getIndirectionsAux pd s nbLevel) -> 
In ind (getConfigPages part s)).
intros.
unfold getConfigPages.
simpl. right.   
apply inGetIndirectionsAuxInConfigPagesPD with pd;trivial.
assert(Hi : forall ind stop,  
  getIndirection pd va level stop s = Some ind ->
  ind <> defaultPage -> In ind (getConfigPages part s)). 
  { intros. apply Hconfig.
    apply Hconfigpart with stop;trivial. }
assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
apply isConfigTable  with vaChild;trivial.
intros. split. 
subst;trivial.
subst;trivial.
assert(Hmykey : forall stop tbl,
    getIndirection pd va level stop s = Some tbl -> 
    (defaultPage =? tbl) = false ->
      tbl <> ptVaChildpd ).
{ intros. 
  unfold not;intros.
  subst.
  assert(Hmykey2 :  disjoint (getConfigPages part s)
                (getConfigPages phyDescChild s)).
  { apply Hconfigdiff;trivial. }
  unfold disjoint in *.
  unfold not in Hmykey2.
  apply Hmykey2 with ptVaChildpd;trivial.
  apply Hi with stop;trivial.
  apply beq_nat_false in Hdefaut.
  intuition.
  subst.
  now contradict Hdefaut. }
assert(Hmykey3 : getIndirection pd va level (nbLevel - 1) s = 
getIndirection pd va level (nbLevel - 1) s').
{ 
   assert(Hpdnotnull : pd <> defaultPage). 
{ unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP part PDidx entry s /\ entry <> defaultPage)).
        apply Hpde;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pd).
apply getPdNextEntryIsPPEq  with part s;trivial.
subst;trivial. } 
revert Hmykey Hlookup Hpdnotnull.

   clear.
   revert pd level.
   induction (nbLevel - 1).
   simpl;trivial.
   simpl in *. 
   intros.
    case_eq( StateLib.Level.eqb level fstLevel);intros;trivial.
    assert(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va level)
    (add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va level)
    (memory s)). symmetry.
    apply readPhyEntryMapMMUPage with entry;trivial.
    left.
    generalize (Hmykey 0 pd);clear Hmykey;intros Hmykey. 
    simpl in *. 
    apply Hmykey;trivial.
    apply NPeano.Nat.eqb_neq.
    unfold not;intros.
    subst.
    destruct defaultPage;destruct pd;simpl in *;subst.
    contradict Hpdnotnull.
    f_equal. apply  proof_irrelevance.
    rewrite H0.
    case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va level) (memory s));intros;trivial.
    case_eq(defaultPage =? p);intros;trivial.
    case_eq(StateLib.Level.pred level );intros;trivial.
    apply IHn;trivial.
    intros.
    apply Hmykey with (S stop).
    simpl.    
      
     rewrite H3 in *.
     rewrite H.
     rewrite H1.
     rewrite H2;trivial.
     trivial.
     apply beq_nat_false in H2.
     unfold not;intros.
     subst. now contradict H2.  }
rewrite <- Hmykey3.
 case_eq( getIndirection pd va level (nbLevel - 1) s);intros. 
 case_eq( defaultPage =? p);intros;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) =
 StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s')).
 simpl. 
 apply readPresentMapMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hpres.
 assert(Hread :StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s) =
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr va fstLevel) (memory s')).
 simpl. 
 apply readPhyEntryMapMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hread.
 trivial.
 trivial. } 
Qed.

Lemma getMappedPageMapMMUPage vax s pdChildphy phyVaChild x ptVaChildpd  r w e
(vaChild : vaddr) (phyDescChild : page) level entry: 
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 


getMappedPage pdChildphy s' vax = SomePage x -> 
Some level = StateLib.getNbLevel -> 
StateLib.getPd phyDescChild (memory s) = Some pdChildphy -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s)
       beqPage beqIndex = Some (PE entry) -> 
consistency s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
In phyDescChild (getPartitions multiplexer s)-> 
(defaultPage =? ptVaChildpd) = false -> 
entryPresentFlag ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) false s -> 
checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false -> 
getMappedPage pdChildphy s vax = SomePage x.
Proof.  
intros s' (* Hor *) Hvax Hlevel Hpp.
intros.
assert(Hindchild : getIndirection pdChildphy vaChild level (nbLevel - 1) s =
  Some ptVaChildpd). 
{ apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
  symmetry;trivial.
  intros;split;trivial.
  subst;trivial. }
rewrite <- Hvax. 
unfold getMappedPage.
rewrite <- Hlevel. 
case_eq(getIndirection pdChildphy vax level (nbLevel - 1) s );intros.
assert(Hii:   getIndirection pdChildphy vax level (nbLevel - 1) s' = Some p).
{ unfold consistency in *. 
  intuition.
  apply getIndirectionMapMMUPage2
    with (currentPartition s) false vaChild phyDescChild entry; subst;trivial.
   symmetry;trivial.
  apply nextEntryIsPPgetPd;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
rewrite Hii.
   assert(Hnodupconf : noDupConfigPagesList s).
    unfold consistency in *. 
    intuition.
  case_eq(defaultPage =? p);intros Hnotdef;trivial.  
   assert(ptVaChildpd <> p \/ (StateLib.getIndexOfAddr vaChild fstLevel) <> 
  (StateLib.getIndexOfAddr vax fstLevel)).
   apply pageTablesOrIndicesAreDifferent with pdChildphy pdChildphy
    level nbLevel s;trivial.
    apply pdPartNotNull with phyDescChild s;trivial.
    apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
    apply pdPartNotNull with phyDescChild s;trivial.
     apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
 apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.

 apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.  

  left.
  split;trivial.
  apply getNbLevelEq.
  trivial.
  assert(Hdefaut: (defaultPage =? ptVaChildpd) = false) by trivial.
    apply beq_nat_false in Hdefaut.
    unfold not;intros;subst;now contradict Hdefaut.
  apply beq_nat_false in Hnotdef.
  unfold not;intros;subst;trivial.
  now contradict Hnotdef.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;symmetry;trivial.
 
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;symmetry;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s)
 = StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s')). 
 apply readPresentMapMMUPage with entry;trivial.
 intuition.
 rewrite <- Hpres.
 case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s));intros.
 destruct b;trivial.
 symmetry.
 assert(Heq : StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s')=
  StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s)).
  symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 intuition.
 rewrite Heq.
 trivial.
 trivial.
 assert(Hnone : getIndirection pdChildphy vax level (nbLevel - 1) s' = None).
 unfold consistency in *.
 intuition.
 apply getIndirectionNoneMapMMUPage2 with (currentPartition s) false vaChild phyDescChild entry;trivial.
symmetry. trivial.
apply nextEntryIsPPgetPd;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply nextEntryIsPPgetPd;trivial.
rewrite Hnone;trivial.
Qed.

Lemma getMappedPageNoneMapMMUPage vax s pdChildphy phyVaChild ptVaChildpd  r w e
(vaChild : vaddr) (phyDescChild : page) level entry: 
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 


getMappedPage pdChildphy s' vax = NonePage-> 
Some level = StateLib.getNbLevel -> 
StateLib.getPd phyDescChild (memory s) = Some pdChildphy -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s)
       beqPage beqIndex = Some (PE entry) -> 
consistency s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
In phyDescChild (getPartitions multiplexer s)-> 
(defaultPage =? ptVaChildpd) = false -> 
entryPresentFlag ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) false s -> 
checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false -> 
getMappedPage pdChildphy s vax = NonePage.
Proof.  
intros s' (* Hor *) Hvax Hlevel Hpp.
intros.
assert(Hindchild : getIndirection pdChildphy vaChild level (nbLevel - 1) s =
  Some ptVaChildpd). 
{ apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
  symmetry;trivial.
  intros;split;trivial.
  subst;trivial. }
rewrite <- Hvax. 
unfold getMappedPage.
rewrite <- Hlevel. 
case_eq(getIndirection pdChildphy vax level (nbLevel - 1) s );intros.
assert(Hii:   getIndirection pdChildphy vax level (nbLevel - 1) s' = Some p).
{ unfold consistency in *. 
  intuition.
  apply getIndirectionMapMMUPage2
    with (currentPartition s) false vaChild phyDescChild entry; subst;trivial.
   symmetry;trivial.
  apply nextEntryIsPPgetPd;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
rewrite Hii.
   assert(Hnodupconf : noDupConfigPagesList s).
    unfold consistency in *. 
    intuition.
  case_eq(defaultPage =? p);intros Hnotdef;trivial.  
   assert(ptVaChildpd <> p \/ (StateLib.getIndexOfAddr vaChild fstLevel) <> 
  (StateLib.getIndexOfAddr vax fstLevel)).
   apply pageTablesOrIndicesAreDifferent with pdChildphy pdChildphy
    level nbLevel s;trivial.
    apply pdPartNotNull with phyDescChild s;trivial.
    apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
    apply pdPartNotNull with phyDescChild s;trivial.
     apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
 
 apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.
 
 apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.
  left.
  split;trivial.
  apply getNbLevelEq.
  trivial.
  assert(Hdefaut: (defaultPage =? ptVaChildpd) = false) by trivial.
    apply beq_nat_false in Hdefaut.
    unfold not;intros;subst;now contradict Hdefaut.
  apply beq_nat_false in Hnotdef.
  unfold not;intros;subst;trivial.
  now contradict Hnotdef.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;symmetry;trivial.
 
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;symmetry;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s)
 = StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s')). 
 apply readPresentMapMMUPage with entry;trivial.
 intuition.
 rewrite <- Hpres.
 case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s));intros.
 destruct b;trivial.
 symmetry.
  assert(Heq : StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s')=
  StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s)).
  symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 intuition.
 rewrite Heq.
 trivial.
 trivial.
 assert(Hnone : getIndirection pdChildphy vax level (nbLevel - 1) s' = None).
 unfold consistency in *.
 intuition.
 apply getIndirectionNoneMapMMUPage2 with (currentPartition s) false vaChild phyDescChild entry;trivial.
symmetry. trivial.
apply nextEntryIsPPgetPd;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply nextEntryIsPPgetPd;trivial.
rewrite Hnone;trivial.
Qed.
Lemma getMappedPageDefaultMapMMUPage vax s pdChildphy phyVaChild ptVaChildpd  r w e
(vaChild : vaddr) (phyDescChild : page) level entry: 
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 


getMappedPage pdChildphy s' vax = SomeDefault-> 
Some level = StateLib.getNbLevel -> 
StateLib.getPd phyDescChild (memory s) = Some pdChildphy -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s)
       beqPage beqIndex = Some (PE entry) -> 
consistency s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
In phyDescChild (getPartitions multiplexer s)-> 
(defaultPage =? ptVaChildpd) = false -> 
entryPresentFlag ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) false s -> 
checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false -> 
getMappedPage pdChildphy s vax = SomeDefault.
Proof.  
intros s' (* Hor *) Hvax Hlevel Hpp.
intros.
assert(Hindchild : getIndirection pdChildphy vaChild level (nbLevel - 1) s =
  Some ptVaChildpd). 
{ apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
  symmetry;trivial.
  intros;split;trivial.
  subst;trivial. }
rewrite <- Hvax. 
unfold getMappedPage.
rewrite <- Hlevel. 
case_eq(getIndirection pdChildphy vax level (nbLevel - 1) s );intros.
assert(Hii:   getIndirection pdChildphy vax level (nbLevel - 1) s' = Some p).
{ unfold consistency in *. 
  intuition.
  apply getIndirectionMapMMUPage2
    with (currentPartition s) false vaChild phyDescChild entry; subst;trivial.
   symmetry;trivial.
  apply nextEntryIsPPgetPd;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
rewrite Hii.
   assert(Hnodupconf : noDupConfigPagesList s).
    unfold consistency in *. 
    intuition.
  case_eq(defaultPage =? p);intros Hnotdef;trivial.  
   assert(ptVaChildpd <> p \/ (StateLib.getIndexOfAddr vaChild fstLevel) <> 
  (StateLib.getIndexOfAddr vax fstLevel)).
   apply pageTablesOrIndicesAreDifferent with pdChildphy pdChildphy
    level nbLevel s;trivial.
    apply pdPartNotNull with phyDescChild s;trivial.
    apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
    apply pdPartNotNull with phyDescChild s;trivial.
     apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
 
 apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.
 
 apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.
  left.
  split;trivial.
  apply getNbLevelEq.
  trivial.
  assert(Hdefaut: (defaultPage =? ptVaChildpd) = false) by trivial.
    apply beq_nat_false in Hdefaut.
    unfold not;intros;subst;now contradict Hdefaut.
  apply beq_nat_false in Hnotdef.
  unfold not;intros;subst;trivial.
  now contradict Hnotdef.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;symmetry;trivial.
 
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;symmetry;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s)
 = StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s')). 
 apply readPresentMapMMUPage with entry;trivial.
 intuition.
 rewrite <- Hpres.
 case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s));intros.
 destruct b;trivial.
 symmetry.
  assert(Heq : StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s')=
  StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s)).
  symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 intuition.
 rewrite Heq.
 trivial.
 trivial.
 assert(Hnone : getIndirection pdChildphy vax level (nbLevel - 1) s' = None).
 unfold consistency in *.
 intuition.
 apply getIndirectionNoneMapMMUPage2 with (currentPartition s) false vaChild phyDescChild entry;trivial.
symmetry. trivial.
apply nextEntryIsPPgetPd;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply nextEntryIsPPgetPd;trivial.
rewrite Hnone;trivial.
Qed.

Lemma getMappedPageNoneMapMMUPage' vax s pdChildphy phyVaChild ptVaChildpd  r w e
(vaChild : vaddr) (phyDescChild : page) level entry: 
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 


getMappedPage pdChildphy s vax = NonePage-> 
Some level = StateLib.getNbLevel -> 
StateLib.getPd phyDescChild (memory s) = Some pdChildphy -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s)
       beqPage beqIndex = Some (PE entry) -> 
consistency s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
In phyDescChild (getPartitions multiplexer s)-> 
(defaultPage =? ptVaChildpd) = false -> 
entryPresentFlag ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) false s -> 
checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false -> 
getMappedPage pdChildphy s' vax = NonePage.
Proof.  
intros s' (* Hor *) Hvax Hlevel Hpp.
intros.
assert(Hindchild : getIndirection pdChildphy vaChild level (nbLevel - 1) s =
  Some ptVaChildpd). 
{ apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
  symmetry;trivial.
  intros;split;trivial.
  subst;trivial. }
rewrite <- Hvax. 
unfold getMappedPage.
rewrite <- Hlevel. 
case_eq(getIndirection pdChildphy vax level (nbLevel - 1) s );intros.
assert(Hii:   getIndirection pdChildphy vax level (nbLevel - 1) s' = Some p).
{ unfold consistency in *. 
  intuition.
  apply getIndirectionMapMMUPage2
    with (currentPartition s) false vaChild phyDescChild entry; subst;trivial.
   symmetry;trivial.
  apply nextEntryIsPPgetPd;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
rewrite Hii.
   assert(Hnodupconf : noDupConfigPagesList s).
    unfold consistency in *. 
    intuition.
  case_eq(defaultPage =? p);intros Hnotdef;trivial.  
   assert(ptVaChildpd <> p \/ (StateLib.getIndexOfAddr vaChild fstLevel) <> 
  (StateLib.getIndexOfAddr vax fstLevel)).
   apply pageTablesOrIndicesAreDifferent with pdChildphy pdChildphy
    level nbLevel s;trivial.
    apply pdPartNotNull with phyDescChild s;trivial.
    apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
    apply pdPartNotNull with phyDescChild s;trivial.
     apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
 
 apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.
 
 apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.
  left.
  split;trivial.
  apply getNbLevelEq.
  trivial.
  assert(Hdefaut: (defaultPage =? ptVaChildpd) = false) by trivial.
    apply beq_nat_false in Hdefaut.
    unfold not;intros;subst;now contradict Hdefaut.
  apply beq_nat_false in Hnotdef.
  unfold not;intros;subst;trivial.
  now contradict Hnotdef.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;symmetry;trivial.
 
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;symmetry;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s)
 = StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s')). 
 apply readPresentMapMMUPage with entry;trivial.
 intuition.
 rewrite <- Hpres.
 case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s));intros.
 destruct b;trivial.
 assert(Heq : StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s')=
  StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s)).
  symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 intuition.
 rewrite Heq.
 trivial.
 trivial.
 assert(Hnone : getIndirection pdChildphy vax level (nbLevel - 1) s' = None).
 unfold consistency in *.
 intuition.
 apply getIndirectionNoneMapMMUPage2 with (currentPartition s) false vaChild phyDescChild entry;trivial.
symmetry. trivial.
apply nextEntryIsPPgetPd;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply nextEntryIsPPgetPd;trivial.
rewrite Hnone;trivial.
Qed.
Lemma getMappedPageDefaultMapMMUPage' vax s pdChildphy phyVaChild ptVaChildpd  r w e
(vaChild : vaddr) (phyDescChild : page) level entry: 
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 


getMappedPage pdChildphy s vax = SomeDefault-> 
Some level = StateLib.getNbLevel -> 
StateLib.getPd phyDescChild (memory s) = Some pdChildphy -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s)
       beqPage beqIndex = Some (PE entry) -> 
consistency s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
In phyDescChild (getPartitions multiplexer s)-> 
(defaultPage =? ptVaChildpd) = false -> 
entryPresentFlag ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) false s -> 
checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false -> 
getMappedPage pdChildphy s' vax = SomeDefault.
Proof.  
intros s' (* Hor *) Hvax Hlevel Hpp.
intros.
assert(Hindchild : getIndirection pdChildphy vaChild level (nbLevel - 1) s =
  Some ptVaChildpd). 
{ apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
  symmetry;trivial.
  intros;split;trivial.
  subst;trivial. }
rewrite <- Hvax. 
unfold getMappedPage.
rewrite <- Hlevel. 
case_eq(getIndirection pdChildphy vax level (nbLevel - 1) s );intros.
assert(Hii:   getIndirection pdChildphy vax level (nbLevel - 1) s' = Some p).
{ unfold consistency in *. 
  intuition.
  apply getIndirectionMapMMUPage2
    with (currentPartition s) false vaChild phyDescChild entry; subst;trivial.
   symmetry;trivial.
  apply nextEntryIsPPgetPd;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
rewrite Hii.
   assert(Hnodupconf : noDupConfigPagesList s).
    unfold consistency in *. 
    intuition.
  case_eq(defaultPage =? p);intros Hnotdef;trivial.  
   assert(ptVaChildpd <> p \/ (StateLib.getIndexOfAddr vaChild fstLevel) <> 
  (StateLib.getIndexOfAddr vax fstLevel)).
   apply pageTablesOrIndicesAreDifferent with pdChildphy pdChildphy
    level nbLevel s;trivial.
    apply pdPartNotNull with phyDescChild s;trivial.
    apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
    apply pdPartNotNull with phyDescChild s;trivial.
     apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
 
 apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.
 
 apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.
  left.
  split;trivial.
  apply getNbLevelEq.
  trivial.
  assert(Hdefaut: (defaultPage =? ptVaChildpd) = false) by trivial.
    apply beq_nat_false in Hdefaut.
    unfold not;intros;subst;now contradict Hdefaut.
  apply beq_nat_false in Hnotdef.
  unfold not;intros;subst;trivial.
  now contradict Hnotdef.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;symmetry;trivial.
 
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;symmetry;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s)
 = StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s')). 
 apply readPresentMapMMUPage with entry;trivial.
 intuition.
 rewrite <- Hpres.
 case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s));intros.
 destruct b;trivial.
 assert(Heq : StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s')=
  StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s)).
  symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 intuition.
 rewrite Heq.
 trivial.
 trivial.
 assert(Hnone : getIndirection pdChildphy vax level (nbLevel - 1) s' = None).
 unfold consistency in *.
 intuition.
 apply getIndirectionNoneMapMMUPage2 with (currentPartition s) false vaChild phyDescChild entry;trivial.
symmetry. trivial.
apply nextEntryIsPPgetPd;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply nextEntryIsPPgetPd;trivial.
rewrite Hnone;trivial.
Qed.
Lemma getMappedPagesMapMMUPage s ptVaChildpd idxvaChild phyVaChild e
 r w part phyDescChild vaChild entry level: 
 let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
 In ptVaChildpd (getConfigPages phyDescChild s) ->
disjoint (getConfigPages phyDescChild s) (getConfigPages part s) -> 
 lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
    Some (PE entry) ->
 Some level = StateLib.getNbLevel->
 configTablesAreDifferent s->
partitionDescriptorEntry s->
In phyDescChild (getPartitions multiplexer s)->
(forall idx : index,
     StateLib.getIndexOfAddr vaChild fstLevel = idx ->
     isPE ptVaChildpd idx s /\
     getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s)->
 (defaultPage =? ptVaChildpd) = false->

 phyDescChild <> part -> 
 In part (getPartitions multiplexer s)      ->               
 getMappedPages part s = getMappedPages part s'.
 Proof.
 intros s' Hconfigpt Hmykey2.
 intros.
   unfold getMappedPages. 
     assert(Hgetpd : forall partition, StateLib.getPd partition
  (add ptVaChildpd idxvaChild(PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) 
     (memory s) beqPage beqIndex ) = StateLib.getPd partition (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
intros. 
rewrite Hgetpd in *. clear Hgetpd.
case_eq(StateLib.getPd part (memory s) );[intros pd Hpd1 |intros Hpd1];
trivial.
unfold getMappedPagesAux.
unfold getMappedPagesOption.
f_equal.
induction getAllVAddrWithOffset0;simpl;trivial.
f_equal.
  assert(Hpde : partitionDescriptorEntry s).
  unfold consistency in *.
  intuition. 
{
  unfold getMappedPage.
  assert(Hlevel : Some level = StateLib.getNbLevel) by trivial.
  rewrite <- Hlevel.
  unfold configTablesAreDifferent in *.
  assert(Hconfigpart : forall ind stop,  
  getIndirection pd a level stop s = Some ind ->
  ind <> defaultPage -> 
  In ind (getIndirectionsAux pd s (nbLevel))).
  { intros.
    apply getIndirectionInGetIndirections with a level stop;trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    omega.
    apply getNbLevelEq in Hlevel.
    subst.
    omega.  
  unfold partitionDescriptorEntry in *.

  assert(Hexist : (exists entry : page,
          nextEntryIsPP part PDidx entry s /\ entry <> defaultPage)).
  
        apply Hpde;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pd).
apply getPdNextEntryIsPPEq  with part s;trivial.
subst;trivial. }
assert(Hconfig : forall ind, In ind (getIndirectionsAux pd s nbLevel) -> 
In ind (getConfigPages part s)).
{
intros.
unfold getConfigPages.
simpl. right.   
apply inGetIndirectionsAuxInConfigPagesPD with pd;trivial. }
assert(Hi : forall ind stop,  
  getIndirection pd a level stop s = Some ind ->
  ind <> defaultPage -> In ind (getConfigPages part s)). 
  { intros. apply Hconfig.
    apply Hconfigpart with stop;trivial. }
    clear Hconfigpt.
assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
apply isConfigTable  with vaChild;trivial.
intros. (* split. 
subst;trivial.
subst;trivial. *)
assert(Hmykey : forall stop tbl,
    getIndirection pd a level stop s = Some tbl -> 
    (defaultPage =? tbl) = false ->
      tbl <> ptVaChildpd ).
{ intros. 
  unfold not;intros.
  subst.
  unfold disjoint in *.
  unfold not in Hmykey2.
  apply Hmykey2 with ptVaChildpd;trivial.
  apply Hi with stop;trivial.
  assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial. 
  apply beq_nat_false in Hdefaut.
  intuition.
  subst.
  now contradict Hdefaut. }
assert(Hmykey3 : getIndirection pd a level (nbLevel - 1) s = 
getIndirection pd a level (nbLevel - 1) s').
{ 
   assert(Hpdnotnull : pd <> defaultPage). 
{ unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP part PDidx entry s /\ entry <> defaultPage)).
        apply Hpde;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pd).
apply getPdNextEntryIsPPEq  with part s;trivial.
subst;trivial. }
assert(Hlookup :lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
     Some (PE entry)) by trivial.
revert Hmykey Hlookup Hpdnotnull.
   clear.
     intros. 
     apply getIndirectionMapMMUPage1 with entry;trivial. }
rewrite <- Hmykey3.
 case_eq( getIndirection pd a level (nbLevel - 1) s);intros. 
 case_eq( defaultPage =? p);intros;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 apply readPresentMapMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hpres.
 assert(Hread :StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 apply readPhyEntryMapMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hread.
 trivial.
 trivial. }
 trivial.
 
 Qed.
 
 Lemma getMappedPageMapMMUPageEq s ptVaChildpd idxvaChild phyVaChild e
 r w part phyDescChild vaChild entry level: 
 let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
 In ptVaChildpd (getConfigPages phyDescChild s) ->
disjoint (getConfigPages phyDescChild s) (getConfigPages part s) -> 
 lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
    Some (PE entry) ->
 Some level = StateLib.getNbLevel->
 configTablesAreDifferent s->
partitionDescriptorEntry s->
In phyDescChild (getPartitions multiplexer s)->
(forall idx : index,
     StateLib.getIndexOfAddr vaChild fstLevel = idx ->
     isPE ptVaChildpd idx s /\
     getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s)->
 (defaultPage =? ptVaChildpd) = false->

 phyDescChild <> part -> 
 In part (getPartitions multiplexer s)      ->  
 forall pd a, StateLib.getPd part (memory s) = Some pd ->              
 getMappedPage pd s a = getMappedPage pd s' a.
 Proof.
 intros s' Hconfigpt Hmykey2.
 intros.

  assert(Hpde : partitionDescriptorEntry s).
  unfold consistency in *.
  intuition. 
{
  unfold getMappedPage.
  assert(Hlevel : Some level = StateLib.getNbLevel) by trivial.
  rewrite <- Hlevel.
  unfold configTablesAreDifferent in *.
  assert(Hconfigpart : forall ind stop,  
  getIndirection pd a level stop s = Some ind ->
  ind <> defaultPage -> 
  In ind (getIndirectionsAux pd s (nbLevel))).
  { intros.
    apply getIndirectionInGetIndirections with a level stop;trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    omega.
    apply getNbLevelEq in Hlevel.
    subst.
    omega.  
  unfold partitionDescriptorEntry in *.

  assert(Hexist : (exists entry : page,
          nextEntryIsPP part PDidx entry s /\ entry <> defaultPage)).
  
        apply Hpde;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pd).
apply getPdNextEntryIsPPEq  with part s;trivial.
subst;trivial. }
assert(Hconfig : forall ind, In ind (getIndirectionsAux pd s nbLevel) -> 
In ind (getConfigPages part s)).
{
intros.
unfold getConfigPages.
simpl. right.   
apply inGetIndirectionsAuxInConfigPagesPD with pd;trivial. }
assert(Hi : forall ind stop,  
  getIndirection pd a level stop s = Some ind ->
  ind <> defaultPage -> In ind (getConfigPages part s)). 
  { intros. apply Hconfig.
    apply Hconfigpart with stop;trivial. }
    clear Hconfigpt.
assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
apply isConfigTable  with vaChild;trivial.
intros. (* split. 
subst;trivial.
subst;trivial. *)
assert(Hmykey : forall stop tbl,
    getIndirection pd a level stop s = Some tbl -> 
    (defaultPage =? tbl) = false ->
      tbl <> ptVaChildpd ).
{ intros. 
  unfold not;intros.
  subst.
  unfold disjoint in *.
  unfold not in Hmykey2.
  apply Hmykey2 with ptVaChildpd;trivial.
  apply Hi with stop;trivial.
  assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial. 
  apply beq_nat_false in Hdefaut.
  intuition.
  subst.
  now contradict Hdefaut. }
assert(Hmykey3 : getIndirection pd a level (nbLevel - 1) s = 
getIndirection pd a level (nbLevel - 1) s').
{ 
   assert(Hpdnotnull : pd <> defaultPage). 
{ unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP part PDidx entry s /\ entry <> defaultPage)).
        apply Hpde;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pd).
apply getPdNextEntryIsPPEq  with part s;trivial.
subst;trivial. }
assert(Hlookup :lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
     Some (PE entry)) by trivial.
revert Hmykey Hlookup Hpdnotnull.
   clear.
     intros. 
     apply getIndirectionMapMMUPage1 with entry;trivial. }
rewrite <- Hmykey3.
 case_eq( getIndirection pd a level (nbLevel - 1) s);intros. 
 case_eq( defaultPage =? p);intros;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 apply readPresentMapMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hpres.
 assert(Hread :StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 apply readPhyEntryMapMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hread.
 trivial.
 trivial. }
 Qed.
 
  Lemma getMappedPageKeepsAnyMappedPage pdChildphy s vax vaChild
        ptVaChildpd x phyVaChild r w e phyDescChild entry level
        (currentPart:page) :
        let s':={|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
     lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
            (memory s) beqPage beqIndex = Some (PE entry) -> 
            Some level = StateLib.getNbLevel -> 
      getMappedPage pdChildphy s vax = SomePage x ->
entryPresentFlag ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) false
  s -> StateLib.getPd phyDescChild (memory s) = Some pdChildphy
  -> 
  partitionDescriptorEntry s -> 
isPresentNotDefaultIff s -> 
noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
pdChildphy <> defaultPage-> 
getIndirection pdChildphy vaChild level (nbLevel - 1) s = Some ptVaChildpd -> 
  getMappedPage pdChildphy s' vax = SomePage x.
  Proof.
  intros s' Hlookup Hlevel Hmap Hpres Hpd.
  intros.
  unfold getMappedPage in *.
  rewrite <- Hlevel in *.
  case_eq(getIndirection pdChildphy vax level (nbLevel - 1) s );
  [intros ind Hind | intros Hind];rewrite Hind in *;
  try now contradict Hmap.
  assert(Hind' :getIndirection pdChildphy vax level (nbLevel - 1) s'
  = Some ind).
  { apply getIndirectionMapMMUPage2
  with currentPart
false vaChild phyDescChild entry;trivial.
symmetry ;trivial. }
rewrite Hind'.
case_eq(defaultPage =? ind);intros Hdef;rewrite Hdef in *.
now contradict Hmap.
case_eq(StateLib.readPresent ind (StateLib.getIndexOfAddr vax fstLevel)
           (memory s));[intros ispres Hispres | intros Hispres];
           rewrite Hispres in *;try now contradict Hmap.
case_eq(ispres);intros Hb;rewrite Hb in *;clear Hb;try now contradict Hmap.
move Hpres at bottom.
assert(Hispres1 : StateLib.readPresent ind (StateLib.getIndexOfAddr vax fstLevel)
            (memory s) = Some true) by trivial.
unfold entryPresentFlag in Hpres.
  unfold StateLib.readPresent in Hispres.
assert(Hmykey5 : ind <> ptVaChildpd \/
StateLib.getIndexOfAddr vax fstLevel <>
StateLib.getIndexOfAddr vaChild fstLevel). 
{
  assert(Hor : (  (ind <> ptVaChildpd \/
StateLib.getIndexOfAddr vax fstLevel <>
StateLib.getIndexOfAddr vaChild fstLevel) \/  (~ (ind <> ptVaChildpd \/
StateLib.getIndexOfAddr vax fstLevel <>
StateLib.getIndexOfAddr vaChild fstLevel)))).
{ apply classic. }
destruct Hor as [Hor | Hor];trivial.
apply not_or_and in Hor.
destruct Hor as(Hi1 & Hi2) .
subst.
apply NNPP in Hi1.
apply NNPP in Hi2.
rewrite Hi2 in *. clear Hi2.
subst.
destruct (lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
              (memory s) beqPage beqIndex);simpl in *;try now contradict Hpres.
destruct v;try now contradict Hpres.
inversion Hispres.
subst.
destruct (present p);try now contradict Hpres. }


assert(Hpreseq :  StateLib.readPresent ind (StateLib.getIndexOfAddr vax fstLevel) (memory s') =
  StateLib.readPresent ind (StateLib.getIndexOfAddr vax fstLevel) (memory s)).
  { symmetry. apply readPresentMapMMUPage with entry;trivial. }
rewrite Hpreseq.
rewrite Hispres1.
rewrite <- Hmap.
symmetry.
 assert(Heq : StateLib.readPhyEntry ind (StateLib.getIndexOfAddr vax fstLevel) (memory s')=
  StateLib.readPhyEntry ind (StateLib.getIndexOfAddr vax fstLevel) (memory s)).
  symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 rewrite Heq.
 trivial.
Qed.

Lemma getIndirectionMapMMUPage4 s ptVaChildpd idxvaChild phyVaChild r w e  
  pdChildphy currentPart va p
presentvaChild vaChild phyDescChild level entry stop1 idxroot:
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
pdChildphy <> defaultPage -> 

getIndirection pdChildphy vaChild level (nbLevel - 1) s =
            Some ptVaChildpd -> 
forall part pd, nextEntryIsPP part idxroot pd s -> (idxroot = PDidx \/
idxroot =sh1idx \/ idxroot = sh2idx) ->   In part (getPartitions multiplexer s) -> 
           (*  stop1 <= (nbLevel -1) ->  *)
   getIndirection pd va level stop1 s' = Some p -> 
getIndirection pd va level stop1 s= Some p.
Proof.
intros s' Hpde Hpresdef Hnodup2 Hconfigdiff Hparts Haccess Hlookup Hlevel 
 Hnotpresent Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild Hpdchildnotnull Hindchild part pd Hpppart Hidxroot Hpart (* H *).
assert(Hor : part= phyDescChild \/ part <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
+ subst.

(*   . *)
{ assert(forall stop tbl,
    stop < level  -> 
    getIndirection pd va level stop s = Some tbl -> 
    (defaultPage =? tbl) = false ->
      tbl <> ptVaChildpd ). 
    {  destruct Hidxroot as [Hidxroot | Hidxroot].
 * subst.
 assert(pd = pdChildphy).
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  apply nextEntryIsPPgetPd;trivial.
  subst.
 assert(Hnodup : NoDup (getIndirections pdChildphy s)).
      { apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition. }
      intros.     
      assert(~In ptVaChildpd (getIndirectionsAux pdChildphy s (stop+1))). 
      { assert(~In ptVaChildpd (getIndirectionsAux pdChildphy s (nbLevel-1))). 
    {  assert(0<nbLevel) by apply nbLevelNotZero.
      assert(nbLevel - 1 + 1 = nbLevel) by omega.
    
 
 assert(Hprevious : exists prevtab,
      getIndirection pdChildphy vaChild level (nbLevel - 2) s =
            Some prevtab /\prevtab <> defaultPage /\  StateLib.readPhyEntry prevtab
  (StateLib.getIndexOfAddr vaChild (CLevel (level- ((nbLevel - 1) - 1)))) (memory s) =
Some ptVaChildpd). 
{   revert Hindchild   Hdefaut  (*  H0 *).


  assert(Hstooo : level > (nbLevel - 1 -1)).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    unfold CLevel in H.
    rewrite H4 in *.
    simpl in *.
    
    omega.
    omega. } 

  
  assert(Htpp : 0 < nbLevel -1).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    unfold CLevel in H.
    rewrite H4 in *.
    simpl in *.
    
    omega.
    omega.
    
     } 
  assert(Hnotdef : pdChildphy <> defaultPage) by intuition. 
  revert Hstooo Htpp Hnotdef.
  clear. 
  replace (nbLevel -2) with (nbLevel -1 -1) by omega.  
  revert pdChildphy level ptVaChildpd.
  induction (nbLevel-1);simpl.
  intros.
  omega.
  intros. 
  case_eq(StateLib.Level.eqb level fstLevel);intros;
  rewrite H in *.
  apply levelEqBEqNatTrue0 in H. 
  omega.
   case_eq(StateLib.readPhyEntry pdChildphy
                (StateLib.getIndexOfAddr vaChild level) (memory s));intros;
    rewrite H0 in *;try now contradict Hindchild.
    case_eq(defaultPage =? p);intros;rewrite H1 in *.
    apply beq_nat_false in Hdefaut.
    inversion Hindchild.
    subst.
    now contradict Hdefaut.
    case_eq(StateLib.Level.pred level );intros;rewrite H2 in *.
    + replace (n-0) with n by omega.
    assert(Hooo : n = 0 \/ 0 < n) by omega.
    destruct Hooo.
    *
    subst. 
    simpl in *. 
    exists  pdChildphy;split;trivial.
    inversion Hindchild. 
    subst. 
    rewrite <- H0.
    split.  trivial. 
    f_equal.
    f_equal.
    rewrite <- minus_n_O.
    apply CLevelIdentity1.
    * assert(Hii : l > n - 1  ) .
    apply levelPredMinus1 in H2.
    subst.
   unfold CLevel.
    case_eq( lt_dec (level - 1) nbLevel );intros.
    simpl.
    omega.
    destruct level.
    simpl in *.
    omega.
    trivial.
    assert(Hi1 : p <> defaultPage).
    apply beq_nat_false in H1.
    intuition.
    subst.
    now contradict H1. 
      generalize(IHn p l ptVaChildpd Hii H3 Hi1 Hindchild Hdefaut
       );clear IHn ; intros iHn .
       destruct iHn as (prevtab & Hindprev & Hdef & Hread).
       exists prevtab;split;trivial.
       intros.
       assert(Hs :S(n-1) = n) by omega.
       rewrite <- Hs.
       simpl.
       rewrite H.
       rewrite H0. 
       rewrite H1.
       rewrite H2;trivial.
       split;trivial.
       rewrite <- Hread.
       f_equal.
       f_equal.
       f_equal.
apply levelPredMinus1 in H2.
rewrite H2.
unfold CLevel.
case_eq(lt_dec (level - 1) nbLevel);intros. 
simpl. 
omega.
destruct level. 
simpl in *.
omega.
trivial.
+ assert(Hnotnone : StateLib.Level.pred level <> None).
apply levelPredNone;trivial. now contradict Hnotnone.  }
destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev). 
       apply getIndirectionInGetIndirections2 with prevtab vaChild level;
      simpl; subst;
      trivial.
      omega.
      simpl.
      rewrite <- Hprevtable.
      f_equal.
      omega.
      rewrite H3. 
      unfold getIndirections in *;trivial.

(*       symmetry in Hlevel.
      apply getNbLevelEq in Hlevel.
      rewrite Hlevel in *.
      unfold CLevel in H0. 
      assert (0<nbLevel) by apply nbLevelNotZero.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros;
      rewrite H6 in *.
      simpl in *.
      omega.
      omega.
      omega. *)
      apply beq_nat_false in Hdefaut.
      unfold not;intros;subst.
      now contradict Hdefaut. 
      move Hlevel at bottom.
      symmetry in Hlevel.

      apply getNbLevelEq in Hlevel.
      rewrite Hlevel.
      unfold CLevel. 
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros. 
      simpl. 
      omega.
      omega.
      }
      unfold not;intros. contradict H2.
      assert(Hincl : incl (getIndirectionsAux pdChildphy s (stop + 1))
      (getIndirectionsAux pdChildphy s (nbLevel - 1))).
      apply inclGetIndirectionsAuxLe;trivial.
      symmetry in Hlevel.
      apply getNbLevelEq in Hlevel.
      subst.
      unfold CLevel in H.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      rewrite H2 in *. 
      simpl in *. omega.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      unfold incl in *. 
      apply Hincl;trivial.
      }
     
      assert(In tbl (getIndirectionsAux pdChildphy s (stop+1))). 
      { apply getIndirectionInGetIndirections1 with va level;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      assert(level < nbLevel).
      apply getNbLevelLt;trivial.      
      omega.
      apply beq_nat_false in H1.
      unfold not;intros;subst.
       
      now contradict H1.  }
      unfold not;intros.
      subst.
      now contradict H3.
   *  unfold noDupConfigPagesList in *. 
      
 destruct Hidxroot; subst.
- intros. 
  assert(Hdisjoint: disjoint (getIndirections pdChildphy s) (getIndirections pd s)). 
  apply Hnodup2 in Hpart.
  unfold getConfigPages in *.
  apply NoDup_cons_iff in Hpart as(_ & Hpart).
  clear Hnodup2.
  unfold getConfigPagesAux in Hpart.
  rewrite nextEntryIsPPgetPd in *. 
  rewrite Hpdchild in Hpart.
    rewrite nextEntryIsPPgetFstShadow in *. 
  rewrite Hpppart in *.
  case_eq (getSndShadow phyDescChild (memory s));[intros sh2 Hsh2 | intros Hsh2] ;
  rewrite Hsh2 in *.
  case_eq (getConfigTablesLinkedList phyDescChild (memory s));[intros ll Hll| intros Hll] ;
  rewrite Hll in *.
  rewrite NoDupSplitInclIff in Hpart.
  destruct Hpart as (Hpart1 & Hpart2).
  unfold disjoint in *. 
  intros x Hdis1.   
  apply Hpart2 in Hdis1.
  intuition.
  assert(False).
  apply getConfigTablesRootNotNone with phyDescChild s;trivial.
  intuition.
  assert(False).
  apply sh2PartNotNone with phyDescChild s;trivial.
  intuition.
  assert(Hin1 : In  ptVaChildpd (getIndirections pdChildphy s)). 
  unfold getIndirections.
  assert(Hpdchild1 : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Htblroot in Hpdchild.
  destruct Hpdchild as (nbL & HnbL & stopx & Hstop & Hind).
   apply getIndirectionInGetIndirections with vaChild nbL stopx;trivial.
  assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in Hdefaut.
  unfold not;intros;subst.
  now contradict Hdefaut.
  apply getNbLevelLe in HnbL;trivial.
  assert(Hin2 : In  tbl (getIndirections pd s)). 
  unfold getIndirections.
  apply getIndirectionInGetIndirections with va level stop;trivial.
   assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in H1.
  unfold not;intros;subst.
  now contradict H0.
  symmetry in Hlevel.
  apply getNbLevelLe in Hlevel;trivial.  
  apply sh1PartNotNull with phyDescChild s;trivial.
  unfold not;intros.
  subst.
  unfold disjoint in *.
  unfold not in *.
  apply Hdisjoint with ptVaChildpd;trivial.

- intros. 
  assert(Hdisjoint: disjoint (getIndirections pdChildphy s) (getIndirections pd s)). 
  apply Hnodup2 in Hpart.
  unfold getConfigPages in *.
  apply NoDup_cons_iff in Hpart as(_ & Hpart).
  clear Hnodup2.
  unfold getConfigPagesAux in Hpart.
  rewrite nextEntryIsPPgetPd in *. 
  rewrite Hpdchild in Hpart.
  case_eq (getFstShadow phyDescChild (memory s));[intros sh1 Hsh1 | intros Hsh1] ;
  rewrite Hsh1 in *.
      rewrite nextEntryIsPPgetSndShadow in *. 
  rewrite Hpppart in *.
  case_eq (getConfigTablesLinkedList phyDescChild (memory s));[intros ll Hll| intros Hll] ;
  rewrite Hll in *.
  rewrite NoDupSplitInclIff in Hpart.
  destruct Hpart as (Hpart1 & Hpart2).
  unfold disjoint in *. 
  intros x Hdis1.   
  apply Hpart2 in Hdis1.
  rewrite in_app_iff in Hdis1.
  apply not_or_and in Hdis1.
  
  intuition.
  assert(False).
  apply getConfigTablesRootNotNone with phyDescChild s;trivial.
  intuition.
  assert(False).
  apply sh1PartNotNone with phyDescChild s;trivial.
  intuition.
  assert(Hin1 : In  ptVaChildpd (getIndirections pdChildphy s)). 
  unfold getIndirections.
  assert(Hpdchild1 : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Htblroot in Hpdchild.
  destruct Hpdchild as (nbL & HnbL & stopx & Hstop & Hind).
   apply getIndirectionInGetIndirections with vaChild nbL stopx;trivial.
  assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in Hdefaut.
  unfold not;intros;subst.
  now contradict Hdefaut.
  apply getNbLevelLe in HnbL;trivial.
  assert(Hin2 : In  tbl (getIndirections pd s)). 
  unfold getIndirections.
  apply getIndirectionInGetIndirections with va level stop;trivial.
   assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in H1.
  unfold not;intros;subst.
  now contradict H0.
  symmetry in Hlevel.
  apply getNbLevelLe in Hlevel;trivial.  
  apply sh2PartNotNull with phyDescChild s;trivial.
  unfold not;intros.
  subst.
  unfold disjoint in *.
  unfold not in *.
  apply Hdisjoint with ptVaChildpd;trivial. 



     

     } 
     
     
    assert(Hlevel1 :  level <= CLevel (nbLevel - 1) ).
    apply getNbLevelLe;trivial.
    symmetry;trivial.
    intros Hi.
    rewrite <- Hi. 
    clear Hlevel. 
    (* assert (Hxi : stop1 <= nbLevel - 1) by trivial. *)
    assert(Hrootnotnull: pd <> defaultPage).
    {    destruct Hidxroot as [Hidxroot | Hidxroot];subst.
    apply pdPartNotNull with phyDescChild s;trivial.
    destruct Hidxroot  as [Hidxroot | Hidxroot];subst.
    apply sh1PartNotNull with phyDescChild s;trivial.
    apply sh2PartNotNull with phyDescChild s;trivial. }
    revert H (* Hxi *) Hlevel1 Hlookup Hrootnotnull Hidxroot.
    clear.
    generalize level at 1 2 3 4 5  as l.
    revert pd. 
  induction stop1;simpl; intros;trivial.
  case_eq( StateLib.Level.eqb l fstLevel);intros;trivial.
   assert(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va l)
    (add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va l)
    (memory s)). symmetry.
    apply readPhyEntryMapMMUPage with entry;trivial.
    left.
    generalize (H 0 pd);clear H;intros H. 
    simpl in *. 
    apply H. 
    apply levelEqBEqNatFalse0;trivial. reflexivity.
    apply NPeano.Nat.eqb_neq.
    clear Hidxroot.
    intuition.
    subst.
    apply Hrootnotnull.
    destruct defaultPage;destruct pd.
    simpl in *.
    subst.
    f_equal.
    apply proof_irrelevance.
    rewrite H1.
    case_eq( StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va l)
    (memory s));intros;trivial.
    case_eq(defaultPage =? p);intros;trivial.
    case_eq(StateLib.Level.pred l );intros;trivial.
    apply IHstop1;trivial.
    intros.
    apply H with (S stop).
    simpl.
     apply levelPredMinus1 in H4;trivial.
     rewrite H4 in *.
       unfold CLevel in H5.
   case_eq(lt_dec (l - 1) nbLevel);intros.
   rewrite H8 in *. 
   simpl in *.
   omega.
   destruct l. 
   simpl in *.
   omega.
   simpl.
    rewrite H4.
    rewrite H0.
    rewrite H2.
    rewrite H3.
    trivial.
    trivial.
    move    Hlevel1 at bottom.
    trivial.
    apply levelPredMinus1 in H4;trivial.
    rewrite H4.
    unfold CLevel.
    unfold CLevel in Hlevel1.
   case_eq(lt_dec (l - 1) nbLevel);intros.
   simpl.
   case_eq(lt_dec (nbLevel - 1) nbLevel);intros;
   rewrite H6 in *.
   simpl in *.
   subst.
   omega.
   omega.
   subst.
   destruct l. 
   simpl in *.
   omega.
   apply beq_nat_false in H3. 
   unfold not;intros;subst. now contradict H3. }
+ intros Hi1.
  rewrite  <- Hi1.
  unfold s'.
  apply getIndirectionMapMMUPage11 with entry;trivial.
  intros.
  assert(Hin1 : In tbl (getIndirectionsAux pd s nbLevel)).
  { apply getIndirectionInGetIndirections with va level stop;trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    omega.
    apply beq_nat_false in H0.
    unfold not;intros Hnot;subst.
    now contradict H0.
    symmetry in Hlevel.
    apply getNbLevelEq in Hlevel.
    subst.
    omega.
    destruct Hidxroot as [Hidxroot | Hidxroot];subst.
    apply pdPartNotNull with part s;trivial.
    destruct Hidxroot  as [Hidxroot | Hidxroot];subst.
    apply sh1PartNotNull with part s;trivial.
    apply sh2PartNotNull with part s;trivial. }
  assert(Hin2 : In ptVaChildpd (getIndirectionsAux pdChildphy s nbLevel)).
  { apply getIndirectionInGetIndirections with vaChild level (nbLevel - 1);trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    omega.
    apply beq_nat_false in Hdefaut.
    clear Hidxroot.
    intuition.
    subst.
    now contradict Hdefaut.
    symmetry in Hlevel.
    apply getNbLevelEq in Hlevel.
    subst.
    omega. }
  unfold not;intros.
  subst.
  assert(Hin11 : In ptVaChildpd (getConfigPages phyDescChild s)).
  apply isConfigTable  with vaChild;trivial.
  intros;subst;split;trivial.
  assert(Hconfig : configTablesAreDifferent s) by trivial.
  unfold configTablesAreDifferent in *.
  unfold disjoint in *.
  
  
  contradict Hin11.
  apply Hconfig with part;trivial.
  unfold getConfigPages;simpl;right.
  destruct Hidxroot as [Hidxroot | Hidxroot];subst.
  apply inGetIndirectionsAuxInConfigPagesPD with pd;trivial.
  apply nextEntryIsPPgetPd;trivial.
  destruct Hidxroot as [Hidxroot | Hidxroot];subst.
  apply inGetIndirectionsAuxInConfigPagesSh1 with pd;trivial.
  apply nextEntryIsPPgetFstShadow;trivial.
  apply inGetIndirectionsAuxInConfigPagesSh2 with pd;trivial.
  apply nextEntryIsPPgetSndShadow;trivial.
      destruct Hidxroot as [Hidxroot | Hidxroot];subst.
    apply pdPartNotNull with part s;trivial.
    destruct Hidxroot  as [Hidxroot | Hidxroot];subst.
    apply sh1PartNotNull with part s;trivial.
    apply sh2PartNotNull with part s;trivial. 
   Qed. 
   Lemma getIndirectionMapMMUPage4None s ptVaChildpd idxvaChild phyVaChild r w e  
  pdChildphy currentPart va
presentvaChild vaChild phyDescChild level entry stop1 idxroot:
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
pdChildphy <> defaultPage -> 

getIndirection pdChildphy vaChild level (nbLevel - 1) s =
            Some ptVaChildpd -> 
forall part pd, nextEntryIsPP part idxroot pd s -> (idxroot = PDidx \/
idxroot =sh1idx \/ idxroot = sh2idx) ->   In part (getPartitions multiplexer s) -> 
           (*  stop1 <= (nbLevel -1) ->  *)
   getIndirection pd va level stop1 s' = None -> 
getIndirection pd va level stop1 s= None.
Proof.
intros s' Hpde Hpresdef Hnodup2 Hconfigdiff Hparts Haccess Hlookup Hlevel 
 Hnotpresent Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild Hpdchildnotnull Hindchild part pd Hpppart Hidxroot Hpart (* H *).
assert(Hor : part= phyDescChild \/ part <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
+ subst.

(*   . *)
{ assert(forall stop tbl,
    stop < level  -> 
    getIndirection pd va level stop s = Some tbl -> 
    (defaultPage =? tbl) = false ->
      tbl <> ptVaChildpd ). 
    {  destruct Hidxroot as [Hidxroot | Hidxroot].
 * subst.
 assert(pd = pdChildphy).
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  apply nextEntryIsPPgetPd;trivial.
  subst.
 assert(Hnodup : NoDup (getIndirections pdChildphy s)).
      { 
 apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition. }
      intros.      
      assert(~In ptVaChildpd (getIndirectionsAux pdChildphy s (stop+1))). 
      { assert(~In ptVaChildpd (getIndirectionsAux pdChildphy s (nbLevel-1))). 
    {  assert(0<nbLevel) by apply nbLevelNotZero.
      assert(nbLevel - 1 + 1 = nbLevel) by omega.
    
 
 assert(Hprevious : exists prevtab,
      getIndirection pdChildphy vaChild level (nbLevel - 2) s =
            Some prevtab /\prevtab <> defaultPage /\  StateLib.readPhyEntry prevtab
  (StateLib.getIndexOfAddr vaChild (CLevel (level- ((nbLevel - 1) - 1)))) (memory s) =
Some ptVaChildpd). 
{   revert Hindchild   Hdefaut  (*  H0 *).


  assert(Hstooo : level > (nbLevel - 1 -1)).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    unfold CLevel in H.
    rewrite H4 in *.
    simpl in *.
    
    omega.
    omega. } 

  
  assert(Htpp : 0 < nbLevel -1).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    unfold CLevel in H.
    rewrite H4 in *.
    simpl in *.
    
    omega.
    omega.
    
     } 
  assert(Hnotdef : pdChildphy <> defaultPage) by intuition. 
  revert Hstooo Htpp Hnotdef.
  clear. 
  replace (nbLevel -2) with (nbLevel -1 -1) by omega.  
  revert pdChildphy level ptVaChildpd.
  induction (nbLevel-1);simpl.
  intros.
  omega.
  intros. 
  case_eq(StateLib.Level.eqb level fstLevel);intros;
  rewrite H in *.
  apply levelEqBEqNatTrue0 in H. 
  omega.
   case_eq(StateLib.readPhyEntry pdChildphy
                (StateLib.getIndexOfAddr vaChild level) (memory s));intros;
    rewrite H0 in *;try now contradict Hindchild.
    case_eq(defaultPage =? p);intros;rewrite H1 in *.
    apply beq_nat_false in Hdefaut.
    inversion Hindchild.
    subst.
    now contradict Hdefaut.
    case_eq(StateLib.Level.pred level );intros;rewrite H2 in *.
    + replace (n-0) with n by omega.
    assert(Hooo : n = 0 \/ 0 < n) by omega.
    destruct Hooo.
    *
    subst. 
    simpl in *. 
    exists  pdChildphy;split;trivial.
    inversion Hindchild. 
    subst. 
    rewrite <- H0.
    split.  trivial. 
    f_equal.
    f_equal.
    rewrite <- minus_n_O.
    apply CLevelIdentity1.
    * assert(Hii : l > n - 1  ) .
    apply levelPredMinus1 in H2.
    subst.
   unfold CLevel.
    case_eq( lt_dec (level - 1) nbLevel );intros.
    simpl.
    omega.
    destruct level.
    simpl in *.
    omega.
    trivial.
    assert(Hi1 : p <> defaultPage).
    apply beq_nat_false in H1.
    intuition.
    subst.
    now contradict H1. 
      generalize(IHn p l ptVaChildpd Hii H3 Hi1 Hindchild Hdefaut
       );clear IHn ; intros iHn .
       destruct iHn as (prevtab & Hindprev & Hdef & Hread).
       exists prevtab;split;trivial.
       intros.
       assert(Hs :S(n-1) = n) by omega.
       rewrite <- Hs.
       simpl.
       rewrite H.
       rewrite H0. 
       rewrite H1.
       rewrite H2;trivial.
       split;trivial.
       rewrite <- Hread.
       f_equal.
       f_equal.
       f_equal.
apply levelPredMinus1 in H2.
rewrite H2.
unfold CLevel.
case_eq(lt_dec (level - 1) nbLevel);intros. 
simpl. 
omega.
destruct level. 
simpl in *.
omega.
trivial.
+ assert(Hnotnone : StateLib.Level.pred level <> None).
apply levelPredNone;trivial. now contradict Hnotnone.  }
destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev). 
       apply getIndirectionInGetIndirections2 with prevtab vaChild level;
      simpl; subst;
      trivial.
      omega.
      simpl.
      rewrite <- Hprevtable.
      f_equal.
      omega.
      rewrite H3. 
      unfold getIndirections in *;trivial.

(*       symmetry in Hlevel.
      apply getNbLevelEq in Hlevel.
      rewrite Hlevel in *.
      unfold CLevel in H0. 
      assert (0<nbLevel) by apply nbLevelNotZero.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros;
      rewrite H6 in *.
      simpl in *.
      omega.
      omega.
      omega. *)
      apply beq_nat_false in Hdefaut.
      unfold not;intros;subst.
      now contradict Hdefaut. 
      move Hlevel at bottom.
      symmetry in Hlevel.

      apply getNbLevelEq in Hlevel.
      rewrite Hlevel.
      unfold CLevel. 
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros. 
      simpl. 
      omega.
      omega.
      }
      unfold not;intros. contradict H2.
      assert(Hincl : incl (getIndirectionsAux pdChildphy s (stop + 1))
      (getIndirectionsAux pdChildphy s (nbLevel - 1))).
      apply inclGetIndirectionsAuxLe;trivial.
      symmetry in Hlevel.
      apply getNbLevelEq in Hlevel.
      subst.
      unfold CLevel in H.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      rewrite H2 in *. 
      simpl in *. omega.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      unfold incl in *. 
      apply Hincl;trivial.
      }
     
      assert(In tbl (getIndirectionsAux pdChildphy s (stop+1))). 
      { apply getIndirectionInGetIndirections1 with va level;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      assert(level < nbLevel).
      apply getNbLevelLt;trivial.      
      omega.
      apply beq_nat_false in H1.
      unfold not;intros;subst.
       
      now contradict H1.  }
      unfold not;intros.
      subst.
      now contradict H3.
   *  unfold noDupConfigPagesList in *. 
      
 destruct Hidxroot; subst.
- intros. 
  assert(Hdisjoint: disjoint (getIndirections pdChildphy s) (getIndirections pd s)). 
  apply Hnodup2 in Hpart.
  unfold getConfigPages in *.
  apply NoDup_cons_iff in Hpart as(_ & Hpart).
  clear Hnodup2.
  unfold getConfigPagesAux in Hpart.
  rewrite nextEntryIsPPgetPd in *. 
  rewrite Hpdchild in Hpart.
    rewrite nextEntryIsPPgetFstShadow in *. 
  rewrite Hpppart in *.
  case_eq (getSndShadow phyDescChild (memory s));[intros sh2 Hsh2 | intros Hsh2] ;
  rewrite Hsh2 in *.
  case_eq (getConfigTablesLinkedList phyDescChild (memory s));[intros ll Hll| intros Hll] ;
  rewrite Hll in *.
  rewrite NoDupSplitInclIff in Hpart.
  destruct Hpart as (Hpart1 & Hpart2).
  unfold disjoint in *. 
  intros x Hdis1.   
  apply Hpart2 in Hdis1.
  intuition.
  assert(False).
  apply getConfigTablesRootNotNone with phyDescChild s;trivial.
  intuition.
  assert(False).
  apply sh2PartNotNone with phyDescChild s;trivial.
  intuition.
  assert(Hin1 : In  ptVaChildpd (getIndirections pdChildphy s)). 
  unfold getIndirections.
  assert(Hpdchild1 : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Htblroot in Hpdchild.
  destruct Hpdchild as (nbL & HnbL & stopx & Hstop & Hind).
   apply getIndirectionInGetIndirections with vaChild nbL stopx;trivial.
  assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in Hdefaut.
  unfold not;intros;subst.
  now contradict Hdefaut.
  apply getNbLevelLe in HnbL;trivial.
  assert(Hin2 : In  tbl (getIndirections pd s)). 
  unfold getIndirections.
  apply getIndirectionInGetIndirections with va level stop;trivial.
   assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in H1.
  unfold not;intros;subst.
  now contradict H0.
  symmetry in Hlevel.
  apply getNbLevelLe in Hlevel;trivial.  
  apply sh1PartNotNull with phyDescChild s;trivial.
  unfold not;intros.
  subst.
  unfold disjoint in *.
  unfold not in *.
  apply Hdisjoint with ptVaChildpd;trivial.

- intros. 
  assert(Hdisjoint: disjoint (getIndirections pdChildphy s) (getIndirections pd s)). 
  apply Hnodup2 in Hpart.
  unfold getConfigPages in *.
  apply NoDup_cons_iff in Hpart as(_ & Hpart).
  clear Hnodup2.
  unfold getConfigPagesAux in Hpart.
  rewrite nextEntryIsPPgetPd in *. 
  rewrite Hpdchild in Hpart.
  case_eq (getFstShadow phyDescChild (memory s));[intros sh1 Hsh1 | intros Hsh1] ;
  rewrite Hsh1 in *.
      rewrite nextEntryIsPPgetSndShadow in *. 
  rewrite Hpppart in *.
  case_eq (getConfigTablesLinkedList phyDescChild (memory s));[intros ll Hll| intros Hll] ;
  rewrite Hll in *.
  rewrite NoDupSplitInclIff in Hpart.
  destruct Hpart as (Hpart1 & Hpart2).
  unfold disjoint in *. 
  intros x Hdis1.   
  apply Hpart2 in Hdis1.
  rewrite in_app_iff in Hdis1.
  apply not_or_and in Hdis1.
  
  intuition.
  assert(False).
  apply getConfigTablesRootNotNone with phyDescChild s;trivial.
  intuition.
  assert(False).
  apply sh1PartNotNone with phyDescChild s;trivial.
  intuition.
  assert(Hin1 : In  ptVaChildpd (getIndirections pdChildphy s)). 
  unfold getIndirections.
  assert(Hpdchild1 : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Htblroot in Hpdchild.
  destruct Hpdchild as (nbL & HnbL & stopx & Hstop & Hind).
   apply getIndirectionInGetIndirections with vaChild nbL stopx;trivial.
  assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in Hdefaut.
  unfold not;intros;subst.
  now contradict Hdefaut.
  apply getNbLevelLe in HnbL;trivial.
  assert(Hin2 : In  tbl (getIndirections pd s)). 
  unfold getIndirections.
  apply getIndirectionInGetIndirections with va level stop;trivial.
   assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in H1.
  unfold not;intros;subst.
  now contradict H0.
  symmetry in Hlevel.
  apply getNbLevelLe in Hlevel;trivial.  
  apply sh2PartNotNull with phyDescChild s;trivial.
  unfold not;intros.
  subst.
  unfold disjoint in *.
  unfold not in *.
  apply Hdisjoint with ptVaChildpd;trivial. 



     

     } 
     
     
    assert(Hlevel1 :  level <= CLevel (nbLevel - 1) ).
    apply getNbLevelLe;trivial.
    symmetry;trivial.
    intros Hi.
    rewrite <- Hi. 
    clear Hlevel. 
    (* assert (Hxi : stop1 <= nbLevel - 1) by trivial. *)
    assert(Hrootnotnull: pd <> defaultPage).
    {    destruct Hidxroot as [Hidxroot | Hidxroot];subst.
    apply pdPartNotNull with phyDescChild s;trivial.
    destruct Hidxroot  as [Hidxroot | Hidxroot];subst.
    apply sh1PartNotNull with phyDescChild s;trivial.
    apply sh2PartNotNull with phyDescChild s;trivial. }
    revert H (* Hxi *) Hlevel1 Hlookup Hrootnotnull Hidxroot.
    clear.
    generalize level at 1 2 3 4 5  as l.
    revert pd. 
  induction stop1;simpl; intros;trivial.
  case_eq( StateLib.Level.eqb l fstLevel);intros;trivial.
   assert(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va l)
    (add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va l)
    (memory s)). symmetry.
    apply readPhyEntryMapMMUPage with entry;trivial.
    left.
    generalize (H 0 pd);clear H;intros H. 
    simpl in *. 
    apply H. 
    apply levelEqBEqNatFalse0;trivial. reflexivity.
    apply NPeano.Nat.eqb_neq.
    clear Hidxroot.
    intuition.
    subst.
    apply Hrootnotnull.
    destruct defaultPage;destruct pd.
    simpl in *.
    subst.
    f_equal.
    apply proof_irrelevance.
    rewrite H1.
    case_eq( StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va l)
    (memory s));intros;trivial.
    case_eq(defaultPage =? p);intros;trivial.
    case_eq(StateLib.Level.pred l );intros;trivial.
    apply IHstop1;trivial.
    intros.
    apply H with (S stop).
    simpl.
     apply levelPredMinus1 in H4;trivial.
     rewrite H4 in *.
       unfold CLevel in H5.
   case_eq(lt_dec (l - 1) nbLevel);intros.
   rewrite H8 in *. 
   simpl in *.
   omega.
   destruct l. 
   simpl in *.
   omega.
   simpl.
    rewrite H4.
    rewrite H0.
    rewrite H2.
    rewrite H3.
    trivial.
    trivial.
    move    Hlevel1 at bottom.
    trivial.
    apply levelPredMinus1 in H4;trivial.
    rewrite H4.
    unfold CLevel.
    unfold CLevel in Hlevel1.
   case_eq(lt_dec (l - 1) nbLevel);intros.
   simpl.
   case_eq(lt_dec (nbLevel - 1) nbLevel);intros;
   rewrite H6 in *.
   simpl in *.
   subst.
   omega.
   omega.
   subst.
   destruct l. 
   simpl in *.
   omega.
   apply beq_nat_false in H3. 
   unfold not;intros;subst. now contradict H3. }
+ intros Hi1.
  rewrite  <- Hi1.
  unfold s'.
  apply getIndirectionMapMMUPage11 with entry;trivial.
  intros.
  assert(Hin1 : In tbl (getIndirectionsAux pd s nbLevel)).
  { apply getIndirectionInGetIndirections with va level stop;trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    omega.
    apply beq_nat_false in H0.
    unfold not;intros Hnot;subst.
    now contradict H0.
    symmetry in Hlevel.
    apply getNbLevelEq in Hlevel.
    subst.
    omega.
    destruct Hidxroot as [Hidxroot | Hidxroot];subst.
    apply pdPartNotNull with part s;trivial.
    destruct Hidxroot  as [Hidxroot | Hidxroot];subst.
    apply sh1PartNotNull with part s;trivial.
    apply sh2PartNotNull with part s;trivial. }
  assert(Hin2 : In ptVaChildpd (getIndirectionsAux pdChildphy s nbLevel)).
  { apply getIndirectionInGetIndirections with vaChild level (nbLevel - 1);trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    omega.
    apply beq_nat_false in Hdefaut.
    clear Hidxroot.
    intuition.
    subst.
    now contradict Hdefaut.
    symmetry in Hlevel.
    apply getNbLevelEq in Hlevel.
    subst.
    omega. }
  unfold not;intros.
  subst.
  assert(Hin11 : In ptVaChildpd (getConfigPages phyDescChild s)).
  apply isConfigTable  with vaChild;trivial.
  intros;subst;split;trivial.
  assert(Hconfig : configTablesAreDifferent s) by trivial.
  unfold configTablesAreDifferent in *.
  unfold disjoint in *.
  
  
  contradict Hin11.
  apply Hconfig with part;trivial.
  unfold getConfigPages;simpl;right.
  destruct Hidxroot as [Hidxroot | Hidxroot];subst.
  apply inGetIndirectionsAuxInConfigPagesPD with pd;trivial.
  apply nextEntryIsPPgetPd;trivial.
  destruct Hidxroot as [Hidxroot | Hidxroot];subst.
  apply inGetIndirectionsAuxInConfigPagesSh1 with pd;trivial.
  apply nextEntryIsPPgetFstShadow;trivial.
  apply inGetIndirectionsAuxInConfigPagesSh2 with pd;trivial.
  apply nextEntryIsPPgetSndShadow;trivial.
      destruct Hidxroot as [Hidxroot | Hidxroot];subst.
    apply pdPartNotNull with part s;trivial.
    destruct Hidxroot  as [Hidxroot | Hidxroot];subst.
    apply sh1PartNotNull with part s;trivial.
    apply sh2PartNotNull with part s;trivial. 
   Qed. 
 Lemma mapPageMapSinglePage1 s vax vaChild pdChildphy level
  phyVaChild r w e ptVaChildpd 
  idxvaChild currentPart
 presentvaChild 
phyDescChild entry  : 
  let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 

  StateLib.getNbLevel = Some level -> 
checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false -> 

noDupConfigPagesList s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
In currentPart (getPartitions multiplexer s) ->
In phyVaChild (getAccessibleMappedPages currentPart s) ->
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) ->
negb presentvaChild = true ->
In phyDescChild (getPartitions multiplexer s) ->
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s ->
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s ->
(defaultPage =? ptVaChildpd) = false ->
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild ->
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
pdChildphy <> defaultPage ->
getIndirection pdChildphy vaChild level (nbLevel - 1) s = Some ptVaChildpd ->
getMappedPage pdChildphy s vax =getMappedPage pdChildphy s' vax .
Proof. 
intros s' Hlevel Hvaneg  Hnodupconfig.
intros.

unfold getMappedPage in *.
rewrite Hlevel in *.
case_eq(getIndirection pdChildphy vax level (nbLevel - 1) s');[intros ind Hind | intros Hind].
-  

assert(Hindeq : getIndirection pdChildphy vax level (nbLevel - 1) s = Some ind). 
{ subst.
apply getIndirectionMapMMUPage4
with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
phyVaChild r w e pdChildphy currentPart presentvaChild vaChild
phyDescChild entry PDidx phyDescChild;trivial.
left;trivial. }
rewrite Hindeq.

case_eq(defaultPage =? ind);intros Hdef; 
trivial.
assert(Hor : ptVaChildpd <> ind \/ (StateLib.getIndexOfAddr vaChild fstLevel)
<> (StateLib.getIndexOfAddr vax fstLevel)). 
{ apply pageTablesOrIndicesAreDifferent with pdChildphy pdChildphy level 
nbLevel s;trivial.

 apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
          apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.

left;split;trivial.
apply getNbLevelEq;symmetry;trivial. 
assert (Hdefault : (defaultPage =? ptVaChildpd) = false) by trivial.
apply beq_nat_false in Hdefault.
unfold not;intros;subst.
now contradict Hdefault.
apply beq_nat_false in Hdef.
unfold not;intros;subst.
now contradict Hdef.
(* assert(Hind1 : getIndirection pdChildphy vaChild level (nbLevel - 1) s =
      Some ptVaChildpd) by trivial.
rewrite <- Hind1. *)
apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial. }
assert (Hpres :StateLib.readPresent ind (StateLib.getIndexOfAddr vax fstLevel) (memory s) =
StateLib.readPresent ind (StateLib.getIndexOfAddr vax fstLevel) (memory s')).

{ subst. apply readPresentMapMMUPage with entry;trivial.
intuition. }
rewrite Hpres.
assert (Hphy :StateLib.readPhyEntry ind (StateLib.getIndexOfAddr vax fstLevel) (memory s) =
StateLib.readPhyEntry ind (StateLib.getIndexOfAddr vax fstLevel) (memory s')).

{ subst. apply readPhyEntryMapMMUPage with entry;trivial.
intuition. }
rewrite Hphy;trivial.
- assert(Hnone : getIndirection pdChildphy vax level (nbLevel - 1) s = None).
apply getIndirectionMapMMUPage4None with
   ptVaChildpd idxvaChild
phyVaChild r w e pdChildphy currentPart presentvaChild vaChild
phyDescChild entry PDidx phyDescChild;trivial.
left;trivial.
subst;trivial.
rewrite Hnone;trivial.
Qed.

Lemma getChildrenMapMMUPageEq s ptVaChildpd idxvaChild phyVaChild r w e  pdChildphy currentPart
presentvaChild vaChild phyDescChild level entry:
  wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->   
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
forall part, In part (getPartitions multiplexer s) -> 

getChildren part {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} =
(getChildren part s).
Proof.
intros Hnewcons Hnewcons2 Hpde Hpresdef Hnodupconf Hconfigdiff Hparts Haccess Hlookup Hlevel  Hnotpresent Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild  part Hpart .
unfold getChildren in *.
rewrite Hlevel in *.
simpl. 
set(s' :=  {|
         currentPartition := _ |}) in *.
         unfold wellFormedFstShadowIfDefaultValues in *.
 
assert(Hgetpd : forall partition, StateLib.getPd partition
  (add ptVaChildpd idxvaChild(PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) 
     (memory s) beqPage beqIndex ) = StateLib.getPd partition (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
intros. 
rewrite Hgetpd in *. clear Hgetpd.
case_eq(StateLib.getPd part (memory s) );[intros pd Hpd |intros Hpd];

trivial.
assert(Hpds : getPdsVAddr part level getAllVAddrWithOffset0 s =
getPdsVAddr part level getAllVAddrWithOffset0 s'). 
apply getPdsVAddrMapMMUPage with  pdChildphy
presentvaChild vaChild phyDescChild entry;trivial.
symmetry;trivial.
rewrite <- Hpds in *.
unfold getMappedPagesAux in *.
unfold getMappedPagesOption in *.
assert(Htrue : getMappedPage pdChildphy s vaChild = SomeDefault).
{ apply getMappedPageNotPresent with ptVaChildpd phyDescChild;intuition.
  + subst;trivial.
  + apply negb_true_iff in Hnotpresent.
    subst;trivial. } 
assert(Hpdchildnotnull : pdChildphy <> defaultPage). 
{ 
apply pdPartNotNull with phyDescChild s;trivial.
}        
assert(Hor : part = phyDescChild \/ part <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor]; subst.
+ assert(Hpdeq : pd = pdChildphy). 
  { symmetry. apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
  subst.
  f_equal.
   assert(Hentrysh1 : (exists entry : page,
   nextEntryIsPP phyDescChild sh1idx entry s /\ entry <> defaultPage)). 
 apply Hpde;trivial.
 right;left;trivial.
 destruct Hentrysh1 as (sh1Childphy & Hsh1child & Hsh1notnull).
 assert(Hpdflag : getPDFlag sh1Childphy vaChild s = false). 
 { apply Hnewcons2 with phyDescChild pdChildphy;trivial.
   apply nextEntryIsPPgetFstShadow;trivial. }

  assert(Hx : ~ In vaChild (getPdsVAddr phyDescChild level getAllVAddr s)).
  {  
  apply getPDFlagGetPdsVAddr' with sh1Childphy;trivial.
  apply nextEntryIsPPgetFstShadow;trivial. } 
    assert(forall va, In va (getPdsVAddr phyDescChild level getAllVAddrWithOffset0 s) ->
    checkVAddrsEqualityWOOffset nbLevel va vaChild level = false ).
    { intros.
    assert(Hor :checkVAddrsEqualityWOOffset nbLevel va vaChild level = true \/ 
    checkVAddrsEqualityWOOffset nbLevel va vaChild level = false) .
    { destruct (checkVAddrsEqualityWOOffset nbLevel va vaChild level).
      left;trivial.
      right;trivial. } 
    destruct Hor as [Hor | Hor];trivial.
    assert ( In va (getPdsVAddr phyDescChild level getAllVAddr s)). 
    { unfold getPdsVAddr in *.
       apply filter_In in H as (Hiva & Hiv2).
       apply filter_In.
       split;trivial.
       apply AllVAddrAll.  } 
       assert(Hfalse : In vaChild (getPdsVAddr phyDescChild level getAllVAddr s)). 
       
apply    checkVAddrsEqualityWOOffsetTrue1 with va;trivial.
rewrite <- Hor.
apply checkVAddrsEqualityWOOffsetPermut.
now contradict Hx.

         }
  {  
  clear Hpds.
  induction (getPdsVAddr phyDescChild level getAllVAddrWithOffset0 s).
  simpl;trivial.
  simpl.
  f_equal.
  simpl in *.

assert(checkVAddrsEqualityWOOffset nbLevel a vaChild level = false).
apply H.
left;trivial.
symmetry.
apply mapPageMapSinglePage1 with level (StateLib.getIndexOfAddr vaChild fstLevel)
currentPart presentvaChild phyDescChild entry;trivial.
rewrite <-H0;apply checkVAddrsEqualityWOOffsetPermut.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
intros;subst;split;trivial.

  apply IHl.
  intuition.
   }
  
+  
  
   clear Hpds.
assert(Hmapped : getMappedPages part s = getMappedPages part s').
{
  apply getMappedPagesMapMMUPage with phyDescChild vaChild
entry level;trivial. 
* apply isConfigTable with vaChild;trivial.
  intros;subst;split;trivial.
  * apply Hconfigdiff;trivial. intuition.
  * symmetry;trivial.
  * intros;subst;split;trivial.
  * intuition.
  
}

assert(forall va, getMappedPage pd s' va = getMappedPage pd s va).
intros.
symmetry.
apply getMappedPageMapMMUPageEq with part phyDescChild
vaChild entry level;trivial.

assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
apply isConfigTable  with vaChild;trivial.

intros; split; 
subst;trivial. trivial.
apply Hconfigdiff;trivial.
intuition.
symmetry;trivial.
intros;subst;split;trivial.
intuition.
induction (getPdsVAddr part level getAllVAddrWithOffset0 s);simpl;trivial.
rewrite H. 
case_eq(getMappedPage pd s a);intros;trivial.
f_equal;trivial.
Qed.



Lemma getPartitionsMapMMUPageEq s entry (vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD 
ptVaChildpd :page) idxvaChild phyVaChild pdChildphy r w e
phyDescChild  vaChild presentvaChild level :
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
noDupPartitionTree s -> 
partitionDescriptorEntry s -> 
isPresentNotDefaultIff s -> 
noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) ->
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
 nextEntryIsPP (currentPartition s) PDidx currentPD s  -> 

getPartitions multiplexer s = getPartitions multiplexer {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hlookup Hnewcons Hnewcons2 Hnoduptree Hi1 Hi2 Hi3 Hi4 Hlevel Hnotpresent
 Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent Hpdchild Hcurpart
 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Hcurrpd.
set(s' :=  {|
         currentPartition := _ |}) in *.
unfold getPartitions. 
assert(Hmult: In multiplexer (getPartitions multiplexer s)).
{ unfold getPartitions.
  destruct (nbPage);simpl; left;trivial. }
revert Hmult.
generalize multiplexer at 1 3 4.
induction (nbPage + 1);trivial;simpl.
intros part Hpart.
f_equal.

assert(Hchild :getChildren part s' = getChildren part s).
{ apply getChildrenMapMMUPageEq with pdChildphy  (currentPartition s)
presentvaChild vaChild phyDescChild level entry;trivial.
assert(getAccessibleMappedPage currentPD s vaInCurrentPartition =SomePage phyVaChild). 
apply isAccessibleMappedPage2 with (currentPartition s) ptVaInCurPartpd;
trivial.
unfold getAccessibleMappedPages.
rewrite nextEntryIsPPgetPd in *. rewrite Hcurrpd. 
unfold getAccessibleMappedPagesAux. 
apply filterOptionInIff.
unfold getAccessibleMappedPagesOption.
apply in_map_iff.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaInCurrentPartition va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1.
split;trivial.
rewrite <- H.
symmetry.
apply getAccessibleMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption. }
  rewrite Hchild.
  clear Hchild.
  assert(forall child, In child (getChildren part s) -> In child (getPartitions multiplexer s)).
  { intros.  apply childrenPartitionInPartitionList with part;trivial. } 
  induction  (getChildren part s);simpl;trivial.
  f_equal.
  apply IHn.
  apply H.
  simpl;left;trivial.
apply IHl;trivial.
intros;apply H.
simpl;right;trivial.
Qed. 

Lemma getPartitionsMapMMUPage s entry (vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD 
ptVaChildpd :page) idxvaChild phyVaChild pdChildphy r w e
phyDescChild  vaChild presentvaChild level :
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
noDupPartitionTree s -> 
partitionDescriptorEntry s -> 
isPresentNotDefaultIff s -> 
noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) ->
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
 nextEntryIsPP (currentPartition s) PDidx currentPD s  -> 
forall part, 
In part (getPartitions multiplexer {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}) -> 
In part (getPartitions multiplexer s).
Proof.
intros Hlookup Hnewcons2 Hnewcons Hnoduptree Hi1 Hi2 Hi3 Hi4 Hlevel Hnotpresent
 Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent Hpdchild Hcurpart
 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Hcurrpd.
set(s' :=  {|
         currentPartition := _ |}) in *.
unfold getPartitions. 
assert(Hmult: In multiplexer (getPartitions multiplexer s)).
{ unfold getPartitions.
  destruct (nbPage);simpl; left;trivial. }
revert Hmult.
generalize multiplexer at 1 3 4.
induction (nbPage + 1);trivial;simpl.
intros mult Hmult part Hpart.
destruct Hpart as [Hpart | Hpart].
left;trivial.
right.
rewrite in_flat_map in *.
destruct Hpart as(child & Hchild1 & Hpart).
exists child.
assert(Hchild : In child (getChildren mult s)).
{ apply getChildrenMapMMUPage with ptVaChildpd idxvaChild
phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild phyDescChild
level entry;trivial.
assert(getAccessibleMappedPage currentPD s vaInCurrentPartition =SomePage phyVaChild). 
apply isAccessibleMappedPage2 with (currentPartition s) ptVaInCurPartpd;
trivial.
unfold getAccessibleMappedPages.
rewrite nextEntryIsPPgetPd in *. rewrite Hcurrpd. 
unfold getAccessibleMappedPagesAux. 
apply filterOptionInIff.
unfold getAccessibleMappedPagesOption.
apply in_map_iff.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaInCurrentPartition va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1.
split;trivial.
rewrite <- H.
symmetry.
apply getAccessibleMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption. }
split;trivial. 
apply IHn;trivial.
apply childrenPartitionInPartitionList with mult;trivial.
Qed. 
Lemma getIndirectionsMapMMUPage1 s phyVaChild ptVaChildpd idxvaChild r w e entry: 
forall root : page,
~ In ptVaChildpd (getIndirections root s) ->
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) ->
getIndirections root s = getIndirections root {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
 Proof. 
 set(s' := {|
  currentPartition := _ |}) in *.
 unfold getIndirections.
 induction nbLevel;simpl;trivial.
 intros root Hi Hlookup.
 f_equal.
 apply not_or_and in Hi.
 destruct Hi as (Hi1 & Hi2).
 rewrite in_flat_map in Hi2.
 assert(Hii: getTablePages root tableSize s = getTablePages root tableSize s').
 revert Hi2 Hi1 Hlookup. 
 clear.
 induction  tableSize.
 simpl;trivial.
 simpl in *. 
 intros.
 assert(Hpairs : beqPairs (ptVaChildpd, idxvaChild) (root, CIndex n0) beqPage beqIndex = true \/
 beqPairs (ptVaChildpd, idxvaChild) (root, CIndex n0) beqPage beqIndex = false).
 { destruct (beqPairs (ptVaChildpd, idxvaChild) (root, CIndex n0) beqPage beqIndex).
   left;trivial.
   right;trivial. } 
 destruct Hpairs as [Hpairs | Hpairs].
 { apply beqPairsTrue in Hpairs.
   destruct Hpairs;subst.
   now contradict Hi1. }
  rewrite Hpairs.
  assert(Hmm : lookup root (CIndex n0) (memory s) beqPage beqIndex =
   lookup root (CIndex n0)
    (removeDup ptVaChildpd idxvaChild (memory s) beqPage beqIndex) beqPage
    beqIndex).
    symmetry. 
    apply removeDupIdentity.
    apply beqPairsFalse in Hpairs.
     intuition.
     rewrite <- Hmm. 
 case_eq(lookup root (CIndex n0) (memory s) beqPage beqIndex );[intros 
 v Hlookup1 | intros Hlookup1];rewrite Hlookup1 in *.
 clear Hmm.
 case_eq v ;intros;subst; try apply IHn0;trivial.
 case_eq(pa p =? defaultPage);intros Hdeff ; rewrite Hdeff in *;
 try apply IHn0;trivial.
 f_equal.
  try apply IHn0;trivial.
  unfold not;intros Hfalse.
  contradict Hi2.
  destruct Hfalse as (x & Hx & Hxx).
  exists x.
  split;trivial.
 apply in_app_iff.
 left;trivial.
 try apply IHn0;trivial.
 rewrite <- Hii. clear Hii.
 induction  (getTablePages root tableSize s);simpl;trivial.
 f_equal.
 apply IHn;trivial.
 unfold not;intros.
 contradict Hi2.
 exists a;simpl.
 split;trivial.
 left;trivial.
 apply IHl.
 unfold
  not;intros.
  contradict Hi2.
  destruct H as (x & Hx & Hxx).
  exists x;simpl.
  split;trivial.
  right;trivial.
  Qed.
Lemma getLLPagesMapMMUPage s phyVaChild ptVaChildpd idxvaChild r w e entry: 
forall root : page,
~ In ptVaChildpd (getLLPages root s (nbPage + 1) ) ->
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) ->
getLLPages root s (nbPage + 1)  = getLLPages root  {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}(nbPage + 1) .
 Proof. 
 set(s' := {|
  currentPartition := _ |}) in *.
 induction (nbPage + 1);simpl;trivial.
 intros. 
 destruct (StateLib.getMaxIndex);intros;trivial.
 assert(Hpp : StateLib.readPhysical root i (memory s)  =
   StateLib.readPhysical root i
    (add ptVaChildpd idxvaChild
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex)).
          symmetry. 
 apply readPhysicalMapMMUPage with entry ;trivial.
 rewrite <- Hpp in *. clear Hpp.
 case_eq(StateLib.readPhysical root i (memory s));intros;trivial.
 rewrite H1 in *.
 case_eq(p =? defaultPage );intros;trivial.
 f_equal.
 rewrite H2 in *.
 simpl in *. 
 apply not_or_and in H. 
 destruct H.
  
 apply IHn;trivial.
 Qed.
 

 Lemma getTablePagesMapMMUPage root n ptVaChildpd s idxvaChild r w e phyVaChild :
 ~
(exists x : page,
   In x (getTablePages root tableSize s) /\
   In ptVaChildpd (getIndirectionsAux x s n)) ->
root <> ptVaChildpd ->

getTablePages root tableSize s = getTablePages root tableSize {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
{
 induction  tableSize.
 simpl;trivial.
 simpl in *. 
 intros.
 assert(Hpairs : beqPairs (ptVaChildpd, idxvaChild) (root, CIndex n0) beqPage beqIndex = true \/
 beqPairs (ptVaChildpd, idxvaChild) (root, CIndex n0) beqPage beqIndex = false).
 { destruct (beqPairs (ptVaChildpd, idxvaChild) (root, CIndex n0) beqPage beqIndex).
   left;trivial.
   right;trivial. } 
 destruct Hpairs as [Hpairs | Hpairs].
 { apply beqPairsTrue in Hpairs.
   destruct Hpairs;subst.
   now contradict H0. }
  rewrite Hpairs.
  assert(Hmm : lookup root (CIndex n0) (memory s) beqPage beqIndex =
   lookup root (CIndex n0)
    (removeDup ptVaChildpd idxvaChild (memory s) beqPage beqIndex) beqPage
    beqIndex).
    symmetry. 
    apply removeDupIdentity.
    apply beqPairsFalse in Hpairs.
     intuition.
     rewrite <- Hmm. 
 case_eq(lookup root (CIndex n0) (memory s) beqPage beqIndex );[intros 
 v Hlookup1 | intros Hlookup1];rewrite Hlookup1 in *.
 clear Hmm.
 case_eq v ;intros;subst; try apply IHn0;trivial.
 case_eq(pa p =? defaultPage);intros Hdeff ; rewrite Hdeff in *;
 try apply IHn0;trivial.
 f_equal.
  try apply IHn0;trivial.
  unfold not;intros Hfalse.
  contradict H.
  destruct Hfalse as (x & Hx & Hxx).
  exists x.
  split;trivial.
 apply in_app_iff.
 left;trivial.
 try apply IHn0;trivial. }
 Qed.
Lemma getConfigPagesMapMMUPage s part ptVaChildpd idxvaChild
  r w  e phyVaChild phyDescChild entry:
  let s' := {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd idxvaChild
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
In ptVaChildpd (getConfigPages phyDescChild s) -> 
disjoint (getConfigPages phyDescChild s) (getConfigPages part s) -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
     Some (PE entry) -> 
  phyDescChild <> part -> 
In part (getPartitions multiplexer s)-> 
getConfigPages part s =
getConfigPages part
  s'.
Proof.
intros s' Hconfigpt Hmykey2 Hlookup.
intros.
unfold getConfigPages in *.
unfold disjoint in *.
f_equal.
assert(Hdiffparts: phyDescChild <> part) by trivial.
revert Hmykey2 Hdiffparts Hconfigpt.
revert Hlookup.
clear.
intros. 
apply Hmykey2 in Hconfigpt.
clear Hmykey2 Hdiffparts.
simpl in *. 
apply not_or_and in Hconfigpt.
destruct Hconfigpt as (_ & Hconfigpt).
unfold getConfigPagesAux in *.
assert(Hgetpd : forall partition, StateLib.getPd partition
  (add ptVaChildpd idxvaChild(PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) 
     (memory s) beqPage beqIndex ) = StateLib.getPd partition (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
intros. 
rewrite Hgetpd in *. clear Hgetpd.
case_eq(StateLib.getPd part (memory s) );[intros pd Hpd |intros Hpd];
rewrite Hpd in *;
trivial.
    assert(Hgetfst : forall partition, StateLib.getFstShadow partition
  (add ptVaChildpd idxvaChild(PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) 
     (memory s) beqPage beqIndex ) = StateLib.getFstShadow partition (memory s)).
{ intros. apply getFstShadowMapMMUPage with entry;trivial. }
intros. 
rewrite Hgetfst in *. clear Hgetfst.
case_eq(StateLib.getFstShadow part (memory s) );[intros sh1 Hsh1 |intros Hsh1];
rewrite Hsh1 in *;trivial.
    assert(Hgetsnd : forall partition, StateLib.getSndShadow partition
  (add ptVaChildpd idxvaChild(PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) 
     (memory s) beqPage beqIndex ) = StateLib.getSndShadow partition (memory s)).
{ intros. apply getSndShadowMapMMUPage with entry;trivial. }
intros. 
rewrite Hgetsnd in *. clear Hgetsnd.
case_eq(StateLib.getSndShadow part (memory s) );[intros sh2 Hsh2 |intros Hsh2];
rewrite Hsh2 in *;trivial.
    assert(Hgetsnd : forall partition, getConfigTablesLinkedList partition
  (add ptVaChildpd idxvaChild(PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) 
     (memory s) beqPage beqIndex ) = getConfigTablesLinkedList partition (memory s)).
{ intros. apply getConfigTablesLinkedListMapMMUPage with entry;trivial. }
intros. 
rewrite Hgetsnd in *. clear Hgetsnd.
case_eq(getConfigTablesLinkedList part (memory s) );[intros ll Hll |intros Hll];
rewrite Hll in *;trivial.
assert(forall root, root= pd \/ root = sh1 \/ root = sh2 -> 
~ In ptVaChildpd (getIndirections root s) ->
getIndirections root s = getIndirections root s').
intros root Ht Hi. 
clear Ht.
revert Hi Hlookup. clear.
revert root. 
intros.
apply getIndirectionsMapMMUPage1 with entry;trivial.
rewrite in_app_iff in Hconfigpt.
apply not_or_and in Hconfigpt.
destruct Hconfigpt.
rewrite in_app_iff in H1.
apply not_or_and in H1.
destruct H1.
rewrite in_app_iff in H2.
apply not_or_and in H2.
destruct H2.
do 3 try rewrite <- H;trivial.
do 3 f_equal.
revert H3 Hlookup.
clear.
intros. 
apply getLLPagesMapMMUPage with entry;trivial.
do 2 right;trivial.
right;left;trivial.
left;trivial. 
Qed.

 Lemma getIndirectionMapMMUPage5 s ptVaChildpd idxvaChild phyVaChild r w e  
  pdChildphy currentPart va p
presentvaChild vaChild phyDescChild level entry stop1 idxroot:
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
pdChildphy <> defaultPage -> 

getIndirection pdChildphy vaChild level (nbLevel - 1) s =
            Some ptVaChildpd -> 
forall part pd, nextEntryIsPP part idxroot pd s -> (idxroot = PDidx \/
idxroot =sh1idx \/ idxroot = sh2idx) ->   In part (getPartitions multiplexer s) -> 
           (*  stop1 <= (nbLevel -1) ->  *)
   getIndirection pd va level stop1 s = Some p -> 
getIndirection pd va level stop1 s'= Some p.
Proof.
intros s' Hpde Hpresdef Hnodup2 Hconfigdiff Hparts Haccess Hlookup Hlevel 
 Hnotpresent Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild Hpdchildnotnull Hindchild part pd Hpppart Hidxroot Hpart (* H *).
assert(Hor : part= phyDescChild \/ part <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
+ subst.

(*   . *)
{ assert(forall stop tbl,
    stop < level  -> 
    getIndirection pd va level stop s = Some tbl -> 
    (defaultPage =? tbl) = false ->
      tbl <> ptVaChildpd ). 
    {  destruct Hidxroot as [Hidxroot | Hidxroot].
 * subst.
 assert(pd = pdChildphy).
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  apply nextEntryIsPPgetPd;trivial.
  subst.
 assert(Hnodup : NoDup (getIndirections pdChildphy s)).
      {  apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
          }
      intros. 
      
      
      
      assert(~In ptVaChildpd (getIndirectionsAux pdChildphy s (stop+1))). 
      { assert(~In ptVaChildpd (getIndirectionsAux pdChildphy s (nbLevel-1))). 
    {  assert(0<nbLevel) by apply nbLevelNotZero.
      assert(nbLevel - 1 + 1 = nbLevel) by omega.
    
 
 assert(Hprevious : exists prevtab,
      getIndirection pdChildphy vaChild level (nbLevel - 2) s =
            Some prevtab /\prevtab <> defaultPage /\  StateLib.readPhyEntry prevtab
  (StateLib.getIndexOfAddr vaChild (CLevel (level- ((nbLevel - 1) - 1)))) (memory s) =
Some ptVaChildpd). 
{   revert Hindchild   Hdefaut  (*  H0 *).


  assert(Hstooo : level > (nbLevel - 1 -1)).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    unfold CLevel in H.
    rewrite H4 in *.
    simpl in *.
    
    omega.
    omega. } 

  
  assert(Htpp : 0 < nbLevel -1).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    unfold CLevel in H.
    rewrite H4 in *.
    simpl in *.
    
    omega.
    omega.
    
     } 
  assert(Hnotdef : pdChildphy <> defaultPage) by intuition. 
  revert Hstooo Htpp Hnotdef.
  clear. 
  replace (nbLevel -2) with (nbLevel -1 -1) by omega.  
  revert pdChildphy level ptVaChildpd.
  induction (nbLevel-1);simpl.
  intros.
  omega.
  intros. 
  case_eq(StateLib.Level.eqb level fstLevel);intros;
  rewrite H in *.
  apply levelEqBEqNatTrue0 in H. 
  omega.
   case_eq(StateLib.readPhyEntry pdChildphy
                (StateLib.getIndexOfAddr vaChild level) (memory s));intros;
    rewrite H0 in *;try now contradict Hindchild.
    case_eq(defaultPage =? p);intros;rewrite H1 in *.
    apply beq_nat_false in Hdefaut.
    inversion Hindchild.
    subst.
    now contradict Hdefaut.
    case_eq(StateLib.Level.pred level );intros;rewrite H2 in *.
    + replace (n-0) with n by omega.
    assert(Hooo : n = 0 \/ 0 < n) by omega.
    destruct Hooo.
    *
    subst. 
    simpl in *. 
    exists  pdChildphy;split;trivial.
    inversion Hindchild. 
    subst. 
    rewrite <- H0.
    split.  trivial. 
    f_equal.
    f_equal.
    rewrite <- minus_n_O.
    apply CLevelIdentity1.
    * assert(Hii : l > n - 1  ) .
    apply levelPredMinus1 in H2.
    subst.
   unfold CLevel.
    case_eq( lt_dec (level - 1) nbLevel );intros.
    simpl.
    omega.
    destruct level.
    simpl in *.
    omega.
    trivial.
    assert(Hi1 : p <> defaultPage).
    apply beq_nat_false in H1.
    intuition.
    subst.
    now contradict H1. 
      generalize(IHn p l ptVaChildpd Hii H3 Hi1 Hindchild Hdefaut
       );clear IHn ; intros iHn .
       destruct iHn as (prevtab & Hindprev & Hdef & Hread).
       exists prevtab;split;trivial.
       intros.
       assert(Hs :S(n-1) = n) by omega.
       rewrite <- Hs.
       simpl.
       rewrite H.
       rewrite H0. 
       rewrite H1.
       rewrite H2;trivial.
       split;trivial.
       rewrite <- Hread.
       f_equal.
       f_equal.
       f_equal.
apply levelPredMinus1 in H2.
rewrite H2.
unfold CLevel.
case_eq(lt_dec (level - 1) nbLevel);intros. 
simpl. 
omega.
destruct level. 
simpl in *.
omega.
trivial.
+ assert(Hnotnone : StateLib.Level.pred level <> None).
apply levelPredNone;trivial. now contradict Hnotnone.  }
destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev). 
       apply getIndirectionInGetIndirections2 with prevtab vaChild level;
      simpl; subst;
      trivial.
      omega.
      simpl.
      rewrite <- Hprevtable.
      f_equal.
      omega.
      rewrite H3. 
      unfold getIndirections in *;trivial.

(*       symmetry in Hlevel.
      apply getNbLevelEq in Hlevel.
      rewrite Hlevel in *.
      unfold CLevel in H0. 
      assert (0<nbLevel) by apply nbLevelNotZero.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros;
      rewrite H6 in *.
      simpl in *.
      omega.
      omega.
      omega. *)
      apply beq_nat_false in Hdefaut.
      unfold not;intros;subst.
      now contradict Hdefaut. 
      move Hlevel at bottom.
      symmetry in Hlevel.

      apply getNbLevelEq in Hlevel.
      rewrite Hlevel.
      unfold CLevel. 
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros. 
      simpl. 
      omega.
      omega.
      }
      unfold not;intros. contradict H2.
      assert(Hincl : incl (getIndirectionsAux pdChildphy s (stop + 1))
      (getIndirectionsAux pdChildphy s (nbLevel - 1))).
      apply inclGetIndirectionsAuxLe;trivial.
      symmetry in Hlevel.
      apply getNbLevelEq in Hlevel.
      subst.
      unfold CLevel in H.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      rewrite H2 in *. 
      simpl in *. omega.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      unfold incl in *. 
      apply Hincl;trivial.
      }
     
      assert(In tbl (getIndirectionsAux pdChildphy s (stop+1))). 
      { apply getIndirectionInGetIndirections1 with va level;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      assert(level < nbLevel).
      apply getNbLevelLt;trivial.      
      omega.
      apply beq_nat_false in H1.
      unfold not;intros;subst.
       
      now contradict H1.  }
      unfold not;intros.
      subst.
      now contradict H3.
   *  unfold noDupConfigPagesList in *. intros.
      
 destruct Hidxroot; subst.
- intros. 
  assert(Hdisjoint: disjoint (getIndirections pdChildphy s) (getIndirections pd s)). 
  apply Hnodup2 in Hpart.
  unfold getConfigPages in *.
  apply NoDup_cons_iff in Hpart as(_ & Hpart).
  clear Hnodup2.
  unfold getConfigPagesAux in Hpart.
  rewrite nextEntryIsPPgetPd in *. 
  rewrite Hpdchild in Hpart.
    rewrite nextEntryIsPPgetFstShadow in *. 
  rewrite Hpppart in *.
  case_eq (getSndShadow phyDescChild (memory s));[intros sh2 Hsh2 | intros Hsh2] ;
  rewrite Hsh2 in *.
  case_eq (getConfigTablesLinkedList phyDescChild (memory s));[intros ll Hll| intros Hll] ;
  rewrite Hll in *.
  rewrite NoDupSplitInclIff in Hpart.
  destruct Hpart as (Hpart1 & Hpart2).
  unfold disjoint in *. 
  intros x Hdis1.   
  apply Hpart2 in Hdis1.
  intuition.
  assert(False).
  apply getConfigTablesRootNotNone with phyDescChild s;trivial.
  intuition.
  assert(False).
  apply sh2PartNotNone with phyDescChild s;trivial.
  intuition.
  assert(Hin1 : In  ptVaChildpd (getIndirections pdChildphy s)). 
  unfold getIndirections.
  assert(Hpdchild1 : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Htblroot in Hpdchild.
  destruct Hpdchild as (nbL & HnbL & stopx & Hstop & Hind).
   apply getIndirectionInGetIndirections with vaChild nbL stopx;trivial.
  assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in Hdefaut.
  unfold not;intros;subst.
  now contradict Hdefaut.
  apply getNbLevelLe in HnbL;trivial.
  assert(Hin2 : In  tbl (getIndirections pd s)). 
  unfold getIndirections.
  apply getIndirectionInGetIndirections with va level stop;trivial.
   assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in H1.
  unfold not;intros;subst.
  now contradict H0.
  symmetry in Hlevel.
  apply getNbLevelLe in Hlevel;trivial.  
  apply sh1PartNotNull with phyDescChild s;trivial.
  unfold not;intros.
  subst.
  unfold disjoint in *.
  unfold not in *.
  apply Hdisjoint with ptVaChildpd;trivial.

- intros. 
  assert(Hdisjoint: disjoint (getIndirections pdChildphy s) (getIndirections pd s)). 
  apply Hnodup2 in Hpart.
  unfold getConfigPages in *.
  apply NoDup_cons_iff in Hpart as(_ & Hpart).
  clear Hnodup2.
  unfold getConfigPagesAux in Hpart.
  rewrite nextEntryIsPPgetPd in *. 
  rewrite Hpdchild in Hpart.
  case_eq (getFstShadow phyDescChild (memory s));[intros sh1 Hsh1 | intros Hsh1] ;
  rewrite Hsh1 in *.
      rewrite nextEntryIsPPgetSndShadow in *. 
  rewrite Hpppart in *.
  case_eq (getConfigTablesLinkedList phyDescChild (memory s));[intros ll Hll| intros Hll] ;
  rewrite Hll in *.
  rewrite NoDupSplitInclIff in Hpart.
  destruct Hpart as (Hpart1 & Hpart2).
  unfold disjoint in *. 
  intros x Hdis1.   
  apply Hpart2 in Hdis1.
  rewrite in_app_iff in Hdis1.
  apply not_or_and in Hdis1.
  
  intuition.
  assert(False).
  apply getConfigTablesRootNotNone with phyDescChild s;trivial.
  intuition.
  assert(False).
  apply sh1PartNotNone with phyDescChild s;trivial.
  intuition.
  assert(Hin1 : In  ptVaChildpd (getIndirections pdChildphy s)). 
  unfold getIndirections.
  assert(Hpdchild1 : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Htblroot in Hpdchild.
  destruct Hpdchild as (nbL & HnbL & stopx & Hstop & Hind).
   apply getIndirectionInGetIndirections with vaChild nbL stopx;trivial.
  assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in Hdefaut.
  unfold not;intros;subst.
  now contradict Hdefaut.
  apply getNbLevelLe in HnbL;trivial.
  assert(Hin2 : In  tbl (getIndirections pd s)). 
  unfold getIndirections.
  apply getIndirectionInGetIndirections with va level stop;trivial.
   assert(0<nbLevel) by apply nbLevelNotZero.
  omega.
  apply beq_nat_false in H1.
  unfold not;intros;subst.
  now contradict H0.
  symmetry in Hlevel.
  apply getNbLevelLe in Hlevel;trivial.  
  apply sh2PartNotNull with phyDescChild s;trivial.
  unfold not;intros.
  subst.
  unfold disjoint in *.
  unfold not in *.
  apply Hdisjoint with ptVaChildpd;trivial. 



     

     } 
     
     
    assert(Hlevel1 :  level <= CLevel (nbLevel - 1) ).
    apply getNbLevelLe;trivial.
    symmetry;trivial.
    intros Hi.
    rewrite <- Hi. 
    clear Hlevel. 
    (* assert (Hxi : stop1 <= nbLevel - 1) by trivial. *)
    assert(Hrootnotnull: pd <> defaultPage).
    {    destruct Hidxroot as [Hidxroot | Hidxroot];subst.
    apply pdPartNotNull with phyDescChild s;trivial.
    destruct Hidxroot  as [Hidxroot | Hidxroot];subst.
    apply sh1PartNotNull with phyDescChild s;trivial.
    apply sh2PartNotNull with phyDescChild s;trivial. }
    revert H (* Hxi *) Hlevel1 Hlookup Hrootnotnull Hidxroot.
    clear.
    generalize level at 1 2 3 4 5  as l.
    revert pd. 
  induction stop1;simpl; intros;trivial.
  case_eq( StateLib.Level.eqb l fstLevel);intros;trivial.
   assert(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va l)
    (add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va l)
    (memory s)). symmetry.
    apply readPhyEntryMapMMUPage with entry;trivial.
    left.
    generalize (H 0 pd);clear H;intros H. 
    simpl in *. 
    apply H. 
    apply levelEqBEqNatFalse0;trivial. reflexivity.
    apply NPeano.Nat.eqb_neq.
    clear Hidxroot.
    intuition.
    subst.
    apply Hrootnotnull.
    destruct defaultPage;destruct pd.
    simpl in *.
    subst.
    f_equal.
    apply proof_irrelevance.
    rewrite H1.
    case_eq( StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va l)
    (memory s));intros;trivial.
    case_eq(defaultPage =? p);intros;trivial.
    case_eq(StateLib.Level.pred l );intros;trivial.
    apply IHstop1;trivial.
    intros.
    apply H with (S stop).
    simpl.
     apply levelPredMinus1 in H4;trivial.
     rewrite H4 in *.
       unfold CLevel in H5.
   case_eq(lt_dec (l - 1) nbLevel);intros.
   rewrite H8 in *. 
   simpl in *.
   omega.
   destruct l. 
   simpl in *.
   omega.
   simpl.
    rewrite H4.
    rewrite H0.
    rewrite H2.
    rewrite H3.
    trivial.
    trivial.
    move    Hlevel1 at bottom.
    trivial.
    apply levelPredMinus1 in H4;trivial.
    rewrite H4.
    unfold CLevel.
    unfold CLevel in Hlevel1.
   case_eq(lt_dec (l - 1) nbLevel);intros.
   simpl.
   case_eq(lt_dec (nbLevel - 1) nbLevel);intros;
   rewrite H6 in *.
   simpl in *.
   subst.
   omega.
   omega.
   subst.
   destruct l. 
   simpl in *.
   omega.
   apply beq_nat_false in H3. 
   unfold not;intros;subst. now contradict H3. }
+ intros Hi1.
  rewrite  <- Hi1.
  unfold s'. symmetry.
  apply getIndirectionMapMMUPage11 with entry;trivial.
  intros.
  assert(Hin1 : In tbl (getIndirectionsAux pd s nbLevel)).
  { apply getIndirectionInGetIndirections with va level stop;trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    omega.
    apply beq_nat_false in H0.
    unfold not;intros Hnot;subst.
    now contradict H0.
    symmetry in Hlevel.
    apply getNbLevelEq in Hlevel.
    subst.
    omega.
    destruct Hidxroot as [Hidxroot | Hidxroot];subst.
    apply pdPartNotNull with part s;trivial.
    destruct Hidxroot  as [Hidxroot | Hidxroot];subst.
    apply sh1PartNotNull with part s;trivial.
    apply sh2PartNotNull with part s;trivial. }
  assert(Hin2 : In ptVaChildpd (getIndirectionsAux pdChildphy s nbLevel)).
  { apply getIndirectionInGetIndirections with vaChild level (nbLevel - 1);trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    omega.
    apply beq_nat_false in Hdefaut.
    clear Hidxroot.
    intuition.
    subst.
    now contradict Hdefaut.
    symmetry in Hlevel.
    apply getNbLevelEq in Hlevel.
    subst.
    omega. }
  unfold not;intros.
  subst.
  assert(Hin11 : In ptVaChildpd (getConfigPages phyDescChild s)).
  apply isConfigTable  with vaChild;trivial.
  intros;subst;split;trivial.
  assert(Hconfig : configTablesAreDifferent s) by trivial.
  unfold configTablesAreDifferent in *.
  unfold disjoint in *.
  
  
  contradict Hin11.
  apply Hconfig with part;trivial.
  unfold getConfigPages;simpl;right.
  destruct Hidxroot as [Hidxroot | Hidxroot];subst.
  apply inGetIndirectionsAuxInConfigPagesPD with pd;trivial.
  apply nextEntryIsPPgetPd;trivial.
  destruct Hidxroot as [Hidxroot | Hidxroot];subst.
  apply inGetIndirectionsAuxInConfigPagesSh1 with pd;trivial.
  apply nextEntryIsPPgetFstShadow;trivial.
  apply inGetIndirectionsAuxInConfigPagesSh2 with pd;trivial.
  apply nextEntryIsPPgetSndShadow;trivial.
      destruct Hidxroot as [Hidxroot | Hidxroot];subst.
    apply pdPartNotNull with part s;trivial.
    destruct Hidxroot  as [Hidxroot | Hidxroot];subst.
    apply sh1PartNotNull with part s;trivial.
    apply sh2PartNotNull with part s;trivial. 
Qed.



Lemma getAccessibleMappedPageMapMMUPage1 s ptVaChildpd idxvaChild phyVaChild e
 r w part phyDescChild vaChild entry level a pd: 
 let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
partitionDescriptorEntry s->
disjoint (getConfigPages phyDescChild s) (getConfigPages part s) -> 
In ptVaChildpd (getConfigPages phyDescChild s) ->
disjoint (getConfigPages phyDescChild s) (getConfigPages part s) -> 
 lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
    Some (PE entry) ->
 Some level = StateLib.getNbLevel->
 configTablesAreDifferent s->

In phyDescChild (getPartitions multiplexer s)->
(forall idx : index,
     StateLib.getIndexOfAddr vaChild fstLevel = idx ->
     isPE ptVaChildpd idx s /\
     getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s)->
 (defaultPage =? ptVaChildpd) = false->

 phyDescChild <> part -> 
 In part (getPartitions multiplexer s)      ->    
  StateLib.getPd part (memory s) = Some pd ->            
 getAccessibleMappedPage pd s a = getAccessibleMappedPage pd s' a. 
Proof.
intros s' Hpde Hmykey2.
intros.
  unfold getAccessibleMappedPage.
  assert(Hlevel : Some level = StateLib.getNbLevel) by trivial.
  rewrite <- Hlevel.
  unfold configTablesAreDifferent in *.
  assert(Hconfigpart : forall ind stop,  
  getIndirection pd a level stop s = Some ind ->
  ind <> defaultPage -> 
  In ind (getIndirectionsAux pd s (nbLevel))).
  { intros.
    apply getIndirectionInGetIndirections with a level stop;trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    omega.
    apply getNbLevelEq in Hlevel.
    subst.
    omega.  
  unfold partitionDescriptorEntry in *.

  assert(Hexist : (exists entry : page,
          nextEntryIsPP part PDidx entry s /\ entry <> defaultPage)).
  
        apply Hpde;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pd).
apply getPdNextEntryIsPPEq  with part s;trivial.
subst;trivial. }
assert(Hconfig : forall ind, In ind (getIndirectionsAux pd s nbLevel) -> 
In ind (getConfigPages part s)).
{
intros.
unfold getConfigPages.
simpl. right.   
apply inGetIndirectionsAuxInConfigPagesPD with pd;trivial. }
assert(Hi : forall ind stop,  
  getIndirection pd a level stop s = Some ind ->
  ind <> defaultPage -> In ind (getConfigPages part s)). 
  { intros. apply Hconfig.
    apply Hconfigpart with stop;trivial. }
assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
apply isConfigTable  with vaChild;trivial.
intros. (* split. 
subst;trivial.
subst;trivial. *)
assert(Hmykey : forall stop tbl,
    getIndirection pd a level stop s = Some tbl -> 
    (defaultPage =? tbl) = false ->
      tbl <> ptVaChildpd ).
{ intros. 
  unfold not;intros.
  subst.
  unfold disjoint in *.
  unfold not in Hmykey2.
  apply Hmykey2 with ptVaChildpd;trivial.
  apply Hi with stop;trivial.
  assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial. 
  apply beq_nat_false in Hdefaut.
  intuition.
  subst.
  now contradict Hdefaut. }
assert(Hmykey3 : getIndirection pd a level (nbLevel - 1) s = 
getIndirection pd a level (nbLevel - 1) s').
{ 
   assert(Hpdnotnull : pd <> defaultPage). 
{ unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP part PDidx entry s /\ entry <> defaultPage)).
        apply Hpde;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pd).
apply getPdNextEntryIsPPEq  with part s;trivial.
subst;trivial. }
assert(Hlookup :lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
     Some (PE entry)) by trivial.
revert Hmykey Hlookup Hpdnotnull.
   clear.
     intros. 
     apply getIndirectionMapMMUPage1 with entry;trivial. }
rewrite <- Hmykey3.
 case_eq( getIndirection pd a level (nbLevel - 1) s);intros. 
 case_eq( defaultPage =? p);intros;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 apply readPresentMapMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hpres.
  assert(Haccess :StateLib.readAccessible p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readAccessible p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 symmetry.
 apply readAccessibleMapMMUPage ;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Haccess.
 assert(Hread :StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 apply readPhyEntryMapMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hread.
 trivial.
 trivial.
 Qed.
Lemma getAccessibleMappedPagesMapMMUPage s ptVaChildpd idxvaChild phyVaChild e
 r w part phyDescChild vaChild entry level: 
 let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
 In ptVaChildpd (getConfigPages phyDescChild s) ->
disjoint (getConfigPages phyDescChild s) (getConfigPages part s) -> 
 lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
    Some (PE entry) ->
 Some level = StateLib.getNbLevel->
 configTablesAreDifferent s->
partitionDescriptorEntry s->
In phyDescChild (getPartitions multiplexer s)->
(forall idx : index,
     StateLib.getIndexOfAddr vaChild fstLevel = idx ->
     isPE ptVaChildpd idx s /\
     getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s)->
 (defaultPage =? ptVaChildpd) = false->

 phyDescChild <> part -> 
 In part (getPartitions multiplexer s)      ->               
 getAccessibleMappedPages part s = getAccessibleMappedPages part s'.
 Proof.
 intros s' Hconfigpt Hmykey2.
 intros.
   unfold getAccessibleMappedPages. 
     assert(Hgetpd : forall partition, StateLib.getPd partition
  (add ptVaChildpd idxvaChild(PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) 
     (memory s) beqPage beqIndex ) = StateLib.getPd partition (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
intros. 
rewrite Hgetpd in *. clear Hgetpd.
case_eq(StateLib.getPd part (memory s) );[intros pd Hpd1 |intros Hpd1];
trivial.
unfold getAccessibleMappedPagesAux.
unfold getAccessibleMappedPagesOption.
f_equal.
induction getAllVAddrWithOffset0;simpl;trivial.
f_equal.
  assert(Hpde : partitionDescriptorEntry s).
  unfold consistency in *.
  intuition. 
{  apply getAccessibleMappedPageMapMMUPage1 with part phyDescChild
vaChild entry level;trivial. }
 trivial.
 
 Qed.
Lemma getUsedPagesMapMMUPage s phyVaChild e w r idxvaChild ptVaChildpd
phyDescChild (vaChild : vaddr) entry level:
let s' := {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd idxvaChild
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
     Some (PE entry)  -> 
Some level = StateLib.getNbLevel -> 
configTablesAreDifferent s -> 
partitionDescriptorEntry s ->
       In phyDescChild (getPartitions multiplexer s) ->
       (forall idx : index,
        StateLib.getIndexOfAddr vaChild fstLevel = idx ->
        isPE ptVaChildpd idx s /\
        getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild  s) ->
       (defaultPage =? ptVaChildpd) = false ->      
forall part, phyDescChild <> part -> 
  In part (getPartitions multiplexer s) -> 
  getUsedPages part s = getUsedPages part s'.
Proof.
intros. 
  unfold getUsedPages.
  assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
  apply isConfigTable  with vaChild;trivial.
  unfold consistency in *. intuition.
  intros. subst. 
  assert(Hmykey2 :  disjoint (getConfigPages phyDescChild s)
                  (getConfigPages part s)).
  { assert(Hconfigdiff : configTablesAreDifferent s ) by (
    unfold consistency in *; intuition). apply Hconfigdiff;trivial. }
  f_equal.
  -  
 apply getConfigPagesMapMMUPage with phyDescChild entry;trivial.
 
 
 - 
 apply getMappedPagesMapMMUPage with phyDescChild vaChild
entry level;trivial.
Qed.

Lemma getIndirectionsPDSamePartMapMMUPage  s phyVaChild r w  e idxvaChild
ptVaChildpd phyDescChild entry (pdChildphy currentPart: page)
 (presentvaChild:bool) (vaChild:vaddr) level pd : 
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
StateLib.getPd phyDescChild (memory s) = Some pd -> 
consistency s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) ->
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s ->
(defaultPage =? ptVaChildpd) = false->
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
     Some (PE entry) -> 
Some level = StateLib.getNbLevel -> 

getIndirections pd s = getIndirections pd s'.
Proof.
intros s' Hpd.
unfold getIndirections.
intros.
{ assert(Hii :~In ptVaChildpd (getIndirectionsAux pdChildphy s (nbLevel-1))) .

assert(Hor1 : (nbLevel - 1) = 0 \/ (nbLevel - 1) > 0) by omega.
destruct Hor1 as [Hor1 | Hor1].
{ rewrite Hor1 in *. 

simpl. intuition. }
unfold consistency in *.
apply indirectionNotInPreviousMMULevel
with idxvaChild phyVaChild
currentPart presentvaChild vaChild phyDescChild level entry;intuition.
assert(Hfalse : pdChildphy = defaultPage) by trivial.
contradict Hfalse.
apply pdPartNotNull with phyDescChild s;trivial.
  { apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
  apply nextEntryIsPPgetPd;trivial.
  symmetry;trivial.
    intros;split;trivial.
    subst;trivial. }
  
 assert( pdChildphy=pd). 
 apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
 subst pd.
revert Hii.
clear.
revert pdChildphy.
induction nbLevel;simpl;trivial.
intros.
f_equal.
assert(Hor : n=0 \/ n>0) by omega.
destruct Hor as[Hor | Hor].
subst.
simpl in *.
induction((getTablePages pdChildphy tableSize s)).
induction((getTablePages pdChildphy tableSize s'));simpl;trivial.
simpl;trivial.
assert(Hrew : S (n -1) = n) by omega.
rewrite <- minus_n_O in Hii.
rewrite <- Hrew in Hii.


simpl in Hii.
apply not_or_and in  Hii.
destruct Hii as (Hii1 & Hii2).

assert(Htable : getTablePages pdChildphy tableSize s =
getTablePages pdChildphy tableSize s').
apply getTablePagesMapMMUPage with (n-1) ;trivial.
rewrite in_flat_map in Hii2;trivial.
rewrite <- Htable.
clear Htable.
rewrite in_flat_map in Hii2.
 induction  (getTablePages pdChildphy tableSize s);simpl;trivial.
 f_equal.
 apply IHn;trivial.
 unfold not;intros.
 contradict Hii2.
 exists a;simpl.
 split;trivial.
 left;trivial.
 apply IHl.
 unfold
  not;intros.
  contradict Hii2.
  destruct H as (x & Hx & Hxx).
  exists x;simpl.
  split;trivial.
  right;trivial. }
Qed.
  
Lemma getConfigPagesMapMMUPage1 s phyVaChild r w  e idxvaChild
ptVaChildpd phyDescChild entry (pdChildphy currentPart: page)
 (presentvaChild:bool) (vaChild:vaddr) level : 
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
consistency s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) ->
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s ->
(defaultPage =? ptVaChildpd) = false->
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
     Some (PE entry) -> 
Some level = StateLib.getNbLevel -> 
getConfigPages phyDescChild s = getConfigPages phyDescChild s'.
Proof.
intros s'.
intros. 
{ unfold getConfigPages.
  f_equal.
unfold getConfigPagesAux.
assert(Hpd : StateLib.getPd phyDescChild (memory s) =
StateLib.getPd phyDescChild (memory s')).
unfold s'. simpl.
symmetry. apply getPdMapMMUPage with entry;trivial.
rewrite <- Hpd. clear Hpd.
assert(Hpd : StateLib.getFstShadow phyDescChild (memory s) =
StateLib.getFstShadow phyDescChild (memory s')).
unfold s'. simpl.
symmetry. apply getFstShadowMapMMUPage with entry;trivial.
rewrite <- Hpd. clear Hpd.
assert(Hpd : StateLib.getSndShadow phyDescChild (memory s) =
StateLib.getSndShadow phyDescChild (memory s')).
unfold s'. simpl.
symmetry. apply getSndShadowMapMMUPage with entry;trivial.
rewrite <- Hpd. clear Hpd.
assert(Hpd : StateLib.getConfigTablesLinkedList  phyDescChild (memory s) =
StateLib.getConfigTablesLinkedList  phyDescChild (memory s')).
unfold s'. simpl.
symmetry. apply getConfigTablesLinkedListMapMMUPage with entry;trivial.
rewrite <- Hpd. clear Hpd.
case_eq(StateLib.getPd phyDescChild (memory s));trivial.
intros pd Hpd.
case_eq(getFstShadow phyDescChild (memory s));trivial.
intros sh1 Hsh1.
case_eq(getSndShadow phyDescChild (memory s));trivial.
intros sh2 Hsh2.
case_eq(getConfigTablesLinkedList phyDescChild (memory s));trivial.
intros ll Hll.
f_equal.
+ apply getIndirectionsPDSamePartMapMMUPage with phyDescChild entry
pdChildphy currentPart presentvaChild vaChild level;trivial.  
+ f_equal.

 unfold getIndirections.
intros.
apply getIndirectionsMapMMUPage1 with entry;trivial.
assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
{ apply isConfigTable  with vaChild;trivial.
unfold consistency in *.
intuition.
intros. subst. split;trivial. }
assert (Hnodup2: noDupConfigPagesList s) by (unfold consistency in *;intuition).
 unfold noDupConfigPagesList in *. 
assert(Hdisjoint: disjoint (getIndirections pdChildphy s) (getIndirections sh1 s)). 
{ (* clear  apply Hnodup2 in Hpart. *)
unfold getConfigPages in *.
(* apply NoDup_cons_iff in Hpart as(_ & Hpart). *)
unfold getConfigPagesAux in *.
assert(Hpdchild : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
rewrite nextEntryIsPPgetPd in *. 
rewrite Hpd in Hconfigpt.
rewrite Hsh1 in *.
case_eq (getSndShadow phyDescChild (memory s));[intros sh21 Hsh21 | intros Hsh21] ;
rewrite Hsh21 in *.
case_eq (getConfigTablesLinkedList phyDescChild (memory s));[intros ll1 Hll1| intros Hll1] ;
rewrite Hll1 in *.
assert(Hpartchild : In phyDescChild (getPartitions multiplexer s)) by trivial.
apply Hnodup2 in Hpartchild.
clear Hnodup2.
rewrite Hpdchild in *.
rewrite Hsh1 in *.
rewrite Hsh21 in *.
rewrite Hll1 in *.
apply NoDup_cons_iff in Hpartchild.
destruct Hpartchild as (Hi1 & Hnodup).
rewrite NoDupSplitInclIff in Hnodup.
destruct Hnodup as (Hi2 & Hnodup).
unfold disjoint in *. 
intuition.
apply Hnodup with x;trivial.
apply in_app_iff.
left;trivial.
now contradict Hll.
now contradict Hsh2. }
unfold disjoint in *.

apply Hdisjoint;trivial.
unfold getIndirections.

apply getIndirectionInGetIndirections with vaChild level (nbLevel -1);trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.

apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
apply nextEntryIsPPgetPd; trivial.
symmetry;trivial.
intros;subst;split;trivial.
assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial.
apply beq_nat_false in Hdefaut.
unfold not;intros;subst.
now contradict Hdefaut.
assert(Hlevel : Some level = StateLib.getNbLevel) by trivial.
apply getNbLevelLe in Hlevel;trivial.

apply pdPartNotNull with phyDescChild s;trivial.
unfold consistency in *.
intuition.
 f_equal. unfold getIndirections.
apply getIndirectionsMapMMUPage1 with entry;trivial.
assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
{ apply isConfigTable  with vaChild;trivial.
unfold consistency in *.
intuition.
intros. subst. split;trivial. }
assert (Hnodup2: noDupConfigPagesList s) by (unfold consistency in *;intuition).
 unfold noDupConfigPagesList in *. 
assert(Hdisjoint: disjoint (getIndirections pdChildphy s) (getIndirections sh2 s)). 
{  (* apply Hnodup2 in Hpart. *)
unfold getConfigPages in *.
(* apply NoDup_cons_iff in Hpart as(_ & Hpart). *)
unfold getConfigPagesAux in *.
assert(Hpdchild : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
rewrite nextEntryIsPPgetPd in *. 
rewrite Hpd in Hconfigpt.
rewrite Hsh1 in *.
case_eq (getSndShadow phyDescChild (memory s));[intros sh21 Hsh21 | intros Hsh21] ;
rewrite Hsh21 in *.
case_eq (getConfigTablesLinkedList phyDescChild (memory s));[intros ll1 Hll1| intros Hll1] ;
rewrite Hll1 in *.
(* clear Hpart. *)
assert(Hpartchild : In phyDescChild (getPartitions multiplexer s)) by trivial.
apply Hnodup2 in Hpartchild.
clear Hnodup2.
rewrite Hpdchild in *.
rewrite Hsh1 in *. 
inversion Hsh2;subst.
inversion Hll;subst.
rewrite Hsh21 in *.
rewrite Hll1 in *. 
apply NoDup_cons_iff in Hpartchild.
destruct Hpartchild as (Hi1 & Hnodup).
rewrite NoDupSplitInclIff in Hnodup.
destruct Hnodup as (Hi2 & Hnodup).
unfold disjoint in *. 
intuition.
apply Hnodup with x;trivial.
apply in_app_iff.
right;trivial.
apply in_app_iff.
left;trivial.

now contradict Hll.
now contradict Hsh2. }
unfold disjoint in *.

apply Hdisjoint;trivial.
unfold getIndirections.

apply getIndirectionInGetIndirections with vaChild level (nbLevel -1);trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.

apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
apply nextEntryIsPPgetPd; trivial.
symmetry;trivial.
intros;subst;split;trivial.
assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial.
apply beq_nat_false in Hdefaut.
unfold not;intros;subst.
now contradict Hdefaut.
assert(Hlevel : Some level = StateLib.getNbLevel) by trivial.
apply getNbLevelLe in Hlevel;trivial.

apply pdPartNotNull with phyDescChild s;trivial.
unfold consistency in *.
intuition.
apply getLLPagesMapMMUPage with entry;trivial.
assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
{ apply isConfigTable  with vaChild;trivial.
unfold consistency in *.
intuition.
intros. subst. split;trivial. }
assert (Hnodup2: noDupConfigPagesList s) by (unfold consistency in *;intuition).
 unfold noDupConfigPagesList in *. 
assert(Hdisjoint: disjoint (getIndirections pdChildphy s) (getLLPages ll s (nbPage + 1))). 
{ (*   apply Hnodup2 in Hpart. *)
unfold getConfigPages in *.
(* apply NoDup_cons_iff in Hpart as(_ & Hpart). *)
unfold getConfigPagesAux in *.
assert(Hpdchild : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
rewrite nextEntryIsPPgetPd in *. 
rewrite Hpd in Hconfigpt.
rewrite Hsh1 in *.
case_eq (getSndShadow phyDescChild (memory s));[intros sh21 Hsh21 | intros Hsh21] ;
rewrite Hsh21 in *.
case_eq (getConfigTablesLinkedList phyDescChild (memory s));[intros ll1 Hll1| intros Hll1] ;
rewrite Hll1 in *.
(* clear Hpart. *)
assert(Hpartchild : In phyDescChild (getPartitions multiplexer s)) by trivial.
apply Hnodup2 in Hpartchild.
clear Hnodup2.
rewrite Hpdchild in *.
rewrite Hsh1 in *. 
inversion Hsh2;subst.
inversion Hll;subst.
rewrite Hsh21 in *.
rewrite Hll1 in *. 
apply NoDup_cons_iff in Hpartchild.
destruct Hpartchild as (Hi1 & Hnodup).
rewrite NoDupSplitInclIff in Hnodup.
destruct Hnodup as (Hi2 & Hnodup).
unfold disjoint in *. 
intuition.
apply Hnodup with x;trivial.
apply in_app_iff.
right;trivial.
apply in_app_iff.
right;trivial.


now contradict Hll.
now contradict Hsh2. }
unfold disjoint in *.

apply Hdisjoint;trivial.
unfold getIndirections.

apply getIndirectionInGetIndirections with vaChild level (nbLevel -1);trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.

apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
apply nextEntryIsPPgetPd; trivial.
symmetry;trivial.
intros;subst;split;trivial.
assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial.
apply beq_nat_false in Hdefaut.
unfold not;intros;subst.
now contradict Hdefaut.
assert(Hlevel : Some level = StateLib.getNbLevel) by trivial.
apply getNbLevelLe in Hlevel;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
unfold consistency in *.
intuition.
}
Qed.



Lemma getAccessibleMappedPageMapMMUPage vax s pdChildphy phyVaChild x ptVaChildpd  r w e
(vaChild : vaddr) (phyDescChild : page) level entry: 
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
x <> phyVaChild -> 
getAccessibleMappedPage pdChildphy s' vax = SomePage x -> 
Some level = StateLib.getNbLevel -> 
StateLib.getPd phyDescChild (memory s) = Some pdChildphy -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s)
       beqPage beqIndex = Some (PE entry) -> 
consistency s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
In phyDescChild (getPartitions multiplexer s)-> 
(defaultPage =? ptVaChildpd) = false -> 
entryPresentFlag ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) false s -> 
checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false -> 
getAccessibleMappedPage pdChildphy s vax = SomePage x.
Proof.  
intros s' Hor Hvax Hlevel Hpp.
intros.
assert(Hindchild : getIndirection pdChildphy vaChild level (nbLevel - 1) s =
  Some ptVaChildpd). 
{ apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
  symmetry;trivial.
  intros;split;trivial.
  subst;trivial. }
rewrite <- Hvax. 
unfold getAccessibleMappedPage.
rewrite <- Hlevel. 
case_eq(getIndirection pdChildphy vax level (nbLevel - 1) s );intros.
assert(Hii:   getIndirection pdChildphy vax level (nbLevel - 1) s' = Some p).
{ unfold consistency in *. 
  intuition.
  apply getIndirectionMapMMUPage2
    with (currentPartition s) false vaChild phyDescChild entry; subst;trivial.
   symmetry;trivial.
  apply nextEntryIsPPgetPd;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
rewrite Hii.
   assert(Hnodupconf : noDupConfigPagesList s).
    unfold consistency in *. 
    intuition.
  case_eq(defaultPage =? p);intros Hnotdef;trivial.  
   assert(ptVaChildpd <> p \/ (StateLib.getIndexOfAddr vaChild fstLevel) <> 
  (StateLib.getIndexOfAddr vax fstLevel)).
   apply pageTablesOrIndicesAreDifferent with pdChildphy pdChildphy
    level nbLevel s;trivial.
    apply pdPartNotNull with phyDescChild s;trivial.
    apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
    apply pdPartNotNull with phyDescChild s;trivial.
     apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
  apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.
    apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.
  left.
  split;trivial.
  apply getNbLevelEq.
  trivial.
  assert(Hdefaut: (defaultPage =? ptVaChildpd) = false) by trivial.
    apply beq_nat_false in Hdefaut.
    unfold not;intros;subst;now contradict Hdefaut.
  apply beq_nat_false in Hnotdef.
  unfold not;intros;subst;trivial.
  now contradict Hnotdef.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;symmetry;trivial.
 
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;symmetry;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s)
 = StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s')). 
 apply readPresentMapMMUPage with entry;trivial.
 intuition.
 rewrite <- Hpres.
  assert(Haccess :StateLib.readAccessible p (StateLib.getIndexOfAddr vax fstLevel) (memory s)
 = StateLib.readAccessible p (StateLib.getIndexOfAddr vax fstLevel) (memory s')). 
 symmetry. apply readAccessibleMapMMUPage;trivial.
 intuition.
 rewrite <- Haccess.
 case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s));intros.
 destruct b;trivial.
 symmetry.
  case_eq(StateLib.readAccessible p (StateLib.getIndexOfAddr vax fstLevel) (memory s));intros.
 destruct b;trivial.
 assert(Heq : StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s')=
  StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s)).
  symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 intuition.
 rewrite Heq.
 trivial.
 trivial.
 trivial.
 assert(Hnone : getIndirection pdChildphy vax level (nbLevel - 1) s' = None).
 unfold consistency in *.
 intuition.
 apply getIndirectionNoneMapMMUPage2 with (currentPartition s) false vaChild phyDescChild entry;trivial.
symmetry. trivial.
apply nextEntryIsPPgetPd;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply nextEntryIsPPgetPd;trivial.
rewrite Hnone;trivial.
Qed.

      

       Lemma getMappedPageKeepsAnyAccessibleMappedPage pdChildphy s vax vaChild
        ptVaChildpd x phyVaChild r w e phyDescChild entry level
        (currentPart:page) :
        let s':={|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
     lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
            (memory s) beqPage beqIndex = Some (PE entry) -> 
            Some level = StateLib.getNbLevel -> 
      getAccessibleMappedPage pdChildphy s vax = SomePage x ->
entryPresentFlag ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) false
  s -> StateLib.getPd phyDescChild (memory s) = Some pdChildphy
  -> 
  partitionDescriptorEntry s -> 
isPresentNotDefaultIff s -> 
noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
pdChildphy <> defaultPage-> 
getIndirection pdChildphy vaChild level (nbLevel - 1) s = Some ptVaChildpd -> 
  getAccessibleMappedPage pdChildphy s' vax = SomePage x.
  Proof.
  intros s' Hlookup Hlevel Hmap Hpres Hpd.
  intros.
  unfold getAccessibleMappedPage in *.
  rewrite <- Hlevel in *.
  case_eq(getIndirection pdChildphy vax level (nbLevel - 1) s );
  [intros ind Hind | intros Hind];rewrite Hind in *;
  try now contradict Hmap.
  assert(Hind' :getIndirection pdChildphy vax level (nbLevel - 1) s'
  = Some ind).
  { apply getIndirectionMapMMUPage2
  with currentPart
false vaChild phyDescChild entry;trivial.
symmetry ;trivial. }
rewrite Hind'.
case_eq(defaultPage =? ind);intros Hdef;rewrite Hdef in *.
now contradict Hmap.
case_eq(StateLib.readPresent ind (StateLib.getIndexOfAddr vax fstLevel)
           (memory s));[intros ispres Hispres | intros Hispres];
           rewrite Hispres in *;try now contradict Hmap.
case_eq(ispres);intros Hb;rewrite Hb in *;clear Hb;try now contradict Hmap.
move Hpres at bottom.
assert(Hispres1 : StateLib.readPresent ind (StateLib.getIndexOfAddr vax fstLevel)
            (memory s) = Some true) by trivial.
unfold entryPresentFlag in Hpres.
  unfold StateLib.readPresent in Hispres.
assert(Hmykey5 : ind <> ptVaChildpd \/
StateLib.getIndexOfAddr vax fstLevel <>
StateLib.getIndexOfAddr vaChild fstLevel). 
{
  assert(Hor : (  (ind <> ptVaChildpd \/
StateLib.getIndexOfAddr vax fstLevel <>
StateLib.getIndexOfAddr vaChild fstLevel) \/  (~ (ind <> ptVaChildpd \/
StateLib.getIndexOfAddr vax fstLevel <>
StateLib.getIndexOfAddr vaChild fstLevel)))).
{ apply classic. }
destruct Hor as [Hor | Hor];trivial.
apply not_or_and in Hor.
destruct Hor as(Hi1 & Hi2) .
subst.
apply NNPP in Hi1.
apply NNPP in Hi2.
rewrite Hi2 in *. clear Hi2.
subst.
destruct (lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
              (memory s) beqPage beqIndex);simpl in *;try now contradict Hpres.
destruct v;try now contradict Hpres.
inversion Hispres.
subst.
destruct (present p);try now contradict Hpres. }


assert(Hpreseq :  StateLib.readPresent ind (StateLib.getIndexOfAddr vax fstLevel) (memory s') =
  StateLib.readPresent ind (StateLib.getIndexOfAddr vax fstLevel) (memory s)).
  { symmetry. apply readPresentMapMMUPage with entry;trivial. }
assert(Haccess :  StateLib.readAccessible ind (StateLib.getIndexOfAddr vax fstLevel) (memory s') =
  StateLib.readAccessible ind (StateLib.getIndexOfAddr vax fstLevel) (memory s)).
  { apply readAccessibleMapMMUPage ;trivial. }
rewrite Hpreseq.
rewrite Hispres1.
rewrite Haccess.
destruct(StateLib.readAccessible ind (StateLib.getIndexOfAddr vax fstLevel)
           (memory s));trivial.

rewrite <- Hmap.
destruct b;trivial.
symmetry.
 assert(Heq : StateLib.readPhyEntry ind (StateLib.getIndexOfAddr vax fstLevel) (memory s')=
  StateLib.readPhyEntry ind (StateLib.getIndexOfAddr vax fstLevel) (memory s)).
  symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 rewrite Heq.
 trivial.
Qed.

Lemma noDupMappedPagesListMapMMUPage s  ptVaChildpd idxvaChild phyVaChild r w e
  entry 
 (vaChild vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD  pdChildphy phyDescChild :page)
  ( presentvaChild :bool)
(level :level) isnotderiv accessiblesrc presentmap:
consistency s -> 
(forall child : page,  
    In child (getChildren (currentPartition s) s) -> ~ In phyVaChild (getMappedPages child s)) -> 
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
noDupMappedPagesList s -> 
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true  -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
noDupPartitionTree s ->
partitionDescriptorEntry s -> 
isPresentNotDefaultIff s -> noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd 
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd  
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> (forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 

In phyDescChild (getChildren (currentPartition s) s) ->
noDupMappedPagesList  {|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hconsitency Hnotderiv Hconsnew1 Hconsnew Hnodup Hlegit.
set(s':= {|  currentPartition := _ |}) in *.
intros.
unfold noDupMappedPagesList in *.
move Hnodup at bottom.
intros partition Hpart.
assert(Hparts : In partition (getPartitions multiplexer s)).
apply getPartitionsMapMMUPage  with entry
vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd idxvaChild
phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
level;trivial.
assert (Hnewmapp : getMappedPage pdChildphy s' vaChild = SomePage phyVaChild).
{    subst.     assert(Hlookup :
lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s)
beqPage beqIndex = Some (PE entry))
by trivial. 
assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
(StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some defaultPage).
{ assert(Hcons1 : isPresentNotDefaultIff s).
unfold consistency in *. intuition.            
apply Hcons1.
subst.
apply andb_true_iff in Hlegit.
destruct Hlegit as (_ & Hlegit).
apply negb_true_iff in Hlegit.
subst.
assert(Hentrypresent : entryPresentFlag ptVaChildpd
(StateLib.getIndexOfAddr vaChild fstLevel) false s) by trivial.
move Hentrypresent at bottom.
unfold entryPresentFlag in *. 
unfold StateLib.readPresent.

rewrite Hlookup in *.
f_equal.
rewrite Hentrypresent. trivial. }
assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some phyVaChild).
{ unfold StateLib.readPhyEntry. 
cbn.
assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
(ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
beqIndex = true); intros.
rewrite <- beqPairsTrue;split;trivial.
rewrite Hpairs.
simpl;trivial. } 
 apply getMappedPageGetTableRoot with ptVaChildpd phyDescChild;
  trivial;fold s'. 
  + intros. 
  split. 
  apply isPEMapMMUPage with entry;trivial.
  subst;trivial.
  assert(Htblroot : getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
  unfold getTableAddrRoot in Htblroot.
  destruct Htblroot as (Hidxs & Htblroot).
  split;trivial.
  intros.
  assert(Hpdchild : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Htblroot in Hpdchild;clear Htblroot.
  move Hpdchild at bottom.
  destruct Hpdchild as (nbL & HnbL & stop & Hstop & Hind1).
  exists nbL ; split ; trivial.
  exists stop;split;trivial.
  assert(tableroot = pdChildphy). 
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  phyVaChild r w  e;trivial.
  subst. trivial.
  subst .
  revert Hind1.       
  assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial.
  assert(Htrue3 : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  revert Htrue1 Htrue2 Hlookup Hdefaut Htrue3.
  clear. 
  intros.
  apply nextEntryIsPPgetPd;trivial.
  subst.
   apply getIndirectionMapMMUPage with entry;trivial;subst;trivial.
+ unfold isEntryPage, StateLib.readPhyEntry in *. 
   destruct(lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
             (memory s') beqPage beqIndex);trivial;try now contradict Htrue2.
   destruct v;try now contradict Htrue2.
   inversion Htrue2;trivial.
+ unfold entryPresentFlag. 
   cbn.
   subst.
   assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
      beqIndex = true).
   apply beqPairsTrue;split;trivial.
   rewrite Hpairs.
   simpl;trivial.
       
+ apply  nextEntryIsPPMapMMUPage with entry;trivial. }  
assert (Hnodup1 : NoDup (getMappedPages partition s) ).
apply Hnodup;trivial. clear Hnodup.
unfold getMappedPages in *.
assert(Hpd : StateLib.getPd partition (memory s) =
        StateLib.getPd partition (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdMapMMUPage with entry;trivial. }
rewrite <- Hpd in *.
case_eq(StateLib.getPd partition (memory s) );[intros pd Hpdpart | intros Hpdpart];[|constructor].
rewrite Hpdpart in *.

assert ( Hor : partition = phyDescChild \/ partition <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [ Hor | Hor]. 
+  subst.
  symmetry in Hpd. 
  assert (pd = pdChildphy).
  { rewrite nextEntryIsPPgetPd in *.
    rewrite Hpdpart in *.
    assert(Heq : Some pd = Some pdChildphy) by trivial.
    inversion Heq;subst;trivial. }
  subst. 
(*   assert(Hnodupva : NoDup getAllVAddr) by apply noDupAllVaddr. *)
  unfold getMappedPagesAux in *.
  assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
assert(Hnewmapp1 : getMappedPage pdChildphy s' va1 = SomePage phyVaChild). 
{ rewrite <- Hnewmapp.
  symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption. }
assert(Hmykey2 : In phyVaChild (getMappedPagesAux pdChildphy getAllVAddrWithOffset0 s')).
{ unfold getMappedPagesAux.
  apply filterOptionInIff.
  unfold getMappedPagesOption.
  apply in_map_iff.
  exists va1;split;trivial. }
assert(Hmykey4 : ~In phyVaChild (getMappedPagesAux pdChildphy getAllVAddrWithOffset0 s)) .
{ assert(Hchild :  In phyDescChild (getChildren (currentPartition s) s) ) by trivial.
  apply Hnotderiv in Hchild. clear Hnotderiv.
  rewrite Hpdpart in *. 
  unfold getMappedPagesAux;trivial. }
clear Hnotderiv.
assert(Hnodupvar : NoDup getAllVAddrWithOffset0) by apply noDupAllVAddrWithOffset0 . 
assert(Htrue : getMappedPage pdChildphy s vaChild = SomeDefault
).
      { apply getMappedPageNotPresent with ptVaChildpd phyDescChild;intuition;
        subst;trivial. 
        apply andb_true_iff in Hlegit.
        destruct Hlegit as (_ & Hlegit).
        apply negb_true_iff in Hlegit.
        subst; trivial. }
  assert(Hnone: getMappedPage pdChildphy s va1 = SomeDefault) .
  { rewrite <- Htrue.
  symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption. }

      assert (Hmykey: exists  l1 l2,
getMappedPages phyDescChild s'
                      = l1 ++ [phyVaChild] ++ l2 /\
getMappedPages phyDescChild s = l1 ++l2).
{  clear Hnodup1 .
  move Hnewmapp at bottom.
  assert(Htriche1 : NoDup getAllVAddrWithOffset0) by  apply noDupAllVAddrWithOffset0.
  unfold getMappedPages .
  rewrite Hpdpart.
  rewrite Hpd.
  unfold getMappedPagesAux in *. 
  unfold getAllVAddrWithOffset0 in *.
  induction getAllVAddr;simpl in *; try now contradict Hva1.
  case_eq(checkOffset0 a);intros Hcheck;rewrite Hcheck in *. 

+
 subst;simpl in *. 
case_eq(getMappedPage pdChildphy s a);[intros phya Ha| intros Ha| intros Ha];rewrite Ha in *.
-  simpl in *.
  apply not_or_and in Hmykey4.
  destruct Hva1 as [ Hva1 | Hva1];subst;trivial.
  * assert(Hey : getMappedPage pdChildphy s va1  = getMappedPage pdChildphy s vaChild).
    { apply getMappedPageEq with  (CLevel (nbLevel - 1)) ;trivial.
      apply getNbLevelEqOption.
      rewrite <- Hva11 .
      apply checkVAddrsEqualityWOOffsetPermut;trivial. }
   rewrite  Hey in Ha.
   rewrite  Ha in Htrue.
   now contradict Htrue.
 * assert (Hk1 : getMappedPage pdChildphy s' a= SomePage phya). 
 { apply getMappedPageKeepsAnyMappedPage with phyDescChild entry level (currentPartition s);
 trivial.
 symmetry;trivial.
rewrite negb_true_iff in *.
subst;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
intros;subst;split;trivial. }
rewrite Hk1 in *.
assert(IHlnew :  exists l1 l2 : list page,
        filterOption
          (getMappedPagesOption pdChildphy (filter checkOffset0 l) s') =
        l1 ++ phyVaChild :: l2 /\
        filterOption
          (getMappedPagesOption pdChildphy (filter checkOffset0 l) s) =
        l1 ++ l2).
{        apply IHl;trivial.
simpl in *. 
  intuition.
  intuition.
  apply NoDup_cons_iff in Htriche1.
  intuition.
  apply NoDup_cons_iff in Htriche1.
  intuition.
         }
clear IHl.
destruct IHlnew as (l1 & l2 & Hs & Hs').
rewrite Hs.
rewrite Hs'.
exists (phya :: l1).
exists l2.
split;
simpl;trivial.
- destruct Hva1 as [ Hva1 | Hva1];subst;trivial.
**  rewrite Hnewmapp1 in *.

simpl in *.
(* destruct Hmykey2 as [ Hmykey2 |Hmykey2 ]. *)
clear Hmykey2.
{ clear IHl. subst.

exists [].
        exists (filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s) ).
        split;simpl;trivial.
        f_equal.
        apply NoDup_cons_iff in Htriche1 as (Hi1 & Hi2).
        (* induction  (filter checkOffset0 l);simpl in *;trivial. *)
        
        
        induction l;simpl in *;trivial.
        case_eq(checkOffset0 a);intros Hoff;simpl in *;rewrite Hoff in *.
        + unfold getMappedPagesOption in Hmykey4.
          simpl in *.
        case_eq( getMappedPage pdChildphy s a );[intros mapped Hmapped | intros Hmapped| intros Hmapped];
        rewrite Hmapped in *.
        -
        assert(Hkeep : getMappedPage pdChildphy s' a = SomePage mapped).
        apply getMappedPageKeepsAnyMappedPage with phyDescChild entry
level (currentPartition s);subst;trivial.
symmetry;trivial.
rewrite negb_true_iff in *.
subst;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
intros;subst;split;trivial.
rewrite Hkeep.
f_equal.
apply IHl.
intuition.
constructor.
intuition.
apply NoDup_cons_iff in Hi2.
intuition.

apply NoDup_cons_iff in Hi2.
intuition.
apply NoDup_cons_iff in Hi2.
intuition.
-
assert(Hoffeq :  checkVAddrsEqualityWOOffset nbLevel a va1
          (CLevel (nbLevel - 1)) = false).
{ assert(Hi1aux :~ (a = va1 \/ In va1 (filter checkOffset0 l))) by trivial.
  apply not_or_and in Hi1aux. 
  destruct Hi1aux as (Hi11 & Hi1aux).
  rewrite filter_In in Hi1aux.
  apply not_and_or in Hi1aux.
  intuition.
  apply checkVAddrsEqualityWOOffsetFalseEqOffset;trivial.
  apply getNbLevelEqOption. } 
 assert(Hnewkey : getMappedPage pdChildphy s' a = SomeDefault).
{ apply getMappedPageDefaultMapMMUPage'  with phyDescChild level entry;trivial.
symmetry;trivial.
rewrite negb_true_iff in *;subst;intuition.
apply checkVAddrsEqualityWOOffsetTrans with va1;trivial.
rewrite <- Hva11.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.
rewrite <- Hoffeq.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.

 }
rewrite  Hnewkey.
apply IHl;intuition.
apply NoDup_cons_iff in Hi2.
intuition.
apply NoDup_cons_iff in Hnodupvar.
rewrite NoDup_cons_iff in Hnodupvar.
constructor.
intuition.
intuition.
apply NoDup_cons_iff in Hnodupvar.
rewrite NoDup_cons_iff in Hnodupvar.
intuition.
-
assert(Hoffeq :  checkVAddrsEqualityWOOffset nbLevel a va1
          (CLevel (nbLevel - 1)) = false).
{ assert(Hi1aux :~ (a = va1 \/ In va1 (filter checkOffset0 l))) by trivial.
  apply not_or_and in Hi1aux. 
  destruct Hi1aux as (Hi11 & Hi1aux).
  rewrite filter_In in Hi1aux.
  apply not_and_or in Hi1aux.
  intuition.
  apply checkVAddrsEqualityWOOffsetFalseEqOffset;trivial.
  apply getNbLevelEqOption. } 
 assert(Hnewkey : getMappedPage pdChildphy s' a = NonePage).
{ apply getMappedPageNoneMapMMUPage'  with phyDescChild level entry;trivial.
symmetry;trivial.
rewrite negb_true_iff in *;subst;intuition.
apply checkVAddrsEqualityWOOffsetTrans with va1;trivial.
rewrite <- Hva11.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.
rewrite <- Hoffeq.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.

 }
rewrite  Hnewkey.
apply IHl;intuition.
apply NoDup_cons_iff in Hi2.
intuition.
apply NoDup_cons_iff in Hnodupvar.
rewrite NoDup_cons_iff in Hnodupvar.
constructor.
intuition.
intuition.
apply NoDup_cons_iff in Hnodupvar.
rewrite NoDup_cons_iff in Hnodupvar.
intuition.
+


 apply IHl;trivial. }
** case_eq (getMappedPage pdChildphy s' a);[intros phy Hphy| intros Hphy| intros Hphy];rewrite Hphy in *. 
{ simpl in *. 
  destruct Hmykey2 as [Hmykey2 | Hmykey2]. 
  + subst. 
  move Hva1 at bottom.
  apply NoDup_cons_iff in Htriche1 as (Htriche1 & _).
  move Htriche1 at bottom.
  move Hcheck at bottom.
  assert(Hcheckva1 : checkOffset0 va1 = true).
  { apply filter_In in Hva1.
    intuition. }
  assert(Hoffeq: checkVAddrsEqualityWOOffset nbLevel a va1
          (CLevel (nbLevel - 1)) = false).
  { apply checkVAddrsEqualityWOOffsetFalseEqOffset ;trivial. 
  apply getNbLevelEqOption.
  unfold not;intros;subst.
  now contradict Htriche1. }
assert(Hgoal : getMappedPage pdChildphy s' a = SomeDefault).
{ apply getMappedPageDefaultMapMMUPage'  with phyDescChild level entry;trivial.
symmetry;trivial.
rewrite negb_true_iff in *;subst;intuition.
apply checkVAddrsEqualityWOOffsetTrans with va1;trivial.
rewrite <- Hva11.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.
rewrite <- Hoffeq.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.

 }
rewrite Hgoal in Hphy.
now contradict Hphy.
+ 
  move Hva1 at bottom.
  apply NoDup_cons_iff in Htriche1 as (Htriche1 & Htriche11).
  move Htriche1 at bottom.
  move Hcheck at bottom.
  assert(Hcheckva1 : checkOffset0 va1 = true).
  { apply filter_In in Hva1.
    intuition. }
  assert(Hoffeq : checkVAddrsEqualityWOOffset nbLevel a va1
          (CLevel (nbLevel - 1)) = false).
  { apply checkVAddrsEqualityWOOffsetFalseEqOffset ;trivial. 
  apply getNbLevelEqOption.
  unfold not;intros;subst.
  now contradict Htriche1. }

assert(Hgoal : getMappedPage pdChildphy s' a = SomeDefault).
{ apply getMappedPageDefaultMapMMUPage'  with phyDescChild level entry;trivial.
symmetry;trivial.
rewrite negb_true_iff in *;subst;intuition.
apply checkVAddrsEqualityWOOffsetTrans with va1;trivial.
rewrite <- Hva11.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.
rewrite <- Hoffeq.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.

 }
 
 
rewrite Hgoal in Hphy.
now contradict Hphy.  }


 
assert(Hihl: exists l1 l2 : list page,
        filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s') =
        l1 ++ phyVaChild :: l2 /\
        filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s) = l1 ++ l2).
{ apply IHl;trivial.


  simpl in *;intuition.
  apply NoDup_cons_iff in Htriche1.
  intuition. 
  apply NoDup_cons_iff in Htriche1;intuition. }
destruct Hihl as (l1 & l2 & Hl1 & Hl2).
exists l1, l2.
split;trivial.
 assert(Hihl: exists l1 l2 : list page,
        filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s') =
        l1 ++ phyVaChild :: l2 /\
        filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s) = l1 ++ l2).
{ apply IHl;trivial.

apply NoDup_cons_iff in Hnodupvar;intuition.

apply NoDup_cons_iff in Hnodupvar;intuition.

 }
destruct Hihl as (l1 & l2 & Hl1 & Hl2).
exists l1, l2.
split;trivial. 
- destruct Hva1 as [ Hva1 | Hva1];subst;trivial.
**  rewrite Hnewmapp1 in *.

simpl in *.
(* destruct Hmykey2 as [ Hmykey2 |Hmykey2 ]. *)
clear Hmykey2.
{ clear IHl. subst.

exists [].
        exists (filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s) ).
        split;simpl;trivial.
        f_equal.
        apply NoDup_cons_iff in Htriche1 as (Hi1 & Hi2).
        (* induction  (filter checkOffset0 l);simpl in *;trivial. *)
        
        
        induction l;simpl in *;trivial.
        case_eq(checkOffset0 a);intros Hoff;simpl in *;rewrite Hoff in *.
        + unfold getMappedPagesOption in Hmykey4.
          simpl in *.
        case_eq( getMappedPage pdChildphy s a );[intros mapped Hmapped | intros Hmapped| intros Hmapped];
        rewrite Hmapped in *.
        -
        assert(Hkeep : getMappedPage pdChildphy s' a = SomePage mapped).
        apply getMappedPageKeepsAnyMappedPage with phyDescChild entry
level (currentPartition s);subst;trivial.
symmetry;trivial.
rewrite negb_true_iff in *.
subst;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
intros;subst;split;trivial.
rewrite Hkeep.
f_equal.
apply IHl.
intuition.
constructor.
intuition.
apply NoDup_cons_iff in Hi2.
intuition.

apply NoDup_cons_iff in Hi2.
intuition.
apply NoDup_cons_iff in Hi2.
intuition.
-
assert(Hoffeq :  checkVAddrsEqualityWOOffset nbLevel a va1
          (CLevel (nbLevel - 1)) = false).
{ assert(Hi1aux :~ (a = va1 \/ In va1 (filter checkOffset0 l))) by trivial.
  apply not_or_and in Hi1aux. 
  destruct Hi1aux as (Hi11 & Hi1aux).
  rewrite filter_In in Hi1aux.
  apply not_and_or in Hi1aux.
  intuition.
  apply checkVAddrsEqualityWOOffsetFalseEqOffset;trivial.
  apply getNbLevelEqOption. } 
 assert(Hnewkey : getMappedPage pdChildphy s' a = SomeDefault).
{ apply getMappedPageDefaultMapMMUPage'  with phyDescChild level entry;trivial.
symmetry;trivial.
rewrite negb_true_iff in *;subst;intuition.
apply checkVAddrsEqualityWOOffsetTrans with va1;trivial.
rewrite <- Hva11.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.
rewrite <- Hoffeq.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.

 }
rewrite  Hnewkey.
apply IHl;intuition.
apply NoDup_cons_iff in Hi2.
intuition.
apply NoDup_cons_iff in Hnodupvar.
rewrite NoDup_cons_iff in Hnodupvar.
constructor.
intuition.
intuition.
apply NoDup_cons_iff in Hnodupvar.
rewrite NoDup_cons_iff in Hnodupvar.
intuition.
-
assert(Hoffeq :  checkVAddrsEqualityWOOffset nbLevel a va1
          (CLevel (nbLevel - 1)) = false).
{ assert(Hi1aux :~ (a = va1 \/ In va1 (filter checkOffset0 l))) by trivial.
  apply not_or_and in Hi1aux. 
  destruct Hi1aux as (Hi11 & Hi1aux).
  rewrite filter_In in Hi1aux.
  apply not_and_or in Hi1aux.
  intuition.
  apply checkVAddrsEqualityWOOffsetFalseEqOffset;trivial.
  apply getNbLevelEqOption. } 
 assert(Hnewkey : getMappedPage pdChildphy s' a = NonePage).
{ apply getMappedPageNoneMapMMUPage'  with phyDescChild level entry;trivial.
symmetry;trivial.
rewrite negb_true_iff in *;subst;intuition.
apply checkVAddrsEqualityWOOffsetTrans with va1;trivial.
rewrite <- Hva11.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.
rewrite <- Hoffeq.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.

 }
rewrite  Hnewkey.
apply IHl;intuition.
apply NoDup_cons_iff in Hi2.
intuition.
apply NoDup_cons_iff in Hnodupvar.
rewrite NoDup_cons_iff in Hnodupvar.
constructor.
intuition.
intuition.
apply NoDup_cons_iff in Hnodupvar.
rewrite NoDup_cons_iff in Hnodupvar.
intuition.
+


 apply IHl;trivial. }
** case_eq (getMappedPage pdChildphy s' a);[intros phy Hphy| intros Hphy| intros Hphy];rewrite Hphy in *. 
{ simpl in *. 
  destruct Hmykey2 as [Hmykey2 | Hmykey2]. 
  + subst. 
  move Hva1 at bottom.
  apply NoDup_cons_iff in Htriche1 as (Htriche1 & _).
  move Htriche1 at bottom.
  move Hcheck at bottom.
  assert(Hcheckva1 : checkOffset0 va1 = true).
  { apply filter_In in Hva1.
    intuition. }
  assert(Hoffeq: checkVAddrsEqualityWOOffset nbLevel a va1
          (CLevel (nbLevel - 1)) = false).
   { apply checkVAddrsEqualityWOOffsetFalseEqOffset ;trivial. 
  apply getNbLevelEqOption.
  unfold not;intros;subst.
  now contradict Htriche1. }
  assert(Hgoal : getMappedPage pdChildphy s' a = NonePage).
{ apply getMappedPageNoneMapMMUPage'  with phyDescChild level entry;trivial.
symmetry;trivial.
rewrite negb_true_iff in *;subst;intuition.
apply checkVAddrsEqualityWOOffsetTrans with va1;trivial.
rewrite <- Hva11.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.
rewrite <- Hoffeq.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.

 }
rewrite Hgoal in Hphy.
now contradict Hphy.
+ 
  move Hva1 at bottom.
  apply NoDup_cons_iff in Htriche1 as (Htriche1 & Htriche11).
  move Htriche1 at bottom.
  move Hcheck at bottom.
  assert(Hcheckva1 : checkOffset0 va1 = true).
  { apply filter_In in Hva1.
    intuition. }
  assert(Hoffeq : checkVAddrsEqualityWOOffset nbLevel a va1
          (CLevel (nbLevel - 1)) = false).
  { apply checkVAddrsEqualityWOOffsetFalseEqOffset ;trivial. 
  apply getNbLevelEqOption.
  unfold not;intros;subst.
  now contradict Htriche1. }
assert(Hgoal : getMappedPage pdChildphy s' a = NonePage).
{ apply getMappedPageNoneMapMMUPage'  with phyDescChild level entry;trivial.
symmetry;trivial.
rewrite negb_true_iff in *;subst;intuition.
apply checkVAddrsEqualityWOOffsetTrans with va1;trivial.
rewrite <- Hva11.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.
rewrite <- Hoffeq.
f_equal.
apply getNbLevelEq;trivial.
symmetry;trivial.

 }
 
 
rewrite Hgoal in Hphy.
now contradict Hphy.  }


 
assert(Hihl: exists l1 l2 : list page,
        filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s') =
        l1 ++ phyVaChild :: l2 /\
        filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s) = l1 ++ l2).
{ apply IHl;trivial.


  simpl in *;intuition.
  apply NoDup_cons_iff in Htriche1.
  intuition. 
  apply NoDup_cons_iff in Htriche1;intuition. }
destruct Hihl as (l1 & l2 & Hl1 & Hl2).
exists l1, l2.
split;trivial.
 assert(Hihl: exists l1 l2 : list page,
        filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s') =
        l1 ++ phyVaChild :: l2 /\
        filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s) = l1 ++ l2).
{ apply IHl;trivial.
apply NoDup_cons_iff in Hnodupvar;intuition.
apply NoDup_cons_iff in Hnodupvar;intuition.

 }
destruct Hihl as (l1 & l2 & Hl1 & Hl2).
exists l1, l2.
split;trivial.
+  assert(Hihl: exists l1 l2 : list page,
        filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s') =
        l1 ++ phyVaChild :: l2 /\
        filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s) = l1 ++ l2).
{ apply IHl;trivial.

 }
destruct Hihl as (l1 & l2 & Hl1 & Hl2).
exists l1, l2.
split;trivial.
}
 

destruct Hmykey as (l1 & l2 & Hl1 & Hl2).
unfold getMappedPages in *.
rewrite Hpdpart in *.
rewrite Hpd in *.
unfold getMappedPagesAux in *.
rewrite Hl1 in *.
rewrite Hl2 in *.
apply NoDupSplitInclIff.
intuition.
apply NoDupSplit in Hnodup1;intuition.
simpl.
constructor.
rewrite in_app_iff in Hmykey4.
intuition.
apply NoDupSplit in Hnodup1;intuition.
unfold disjoint; intros x Hx.
simpl.
apply and_not_or.
split.
unfold not;intros Hfalse.
apply Hmykey4.
subst.
apply in_app_iff.
left;trivial.
unfold not;intros Hfalse.
apply NoDupSplitInclIff in Hnodup1.
destruct Hnodup1 as (_ & Hnodup1).
unfold
 disjoint in *.
 unfold not in *. 
 apply Hnodup1 with x;trivial. 

+ assert(Hinconfig : In ptVaChildpd (getConfigPages phyDescChild s)). 
  { apply isConfigTable with vaChild ;trivial.
    unfold consistency in *.
    intuition.
    intros;subst;trivial. }
  assert(Hmap : getMappedPages partition s = getMappedPages partition s').
  { apply getMappedPagesMapMMUPage with phyDescChild vaChild
    entry level;trivial.
    assert(HisoK : configTablesAreDifferent s) by trivial.
    apply HisoK;trivial.
    intuition.
    unfold consistency in *; intuition.
    intros;subst;split;trivial.
    intuition. }
   unfold getMappedPages in *. 
   rewrite Hpdpart in *.
   rewrite <- Hpd in *.
    rewrite <- Hmap;trivial.
Qed.

 Lemma  partitionsIsolationMapMMUPage s entry vaInCurrentPartition vaChild currentPart
currentShadow  idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild isnotderiv currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level r w e  :
negb presentDescPhy = false -> 
negb presentvaChild = true ->
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild (negb isnotderiv) currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level /\
StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
Some vaInCurrentPartition /\
isPartitionFalse ptVaInCurPart idxvaInCurPart s -> 
 (forall child : page, 
    In child (getChildren currentPart s) -> ~ In phyVaChild (getMappedPages child s)) -> 
partitionsIsolation {|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
unfold propagatedPropertiesAddVaddr; intuition.
assert (Hiso : partitionsIsolation s) by trivial.
unfold partitionsIsolation in *.
simpl. 
set(s':= {|  currentPartition := _ |}) in *.
intros parent child1 child2  Hparent Hchild1 Hchild2 Hdist.
assert(Hchild : In phyDescChild (getPartitions multiplexer s)).
{ unfold consistency in *.
  apply childrenPartitionInPartitionList with currentPart;intuition;subst;trivial. }
try repeat rewrite andb_true_iff in *. 

assert(Haccess : In phyVaChild (getAccessibleMappedPages currentPart s)). 
{ apply physicalPageIsAccessible
  with ptVaInCurPartpd vaInCurrentPartition idxvaInCurPart true  level true currentPD;trivial.
  intros;split;
  subst;trivial.
  intuition;subst;trivial.
  intuition;subst;trivial.
  subst;trivial.
  unfold consistency in *; unfold currentPartitionInPartitionsList in *;
  intuition; subst;trivial. }

assert(Hpart : In parent (getPartitions multiplexer s)). 
{ unfold consistency in *.
  intuition. subst.
  apply getPartitionsMapMMUPage  with  entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
  level;trivial.
  symmetry;trivial.
  intros. subst.
  split;trivial. }

assert(Hchild1s : In child1 (getChildren parent s)).
{ unfold consistency in *.
  intuition. subst.
  apply getChildrenMapMMUPage with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild
  phyDescChild level entry;trivial.
  symmetry;trivial. }

assert(Hchild2s : In child2 (getChildren parent s)).
{ unfold consistency in *.
  intuition. subst.
  apply getChildrenMapMMUPage with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild
  phyDescChild level entry;trivial.
  symmetry;trivial. }

assert(Hnotsamepart : forall part, phyDescChild <> part -> 
In part (getPartitions multiplexer s) -> 
getUsedPages part s = getUsedPages part s').
{ intros.
  apply getUsedPagesMapMMUPage with phyDescChild vaChild entry level ;trivial.
  unfold consistency in *.
  intuition.
  unfold consistency in *.
  intuition.
  split. 
  subst;trivial.
  subst;trivial. }

assert (Hcurconfig : getConfigPages phyDescChild s = getConfigPages phyDescChild s').
{ apply getConfigPagesMapMMUPage1 with entry pdChildphy
  currentPart presentvaChild vaChild level ;trivial.
  subst.
  unfold consistency in *.
  unfold currentPartitionInPartitionsList in *.
  intuition. }

assert(Hor3:  ( phyDescChild <> child1 /\ phyDescChild <> child2) \/
            (phyDescChild = child1 \/ phyDescChild = child2)).
{ clear. destruct phyDescChild;destruct child1 ; destruct child2.
  simpl in *.
  assert(  (p <> p0 /\ p <> p1) \/
  (p = p0 \/ p = p1)) by omega.
  destruct
   H. left. 
   destruct H.
   split. 
   unfold not;intros.
   inversion H1.
   subst.
   omega.
   unfold not;intros.
   inversion H1.
   subst.
   omega.
   right. 
   destruct H. 
   left. 
   subst.
   f_equal.
   apply proof_irrelevance.
   right. 
   subst;f_equal.
   apply proof_irrelevance. }
 
destruct Hor3 as [Hor3| Hor3].
+ (*phyDescChild <> child1 /\ phyDescChild <> child2 *)
 destruct Hor3 as (Hor1 & Hor2).
 assert(Hnodup :  noDupPartitionTree s).
 unfold consistency in *.
 intuition.
  rewrite <- Hnotsamepart;trivial.
  rewrite <- Hnotsamepart;trivial.
  apply Hiso with parent;trivial.
  apply childrenPartitionInPartitionList with parent;trivial.
  apply childrenPartitionInPartitionList with parent;trivial.
+ destruct Hor3 as [Hor3 | Hor3]. 
  
  - (** phyDescChild = child1 **)
    subst child1.
    assert(Huseeq : getUsedPages child2 s = getUsedPages child2 s').
    { apply Hnotsamepart;trivial.
      apply childrenPartitionInPartitionList with parent;trivial.
      unfold consistency in *.
      intuition. }
    rewrite <- Huseeq.
    clear Huseeq.
    unfold getUsedPages.
    unfold disjoint.
    intros x Hx. 
    apply in_app_iff in Hx.
    destruct Hx as [Hx | Hx].
    * (** In x (getConfigPages phyDescChild s **)
      rewrite in_app_iff.
      apply and_not_or.
      split.
      { (** ~ In x (getConfigPages child2 s) **)
        rewrite <- Hcurconfig in *.
        clear Hcurconfig.  
        assert(Hnodupconfig : configTablesAreDifferent s ).
        unfold consistency in *.
        intuition.
        unfold configTablesAreDifferent in *. 
        unfold disjoint in *. 
        apply Hnodupconfig with phyDescChild;trivial.
        apply childrenPartitionInPartitionList with parent;trivial.
        unfold consistency in *.
        intuition. }
      { (** ~ In x (getMappedPages child2 s) **)
        rewrite <- Hcurconfig in *. 
        assert(Hisogoal : ~ In x (getUsedPages child2 s)).
        unfold disjoint in Hiso.
        apply Hiso with parent phyDescChild;trivial.
        unfold getUsedPages.
        apply in_app_iff.
        left;trivial.
        unfold getUsedPages in *. 
        rewrite in_app_iff in *.
        apply not_or_and in Hisogoal.
        intuition. }
    * (** In x (getMappedPages phyDescChild s') **)
       assert(Hparentcons : isParent s).
        unfold consistency in *.
        intuition.
        assert((currentPartition s) =parent ). 
        { apply getParentNextEntryIsPPEq with phyDescChild s;
          trivial.
          apply nextEntryIsPPgetParent;trivial.
          apply Hparentcons;trivial.
          unfold consistency in *.
          unfold currentPartitionInPartitionsList in *. 
          intuition.
          apply Hparentcons;trivial. }
      assert(Hnotpresent : negb presentvaChild = true) by trivial.
      assert(Hentrypresent : entryPresentFlag ptVaChildpd idxvaChild presentvaChild s)
      by trivial.
      apply negb_true_iff in Hnotpresent.
      assert(Hlookup :lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
      Some (PE entry)) by trivial. 
      assert (Hnewpres : entryPresentFlag ptVaChildpd
                    (StateLib.getIndexOfAddr vaChild fstLevel) true s').
      { unfold s'. 
        unfold entryPresentFlag.
        cbn.
        assert(Hpairs :  beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
            (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
            beqIndex = true).
        { apply beqPairsTrue; split;trivial. }
       subst.
       rewrite Hpairs;simpl;trivial. }
      assert(HnewEntry : isEntryPage ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) phyVaChild
          s').
      { unfold s'. 
        unfold isEntryPage.
        cbn.
        assert(Hpairs :  beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
            (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
            beqIndex = true).
        { apply beqPairsTrue; split;trivial. }
       subst.
       rewrite Hpairs;simpl;trivial. }
      assert(Htrue : getMappedPage pdChildphy s vaChild = SomeDefault).
      { apply getMappedPageNotPresent with ptVaChildpd phyDescChild;intuition;
        subst;trivial. }
      assert (Hnewmap : getMappedPage pdChildphy s' vaChild = SomePage phyVaChild).
      { apply getMappedPageGetTableRoot with ptVaChildpd phyDescChild;
        trivial;fold s'. 
        + intros. 
          split. 
          apply isPEMapMMUPage with entry;trivial.
          subst;trivial.
          assert(Htblroot : getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
          unfold getTableAddrRoot in Htblroot.
          destruct Htblroot as (Hidxs & Htblroot).
          split;trivial.
          intros.
          assert(Hpdchild : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
          apply Htblroot in Hpdchild;clear Htblroot.
          move Hpdchild at bottom.
          destruct Hpdchild as (nbL & HnbL & stop & Hstop & Hind1).
          exists nbL ; split ; trivial.
          exists stop;split;trivial.
          assert(tableroot = pdChildphy). 
          apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
          apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
          phyVaChild r w  e;trivial.
          subst. trivial.
          apply nextEntryIsPPgetPd;trivial.
          subst .
          revert Hind1.
          assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
                  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some defaultPage).
          { assert(Hcons1 : isPresentNotDefaultIff s).
           unfold consistency in *. intuition.            
            apply Hcons1.
            subst.
            move Hentrypresent at bottom.
            unfold entryPresentFlag in *. 
            unfold StateLib.readPresent. 
            rewrite Hlookup in *.
            f_equal.
            rewrite Hentrypresent. trivial. }
          assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
                          (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some phyVaChild).
          { unfold StateLib.readPhyEntry. 
            cbn.
            assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
              (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
              beqIndex = true); intros.
            rewrite <- beqPairsTrue;split;trivial.
            rewrite Hpairs.
            simpl;trivial. }
          assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial. 
          revert Htrue1 Htrue2 Hlookup Hdefaut.
          clear. 
          intros. apply getIndirectionMapMMUPage with entry;trivial;subst;trivial.
        + apply nextEntryIsPPMapMMUPage with entry;trivial. } 
      assert(Hpd : StateLib.getPd phyDescChild (memory s) =
        StateLib.getPd phyDescChild (memory s')).
      { unfold s'. simpl.
        symmetry. apply getPdMapMMUPage with entry;trivial. }
      assert(Hpp : nextEntryIsPP phyDescChild PDidx pdChildphy s)
        by trivial.
      rewrite nextEntryIsPPgetPd in *.
      rewrite Hpp in *.
      unfold getMappedPages in Hx. 
      rewrite <- Hpd in *. clear Hpd.
      unfold getMappedPagesAux in *. 
      apply filterOptionInIff in Hx.
      unfold getMappedPagesOption in *. 
      apply in_map_iff in Hx.
      destruct Hx as (vax & Hvax & Hallva).
      assert(Hor : x= phyVaChild \/ x <> phyVaChild) by apply pageDecOrNot.
       destruct Hor as [Hor | Hor].
      { subst phyVaChild.
        subst.
        rewrite in_app_iff.
      apply and_not_or.
        split.
        (** ~ In x (getConfigPages child2 s) **)
        assert(Hconfigaccess : kernelDataIsolation s) by trivial.
        unfold kernelDataIsolation in *.  
        unfold disjoint in *. 
        apply Hconfigaccess with (currentPartition s);trivial.
        subst;trivial.
        unfold consistency in *.
        unfold currentPartitionInPartitionsList in *. 
        intuition.
        apply childrenPartitionInPartitionList with (currentPartition s);trivial.
        unfold consistency in *. 
        intuition.
        (** ~ In x (getMappedPages child2 s) **)
       subst.
       assert(Hi : forall child : page,
         In child (getChildren (currentPartition s) s) ->
         In x (getMappedPages child s) -> False) by trivial.
      unfold not;intros.
      apply Hi with child2;trivial.
       }
      assert(Hor1 :checkVAddrsEqualityWOOffset nbLevel vaChild vax level = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false).
      { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild vax level);intuition. }
      destruct Hor1 as [Hor1 | Hor1].
      ++ assert (Hmapsfalse : getMappedPage pdChildphy s' vaChild = 
          getMappedPage pdChildphy s' vax).
         apply getMappedPageEq with level;trivial .
         symmetry;trivial.
      rewrite <- Hmapsfalse in Hvax.
      rewrite Hnewmap in *.
      inversion Hvax;subst.
      now contradict Hor.
      ++ unfold disjoint in Hiso. 
        unfold getUsedPages in Hiso.
        apply Hiso with (currentPartition s) phyDescChild;trivial.
        unfold consistency in *.
        unfold currentPartitionInPartitionsList in *. 
        intuition.
        subst.
        trivial.
        apply in_app_iff.
        right.
        subst.
        unfold getMappedPages.
        rewrite Hpp.
        unfold getMappedPagesAux.
        apply filterOptionInIff.
        unfold getMappedPagesOption.
        apply in_map_iff.
        
        exists vax.
        split;[|trivial].
        move Hvax at bottom.
        
        
        
        
          assert(Hindchild : getIndirection pdChildphy vaChild level (nbLevel - 1) s =
  Some ptVaChildpd). 
  { apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
    symmetry;trivial.
    intros;split;trivial.
    subst;trivial. }
   rewrite <- Hvax. 
    unfold getMappedPage.
    assert(Hlevel : StateLib.getNbLevel = Some level).
    symmetry; trivial.
    rewrite Hlevel. 
    case_eq(getIndirection pdChildphy vax level (nbLevel - 1) s );intros.

assert(Hii:   getIndirection pdChildphy vax level (nbLevel - 1) s' = Some p).

{ unfold consistency in *. intuition.
apply getIndirectionMapMMUPage2
with (currentPartition s) false vaChild phyDescChild entry;trivial.
apply nextEntryIsPPgetPd;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply nextEntryIsPPgetPd;trivial.
}
rewrite Hii.
   assert(Hnodupconf : noDupConfigPagesList s).
    unfold consistency in *. 
    intuition.
  case_eq(defaultPage =? p);intros Hnotdef;trivial.  
   assert(ptVaChildpd <> p \/ (StateLib.getIndexOfAddr vaChild fstLevel) <> 
  (StateLib.getIndexOfAddr vax fstLevel)).
   apply pageTablesOrIndicesAreDifferent with pdChildphy pdChildphy
    level nbLevel s;trivial.
    apply pdPartNotNull with phyDescChild s;trivial.
    apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
    apply pdPartNotNull with phyDescChild s;trivial.
     apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
   apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.
unfold noDupConfigPagesList in *.
  apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial. 

  left.
  split;trivial.
  apply getNbLevelEq.
  symmetry;trivial.
  assert(Hdefaut: (defaultPage =? ptVaChildpd) = false) by trivial.
    apply beq_nat_false in Hdefaut.
    unfold not;intros;subst;now contradict Hdefaut.
  apply beq_nat_false in Hnotdef.
  unfold not;intros;subst;trivial.
  now contradict Hnotdef.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s)
 = StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s')). 
 apply readPresentMapMMUPage with entry;trivial.
 intuition.
 rewrite <- Hpres.
 case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s));intros.
 destruct b;trivial.
 symmetry.
 assert(Heq : StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s')=
  StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s)).
  symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 intuition.
 rewrite Heq.
 trivial.
 trivial.
 assert(Hnone : getIndirection pdChildphy vax level (nbLevel - 1) s' = None).
 unfold consistency in *.
 intuition.
 apply getIndirectionNoneMapMMUPage2 with (currentPartition s) false vaChild phyDescChild entry;trivial.
apply nextEntryIsPPgetPd;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply nextEntryIsPPgetPd;trivial.
rewrite Hnone;trivial.
- (** phyDescChild = child2 **)
    subst child2.
    apply disjointPermut.
    assert(Huseeq : getUsedPages child1 s = getUsedPages child1 s').
    { apply Hnotsamepart;trivial.
      intuition.
      apply childrenPartitionInPartitionList with parent;trivial.
      unfold consistency in *.
      intuition. }
    rewrite <- Huseeq.
    clear Huseeq.
    unfold getUsedPages.
    unfold disjoint.
    intros x Hx. 
    apply in_app_iff in Hx.
    destruct Hx as [Hx | Hx].
    * (** In x (getConfigPages phyDescChild s **)
      rewrite in_app_iff.
      apply and_not_or.
      split.
      { (** ~ In x (getConfigPages child1 s) **)
        rewrite <- Hcurconfig in *.
        clear Hcurconfig.  
        assert(Hnodupconfig : configTablesAreDifferent s ).
        unfold consistency in *.
        intuition.
        unfold configTablesAreDifferent in *. 
        unfold disjoint in *. 
        apply Hnodupconfig with phyDescChild;trivial.
        apply childrenPartitionInPartitionList with parent;trivial.
        unfold consistency in *.
        intuition.
        intuition. }
      { (** ~ In x (getMappedPages child1 s) **)
        rewrite <- Hcurconfig in *. 
        assert(Hisogoal : ~ In x (getUsedPages child1 s)).
        unfold disjoint in Hiso.
        apply Hiso with parent phyDescChild;trivial.
        intuition.
        unfold getUsedPages.
        apply in_app_iff.
        left;trivial.
        unfold getUsedPages in *. 
        rewrite in_app_iff in *.
        apply not_or_and in Hisogoal.
        intuition. }
    * (** In x (getMappedPages phyDescChild s') **)
       assert(Hparentcons : isParent s).
        unfold consistency in *.
        intuition.
        assert((currentPartition s) =parent ). 
        { apply getParentNextEntryIsPPEq with phyDescChild s;
          trivial.
          apply nextEntryIsPPgetParent;trivial.
          apply Hparentcons;trivial.
          unfold consistency in *.
          unfold currentPartitionInPartitionsList in *. 
          intuition.
          apply Hparentcons;trivial. }
      assert(Hnotpresent : negb presentvaChild = true) by trivial.
      assert(Hentrypresent : entryPresentFlag ptVaChildpd idxvaChild presentvaChild s)
      by trivial.
      apply negb_true_iff in Hnotpresent.
      assert(Hlookup :lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
      Some (PE entry)) by trivial. 
      assert (Hnewpres : entryPresentFlag ptVaChildpd
                    (StateLib.getIndexOfAddr vaChild fstLevel) true s').
      { unfold s'. 
        unfold entryPresentFlag.
        cbn.
        assert(Hpairs :  beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
            (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
            beqIndex = true).
        { apply beqPairsTrue; split;trivial. }
       subst.
       rewrite Hpairs;simpl;trivial. }
      assert(HnewEntry : isEntryPage ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) phyVaChild
          s').
      { unfold s'. 
        unfold isEntryPage.
        cbn.
        assert(Hpairs :  beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
            (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
            beqIndex = true).
        { apply beqPairsTrue; split;trivial. }
       subst.
       rewrite Hpairs;simpl;trivial. }
      assert(Htrue : getMappedPage pdChildphy s vaChild = SomeDefault).
      { apply getMappedPageNotPresent with ptVaChildpd phyDescChild;intuition;
        subst;trivial. }
      assert (Hnewmap : getMappedPage pdChildphy s' vaChild = SomePage phyVaChild).
      { apply getMappedPageGetTableRoot with ptVaChildpd phyDescChild;
        trivial;fold s'. 
        + intros. 
          split. 
          apply isPEMapMMUPage with entry;trivial.
          subst;trivial.
          assert(Htblroot : getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
          unfold getTableAddrRoot in Htblroot.
          destruct Htblroot as (Hidxs & Htblroot).
          split;trivial.
          intros.
          assert(Hpdchild : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
          apply Htblroot in Hpdchild;clear Htblroot.
          move Hpdchild at bottom.
          destruct Hpdchild as (nbL & HnbL & stop & Hstop & Hind1).
          exists nbL ; split ; trivial.
          exists stop;split;trivial.
          assert(tableroot = pdChildphy). 
          apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
          apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
          phyVaChild r w  e;trivial.
          subst. trivial.
          apply nextEntryIsPPgetPd;trivial.
          subst .
          revert Hind1.
          assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
                  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some defaultPage).
          { assert(Hcons1 : isPresentNotDefaultIff s).
           unfold consistency in *. intuition.            
            apply Hcons1.
            subst.
            move Hentrypresent at bottom.
            unfold entryPresentFlag in *. 
            unfold StateLib.readPresent. 
            rewrite Hlookup in *.
            f_equal.
            rewrite Hentrypresent. trivial. }
          assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
                          (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some phyVaChild).
          { unfold StateLib.readPhyEntry. 
            cbn.
            assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
              (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
              beqIndex = true); intros.
            rewrite <- beqPairsTrue;split;trivial.
            rewrite Hpairs.
            simpl;trivial. }
          assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial. 
          revert Htrue1 Htrue2 Hlookup Hdefaut.
          clear. 
          intros. apply getIndirectionMapMMUPage with entry;trivial;subst;trivial.
        + apply nextEntryIsPPMapMMUPage with entry;trivial. } 
      assert(Hpd : StateLib.getPd phyDescChild (memory s) =
        StateLib.getPd phyDescChild (memory s')).
      { unfold s'. simpl.
        symmetry. apply getPdMapMMUPage with entry;trivial. }
      assert(Hpp : nextEntryIsPP phyDescChild PDidx pdChildphy s)
        by trivial.
      rewrite nextEntryIsPPgetPd in *.
      rewrite Hpp in *.
      unfold getMappedPages in Hx. 
      rewrite <- Hpd in *. clear Hpd.
      unfold getMappedPagesAux in *. 
      apply filterOptionInIff in Hx.
      unfold getMappedPagesOption in *. 
      apply in_map_iff in Hx.
      destruct Hx as (vax & Hvax & Hallva).
      assert(Hor : x= phyVaChild \/ x <> phyVaChild) by apply pageDecOrNot.
       destruct Hor as [Hor | Hor].
      { subst phyVaChild.
        subst.
        rewrite in_app_iff.
      apply and_not_or.
        split.
        (** ~ In x (getConfigPages child1 s) **)
        assert(Hconfigaccess : kernelDataIsolation s) by trivial.
        unfold kernelDataIsolation in *.  
        unfold disjoint in *. 
        apply Hconfigaccess with (currentPartition s);trivial.
        subst;trivial.
        unfold consistency in *.
        unfold currentPartitionInPartitionsList in *. 
        intuition.
        apply childrenPartitionInPartitionList with (currentPartition s);trivial.
        unfold consistency in *. 
        intuition.
        (** ~ In x (getMappedPages child1 s) **)
       subst.
       assert(Hi : forall child : page,
       
         In child (getChildren (currentPartition s) s) ->
         In x (getMappedPages child s) -> False) by trivial.
      unfold not;intros.
      apply Hi with child1;trivial.
       }
      assert(Hor1 :checkVAddrsEqualityWOOffset nbLevel vaChild vax level = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false).
      { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild vax level);intuition. }
      destruct Hor1 as [Hor1 | Hor1].
      ++ assert (Hmapsfalse : getMappedPage pdChildphy s' vaChild = 
          getMappedPage pdChildphy s' vax).
         apply getMappedPageEq with level;trivial .
         symmetry;trivial.
      rewrite <- Hmapsfalse in Hvax.
      rewrite Hnewmap in *.
      inversion Hvax;subst.
      now contradict Hor.
      ++ unfold disjoint in Hiso. 
        unfold getUsedPages in Hiso.
        apply Hiso with (currentPartition s) phyDescChild;trivial.
        unfold consistency in *.
        unfold currentPartitionInPartitionsList in *. 
        intuition.
        subst.
        trivial.
        intuition.
        apply in_app_iff.
        right.
        subst.
        unfold getMappedPages.
        rewrite Hpp.
        unfold getMappedPagesAux.
        apply filterOptionInIff.
        unfold getMappedPagesOption.
        apply in_map_iff.
        exists vax.
        split;[| trivial].
        move Hvax at bottom.
          assert(Hindchild : getIndirection pdChildphy vaChild level (nbLevel - 1) s =
  Some ptVaChildpd). 
  { apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
    symmetry;trivial.
    intros;split;trivial.
    subst;trivial. }
   rewrite <- Hvax. 
    unfold getMappedPage.
    assert(Hlevel : StateLib.getNbLevel = Some level).
    symmetry; trivial.
    rewrite Hlevel. 
    case_eq(getIndirection pdChildphy vax level (nbLevel - 1) s );intros.

assert(Hii:   getIndirection pdChildphy vax level (nbLevel - 1) s' = Some p).

{ unfold consistency in *. intuition.
apply getIndirectionMapMMUPage2
with (currentPartition s) false vaChild phyDescChild entry;trivial.
apply nextEntryIsPPgetPd;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply nextEntryIsPPgetPd;trivial.
}
rewrite Hii.
   assert(Hnodupconf : noDupConfigPagesList s).
    unfold consistency in *. 
    intuition.
  case_eq(defaultPage =? p);intros Hnotdef;trivial.  
   assert(ptVaChildpd <> p \/ (StateLib.getIndexOfAddr vaChild fstLevel) <> 
  (StateLib.getIndexOfAddr vax fstLevel)).
   apply pageTablesOrIndicesAreDifferent with pdChildphy pdChildphy
    level nbLevel s;trivial.
    apply pdPartNotNull with phyDescChild s;trivial.
    apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
    apply pdPartNotNull with phyDescChild s;trivial.
     apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *. intuition.
   apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.
   apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
         unfold consistency in *;intuition.
         unfold consistency in *;intuition.
left;trivial.
 apply nextEntryIsPPgetPd;trivial.

  left.
  split;trivial.
  apply getNbLevelEq.
  symmetry;trivial.
  assert(Hdefaut: (defaultPage =? ptVaChildpd) = false) by trivial.
    apply beq_nat_false in Hdefaut.
    unfold not;intros;subst;now contradict Hdefaut.
  apply beq_nat_false in Hnotdef.
  unfold not;intros;subst;trivial.
  now contradict Hnotdef.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s)
 = StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s')). 
 apply readPresentMapMMUPage with entry;trivial.
 intuition.
 rewrite <- Hpres.
 case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr vax fstLevel) (memory s));intros.
 destruct b;trivial.
 symmetry.
 assert(Heq : StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s')=
  StateLib.readPhyEntry p (StateLib.getIndexOfAddr vax fstLevel) (memory s)).
  symmetry.
 apply readPhyEntryMapMMUPage with entry;trivial.
 intuition.
 rewrite Heq.
 trivial.
 trivial.
 assert(Hnone : getIndirection pdChildphy vax level (nbLevel - 1) s' = None).
 unfold consistency in *.
 intuition.
 apply getIndirectionNoneMapMMUPage2 with (currentPartition s) false vaChild phyDescChild entry;trivial.
apply nextEntryIsPPgetPd;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply nextEntryIsPPgetPd;trivial.
rewrite Hnone;trivial.

Qed.

 Lemma  kernelDataIsolationMapMMUPage s entry vaInCurrentPartition vaChild currentPart
currentShadow  idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild isnotderiv currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level r w e  :
negb presentDescPhy = false -> 
negb presentvaChild = true ->
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild (negb isnotderiv) currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level /\
StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
Some vaInCurrentPartition /\
isPartitionFalse ptVaInCurPart idxvaInCurPart s -> 
 (forall child : page, 
    In child (getChildren currentPart s) -> ~ In phyVaChild (getMappedPages child s)) -> 
kernelDataIsolation {|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
unfold propagatedPropertiesAddVaddr; intuition.
assert (Hiso : kernelDataIsolation s) by trivial.
unfold partitionsIsolation in *.
simpl. 
set(s':= {|  currentPartition := _ |}) in *.
unfold kernelDataIsolation in *.
intros partition1 partition2  Hpart1 Hpart2 .
assert(Hcurpart : In (currentPartition s) (getPartitions multiplexer s)).
{ unfold consistency in *. 
  unfold currentPartitionInPartitionsList in *.
  intuition. }

assert(Hchild : In phyDescChild (getPartitions multiplexer s)).
{ unfold consistency in *.
  apply childrenPartitionInPartitionList with currentPart;intuition;subst;trivial. }
  try repeat rewrite andb_true_iff in *. 
assert(Haccess : In phyVaChild (getAccessibleMappedPages currentPart s)). 
{ apply physicalPageIsAccessible
   with ptVaInCurPartpd vaInCurrentPartition idxvaInCurPart true  level true currentPD;trivial.
  intros;split;
  subst;trivial.
  intuition;subst;trivial.
  intuition;subst;trivial.
  subst;trivial.
  unfold consistency in *; unfold currentPartitionInPartitionsList in *;
  intuition; subst;trivial. }

assert(Hpart1mult : In partition1 (getPartitions multiplexer s)). 
{ unfold consistency in *.
  intuition. subst.
  apply getPartitionsMapMMUPage  with  entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
  level;trivial.
  symmetry;trivial.
  intros. subst.
  split;trivial. }

assert(Hpart2mult : In partition2 (getPartitions multiplexer s)). 
{ unfold consistency in *.
  intuition. subst.
  apply getPartitionsMapMMUPage  with  entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
  level;trivial.
  symmetry;trivial.
  intros. subst.
  split;trivial. }

assert(Hinconfig : In ptVaChildpd (getConfigPages phyDescChild s)). 
{ apply isConfigTable with vaChild ;trivial.
  unfold consistency in *.
  intuition.
  intros;subst;split;trivial. }

assert(Hor3:  
( phyDescChild <> partition1 /\ phyDescChild <> partition2) \/
  (phyDescChild = partition1 \/ phyDescChild = partition2)).
{ clear. destruct phyDescChild;destruct partition1 ; destruct partition2.
  simpl in *.
  assert(  (p <> p0 /\ p <> p1) \/
  (p = p0 \/ p = p1)) by omega.
  destruct H. left. 
  destruct H.
  split. 
  unfold not;intros.
  inversion H1.
  subst.
  omega.
  unfold not;intros.
  inversion H1.
  subst.
  omega.
  right. 
  destruct H. 
  left. 
  subst.
  f_equal.
  apply proof_irrelevance.
  right. 
  subst;f_equal.
  apply proof_irrelevance. }
assert(Hconfigdiff : configTablesAreDifferent s).
{ unfold consistency in *. intuition. } 

assert(Hlookup : lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
     Some (PE entry)) by trivial.

assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
          (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some defaultPage).
{ assert(Hcons1 : isPresentNotDefaultIff s).
  unfold consistency in *. intuition.            
  apply Hcons1.
  subst.
  unfold entryPresentFlag in *. 
  unfold StateLib.readPresent.
  rewrite Hlookup in *.
  f_equal.
  subst.
  assert (Hentrypresent : negb (present entry) = true) by trivial.
  apply negb_true_iff in Hentrypresent.
  subst. trivial. }

assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
              (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some phyVaChild).
{ unfold StateLib.readPhyEntry. 
  cbn.
  assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
  (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
  beqIndex = true); intros.
  rewrite <- beqPairsTrue;split;trivial.
  subst.
  rewrite Hpairs.
  simpl;trivial. }

assert (Hnewmap1 : getMappedPage pdChildphy s' vaChild = SomePage phyVaChild).
{ apply getMappedPageGetTableRoot with ptVaChildpd phyDescChild;
  trivial;fold s'. 
  + intros. 
  split. 
  apply isPEMapMMUPage with entry;trivial.
  subst;trivial.
  assert(Htblroot : getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
  unfold getTableAddrRoot in Htblroot.
  destruct Htblroot as (Hidxs & Htblroot).
  split;trivial.
  intros.
  assert(Hpdchild : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Htblroot in Hpdchild;clear Htblroot.
  move Hpdchild at bottom.
  destruct Hpdchild as (nbL & HnbL & stop & Hstop & Hind1).
  exists nbL ; split ; trivial.
  exists stop;split;trivial.
  assert(tableroot = pdChildphy). 
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  phyVaChild r w  e;trivial.
  subst. trivial.
  apply nextEntryIsPPgetPd;trivial.
  subst .
  revert Hind1.
 
  assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial. 
  revert Htrue1 Htrue2 Hlookup Hdefaut.
  clear. 
  intros.
   apply getIndirectionMapMMUPage with entry;trivial;subst;trivial.
 + unfold isEntryPage, StateLib.readPhyEntry in *. 
   destruct(lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
             (memory s') beqPage beqIndex);trivial;try now contradict Htrue2.
   destruct v;try now contradict Htrue2.
   inversion Htrue2;trivial.
 + unfold entryPresentFlag. 
   cbn.
   subst.
   assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
      beqIndex = true).
   apply beqPairsTrue;split;trivial.
   rewrite Hpairs.
   simpl;trivial.
       
+ apply  nextEntryIsPPMapMMUPage with entry;trivial. } 

assert(Hindchild : getIndirection pdChildphy vaChild level (nbLevel - 1) s =
      Some ptVaChildpd). 
{ apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
  rewrite nextEntryIsPPgetPd in *. 
 trivial.
 symmetry;trivial.
  intros;split;trivial.
  subst;trivial. }

assert(Hindchild' :  getIndirection pdChildphy vaChild level (nbLevel - 1) s' =
  Some ptVaChildpd). 
{ unfold s'.
  subst.
  apply getIndirectionMapMMUPage3 with entry;trivial. }

assert (Hnewmap :getAccessibleMappedPage pdChildphy s' vaChild = SomePage phyVaChild).
{ assert(Hlevel : Some level = StateLib.getNbLevel ) by trivial.
  revert Hnewmap1 Hindchild' Hlevel.
  subst.
  clear.
  unfold  getMappedPage, getAccessibleMappedPage. 
  intros.
  rewrite <- Hlevel in *.
  rewrite Hindchild' in *.
  destruct(defaultPage =? ptVaChildpd);try now contradict Hnewmap1.
  destruct ( StateLib.readPresent ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  (memory s'));try now contradict Hnewmap1. 
  destruct b;try now contradict Hnewmap1.
  unfold StateLib.readAccessible. 
  cbn.
  assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
  (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
  beqIndex = true).
  { apply beqPairsTrue;split;trivial. }
  rewrite Hpairs.
  simpl. trivial. }

assert(Hconfig :forall part, In part (getPartitions multiplexer s) -> 
     getConfigPages part s = getConfigPages part s').
{ intros. assert (Hor : phyDescChild = part \/ 
    phyDescChild <> part) by apply pageDecOrNot.
  destruct Hor as [Hor | Hor].
  subst.
  + apply getConfigPagesMapMMUPage1 with entry pdChildphy
    (currentPartition s)  presentvaChild vaChild level;trivial.
  + apply getConfigPagesMapMMUPage with phyDescChild entry;trivial.
    apply Hconfigdiff;trivial. }
destruct Hor3 as [Hor3| Hor3].
+ (*phyDescChild <> partition1 /\ phyDescChild <> partition2 *)
  destruct Hor3 as (Hor1 & Hor2).
(*   assert(Hconfig : getConfigPages partition2 s = getConfigPages partition2 s').
  { apply getConfigPagesMapMMUPage with phyDescChild entry;trivial.
    apply Hconfigdiff;trivial. } *)
  rewrite <- Hconfig;trivial.
  unfold consistency in *.
  assert(Hmaps: getAccessibleMappedPages partition1 s =
        getAccessibleMappedPages partition1 s').
  { apply getAccessibleMappedPagesMapMMUPage with phyDescChild vaChild
      entry level;intuition.    
    subst.
    intuition. }
  rewrite <- Hmaps. clear Hmaps.
  apply Hiso;trivial.
+ destruct Hor3 as [Hor3 | Hor3]. 
  - (** phyDescChild = partition1 **)
    subst partition1.
    rewrite <- Hconfig;trivial.
    unfold disjoint;intros x Hx.
    assert(Hmykey : x = phyVaChild  \/ x <> phyVaChild) by apply pageDecOrNot.
    destruct Hmykey as [Hmykey | Hmykey].
    * subst phyVaChild.
      unfold disjoint in Hiso.
      apply Hiso with currentPart;trivial.
      subst;trivial.
    * assert(In x (getAccessibleMappedPages phyDescChild s)).
      { unfold getAccessibleMappedPages in *.
      assert(Hpd : StateLib.getPd phyDescChild (memory s) =
              StateLib.getPd phyDescChild (memory s')).
      { unfold s'. simpl.
        symmetry. apply getPdMapMMUPage with entry;trivial. }
      rewrite  nextEntryIsPPgetPd in *.
      rewrite <- Hpd in *.
      assert(Hpp : StateLib.getPd phyDescChild (memory s) = Some pdChildphy);trivial.
      rewrite Hpp in *.
      unfold getAccessibleMappedPagesAux in *.
      apply filterOptionInIff in Hx.
      apply filterOptionInIff.
      unfold getAccessibleMappedPagesOption in *.
      apply in_map_iff in Hx.
      apply in_map_iff.
      destruct Hx as (vax & Hvax & Hva).
      exists vax;split;trivial.
      assert(Hor1 :checkVAddrsEqualityWOOffset nbLevel vaChild vax level = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false).
      { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild vax level);intuition. }
      destruct Hor1 as [Hor1 | Hor1].
      ++ assert (Hmapsfalse : getAccessibleMappedPage pdChildphy s' vaChild = 
          getAccessibleMappedPage pdChildphy s' vax).
         apply getAccessibleMappedPageEq with level;trivial .
         symmetry;trivial.
        rewrite <- Hmapsfalse in Hvax.
        clear Hconfig.     
        rewrite Hnewmap in *.
        inversion Hvax;subst.
        now contradict Hmykey.
      ++ unfold disjoint in Hiso.
        subst.
        apply getAccessibleMappedPageMapMMUPage with phyVaChild ptVaChildpd
          r w e vaChild phyDescChild level entry;trivial.
        rewrite negb_true_iff in *. 
        subst;trivial. }
      unfold disjoint in *.
      apply Hiso with phyDescChild;trivial.
  - (** phyDescChild = partition2 **)
    subst partition2.   
    rewrite <- Hconfig in *;trivial.
    assert(Hor2 : partition1 = phyDescChild \/ partition1 <> phyDescChild) by apply pageDecOrNot.
    destruct Hor2 as [Hor2 | Hor2].
    * subst.
      unfold disjoint;intros x Hx.
      assert(Hmykey : x = phyVaChild  \/ x <> phyVaChild) by apply pageDecOrNot.
    destruct Hmykey as [Hmykey | Hmykey].
    ++ subst phyVaChild.
      unfold disjoint in Hiso.
      apply Hiso with (currentPartition s);trivial.
    ++ assert(In x (getAccessibleMappedPages phyDescChild s)).
      { unfold getAccessibleMappedPages in *.
      assert(Hpd : StateLib.getPd phyDescChild (memory s) =
              StateLib.getPd phyDescChild (memory s')).
      { unfold s'. simpl.
        symmetry. apply getPdMapMMUPage with entry;trivial. }
      rewrite  nextEntryIsPPgetPd in *.
      rewrite <- Hpd in *.
      assert(Hpp : StateLib.getPd phyDescChild (memory s) = Some pdChildphy);trivial.
      rewrite Hpp in *.
      unfold getAccessibleMappedPagesAux in *.
      apply filterOptionInIff in Hx.
      apply filterOptionInIff.
      unfold getAccessibleMappedPagesOption in *.
      apply in_map_iff in Hx.
      apply in_map_iff.
      destruct Hx as (vax & Hvax & Hva).
      exists vax;split;trivial.
      assert(Hor1 :checkVAddrsEqualityWOOffset nbLevel vaChild vax level = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false).
      { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild vax level);intuition. }
      destruct Hor1 as [Hor1 | Hor1].
      ++ assert (Hmapsfalse : getAccessibleMappedPage pdChildphy s' vaChild = 
          getAccessibleMappedPage pdChildphy s' vax).
         apply getAccessibleMappedPageEq with level;trivial .
         symmetry;trivial.
        rewrite <- Hmapsfalse in Hvax.
        clear Hconfig.     
        rewrite Hnewmap in *.
        inversion Hvax;subst.
        now contradict Hmykey.
      ++ unfold disjoint in Hiso.
        subst.
        apply getAccessibleMappedPageMapMMUPage with phyVaChild ptVaChildpd
          r w e vaChild phyDescChild level entry;trivial.
        rewrite negb_true_iff in *. 
        subst;trivial. }
      unfold disjoint in *.
      apply Hiso with phyDescChild;trivial.
  * assert(Haccesseq : getAccessibleMappedPages partition1 s =
      getAccessibleMappedPages partition1 s').
    { subst.
      unfold consistency in *.
      intuition.
      apply getAccessibleMappedPagesMapMMUPage with phyDescChild vaChild
      entry level;trivial.
      apply Hconfigdiff;trivial.
      intuition.
      intros;split;subst;trivial.
      intuition. }
    rewrite <- Haccesseq.
    apply Hiso;trivial.
Qed.

 Lemma  verticalSharingMapMMUPage s entry vaInCurrentPartition vaChild currentPart
currentShadow  idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild isnotderiv currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level r w e  :
negb presentDescPhy = false -> 
negb presentvaChild = true ->
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild (negb isnotderiv) currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level /\
StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
Some vaInCurrentPartition /\
isPartitionFalse ptVaInCurPart idxvaInCurPart s -> 
 (forall child : page, 
    In child (getChildren currentPart s) -> ~ In phyVaChild (getMappedPages child s)) -> 
verticalSharing {|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros.
unfold propagatedPropertiesAddVaddr in *.
intuition.
assert (Hvs : verticalSharing s) by trivial.
unfold verticalSharing in *.
intros parent child Hvs1 Hvs2.
assert(Hcurpart : In (currentPartition s) (getPartitions multiplexer s)).
{ unfold consistency in *. 
  unfold currentPartitionInPartitionsList in *.
  intuition. }

assert(Hchild : In phyDescChild (getPartitions multiplexer s)).
{ unfold consistency in *.
  apply childrenPartitionInPartitionList with currentPart;intuition;subst;trivial. }
  
  try repeat rewrite andb_true_iff in *. 
assert(Haccess : In phyVaChild (getAccessibleMappedPages currentPart s)). 
{ apply physicalPageIsAccessible
   with ptVaInCurPartpd vaInCurrentPartition idxvaInCurPart true  level true currentPD;trivial.
  intros;split;
  subst;trivial.
  intuition;subst;trivial.
  intuition;subst;trivial.
  subst;trivial.
  unfold consistency in *; unfold currentPartitionInPartitionsList in *;
  intuition; subst;trivial. }

assert(Hparentmult : In parent (getPartitions multiplexer s)). 
{ unfold consistency in *.
  intuition. subst.
  apply getPartitionsMapMMUPage  with  entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
  level;trivial.
  symmetry;trivial.
  intros. subst.
  split;trivial. }

assert(Hchild1s : In child (getChildren parent s)).
{ unfold consistency in *.
  intuition. subst.
  apply getChildrenMapMMUPage with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild
  phyDescChild level entry;trivial.
  symmetry;trivial. }


assert(Hinconfig : In ptVaChildpd (getConfigPages phyDescChild s)). 
{ apply isConfigTable with vaChild ;trivial.
  unfold consistency in *.
  intuition.
  intros;subst;split;trivial. }

assert(Hconfigdiff : configTablesAreDifferent s).
{ unfold consistency in *. intuition. } 

assert(Hlookup : lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
     Some (PE entry)) by trivial.

assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
          (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some defaultPage).
{ assert(Hcons1 : isPresentNotDefaultIff s).
  unfold consistency in *. intuition.            
  apply Hcons1.
  subst.
  unfold entryPresentFlag in *. 
  unfold StateLib.readPresent.
  rewrite Hlookup in *.
  f_equal.
  subst.
  assert (Hentrypresent : negb (present entry) = true) by trivial.
  apply negb_true_iff in Hentrypresent.
  subst. trivial. }

assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
              (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some phyVaChild).
{ unfold StateLib.readPhyEntry. 
  cbn.
  assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
  (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
  beqIndex = true); intros.
  rewrite <- beqPairsTrue;split;trivial.
  subst.
  rewrite Hpairs.
  simpl;trivial. }

assert (Hcurconfig : getConfigPages phyDescChild s = getConfigPages phyDescChild s').
{ apply getConfigPagesMapMMUPage1 with entry pdChildphy
  currentPart presentvaChild vaChild level ;trivial.
  subst.
  unfold consistency in *.
  unfold currentPartitionInPartitionsList in *.
  intuition. }

assert(Hor3:  
( phyDescChild <> child /\ phyDescChild <> parent) \/
  (phyDescChild = child \/ phyDescChild = parent)).
{ clear. destruct phyDescChild;destruct child ; destruct parent.
  simpl in *.
  assert(  (p <> p0 /\ p <> p1) \/
  (p = p0 \/ p = p1)) by omega.
  destruct H. left. 
  destruct H.
  split. 
  unfold not;intros.
  inversion H1.
  subst.
  omega.
  unfold not;intros.
  inversion H1.
  subst.
  omega.
  right. 
  destruct H. 
  left. 
  subst.
  f_equal.
  apply proof_irrelevance.
  right. 
  subst;f_equal.
  apply proof_irrelevance. }

assert(Hisparent : isParent s) by (unfold consistency in *; intuition).

assert (Hnewmap : getMappedPage pdChildphy s' vaChild = SomePage phyVaChild).
{ apply getMappedPageGetTableRoot with ptVaChildpd phyDescChild;
  trivial;fold s'. 
  + intros. 
  split. 
  apply isPEMapMMUPage with entry;trivial.
  subst;trivial.
  assert(Htblroot : getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
  unfold getTableAddrRoot in Htblroot.
  destruct Htblroot as (Hidxs & Htblroot).
  split;trivial.
  intros.
  assert(Hpdchild : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Htblroot in Hpdchild;clear Htblroot.
  move Hpdchild at bottom.
  destruct Hpdchild as (nbL & HnbL & stop & Hstop & Hind1).
  exists nbL ; split ; trivial.
  exists stop;split;trivial.
  assert(tableroot = pdChildphy). 
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  phyVaChild r w  e;trivial.
  subst. trivial.
  apply nextEntryIsPPgetPd;trivial.
  subst .
  revert Hind1.
 
  assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial. 
  revert Htrue1 Htrue2 Hlookup Hdefaut.
  clear. 
  intros.
   apply getIndirectionMapMMUPage with entry;trivial;subst;trivial.
 + unfold isEntryPage, StateLib.readPhyEntry in *. 
   destruct(lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
             (memory s') beqPage beqIndex);trivial;try now contradict Htrue2.
   destruct v;try now contradict Htrue2.
   inversion Htrue2;trivial.
 + unfold entryPresentFlag. 
   cbn.
   subst.
   assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
      beqIndex = true).
   apply beqPairsTrue;split;trivial.
   rewrite Hpairs.
   simpl;trivial.
       
+ apply  nextEntryIsPPMapMMUPage with entry;trivial. } 

destruct Hor3 as [Hor3| Hor3].
+ (** phyDescChild <> child /\ phyDescChild <> parent **)
  destruct Hor3 as (Hor1 & Hor2).
  unfold consistency in *. intuition.
  assert(Hused : getUsedPages child s' = getUsedPages child s). 
  { symmetry. 
    apply getUsedPagesMapMMUPage with phyDescChild vaChild entry level;trivial.
    unfold consistency in *.
    intros;subst;split;trivial.
    apply childrenPartitionInPartitionList with parent;trivial. }
  rewrite Hused. clear Hused.
  assert(Hmap : getMappedPages parent s = getMappedPages parent s').
  { apply getMappedPagesMapMMUPage with phyDescChild vaChild
      entry level;trivial.
    assert(HisoK : configTablesAreDifferent s) by trivial.
    apply HisoK;trivial.
    intros;subst;split;trivial. }
  rewrite <- Hmap.
  apply Hvs;trivial.
+ 
  destruct Hor3 as [Hor3 | Hor3]. 
  - (** phyDescChild = child **) 
    subst child.
    assert(Htrue : parent <> phyDescChild).
    { assert(Hparent : StateLib.getParent phyDescChild (memory s) = Some parent)by
      (apply Hisparent;trivial).
      assert (Hisances : In parent (getAncestors phyDescChild s)) by(
      unfold getAncestors;destruct nbPage;simpl;rewrite Hparent;simpl
      ;left;trivial).
      assert(Hnocycle : noCycleInPartitionTree s) by 
      (unfold consistency in *; intuition).
      apply Hnocycle;trivial. }
    assert(Hmap : getMappedPages parent s = getMappedPages parent s').
    { apply getMappedPagesMapMMUPage with phyDescChild vaChild
      entry level;trivial.
      assert(HisoK : configTablesAreDifferent s) by trivial.
      apply HisoK;trivial.
      intuition.
      unfold consistency in *; intuition.
      intros;subst;split;trivial.
      intuition. }
    rewrite <- Hmap.
    unfold incl.
    intros x Hx.
    assert (Hvs' : incl (getUsedPages phyDescChild s) (getMappedPages parent s))by
    (apply Hvs;trivial).  
    unfold incl in *. 
    unfold getUsedPages in *. 
    assert(Hmykey : x = phyVaChild  \/ x <> phyVaChild) by apply pageDecOrNot.
    destruct Hmykey as [Hmykey | Hmykey].
    * subst phyVaChild.
      assert((currentPartition s) =parent ). 
      { apply getParentNextEntryIsPPEq with phyDescChild s;
        trivial.
        apply nextEntryIsPPgetParent;trivial.
        apply Hisparent;trivial.
        unfold consistency in *.
        unfold currentPartitionInPartitionsList in *. 
        intuition. }
      subst.
      apply accessibleMappedPagesInMappedPages;trivial.
    * apply Hvs';trivial.
      apply in_app_iff in Hx.
      apply in_app_iff.
      destruct Hx as [Hx | Hx].
      ++ left. rewrite Hcurconfig in *;trivial.
      ++ right.
      unfold getMappedPages in *.
      assert(Hpd : StateLib.getPd phyDescChild (memory s) =
              StateLib.getPd phyDescChild (memory s')).
      { unfold s'. simpl.
        symmetry. apply getPdMapMMUPage with entry;trivial. }
      rewrite  nextEntryIsPPgetPd in *.
      rewrite <- Hpd in *.
      assert(Hpp : StateLib.getPd phyDescChild (memory s) = Some pdChildphy);trivial.
      rewrite Hpp in *.
      unfold getMappedPagesAux in *.
      apply filterOptionInIff in Hx.
      apply filterOptionInIff.
      unfold getMappedPagesOption in *.
      apply in_map_iff in Hx.
      apply in_map_iff.
      destruct Hx as (vax & Hvax & Hva).
      exists vax;split;trivial.
      assert(Hor1 :checkVAddrsEqualityWOOffset nbLevel vaChild vax level = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false).
      { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild vax level);intuition. }
      destruct Hor1 as [Hor1 | Hor1].
      -- assert (Hmapsfalse : getMappedPage pdChildphy s' vaChild = 
          getMappedPage pdChildphy s' vax).
         apply getMappedPageEq with level;trivial .
         symmetry;trivial.
        rewrite <- Hmapsfalse in Hvax.
        
        rewrite Hnewmap in *.
        inversion Hvax;subst.
        now contradict Hmykey.
      -- subst.
        apply getMappedPageMapMMUPage with phyVaChild ptVaChildpd
          r w e vaChild phyDescChild level entry;trivial.
        rewrite negb_true_iff in *. 
        subst;trivial.
    - (** phyDescChild = parent *)
      subst parent.
      assert(Htrue : phyDescChild <> child).
      { assert(Hparent : StateLib.getParent child (memory s) = Some phyDescChild)by
        (apply Hisparent;trivial).
        assert (Hisances : In phyDescChild (getAncestors child s)) by(
        unfold getAncestors;destruct nbPage;simpl;rewrite Hparent;simpl
        ;left;trivial).
        assert(Hnocycle : noCycleInPartitionTree s) by 
        (unfold consistency in *; intuition).
        apply Hnocycle;trivial.
        apply childrenPartitionInPartitionList with phyDescChild ; 
        (unfold consistency in *; intuition).
         }
      assert(Hused : getUsedPages child s' = getUsedPages child s). 
      { symmetry. 
        apply getUsedPagesMapMMUPage with phyDescChild vaChild entry level;trivial.
        unfold consistency in *. intuition.
        intros;subst;split;trivial.
        apply childrenPartitionInPartitionList with phyDescChild; 
        (unfold consistency in *; intuition). }
      rewrite Hused. clear Hused.
      unfold incl; intros x Hx.
      assert(Hmykey : x = phyVaChild  \/ x <> phyVaChild) by apply pageDecOrNot.
    destruct Hmykey as [Hmykey | Hmykey].
    * subst phyVaChild.
      unfold getMappedPages.
      assert(Hpd : StateLib.getPd phyDescChild (memory s) =
              StateLib.getPd phyDescChild (memory s')).
      { unfold s'. simpl.
        symmetry. apply getPdMapMMUPage with entry;trivial. }
      rewrite  nextEntryIsPPgetPd in *.
      rewrite <- Hpd in *.
      assert(Hpp : StateLib.getPd phyDescChild (memory s) = Some pdChildphy);trivial.
      rewrite Hpp in *.
      unfold getMappedPagesAux.
      apply filterOptionInIff.
      unfold getMappedPagesOption.
      apply in_map_iff.
      assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
      StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va1 ( CLevel (nbLevel -1) ) = true )
      by apply AllVAddrWithOffset0.
      destruct Heqvars as (va1 & Hva1 & Hva11).  
      exists va1.
      split;trivial.
      rewrite <- Hnewmap.
      symmetry.
      apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
      apply getNbLevelEqOption.
    * assert(Hmykey1 : In x (getMappedPages phyDescChild s)).
      { unfold incl in Hvs.
        apply Hvs with child;trivial. }    
      unfold getMappedPages in *.
      assert(Hpd : StateLib.getPd phyDescChild (memory s) =
              StateLib.getPd phyDescChild (memory s')).
      { unfold s'. simpl.
        symmetry. apply getPdMapMMUPage with entry;trivial. }
      rewrite  nextEntryIsPPgetPd in *.
      rewrite <- Hpd in *.      
      assert(Hpp : StateLib.getPd phyDescChild (memory s) = Some pdChildphy);trivial.
      rewrite Hpp in *.
      unfold getMappedPagesAux in *.
      apply filterOptionInIff.
      apply filterOptionInIff in Hmykey1.
      unfold getMappedPagesOption in *.
      apply in_map_iff.
      apply in_map_iff in Hmykey1.
      destruct Hmykey1 as (vax & Hvax & Hva).
      exists vax;split;trivial.
      assert(Hor1 :checkVAddrsEqualityWOOffset nbLevel vaChild vax level = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false).
      { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild vax level);intuition. }
      destruct Hor1 as [Hor1 | Hor1].
      ++ assert (Hmapsfalse : getMappedPage pdChildphy s vaChild = 
         getMappedPage pdChildphy s vax).
         { apply getMappedPageEq with level;trivial .
           symmetry;trivial. }
         assert(Hmykey3 : getMappedPage pdChildphy s vaChild = SomeDefault).
         { apply getMappedPageNotPresent with ptVaChildpd phyDescChild;intuition;
           subst;trivial. rewrite negb_true_iff in *. subst;trivial.
           apply nextEntryIsPPgetPd;trivial. }
        rewrite <- Hmapsfalse in *.
        rewrite Hmykey3 in *.
        now contradict Hvax.
      ++  rewrite negb_true_iff in *. 
        subst.
        assert(Hmykey4 : entryPresentFlag ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
        false s) by trivial.
        unfold consistency in *;intuition.
        assert(Hpppd : nextEntryIsPP phyDescChild PDidx pdChildphy s).
        apply nextEntryIsPPgetPd;trivial.
apply getMappedPageKeepsAnyMappedPage with phyDescChild entry
level (currentPartition s);trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
symmetry;trivial.
intros;subst;split;trivial.
Qed.


 Lemma  partitionDescriptorEntryMapMMUPage s entry ptVaChildpd r w e idxvaChild phyVaChild
 (vaChild vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD  pdChildphy phyDescChild :page)
  ( presentvaChild :bool)
(level :level)
:

lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
noDupPartitionTree s ->
isPresentNotDefaultIff s -> noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd 
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd  
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> (forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
partitionDescriptorEntry s -> 
partitionDescriptorEntry {|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros.
assert(Hpde : partitionDescriptorEntry s) by trivial.
unfold partitionDescriptorEntry in *.
intros.
assert( idxroot < tableSize - 1 /\
     isVA partition idxroot s /\
     (exists entry : page,
        nextEntryIsPP partition idxroot entry s /\ entry <> defaultPage)) 
        as (Hi1 & Hi2 & Hi3) .
apply Hpde;trivial.
apply getPartitionsMapMMUPage with entry
vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd idxvaChild
phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
level;trivial.
split;trivial.
split.
apply isVAMapMMUPage with entry;trivial.
destruct Hi3 as (pp & Hpp & Hnotdef).
exists pp;split;trivial.
apply nextEntryIsPPMapMMUPage with entry;trivial.
Qed.

Lemma  dataStructurePdSh1Sh2asRootMapMMUPagePD s entry ptVaChildpd r w e idxvaChild phyVaChild
 (vaChild vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD  pdChildphy phyDescChild :page)
  ( presentvaChild :bool)
(level :level) 
:

lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
noDupPartitionTree s ->
isPresentNotDefaultIff s -> noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd 
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd  
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> (forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
partitionDescriptorEntry s -> 
dataStructurePdSh1Sh2asRoot PDidx s -> 
dataStructurePdSh1Sh2asRoot PDidx {|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros.
assert(Hpde : dataStructurePdSh1Sh2asRoot PDidx s) by trivial.
unfold dataStructurePdSh1Sh2asRoot in *.
intros.
assert(Hparts : In partition (getPartitions multiplexer s)).
apply getPartitionsMapMMUPage  with entry
vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd idxvaChild
phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
level;trivial.
assert(Hpp': nextEntryIsPP partition PDidx entry0 s).
apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  phyVaChild r w  e;trivial.
subst. trivial.
assert(Hind : getIndirection entry0 va level0 stop s = Some indirection).
{ apply getIndirectionMapMMUPage4 with ptVaChildpd idxvaChild
phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild
phyDescChild entry PDidx  partition;trivial.
symmetry;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
apply nextEntryIsPPgetPd;trivial.
symmetry;trivial.
intros;subst;split;trivial.
left;trivial. }
assert(HT : True);trivial.
assert(Hlevel : Some level0 = StateLib.getNbLevel)by trivial.
generalize (Hpde partition Hparts entry0  Hpp' va HT level0 stop Hlevel indirection idx Hind);clear Hpde;
 intros Hpde.
destruct Hpde as [ Hpde | Hpde].
left. assumption.
right.
destruct Hpde as (Hpde & Hnotnull). 
split;trivial.
clear Hlevel.
destruct Hpde as [(Hlevel & Hpde) | (Hlevel & Hpde)].
+ left. split. assumption.
  apply isPEMapMMUPage with entry;trivial.
+ right. split; trivial. 
  destruct Hpde as [(Hvalue & Hidxpd) | [(Hvalue & Hidxpd) |(Hvalue & Hidxpd)]].
  - contradict Hidxpd.
    apply  idxPDidxSh1notEq.
  - contradict Hidxpd.
    apply idxPDidxSh2notEq.
  - do 2 right.
    split;trivial.
    apply isPEMapMMUPage with entry;trivial.
Qed. 

Lemma  dataStructurePdSh1Sh2asRootMapMMUPageSh1 s entry ptVaChildpd r w e idxvaChild phyVaChild
 (vaChild vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD  pdChildphy phyDescChild :page)
  ( presentvaChild :bool)
(level :level) 
:

lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
noDupPartitionTree s ->
isPresentNotDefaultIff s -> noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd 
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd  
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> (forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
partitionDescriptorEntry s -> 
dataStructurePdSh1Sh2asRoot sh1idx s -> 
dataStructurePdSh1Sh2asRoot sh1idx {|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros.
assert(Hpde : dataStructurePdSh1Sh2asRoot sh1idx s) by trivial.
unfold dataStructurePdSh1Sh2asRoot in *.
intros.
assert(Hparts : In partition (getPartitions multiplexer s)).
apply getPartitionsMapMMUPage  with entry
vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd idxvaChild
phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
level;trivial.
assert(Hpp': nextEntryIsPP partition sh1idx entry0 s).
apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  phyVaChild r w  e;trivial.
subst. trivial.
assert(Hind : getIndirection entry0 va level0 stop s = Some indirection).
{ apply getIndirectionMapMMUPage4 with ptVaChildpd idxvaChild
phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild
phyDescChild entry sh1idx  partition;trivial.
symmetry;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
apply nextEntryIsPPgetPd;trivial.
symmetry;trivial.
intros;subst;split;trivial.
right;left;trivial. }
assert(HT : True);trivial.
assert(Hlevel : Some level0 = StateLib.getNbLevel)by trivial.
generalize (Hpde partition Hparts entry0  Hpp' va HT level0 stop Hlevel indirection idx Hind);clear Hpde;
 intros Hpde.
destruct Hpde as [ Hpde | Hpde].
left. assumption.
right.
destruct Hpde as (Hpde & Hnotnull). 
split;trivial.
clear Hlevel.
destruct Hpde as [(Hlevel & Hpde) | (Hlevel & Hpde)].
+ left. split. assumption.
  apply isPEMapMMUPage with entry;trivial.
+ right. split; trivial. 
  destruct Hpde as [(Hvalue & Hidxpd) | [(Hvalue & Hidxpd) |(Hvalue & Hidxpd)]].
  - left. split;trivial.
    apply isVEMapMMUPage with entry;trivial.
  - contradict Hidxpd.
    symmetrynot.    apply idxSh2idxSh1notEq. 
  - contradict Hidxpd.
    symmetrynot.
    apply idxPDidxSh1notEq.
Qed.

Lemma  dataStructurePdSh1Sh2asRootMapMMUPageSh2 s entry ptVaChildpd r w e idxvaChild phyVaChild
 (vaChild vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD  pdChildphy phyDescChild :page)
  ( presentvaChild :bool)
(level :level) 
:

lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
noDupPartitionTree s ->
isPresentNotDefaultIff s -> noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd 
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd  
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> (forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
partitionDescriptorEntry s -> 
dataStructurePdSh1Sh2asRoot sh2idx s -> 
dataStructurePdSh1Sh2asRoot sh2idx {|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros.
assert(Hpde : dataStructurePdSh1Sh2asRoot sh2idx s) by trivial.
unfold dataStructurePdSh1Sh2asRoot in *.
intros.
assert(Hparts : In partition (getPartitions multiplexer s)).
apply getPartitionsMapMMUPage  with entry
vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd idxvaChild
phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
level;trivial.
assert(Hpp': nextEntryIsPP partition sh2idx entry0 s).
apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  phyVaChild r w  e;trivial.
subst. trivial.
assert(Hind : getIndirection entry0 va level0 stop s = Some indirection).
{ apply getIndirectionMapMMUPage4 with ptVaChildpd idxvaChild
phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild
phyDescChild entry sh2idx  partition;trivial.
symmetry;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
apply nextEntryIsPPgetPd;trivial.
symmetry;trivial.
intros;subst;split;trivial.
do 2 right;trivial. }
assert(HT : True);trivial.
assert(Hlevel : Some level0 = StateLib.getNbLevel)by trivial.
generalize (Hpde partition Hparts entry0  Hpp' va HT level0 stop Hlevel indirection idx Hind);clear Hpde;
 intros Hpde.
destruct Hpde as [ Hpde | Hpde].
left. assumption.
right.
destruct Hpde as (Hpde & Hnotnull). 
split;trivial.
clear Hlevel.
destruct Hpde as [(Hlevel & Hpde) | (Hlevel & Hpde)].
+ left. split. assumption.
  apply isPEMapMMUPage with entry;trivial.
+ right. split; trivial. 
  destruct Hpde as [(Hvalue & Hidxpd) | [(Hvalue & Hidxpd) |(Hvalue & Hidxpd)]].
  - contradict Hidxpd.
    apply idxSh2idxSh1notEq. 
  - right; left. split;trivial.
    apply isVAMapMMUPage with entry;trivial.
  - contradict Hidxpd.
    symmetrynot.
    apply idxPDidxSh2notEq.
Qed.

Lemma getPartitionsMapMMUPage1 s entry (vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD 
ptVaChildpd :page) idxvaChild phyVaChild pdChildphy r w e
phyDescChild  vaChild presentvaChild level :
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
noDupPartitionTree s -> 
partitionDescriptorEntry s -> 
isPresentNotDefaultIff s -> 
noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) ->
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
 nextEntryIsPP (currentPartition s) PDidx currentPD s  -> 
forall part, 
In part (getPartitions multiplexer s) -> 
In part (getPartitions multiplexer {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}).
Proof.
intros Hlookup Hnewcons2 Hnewcons Hnoduptree Hi1 Hi2 Hi3 Hi4 Hlevel Hnotpresent
 Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent Hpdchild Hcurpart
 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Hcurrpd.
set(s' :=  {|
         currentPartition := _ |}) in *.
unfold getPartitions. 
assert(Hmult: In multiplexer (getPartitions multiplexer s)).
{ unfold getPartitions.
  destruct (nbPage);simpl; left;trivial. }
revert Hmult.
generalize multiplexer at 1 3 4.
induction (nbPage + 1);trivial;simpl.
intros mult Hmult part Hpart.
destruct Hpart as [Hpart | Hpart].
left;trivial.
right.
rewrite in_flat_map in *.
destruct Hpart as(child & Hchild1 & Hpart).
exists child.
assert(Hchild : In child (getChildren mult s')).
{ apply getChildrenMapMMUPage1 with pdChildphy  (currentPartition s)
presentvaChild vaChild phyDescChild level entry;trivial.
assert(getAccessibleMappedPage currentPD s vaInCurrentPartition =SomePage phyVaChild). 
apply isAccessibleMappedPage2 with (currentPartition s) ptVaInCurPartpd;
trivial.
unfold getAccessibleMappedPages.
rewrite nextEntryIsPPgetPd in *. rewrite Hcurrpd. 
unfold getAccessibleMappedPagesAux. 
apply filterOptionInIff.
unfold getAccessibleMappedPagesOption.
apply in_map_iff.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaInCurrentPartition va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1.
split;trivial.
rewrite <- H.
symmetry.
apply getAccessibleMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption. }
split;trivial. 
apply IHn;trivial.
apply childrenPartitionInPartitionList with mult;trivial.
Qed. 

Lemma currentPartitionInPartitionsListMapMMUPage s ptVaChildpd idxvaChild phyVaChild r w e
  entry 
 (vaChild vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD  pdChildphy phyDescChild :page)
  ( presentvaChild :bool)
(level :level)  :
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
noDupPartitionTree s ->
partitionDescriptorEntry s -> 
isPresentNotDefaultIff s -> noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd 
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd  
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> (forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
currentPartitionInPartitionsList s -> 
currentPartitionInPartitionsList
{|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
unfold currentPartitionInPartitionsList;simpl.
intros.
apply getPartitionsMapMMUPage1 with  entry
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
vaChild presentvaChild level;trivial.
Qed.

 Lemma mapPageMapSinglePage s vax vaChild pdChildphy level
  phyVaChild r w e ptVaChildpd mapped
  idxvaChild currentPart
 presentvaChild 
phyDescChild entry  : 
  let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 

  StateLib.getNbLevel = Some level -> 
checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false -> 
getMappedPage pdChildphy s' vax =  SomePage mapped -> 
noDupConfigPagesList s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
In currentPart (getPartitions multiplexer s) ->
In phyVaChild (getAccessibleMappedPages currentPart s) ->
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) ->
negb presentvaChild = true ->
In phyDescChild (getPartitions multiplexer s) ->
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s ->
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s ->
(defaultPage =? ptVaChildpd) = false ->
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild ->
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
pdChildphy <> defaultPage ->
getIndirection pdChildphy vaChild level (nbLevel - 1) s = Some ptVaChildpd ->
getMappedPage pdChildphy s vax = SomePage mapped.
Proof. 
intros s' Hlevel Hvaneg Hmapped Hnodupconfig.
intros.
move Hmapped at bottom.
unfold getMappedPage in *.
rewrite Hlevel in *.
case_eq(getIndirection pdChildphy vax level (nbLevel - 1) s');[intros ind Hind | intros Hind];
rewrite Hind in *;try now contradict Hmapped.

assert(Hindeq : getIndirection pdChildphy vax level (nbLevel - 1) s = Some ind). 
{ subst.
apply getIndirectionMapMMUPage4
with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
phyVaChild r w e pdChildphy currentPart presentvaChild vaChild
phyDescChild entry PDidx phyDescChild;trivial.
left;trivial. }
rewrite Hindeq.
case_eq(defaultPage =? ind);intros Hdef; rewrite Hdef in *;try now contradict Hmapped;
trivial.
assert(Hor : ptVaChildpd <> ind \/ (StateLib.getIndexOfAddr vaChild fstLevel)
<> (StateLib.getIndexOfAddr vax fstLevel)). 
{ apply pageTablesOrIndicesAreDifferent with pdChildphy pdChildphy level 
nbLevel s;trivial.  apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
         unfold noDupConfigPagesList in *. 
unfold consistency in *;intuition.
unfold consistency in *;intuition.
apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
unfold noDupConfigPagesList in *. 
unfold consistency in *;intuition.
unfold consistency in *;intuition.
left.
split;trivial.
apply getNbLevelEq;symmetry;trivial. 
assert (Hdefault : (defaultPage =? ptVaChildpd) = false) by trivial.
apply beq_nat_false in Hdefault.
unfold not;intros;subst.
now contradict Hdefault.
apply beq_nat_false in Hdef.
unfold not;intros;subst.
now contradict Hdef.
(* assert(Hind1 : getIndirection pdChildphy vaChild level (nbLevel - 1) s =
      Some ptVaChildpd) by trivial.
rewrite <- Hind1. *)
apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial.
 apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
 apply getNbLevelLt;trivial.
 symmetry.
 rewrite getNbLevelEq with level;trivial.
 symmetry. apply nbLevelEq.
 symmetry;trivial. }
assert (Hpres :StateLib.readPresent ind (StateLib.getIndexOfAddr vax fstLevel) (memory s) =
StateLib.readPresent ind (StateLib.getIndexOfAddr vax fstLevel) (memory s')).

{ subst. apply readPresentMapMMUPage with entry;trivial.
intuition. }
rewrite Hpres.
assert (Hphy :StateLib.readPhyEntry ind (StateLib.getIndexOfAddr vax fstLevel) (memory s) =
StateLib.readPhyEntry ind (StateLib.getIndexOfAddr vax fstLevel) (memory s')).

{ subst. apply readPhyEntryMapMMUPage with entry;trivial.
intuition. }
rewrite Hphy;trivial.
Qed.




Lemma noDupConfigPagesListMapMMUPage 
 s entry (vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD 
ptVaChildpd :page) idxvaChild phyVaChild pdChildphy r w e
phyDescChild  vaChild presentvaChild level :
let s' := {|
     currentPartition := currentPartition s;
     memory := add ptVaChildpd idxvaChild
                 (PE
                    {|
                    read := r;
                    write := w;
                    exec := e;
                    present := true;
                    user := true;
                    pa := phyVaChild |}) (memory s) beqPage beqIndex |} in 
( forall part,
In part (getPartitions multiplexer s) -> 
 NoDup (getConfigPages part s)) -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
consistency s -> StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) ->
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
 nextEntryIsPP (currentPartition s) PDidx currentPD s  -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 

noDupConfigPagesList s'.
Proof.
intros s' Hcons.
intros.
unfold consistency in *.
intuition.
unfold noDupConfigPagesList in *. 
intros part.
intros.
assert(Hparts : In part (getPartitions multiplexer s)) by
(apply getPartitionsMapMMUPage  with entry
vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd idxvaChild
phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
level;trivial).
assert(Hor : phyDescChild = part \/  phyDescChild <> part) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
+ subst part.
  assert(Hconf :getConfigPages phyDescChild s = getConfigPages phyDescChild s').
  apply getConfigPagesMapMMUPage1 with entry pdChildphy
(currentPartition s) presentvaChild vaChild level;trivial.
unfold consistency;intuition.
symmetry ;trivial.
rewrite <- Hconf.
unfold consistency in *;intuition.
+ assert(Hconf :getConfigPages part s = getConfigPages part s').
apply getConfigPagesMapMMUPage with phyDescChild entry;trivial .
  apply isConfigTable  with vaChild;trivial.
  intros;split;subst;trivial.

  { assert(Hconfigdiff : configTablesAreDifferent s ) by (
    unfold consistency in *; intuition). apply Hconfigdiff;trivial. }
    rewrite <- Hconf.
    intuition.
Qed.

Lemma parentInPartitionListMapMMUPage
 s entry (vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD 
ptVaChildpd :page) idxvaChild phyVaChild pdChildphy r w e
phyDescChild  vaChild presentvaChild level :
let s' :={|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
parentInPartitionList s -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
consistency s -> StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) ->
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
 nextEntryIsPP (currentPartition s) PDidx currentPD s  -> 
parentInPartitionList s'.
Proof.
unfold parentInPartitionList.
intros Hcons.
intros.
move Hcons at bottom.
unfold consistency in *.
intuition.
assert(Hparts : In partition (getPartitions multiplexer s)).
apply getPartitionsMapMMUPage  with entry
vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd idxvaChild
phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
level;trivial.
apply getPartitionsMapMMUPage1 with  entry
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
vaChild presentvaChild level;trivial.
apply Hcons with partition;trivial.
apply nextEntryIsPPMapMMUPage' with ptVaChildpd idxvaChild phyVaChild
r w e;trivial.
Qed.

Lemma getPDFlagMapMMUPage s phyVaChild ptVaChildpd idxvaChild r w e sh1 va
entry
 (vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD 
 :page)   pdChildphy 
phyDescChild  vaChild presentvaChild level part
:
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex =
    Some (PE entry) -> 
    StateLib.getNbLevel = Some level ->
consistency s -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) ->
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
 nextEntryIsPP (currentPartition s) PDidx currentPD s  -> 
 In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
 getFstShadow part (memory s) = Some sh1 -> 
 In part (getPartitions multiplexer s) ->
getPDFlag sh1 va s' = getPDFlag sh1 va s.
Proof.
intros s' Hlookup Hlevel Hcons.
intros.
unfold consistency in *. intuition.
unfold getPDFlag.
rewrite Hlevel.

case_eq( getIndirection sh1 va level (nbLevel - 1) s');
[intros ind Hind | intros Hind].
+ assert (Hind' :  getIndirection sh1 va level (nbLevel - 1) s = Some ind).
  { apply getIndirectionMapMMUPage4 with
   ptVaChildpd idxvaChild
phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild
phyDescChild entry sh1idx part;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
   apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
   apply nextEntryIsPPgetPd;trivial.
   intros;subst;split;trivial.
   apply nextEntryIsPPgetFstShadow;trivial.
   right;left;trivial. }
rewrite Hind'.
destruct (ind =? defaultPage);trivial. 
assert(Hread:  StateLib.readPDflag ind (StateLib.getIndexOfAddr va fstLevel) (memory s') 
=  StateLib.readPDflag ind (StateLib.getIndexOfAddr va fstLevel) (memory s)).
apply readPDflagMapMMUPage with entry;trivial.
rewrite Hread;trivial.
+ assert (Hind' :  getIndirection sh1 va level (nbLevel - 1) s =None).
  { apply getIndirectionMapMMUPage4None with
   ptVaChildpd idxvaChild
phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild
phyDescChild entry sh1idx part;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
   apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
   apply nextEntryIsPPgetPd;trivial.
   intros;subst;split;trivial.
   apply nextEntryIsPPgetFstShadow;trivial.
   right;left;trivial. }
rewrite Hind';trivial.
Qed.

Lemma accessibleVAIsNotPartitionDescriptorMapMMUPage  s entry (vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD 
ptVaChildpd :page) idxvaChild phyVaChild pdChildphy r w e
phyDescChild  vaChild presentvaChild level :
let s' :={|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
accessibleVAIsNotPartitionDescriptor s -> 
(forall child : page,  
    In child (getChildren  (currentPartition s) s) -> ~ In phyVaChild (getMappedPages child s)) -> 
In phyDescChild (getChildren (currentPartition s) s) ->

lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
consistency s -> StateLib.getNbLevel = Some level -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) ->
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
 nextEntryIsPP (currentPartition s) PDidx currentPD s  -> 
accessibleVAIsNotPartitionDescriptor s'.
Proof.
intros s'  Hnewcons2 Hnewcons Hcons Hnotderiv ;intros;move Hcons at bottom.
unfold consistency in *. intuition.
unfold accessibleVAIsNotPartitionDescriptor in *.
intros part va pd sh1 pg Hpart Hpd Hsh1 Haccess.
assert(Hparts :  In part (getPartitions multiplexer s)).
{ apply getPartitionsMapMMUPage with entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd idxvaChild
  phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
  level;trivial. }
assert(Hpd' : StateLib.getPd part (memory s) =
        StateLib.getPd part (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdMapMMUPage with entry;trivial. }
rewrite <- Hpd' in *. clear Hpd'.
assert(Hsh1' : StateLib.getFstShadow part (memory s) =
        StateLib.getFstShadow part (memory s')).
{ unfold s'. simpl.
  symmetry. apply getFstShadowMapMMUPage with entry;trivial. }
rewrite <- Hsh1' in *. clear Hsh1'.
assert (Hpdflag :  getPDFlag sh1 va s' = getPDFlag sh1 va s).
{  apply getPDFlagMapMMUPage with entry
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
vaChild presentvaChild level part;trivial.
unfold consistency ;intuition;trivial. }
rewrite Hpdflag.
assert(Hor : part = phyDescChild \/ part <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor]; subst.
+ assert(Hpdeq : pd = pdChildphy).
  { symmetry. apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
  subst.

assert(Hor1 :checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaChild va level = false).
      { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild va level);intuition. }
destruct Hor1 as [Hor1 | Hor1].
- assert (Hmapsfalse : getMappedPage pdChildphy s vaChild = 
         getMappedPage pdChildphy s va).
         { apply getMappedPageEq with level;trivial . }
         assert(Hmykey3 : getMappedPage pdChildphy s vaChild = SomeDefault).
         { apply getMappedPageNotPresent with ptVaChildpd phyDescChild;intuition;
           subst;trivial. rewrite negb_true_iff in *. subst;trivial. }
         unfold wellFormedFstShadowIfDefaultValues in *.

        apply Hnewcons with phyDescChild pdChildphy;trivial.
        rewrite <- Hmapsfalse in *;trivial.
- assert(Hor :pg = phyVaChild \/ pg <> phyVaChild) by apply pageDecOrNot.
  destruct Hor as [Hor | Hor].
  * subst.
    assert(Hlookup : lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
     (memory s) beqPage beqIndex =
     Some (PE entry)) by trivial.

assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
          (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some defaultPage).
{ assert(Hcons1 : isPresentNotDefaultIff s).
  unfold consistency in *. intuition.            
  apply Hcons1.
  subst.
  unfold entryPresentFlag in *. 
  unfold StateLib.readPresent.
  rewrite Hlookup in *.
  f_equal.
  subst.
  assert (Hentrypresent : negb (present entry) = true) by trivial.
  apply negb_true_iff in Hentrypresent.
  subst. trivial. }

assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
              (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some phyVaChild).
{ unfold StateLib.readPhyEntry. 
  cbn.
  assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
  (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
  beqIndex = true); intros.
  rewrite <- beqPairsTrue;split;trivial.
  subst.
  rewrite Hpairs.
  simpl;trivial. }
    assert (Hnewmap1 : getMappedPage pdChildphy s' vaChild = SomePage phyVaChild).
    { apply getMappedPageGetTableRoot with ptVaChildpd phyDescChild;
      trivial;fold s'. 
      + intros. 
      split. 
      apply isPEMapMMUPage with entry;trivial.
      subst;trivial.
      assert(Htblroot : getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
      unfold getTableAddrRoot in Htblroot.
      destruct Htblroot as (Hidxs & Htblroot).
      split;trivial.
      intros.
      assert(Hpdchild : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
      apply Htblroot in Hpdchild;clear Htblroot.
      move Hpdchild at bottom.
      destruct Hpdchild as (nbL & HnbL & stop & Hstop & Hind1).
      exists nbL ; split ; trivial.
      exists stop;split;trivial.
      assert(tableroot = pdChildphy). 
      apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
      apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
      phyVaChild r w  e;trivial.
      subst. trivial.
      subst .
      revert Hind1.
     
      assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial.
      
      revert Htrue1 Htrue2 Hlookup Hdefaut.
      clear. 
      intros.
       apply getIndirectionMapMMUPage with entry;trivial;subst;trivial.
     + unfold isEntryPage, StateLib.readPhyEntry in *. 
       destruct(lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                 (memory s') beqPage beqIndex);trivial;try now contradict Htrue2.
       destruct v;try now contradict Htrue2.
       inversion Htrue2;trivial.
     + unfold entryPresentFlag. 
       cbn.
       subst.
       assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
          (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
          beqIndex = true).
       apply beqPairsTrue;split;trivial.
       rewrite Hpairs.
       simpl;trivial.
           
    + apply  nextEntryIsPPMapMMUPage with entry;trivial. }
    assert(Hindchild' :  getIndirection pdChildphy vaChild level (nbLevel - 1) s' =
  Some ptVaChildpd). 
{ unfold s'.
  subst.
  apply getIndirectionMapMMUPage3 with entry;trivial.
  apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
  intros;subst;split;trivial. }
    assert(Htrue : getAccessibleMappedPage pdChildphy s' vaChild = SomePage phyVaChild). 
    { assert (Hlevel :StateLib.getNbLevel = Some level) by trivial.
     revert Hnewmap1 Hindchild' Hlevel.
      subst.
      clear.
      unfold  getMappedPage, getAccessibleMappedPage. 
      intros.
      rewrite  Hlevel in *.
      rewrite Hindchild' in *.
      destruct(defaultPage =? ptVaChildpd);try now contradict Hnewmap1.
      destruct ( StateLib.readPresent ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
      (memory s'));try now contradict Hnewmap1. 
      destruct b;try now contradict Hnewmap1.
      unfold StateLib.readAccessible. 
      cbn.
      assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
      beqIndex = true).
      { apply beqPairsTrue;split;trivial. }
      rewrite Hpairs.
      simpl. trivial. }
    assert(Hmykey :vaChild <> va).
    apply checkVAddrsEqualityWOOffsetEqFalse with level level;trivial;
    symmetry;trivial.
    assert(Hfalse :phyVaChild <> phyVaChild).
apply twoMappedPagesAreDifferent with vaChild va pdChildphy level s';trivial.
apply accessiblePAgeIsMapped;trivial.
assert(HnodupS : noDupMappedPagesList s').
{
apply noDupMappedPagesListMapMMUPage  with entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
presentvaChild level true true true ;trivial ;intros;subst;trivial.
unfold consistency in *;intuition. }
unfold noDupMappedPagesList in HnodupS.
unfold getMappedPages in HnodupS.
apply HnodupS in Hpart.
assert(Hpd' : StateLib.getPd phyDescChild (memory s) =
        StateLib.getPd phyDescChild (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdMapMMUPage with entry;trivial. }
  rewrite Hpd' in Hpd.
  rewrite Hpd in Hpart.
  unfold getMappedPagesAux in Hpart.
  unfold getMappedPagesOption in Hpart;trivial.
now contradict Hfalse.

  * apply Hcons with phyDescChild pdChildphy pg;trivial.
  apply getAccessibleMappedPageMapMMUPage with phyVaChild ptVaChildpd
r w e vaChild phyDescChild level entry;trivial.
symmetry;trivial.
unfold consistency in *;intuition.
rewrite negb_true_iff in *.  
        subst;trivial.
+   assert(Hmykey2 :  disjoint (getConfigPages phyDescChild s)
                  (getConfigPages part s)).
  { assert(Hconfigdiff : configTablesAreDifferent s ) by (
    unfold consistency in *; intuition). apply Hconfigdiff;trivial.
    intuition. }
    apply Hcons with part pd pg;trivial.
rewrite <- Haccess.
  apply getAccessibleMappedPageMapMMUPage1  with part phyDescChild
vaChild entry level;trivial.
apply isConfigTable with vaChild;trivial.
intros;subst;split;trivial.
symmetry;trivial. 
intros;subst;split;trivial.
intuition.
Qed.

Lemma  getVirtualAddressSh2MapMMUPage  
s entry (vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD 
ptVaChildpd :page) idxvaChild phyVaChild pdChildphy r w e
phyDescChild  vaChild presentvaChild level va :
let s' :={|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
consistency s -> StateLib.getNbLevel = Some level -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) ->
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
 nextEntryIsPP (currentPartition s) PDidx currentPD s  ->
 forall part sh2, In part (getPartitions multiplexer s) ->   
getSndShadow part (memory s) = Some sh2 ->
getVirtualAddressSh2 sh2 s va = getVirtualAddressSh2 sh2 s' va.
Proof.
intros. 
unfold getVirtualAddressSh2.
unfold consistency in *;intuition.
assert(Hlevel:  StateLib.getNbLevel = Some level) by trivial.
rewrite Hlevel.

case_eq( getIndirection sh2 va level (nbLevel - 1) s');
[intros ind Hind | intros Hind].
+ assert (Hind' :  getIndirection sh2 va level (nbLevel - 1) s = Some ind).
  { apply getIndirectionMapMMUPage4 with
   ptVaChildpd idxvaChild
phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild
phyDescChild entry sh2idx part;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
   apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
   apply nextEntryIsPPgetPd;trivial.
   intros;subst;split;trivial.
   apply nextEntryIsPPgetSndShadow;trivial.
   do 2 right;trivial. }
rewrite Hind'.
destruct (defaultPage =? ind);trivial. 
assert(Hread:  StateLib.readVirtual ind (StateLib.getIndexOfAddr va fstLevel) (memory s') 
=  StateLib.readVirtual ind (StateLib.getIndexOfAddr va fstLevel) (memory s)).
apply readVirtualMapMMUPage with entry;trivial.
rewrite Hread;trivial.
+ assert (Hind' :  getIndirection sh2 va level (nbLevel - 1) s =None).
  { apply getIndirectionMapMMUPage4None with
   ptVaChildpd idxvaChild
phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild
phyDescChild entry sh2idx part;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
   apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
   apply nextEntryIsPPgetPd;trivial.
   intros;subst;split;trivial.
   apply nextEntryIsPPgetSndShadow;trivial.
   do 2 right;trivial. }
rewrite Hind';trivial.
   Qed.
   
Lemma  getVirtualAddressSh1MapMMUPage  
s entry (vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD 
ptVaChildpd :page) idxvaChild phyVaChild pdChildphy r w e
phyDescChild  vaChild presentvaChild level va :
let s' :={|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
consistency s -> StateLib.getNbLevel = Some level -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) ->
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
 nextEntryIsPP (currentPartition s) PDidx currentPD s  ->
 forall part sh1, In part (getPartitions multiplexer s) ->   
getFstShadow part (memory s) = Some sh1 ->
getVirtualAddressSh1 sh1 s va = getVirtualAddressSh1 sh1 s' va.
Proof.
intros. 
unfold getVirtualAddressSh1.
unfold consistency in *;intuition.
assert(Hlevel:  StateLib.getNbLevel = Some level) by trivial.
rewrite Hlevel.

case_eq( getIndirection sh1 va level (nbLevel - 1) s');
[intros ind Hind | intros Hind].
+ assert (Hind' :  getIndirection sh1 va level (nbLevel - 1) s = Some ind).
  { apply getIndirectionMapMMUPage4 with
   ptVaChildpd idxvaChild
phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild
phyDescChild entry sh1idx part;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
   apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
   apply nextEntryIsPPgetPd;trivial.
   intros;subst;split;trivial.
   apply nextEntryIsPPgetFstShadow;trivial.
   right;left;trivial. }
rewrite Hind'.
destruct (defaultPage =? ind);trivial. 
assert(Hread:  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va fstLevel) (memory s') 
=  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va fstLevel) (memory s)).
symmetry. apply readVirEntryMapMMUPage with entry;trivial.
rewrite Hread;trivial.
+ assert (Hind' :  getIndirection sh1 va level (nbLevel - 1) s =None).
  { apply getIndirectionMapMMUPage4None with
   ptVaChildpd idxvaChild
phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild
phyDescChild entry sh1idx part;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
   apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
   apply nextEntryIsPPgetPd;trivial.
   intros;subst;split;trivial.
   apply nextEntryIsPPgetFstShadow;trivial.
   right;left;trivial. }
rewrite Hind';trivial.
   Qed.
Lemma accessibleChildPageIsAccessibleIntoParentMapMMUPage   s entry (vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD 
ptVaChildpd :page) idxvaChild phyVaChild pdChildphy r w e 
phyDescChild  vaChild presentvaChild level ptVaChildsh2:
let s' :={|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
accessibleChildPageIsAccessibleIntoParent s ->
(forall child : page,  
    In child (getChildren  (currentPartition s) s) -> ~ In phyVaChild (getMappedPages child s)) -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
consistency s -> StateLib.getNbLevel = Some level -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) ->
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
 nextEntryIsPP (currentPartition s) PDidx currentPD s  -> 
isVA ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildsh2 sh2idx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildsh2) = false -> 
StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
Some vaInCurrentPartition -> 
In phyDescChild (getChildren (currentPartition s) s) ->

accessibleChildPageIsAccessibleIntoParent s'.
Proof.
intros s' Hcons Hnotderived;intros.
unfold consistency in *. intuition.
move Hcons at bottom.
unfold accessibleChildPageIsAccessibleIntoParent in *.
intros part va pd accespg Hpart Hpd Haccespg.
assert(Hparts :  In part (getPartitions multiplexer s)).
{ apply getPartitionsMapMMUPage with entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd idxvaChild
  phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
  level;trivial. }
assert(Hpd' : StateLib.getPd part (memory s) =
        StateLib.getPd part (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdMapMMUPage with entry;trivial. }
rewrite <- Hpd' in *. clear Hpd'.
subst.
  assert(Hlookup : lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  (memory s) beqPage beqIndex =
  Some (PE entry)) by trivial.
  assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
          (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some defaultPage).
  { assert(Hcons1 : isPresentNotDefaultIff s).
    unfold consistency in *. intuition.            
    apply Hcons1.
    subst.
    unfold entryPresentFlag in *. 
    unfold StateLib.readPresent.
    rewrite Hlookup in *.
    f_equal.
    subst.
    assert (Hentrypresent : negb (present entry) = true) by trivial.
    apply negb_true_iff in Hentrypresent.
    subst. trivial. }
  assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
                (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some phyVaChild).
  { unfold StateLib.readPhyEntry. 
    cbn.
    assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
    (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
    beqIndex = true); intros.
    rewrite <- beqPairsTrue;split;trivial.
    subst.
    rewrite Hpairs.
    simpl;trivial. }
  assert (Hnewmap1 : getMappedPage pdChildphy s' vaChild = SomePage phyVaChild).
    { apply getMappedPageGetTableRoot with ptVaChildpd phyDescChild;
      trivial;fold s'. 
      + intros. 
      split. 
      apply isPEMapMMUPage with entry;trivial.
      subst;trivial.
      assert(Htblroot : getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
      unfold getTableAddrRoot in Htblroot.
      destruct Htblroot as (Hidxs & Htblroot).
      split;trivial.
      intros.
      assert(Hpdchild : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
      apply Htblroot in Hpdchild;clear Htblroot.
      move Hpdchild at bottom.
      destruct Hpdchild as (nbL & HnbL & stop & Hstop & Hind1).
      exists nbL ; split ; trivial.
      exists stop;split;trivial.
      assert(tableroot = pdChildphy). 
      apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
      apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
      phyVaChild r w  e;trivial.
      intros;apply nextEntryIsPPgetPd;trivial. 
      subst. trivial.
      subst .
      
      revert Hind1.     
      assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial.
           
      revert Htrue1 Htrue2 Hlookup Hdefaut.
      clear. 
      intros.
       apply getIndirectionMapMMUPage with entry;trivial;subst;trivial.
     + unfold isEntryPage, StateLib.readPhyEntry in *. 
       destruct(lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                 (memory s') beqPage beqIndex);trivial;try now contradict Htrue2.
       destruct v;try now contradict Htrue2.
       inversion Htrue2;trivial.
     + unfold entryPresentFlag. 
       cbn.
       subst.
       assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
          (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
          beqIndex = true).
       apply beqPairsTrue;split;trivial.
       rewrite Hpairs.
       simpl;trivial.
           
    + apply  nextEntryIsPPMapMMUPage with entry;trivial. }
  assert(Hconfdiff : configTablesAreDifferent s)by trivial.
assert( Hparent :getParent phyDescChild (memory s) = Some (currentPartition s)).
{ assert(Hisparent: isParent s);trivial.
  unfold isParent.
  apply Hisparent;trivial. }
assert( currentPartition s<> phyDescChild).
 { assert (Hnocycle : noCycleInPartitionTree s) by trivial. 
   apply Hnocycle;trivial.
   unfold getAncestors.
  destruct nbPage;simpl;
  rewrite Hparent;simpl;left;trivial. }
 assert(Hi1 : disjoint (getConfigPages phyDescChild s)
  (getConfigPages (currentPartition s) s)).
{  apply Hconfdiff;trivial. intuition. }   
assert(Hor : part = phyDescChild \/ part <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor]; subst.
+ assert(Hpdeq : pd = pdChildphy).
  { symmetry. apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
  subst.
assert(Hor1 :checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaChild va level = false).
      { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild va level);intuition. }
destruct Hor1 as [Hor1 | Hor1].
- assert(Hmapva :getMappedPage pdChildphy s' va = SomePage accespg).
  apply  accessiblePAgeIsMapped;trivial.

  assert(accespg = phyVaChild).
  { assert(Hmapeq : getMappedPage pdChildphy s' vaChild =getMappedPage pdChildphy s' va).
    apply getMappedPageEq with level;trivial.
    rewrite Hmapeq in *.
    rewrite Hnewmap1 in *.
    inversion Hmapva;subst;trivial. }
  subst.
  unfold isAccessibleMappedPageInParent.
  assert(Hi2 : getSndShadow phyDescChild (memory s') =
    getSndShadow phyDescChild (memory s)).
    { apply getSndShadowMapMMUPage with entry;trivial. }
  rewrite Hi2 in *.
  case_eq(getSndShadow phyDescChild (memory s));
  [intros sh2 Hsh2 | intros Hsh2]. 
  * assert(HgetVA : getVirtualAddressSh2 sh2 s' va = Some vaInCurrentPartition).
    { unfold getVirtualAddressSh2.
      assert (Hlevel : StateLib.getNbLevel = Some level) by trivial.
      rewrite Hlevel.
      assert(Htableroot : getTableAddrRoot ptVaChildsh2 sh2idx phyDescChild vaChild s) 
      by trivial.
      unfold getTableAddrRoot in *. 
      destruct Htableroot as (_ & Htableroot).
      apply nextEntryIsPPgetSndShadow in Hsh2.
      assert(Hkeepsh2 : nextEntryIsPP phyDescChild sh2idx sh2 s) by trivial.
      apply Htableroot in Hsh2.
      clear Htableroot.
      destruct Hsh2 as (nbL & HnbL & stop & Hstop& Hindsh2).
      subst.
      assert (Hnewindsh2 :getIndirection sh2 vaChild nbL (nbLevel-1) s = Some ptVaChildsh2). 
      { apply getIndirectionStopLevelGT2 with (nbL + 1);trivial.
        omega.
        rewrite <- HnbL in *.
        inversion Hlevel;subst.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        apply nbLevelEq. }
      rewrite <- HnbL in Hlevel.
          inversion Hlevel;subst.
      assert(Hnewgoal : getIndirection sh2 va level (nbLevel - 1) s' = Some ptVaChildsh2).
      { apply getIndirectionMapMMUPage5  with pdChildphy (currentPartition s)
          presentvaChild vaChild phyDescChild entry sh2idx phyDescChild;trivial.
        * apply pdPartNotNull with phyDescChild s;trivial .
        * apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
          intros;subst;split;trivial.
        * do 2 right;trivial.
        * rewrite <- Hnewindsh2.
          apply getIndirectionEq;trivial.
          apply getNbLevelLt;trivial.
          rewrite <- Hor1.
          apply checkVAddrsEqualityWOOffsetPermut.  }
      rewrite Hnewgoal.
     assert( (defaultPage =? ptVaChildsh2) = false /\
            StateLib.readVirtual ptVaChildsh2 
            (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =
            Some vaInCurrentPartition ) as (Hi4 & Hi3) by intuition.
      rewrite Hi4.
      rewrite <- Hi3.
      symmetry.
      assert(Hi5 : (StateLib.getIndexOfAddr vaChild fstLevel) =
      (StateLib.getIndexOfAddr va fstLevel)).
      { apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level;trivial.
        apply fstLevelLe.
        apply getNbLevelLt;trivial. }
      rewrite Hi5.
      symmetry.
      apply readVirtualMapMMUPage with entry;trivial. }
  rewrite HgetVA.
 assert(Hparent' : getParent phyDescChild (memory s')  = getParent phyDescChild (memory s)).
{ apply getParentMapMMUPage with entry;trivial. }
rewrite Hparent' in *;clear Hparent'.
 
   rewrite  Hparent. 
assert(Hpd' : StateLib.getPd (currentPartition s) (memory s) =
        StateLib.getPd (currentPartition s) (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdMapMMUPage with entry;trivial. }
rewrite <- Hpd' in *. clear Hpd'.
subst.
 assert(Hpdcurpart : StateLib.getPd (currentPartition s) (memory s) = Some currentPD)
 by (apply nextEntryIsPPgetPd;trivial).
 rewrite Hpdcurpart.
 assert(Haccesinparent : getAccessibleMappedPage currentPD s vaInCurrentPartition =
  SomePage phyVaChild).
  { apply isAccessibleMappedPage2 with (currentPartition s) ptVaInCurPartpd;trivial.  }

 assert(Hgetaccess' : getAccessibleMappedPage currentPD s vaInCurrentPartition =
 getAccessibleMappedPage currentPD s' vaInCurrentPartition).
 apply getAccessibleMappedPageMapMMUPage1 with (currentPartition s) phyDescChild
 vaChild entry level;trivial.
 apply isConfigTable with vaChild;trivial.
intros;subst;split;trivial.
symmetry;trivial. 
intros;subst;split;trivial.
intuition.
rewrite <- Hgetaccess'.
rewrite Haccesinparent.
symmetry.
apply beq_nat_refl.
  * assert(Hped : partitionDescriptorEntry s) by trivial.
    unfold partitionDescriptorEntry in *.
    assert(Hsh2pde : (exists entry : page,
          nextEntryIsPP phyDescChild sh2idx entry s /\ entry <> defaultPage)).
    apply Hped;trivial.
    do 2 right;left;trivial.
    destruct  Hsh2pde as (sh2 & Hsh2' & _).  
    apply nextEntryIsPPgetSndShadow in Hsh2'.
    
    rewrite Hsh2 in Hsh2'.
    now contradict Hsh2'.
  -  assert(Hmykey :vaChild <> va).
   { apply checkVAddrsEqualityWOOffsetEqFalse with level level;trivial;
    symmetry;trivial. }
    assert(Hfalse : phyVaChild <> accespg).
    { apply twoMappedPagesAreDifferent with vaChild va pdChildphy level s';trivial.
apply accessiblePAgeIsMapped;trivial.
assert(HnodupS : noDupMappedPagesList s').
{
apply noDupMappedPagesListMapMMUPage  with entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
presentvaChild level true true true ;trivial ;intros;subst;trivial.
unfold consistency in *;intuition. }
unfold noDupMappedPagesList in HnodupS.
unfold getMappedPages in HnodupS.
apply HnodupS in Hpart.
assert(Hpd' : StateLib.getPd phyDescChild (memory s) =
        StateLib.getPd phyDescChild (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdMapMMUPage with entry;trivial. }
  rewrite Hpd' in Hpd.
  rewrite Hpd in Hpart.
  unfold getMappedPagesAux in Hpart.
  unfold getMappedPagesOption in Hpart;trivial.


 }
  
  assert(Hisaccess : isAccessibleMappedPageInParent phyDescChild va accespg s = true).
 {   apply Hcons with pdChildphy;trivial.
    apply getAccessibleMappedPageMapMMUPage with  phyVaChild ptVaChildpd
    r w e vaChild phyDescChild level entry;trivial.
    intuition.
    symmetry;trivial.
    unfold consistency in *;intuition.
    rewrite negb_true_iff in *.  
    subst;trivial. }
    clear Hcons.
unfold isAccessibleMappedPageInParent in *.
assert(Hsh2 : getSndShadow phyDescChild (memory s') =
getSndShadow phyDescChild (memory s)).
apply getSndShadowMapMMUPage with entry;trivial.
rewrite Hsh2 in *;clear Hsh2.
case_eq( getSndShadow phyDescChild (memory s));
[intros sh2 Hsh2| intros Hsh2];rewrite Hsh2 in *;
try now contradict Hisaccess.
assert(Hvirteq :getVirtualAddressSh2 sh2 s va = getVirtualAddressSh2 sh2 s' va).
apply getVirtualAddressSh2MapMMUPage with entry
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
vaChild presentvaChild level phyDescChild;trivial.
unfold consistency ;intuition.
rewrite <- Hvirteq.
case_eq(getVirtualAddressSh2 sh2 s va);[intros vaInParent HvaInParent |
intros HvaInParent];rewrite HvaInParent in *;try now contradict Hisaccess.
assert(Hparent' : getParent phyDescChild (memory s')  = getParent phyDescChild (memory s)).
{ apply getParentMapMMUPage with entry;trivial. }
rewrite Hparent' in *;clear Hparent'.

rewrite Hparent in *.
assert(Hpd' : StateLib.getPd (currentPartition s) (memory s) =
        StateLib.getPd (currentPartition s) (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdMapMMUPage with entry;trivial. }
rewrite <- Hpd' in *. clear Hpd'. 
assert(Hpdparent: StateLib.getPd (currentPartition s) (memory s) = Some  currentPD).
{ apply nextEntryIsPPgetPd;trivial. }
rewrite Hpdparent in *.

assert(Haccesseq : getAccessibleMappedPage currentPD s vaInParent =
getAccessibleMappedPage currentPD s' vaInParent).
{ apply getAccessibleMappedPageMapMMUPage1 with 
(currentPartition s) phyDescChild
vaChild entry level;trivial.
 apply isConfigTable with vaChild;trivial.
intros;subst;split;trivial.
symmetry;trivial. 
intros;subst;split;trivial.
intuition. }

rewrite <- Haccesseq;trivial.
+  assert(Hisaccess : isAccessibleMappedPageInParent part va accespg s = true).
 {   apply Hcons with pd;trivial.
    rewrite <- Haccespg.
    apply getAccessibleMappedPageMapMMUPage1 with  part phyDescChild
    vaChild entry level;trivial.
    * apply Hconfdiff;trivial. intuition.
    * apply isConfigTable with vaChild;trivial.
      intros;subst;split;trivial.
    * apply Hconfdiff;trivial. intuition.
    * symmetry;trivial.
    * intros;subst;split;trivial.
    * intuition. }
unfold isAccessibleMappedPageInParent in *.
assert(Hsh2 : getSndShadow part (memory s') =
getSndShadow part (memory s)).
apply getSndShadowMapMMUPage with entry;trivial.
rewrite Hsh2 in *;clear Hsh2.
case_eq( getSndShadow part (memory s));
[intros sh2 Hsh2| intros Hsh2];rewrite Hsh2 in *;
try now contradict Hisaccess.
assert(Hvirteq :getVirtualAddressSh2 sh2 s va = getVirtualAddressSh2 sh2 s' va).
apply getVirtualAddressSh2MapMMUPage with entry
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
vaChild presentvaChild level part;trivial.
unfold consistency ;intuition.
rewrite <- Hvirteq.
case_eq(getVirtualAddressSh2 sh2 s va);[intros vaInParent HvaInParent |
intros HvaInParent];rewrite HvaInParent in *;try now contradict Hisaccess.
assert(Hparent' : getParent part (memory s')  = getParent part (memory s)).
{ apply getParentMapMMUPage with entry;trivial. }
rewrite Hparent' in *;clear Hparent'.
case_eq( StateLib.getParent  part (memory s));
[intros parent HParent | intros HParent];rewrite HParent in *;
try now contradict Hisaccess.
assert(Hpd' : StateLib.getPd parent (memory s) =
        StateLib.getPd parent (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdMapMMUPage with entry;trivial. }
rewrite <- Hpd' in *. clear Hpd'. 
case_eq( StateLib.getPd  parent (memory s));
[intros pdpart Hpdpart | intros Hpdpart];rewrite Hpdpart in *;
try now contradict Hisaccess.
assert(Hor2:parent = phyDescChild \/ parent <> phyDescChild) by apply pageDecOrNot.
destruct Hor2 as [Ho2 | Hor2].
* subst.
  clear Hcons.
 assert(Hmykey3 : getMappedPage pdChildphy s vaChild = SomeDefault).
 { apply getMappedPageNotPresent with ptVaChildpd phyDescChild;intuition;
   subst;trivial. rewrite negb_true_iff in *. subst;trivial. }
 assert(Hpdeq : pdpart = pdChildphy).
  { symmetry. apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
  subst.
 case_eq(getAccessibleMappedPage pdChildphy s vaInParent);
 [intros somepage Hsomepage | intros Hsomepage | intros Hsomepage];rewrite Hsomepage in *;
 try now contradict Hisaccess.
 assert(Hmapped : getMappedPage pdChildphy s vaInParent = SomePage somepage).
 apply accessiblePAgeIsMapped;trivial.
 assert(Hnewgoal: getAccessibleMappedPage pdChildphy s' vaInParent = SomePage somepage).
 { apply getMappedPageKeepsAnyAccessibleMappedPage with phyDescChild entry
    level (currentPartition s);trivial. 
   * symmetry;trivial.
   * assert(Hlegit: negb presentvaChild = true) by trivial.
     apply negb_true_iff in Hlegit. subst;trivial.
   * apply pdPartNotNull with phyDescChild s;trivial.
   * apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
     intros;subst;split;trivial. }
 rewrite Hnewgoal.
 trivial.
   
*
 assert(Hi2 : In parent (getPartitions multiplexer s)).
 { assert(Hparentpart : parentInPartitionList s) by trivial.
    unfold parentInPartitionList in Hparentpart.
    apply Hparentpart with part;trivial.
    apply nextEntryIsPPgetParent;trivial. }
assert(Haccesseq : getAccessibleMappedPage pdpart s vaInParent =
getAccessibleMappedPage pdpart s' vaInParent).
{ apply getAccessibleMappedPageMapMMUPage1 with 
  parent phyDescChild
  vaChild entry level;trivial.
  * apply Hconfdiff;trivial. 
     intuition.
  * apply isConfigTable with vaChild;trivial.
    intros;subst;split;trivial.
  * apply Hconfdiff;trivial. intuition.
  * symmetry;trivial.
  * intros;subst;split;trivial.
  * intuition. }

rewrite <- Haccesseq;trivial.
Qed.

Lemma getAncestorsMapMMUPage  ( partition : page) entry s table idx phyVaChild w r e:
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->
getAncestors partition s = getAncestors partition {|
      currentPartition := currentPartition s;
      memory :=
(add table idx
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex) |}.
Proof.
intros.
revert partition.
unfold getAncestors.
induction (nbPage + 1);simpl in *;intros;trivial.
assert(Hparent : getParent partition (memory s) =
getParent partition (add table idx
           (PE
              {|
              read := r;
              write := w;
              exec := e;
              present := true;
              user := true;
              pa := phyVaChild |}) (memory s) beqPage beqIndex) ).
symmetry. apply getParentMapMMUPage with entry;trivial.
rewrite <- Hparent. clear Hparent.
destruct(getParent partition (memory s));trivial.
f_equal.
apply IHn.
Qed.


Lemma noCycleInPartitionTreeMapMMUPage 
 s ptVaChildpd idxvaChild phyVaChild r w e
  entry 
 (vaChild vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD  pdChildphy phyDescChild :page)
  ( presentvaChild :bool)
(level :level)  :

let s' :={|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
noCycleInPartitionTree s ->
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
noDupPartitionTree s ->
partitionDescriptorEntry s -> 
isPresentNotDefaultIff s -> noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd 
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd  
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> (forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 

noCycleInPartitionTree s'.
Proof.
intros s' Hnewcons2 Hnewcons  Hnocycle .
intros.
unfold noCycleInPartitionTree in *.
intros ancestor part Hpart Hances.
assert(Hparts :  In part (getPartitions multiplexer s)).
{ apply getPartitionsMapMMUPage with entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd idxvaChild
  phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
  level;trivial. }
assert(Hanc :  getAncestors part s = getAncestors part s').
{ apply getAncestorsMapMMUPage with entry; trivial. }
apply Hnocycle;trivial.
rewrite Hanc;trivial.
Qed.

Lemma configTablesAreDifferentMapMMUPage 
 s ptVaChildpd idxvaChild phyVaChild r w e
  entry 
 (vaChild vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD  pdChildphy phyDescChild :page)
  ( presentvaChild :bool)
(level :level)  :

let s' :={|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
                      wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
configTablesAreDifferent s -> 
consistency s -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
noDupPartitionTree s ->
partitionDescriptorEntry s -> 
isPresentNotDefaultIff s -> noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd 
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd  
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> (forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
configTablesAreDifferent s'.
Proof.
intros s' Hnewcons2 Hnewcons Hcons.
intros.
move Hcons at bottom.
unfold configTablesAreDifferent in *.
intros part1 part2 Hpart1 Hpart2 Hdist.
assert(Hparts : forall part, In part (getPartitions multiplexer s') ->  In part (getPartitions multiplexer s)).
{ intros. apply getPartitionsMapMMUPage with entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd idxvaChild
  phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
  level;trivial. }
assert(Hconfigs : forall part, In part (getPartitions multiplexer s) -> 
getConfigPages part s = getConfigPages part s').
{ intros. 
  assert(Hor : phyDescChild = part  \/ phyDescChild <> part) by apply pageDecOrNot. 
  destruct Hor as [Hor | Hor].
  - subst. 
    apply getConfigPagesMapMMUPage1 with entry pdChildphy
    (currentPartition s) presentvaChild vaChild level;trivial.
    symmetry;trivial.
  -  apply getConfigPagesMapMMUPage with phyDescChild entry;trivial.
    + apply isConfigTable with vaChild;trivial.
      intros;subst;split;trivial.
    +  assert(Hconfdiff : configTablesAreDifferent s)by trivial.
      apply Hconfdiff;trivial. }
rewrite <- Hconfigs;[|apply Hparts;trivial].

rewrite <- Hconfigs;[|apply Hparts;trivial]. 
apply Hcons;trivial;apply Hparts;trivial.
Qed.

Lemma isChildMapMMUPage 
 s ptVaChildpd idxvaChild phyVaChild r w e
  entry 
 (vaChild vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD  pdChildphy phyDescChild :page)
  ( presentvaChild :bool)
(level :level)  :
let s' :={|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
isChild s ->  
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
parentInPartitionList s -> 
noDupPartitionTree s ->
partitionDescriptorEntry s -> 
isPresentNotDefaultIff s -> noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd 
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd  
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> (forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
isChild s'.
Proof.
intros s' Hnewcons2 Hnewcons Hcons.
intros.
move Hcons at bottom.
unfold isChild in *.
intros part parent Hpart Hparent.
assert(Hparts :  In part (getPartitions multiplexer s)).
{ intros. apply getPartitionsMapMMUPage with entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd idxvaChild
  phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
  level;trivial. }
assert(Hpernt : getParent part (memory s') = getParent part (memory s)).
{ apply getParentMapMMUPage with entry;trivial. }
rewrite Hpernt in *.  
apply getChildrenMapMMUPage1 with pdChildphy  (currentPartition s)
presentvaChild vaChild phyDescChild level entry;trivial.
assert(Hconsparent : parentInPartitionList s) by trivial.
unfold parentInPartitionList in *.
apply Hconsparent with part;trivial.
apply nextEntryIsPPgetParent;trivial.
apply Hcons;trivial.
Qed.

Lemma isParentMapMMUPage 
 s ptVaChildpd idxvaChild phyVaChild r w e
  entry 
 (vaChild vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD  pdChildphy phyDescChild :page)
  ( presentvaChild :bool)
(level :level)  :
let s' :={|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
isParent s ->  
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
parentInPartitionList s -> 
noDupPartitionTree s ->
partitionDescriptorEntry s -> 
isPresentNotDefaultIff s -> noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd 
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd  
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> (forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
isParent s'.
Proof.
intros s'  Hnewcons2 Hnewcons Hcons.
intros.
move Hcons at bottom.
unfold isParent in *.
intros part parent Hpart Hparent.
assert(Hparts :  In parent (getPartitions multiplexer s)).
{ intros. apply getPartitionsMapMMUPage with entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd idxvaChild
  phyVaChild pdChildphy r w e phyDescChild vaChild presentvaChild
  level;trivial. }
assert(Hchild :  In part (getChildren parent s)).
{ intros. apply getChildrenMapMMUPage with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
  phyVaChild r w e pdChildphy (currentPartition s) presentvaChild vaChild
  phyDescChild level entry;trivial;subst;trivial. }
 assert(Hpernt : getParent part (memory s') = getParent part (memory s)).
{ apply getParentMapMMUPage with entry;trivial. }
rewrite Hpernt in *.  
apply Hcons;trivial.
Qed.

Lemma  isPresentNotDefaultIffMapMMUPage  s phyVaChild  ptVaChildpd idxvaChild r w e 
isnotderiv accessiblesrc presentmap  presentvaChild idxvaInCurPart ptVaInCurPartpd
entry
:
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
entryPresentFlag ptVaInCurPartpd idxvaInCurPart presentmap s -> 
isEntryPage ptVaInCurPartpd idxvaInCurPart phyVaChild s -> 
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
isPresentNotDefaultIff s -> 
isPresentNotDefaultIff {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
unfold isPresentNotDefaultIff.
intros Hlookup Hi1 Hi2 Hlegit Hi4.
simpl.
intros.
repeat rewrite andb_true_iff in Hlegit.
assert(Hmykey : phyVaChild <> defaultPage). 
{ generalize (Hi4  ptVaInCurPartpd idxvaInCurPart);clear Hi4;intros Hi4.
  destruct Hi4 as (Hi4 & Hi5).
  unfold entryPresentFlag in *.
  unfold isEntryPage in *.
  unfold StateLib.readPresent in *.
  unfold StateLib.readPhyEntry in *.
  case_eq(lookup ptVaInCurPartpd idxvaInCurPart (memory s) beqPage beqIndex);
  [intros v Hv | intros Hv];rewrite Hv in *;try now contradict Hi2.
  destruct v;subst;try now contradict Hi2.
  unfold not;intros.
  assert(Some (present p) = Some false).
  { apply Hi5.
  f_equal;trivial. }
  
intuition;subst.
  inversion H2. 
  destruct (present p).
  now contradict H4.
  now contradict H4. }  
 assert(Hor : (  (table <> ptVaChildpd \/
idx <>
idxvaChild) \/  (~ (table <> ptVaChildpd \/
idx <>
idxvaChild)))).
{ apply classic. }
destruct Hor as [Hor | Hor];trivial.
+ assert(Hpres :StateLib.readPresent table idx
  (add ptVaChildpd idxvaChild
     (PE
        {|
        read := r;
        write := w;
        exec := e;
        present := true;
        user := true;
        pa := phyVaChild |}) (memory s) beqPage beqIndex)=
         StateLib.readPresent table idx (memory s) ).
   symmetry.
  apply readPresentMapMMUPage with entry;trivial.
  rewrite Hpres.
  assert(Hacces :StateLib.readPhyEntry table idx
  (add ptVaChildpd idxvaChild
     (PE
        {|
        read := r;
        write := w;
        exec := e;
        present := true;
        user := true;
        pa := phyVaChild |}) (memory s) beqPage beqIndex)=
         StateLib.readPhyEntry table idx (memory s) ).
   symmetry.
  apply readPhyEntryMapMMUPage with entry;trivial.
  rewrite Hacces.
  trivial.
+
apply not_or_and in Hor.
destruct Hor as(Hi5 & Hi6) .
subst.
apply NNPP in Hi5.
apply NNPP in Hi6.
rewrite Hi6 in *. clear Hi6.
subst.
assert(Htrue: beqPairs (ptVaChildpd, idxvaChild) (ptVaChildpd, idxvaChild) beqPage
           beqIndex = true).
  { apply beqPairsTrue; split;trivial. }
split.
* intros. unfold StateLib.readPresent in *.
  simpl in *.
  rewrite Htrue in *.
  simpl in *.
  inversion H.
* intros. 
  intros. unfold StateLib.readPresent.
  unfold StateLib.readPhyEntry in H.
    simpl in *.
  rewrite Htrue in *.
  simpl in *.
  inversion H;subst.
  now contradict Hmykey.
Qed.

Lemma multiplexerWithoutParentMapMMUPage s phyVaChild  ptVaChildpd idxvaChild r w e 
      
entry
:
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
multiplexerWithoutParent s ->
multiplexerWithoutParent  {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
unfold multiplexerWithoutParent.
intros.
simpl.
rewrite <- H0.
apply getParentMapMMUPage with entry;trivial.
Qed.

Lemma noDupPartitionTreeMapMMUPage s ptVaChildpd idxvaChild phyVaChild r w e
  entry 
 (vaChild vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD  pdChildphy phyDescChild :page)
  ( presentvaChild :bool)
(level :level)  :
let s' :={|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
noDupPartitionTree s -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
noDupPartitionTree s ->
partitionDescriptorEntry s -> 
isPresentNotDefaultIff s -> noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd 
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd  
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> (forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
noDupPartitionTree s'.
Proof.
intros s' Hnewcons Hnocycle .
intros.
unfold noDupPartitionTree in *.
move Hnocycle at bottom.
assert(Hpartseq : getPartitions multiplexer s = getPartitions multiplexer s').
apply getPartitionsMapMMUPageEq with entry
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
vaChild presentvaChild level;trivial.
rewrite <- Hpartseq;trivial.
Qed.

Lemma vaIsDerived currentPart shadow1 (ptSh1ChildFromSh1 : page) s : 
    consistency s ->
    In currentPart (getPartitions multiplexer s) -> 
     (defaultPage =? ptSh1ChildFromSh1) = false  -> 
    (exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 (StateLib.getIndexOfAddr shadow1 fstLevel) va s /\
        beqVAddr defaultVAddr va = false) -> 
     (forall idx : index,
     StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
     isVE ptSh1ChildFromSh1 idx s /\ getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) -> 
    isDerived currentPart shadow1 s .
Proof.
intros Hcons Hparts Hptfromsh1notnull Hii Hi. 

destruct Hi with (StateLib.getIndexOfAddr shadow1 fstLevel) as 
(Hve & Hgetve);trivial.

clear Hi.
destruct Hii as (va0 & Hvae & Hveq).
unfold isDerived.
unfold getTableAddrRoot in *.
destruct Hgetve as (_ & Hgetve).
assert(Hcursh1 :(exists entry : page, nextEntryIsPP currentPart sh1idx entry s /\ entry <> defaultPage)).
assert(Hpde :  partitionDescriptorEntry s).
unfold consistency in *.
intuition.
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
abstract omega.
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
trivial.
Qed.
 Lemma isDerivedcheckVAddrsEqualityTrue part vaInCurrentPartition va level s :
    StateLib.getNbLevel = Some level -> 
    isDerived  part vaInCurrentPartition s -> 
    checkVAddrsEqualityWOOffset nbLevel vaInCurrentPartition va level =
       true -> 
    isDerived part va s.
    Proof.
    unfold isDerived.
    destruct (getFstShadow part (memory s));trivial.
    intros.
    unfold getVirtualAddressSh1 in *.
    rewrite H in *.
    assert(getIndirection p vaInCurrentPartition level (nbLevel - 1) s  =
    getIndirection p va level (nbLevel - 1) s ).
    apply getIndirectionEq;trivial.
    apply getNbLevelLt;trivial.
    rewrite H2 in *.
    assert((StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) = 
    (StateLib.getIndexOfAddr va fstLevel)).
    apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level;trivial.
    apply fstLevelLe.
    apply getNbLevelLt;trivial.
    rewrite H3 in *;trivial.
    Qed.
              
Lemma physicalPageNotDerivedMapMMUPage s entry vaInCurrentPartition vaChild 
currentShadow  idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild isnotderiv currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level r w e  : 
let s' :={|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
physicalPageNotDerived s -> 
negb presentDescPhy = false -> 
negb presentvaChild = true ->

isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild (currentPartition s)
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild (negb isnotderiv) currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level /\
StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
Some vaInCurrentPartition /\
isPartitionFalse ptVaInCurPart idxvaInCurPart s -> 
 (forall child : page, 
    In child (getChildren (currentPartition s) s) -> ~ In phyVaChild (getMappedPages child s)) -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
In phyDescChild (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
In phyDescChild (getChildren (currentPartition s) s) ->
physicalPageNotDerived s ->
physicalPageNotDerived s'.
Proof.
intros s' Hnotderiv.
intros.
assert(Hxx: forall child : page,
     In child (getChildren (currentPartition s) s) ->
     ~ In phyVaChild (getMappedPages child s)) by trivial.
     
unfold propagatedPropertiesAddVaddr in *.
intuition.
unfold consistency in *.
intuition.
rewrite negb_true_iff in *;rewrite negb_false_iff in *;subst.
assert(Hlegit : isnotderiv && accessiblesrc && presentmap && negb false = true) by trivial.
repeat rewrite andb_true_iff in Hlegit.
intuition;subst.
assert(Hlevel : StateLib.getNbLevel = Some level) by (symmetry;trivial).
unfold physicalPageNotDerived in *.
assert(Hcurrpd : nextEntryIsPP (currentPartition s) PDidx currentPD s) by trivial.
move Hnotderiv at bottom.
intros parent va pdParent pageParent 
Hparent Hpdparent Hnotderivp Hmapparent.
intros child pdchild vaInChild pageChild
Hchild Hpdchild Hmapchild.
assert(Hpartseq :getPartitions multiplexer s = getPartitions multiplexer s').
{ apply getPartitionsMapMMUPageEq  with entry
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
vaChild false level;trivial.
intros;subst;split;trivial. }
rewrite <- Hpartseq in *.
assert(Hnocycle : noCycleInPartitionTree s) by trivial.
assert(Hpd : forall part, StateLib.getPd part (memory s') =
StateLib.getPd part (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
rewrite Hpd in *.
assert(Hchildeq : getChildren parent s' = getChildren parent s).
{ apply getChildrenMapMMUPageEq with pdChildphy  (currentPartition s)
  false vaChild phyDescChild level entry;trivial. }
 rewrite Hchildeq in *. 
assert(Hisparent: isParent s) by trivial.
assert(Hparentchild : StateLib.getParent child (memory s) = Some parent).
{ apply Hisparent;trivial. }
assert(Htrue : parent <> child).
{ apply Hnocycle.
  apply childrenPartitionInPartitionList with parent;trivial.
  unfold getAncestors.
  induction (nbPage );simpl;rewrite Hparentchild;simpl;left;trivial. } 
assert(Hderiv :~ isDerived parent va s).
{ unfold isDerived in *.  
  assert(Hsh1 :  StateLib.getFstShadow parent (memory s') =
  StateLib.getFstShadow parent (memory s)).
  { intros. apply getFstShadowMapMMUPage with entry;trivial. }
  rewrite Hsh1 in *. clear Hsh1.
  case_eq(getFstShadow parent (memory s));[intros sh1 Hsh1  | intros Hsh1];
  rewrite Hsh1 in *;[|intuition].
  assert (Hgetva : getVirtualAddressSh1 sh1 s va = getVirtualAddressSh1 sh1 s' va).
  { apply getVirtualAddressSh1MapMMUPage with entry vaInCurrentPartition ptVaInCurPartpd currentPD
   pdChildphy phyDescChild vaChild false level parent;trivial.
   unfold consistency ;intuition.
   intros;subst;split;trivial. }
  rewrite Hgetva;trivial. }
assert(Hor3:  
( phyDescChild <> child /\ phyDescChild <> parent) \/
  (phyDescChild = child \/ phyDescChild = parent)).
{ clear. destruct phyDescChild;destruct child ; destruct parent.
  simpl in *.
  assert(  (p <> p0 /\ p <> p1) \/
  (p = p0 \/ p = p1)) by omega.
  destruct H. left. 
  destruct H.
  split. 
  unfold not;intros.
  inversion H1.
  subst.
  omega.
  unfold not;intros.
  inversion H1.
  subst.
  omega.
  right. 
  destruct H. 
  left. 
  subst.
  f_equal.
  apply proof_irrelevance.
  right. 
  subst;f_equal.
  apply proof_irrelevance. }
clear Hchildeq Hpartseq Hpd.
assert (Hnewmap : getMappedPage pdChildphy s' vaChild = SomePage phyVaChild).
{  assert(Hlookup : lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s)
       beqPage beqIndex = Some (PE entry)) by trivial.
  assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial. 
  assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
          (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some defaultPage).
  { assert(Hcons1 : isPresentNotDefaultIff s).
    unfold consistency in *. intuition.            
    apply Hcons1.
    subst.
    unfold entryPresentFlag in *. 
    unfold StateLib.readPresent.
    rewrite Hlookup in *.
    f_equal.
    subst.
    assert (Hentrypresent : negb (present entry) = true).
    { assert (Hii : false = present entry) by trivial.
       destruct (present entry) ;subst;try now contradict Hii.
       trivial. }
    apply negb_true_iff in Hentrypresent.
    subst. trivial. }
  assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
                (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some phyVaChild).
  { unfold StateLib.readPhyEntry. 
    cbn.
    assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
    (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
    beqIndex = true); intros.
    rewrite <- beqPairsTrue;split;trivial.
    subst.
    rewrite Hpairs.
    simpl;trivial. }
  apply getMappedPageGetTableRoot with ptVaChildpd phyDescChild;
  trivial;fold s'. 
  + intros. 
  split. 
  apply isPEMapMMUPage with entry;trivial.
  subst;trivial.
  assert(Htblroot : getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
  unfold getTableAddrRoot in Htblroot.
  destruct Htblroot as (Hidxs & Htblroot).
  split;trivial.
  intros.
  rename Hpdchild into Hpdchild1.
  assert(Hpdchild :nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Htblroot in Hpdchild;clear Htblroot.
  move Hpdchild at bottom.
  destruct Hpdchild as (nbL & HnbL & stop & Hstop & Hind1).
  exists nbL ; split ; trivial.
  exists stop;split;trivial.
  assert(tableroot = pdChildphy). 
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  phyVaChild r w  e;trivial.
  subst. trivial.
  apply nextEntryIsPPgetPd;trivial.
  subst .
  revert Hind1.

  revert Htrue1 Htrue2 Hlookup Hdefaut.
  clear. 
  intros.
   apply getIndirectionMapMMUPage with entry;trivial;subst;trivial.
 + unfold isEntryPage, StateLib.readPhyEntry in *. 
   destruct(lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
             (memory s') beqPage beqIndex);trivial;try now contradict Htrue2.
   destruct v;try now contradict Htrue2.
   inversion Htrue2;trivial.
 + unfold entryPresentFlag. 
   cbn.
   subst.
   assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
      beqIndex = true).
   apply beqPairsTrue;split;trivial.
   rewrite Hpairs.
   simpl;trivial.
       
+ apply  nextEntryIsPPMapMMUPage with entry;trivial. } 
destruct Hor3 as [(Hi1 & Hi2) | Hor3].
+ apply Hnotderiv with parent va pdParent child pdchild vaInChild;trivial.
  - rewrite <- Hmapparent.
    apply getMappedPageMapMMUPageEq with parent phyDescChild vaChild entry level;trivial.
    apply isConfigTable  with vaChild;trivial.
    intros; split; 
    subst;trivial. trivial.
    assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
    apply Hconfigdiff;trivial.
    intuition.
    intros;subst;trivial.
  - rewrite <- Hmapchild.
    apply getMappedPageMapMMUPageEq with child phyDescChild vaChild entry level;trivial.
    apply isConfigTable  with vaChild;trivial.
    intros; split; 
    subst;trivial. trivial.
    assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
    apply Hconfigdiff;trivial.
    apply childrenPartitionInPartitionList with parent;trivial.
    intuition.
    intros;subst;trivial.
    apply childrenPartitionInPartitionList with parent;trivial.
+ destruct Hor3 as [Hor | Hor].
  - subst child.
    assert(Hparenteq : parent = currentPartition s).
    { apply getParentNextEntryIsPPEq with phyDescChild s;trivial.
      apply nextEntryIsPPgetParent;trivial.
      apply Hisparent;trivial.
    }
    subst parent.
    assert( currentPD = pdParent ).
    apply getPdNextEntryIsPPEq with (currentPartition s) s;trivial.
    subst pdParent.
    assert(pdChildphy = pdchild).
    apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
    subst pdchild.
    assert(Hpameq : getMappedPage currentPD s va = getMappedPage currentPD s' va ).
    { apply getMappedPageMapMMUPageEq with (currentPartition s)  phyDescChild vaChild
      entry level;trivial.
      apply isConfigTable with vaChild;trivial.
      intros; split; 
      subst;trivial.
      assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
      apply Hconfigdiff;trivial.
      intuition.
      intros;subst;split;trivial.
      intuition. }
    rewrite <- Hpameq in *.
    assert(Hmapinparent : getMappedPage currentPD s vaInCurrentPartition = SomePage phyVaChild).
      { apply getMappedPageGetTableRoot with ptVaInCurPartpd
      (currentPartition s);trivial.
      intros;subst;split;trivial. }
    assert(Hor : checkVAddrsEqualityWOOffset nbLevel vaInCurrentPartition va level = true \/
    checkVAddrsEqualityWOOffset nbLevel vaInCurrentPartition va level = false ).
    { destruct (checkVAddrsEqualityWOOffset nbLevel vaInCurrentPartition va level);intuition. }
    destruct Hor as [Hor1 | Hor1].
    * unfold not;intros;subst.
      assert(Hmapeq : getMappedPage currentPD s vaInCurrentPartition = getMappedPage currentPD s va).
      { apply getMappedPageEq with level;trivial.  }      
      rewrite Hmapeq in *. 
      rewrite Hmapparent in Hmapinparent.
      inversion Hmapinparent;subst.
      assert(Hmykey : isDerived (currentPartition s) vaInCurrentPartition s).
      apply vaIsDerived with ptVaInCurPart;trivial.
      unfold consistency;intuition.
      exists descChild;split;trivial.
      intros;subst;split;trivial.
      assert(Hmykey2 : isDerived (currentPartition s) va s).
      apply isDerivedcheckVAddrsEqualityTrue with vaInCurrentPartition level;
      trivial.
      now contradict Hmykey2.
    * assert(Hmykey1 : pageParent <> phyVaChild).
      apply twoMappedPagesAreDifferent with va vaInCurrentPartition
      currentPD level s;trivial.
      assert(Hnodup : noDupMappedPagesList s) by trivial.
      unfold noDupMappedPagesList in *.
      apply Hnodup in Hparent.
      unfold getMappedPages in *.
      rewrite Hpdparent in Hparent;trivial.
      rewrite <-  Hor1.
      apply checkVAddrsEqualityWOOffsetPermut;trivial.
      assert(Hor : checkVAddrsEqualityWOOffset nbLevel vaChild vaInChild level = true \/
    checkVAddrsEqualityWOOffset nbLevel vaChild vaInChild  level = false ).
    { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild vaInChild  level);intuition. }
    destruct Hor as [Hor | Hor].
    { assert(getMappedPage pdChildphy s' vaInChild = SomePage phyVaChild).
      { rewrite <- Hnewmap.
        apply getMappedPageEq with level;trivial.
        rewrite <- Hor. 
        apply checkVAddrsEqualityWOOffsetPermut.      
       }
    rewrite H in Hmapchild.
    inversion Hmapchild.
    subst;trivial. }
    { apply Hnotderiv with (currentPartition s) va currentPD
        phyDescChild pdChildphy vaInChild;trivial.
      apply getMappedPageMapMMUPage with  phyVaChild ptVaChildpd r w e vaChild 
        phyDescChild level entry;trivial.
      unfold consistency ;intuition. }
  - subst parent.
    assert(pdChildphy = pdParent).
    apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
    subst pdParent.
    assert(Hmykey : getMappedPage pdchild s vaInChild =
      getMappedPage pdchild s' vaInChild).
    { apply getMappedPageMapMMUPageEq with child phyDescChild vaChild entry level;trivial.
      + apply isConfigTable with vaChild;trivial.
        intros;subst;split;trivial.
      + assert(Hconfig :   configTablesAreDifferent s) by trivial.
        apply Hconfig;intuition.
        apply childrenPartitionInPartitionList with phyDescChild;trivial.
      + intros;subst;split;trivial.
      + apply childrenPartitionInPartitionList with phyDescChild;trivial. }
     rewrite <- Hmykey in *. clear Hmykey.
     assert(Hor : checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/
    checkVAddrsEqualityWOOffset nbLevel vaChild va  level = false ).
    { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild va  level);intuition. }
    destruct Hor as [Hor | Hor].
    * assert (Hmykey : getMappedPage pdChildphy s' vaChild = getMappedPage pdChildphy s' va).
      { apply getMappedPageEq with level;trivial. }
     rewrite Hmykey in *.   
    rewrite Hnewmap in *.
    inversion Hmapparent.
    subst pageParent.
    unfold not;intros;subst pageChild. 
    assert(Hmykey1 : In phyVaChild (getMappedPages phyDescChild s)).
    { assert(Hvs : verticalSharing s) by trivial.
      unfold verticalSharing in Hvs.
      assert(Hvsaux : incl (getUsedPages child s) (getMappedPages phyDescChild s)).
      apply Hvs;trivial.
      clear Hvs. unfold incl in Hvsaux .
      apply Hvsaux;trivial.
      unfold getUsedPages.
      apply in_app_iff;right.
      unfold getMappedPages. 
      rewrite Hpdchild .
      unfold  getMappedPagesAux.
      apply filterOptionInIff.
      apply in_map_iff.
      unfold getMappedPagesOption.
      assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
      StateLib.checkVAddrsEqualityWOOffset nbLevel vaInChild va1 ( CLevel (nbLevel -1) ) = true )
      by apply AllVAddrWithOffset0.
      destruct Heqvars as (va1 & Hva1 & Hva11).  
      exists va1.
      split;trivial.
      rewrite <- Hmapchild.
      symmetry.
      apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
      apply getNbLevelEqOption.
       }
     
     assert(Hmykey2 :~ In phyVaChild (getMappedPages phyDescChild s)).
     { unfold not;intros. apply Hxx with phyDescChild;trivial. }
    now contradict Hmykey2.
  * apply Hnotderiv with phyDescChild va pdChildphy child pdchild vaInChild;
     trivial.
    apply getMappedPageMapMMUPage with  phyVaChild ptVaChildpd r w e vaChild 
        phyDescChild level entry;trivial.
      unfold consistency ;intuition.
Qed.
Lemma getVirtualAddressSh1GetTableRoot:
forall (ptsh2 descParent  sh2  : page) 
    (vaInAncestor va: vaddr) (s : state) L,
(forall idx : index,
  StateLib.getIndexOfAddr va fstLevel = idx ->
   isVE ptsh2 idx s /\ getTableAddrRoot ptsh2 sh1idx descParent va s) ->
(defaultPage =? ptsh2) = false ->
isEntryVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s -> 
StateLib.getFstShadow descParent (memory s) = Some sh2 -> 
Some L = StateLib.getNbLevel ->
getVirtualAddressSh1 sh2 s va = Some vaInAncestor.
Proof. 
intros ptsh2 descParent sh2 vaInAncestor va  s L.
intros Hget Hnotnull Hisva Hsh2 HL.

unfold getVirtualAddressSh1.
rewrite <- HL.
destruct Hget with (StateLib.getIndexOfAddr va fstLevel)
as (Hpe2 & Hroot2);trivial.
clear Hget.
unfold getTableAddrRoot in Hroot2.
destruct Hroot2 as (_ & Htableroot).
rewrite <- nextEntryIsPPgetFstShadow in *. 
apply Htableroot in Hsh2.
clear Htableroot.
destruct Hsh2 as (nbL & HnbL & stop & Hstop & Hind ).
subst.
rewrite <- HnbL in *.
inversion HL.
subst. 
assert(Hnewind :getIndirection sh2 va nbL (nbLevel - 1) s
= Some ptsh2).
apply getIndirectionStopLevelGT2 with (nbL +1);try omega;trivial.
apply getNbLevelEq in HnbL.
subst. apply nbLevelEq.
rewrite Hnewind.
rewrite Hnotnull.
unfold isEntryVA in *.
unfold StateLib.readVirEntry.
destruct(lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) 
(memory s) beqPage beqIndex );
try now contradict Hisva.
destruct v; try now contradict Hisva.
f_equal;trivial.
Qed.
Lemma getVirtualAddressSh1Eq vaChild va level s sh1: 
StateLib.getNbLevel = Some level -> 
 checkVAddrsEqualityWOOffset nbLevel vaChild va level = true -> 
getVirtualAddressSh1 sh1 s va = getVirtualAddressSh1 sh1 s vaChild.
Proof.
intros.
unfold getVirtualAddressSh1 in *.
rewrite H in *.
assert(getIndirection sh1 vaChild level (nbLevel - 1) s  =
getIndirection sh1 va level (nbLevel - 1) s ).
apply getIndirectionEq;trivial.
apply getNbLevelLt;trivial.
rewrite H1 in *.
assert((StateLib.getIndexOfAddr vaChild fstLevel) = 
(StateLib.getIndexOfAddr va fstLevel)).
apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level;trivial.
apply fstLevelLe.
apply getNbLevelLt;trivial.
rewrite H2 in *;trivial.
Qed.

Lemma getVirtualAddressSh2Eq vaChild va level s sh1: 
StateLib.getNbLevel = Some level -> 
 checkVAddrsEqualityWOOffset nbLevel vaChild va level = true -> 
getVirtualAddressSh2 sh1 s va = getVirtualAddressSh2 sh1 s vaChild.
Proof.
intros.
unfold getVirtualAddressSh2 in *.
rewrite H in *.
assert(getIndirection sh1 vaChild level (nbLevel - 1) s  =
getIndirection sh1 va level (nbLevel - 1) s ).
apply getIndirectionEq;trivial.
apply getNbLevelLt;trivial.
rewrite H1 in *.
assert((StateLib.getIndexOfAddr vaChild fstLevel) = 
(StateLib.getIndexOfAddr va fstLevel)).
apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level;trivial.
apply fstLevelLe.
apply getNbLevelLt;trivial.
rewrite H2 in *;trivial.
Qed.

Lemma wellFormedFstShadowMapMMUPage  s entry vaInCurrentPartition vaChild currentPart
currentShadow  idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild isnotderiv currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level r w e  :
let s' :={|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
negb presentDescPhy = false -> 
negb presentvaChild = true ->
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild (negb isnotderiv) currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level /\
StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
Some vaInCurrentPartition /\
isPartitionFalse ptVaInCurPart idxvaInCurPart s -> 
 (forall child : page, 
    In child (getChildren currentPart s) -> ~ In phyVaChild (getMappedPages child s)) -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
wellFormedFstShadow s ->
wellFormedFstShadow s'.
Proof.
intros s'.
unfold propagatedPropertiesAddVaddr.
intuition.
unfold consistency in *. intuition;subst.
assert(Hcons : wellFormedFstShadow s) by trivial.
unfold wellFormedFstShadow in Hcons.
unfold wellFormedFstShadow.
intros partition Hpart va pg pd sh1 Hpd Hsh1 Hmap.
assert(Hchild : In phyDescChild (getPartitions multiplexer s)).
{ unfold consistency in *.
  apply childrenPartitionInPartitionList with  (currentPartition s);intuition;subst;trivial. }
rewrite negb_true_iff in *;rewrite negb_false_iff in *;subst.
assert(Hlegit : isnotderiv && accessiblesrc && presentmap && negb false = true) by trivial.
repeat rewrite andb_true_iff in Hlegit.
intuition.
assert(Hlevel : StateLib.getNbLevel = Some level) by (symmetry;trivial).
assert(Hpds : forall part, StateLib.getPd part (memory s') =
StateLib.getPd part (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
rewrite Hpds in *;clear Hpds.
assert(Hsh1s :  StateLib.getFstShadow partition (memory s') =
StateLib.getFstShadow partition (memory s)).
{ intros. apply getFstShadowMapMMUPage with entry;trivial. }
rewrite Hsh1s in *; clear Hsh1s.
assert(Hparts : In partition (getPartitions multiplexer s)).
{ apply getPartitionsMapMMUPage with entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd 
  (StateLib.getIndexOfAddr vaChild fstLevel)
  phyVaChild pdChildphy r w e phyDescChild vaChild false
  level;subst;trivial. intros;subst;split;trivial. }
  
subst.
assert(Hor : partition= phyDescChild \/ partition <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
+ subst partition.
  assert(pdChildphy = pd).
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  subst pd.
  assert(Hor : checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/
    checkVAddrsEqualityWOOffset nbLevel vaChild va  level = false ).
  { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild va  level);intuition. }
  destruct Hor as [Hor | Hor].
  - exists defaultVAddr.
   assert(Heqtmp:(StateLib.getIndexOfAddr vaChild fstLevel) = (StateLib.getIndexOfAddr va fstLevel)).
  { apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level;trivial.
    apply fstLevelLe.
    apply getNbLevelLt;trivial. }
    assert(Heq : getVirtualAddressSh1 sh1 s va = getVirtualAddressSh1 sh1 s' va).
  {  apply getVirtualAddressSh1MapMMUPage with entry vaInCurrentPartition ptVaInCurPartpd currentPD
   pdChildphy phyDescChild vaChild false level phyDescChild;trivial.
   unfold consistency ;intuition.
   subst. trivial.
   intros;subst;split;trivial. }
   rewrite <-  Heq;clear Heq.
   assert(Hnewpro : getVirtualAddressSh1 sh1 s vaChild = Some defaultVAddr).
     assert(Hnone : getMappedPage pdChildphy s vaChild = SomeDefault).
  { apply getMappedPageNotPresent with  ptVaChildpd  phyDescChild;trivial.
    intros;subst;split;trivial. }
    assert(Hwellsh1 :wellFormedFstShadowIfDefaultValues s) by trivial.
    unfold  wellFormedFstShadowIfDefaultValues in Hwellsh1.
  assert(getPDFlag sh1 vaChild s  = false /\
           getVirtualAddressSh1 sh1 s vaChild = Some defaultVAddr) as (_ & Hkey).
  apply Hwellsh1 with phyDescChild pdChildphy;trivial.
  trivial.
   rewrite <- Hnewpro.
   apply getVirtualAddressSh1Eq with level;trivial.
 -  assert(exists vainparent : vaddr,
          getVirtualAddressSh1 sh1 s va = Some vainparent).
  apply Hcons with phyDescChild pg pdChildphy;trivial.
  apply getMappedPageMapMMUPage with  phyVaChild ptVaChildpd r w e vaChild 
        phyDescChild level entry;trivial.
      unfold consistency ;intuition.
      destruct H as (vainparent & Hx).
      exists vainparent.
      rewrite <- Hx.
      symmetry.
      apply getVirtualAddressSh1MapMMUPage with entry vaInCurrentPartition ptVaInCurPartpd currentPD
   pdChildphy phyDescChild vaChild false level phyDescChild;trivial.
    unfold consistency ;intuition.
   subst. trivial.
   intros;subst;split;trivial.
 + assert(exists vainparent : vaddr,
          getVirtualAddressSh1 sh1 s va = Some vainparent).
  apply Hcons with partition pg pd;trivial.
  rewrite <- Hmap.
  apply getMappedPageMapMMUPageEq with partition phyDescChild vaChild entry level;
  trivial.
  apply isConfigTable with vaChild;trivial.
        intros;subst;split;trivial.
  assert(Hconfig :   configTablesAreDifferent s) by trivial.
        apply Hconfig;intuition.
  intros;subst;split;trivial.
  intuition.

      destruct H as (vainparent & Hx).
      exists vainparent.
      rewrite <- Hx.
      symmetry.
      apply getVirtualAddressSh1MapMMUPage with entry vaInCurrentPartition ptVaInCurPartpd currentPD
   pdChildphy phyDescChild vaChild false level partition;trivial.
    unfold consistency ;intuition.
   subst. trivial.
   intros;subst;split;trivial.
Qed.
    Lemma readVirtualIsVA' table idx va s :
    StateLib.readVirtual table idx (memory s) =
     Some va -> 
    isVA' table idx va s.
    Proof.
    unfold StateLib.readVirtual, isVA'.
    destruct (lookup table idx (memory s) beqPage beqIndex);intros;
    try now contradict H.
    destruct v;try now contradict H.
    inversion H;trivial.
    Qed.
Lemma wellFormedSndShadowMapMMUPage  s entry vaInCurrentPartition vaChild currentPart
currentShadow  idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild isnotderiv currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level r w e  :
let s' :={|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
negb presentDescPhy = false -> 
negb presentvaChild = true ->
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild (negb isnotderiv) currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level /\
StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
Some vaInCurrentPartition /\
isPartitionFalse ptVaInCurPart idxvaInCurPart s -> 
 (forall child : page, 
    In child (getChildren currentPart s) -> ~ In phyVaChild (getMappedPages child s)) -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
wellFormedSndShadow s ->
wellFormedSndShadow s'.
Proof.
intros s'.
unfold propagatedPropertiesAddVaddr.
intuition.
unfold consistency in *. intuition;subst.
assert(Hcons : wellFormedSndShadow s) by trivial.
unfold wellFormedSndShadow in Hcons.
unfold wellFormedSndShadow.
intros partition Hpart Hmult va pg pd sh1 Hpd Hsh1 Hmap.
assert(Hchild : In phyDescChild (getPartitions multiplexer s)).
{ unfold consistency in *.
  apply childrenPartitionInPartitionList with  (currentPartition s);intuition;subst;trivial. }
rewrite negb_true_iff in *;rewrite negb_false_iff in *;subst.
assert(Hlegit : isnotderiv && accessiblesrc && presentmap && negb false = true) by trivial.
repeat rewrite andb_true_iff in Hlegit.
intuition.
assert(Hlevel : StateLib.getNbLevel = Some level) by (symmetry;trivial).
assert(Hpds : forall part, StateLib.getPd part (memory s') =
StateLib.getPd part (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
rewrite Hpds in *;clear Hpds.
assert(Hsh1s :  StateLib.getSndShadow partition (memory s') =
StateLib.getSndShadow partition (memory s)).
{ intros. apply getSndShadowMapMMUPage with entry;trivial. }
rewrite Hsh1s in *; clear Hsh1s.
assert(Hparts : In partition (getPartitions multiplexer s)).
{ apply getPartitionsMapMMUPage with entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd 
  (StateLib.getIndexOfAddr vaChild fstLevel)
  phyVaChild pdChildphy r w e phyDescChild vaChild false
  level;subst;trivial. intros;subst;split;trivial. }
  
subst.
assert(Hor : partition= phyDescChild \/ partition <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
+ subst partition.
  assert(pdChildphy = pd).
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  subst pd.
  assert(Hor : checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/
    checkVAddrsEqualityWOOffset nbLevel vaChild va  level = false ).
  { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild va  level);intuition. }
  destruct Hor as [Hor | Hor].
  - exists vaInCurrentPartition.
    assert(Hnewpro : getVirtualAddressSh2 sh1 s vaChild = Some vaInCurrentPartition).
    { apply getVirtualAddressSh2GetTableRoot with ptVaChildsh2 phyDescChild level ;trivial.
      intros;subst;split;trivial.
      apply readVirtualIsVA';trivial.
     }
  assert(Heqtmp:(StateLib.getIndexOfAddr vaChild fstLevel) = (StateLib.getIndexOfAddr va fstLevel)).
  { apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level;trivial.
    apply fstLevelLe.
    apply getNbLevelLt;trivial. }
    assert(Heq : getVirtualAddressSh2 sh1 s va = getVirtualAddressSh2 sh1 s' va).
  apply getVirtualAddressSh2MapMMUPage with entry vaInCurrentPartition ptVaInCurPartpd currentPD
   pdChildphy phyDescChild vaChild false level phyDescChild;trivial.
   unfold consistency ;intuition.
   subst. trivial.
   intros;subst;split;trivial.
   rewrite <-  Heq;clear Heq.
   rewrite <- Hnewpro.
   split.
   apply getVirtualAddressSh2Eq with level;trivial.
   trivial. (* beqVAddr defaultVAddr vaInCurrentPartition = false *)
 - assert(exists vainparent : vaddr,
          getVirtualAddressSh2 sh1 s va = Some vainparent /\
  beqVAddr defaultVAddr vainparent = false).
  apply Hcons with phyDescChild pg pdChildphy;trivial.
  apply getMappedPageMapMMUPage with  phyVaChild ptVaChildpd r w e vaChild 
        phyDescChild level entry;trivial.
      unfold consistency ;intuition.
      destruct H as (vainparent & Hx & Hxx).
      exists vainparent.
      rewrite <- Hx.
      split;trivial.
      symmetry.
      apply getVirtualAddressSh2MapMMUPage with entry vaInCurrentPartition ptVaInCurPartpd currentPD
   pdChildphy phyDescChild vaChild false level phyDescChild;trivial.
    unfold consistency ;intuition.
   subst. trivial.
   intros;subst;split;trivial.
 + assert(exists vainparent : vaddr,
          getVirtualAddressSh2 sh1 s va = Some vainparent /\
  beqVAddr defaultVAddr vainparent = false).
  apply Hcons with partition pg pd;trivial.
  rewrite <- Hmap.
  apply getMappedPageMapMMUPageEq with partition phyDescChild vaChild entry level;
  trivial.
  apply isConfigTable with vaChild;trivial.
        intros;subst;split;trivial.
  assert(Hconfig :   configTablesAreDifferent s) by trivial.
        apply Hconfig;intuition.
  intros;subst;split;trivial.
  intuition.

      destruct H as (vainparent & Hx & Hxx).
      exists vainparent.
      split;trivial.
      rewrite <- Hx.
      symmetry.
      apply getVirtualAddressSh2MapMMUPage with entry vaInCurrentPartition ptVaInCurPartpd currentPD
   pdChildphy phyDescChild vaChild false level partition;trivial.
    unfold consistency ;intuition.
   subst. trivial.
   intros;subst;split;trivial.
Qed.

Lemma wellFormedShadowsMapMMUPage root 
 s ptVaChildpd idxvaChild phyVaChild r w e
  entry 
 (vaChild vaInCurrentPartition :vaddr) (ptVaInCurPartpd currentPD  pdChildphy phyDescChild :page)
  ( presentvaChild :bool)
(level :level)  :
let s' :={|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
(root = sh1idx \/ root = sh2idx) -> 
 wellFormedFstShadowIfNone s -> wellFormedFstShadowIfDefaultValues  s ->  
wellFormedShadows root s ->
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
parentInPartitionList s -> 
noDupPartitionTree s ->
partitionDescriptorEntry s -> 
isPresentNotDefaultIff s -> noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
(defaultPage =? ptVaInCurPartpd) = false -> 
entryPresentFlag ptVaInCurPartpd
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
entryUserFlag ptVaInCurPartpd 
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) true s -> 
isEntryPage ptVaInCurPartpd  
  (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) phyVaChild s -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> (forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\
getTableAddrRoot ptVaInCurPartpd PDidx (currentPartition s)
  vaInCurrentPartition s) -> 
nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 

wellFormedShadows root s'.
Proof.
intros s' Hroot Hnewcons2 Hnewcons Hcons.
intros.
rewrite negb_true_iff in *;subst.
unfold wellFormedShadows in *.
move Hcons at bottom.
intros partition Hpart pd Hpd structroot Hpp nbL stop Hlevel ind1 va Hind Hnotnull.
assert(Hpds : forall part, StateLib.getPd part (memory s') =
StateLib.getPd part (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
rewrite Hpds in *;clear Hpds.
assert(Hpartseq :getPartitions multiplexer s = getPartitions multiplexer s').
{ apply getPartitionsMapMMUPageEq  with entry
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
vaChild false level;trivial. }
rewrite <- Hpartseq in *.
assert(HppS: nextEntryIsPP partition root structroot s).
{ destruct Hroot ;subst;  apply nextEntryIsPPMapMMUPage' with ptVaChildpd 
(StateLib.getIndexOfAddr vaChild fstLevel) phyVaChild
r w e;trivial. }
assert(HindS : getIndirection pd va nbL stop s = Some ind1).
apply getIndirectionMapMMUPage4 with  ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
phyVaChild r w e pdChildphy (currentPartition s) false vaChild
phyDescChild entry PDidx partition;trivial.
symmetry;trivial.
  apply pdPartNotNull with phyDescChild s;trivial.
   apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
   apply nextEntryIsPPgetPd;trivial.
   symmetry;trivial.
   intros;subst;split;trivial.
   apply nextEntryIsPPgetPd;trivial.
   left;trivial.
assert(Hnewgoal : exists indirection2 : page,
  getIndirection structroot va nbL stop s = Some indirection2 /\
  (defaultPage =? indirection2) = false).
{ move Hcons at bottom. apply Hcons with partition pd ind1;trivial. } 
destruct Hnewgoal as (ind2 & Hind2 & Hdef).
exists ind2;split;trivial.
apply getIndirectionMapMMUPage5  with pdChildphy (currentPartition s)
          false vaChild phyDescChild entry root partition;trivial.
        symmetry;trivial.
        apply pdPartNotNull with phyDescChild s;trivial .
        apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
        apply nextEntryIsPPgetPd;trivial.
        symmetry;trivial.
          intros;subst;split;trivial.
          destruct Hroot;subst. 
         right;left;trivial.
        do 2 right;trivial.


Qed.

Lemma  wellFormedFstShadowIfNoneMapMMUPage  s entry vaInCurrentPartition vaChild currentPart
currentShadow  idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild isnotderiv currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level r w e  :
let s' :={|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
negb presentDescPhy = false -> 
negb presentvaChild = true ->
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild (negb isnotderiv) currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level /\
StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
Some vaInCurrentPartition /\
isPartitionFalse ptVaInCurPart idxvaInCurPart s -> 
 (forall child : page, 
    In child (getChildren currentPart s) -> ~ In phyVaChild (getMappedPages child s)) -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfNone s'.
Proof.
intros s'.
unfold propagatedPropertiesAddVaddr.
intuition.
unfold consistency in *. intuition;subst.
assert(Hcons : wellFormedFstShadowIfNone s) by trivial.
unfold wellFormedFstShadowIfNone in Hcons.
unfold wellFormedFstShadowIfNone.
intros partition va  pd sh1 Hpart Hpd Hsh1 Hmap.
assert(Hchild : In phyDescChild (getPartitions multiplexer s)).
{ unfold consistency in *.
  apply childrenPartitionInPartitionList with  (currentPartition s);intuition;subst;trivial. }
rewrite negb_true_iff in *;rewrite negb_false_iff in *;subst.
assert(Hlegit : isnotderiv && accessiblesrc && presentmap && negb false = true) by trivial.
repeat rewrite andb_true_iff in Hlegit.
destruct Hlegit as (((Hi1 & Hi2 ) & Hi3 ) & Hi4).
subst.
assert(Hlevel : StateLib.getNbLevel = Some level) by (symmetry;trivial).
assert(Hpds : forall part, StateLib.getPd part (memory s') =
StateLib.getPd part (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
rewrite Hpds in *;clear Hpds.
assert(Hsh1s :  StateLib.getFstShadow partition (memory s') =
StateLib.getFstShadow partition (memory s)).
{ intros. apply getFstShadowMapMMUPage with entry;trivial. }
rewrite Hsh1s in *; clear Hsh1s.
assert(Hparts : In partition (getPartitions multiplexer s)).
{ apply getPartitionsMapMMUPage with entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd 
  (StateLib.getIndexOfAddr vaChild fstLevel)
  phyVaChild pdChildphy r w e phyDescChild vaChild false
  level;subst;trivial. intros;subst;split;trivial. }
subst.
assert (Hnewmap : getMappedPage pdChildphy s' vaChild = SomePage phyVaChild).
{  assert(Hlookup : lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s)
       beqPage beqIndex = Some (PE entry)) by trivial.
  assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial. 
  assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
          (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some defaultPage).
  { assert(Hcons1 : isPresentNotDefaultIff s).
    unfold consistency in *. intuition.            
    apply Hcons1.
    subst.
    unfold entryPresentFlag in *. 
    unfold StateLib.readPresent.
    rewrite Hlookup in *.
    f_equal.
    subst.
    assert (Hentrypresent : negb (present entry) = true).
    { assert (Hii : false = present entry) by trivial.
       destruct (present entry) ;subst;try now contradict Hii.
       trivial. }
    apply negb_true_iff in Hentrypresent.
    subst. trivial. }
  assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
                (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some phyVaChild).
  { unfold StateLib.readPhyEntry. 
    cbn.
    assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
    (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
    beqIndex = true); intros.
    rewrite <- beqPairsTrue;split;trivial.
    subst.
    rewrite Hpairs.
    simpl;trivial. }
  apply getMappedPageGetTableRoot with ptVaChildpd phyDescChild;
  trivial;fold s'. 
  + intros. 
  split. 
  apply isPEMapMMUPage with entry;trivial.
  subst;trivial.
  assert(Htblroot : getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
  unfold getTableAddrRoot in Htblroot.
  destruct Htblroot as (Hidxs & Htblroot).
  split;trivial.
  intros.
  assert(Hpdchild :nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Htblroot in Hpdchild;clear Htblroot.
  move Hpdchild at bottom.
  destruct Hpdchild as (nbL & HnbL & stop & Hstop & Hind1).
  exists nbL ; split ; trivial.
  exists stop;split;trivial.
  assert(tableroot = pdChildphy). 
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  phyVaChild r w  e;trivial.
  subst. trivial.
  apply nextEntryIsPPgetPd;trivial.
  subst .
  revert Hind1.

  revert Htrue1 Htrue2 Hlookup Hdefaut.
  clear. 
  intros.
   apply getIndirectionMapMMUPage with entry;trivial;subst;trivial.
 + unfold isEntryPage, StateLib.readPhyEntry in *. 
   destruct(lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
             (memory s') beqPage beqIndex);trivial;try now contradict Htrue2.
   destruct v;try now contradict Htrue2.
   inversion Htrue2;trivial.
 + unfold entryPresentFlag. 
   cbn.
   subst.
   assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
      beqIndex = true).
   apply beqPairsTrue;split;trivial.
   rewrite Hpairs.
   simpl;trivial.
       
+ apply  nextEntryIsPPMapMMUPage with entry;trivial. } 
assert(Hor : partition= phyDescChild \/ partition <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
+ subst partition.
  assert(pdChildphy = pd).
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  subst pd.
  assert(Hor : checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/
    checkVAddrsEqualityWOOffset nbLevel vaChild va  level = false ).
  { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild va  level);intuition. }
  destruct Hor as [Hor | Hor].
  - assert(Hmykey :   getMappedPage pdChildphy s' va = 
   getMappedPage pdChildphy s' vaChild). 
    { apply getMappedPageEq with level;trivial.
      rewrite <- Hor.
      apply checkVAddrsEqualityWOOffsetPermut. }
   rewrite Hmap in *.
   rewrite <- Hmykey in Hnewmap.
   now contradict Hnewmap.
 - assert(Heq : getPDFlag sh1 va s' = getPDFlag sh1 va s).
   { apply getPDFlagMapMMUPage with entry
    vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
    vaChild false level phyDescChild;trivial.
    unfold consistency;intuition.
    intros;subst;split;trivial. }
  rewrite Heq.
  assert(Heqsh1 : getVirtualAddressSh1 sh1 s' va  =getVirtualAddressSh1 sh1 s va ).
   { symmetry. apply getVirtualAddressSh1MapMMUPage with entry
    vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
    vaChild false level phyDescChild;trivial.
    unfold consistency;intuition.
    intros;subst;split;trivial. }
  rewrite Heqsh1.
  apply Hcons with phyDescChild pdChildphy;trivial.
  assert(Hnone : getMappedPage pdChildphy s va = NonePage).
  { apply getMappedPageNoneMapMMUPage with  phyVaChild ptVaChildpd r w e vaChild 
        phyDescChild level entry;trivial.
      unfold consistency ;intuition. }
  trivial.
 + assert(Heq : getPDFlag sh1 va s' = getPDFlag sh1 va s).
   { apply getPDFlagMapMMUPage with entry
    vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
    vaChild false level partition;trivial.
    unfold consistency;intuition.
    intros;subst;split;trivial. }
    rewrite Heq.
  assert(Heqsh1 : getVirtualAddressSh1 sh1 s' va  =getVirtualAddressSh1 sh1 s va ).
   { symmetry. apply getVirtualAddressSh1MapMMUPage with entry
    vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
    vaChild false level partition;trivial.
    unfold consistency;intuition.
    intros;subst;split;trivial. }
  rewrite Heqsh1.
  apply Hcons with partition pd;trivial.
  rewrite <- Hmap.
  apply getMappedPageMapMMUPageEq with partition phyDescChild vaChild entry level;
  trivial.
  apply isConfigTable with vaChild;trivial.
        intros;subst;split;trivial.
  assert(Hconfig :   configTablesAreDifferent s) by trivial.
        apply Hconfig;intuition.
  intros;subst;split;trivial.
  intuition.
Qed.

Lemma  wellFormedFstShadowIfDefaultValuesMapMMUPage  s entry vaInCurrentPartition vaChild currentPart
currentShadow  idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild isnotderiv currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level r w e  :
let s' :={|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |} in
negb presentDescPhy = false -> 
negb presentvaChild = true ->
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild (negb isnotderiv) currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level /\
StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
Some vaInCurrentPartition /\
isPartitionFalse ptVaInCurPart idxvaInCurPart s -> 
 (forall child : page, 
    In child (getChildren currentPart s) -> ~ In phyVaChild (getMappedPages child s)) -> 
In phyVaChild (getAccessibleMappedPages (currentPartition s) s) -> 
wellFormedFstShadowIfDefaultValues s ->
wellFormedFstShadowIfDefaultValues s'.
Proof.
intros s'.
unfold propagatedPropertiesAddVaddr.
intuition.
unfold consistency in *. intuition;subst.
assert(Hcons : wellFormedFstShadowIfDefaultValues s) by trivial.
unfold wellFormedFstShadowIfDefaultValues in Hcons.
unfold wellFormedFstShadowIfDefaultValues.
intros partition va  pd sh1 Hpart Hpd Hsh1 Hmap.
assert(Hchild : In phyDescChild (getPartitions multiplexer s)).
{ unfold consistency in *.
  apply childrenPartitionInPartitionList with  (currentPartition s);intuition;subst;trivial. }
rewrite negb_true_iff in *;rewrite negb_false_iff in *;subst.
assert(Hlegit : isnotderiv && accessiblesrc && presentmap && negb false = true) by trivial.
repeat rewrite andb_true_iff in Hlegit.
destruct Hlegit as (((Hi1 & Hi2 ) & Hi3 ) & Hi4).
subst.
assert(Hlevel : StateLib.getNbLevel = Some level) by (symmetry;trivial).
assert(Hpds : forall part, StateLib.getPd part (memory s') =
StateLib.getPd part (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
rewrite Hpds in *;clear Hpds.
assert(Hsh1s :  StateLib.getFstShadow partition (memory s') =
StateLib.getFstShadow partition (memory s)).
{ intros. apply getFstShadowMapMMUPage with entry;trivial. }
rewrite Hsh1s in *; clear Hsh1s.
assert(Hparts : In partition (getPartitions multiplexer s)).
{ apply getPartitionsMapMMUPage with entry
  vaInCurrentPartition ptVaInCurPartpd currentPD ptVaChildpd 
  (StateLib.getIndexOfAddr vaChild fstLevel)
  phyVaChild pdChildphy r w e phyDescChild vaChild false
  level;subst;trivial. intros;subst;split;trivial. }
subst.
assert (Hnewmap : getMappedPage pdChildphy s' vaChild = SomePage phyVaChild).
{  assert(Hlookup : lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s)
       beqPage beqIndex = Some (PE entry)) by trivial.
  assert(Hdefaut : (defaultPage =? ptVaChildpd) = false) by trivial. 
  assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
          (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some defaultPage).
  { assert(Hcons1 : isPresentNotDefaultIff s).
    unfold consistency in *. intuition.            
    apply Hcons1.
    subst.
    unfold entryPresentFlag in *. 
    unfold StateLib.readPresent.
    rewrite Hlookup in *.
    f_equal.
    subst.
    assert (Hentrypresent : negb (present entry) = true).
    { assert (Hii : false = present entry) by trivial.
       destruct (present entry) ;subst;try now contradict Hii.
       trivial. }
    apply negb_true_iff in Hentrypresent.
    subst. trivial. }
  assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
                (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some phyVaChild).
  { unfold StateLib.readPhyEntry. 
    cbn.
    assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
    (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
    beqIndex = true); intros.
    rewrite <- beqPairsTrue;split;trivial.
    subst.
    rewrite Hpairs.
    simpl;trivial. }
  apply getMappedPageGetTableRoot with ptVaChildpd phyDescChild;
  trivial;fold s'. 
  + intros. 
  split. 
  apply isPEMapMMUPage with entry;trivial.
  subst;trivial.
  assert(Htblroot : getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
  unfold getTableAddrRoot in Htblroot.
  destruct Htblroot as (Hidxs & Htblroot).
  split;trivial.
  intros.
  assert(Hpdchild :nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Htblroot in Hpdchild;clear Htblroot.
  move Hpdchild at bottom.
  destruct Hpdchild as (nbL & HnbL & stop & Hstop & Hind1).
  exists nbL ; split ; trivial.
  exists stop;split;trivial.
  assert(tableroot = pdChildphy). 
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  apply nextEntryIsPPMapMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  phyVaChild r w  e;trivial.
  subst. trivial.
  apply nextEntryIsPPgetPd;trivial.
  subst .
  revert Hind1.

  revert Htrue1 Htrue2 Hlookup Hdefaut.
  clear. 
  intros.
   apply getIndirectionMapMMUPage with entry;trivial;subst;trivial.
 + unfold isEntryPage, StateLib.readPhyEntry in *. 
   destruct(lookup ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
             (memory s') beqPage beqIndex);trivial;try now contradict Htrue2.
   destruct v;try now contradict Htrue2.
   inversion Htrue2;trivial.
 + unfold entryPresentFlag. 
   cbn.
   subst.
   assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
      beqIndex = true).
   apply beqPairsTrue;split;trivial.
   rewrite Hpairs.
   simpl;trivial.
       
+ apply  nextEntryIsPPMapMMUPage with entry;trivial. } 
assert(Hor : partition= phyDescChild \/ partition <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
+ subst partition.
  assert(pdChildphy = pd).
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  subst pd.
  assert(Hor : checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/
    checkVAddrsEqualityWOOffset nbLevel vaChild va  level = false ).
  { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild va  level);intuition. }
  destruct Hor as [Hor | Hor].
  - assert(Hmykey :   getMappedPage pdChildphy s' va = 
   getMappedPage pdChildphy s' vaChild). 
    { apply getMappedPageEq with level;trivial.
      rewrite <- Hor.
      apply checkVAddrsEqualityWOOffsetPermut. }
   rewrite Hmap in *.
   rewrite <- Hmykey in Hnewmap.
   now contradict Hnewmap.
 - assert(Heq : getPDFlag sh1 va s' = getPDFlag sh1 va s).
   { apply getPDFlagMapMMUPage with entry
    vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
    vaChild false level phyDescChild;trivial.
    unfold consistency;intuition.
    intros;subst;split;trivial. }
  rewrite Heq.
  assert(Heqsh1 : getVirtualAddressSh1 sh1 s' va  =getVirtualAddressSh1 sh1 s va ).
   { symmetry. apply getVirtualAddressSh1MapMMUPage with entry
    vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
    vaChild false level phyDescChild;trivial.
    unfold consistency;intuition.
    intros;subst;split;trivial. }
  rewrite Heqsh1.
  apply Hcons with phyDescChild pdChildphy;trivial.
  assert(Hnone : getMappedPage pdChildphy s va = SomeDefault).
  { apply getMappedPageDefaultMapMMUPage with  phyVaChild ptVaChildpd r w e vaChild 
        phyDescChild level entry;trivial.
      unfold consistency ;intuition. }
  trivial.
 + assert(Heq : getPDFlag sh1 va s' = getPDFlag sh1 va s).
   { apply getPDFlagMapMMUPage with entry
    vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
    vaChild false level partition;trivial.
    unfold consistency;intuition.
    intros;subst;split;trivial. }
    rewrite Heq.
  assert(Heqsh1 : getVirtualAddressSh1 sh1 s' va  =getVirtualAddressSh1 sh1 s va ).
   { symmetry. apply getVirtualAddressSh1MapMMUPage with entry
    vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
    vaChild false level partition;trivial.
    unfold consistency;intuition.
    intros;subst;split;trivial. }
  rewrite Heqsh1.
  apply Hcons with partition pd;trivial.
  rewrite <- Hmap.
  apply getMappedPageMapMMUPageEq with partition phyDescChild vaChild entry level;
  trivial.
  apply isConfigTable with vaChild;trivial.
        intros;subst;split;trivial.
  assert(Hconfig :   configTablesAreDifferent s) by trivial.
        apply Hconfig;intuition.
  intros;subst;split;trivial.
  intuition.
Qed.


Lemma  consistencyMapMMUPage s entry vaInCurrentPartition vaChild currentPart
currentShadow  idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild isnotderiv currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level r w e  :
negb presentDescPhy = false -> 
negb presentvaChild = true ->
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild (negb isnotderiv) currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level /\
StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
Some vaInCurrentPartition /\
isPartitionFalse ptVaInCurPart idxvaInCurPart s -> 
 (forall child : page,  
    In child (getChildren currentPart s) -> ~ In phyVaChild (getMappedPages child s)) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) -> 
consistency {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros.
unfold propagatedPropertiesAddVaddr in *.
intuition.

assert(Hchild : In phyDescChild (getPartitions multiplexer s)).
{ unfold consistency in *.
  apply childrenPartitionInPartitionList with currentPart;intuition;subst;trivial. }
rewrite negb_true_iff in *;rewrite negb_false_iff in *;subst.
assert(Hlegit : isnotderiv && accessiblesrc && presentmap && negb false = true) by trivial.
repeat rewrite andb_true_iff in Hlegit.
intuition;subst.
assert(Hlevel : StateLib.getNbLevel = Some level) by (symmetry;trivial).
assert (Hcons : consistency s) by trivial.
unfold consistency in *. intuition.

+ apply partitionDescriptorEntryMapMMUPage with entry vaChild
  vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
  false level;trivial;intros;subst;split;trivial.

+ apply dataStructurePdSh1Sh2asRootMapMMUPagePD with entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
false level;trivial ;intros;subst;split;trivial.

+ apply dataStructurePdSh1Sh2asRootMapMMUPageSh1 with entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
false level;trivial ;intros;subst;split;trivial.

+ apply dataStructurePdSh1Sh2asRootMapMMUPageSh2 with entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
false level;trivial ;intros;subst;split;trivial.

+ apply currentPartitionInPartitionsListMapMMUPage with entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
false level;trivial ;intros;subst;split;trivial.

+ apply noDupMappedPagesListMapMMUPage  with entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
false level true true true ;trivial ;intros;subst;split;trivial. intuition.    

+ apply noDupConfigPagesListMapMMUPage with entry 
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild vaChild
false level;trivial ;intros;subst;split;trivial. intuition.

+ apply parentInPartitionListMapMMUPage with entry 
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild vaChild
false level;trivial ;intros;subst;split;trivial. intuition.

+ apply accessibleVAIsNotPartitionDescriptorMapMMUPage with entry 
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild vaChild
false level;trivial ;intros;subst;split;trivial. intuition.

+ apply accessibleChildPageIsAccessibleIntoParentMapMMUPage with entry 
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild vaChild
false level ptVaChildsh2;trivial ;intros;subst;split;trivial. intuition.

+ apply noCycleInPartitionTreeMapMMUPage with entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
false level;trivial ;intros;subst;split;trivial. 

+ apply configTablesAreDifferentMapMMUPage with entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
false level;trivial;unfold consistency in *;intuition;subst;trivial.

+ apply isChildMapMMUPage with entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
false level;trivial;unfold consistency in *;intuition;subst;trivial.

+ apply isPresentNotDefaultIffMapMMUPage with true
  true true false (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) ptVaInCurPartpd
  entry;trivial.

+ apply physicalPageNotDerivedMapMMUPage with entry
vaInCurrentPartition vaChild currentShadow (StateLib.getIndexOfAddr descChild fstLevel) ptDescChild
ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) descChild 
true currentPD
ptVaInCurPartpd true true ptDescChildpd (StateLib.getIndexOfAddr descChild fstLevel)
true phyDescChild pdChildphy false sh2Childphy
ptVaChildsh2 level;trivial. unfold propagatedPropertiesAddVaddr;intuition.
unfold consistency;intuition.

+ apply multiplexerWithoutParentMapMMUPage with entry;trivial.

+ apply isParentMapMMUPage  with entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
false level;trivial;unfold consistency in *;intuition;subst;trivial.

+ apply noDupPartitionTreeMapMMUPage with entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
false level;trivial ;intros;subst;split;trivial.

+ apply wellFormedFstShadowMapMMUPage with entry
vaInCurrentPartition vaChild  (currentPartition s) currentShadow (StateLib.getIndexOfAddr descChild fstLevel) ptDescChild
ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) descChild 
true currentPD
ptVaInCurPartpd true true ptDescChildpd (StateLib.getIndexOfAddr descChild fstLevel)
true phyDescChild pdChildphy false sh2Childphy
ptVaChildsh2 level;trivial. unfold propagatedPropertiesAddVaddr;intuition.
unfold consistency;intuition.

+ apply wellFormedSndShadowMapMMUPage with entry
vaInCurrentPartition vaChild  (currentPartition s) currentShadow (StateLib.getIndexOfAddr descChild fstLevel) ptDescChild
ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) descChild 
true currentPD
ptVaInCurPartpd true true ptDescChildpd (StateLib.getIndexOfAddr descChild fstLevel)
true phyDescChild pdChildphy false sh2Childphy
ptVaChildsh2 level;trivial. unfold propagatedPropertiesAddVaddr;intuition.
unfold consistency;intuition.

+ apply wellFormedShadowsMapMMUPage with  entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
false level;trivial;unfold consistency in *;intuition;subst;trivial.

+ apply wellFormedShadowsMapMMUPage with  entry vaChild
vaInCurrentPartition ptVaInCurPartpd currentPD pdChildphy phyDescChild
false level;trivial;unfold consistency in *;intuition;subst;trivial.

+ apply wellFormedFstShadowIfNoneMapMMUPage with entry
vaInCurrentPartition vaChild  (currentPartition s) currentShadow (StateLib.getIndexOfAddr descChild fstLevel) ptDescChild
ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) descChild 
true currentPD
ptVaInCurPartpd true true ptDescChildpd (StateLib.getIndexOfAddr descChild fstLevel)
true phyDescChild pdChildphy false sh2Childphy
ptVaChildsh2 level;trivial. unfold propagatedPropertiesAddVaddr;intuition.
unfold consistency;intuition.
+ apply wellFormedFstShadowIfDefaultValuesMapMMUPage with entry
vaInCurrentPartition vaChild  (currentPartition s) currentShadow (StateLib.getIndexOfAddr descChild fstLevel) ptDescChild
ptVaInCurPart (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) descChild 
true currentPD
ptVaInCurPartpd true true ptDescChildpd (StateLib.getIndexOfAddr descChild fstLevel)
true phyDescChild pdChildphy false sh2Childphy
ptVaChildsh2 level;trivial. unfold propagatedPropertiesAddVaddr;intuition.
unfold consistency;intuition.
Qed.

Lemma writePhyEntryMapMMUPage vaInCurrentPartition vaChild currentPart
     currentShadow idxDescChild ptDescChild ptVaInCurPart
     idxvaInCurPart descChild isnotderiv currentPD ptVaInCurPartpd
     accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
     phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild
     sh2Childphy ptVaChildsh2 level r w e:
     negb presentDescPhy = false -> 
negb presentvaChild = true ->
isnotderiv && accessiblesrc && presentmap && negb presentvaChild = true -> 
{{ fun s : state =>
   propagatedPropertiesAddVaddr s vaInCurrentPartition vaChild currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart
idxvaInCurPart descChild (negb isnotderiv) currentPD ptVaInCurPartpd
accessiblesrc presentmap ptDescChildpd idxDescChild1 presentDescPhy
phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild
phyVaChild sh2Childphy ptVaChildsh2 level /\
StateLib.readVirtual ptVaChildsh2 idxvaChild (memory s) =
Some vaInCurrentPartition /\
isPartitionFalse ptVaInCurPart idxvaInCurPart s /\
 (forall child : page,  
    In child (getChildren currentPart s) -> ~ In phyVaChild (getMappedPages child s)) 
     }} 
  writePhyEntry ptVaChildpd idxvaChild phyVaChild true true r w e {{ fun _ (s : state) =>
                       partitionsIsolation s /\
                       kernelDataIsolation s /\
                       verticalSharing s /\ consistency s }}.
Proof.
intros Hlegit Hlegit1 Hlegit2.
eapply weaken.
eapply WP.writePhyEntry.
simpl;intros.
set(s':= {|  currentPartition := _ |}) in *.


assert (exists entry : Pentry,
      lookup  ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      unfold propagatedPropertiesAddVaddr in *.
      intuition.
      subst. trivial. }
destruct Hlookup as (entry & Hlookup).
assert(Hcurpart : In (currentPartition s) (getPartitions multiplexer s)).
{ unfold   propagatedPropertiesAddVaddr in *.
  intuition. subst. unfold consistency in *. 
  unfold currentPartitionInPartitionsList in *.
  intuition. }
assert(Hchild : In phyDescChild (getPartitions multiplexer s)).
{ unfold propagatedPropertiesAddVaddr in *.
      intuition. unfold consistency in *.
  apply childrenPartitionInPartitionList with currentPart;intuition;subst;trivial. }
  
  try repeat rewrite andb_true_iff in *. 
assert(Haccess : In phyVaChild (getAccessibleMappedPages currentPart s)). 
{ unfold   propagatedPropertiesAddVaddr in *.
  intuition. 
  apply physicalPageIsAccessible
   with ptVaInCurPartpd vaInCurrentPartition idxvaInCurPart true  level true currentPD;trivial.
  intros;split;
  subst;trivial.
  intuition;subst;trivial.
  intuition;subst;trivial.
  subst;trivial.
  unfold consistency in *; unfold currentPartitionInPartitionsList in *;
  intuition; subst;trivial. }
intuition;subst.
+ apply partitionsIsolationMapMMUPage with entry
    vaInCurrentPartition vaChild currentPart currentShadow idxDescChild
    ptDescChild ptVaInCurPart idxvaInCurPart descChild true currentPD
    ptVaInCurPartpd true true ptDescChildpd idxDescChild1
    presentDescPhy phyDescChild pdChildphy presentvaChild sh2Childphy
    ptVaChildsh2 level;intuition.
+ apply kernelDataIsolationMapMMUPage with  entry
    vaInCurrentPartition vaChild currentPart currentShadow idxDescChild
    ptDescChild ptVaInCurPart idxvaInCurPart descChild true currentPD
    ptVaInCurPartpd true true ptDescChildpd idxDescChild1
    presentDescPhy phyDescChild pdChildphy presentvaChild sh2Childphy
    ptVaChildsh2 level;intuition.
+ apply verticalSharingMapMMUPage with  entry
    vaInCurrentPartition vaChild currentPart currentShadow idxDescChild
    ptDescChild ptVaInCurPart idxvaInCurPart descChild true currentPD
    ptVaInCurPartpd true true ptDescChildpd idxDescChild1
    presentDescPhy phyDescChild pdChildphy presentvaChild sh2Childphy
    ptVaChildsh2 level;intuition.
+  apply consistencyMapMMUPage with entry
    vaInCurrentPartition vaChild currentPart currentShadow idxDescChild
    ptDescChild ptVaInCurPart idxvaInCurPart descChild true currentPD
    ptVaInCurPartpd true true ptDescChildpd idxDescChild1
    presentDescPhy phyDescChild pdChildphy presentvaChild sh2Childphy
    ptVaChildsh2 level;intuition.
Qed.
