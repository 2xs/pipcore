Require Import  Model.ADT Model.Hardware Core.Services Isolation
Consistency Invariants WeakestPreconditions Model.Lib 
Model.MAL Lib InternalLemmas DependentTypeLemmas GetTableAddr PropagatedProperties StateLib.
Require Import Omega Bool  Coq.Logic.ProofIrrelevance List Classical_Prop.
 Import List.ListNotations.
 
Lemma getPdRemoveMMUPage ( partition : page) entry s table idx :
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->
StateLib.getPd partition
  (add table idx
                  (PE
                      {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex ) = StateLib.getPd partition (memory s).
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
Lemma getFstShadowRemoveMMUPage partition table idx  s entry: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getFstShadow partition
  (add table idx
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) =
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
Lemma getSndShadowRemoveMMUPage partition table idx  s entry: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getSndShadow partition
  (add table idx
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) =
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

Lemma getConfigTablesLinkedListRemoveMMUPage partition table idx  s entry: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getConfigTablesLinkedList partition
  (add table idx
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) =
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

Lemma getParentRemoveMMUPage partition table idx  s entry: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getParent partition
  (add table idx
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) =
StateLib.getParent partition (memory s). 
Proof.
intro Hentry.
cbn.
unfold StateLib.getParent. 
case_eq (Index.succ PPRidx);trivial.
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

Lemma readPysicalRemoveMMUPage ( root : page) i entry s table idx :
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->
StateLib.readPhysical root i (memory s)  =
   StateLib.readPhysical root i
    (add table idx
       (PE
           {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex).
Proof.
simpl. 
intros Hentry. 
unfold StateLib.readPhysical.
cbn. 
case_eq (beqPairs (table, idx) (root, i) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry. 
   cbn. trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  root i (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  root i   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.


Lemma readPhyEntryRemoveMMUPage table1 table2 idx1 idx2  entry  s : 
(table2 <> table1 \/ idx2 <> idx1) -> 
lookup table1 idx1(memory s) beqPage beqIndex = Some (PE entry) ->
StateLib.readPhyEntry table2 idx2 (memory s) = 
StateLib.readPhyEntry table2 idx2 
( add table1 idx1
    (PE
      {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex ).
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
Lemma readPresentRemoveMMUPage table1 table2 idx1 idx2  entry  s : 
(table2 <> table1 \/ idx2 <> idx1) -> 
lookup table1 idx1(memory s) beqPage beqIndex = Some (PE entry) ->
StateLib.readPresent table2 idx2 (memory s) = 
StateLib.readPresent table2 idx2 
( add table1 idx1
    (PE
       {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex ).
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
 Lemma getIndirectionRemoveMMUPage1 s a ( ptVaChildpd pd:page)  idxvaChild  entry level :  
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
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
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
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a level)
    (memory s)). symmetry.
    apply readPhyEntryRemoveMMUPage with entry;trivial.
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
Lemma readPDflagRemoveMMUPage s entry  idx table pg i: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
 StateLib.readPDflag pg i
  (add table idx
     (PE
       {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) = StateLib.readPDflag pg i (memory s).
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
Lemma readVirtualRemoveMMUPage s entry  idx table pg i: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
 StateLib.readVirtual pg i
  (add table idx
     (PE
       {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) = StateLib.readVirtual pg i (memory s).
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

Lemma readVirEntryRemoveMMUPage s entry  idx table pg i: 
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
 StateLib.readVirEntry pg i
  (add table idx
     (PE
       {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) = StateLib.readVirEntry pg i (memory s).
Proof.     
intros Hentry.
unfold StateLib.readVirEntry. cbn. 
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


Lemma isVARemoveMMUPage table1 table2 idx1 idx2 entry s : 
lookup table1 idx1 (memory s) beqPage beqIndex =
Some (PE entry) -> 
isVA table2 idx2 s ->
isVA table2 idx2
{|
currentPartition := currentPartition s;
memory := add table1 idx1
 (PE  {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}. 
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

Lemma isVA'RemoveMMUPage table1 table2 idx1 idx2 entry va s : 
lookup table1 idx1 (memory s) beqPage beqIndex =
Some (PE entry) -> 
isVA' table2 idx2 va s ->
isVA' table2 idx2 va
{|
currentPartition := currentPartition s;
memory := add table1 idx1
 (PE  {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}. 
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




Lemma isVERemoveMMUPage table1 table2 idx1 idx2  entry s : 
lookup table1 idx1 (memory s) beqPage beqIndex =
Some (PE entry) -> 
isVE table2 idx2 s ->
isVE table2 idx2
{|
currentPartition := currentPartition s;
memory := add table1 idx1
 (PE  {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}. 
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

Lemma entryPDFlagRemoveMMUPage table1 table2 idx1 idx2  entry flag s : 
lookup table1 idx1 (memory s) beqPage beqIndex =
Some (PE entry) -> 
entryPDFlag table2 idx2 flag s ->
entryPDFlag table2 idx2 flag
{|
currentPartition := currentPartition s;
memory := add table1 idx1
 (PE  {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup Hve.
unfold entryPDFlag in *.
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

Lemma isEntryVARemoveMMUPage table1 table2 idx1 idx2  entry flag s : 
lookup table1 idx1 (memory s) beqPage beqIndex =
Some (PE entry) -> 
isEntryVA table2 idx2 flag s ->
isEntryVA table2 idx2 flag
{|
currentPartition := currentPartition s;
memory := add table1 idx1
 (PE  {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}. 
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


(* Lemma entryPresentFlagRemoveMMUPage table1 table2 idx1 idx2  entry flag s : 
lookup table1 idx1 (memory s) beqPage beqIndex =
Some (PE entry) -> 
entryPresentFlag table2 idx2 flag s ->
entryPresentFlag table2 idx2 flag
{|
currentPartition := currentPartition s;
memory := add table1 idx1
 (PE  {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}. 
Proof.
intros Hlookup Hve.
unfold entryPresentFlag in *.
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
Qed. *)



 Lemma getIndirectionRemoveMMUPage11 s a ( ptVaChildpd pd:page)idxvaChild  entry level stop1:  
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
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
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
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a level)
    (memory s)). symmetry.
    apply readPhyEntryRemoveMMUPage with entry;trivial.
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
     
     Lemma inSubsetGetMappedPages s' pd:
forall l' l  child,
In child (getMappedPagesAux pd l' s') -> 
incl l' l -> 
 In child  (getMappedPagesAux pd l s').
Proof.
induction l';simpl.
intros.
now contradict H0.
intros.
unfold incl in H0.

simpl in *.
unfold getMappedPagesAux in *.
rewrite filterOptionInIff in *.
unfold getMappedPagesOption in *.
rewrite in_map_iff in *.

destruct H as (x & Hx & Hxx).
simpl in *.
apply H0 in Hxx.
exists x;split;trivial.
Qed.

     
Lemma checkChildRemoveMMUPage s vaChild ptVaChildpd idxvaChild phyDescChild
      
(* ptDescChildFromPD *) (* idxDescChild1 *) pdChildphy level a part entry 
(* shadow1Child *):
In part (getPartitions multiplexer s) -> 
configTablesAreDifferent s  -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
noDupConfigPagesList s -> 
currentPartitionInPartitionsList s ->
partitionDescriptorEntry s-> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s ->
(defaultPage =? ptVaChildpd) = false -> 
Some level = getNbLevel -> 
noDupPartitionTree s -> 
In phyDescChild (getChildren (currentPartition s) s) ->

checkChild part level {|
     currentPartition := currentPartition s;
     memory := add ptVaChildpd idxvaChild
                 (PE
                   {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} a =
                   checkChild part level s a.
Proof.
intros Hpartx Hconfig Hlookup Hnodup2 Hcurpart Hpde Hpdchild Htblroot Hdefaut Hlevel
Hpartchild.
intros.
unfold checkChild.
simpl.
assert(Hgetsh1 : forall part, getFstShadow part (memory s) =
 getFstShadow part
    (add ptVaChildpd idxvaChild
       (PE
          {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex)).
{ intros. symmetry.
  apply getFstShadowRemoveMMUPage with entry;trivial. }
rewrite <- Hgetsh1. clear Hgetsh1.
case_eq(getFstShadow part (memory s));[intros sh1 Hsh1 | intros Hsh1];trivial.
assert(Hind : getIndirection sh1 a level (nbLevel - 1) s  = 
getIndirection sh1 a level (nbLevel - 1) {|
    currentPartition := currentPartition s;
    memory := add ptVaChildpd idxvaChild
                (PE
                   {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}).
 unfold getTableAddrRoot in *. 
destruct Htblroot as (_ & Hroot).
assert(Hparts : part = phyDescChild \/ part <> phyDescChild) by apply pageDecOrNot.
destruct Hparts as [Hparts | Hparts];subst.
 + unfold noDupConfigPagesList in *. 
apply getIndirectionRemoveMMUPage1 with entry;trivial.
 
 
  intros. 
  assert(Hdisjoint: disjoint (getIndirections pdChildphy s) (getIndirections sh1 s)).
  assert(Hpart : In phyDescChild (getPartitions multiplexer s)).
  { apply childrenPartitionInPartitionList with (currentPartition s); trivial.
   }
  unfold noDupConfigPagesList in *.
  trivial.
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
  apply beq_nat_false in H1.
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
  apply sh1PartNotNull with phyDescChild s;trivial. 
  apply nextEntryIsPPgetFstShadow ;trivial.
  
+ apply getIndirectionRemoveMMUPage1 with entry;trivial.
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
  apply beq_nat_false in H1.
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
  apply childrenPartitionInPartitionList with (currentPartition s); trivial.
  
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
  apply childrenPartitionInPartitionList with (currentPartition s); trivial.
   
 apply nextEntryIsPPgetPd;trivial.
  unfold configTablesAreDifferent in *.
  unfold disjoint in *.
  unfold not in *.
  intros. 
  subst. 
  apply H2 with part phyDescChild ptVaChildpd;trivial.
    apply childrenPartitionInPartitionList with (currentPartition s); trivial.
 
  apply sh1PartNotNull with part s;trivial.
  apply nextEntryIsPPgetFstShadow;trivial.
  +

rewrite <- Hind.                   
case_eq(getIndirection sh1 a level (nbLevel - 1) s);intros;trivial.
assert(Hpdflag : StateLib.readPDflag p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPDflag p (StateLib.getIndexOfAddr a fstLevel)
      (add ptVaChildpd idxvaChild
         (PE
            {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex)).
            symmetry. 
            apply readPDflagRemoveMMUPage with entry;trivial.
rewrite Hpdflag.
trivial.
Qed.       




Lemma getPdsVAddrRemoveMMUPage   s ptVaChildpd idxvaChild  pdChildphy
 vaChild phyDescChild level entry:
noDupConfigPagesList s -> 
partitionDescriptorEntry s ->
configTablesAreDifferent s -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 

In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild true s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
Some level = StateLib.getNbLevel -> 
currentPartitionInPartitionsList s -> 
noDupPartitionTree s -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
forall part, In part (getPartitions multiplexer s) -> 
getPdsVAddr part level getAllVAddrWithOffset0 s = getPdsVAddr part level getAllVAddrWithOffset0
     {|
     currentPartition := currentPartition s;
     memory := add ptVaChildpd idxvaChild
                 (PE
                   {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hnodup Hpde Hconfigdiff Hlookup  Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild Hlevel Hcurpart Hnoduptree Hchildcurpart part Hpart .
set(s':= {| currentPartition := _ |}).
unfold getPdsVAddr.
induction getAllVAddrWithOffset0;simpl;trivial.
intros.
assert(Hcheck :  checkChild part level s a =
                   checkChild part level s' a). 
{                    
  symmetry.
  apply checkChildRemoveMMUPage  with vaChild phyDescChild
  pdChildphy entry;trivial. }
 case_eq(checkChild part level s a);intros.
rewrite <- Hcheck.
case_eq(checkChild part level s a);intros.
f_equal.
apply IHl;trivial. 
rewrite H in *.
now contradict H0.
rewrite <- Hcheck;trivial.
rewrite H.
apply IHl;trivial.
Qed.
 Lemma getIndirectionRemoveMMUPage5 s ptVaChildpd idxvaChild   
  pdChildphy currentPart va (* p *)
 vaChild phyDescChild level entry stop1 idxroot:
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} in 
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
(* In phyVaChild (getAccessibleMappedPages currentPart s) ->  *)
True -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
(* negb presentvaChild = true ->  *)
True -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild true s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
pdChildphy <> defaultPage -> 

getIndirection pdChildphy vaChild level (nbLevel - 1) s =
            Some ptVaChildpd -> 
forall part pd, nextEntryIsPP part idxroot pd s -> (idxroot = PDidx \/
idxroot =sh1idx \/ idxroot = sh2idx) ->   In part (getPartitions multiplexer s) -> 
           (*  stop1 <= (nbLevel -1) ->  *)
   getIndirection pd va level stop1 s' = getIndirection pd va level stop1 s.
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
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va l)
    (memory s)). symmetry.
    apply readPhyEntryRemoveMMUPage with entry;trivial.
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
+ unfold s'.
symmetry.
  apply getIndirectionRemoveMMUPage11 with entry;trivial.
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
Lemma getIndirectionRemoveMMUPage4 s ptVaChildpd idxvaChild   
  pdChildphy currentPart va p
 vaChild phyDescChild level entry stop1 idxroot:
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} in 
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
(* In phyVaChild (getAccessibleMappedPages currentPart s) ->  *)
True -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
(* negb presentvaChild = true ->  *)
True -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild true s ->  
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
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va l)
    (memory s)). symmetry.
    apply readPhyEntryRemoveMMUPage with entry;trivial.
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
  apply getIndirectionRemoveMMUPage11 with entry;trivial.
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
    Lemma getIndirectionRemoveMMUPage4None s ptVaChildpd idxvaChild  
  pdChildphy currentPart va
 vaChild phyDescChild level entry stop1 idxroot:
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} in 
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
(* In phyVaChild (getAccessibleMappedPages currentPart s) ->  *)
True -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
(* negb presentvaChild = true ->  *)
True -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild true s ->  
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
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) = 
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va l)
    (memory s)). symmetry.
    apply readPhyEntryRemoveMMUPage with entry;trivial.
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
  apply getIndirectionRemoveMMUPage11 with entry;trivial.
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
Lemma mapPageRemoveSinglePage1 s vax vaChild pdChildphy level
   ptVaChildpd 
  idxvaChild currentPart
 (* presentvaChild *) 
phyDescChild entry  : 
  let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                    {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} in 

  StateLib.getNbLevel = Some level -> 
checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false -> 

noDupConfigPagesList s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
In currentPart (getPartitions multiplexer s) ->
True -> (* In phyVaChild (getAccessibleMappedPages currentPart s) -> *)
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) ->
True -> (* negb presentvaChild = true -> *)
In phyDescChild (getPartitions multiplexer s) ->
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s ->
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s ->
(defaultPage =? ptVaChildpd) = false ->
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild ->
entryPresentFlag ptVaChildpd idxvaChild true s ->
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
 apply getIndirectionRemoveMMUPage4
with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
 pdChildphy currentPart  vaChild
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

{ subst. apply readPresentRemoveMMUPage with entry;trivial.
intuition. }
rewrite Hpres.
assert (Hphy :StateLib.readPhyEntry ind (StateLib.getIndexOfAddr vax fstLevel) (memory s) =
StateLib.readPhyEntry ind (StateLib.getIndexOfAddr vax fstLevel) (memory s')).

{ subst. apply readPhyEntryRemoveMMUPage with entry;trivial.
intuition. }
rewrite Hphy;trivial.
- assert(Hnone : getIndirection pdChildphy vax level (nbLevel - 1) s = None).
 apply getIndirectionRemoveMMUPage4None with
   ptVaChildpd idxvaChild
 pdChildphy currentPart  vaChild
phyDescChild entry PDidx phyDescChild;subst;trivial.  left;trivial.
subst;trivial.
rewrite Hnone;trivial.
Qed. 

Lemma getMappedPagesRemoveMMUPage s ptVaChildpd idxvaChild part phyDescChild vaChild entry level: 
 let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} in 
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
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) 
     (memory s) beqPage beqIndex ) = StateLib.getPd partition (memory s)).
{ intros. apply getPdRemoveMMUPage with entry;trivial. }
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
     apply getIndirectionRemoveMMUPage1 with entry;trivial. }
rewrite <- Hmykey3.
 case_eq( getIndirection pd a level (nbLevel - 1) s);intros. 
 case_eq( defaultPage =? p);intros;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 apply readPresentRemoveMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hpres.
 assert(Hread :StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 apply readPhyEntryRemoveMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hread.
 trivial.
 trivial. }
 trivial.
 
 Qed.
 Lemma readAccessibleRemoveMMUPage table1 table2 idx1 idx2 s :
table1 <> table2 \/ idx1 <> idx2 -> 
 StateLib.readAccessible table1 idx1
           (add table2 idx2
                  (PE
                      {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) = 
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
 Lemma getAccessibleMappedPageRemoveMMUPage1 s ptVaChildpd idxvaChild part phyDescChild vaChild entry level a pd: 
 let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} in 
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
     apply getIndirectionRemoveMMUPage1 with entry;trivial. }
rewrite <- Hmykey3.
 case_eq( getIndirection pd a level (nbLevel - 1) s);intros. 
 case_eq( defaultPage =? p);intros;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 apply readPresentRemoveMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hpres.
  assert(Haccess :StateLib.readAccessible p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readAccessible p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 symmetry.
 apply readAccessibleRemoveMMUPage ;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Haccess.
 assert(Hread :StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 apply readPhyEntryRemoveMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hread.
 trivial.
 trivial.
 Qed.
Lemma getAccessibleMappedPagesRemoveMMUPage s ptVaChildpd idxvaChild part phyDescChild vaChild entry level: 
 let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} in 
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
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) 
     (memory s) beqPage beqIndex ) = StateLib.getPd partition (memory s)).
{ intros. apply getPdRemoveMMUPage with entry;trivial. }
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
{  apply getAccessibleMappedPageRemoveMMUPage1 with part phyDescChild
vaChild entry level;trivial. }
 trivial.
 
 Qed.

 
 
 Lemma getMappedPageRemoveMMUPageEq s ptVaChildpd idxvaChild part phyDescChild vaChild entry level: 
 let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} in 
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
     apply getIndirectionRemoveMMUPage1 with entry;trivial. }
rewrite <- Hmykey3.
 case_eq( getIndirection pd a level (nbLevel - 1) s);intros. 
 case_eq( defaultPage =? p);intros;trivial.
 assert(Hpres :StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 apply readPresentRemoveMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hpres.
 assert(Hread :StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 simpl. 
 apply readPhyEntryRemoveMMUPage with entry;trivial.
 left. 
 apply Hmykey with (nbLevel - 1);trivial.
 rewrite <- Hread.
 trivial.
 trivial. }
 Qed.
 
 
Lemma removeMappedPageGetChildren   shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild :
accessibleVAIsNotPartitionDescriptor s ->
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
forall part, In part (getPartitions multiplexer s) ->
getChildren part {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} =
                 getChildren part s.
Proof.
set(s':= {|
     currentPartition := _|}).
intros Hkey Hnodup Hnewcons2 Hnewcons Hnoduptree Hi1 Hi2 Hi3 Hi4 Hlookup Hchildpart 
Hpp Hlevel HPE  Htableroot Hdefault Hpresent Huser Hmapped Hnotdefault Hsh1child part Hpart.
unfold getChildren.
rewrite <- Hlevel in *.
assert(Hgetpd : forall partition, getPd partition (memory s') = StateLib.getPd partition (memory s)).
{ intros. apply getPdRemoveMMUPage with entry;trivial. }
rewrite Hgetpd in *.
case_eq(StateLib.getPd part (memory s) );[intros pd Hpd |intros Hpd]
;trivial.

assert(Hpds : getPdsVAddr part level getAllVAddrWithOffset0 s =
getPdsVAddr part level getAllVAddrWithOffset0 s').
apply getPdsVAddrRemoveMMUPage with pdChildphy vaChild phyDescChild entry ;trivial.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
rewrite  <- Hpds.
clear Hpds.
unfold getMappedPagesAux in *.
unfold getMappedPagesOption in *.
assert(Hor : part = phyDescChild \/ part <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor]; subst.
+ assert(Hpdeq : pd = pdChildphy). 
  { symmetry. apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
  subst.
  f_equal.
  
  assert(Hpdflag : getPDFlag shadow1Child vaChild s = false). 
 { assert(Haccessible :getAccessibleMappedPage pdChildphy s vaChild = SomePage (pa entry)). 
   {  apply isAccessibleMappedPage2 with phyDescChild ptVaChildpd;trivial.
      apply isEntryPageReadPhyEntry2;trivial.
      unfold readPhyEntry.
      rewrite Hlookup;reflexivity.
      intros.
      split;subst;trivial. }
      unfold accessibleVAIsNotPartitionDescriptor in *. 
      apply Hkey  with phyDescChild pdChildphy (pa entry);
      trivial. apply nextEntryIsPPgetFstShadow;trivial.
       }
  assert(Hx : ~ In vaChild (getPdsVAddr phyDescChild level getAllVAddr s)).
  {  
  apply getPDFlagGetPdsVAddr' with shadow1Child;trivial.
  symmetry;trivial.
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
symmetry;trivial.
now contradict Hx.  }
   {  

  induction (getPdsVAddr phyDescChild level getAllVAddrWithOffset0 s).
  simpl;trivial.
  simpl.
  f_equal.
  simpl in *.

assert(checkVAddrsEqualityWOOffset nbLevel a vaChild level = false).
apply H.
left;trivial.
symmetry.
 apply mapPageRemoveSinglePage1 with level (StateLib.getIndexOfAddr vaChild fstLevel)
(currentPartition s)  phyDescChild entry;trivial.
symmetry;trivial.
rewrite <-H0;apply checkVAddrsEqualityWOOffsetPermut.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
symmetry;trivial.
intros;subst;split;trivial.

  apply IHl.
  intuition.
   } 
+  assert(Hiii : In phyDescChild (getPartitions multiplexer s)).
  { apply childrenPartitionInPartitionList with (currentPartition s);trivial. }
 assert(Hmappedaux : getMappedPages part s = getMappedPages part s').
{ apply getMappedPagesRemoveMMUPage with phyDescChild vaChild
      entry level;trivial.  
  * apply isConfigTable with vaChild;trivial.
 
  intros;subst;split;trivial.
  * apply Hi3;trivial.
   intuition.
  * intros;subst;split;trivial.
  * intuition.
  
}

assert(forall va, getMappedPage pd s' va = getMappedPage pd s va).
intros.
symmetry.
 apply getMappedPageRemoveMMUPageEq with part phyDescChild
vaChild entry level;trivial.
assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
apply isConfigTable  with vaChild;trivial.
intros; split; 
subst;trivial. trivial.
apply Hi3;trivial.
intuition.
intros; split; 
subst;trivial. trivial.
intuition.
induction (getPdsVAddr part level getAllVAddrWithOffset0 s);simpl;trivial.
rewrite H. 
case_eq(getMappedPage pd s a);intros;trivial.
f_equal;trivial. 
Qed. 

Lemma getPartitionsRemoveMMUPage shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
forall part, 
In part (getPartitions multiplexer {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}) -> 
In part (getPartitions multiplexer s).
Proof.
set(s' :=  {|
         currentPartition := _ |}) in *.
intros Hispart Hsh1child Hnodup Hnewcons2 Hnewcons Hnoduptree Hi1 Hi2 Hi3 Hi4 Hlookup Hchildpart 
Hpp Hlevel HPE  Htableroot Hdefault Hpresent Huser Hnotdefault Hmapped.
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

assert(Hchild : getChildren mult s' =getChildren mult s).
{ apply removeMappedPageGetChildren with shadow1Child pdChildphy phyDescChild level entry;trivial. 
(*  symmetry;trivial.
 apply childrenPartitionInPartitionList with (currentPartition s);trivial.
 *) }
 split ;trivial.
 rewrite <- Hchild;trivial.
 apply IHn;trivial.
 apply childrenPartitionInPartitionList with mult;trivial.
 
 rewrite <- Hchild;trivial.
Qed. 
Lemma getPartitionsRemoveMMUPage1 shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
getPartitions multiplexer {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} = (getPartitions multiplexer s).
Proof.
set(s' :=  {|
         currentPartition := _ |}) in *.
intros Hispart Hsh1child Hnodup Hnewcons2 Hnewcons Hnoduptree Hi1 Hi2 Hi3 Hi4 Hlookup Hchildpart 
Hpp Hlevel HPE  Htableroot Hdefault Hpresent Huser Hnotdefault Hmapped.
unfold getPartitions. 
assert(Hmult: In multiplexer (getPartitions multiplexer s)).
{ unfold getPartitions.
  destruct (nbPage);simpl; left;trivial. }
revert Hmult.
generalize multiplexer at 1 3 4.
induction (nbPage + 1);trivial;simpl.
intros mult Hmult (* part Hpart *).
f_equal.

assert(Hchild : getChildren mult s' =getChildren mult s).
{ apply removeMappedPageGetChildren with shadow1Child pdChildphy phyDescChild level entry;trivial. 
(*  symmetry;trivial.
 apply childrenPartitionInPartitionList with (currentPartition s);trivial.
 *) }
 rewrite  Hchild;trivial.
 clear Hchild.
 assert(forall child, In child (getChildren mult s) -> In child (getPartitions multiplexer s)).
 intros.
 apply childrenPartitionInPartitionList with mult;trivial.
 induction (getChildren mult s);intros;simpl in *;trivial.
 f_equal;trivial.
 apply IHn;trivial.
 apply H.
 left;trivial.
 apply IHl;trivial.
 intros.
 apply H;right;trivial.
Qed.

 
Lemma getIndirectionsRemoveMMUPage1 s ptVaChildpd idxvaChild entry: 
forall root : page,
~ In ptVaChildpd (getIndirections root s) ->
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) ->
getIndirections root s = getIndirections root {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                      {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
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
  
Lemma getLLPagesRemoveMMUPage s  ptVaChildpd idxvaChild entry: 
forall root : page,
~ In ptVaChildpd (getLLPages root s (nbPage + 1) ) ->
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) ->
getLLPages root s (nbPage + 1)  = getLLPages root  {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}(nbPage + 1) .
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
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex)).
           
 apply readPysicalRemoveMMUPage with entry ;trivial.
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
 


Lemma getConfigPagesRemoveMMUPage s part ptVaChildpd idxvaChild
  phyDescChild entry:
  let s' := {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd idxvaChild
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} in 
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
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) 
     (memory s) beqPage beqIndex ) = StateLib.getPd partition (memory s)).
{ intros. apply getPdRemoveMMUPage with entry;trivial. }
intros. 
rewrite Hgetpd in *. clear Hgetpd.
case_eq(StateLib.getPd part (memory s) );[intros pd Hpd |intros Hpd];
rewrite Hpd in *;
trivial.
    assert(Hgetfst : forall partition, StateLib.getFstShadow partition
  (add ptVaChildpd idxvaChild(PE
                    {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) 
     (memory s) beqPage beqIndex ) = StateLib.getFstShadow partition (memory s)).
{ intros. apply getFstShadowRemoveMMUPage with entry;trivial. }
intros. 
rewrite Hgetfst in *. clear Hgetfst.
case_eq(StateLib.getFstShadow part (memory s) );[intros sh1 Hsh1 |intros Hsh1];
rewrite Hsh1 in *;trivial.
    assert(Hgetsnd : forall partition, StateLib.getSndShadow partition
  (add ptVaChildpd idxvaChild(PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) 
     (memory s) beqPage beqIndex ) = StateLib.getSndShadow partition (memory s)).
{ intros. apply getSndShadowRemoveMMUPage with entry;trivial. }
intros. 
rewrite Hgetsnd in *. clear Hgetsnd.
case_eq(StateLib.getSndShadow part (memory s) );[intros sh2 Hsh2 |intros Hsh2];
rewrite Hsh2 in *;trivial.
    assert(Hgetsnd : forall partition, getConfigTablesLinkedList partition
  (add ptVaChildpd idxvaChild(PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) 
     (memory s) beqPage beqIndex ) = getConfigTablesLinkedList partition (memory s)).
{ intros. apply getConfigTablesLinkedListRemoveMMUPage with entry;trivial. }
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
apply getIndirectionsRemoveMMUPage1 with entry;trivial.
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
apply getLLPagesRemoveMMUPage with entry;trivial.
do 2 right;trivial.
right;left;trivial.
left;trivial. 
Qed.


Lemma getUsedPagesRemoveMMUPage s idxvaChild ptVaChildpd
phyDescChild (vaChild : vaddr) entry level:
let s' := {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd idxvaChild
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} in
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
 apply getConfigPagesRemoveMMUPage with phyDescChild entry;trivial.
 - 
 apply getMappedPagesRemoveMMUPage with phyDescChild vaChild
entry level;trivial.
Qed.

 Lemma getTablePagesRemoveMMUPage root n ptVaChildpd s idxvaChild :
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
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
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


Lemma getIndirectionsPDSamePartRemoveMMUPage  s  idxvaChild
ptVaChildpd phyDescChild entry (pdChildphy currentPart: page)
  (vaChild:vaddr) level pd : 
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} in 
StateLib.getPd phyDescChild (memory s) = Some pd -> 
consistency s -> 
In currentPart (getPartitions multiplexer s) -> 
(* In phyVaChild (getAccessibleMappedPages currentPart s) ->
negb presentvaChild = true ->  *)
True -> 
True -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s ->
(defaultPage =? ptVaChildpd) = false->
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild true s -> 
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

 apply indirectionNotInPreviousMMULevel1
with idxvaChild vaChild phyDescChild level entry;intuition.
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
apply getTablePagesRemoveMMUPage with (n-1) ;trivial. 
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
  

Lemma getConfigPagesRemoveMMUPage1 s idxvaChild
ptVaChildpd phyDescChild entry (pdChildphy currentPart: page)
(vaChild:vaddr) level : 
let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} in 
consistency s -> 
In currentPart (getPartitions multiplexer s) -> 
(* In phyVaChild (getAccessibleMappedPages currentPart s) -> *)
True -> 
(* negb presentvaChild = true ->  *)
True -> 
In phyDescChild (getPartitions multiplexer s) -> 
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s ->
(defaultPage =? ptVaChildpd) = false->
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
entryPresentFlag ptVaChildpd idxvaChild true s -> 
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
symmetry. apply getPdRemoveMMUPage with entry;trivial.
rewrite <- Hpd. clear Hpd.
assert(Hpd : StateLib.getFstShadow phyDescChild (memory s) =
StateLib.getFstShadow phyDescChild (memory s')).
unfold s'. simpl.
symmetry. apply getFstShadowRemoveMMUPage with entry;trivial.
rewrite <- Hpd. clear Hpd.
assert(Hpd : StateLib.getSndShadow phyDescChild (memory s) =
StateLib.getSndShadow phyDescChild (memory s')).
unfold s'. simpl.
symmetry. apply getSndShadowRemoveMMUPage with entry;trivial.
rewrite <- Hpd. clear Hpd.
assert(Hpd : StateLib.getConfigTablesLinkedList  phyDescChild (memory s) =
StateLib.getConfigTablesLinkedList  phyDescChild (memory s')).
unfold s'. simpl.
symmetry. apply getConfigTablesLinkedListRemoveMMUPage with entry;trivial.
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
+ apply getIndirectionsPDSamePartRemoveMMUPage with phyDescChild entry
pdChildphy currentPart  vaChild level;trivial.
+ f_equal.

 unfold getIndirections.
intros.
apply getIndirectionsRemoveMMUPage1 with entry;trivial.
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
apply getIndirectionsRemoveMMUPage1 with entry;trivial.
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
apply getLLPagesRemoveMMUPage with entry;trivial.
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
Lemma isPERemoveMMUPage table idx table1 idx1 s entry  :   
lookup table1 idx1 (memory s) beqPage beqIndex = Some (PE entry) -> 
isPE table idx s -> 
isPE table idx
{|
    currentPartition := currentPartition s;
    memory := add table1 idx1
                (PE
                   {|
                     read := false;
                     write := false;
                     exec := false;
                     present := false;
                     user := false;
                     pa := defaultPage |}) (memory s) beqPage beqIndex |}.
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

Lemma nextEntryIsPPRemoveMMUPage' table idx table1 idx1 res s (entry : Pentry) : 
nextEntryIsPP table idx res 
{|
currentPartition := currentPartition s;
memory := add table1 idx1 
      (PE
          {|
                     read := false;
                     write := false;
                     exec := false;
                     present := false;
                     user := false;
                     pa := defaultPage |}) (memory s) beqPage beqIndex |} -> nextEntryIsPP table idx res s .
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

 Lemma nextEntryIsPPRemoveMMUPage table idx table1 idx1 res s (entry : Pentry) : 
lookup table1 idx1  (memory s) beqPage beqIndex = Some (PE entry) ->
nextEntryIsPP table idx res s -> nextEntryIsPP table idx res 
{|
currentPartition := currentPartition s;
memory := add table1 idx1 
      (PE
         {|
                     read := false;
                     write := false;
                     exec := false;
                     present := false;
                     user := false;
                     pa := defaultPage |}) (memory s) beqPage beqIndex |}.
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



Lemma inclGetMappedPagesRemoveVaddr phyDescChild ptVaChildpd vaChild s entry 
pdChildphy nbL1:
partitionDescriptorEntry s->
isPresentNotDefaultIff s->
noDupConfigPagesList s->
configTablesAreDifferent s->
noDupPartitionTree s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s)
            beqPage beqIndex = Some (PE entry)-> 
pa entry <> defaultPage ->
Some nbL1 = StateLib.getNbLevel -> 
incl (getMappedPages phyDescChild {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := false;
                     write := false;
                     exec := false;
                     present := false;
                     user := false;
                     pa := defaultPage |}) (memory s) beqPage beqIndex |}) 
     (getMappedPages phyDescChild s). 
Proof. 

set(s':=  {|
     currentPartition := _ |}).
intros Hcurparttree Hcons1 Hcons2 Hcons3 Hcons4 Hcons5 Hchild Hpp Hpe Htblroot 
Hnotdefault Hpresent Huser Hlookup Hmapped HnbL1. 
unfold getMappedPages.
assert(Hpd : StateLib.getPd phyDescChild (memory s) =
StateLib.getPd phyDescChild (memory s')).
unfold s'. simpl.
symmetry. apply getPdRemoveMMUPage with entry;trivial.
rewrite <- Hpd. clear Hpd.
case_eq(getPd phyDescChild (memory s));intros;[|intuition].
unfold incl.
intros apage Hs'.
unfold getMappedPagesAux in *.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).
assert (Hexistmap: getMappedPage pdChildphy s vaChild = SomePage (pa entry)).
{ apply getMappedPageGetTableRoot with  ptVaChildpd phyDescChild;trivial.
  intros;split;subst;trivial.
  unfold isEntryPage.
  rewrite Hlookup;trivial. }
assert (Hnewmapp : getMappedPage pdChildphy s' vaChild = SomeDefault).
{    subst. 
assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
(StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some (pa entry)).
{ unfold  readPhyEntry. rewrite Hlookup;trivial. }
assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some defaultPage).
{ unfold StateLib.readPhyEntry. 
cbn.
assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
(ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
beqIndex = true); intros.
rewrite <- beqPairsTrue;split;trivial.
rewrite Hpairs.
simpl;trivial. }

 apply getMappedPageNotPresent with ptVaChildpd phyDescChild;
  trivial;fold s'. 
  + intros. 
  split. 
  apply isPERemoveMMUPage with entry;trivial.
  subst;trivial.
assert(Htableroot: getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
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
  apply nextEntryIsPPRemoveMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  ;trivial.
  
  apply nextEntryIsPPgetPd;trivial.
  subst.
  rewrite <- Hind1.
  apply getIndirectionRemoveMMUPage5 with 
pdChildphy (currentPartition s) vaChild phyDescChild entry PDidx phyDescChild;trivial.
symmetry;trivial.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
omega.
apply getNbLevelEq in HnbL.
subst. apply nbLevelEq.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.

+ unfold entryPresentFlag. 
   cbn.
   subst.
   assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
      beqIndex = true).
   apply beqPairsTrue;split;trivial.
   rewrite Hpairs.
   simpl;trivial.
       
+ apply  nextEntryIsPPRemoveMMUPage with entry;trivial. }  


assert(Hremovemapp1 : getMappedPage pdChildphy s' va1 = SomeDefault). 
{ rewrite <- Hnewmapp.
  symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption. }
rewrite filterOptionInIff in *.
unfold getMappedPagesOption in *.
rewrite in_map_iff in *.
destruct Hs' as (x & Hx & Hxx).
exists x;split;trivial.
rewrite nextEntryIsPPgetPd in Hpp.
rewrite Hpp in H. inversion H;subst p.
clear H.

assert(Hor: checkVAddrsEqualityWOOffset nbLevel x va1
          (CLevel (nbLevel - 1)) = true \/ checkVAddrsEqualityWOOffset nbLevel x va1
          (CLevel (nbLevel - 1)) = false).
{ destruct(checkVAddrsEqualityWOOffset nbLevel x va1
          (CLevel (nbLevel - 1))).
      left;trivial.
      right;trivial. }
destruct Hor as [Hor | Hor];subst.
+ assert(getMappedPage pdChildphy s' x = getMappedPage pdChildphy s' va1 ).
  apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
  apply getNbLevelEqOption.
  rewrite Hremovemapp1 in H.
  rewrite Hx in H.
  inversion H.
+ rewrite <- Hx.
  apply mapPageRemoveSinglePage1 with nbL1 (StateLib.getIndexOfAddr vaChild fstLevel)
(currentPartition s)  phyDescChild entry;trivial.
symmetry;trivial.
assert(Htmp : checkVAddrsEqualityWOOffset nbLevel vaChild x (CLevel (nbLevel - 1)) = false). 
apply checkVAddrsEqualityWOOffsetTrans with va1;trivial.
rewrite <- Htmp.
f_equal.
apply getNbLevelEq;trivial.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
apply nextEntryIsPPgetPd;trivial.
apply pdPartNotNull with  phyDescChild s;trivial.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
apply nextEntryIsPPgetPd;trivial. 
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
symmetry;trivial.
intros;split;subst;trivial.
Qed.

Lemma partitionsIsolationRemoveMMUPage shadow1Child s vaChild ptVaChildpd idxvaChild phyDescChild
currentPart currentShadow descChild idxDescChild ptDescChild currentPD 
ptDescChildFromPD idxDescChild1 pdChildphy level: 
consistency s -> 
partitionsIsolation s ->
currentPart = currentPartition s ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart sh1idx currentShadow s ->
getIndexOfAddr descChild fstLevel = idxDescChild ->
isVE ptDescChild (getIndexOfAddr descChild fstLevel) s ->
getTableAddrRoot ptDescChild sh1idx currentPart
descChild s -> (defaultPage =? ptDescChild) = false ->
entryPDFlag ptDescChild idxDescChild true s ->
nextEntryIsPP currentPart PDidx currentPD s ->
isPE ptDescChildFromPD
(getIndexOfAddr descChild fstLevel) s ->
getTableAddrRoot ptDescChildFromPD PDidx currentPart descChild s ->
(defaultPage =? ptDescChildFromPD) = false ->
getIndexOfAddr descChild fstLevel = idxDescChild1 ->
entryPresentFlag ptDescChildFromPD idxDescChild1
true s ->
isEntryPage ptDescChildFromPD idxDescChild1 phyDescChild s ->
In phyDescChild (getChildren (currentPartition s) s) ->
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
getIndexOfAddr vaChild fstLevel = idxvaChild ->
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s ->
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s ->
(defaultPage =? ptVaChildpd) = false ->
entryUserFlag ptVaChildpd idxvaChild true s ->
entryPresentFlag ptVaChildpd idxvaChild true s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
partitionsIsolation
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hcons Hiso.
intros.
assert (exists entry : Pentry,
      lookup  ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      
      intuition. }

destruct Hlookup as (entry & Hlookup).
assert((pa entry) <> defaultPage).
{ assert(Hconspresent: isPresentNotDefaultIff s). { unfold consistency in *; intuition. }
  unfold isPresentNotDefaultIff in *.
  generalize (Hconspresent ptVaChildpd (getIndexOfAddr vaChild fstLevel)); 
  clear Hconspresent; intros Hconspresent.
  destruct Hconspresent as (Hleft & Hright).
  assert(Hentry :  entryPresentFlag ptVaChildpd idxvaChild true s) by trivial.
  unfold not.
  intros Htrue.
  unfold readPhyEntry in Hright.
  rewrite Hlookup in Hright.
  assert (Htmp: Some (pa entry) = Some defaultPage ); f_equal;trivial.
  apply Hright in Htmp.
  
  subst.
  assert(Htmp2: entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s)
  by trivial.
  apply entryPresentFlagReadPresent in Htmp2.
  rewrite Htmp in  Htmp2.
  inversion Htmp2. }

unfold partitionsIsolation in *.
intros parent child1 child2  Hparent Hchild1 Hchild2 Hdist.
assert(Hpart : In parent (getPartitions multiplexer s)). 
{ unfold consistency in *.
  intuition. subst.
  apply getPartitionsRemoveMMUPage   with shadow1Child ptVaChildpd pdChildphy
phyDescChild level entry vaChild;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
}
unfold consistency in *.
intuition.
assert(Hchildispart : In phyDescChild (getPartitions multiplexer s)).
{ apply childrenPartitionInPartitionList with (currentPartition s);trivial. }
assert(Hchildeq : getChildren parent s' =
                 getChildren parent s).
{ apply removeMappedPageGetChildren  with shadow1Child pdChildphy
   phyDescChild level entry ;subst;trivial.
apply pdPartNotNull with phyDescChild s;trivial.   
 }


assert(Hchild1s : In child1 (getChildren parent s)).
{ rewrite <- Hchildeq;trivial. }

assert(Hchild2s : In child2 (getChildren parent s)).
{ rewrite <- Hchildeq;trivial. }

assert(Hnotsamepart : forall part, phyDescChild <> part -> 
In part (getPartitions multiplexer s) -> 
getUsedPages part s = getUsedPages part s').
{ intros.
  apply getUsedPagesRemoveMMUPage with phyDescChild vaChild entry level ;trivial.
  intros.
  split;subst;trivial. }
subst.
assert (Hcurconfig : getConfigPages phyDescChild s = getConfigPages phyDescChild s').
{ apply getConfigPagesRemoveMMUPage1 with entry pdChildphy
  (currentPartition s)  vaChild level ;trivial.
  unfold consistency in *.
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
      apply childrenPartitionInPartitionList with parent;trivial. }
    rewrite <- Huseeq.
    clear Huseeq.
    unfold getUsedPages.
    rewrite <- Hcurconfig.
    unfold disjoint.
    intros x Hx. 
    apply in_app_iff in Hx.
    
    destruct Hx as [Hx | Hx].
    * (** In x (getConfigPages phyDescChild s **)
      rewrite in_app_iff.
      apply and_not_or.
      split.
      { (** ~ In x (getConfigPages child2 s) **) 
        assert(Hnodupconfig : configTablesAreDifferent s ).
        unfold consistency in *.
        intuition.
        unfold configTablesAreDifferent in *. 
        unfold disjoint in *. 
        apply Hnodupconfig with phyDescChild;trivial.
        apply childrenPartitionInPartitionList with parent;trivial.
 }
      { (** ~ In x (getMappedPages child2 s) **)
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
     assert(In x (getMappedPages phyDescChild s)).
     assert(Hincl : incl (getMappedPages phyDescChild s')(getMappedPages phyDescChild s)).
     apply inclGetMappedPagesRemoveVaddr with  entry pdChildphy level;trivial.
      unfold incl in *.
      apply Hincl;trivial.
      
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
       intuition. }
     subst.
     assert (Hisocase : disjoint (getUsedPages phyDescChild s) (getUsedPages child2 s)). 
     apply Hiso with (currentPartition s);trivial.
     unfold disjoint in Hisocase.
     generalize(Hisocase x );clear Hisocase;intros Hisocase. 
     unfold getUsedPages in Hisocase.
     apply Hisocase.
     simpl.
     right;simpl. 
     apply in_app_iff.
     right;trivial.
- (** phyDescChild = child2 **) 
subst child2.  
unfold disjoint.
intros x H.
unfold not; intros Hx .
contradict H.
    assert(Huseeq : getUsedPages child1 s = getUsedPages child1 s').
    { apply Hnotsamepart;trivial.
    intuition.
      apply childrenPartitionInPartitionList with parent;trivial. }
    rewrite <- Huseeq.
    clear Huseeq.
    unfold getUsedPages in *.
    rewrite <- Hcurconfig in *.
    apply in_app_iff in Hx.
    
    destruct Hx as [Hx | Hx].
    * (** In x (getConfigPages phyDescChild s **)
      rewrite in_app_iff.
      apply and_not_or.
      split.
      { (** ~ In x (getConfigPages child1 s) **) 
        assert(Hnodupconfig : configTablesAreDifferent s ).
        unfold consistency in *.
        intuition.
        unfold configTablesAreDifferent in *. 
        unfold disjoint in *. 
        apply Hnodupconfig with phyDescChild;trivial.
        apply childrenPartitionInPartitionList with parent;trivial.
        intuition.
 }
      { (** ~ In x (getMappedPages child1 s) **)
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
     assert(In x (getMappedPages phyDescChild s)).
     assert(Hincl : incl (getMappedPages phyDescChild s')(getMappedPages phyDescChild s)).
     apply inclGetMappedPagesRemoveVaddr with  entry pdChildphy level;trivial.
      unfold incl in *.
      apply Hincl;trivial.
      
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
       intuition. }
     subst.
     assert (Hisocase : disjoint (getUsedPages phyDescChild s) (getUsedPages child1 s)). 
     apply Hiso with (currentPartition s);trivial.
     intuition.
     unfold disjoint in Hisocase.
     generalize(Hisocase x );clear Hisocase;intros Hisocase. 
     unfold getUsedPages in Hisocase.
     apply Hisocase.
     simpl.
     right;simpl. 
     apply in_app_iff.
     right;trivial.
Qed.
(* Lemma getAccessibleMappedPageNotPresent 
ptvaInAncestor ancestor  pdAncestor vaInAncestor s :
( forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) -> 
(defaultPage =? ptvaInAncestor) = false ->
 entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) false s ->
nextEntryIsPP ancestor PDidx pdAncestor s -> 
getAccessibleMappedPage pdAncestor s vaInAncestor = NonePage.
Proof.
intros Hget Hnotnull  Hpresent  Hpdparent.
destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
as (Hpe2 & Hroot2);trivial.
clear Hget.
unfold getTableAddrRoot in Hroot2.
destruct Hroot2 as (_ & Htableroot).
unfold getAccessibleMappedPage.
assert(Hpd : StateLib.getPd ancestor (memory s) = Some pdAncestor).
apply nextEntryIsPPgetPd;trivial.
apply Htableroot in Hpdparent.
 clear Htableroot.
destruct Hpdparent as (nbL & HnbL & stop & Hstop & Hind ).
unfold getAccessibleMappedPage.
rewrite <- HnbL.
subst.
assert(Hnewind :getIndirection pdAncestor vaInAncestor nbL  (nbLevel - 1) s
 = Some ptvaInAncestor).
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
omega.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel);
intros;simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.
rewrite Hnewind.
rewrite Hnotnull.
apply entryPresentFlagReadPresent in Hpresent.
rewrite Hpresent.
trivial.
Qed. *)
Lemma getAccessibleMappedPageRemoveSinglePage1 s vax vaChild pdChildphy level
   ptVaChildpd 
  idxvaChild currentPart
 (* presentvaChild *) 
phyDescChild entry  : 
  let s' := {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                    {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} in 

  StateLib.getNbLevel = Some level -> 
checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false -> 

noDupConfigPagesList s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
In currentPart (getPartitions multiplexer s) ->
True -> (* In phyVaChild (getAccessibleMappedPages currentPart s) -> *)
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) ->
True -> (* negb presentvaChild = true -> *)
In phyDescChild (getPartitions multiplexer s) ->
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s ->
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s ->
(defaultPage =? ptVaChildpd) = false ->
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild ->
entryPresentFlag ptVaChildpd idxvaChild true s ->
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
pdChildphy <> defaultPage ->
getIndirection pdChildphy vaChild level (nbLevel - 1) s = Some ptVaChildpd ->
getAccessibleMappedPage pdChildphy s vax =getAccessibleMappedPage pdChildphy s' vax .
Proof. 
intros s' Hlevel Hvaneg  Hnodupconfig.
intros.

unfold getAccessibleMappedPage in *.
rewrite Hlevel in *.
case_eq(getIndirection pdChildphy vax level (nbLevel - 1) s');[intros ind Hind | intros Hind].
-  

assert(Hindeq : getIndirection pdChildphy vax level (nbLevel - 1) s = Some ind). 
{ subst.
 apply getIndirectionRemoveMMUPage4
with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
 pdChildphy currentPart  vaChild
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

{ subst. apply readPresentRemoveMMUPage with entry;trivial.
intuition. }
rewrite Hpres.
assert (Haccess :StateLib.readAccessible ind (StateLib.getIndexOfAddr vax fstLevel) (memory s) =
StateLib.readAccessible ind (StateLib.getIndexOfAddr vax fstLevel) (memory s')).

{ subst. symmetry. apply readAccessibleRemoveMMUPage;trivial.
intuition. }
rewrite Haccess.
assert (Hphy :StateLib.readPhyEntry ind (StateLib.getIndexOfAddr vax fstLevel) (memory s) =
StateLib.readPhyEntry ind (StateLib.getIndexOfAddr vax fstLevel) (memory s')).

{ subst. apply readPhyEntryRemoveMMUPage with entry;trivial.
intuition. }
rewrite Hphy;trivial.
- assert(Hnone : getIndirection pdChildphy vax level (nbLevel - 1) s = None).
 apply getIndirectionRemoveMMUPage4None with
   ptVaChildpd idxvaChild
 pdChildphy currentPart  vaChild
phyDescChild entry PDidx phyDescChild;subst;trivial.  left;trivial.
subst;trivial.
rewrite Hnone;trivial.
Qed. 

Lemma inclGetAccessibleMappedPagesRemoveVaddr phyDescChild ptVaChildpd vaChild s entry 
pdChildphy nbL1:
partitionDescriptorEntry s->
isPresentNotDefaultIff s->
noDupConfigPagesList s->
configTablesAreDifferent s->
noDupPartitionTree s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s)
            beqPage beqIndex = Some (PE entry)-> 
pa entry <> defaultPage ->
Some nbL1 = StateLib.getNbLevel -> 
forall apage, In apage (getAccessibleMappedPages phyDescChild {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := false;
                     write := false;
                     exec := false;
                     present := false;
                     user := false;
                     pa := defaultPage |}) (memory s) beqPage beqIndex |}) -> 
                     
   In apage (getAccessibleMappedPages phyDescChild s). 
Proof. 
set(s':=  {|
     currentPartition := _ |}).
intros Hcurparttree Hcons1 Hcons2 Hcons3 Hcons4 Hcons5 Hchild Hpp Hpe Htblroot 
Hnotdefault Hpresent Huser Hlookup Hmapped HnbL1 apage Hs'. 
unfold getAccessibleMappedPages in *.
assert(Hpd : StateLib.getPd phyDescChild (memory s') =
StateLib.getPd phyDescChild (memory s)).
unfold s'. simpl.
apply getPdRemoveMMUPage with entry;trivial.
rewrite  Hpd in *. clear Hpd.
case_eq(getPd phyDescChild (memory s));[intros pd Hpd |intros Hpd] ;rewrite Hpd in *;[|intuition].
unfold incl.
unfold getAccessibleMappedPagesAux in *.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).
assert (Hexistmap: getAccessibleMappedPage pdChildphy s vaChild = SomePage (pa entry)).
{ apply isAccessibleMappedPage2 with phyDescChild ptVaChildpd ;subst;trivial.
  unfold isEntryPage.
  rewrite Hlookup;trivial.
    intros;split;subst;trivial. }
assert (Hnewmapp : getAccessibleMappedPage pdChildphy s' vaChild = NonePage).
{    subst. 
assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
(StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some (pa entry)).
{ unfold  readPhyEntry. rewrite Hlookup;trivial. }
assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some defaultPage).
{ unfold StateLib.readPhyEntry. 
cbn.
assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
(ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
beqIndex = true); intros.
rewrite <- beqPairsTrue;split;trivial.
rewrite Hpairs.
simpl;trivial. }
apply getAccessibleMappedPageNotPresent with ptVaChildpd phyDescChild;
  trivial;fold s'. 
  + intros. 
  split. 
  apply isPERemoveMMUPage with entry;trivial.
  subst;trivial.
assert(Htableroot: getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
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
  apply nextEntryIsPPRemoveMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  ;trivial.
  
  apply nextEntryIsPPgetPd;trivial.
  subst.
  rewrite <- Hind1.
  apply getIndirectionRemoveMMUPage5 with 
pdChildphy (currentPartition s) vaChild phyDescChild entry PDidx phyDescChild;trivial.
symmetry;trivial.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
omega.
apply getNbLevelEq in HnbL.
subst. apply nbLevelEq.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.

+ unfold entryPresentFlag. 
   cbn.
   subst.
   assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
      beqIndex = true).
   apply beqPairsTrue;split;trivial.
   rewrite Hpairs.
   simpl;trivial.
       
+ apply  nextEntryIsPPRemoveMMUPage with entry;trivial. }  


assert(Hremovemapp1 : getAccessibleMappedPage pdChildphy s' va1 = NonePage). 
{ rewrite <- Hnewmapp.
  symmetry.
apply getAccessibleMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption. }
rewrite filterOptionInIff in *.
unfold getAccessibleMappedPagesOption in *.
rewrite in_map_iff in *.
destruct Hs' as (x & Hx & Hxx).
exists x;split;trivial.
rewrite nextEntryIsPPgetPd in Hpp.
rewrite Hpp in Hpd. inversion Hpd;subst pd.
clear Hpd.
assert(Hor: checkVAddrsEqualityWOOffset nbLevel x va1
          (CLevel (nbLevel - 1)) = true \/ checkVAddrsEqualityWOOffset nbLevel x va1
          (CLevel (nbLevel - 1)) = false).
{ destruct(checkVAddrsEqualityWOOffset nbLevel x va1
          (CLevel (nbLevel - 1))).
      left;trivial.
      right;trivial. }
destruct Hor as [Hor | Hor];subst.
+ assert(getAccessibleMappedPage pdChildphy s' x = getAccessibleMappedPage pdChildphy s' va1 ).
  apply getAccessibleMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
  apply getNbLevelEqOption.
  rewrite Hremovemapp1 in H.
  rewrite Hx in H.
  inversion H.
+ rewrite <- Hx.
  apply getAccessibleMappedPageRemoveSinglePage1 with nbL1 (StateLib.getIndexOfAddr vaChild fstLevel)
(currentPartition s)  phyDescChild entry;trivial.
symmetry;trivial.
assert(Htmp : checkVAddrsEqualityWOOffset nbLevel vaChild x (CLevel (nbLevel - 1)) = false). 
apply checkVAddrsEqualityWOOffsetTrans with va1;trivial.
rewrite <- Htmp.
f_equal.
apply getNbLevelEq;trivial.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
apply nextEntryIsPPgetPd;trivial.
apply pdPartNotNull with  phyDescChild s;trivial.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
apply nextEntryIsPPgetPd;trivial. 
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
symmetry;trivial.
intros;split;subst;trivial.
Qed.


Lemma kernelDataIsolationRemoveMMUPage shadow1Child s vaChild ptVaChildpd idxvaChild phyDescChild
currentPart currentShadow descChild idxDescChild ptDescChild currentPD 
ptDescChildFromPD idxDescChild1 pdChildphy level: 
consistency s -> 
kernelDataIsolation s ->
currentPart = currentPartition s ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart sh1idx currentShadow s ->
getIndexOfAddr descChild fstLevel = idxDescChild ->
isVE ptDescChild (getIndexOfAddr descChild fstLevel) s ->
getTableAddrRoot ptDescChild sh1idx currentPart
descChild s -> (defaultPage =? ptDescChild) = false ->
entryPDFlag ptDescChild idxDescChild true s ->
nextEntryIsPP currentPart PDidx currentPD s ->
isPE ptDescChildFromPD
(getIndexOfAddr descChild fstLevel) s ->
getTableAddrRoot ptDescChildFromPD PDidx currentPart descChild s ->
(defaultPage =? ptDescChildFromPD) = false ->
getIndexOfAddr descChild fstLevel = idxDescChild1 ->
entryPresentFlag ptDescChildFromPD idxDescChild1
true s ->
isEntryPage ptDescChildFromPD idxDescChild1 phyDescChild s ->
In phyDescChild (getChildren (currentPartition s) s) ->
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
getIndexOfAddr vaChild fstLevel = idxvaChild ->
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s ->
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s ->
(defaultPage =? ptVaChildpd) = false ->
entryUserFlag ptVaChildpd idxvaChild true s ->
entryPresentFlag ptVaChildpd idxvaChild true s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
kernelDataIsolation
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hcons Hiso.
intros.
assert (exists entry : Pentry,
      lookup  ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      
      intuition. }

destruct Hlookup as (entry & Hlookup).
assert((pa entry) <> defaultPage).
{ assert(Hconspresent: isPresentNotDefaultIff s). { unfold consistency in *; intuition. }
  unfold isPresentNotDefaultIff in *.
  generalize (Hconspresent ptVaChildpd (getIndexOfAddr vaChild fstLevel)); 
  clear Hconspresent; intros Hconspresent.
  destruct Hconspresent as (Hleft & Hright).
  assert(Hentry :  entryPresentFlag ptVaChildpd idxvaChild true s) by trivial.
  unfold not.
  intros Htrue.
  unfold readPhyEntry in Hright.
  rewrite Hlookup in Hright.
  assert (Htmp: Some (pa entry) = Some defaultPage ); f_equal;trivial.
  apply Hright in Htmp.
  
  subst.
  assert(Htmp2: entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s)
  by trivial.
  apply entryPresentFlagReadPresent in Htmp2.
  rewrite Htmp in  Htmp2.
  inversion Htmp2. }
unfold kernelDataIsolation in *.
intros partition1 partition2  Hpart1 Hpart2 .
assert(Hcurpart : In (currentPartition s) (getPartitions multiplexer s)).
{ unfold consistency in *. 
  unfold currentPartitionInPartitionsList in *.
  intuition. }
unfold consistency in *.
intuition.
assert(Hchild : In phyDescChild (getPartitions multiplexer s)).
{ unfold consistency in *.
  apply childrenPartitionInPartitionList with currentPart;intuition;subst;trivial. }
subst.
assert(Haccess : In (pa entry) (getAccessibleMappedPages phyDescChild s)). 
{ apply physicalPageIsAccessible
   with ptVaChildpd vaChild (getIndexOfAddr vaChild fstLevel) true  level true pdChildphy;trivial.
  intros;split;
  subst;trivial.
  intuition;subst;trivial.
  intuition;subst;trivial.
  subst;trivial.
  unfold isEntryPage;rewrite Hlookup;trivial. }

assert(Hpart1mult : In partition1 (getPartitions multiplexer s)). 
{ unfold consistency in *.
  intuition. subst.
  apply getPartitionsRemoveMMUPage   with shadow1Child ptVaChildpd pdChildphy
phyDescChild level entry vaChild;trivial.
apply pdPartNotNull with phyDescChild s;trivial. }
assert(Hconfigdiff : configTablesAreDifferent s).
{ unfold consistency in *. intuition. } 

assert(Hpart2mult : In partition2 (getPartitions multiplexer s)). 
{ unfold consistency in *.
  intuition. subst.
  apply getPartitionsRemoveMMUPage   with shadow1Child ptVaChildpd pdChildphy
phyDescChild level entry vaChild;trivial.
apply pdPartNotNull with phyDescChild s;trivial. }

assert(Hinconfig : In ptVaChildpd (getConfigPages phyDescChild s)). 
{ apply isConfigTable with vaChild ;trivial.
  intros;subst;split;trivial. }
assert(Hnotsamepart : forall part, phyDescChild <> part -> 
In part (getPartitions multiplexer s) -> 
getUsedPages part s = getUsedPages part s').
{ intros.
  apply getUsedPagesRemoveMMUPage with phyDescChild vaChild entry level ;trivial.
  intros.
  split;subst;trivial. }
subst.
assert (Hcurconfig : getConfigPages phyDescChild s = getConfigPages phyDescChild s').
{ apply getConfigPagesRemoveMMUPage1 with entry pdChildphy
  (currentPartition s)  vaChild level ;trivial.
  unfold consistency in *.
  intuition. }
assert(Hor3:  ( phyDescChild <> partition1 /\ phyDescChild <> partition2) \/
            (phyDescChild = partition1 \/ phyDescChild = partition2)).
{ clear. destruct phyDescChild;destruct partition1 ; destruct partition2.
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
assert(Hconfig :forall part, In part (getPartitions multiplexer s) -> 
     getConfigPages part s = getConfigPages part s').
{ intros. assert (Hor : phyDescChild = part \/ 
    phyDescChild <> part) by apply pageDecOrNot.
  destruct Hor as [Hor | Hor].
  subst.
  + apply getConfigPagesRemoveMMUPage1 with entry pdChildphy
  (currentPartition s)  vaChild level ;trivial.
  unfold consistency in *.
  intuition. 
  + apply getConfigPagesRemoveMMUPage with phyDescChild entry;trivial.
    apply Hconfigdiff;trivial. }
rewrite <- Hconfig;trivial.

destruct Hor3 as [Hor3| Hor3].
+ (*phyDescChild <> child1 /\ phyDescChild <> child2 *)
 destruct Hor3 as (Hor1 & Hor2).
 assert(Hnodup :  noDupPartitionTree s).
 unfold consistency in *.
 intuition.
 assert(Hmaps: getAccessibleMappedPages partition1 s =
        getAccessibleMappedPages partition1 s').
  { apply getAccessibleMappedPagesRemoveMMUPage with phyDescChild vaChild
      entry level;intuition.    
    subst.
    intuition. }
  rewrite <- Hmaps. clear Hmaps.
  apply Hiso;trivial.
+ destruct Hor3 as [Hor3 | Hor3]. 
  - subst partition1.
  assert(Hiso1 : disjoint (getAccessibleMappedPages phyDescChild s)
  (getConfigPages partition2 s)).
  apply Hiso;trivial.
  unfold disjoint in Hiso1.
  unfold disjoint.
  intros x Hx.
  apply Hiso1. 
  apply inclGetAccessibleMappedPagesRemoveVaddr with ptVaChildpd vaChild
entry pdChildphy level;trivial.
- subst partition2.
  assert(Hor: partition1 = phyDescChild \/ partition1 <> phyDescChild)by apply pageDecOrNot.
  destruct Hor as [Hor | Hor];subst.
  * assert(Hiso1 : disjoint (getAccessibleMappedPages phyDescChild s)
                      (getConfigPages phyDescChild s)).
    apply Hiso;trivial.
    unfold disjoint in Hiso1.
    unfold disjoint.
    intros x Hx.
    apply Hiso1.
    apply inclGetAccessibleMappedPagesRemoveVaddr with ptVaChildpd vaChild
    entry pdChildphy level;trivial.
  * assert(Hiso1 : disjoint (getAccessibleMappedPages partition1 s)
                      (getConfigPages phyDescChild s)).
    apply Hiso;trivial.
    unfold disjoint in Hiso1.
    unfold disjoint.
    intros x Hx.
    apply Hiso1.
    assert(Hmaps: getAccessibleMappedPages partition1 s =
        getAccessibleMappedPages partition1 s').
  { apply getAccessibleMappedPagesRemoveMMUPage with phyDescChild vaChild
      entry level;subst;intuition.
      subst;trivial. }
  rewrite Hmaps;trivial.
Qed.

Lemma verticalSharingRemoveMMUPage shadow1Child s vaChild ptVaChildpd idxvaChild phyDescChild
currentPart currentShadow descChild idxDescChild ptDescChild currentPD 
ptDescChildFromPD idxDescChild1 pdChildphy level ptVaChildFromSh1 vainve: 
consistency s -> 
verticalSharing s ->
kernelDataIsolation s -> 
currentPart = currentPartition s ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart sh1idx currentShadow s ->
getIndexOfAddr descChild fstLevel = idxDescChild ->
isVE ptDescChild (getIndexOfAddr descChild fstLevel) s ->
getTableAddrRoot ptDescChild sh1idx currentPart
descChild s -> (defaultPage =? ptDescChild) = false ->
entryPDFlag ptDescChild idxDescChild true s ->
nextEntryIsPP currentPart PDidx currentPD s ->
isPE ptDescChildFromPD
(getIndexOfAddr descChild fstLevel) s ->
getTableAddrRoot ptDescChildFromPD PDidx currentPart descChild s ->
(defaultPage =? ptDescChildFromPD) = false ->
getIndexOfAddr descChild fstLevel = idxDescChild1 ->
entryPresentFlag ptDescChildFromPD idxDescChild1
true s ->
isEntryPage ptDescChildFromPD idxDescChild1 phyDescChild s ->
In phyDescChild (getChildren (currentPartition s) s) ->
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
getIndexOfAddr vaChild fstLevel = idxvaChild ->
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s ->
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s ->
(defaultPage =? ptVaChildpd) = false ->
entryUserFlag ptVaChildpd idxvaChild true s ->
entryPresentFlag ptVaChildpd idxvaChild true s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
isVE ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildFromSh1 sh1idx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildFromSh1) = false-> 
beqVAddr defaultVAddr vainve = true -> 
isEntryVA ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) vainve s -> 

verticalSharing
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hcons Hiso.
intros.
assert (exists entry : Pentry,
      lookup  ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      
      intuition. }

destruct Hlookup as (entry & Hlookup).
assert((pa entry) <> defaultPage).
{ assert(Hconspresent: isPresentNotDefaultIff s). { unfold consistency in *; intuition. }
  unfold isPresentNotDefaultIff in *.
  generalize (Hconspresent ptVaChildpd (getIndexOfAddr vaChild fstLevel)); 
  clear Hconspresent; intros Hconspresent.
  destruct Hconspresent as (Hleft & Hright).
  assert(Hentry :  entryPresentFlag ptVaChildpd idxvaChild true s) by trivial.
  unfold not.
  intros Htrue.
  unfold readPhyEntry in Hright.
  rewrite Hlookup in Hright.
  assert (Htmp: Some (pa entry) = Some defaultPage ); f_equal;trivial.
  apply Hright in Htmp.
  
  subst.
  assert(Htmp2: entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s)
  by trivial.
  apply entryPresentFlagReadPresent in Htmp2.
  rewrite Htmp in  Htmp2.
  inversion Htmp2. }
assert (Hvs : verticalSharing s) by trivial.
unfold verticalSharing in *.
intros parent child Hvs1 Hvs2.
unfold consistency in *;intuition;subst.
assert(Hcurpart : In (currentPartition s) (getPartitions multiplexer s)).
{ unfold currentPartitionInPartitionsList in *;trivial. }

assert(Hchild : In phyDescChild (getPartitions multiplexer s)).
{ 
  apply childrenPartitionInPartitionList with (currentPartition s) ;trivial. } 

assert(Hcons1: accessibleChildPageIsAccessibleIntoParent s);trivial.

assert(Hparentmult : In parent (getPartitions multiplexer s)). 
{ apply getPartitionsRemoveMMUPage   with shadow1Child ptVaChildpd pdChildphy
    phyDescChild level entry vaChild;trivial.
  apply pdPartNotNull with phyDescChild s;trivial. }
assert(Hchildeq : getChildren parent s' =
                 getChildren parent s).
{ apply removeMappedPageGetChildren  with shadow1Child pdChildphy
   phyDescChild level entry ;subst;trivial.
apply pdPartNotNull with phyDescChild s;trivial.   
 }
assert(Hchild1s : In child (getChildren parent s)).
{ rewrite <- Hchildeq;trivial. }

assert(Hinconfig : In ptVaChildpd (getConfigPages phyDescChild s)). 
{ apply isConfigTable with vaChild ;trivial.
  intros;subst;split;trivial. }

assert(Hconfigdiff : configTablesAreDifferent s) by trivial.

assert (Hcurconfig : getConfigPages phyDescChild s = getConfigPages phyDescChild s').
{ apply getConfigPagesRemoveMMUPage1 with entry pdChildphy
  (currentPartition s)  vaChild level ;trivial.
  unfold consistency in *.
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

assert(Hisparent : isParent s) by trivial.
destruct Hor3 as [Hor3| Hor3].
+ (** phyDescChild <> child /\ phyDescChild <> parent **)
  destruct Hor3 as (Hor1 & Hor2).
  assert(Hused : getUsedPages child s' = getUsedPages child s). 
  { intros.
    symmetry.
    apply getUsedPagesRemoveMMUPage with phyDescChild vaChild entry level ;trivial.
    intros.
    split;subst;trivial.
    apply childrenPartitionInPartitionList with parent;trivial. }
  rewrite Hused. clear Hused.
  assert(Hmap : getMappedPages parent s = getMappedPages parent s').
  { apply getMappedPagesRemoveMMUPage with phyDescChild vaChild
      entry level;subst;intuition.
    subst;trivial. } 
  rewrite <- Hmap.
  apply Hvs;trivial.
+  destruct Hor3 as [Hor3 | Hor3]. 
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
    { apply getMappedPagesRemoveMMUPage with phyDescChild vaChild
      entry level;subst;intuition.
      subst;trivial. } 
    rewrite <- Hmap.
    unfold incl.
    intros x Hx. 
    assert (Hvs' : incl (getUsedPages phyDescChild s) (getMappedPages parent s))by
    (apply Hvs;trivial).  
    unfold incl in *.
    apply Hvs'.  clear Hvs'.
      unfold getUsedPages in *.
    rewrite in_app_iff in *.
    destruct Hx as [Hx | Hx].
    left.
    rewrite Hcurconfig;trivial.
    right.
    assert(Hincl : incl (getMappedPages phyDescChild s')(getMappedPages phyDescChild s)).
    apply inclGetMappedPagesRemoveVaddr with  entry pdChildphy level;trivial.
    unfold incl in *.
    apply Hincl;trivial.
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
    { intros.
      symmetry.
      apply getUsedPagesRemoveMMUPage with phyDescChild vaChild entry level ;trivial.
      intros.
      split;subst;trivial.
      apply childrenPartitionInPartitionList with phyDescChild;trivial. }
    rewrite Hused. clear Hused.
    unfold incl.
    intros x Hx.
    assert(Hmykey : x = (pa entry)  \/ x <> pa entry) by apply pageDecOrNot.
    destruct Hmykey as [Hmykey | Hmykey].
    * subst.
      assert(Hnotshared : ~ isDerived phyDescChild vaChild s ).
      { apply vaNotDerived with ptVaChildFromSh1;trivial.
        unfold consistency in *;intuition.
        exists defaultVAddr;split;trivial.
        assert(defaultVAddr =vainve).
        apply beqVAddrTrueEq;trivial.
        subst. trivial.
        apply beqVAddrTrue.
        intros;split;subst;trivial. }
      assert(  ~ In (pa entry) (getMappedPages child s)).
      { apply phyNotDerived with phyDescChild pdChildphy  vaChild ptVaChildpd;trivial.
        unfold consistency in *;intuition.
        intros;split;subst;trivial.
        unfold isEntryPage.
        rewrite Hlookup;trivial. }
      unfold getUsedPages in Hx.
      rewrite in_app_iff in Hx.
      destruct Hx as [Hx|Hx]; try now contradict Hx.
      assert(Hkiso : disjoint (getAccessibleMappedPages phyDescChild s)
            (getConfigPages child s)).
       { assert(Hki:  kernelDataIsolation s) by trivial.
         unfold kernelDataIsolation in *.
         apply Hki;trivial.
         apply childrenPartitionInPartitionList with phyDescChild ; 
          (unfold consistency in *; intuition). }
       unfold disjoint in Hkiso.
       assert(Hnotconfig: ~ In (pa entry) (getConfigPages child s)).
       apply  Hkiso;trivial.
       apply physicalPageIsAccessible with ptVaChildpd vaChild
         (getIndexOfAddr vaChild fstLevel) true level true pdChildphy;trivial.
       intros;split;subst;trivial.
       unfold isEntryPage;rewrite Hlookup;trivial.
       now contradict Hnotconfig.
     * assert(Hor : In x(getMappedPages phyDescChild s) \/ 
              ~In x(getMappedPages phyDescChild s) ) by apply listPageDecOrNot.
       destruct Hor as [Hor|Hor].
       ++ unfold getMappedPages .
          unfold getMappedPages in Hor.
          assert(Hpd : StateLib.getPd phyDescChild (memory s) =
              StateLib.getPd phyDescChild (memory s')).
           { unfold s'. simpl.
             symmetry. apply getPdRemoveMMUPage with entry;trivial. }
          assert(Hpppd: nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
          rewrite nextEntryIsPPgetPd in *.
          rewrite <- Hpd.
          rewrite Hpppd in *.  
          unfold getMappedPagesAux in *.
          apply filterOptionInIff.
          apply filterOptionInIff in Hor.
          unfold getMappedPagesOption in *.
          apply in_map_iff.
          apply in_map_iff in Hor.
          destruct Hor as (vax & Hvax & Hva).
          exists vax;split;trivial.
          assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
                     StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va1 ( CLevel (nbLevel -1) ) = true )
                     by apply AllVAddrWithOffset0.
          destruct Heqvars as (va1 & Hva1 & Hva11).
          assert(Hor1 :checkVAddrsEqualityWOOffset nbLevel vaChild vax level = true \/ 
             checkVAddrsEqualityWOOffset nbLevel vaChild vax level = false).
          { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild vax level);intuition. }
            destruct Hor1 as [Hor1 | Hor1].
            -- assert (Hmapsfalse : getMappedPage pdChildphy s vaChild = 
                    getMappedPage pdChildphy s vax).
                { apply getMappedPageEq with level;trivial .
                  symmetry;trivial. }
               assert (Hexistmap: getMappedPage pdChildphy s vaChild = SomePage (pa entry)).
               { apply getMappedPageGetTableRoot with  ptVaChildpd phyDescChild;trivial.
                 intros;split;subst;trivial.
                 unfold isEntryPage.
                 rewrite Hlookup;trivial. apply nextEntryIsPPgetPd;trivial. }
               rewrite Hvax in Hmapsfalse. rewrite Hexistmap in Hmapsfalse.
               inversion Hmapsfalse.
               subst; now contradict Hmykey.
            -- rewrite <- Hvax. symmetry.
               apply mapPageRemoveSinglePage1 with level (StateLib.getIndexOfAddr vaChild fstLevel)
               (currentPartition s)  phyDescChild entry;trivial.
               symmetry;trivial.
               apply nextEntryIsPPgetPd;trivial.
               apply pdPartNotNull with phyDescChild s;trivial.
               apply nextEntryIsPPgetPd;trivial.
               apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
               symmetry;trivial.
               intros;subst;split;trivial.
       ++ assert(Hismapped: In x (getMappedPages phyDescChild s)).
          assert(Hin: incl (getUsedPages child s) (getMappedPages phyDescChild s)). 
          
          apply Hvs;trivial.
          unfold incl in Hin.
          apply Hin;trivial.
          now contradict Hismapped.
Qed.

Lemma partitionDescriptorEntryRemoveMMUPage
shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
partitionDescriptorEntry
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
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
apply getPartitionsRemoveMMUPage with shadow1Child ptVaChildpd pdChildphy
    phyDescChild level entry vaChild;trivial.
split;trivial.
split.
apply isVARemoveMMUPage with entry;trivial.
destruct Hi3 as (pp & Hpp & Hnotdef).
exists pp;split;trivial.
apply nextEntryIsPPRemoveMMUPage with entry;trivial.
Qed.
Lemma  dataStructurePdSh1Sh2asRootRemoveMMUPagePD shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
dataStructurePdSh1Sh2asRoot PDidx s -> 
dataStructurePdSh1Sh2asRoot PDidx
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros.
assert(Hpde : dataStructurePdSh1Sh2asRoot PDidx s) by trivial.
unfold dataStructurePdSh1Sh2asRoot in *.
intros.
assert(Hparts : In partition (getPartitions multiplexer s)).
apply getPartitionsRemoveMMUPage with shadow1Child ptVaChildpd pdChildphy
    phyDescChild level entry vaChild;trivial.
assert(Hpp': nextEntryIsPP partition PDidx entry0 s).
apply nextEntryIsPPRemoveMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  ;trivial.
assert(Hind : getIndirection entry0 va level0 stop s = Some indirection).
{ apply getIndirectionRemoveMMUPage4
with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
 pdChildphy (currentPartition s)  vaChild
phyDescChild entry PDidx partition;trivial.
symmetry;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
apply nextEntryIsPPgetPd;trivial.
symmetry;trivial.
intros;subst;split;trivial.
subst.
left;trivial. }
assert(Hlevel : Some level0 = StateLib.getNbLevel)by trivial.
assert(HT : True);trivial.
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
  apply isPERemoveMMUPage with entry;trivial.
+ right. split; trivial. 
  destruct Hpde as [(Hvalue & Hidxpd) | [(Hvalue & Hidxpd) |(Hvalue & Hidxpd)]].
  - contradict Hidxpd.
    apply  idxPDidxSh1notEq.
  - contradict Hidxpd.
    apply idxPDidxSh2notEq.
  - do 2 right.
    split;trivial.
    apply isPERemoveMMUPage with entry;trivial.
Qed.

Lemma  dataStructurePdSh1Sh2asRootRemoveMMUPageSh1 shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
dataStructurePdSh1Sh2asRoot sh1idx s -> 
dataStructurePdSh1Sh2asRoot sh1idx
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros.
assert(Hpde : dataStructurePdSh1Sh2asRoot sh1idx s) by trivial.
unfold dataStructurePdSh1Sh2asRoot in *.
intros.
assert(Hparts : In partition (getPartitions multiplexer s)).
apply getPartitionsRemoveMMUPage with shadow1Child ptVaChildpd pdChildphy
    phyDescChild level entry vaChild;trivial.
assert(Hpp': nextEntryIsPP partition sh1idx entry0 s).
apply nextEntryIsPPRemoveMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  ;trivial.
assert(Hind : getIndirection entry0 va level0 stop s = Some indirection).
{ apply getIndirectionRemoveMMUPage4
with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
 pdChildphy (currentPartition s)  vaChild
phyDescChild entry sh1idx partition;trivial.
symmetry;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
apply nextEntryIsPPgetPd;trivial.
symmetry;trivial.
intros;subst;split;trivial.
subst.
right.
left;trivial. }
assert(Hlevel : Some level0 = StateLib.getNbLevel)by trivial.
assert(HT : True);trivial.
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
  apply isPERemoveMMUPage with entry;trivial.
+ right. split; trivial. 
  destruct Hpde as [(Hvalue & Hidxpd) | [(Hvalue & Hidxpd) |(Hvalue & Hidxpd)]].
  - left. split;trivial.
    apply isVERemoveMMUPage with entry;trivial.
  - contradict Hidxpd.
    symmetrynot.    apply idxSh2idxSh1notEq. 
  - contradict Hidxpd.
    symmetrynot.
    apply idxPDidxSh1notEq.
Qed.

Lemma  dataStructurePdSh1Sh2asRootRemoveMMUPageSh2 shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
dataStructurePdSh1Sh2asRoot sh2idx s -> 
dataStructurePdSh1Sh2asRoot sh2idx
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros.
assert(Hpde : dataStructurePdSh1Sh2asRoot sh2idx s) by trivial.
unfold dataStructurePdSh1Sh2asRoot in *.
intros.
assert(Hparts : In partition (getPartitions multiplexer s)).
apply getPartitionsRemoveMMUPage with shadow1Child ptVaChildpd pdChildphy
    phyDescChild level entry vaChild;trivial.
assert(Hpp': nextEntryIsPP partition sh2idx entry0 s).
apply nextEntryIsPPRemoveMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  ;trivial.
assert(Hind : getIndirection entry0 va level0 stop s = Some indirection).
{ apply getIndirectionRemoveMMUPage4
with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
 pdChildphy (currentPartition s)  vaChild
phyDescChild entry sh2idx partition;trivial.
symmetry;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
apply nextEntryIsPPgetPd;trivial.
symmetry;trivial.
intros;subst;split;trivial.
subst.
right;right;trivial. }
assert(Hlevel : Some level0 = StateLib.getNbLevel)by trivial.
assert(HT : True);trivial.
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
  apply isPERemoveMMUPage with entry;trivial.
+ right. split; trivial. 
  destruct Hpde as [(Hvalue & Hidxpd) | [(Hvalue & Hidxpd) |(Hvalue & Hidxpd)]].
  - contradict Hidxpd.
    apply idxSh2idxSh1notEq. 
  - right; left. split;trivial.
    apply isVARemoveMMUPage with entry;trivial.
  - contradict Hidxpd.
    symmetrynot.
    apply idxPDidxSh2notEq.
Qed.

Lemma  currentPartitionInPartitionsListRemoveMMUPage shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
currentPartitionInPartitionsList s -> 
currentPartitionInPartitionsList
{|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                    {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
unfold currentPartitionInPartitionsList;simpl.
intros.
set(s' :=  {|
         currentPartition := _ |}) in *.
assert(Hparteq :getPartitions multiplexer s' = getPartitions multiplexer s).
apply getPartitionsRemoveMMUPage1 with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparteq.
trivial.
Qed.

Lemma noDupMappedPagesListRemoveMMUPage shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
noDupMappedPagesList s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
noDupMappedPagesList {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd  (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros.
assert (lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage
        beqIndex = Some (PE entry)) as Hlookup; trivial.
assert(Htblroot:getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
assert(Hnodup : noDupMappedPagesList s) by trivial.
unfold noDupMappedPagesList in *.
intros partition Hpart.
assert(Hparts : In partition (getPartitions multiplexer s)).
apply getPartitionsRemoveMMUPage with shadow1Child ptVaChildpd pdChildphy
    phyDescChild level entry vaChild;trivial.
assert (Hnodup1 : NoDup (getMappedPages partition s) ).
apply Hnodup;trivial. clear Hnodup.
assert ( Hor : partition = phyDescChild \/ partition <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [ Hor | Hor]. 
+ subst. 
  unfold getMappedPages in Hnodup1.
  unfold getMappedPages. 
 assert(Hpd : StateLib.getPd phyDescChild (memory s) =
        StateLib.getPd phyDescChild (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdRemoveMMUPage with entry;trivial. }
rewrite <- Hpd in *. 
case_eq(StateLib.getPd phyDescChild (memory s) );[intros pd Hpdpart | intros Hpdpart];[|constructor].
rewrite Hpdpart in *.
subst.
  symmetry in Hpd. 
  assert (pd = pdChildphy).
  { rewrite nextEntryIsPPgetPd in *.
    rewrite Hpdpart in *.
    assert(Heq : Some pd = Some pdChildphy) by trivial.
    inversion Heq;subst;trivial. }
  subst. 
(*   assert(Hnodupva : NoDup getAllVAddr) by apply noDupAllVaddr. *)

  assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).
assert (Hexistmap: getMappedPage pdChildphy s vaChild = SomePage (pa entry)).
{ apply getMappedPageGetTableRoot with  ptVaChildpd phyDescChild;trivial.
  intros;split;subst;trivial.
  unfold isEntryPage.
  rewrite Hlookup;trivial. }
assert (Hnewmapp : getMappedPage pdChildphy s' vaChild = SomeDefault).
{    subst. 
assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
(StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some (pa entry)).
{ unfold  readPhyEntry. rewrite Hlookup;trivial. }
assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some defaultPage).
{ unfold StateLib.readPhyEntry. 
cbn.
assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
(ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
beqIndex = true); intros.
rewrite <- beqPairsTrue;split;trivial.
rewrite Hpairs.
simpl;trivial. }

 apply getMappedPageNotPresent with ptVaChildpd phyDescChild;
  trivial;fold s'. 
  + intros. 
  split. 
  apply isPERemoveMMUPage with entry;trivial.
  subst;trivial.
assert(Htableroot: getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
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
  apply nextEntryIsPPRemoveMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  ;trivial.
  subst.
  rewrite <- Hind1.
  apply getIndirectionRemoveMMUPage5 with 
pdChildphy (currentPartition s) vaChild phyDescChild entry PDidx phyDescChild;trivial.
symmetry;trivial.
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
omega.
apply getNbLevelEq in HnbL.
subst. apply nbLevelEq.

+ unfold entryPresentFlag. 
   cbn.
   subst.
   assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
      beqIndex = true).
   apply beqPairsTrue;split;trivial.
   rewrite Hpairs.
   simpl;trivial.
       
+ apply  nextEntryIsPPRemoveMMUPage with entry;trivial. } 
  assert (Hmap1 : getMappedPage pdChildphy s vaChild = 
                    getMappedPage pdChildphy s va1).
  { apply getMappedPageEq with (CLevel (nbLevel - 1));trivial .
    symmetry;trivial.
    assert(Hlevel : Some level = getNbLevel) by trivial.
    rewrite <- Hlevel.
    symmetry.
    f_equal.
    apply getNbLevelEq;trivial. }
  assert(Hmap2: getMappedPage pdChildphy s' vaChild = getMappedPage pdChildphy s' va1 ).
  { apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
    apply getNbLevelEqOption. }
  rewrite Hexistmap in *.
  rewrite Hnewmapp in *.
  assert(Hmykey2: In (pa entry)
            (getMappedPagesAux pdChildphy getAllVAddrWithOffset0 s)).
  { assert (Htmp: In (pa entry) (getMappedPages phyDescChild s)).
    { apply inGetMappedPagesGetTableRoot with vaChild ptVaChildpd pdChildphy;trivial.
      intros;split;subst;trivial.
      unfold isEntryPage ;rewrite Hlookup;trivial. }
      unfold getMappedPages in Htmp.
      assert(Hpp : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
      apply nextEntryIsPPgetPd in Hpp.
      rewrite Hpp in Htmp;trivial. }
    
  assert(Hmykey4 : ~ In (pa entry)
            (getMappedPagesAux pdChildphy getAllVAddrWithOffset0 s')).            
  { 
   unfold getMappedPagesAux in *.
   rewrite filterOptionInIff.
   unfold getMappedPagesOption.
   rewrite in_map_iff.
   unfold not;intros Hx1.
   destruct Hx1 as (a & Hx1 & Hxx1).
   assert(Htrueor :  a=va1\/  a <> va1) by apply vaddrDecOrNot.
     destruct Htrueor as [Htrueor |Htrueor].
  subst.
  rewrite Hx1 in Hmap2.
  now contradict Hmap2.
  assert (Hmapeq: getMappedPage pdChildphy s a = getMappedPage pdChildphy s' a).
    { apply mapPageRemoveSinglePage1 with level (getIndexOfAddr vaChild fstLevel)
        (currentPartition s) phyDescChild entry;trivial.
      + symmetry;trivial.
      + assert(Htrue:checkVAddrsEqualityWOOffset nbLevel va1 a level = false). 
        { unfold getAllVAddrWithOffset0 in *.
          rewrite filter_In in *.
          apply checkVAddrsEqualityWOOffsetFalseEqOffset;intuition.
        
 }
        apply checkVAddrsEqualityWOOffsetTrans with va1;trivial.
            rewrite <- Hva11.
            f_equal.
            apply getNbLevelEq;trivial.
            rewrite <- Htrue.
            apply checkVAddrsEqualityWOOffsetPermut.
      + apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
        symmetry;trivial.
        intros;split;subst;trivial. }
        rewrite  <- Hmapeq in Hx1.
        assert(Hfalse: a = va1).
        apply eqMappedPagesEqVaddrs with (pa entry) pdChildphy s;trivial.
        symmetry;trivial.
        subst. now contradict Htrueor.

  }
  
  assert (Hmykey: exists  l1 l2,
  getMappedPages phyDescChild s = l1 ++ [(pa entry)] ++ l2  /\
  getMappedPages phyDescChild s'= l1 ++l2  ).
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

+ subst;simpl in *.
assert(Htrueor :  a=va1\/  a <> va1)  by apply vaddrDecOrNot.
  destruct Htrueor as [Htrueor |Htrueor].
  subst.
  destruct Hva1 as [ Hva1 | Hva1];subst;trivial.
  - rewrite <- Hmap2 in *.
    rewrite <- Hmap1 in *.
    clear Hmykey2. clear IHl.
     exists [].
        exists (filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s) ).
        split;simpl;trivial.
        apply NoDup_cons_iff in Htriche1 as (Hi1 & Hi2).
        (* induction  (filter checkOffset0 l);simpl in *;trivial. *)
        
        
        induction l;simpl in *;trivial.
        case_eq(checkOffset0 a);intros Hoff;simpl in *;rewrite Hoff in *.
        * unfold getMappedPagesOption in Hmykey4.
          simpl in *.
            assert (Hmapeq: getMappedPage pdChildphy s a = getMappedPage pdChildphy s' a).
    { apply mapPageRemoveSinglePage1 with level (getIndexOfAddr vaChild fstLevel)
        (currentPartition s) phyDescChild entry;trivial.
      + symmetry;trivial.
      + assert(Htrue:checkVAddrsEqualityWOOffset nbLevel va1 a level = false). 
        { apply checkVAddrsEqualityWOOffsetFalseEqOffset;intuition.
 }
        apply checkVAddrsEqualityWOOffsetTrans with va1;trivial.
            rewrite <- Hva11.
            f_equal.
            apply getNbLevelEq;trivial.
            rewrite <- Htrue.
            apply checkVAddrsEqualityWOOffsetPermut.
      + apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
        symmetry;trivial.
        intros;split;subst;trivial. }
       rewrite Hmapeq in *.
        
        
        
        
        case_eq( getMappedPage pdChildphy s' a );[intros mapped Hmapped | intros Hmapped| intros Hmapped];
        rewrite Hmapped in *.
        -- f_equal.
        
apply IHl;trivial.
        simpl in *.
        apply not_or_and in Hmykey4.
        intuition.
        apply not_or_and in Hi1.
        intuition.
        apply NoDup_cons_iff in Hi2.
intuition.
-- apply IHl;trivial.
        simpl in *.
       
        apply not_or_and in Hi1.
        intuition.
        apply NoDup_cons_iff in Hi2.
intuition.
-- apply IHl;trivial.
        simpl in *.
        apply not_or_and in Hi1.
        intuition.
        apply NoDup_cons_iff in Hi2.
intuition.
* apply IHl;trivial.
- rewrite <- Hmap2 in *.
    rewrite <- Hmap1 in *.
    clear Hmykey2. clear IHl.
     exists [].
        exists (filterOption (getMappedPagesOption pdChildphy (filter checkOffset0 l) s) ).
        split;simpl;trivial.
        apply NoDup_cons_iff in Htriche1 as (Hi1 & Hi2).
        (* induction  (filter checkOffset0 l);simpl in *;trivial. *)
        now contradict Hva1.
- destruct Hva1 as [ Hva1 | Hva1];subst;trivial.
  now contradict Htrueor.
            assert (Hmapeq: getMappedPage pdChildphy s a = getMappedPage pdChildphy s' a).
    { apply mapPageRemoveSinglePage1 with level (getIndexOfAddr vaChild fstLevel)
        (currentPartition s) phyDescChild entry;trivial.
      + symmetry;trivial.
      + assert(Htrue:checkVAddrsEqualityWOOffset nbLevel va1 a level = false). 
        { apply checkVAddrsEqualityWOOffsetFalseEqOffset;intuition. 
        assert(Hx :In va1 (filter checkOffset0 l)) by trivial.
        apply filter_In in Hx;intuition.
 }
        apply checkVAddrsEqualityWOOffsetTrans with va1;trivial.
            rewrite <- Hva11.
            f_equal.
            apply getNbLevelEq;trivial.
            rewrite <- Htrue.
            apply checkVAddrsEqualityWOOffsetPermut.
      + apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
        symmetry;trivial.
        intros;split;subst;trivial. }
rewrite Hmapeq in *.
case_eq(getMappedPage pdChildphy s' a);[intros phya Ha| intros Ha| intros Ha];
rewrite Ha in *.
*

    assert(IHlnew :  exists l1 l2 : list page,
        filterOption
          (getMappedPagesOption pdChildphy (filter checkOffset0 l) s) =
        l1 ++ (pa entry) :: l2 /\
        filterOption
          (getMappedPagesOption pdChildphy (filter checkOffset0 l) s') =
        l1 ++ l2).
    {        apply IHl;trivial.
    simpl in *.
    apply not_or_and in Hmykey4.
    intuition.
    intuition.

     apply NoDup_cons_iff in Htriche1;intuition.
  }
clear IHl.
destruct IHlnew as (l1 & l2 & Hs & Hs').
rewrite Hs.
rewrite Hs'.
exists (phya :: l1).
exists l2.
split;
simpl;trivial.
* apply IHl;trivial.
    apply NoDup_cons_iff in Htriche1;intuition.
* apply IHl;trivial.
    apply NoDup_cons_iff in Htriche1;intuition.
    + apply IHl;trivial. }
 
 
 
destruct Hmykey as (l1 & l2 & Hl1 & Hl2).
unfold getMappedPages in *.
rewrite Hpdpart in *.
rewrite Hpd in *.
unfold getMappedPagesAux in *.
rewrite Hl1 in *.
rewrite Hl2 in *.

apply NoDupSplitInclIff.
apply NoDupSplitInclIff in Hnodup1.
intuition.
simpl in *.
assert(Hxx : NoDup (pa entry :: l2)) by trivial.

apply NoDup_cons_iff in Hxx.
intuition.
unfold disjoint in *; intros x Hx.
simpl in *.
assert(Hx1: forall x : page, In x l1 -> ~ (pa entry = x \/ In x l2))
by trivial.
apply Hx1 in Hx;trivial.
intuition.

+ 
  assert(Hmap : getMappedPages partition s = getMappedPages partition s').
  { apply getMappedPagesRemoveMMUPage with phyDescChild vaChild
    entry level;intuition.
apply isConfigTable with vaChild ;trivial.
  intros;subst;split;trivial.
  subst;trivial. }
    rewrite <- Hmap;trivial.
Qed.

Lemma noDupConfigPagesListRemoveMMUPage shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
consistency s ->
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
noDupMappedPagesList s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
noDupConfigPagesList s -> 
noDupConfigPagesList
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.

set(s':= {|  currentPartition := _ |}) in *.
intros.
assert(Hnodup : noDupConfigPagesList s) by trivial.
unfold noDupConfigPagesList in *.
intros partition Hpart.
subst.
assert(Hparts : In partition (getPartitions multiplexer s)).
apply getPartitionsRemoveMMUPage with shadow1Child ptVaChildpd pdChildphy
    phyDescChild level entry vaChild;trivial.
assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
assert(Hconfig: getConfigPages partition s =getConfigPages partition s').
{ assert (Hor : phyDescChild = partition \/ 
    phyDescChild <> partition) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
subst.
+ apply getConfigPagesRemoveMMUPage1 with entry pdChildphy
  (currentPartition s)  vaChild level ;trivial.
+ apply getConfigPagesRemoveMMUPage with phyDescChild entry;intuition.
    apply isConfigTable with vaChild;trivial.
    intros;split;subst;trivial. }
rewrite <- Hconfig;trivial.
  apply Hnodup;trivial.
Qed.

Lemma parentInPartitionListRemoveMMUPage  shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
parentInPartitionList s -> 
parentInPartitionList
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros.
assert(Hcons: parentInPartitionList s) by trivial.
unfold parentInPartitionList in *.
intros child Hchild parent Hparent.
assert(Hparts : getPartitions multiplexer s' =  getPartitions multiplexer s ).
apply getPartitionsRemoveMMUPage1  with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparts in *.
apply Hcons with child;trivial.
apply nextEntryIsPPRemoveMMUPage' with ptVaChildpd (getIndexOfAddr vaChild fstLevel);trivial.
Qed.

Lemma getPDFlagRemoveMMUPage sh1 va  shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild part:
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex =
    Some (PE entry) -> 
StateLib.getNbLevel = Some level ->
In part (getPartitions multiplexer s) -> 
StateLib.getFstShadow part (memory s) = Some sh1 -> 
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
getPDFlag sh1 va {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |} = getPDFlag sh1 va s.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hlookup Hlevel Hpart Hsh1.
intros.
unfold getPDFlag.
rewrite Hlevel.
case_eq( getIndirection sh1 va level (nbLevel - 1) s');
[intros ind Hind | intros Hind].
+ assert (Hind' :  getIndirection sh1 va level (nbLevel - 1) s = Some ind).
  { apply getIndirectionRemoveMMUPage4 with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
 pdChildphy (currentPartition s)  vaChild
phyDescChild entry sh1idx part;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
apply nextEntryIsPPgetPd;trivial.
intros;subst;split;trivial.
subst.
apply nextEntryIsPPgetFstShadow;trivial.
right;left;trivial. }
rewrite Hind'.
destruct (ind =? defaultPage);trivial. 
assert(Hread:  StateLib.readPDflag ind (StateLib.getIndexOfAddr va fstLevel) (memory s') 
=  StateLib.readPDflag ind (StateLib.getIndexOfAddr va fstLevel) (memory s)).
apply readPDflagRemoveMMUPage with entry;trivial.
rewrite Hread;trivial.
+ assert (Hind' :  getIndirection sh1 va level (nbLevel - 1) s =None).
  { apply getIndirectionRemoveMMUPage4None with
   ptVaChildpd (getIndexOfAddr vaChild fstLevel)
 pdChildphy (currentPartition s)  vaChild
phyDescChild entry sh1idx part;subst;trivial.
   apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
   apply nextEntryIsPPgetPd;trivial.
   intros;subst;split;trivial.
   apply nextEntryIsPPgetFstShadow;trivial.
   right;left;trivial. }
rewrite Hind';trivial.
Qed.

Lemma accessibleVAIsNotPartitionDescriptorRemoveMMUPage  shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
accessibleVAIsNotPartitionDescriptor s -> 
accessibleVAIsNotPartitionDescriptor
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hlookup.
intros.
assert(Hcons: accessibleVAIsNotPartitionDescriptor s) by trivial.
unfold accessibleVAIsNotPartitionDescriptor in *.
intros part va pd sh1 phypage Hpart Hpdpart Hsh1part Haccess.
assert(Hparts : getPartitions multiplexer s' =  getPartitions multiplexer s ).
apply getPartitionsRemoveMMUPage1  with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparts in *.
assert(Hpd : forall part, StateLib.getPd part (memory s) =
        StateLib.getPd part (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdRemoveMMUPage with entry;trivial. }
rewrite <- Hpd in *. 
assert(Hsh1 : forall part, StateLib.getFstShadow part (memory s) =
        StateLib.getFstShadow part (memory s')).
{ unfold s'. simpl.
  symmetry. apply getFstShadowRemoveMMUPage with entry;trivial. }
rewrite <- Hsh1 in *. 
assert (Hpdflag :  getPDFlag sh1 va s' = getPDFlag sh1 va s).
{  apply getPDFlagRemoveMMUPage with shadow1Child pdChildphy
phyDescChild level entry part;trivial.
symmetry;trivial. }
rewrite Hpdflag.
apply Hcons with part pd phypage;trivial.
assert(Hor : part = phyDescChild \/ part <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor]; subst.
+ assert(Hpdeq : pd = pdChildphy).
  { symmetry. apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
  subst.
assert(Hor1 :checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaChild va level = false).
      { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild va level);intuition. }
destruct Hor1 as [Hor1 | Hor1].
-
 assert (Hnewmapp : getAccessibleMappedPage pdChildphy s' vaChild = NonePage).
{    subst. 
assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
(StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some (pa entry)).
{ unfold  readPhyEntry. rewrite Hlookup;trivial. }
assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some defaultPage).
{ unfold StateLib.readPhyEntry. 
cbn.
assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
(ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
beqIndex = true); intros.
rewrite <- beqPairsTrue;split;trivial.
rewrite Hpairs.
simpl;trivial. }
apply getAccessibleMappedPageNotPresent with ptVaChildpd phyDescChild;
  trivial;fold s'. 
  + intros. 
  split. 
  apply isPERemoveMMUPage with entry;trivial.
  subst;trivial.
(* assert(Htableroot: getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial. *)
assert(Htblroot: getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.

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
  apply nextEntryIsPPRemoveMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  ;trivial.
  
  subst.
  rewrite <- Hind1.
  apply getIndirectionRemoveMMUPage5 with 
  pdChildphy (currentPartition s) vaChild phyDescChild entry PDidx phyDescChild;trivial.
  symmetry;trivial.
  apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
  omega.
  apply getNbLevelEq in HnbL.
  subst. apply nbLevelEq.
  + unfold entryPresentFlag. 
     cbn.
     subst.
     assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
        (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
        beqIndex = true).
     apply beqPairsTrue;split;trivial.
     rewrite Hpairs.
     simpl;trivial.
         
  + apply  nextEntryIsPPRemoveMMUPage with entry;trivial. }
    assert (Hmapsfalse : getAccessibleMappedPage pdChildphy s' vaChild = 
         getAccessibleMappedPage pdChildphy s' va).
    { apply getAccessibleMappedPageEq with level;trivial.
      symmetry;trivial. }
    rewrite Hnewmapp in Hmapsfalse.    
    rewrite Haccess in Hmapsfalse.
    now contradict Hmapsfalse.
- rewrite <- Haccess.
  apply getAccessibleMappedPageRemoveSinglePage1 with level 
  (getIndexOfAddr vaChild fstLevel) (currentPartition s) phyDescChild entry;trivial.
  symmetry;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
symmetry;trivial.
intros;split;subst;trivial.
+ rewrite <- Haccess.
  apply getAccessibleMappedPageRemoveMMUPage1 with part phyDescChild vaChild entry level;intuition.
  apply isConfigTable with vaChild ;trivial.
  intros;subst;split;trivial.
  subst;trivial.
Qed.
 Lemma mappedPageNotAccessible pdChildphy vaChild s (ptVaChildpd phyDescChild: page)  entry: 
 lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s)
            beqPage beqIndex = Some (PE entry) -> 
 isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
partitionDescriptorEntry s -> 
isPresentNotDefaultIff s ->
noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
In phyDescChild (getPartitions multiplexer s) -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s -> 
pdChildphy <> defaultPage ->
getAccessibleMappedPage pdChildphy {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := false;
                     write := false;
                     exec := false;
                     present := false;
                     user := false;
                     pa := defaultPage |}) (memory s) beqPage beqIndex |} vaChild = NonePage.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hlookup Hpe Htblroot Hpdchild. intros.
subst. 
assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
(StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some (pa entry)).
{ unfold  readPhyEntry. rewrite Hlookup;trivial. }
assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some defaultPage).
{ unfold StateLib.readPhyEntry. 
cbn.
assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
(ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
beqIndex = true); intros.
rewrite <- beqPairsTrue;split;trivial.
rewrite Hpairs.
simpl;trivial. }
apply getAccessibleMappedPageNotPresent with ptVaChildpd phyDescChild;
  trivial. 
  + intros. 
  split. 
  apply isPERemoveMMUPage with entry;trivial.
  subst;trivial.
(* assert(Htableroot: getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial. *)

   unfold getTableAddrRoot in Htblroot.
  assert(Hpdchild2 : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
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
  apply nextEntryIsPPRemoveMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  ;trivial.
  apply nextEntryIsPPgetPd;trivial.
  
  subst.
  
  rewrite <- Hind1.
  apply getIndirectionRemoveMMUPage5 with 
  pdChildphy (currentPartition s) vaChild phyDescChild entry PDidx phyDescChild;trivial.
  symmetry;trivial.
  apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
  omega.
  apply getNbLevelEq in HnbL.
  subst. apply nbLevelEq.
  + unfold entryPresentFlag. 
     cbn.
     subst.
     assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
        (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
        beqIndex = true).
     apply beqPairsTrue;split;trivial.
     rewrite Hpairs. 
     simpl;trivial.
         
  + apply  nextEntryIsPPRemoveMMUPage with entry;trivial.  
  Qed.

 Lemma removeMappedPagePutSomeDefault pdChildphy vaChild s (ptVaChildpd phyDescChild: page)  entry: 
 lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s)
            beqPage beqIndex = Some (PE entry) -> 
 isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
partitionDescriptorEntry s -> 
isPresentNotDefaultIff s ->
noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In (currentPartition s) (getPartitions multiplexer s) -> 
In phyDescChild (getPartitions multiplexer s) -> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
(defaultPage =? ptVaChildpd) = false -> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s -> 
pdChildphy <> defaultPage ->
getMappedPage pdChildphy {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := false;
                     write := false;
                     exec := false;
                     present := false;
                     user := false;
                     pa := defaultPage |}) (memory s) beqPage beqIndex |} vaChild = SomeDefault.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hlookup Hpe Htblroot Hpdchild. intros.
subst. 
assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
(StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some (pa entry)).
{ unfold  readPhyEntry. rewrite Hlookup;trivial. }
assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some defaultPage).
{ unfold StateLib.readPhyEntry. 
cbn.
assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
(ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
beqIndex = true); intros.
rewrite <- beqPairsTrue;split;trivial.
rewrite Hpairs.
simpl;trivial. }
apply getMappedPageNotPresent with ptVaChildpd phyDescChild;
  trivial. 
  + intros. 
  split. 
  apply isPERemoveMMUPage with entry;trivial.
  subst;trivial.
(* assert(Htableroot: getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial. *)

   unfold getTableAddrRoot in Htblroot.
  assert(Hpdchild2 : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
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
  apply nextEntryIsPPRemoveMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  ;trivial.
  apply nextEntryIsPPgetPd;trivial.
  
  subst.
  
  rewrite <- Hind1.
  apply getIndirectionRemoveMMUPage5 with 
  pdChildphy (currentPartition s) vaChild phyDescChild entry PDidx phyDescChild;trivial.
  symmetry;trivial.
  apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
  omega.
  apply getNbLevelEq in HnbL.
  subst. apply nbLevelEq.
  + unfold entryPresentFlag. 
     cbn.
     subst.
     assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
        (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
        beqIndex = true).
     apply beqPairsTrue;split;trivial.
     rewrite Hpairs. 
     simpl;trivial.
         
  + apply  nextEntryIsPPRemoveMMUPage with entry;trivial.  
  Qed.
Lemma  getVirtualAddressSh2RemoveMMUPage   shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
 forall part sh2 va, In part (getPartitions multiplexer s) ->   
getSndShadow part (memory s) = Some sh2 ->
getVirtualAddressSh2 sh2 s va = getVirtualAddressSh2 sh2 {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := false;
                     write := false;
                     exec := false;
                     present := false;
                     user := false;
                     pa := defaultPage |}) (memory s) beqPage beqIndex |} va.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros. 
unfold getVirtualAddressSh2.
unfold consistency in *;intuition.
assert(Hlevel:  StateLib.getNbLevel = Some level) by(symmetry; trivial).
rewrite Hlevel.
case_eq( getIndirection sh2 va level (nbLevel - 1) s');
[intros ind Hind | intros Hind].
+ assert (Hind' :  getIndirection sh2 va level (nbLevel - 1) s = Some ind).
  { apply getIndirectionRemoveMMUPage4 with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
 pdChildphy (currentPartition s)  vaChild
phyDescChild entry sh2idx part;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
apply nextEntryIsPPgetPd;trivial.
intros;subst;split;trivial.
subst.
apply nextEntryIsPPgetSndShadow;trivial.
right;right;trivial. }
rewrite Hind'.
destruct (defaultPage =? ind);trivial. 
assert(Hread:  StateLib.readVirtual ind (StateLib.getIndexOfAddr va fstLevel) (memory s') 
=  StateLib.readVirtual ind (StateLib.getIndexOfAddr va fstLevel) (memory s)).
apply readVirtualRemoveMMUPage with entry;trivial.
rewrite Hread;trivial.
+ assert (Hind' :  getIndirection sh2 va level (nbLevel - 1) s =None).
  { apply getIndirectionRemoveMMUPage4None with
   ptVaChildpd (getIndexOfAddr vaChild fstLevel)
 pdChildphy (currentPartition s)  vaChild
phyDescChild entry sh2idx part;subst;trivial.
   apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
   apply nextEntryIsPPgetPd;trivial.
   intros;subst;split;trivial.
   apply nextEntryIsPPgetSndShadow;trivial.
   right;right;trivial. }
rewrite Hind';trivial.
   Qed.
     
  
Lemma accessibleChildPageIsAccessibleIntoParentRemoveMMUPage  shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild vainve ptVaChildFromSh1:
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
isParent s -> 
noCycleInPartitionTree s -> 
configTablesAreDifferent s -> 
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
isVE ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildFromSh1 sh1idx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildFromSh1) = false-> 
beqVAddr defaultVAddr vainve = true -> 
isEntryVA ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) vainve s -> 
consistency s -> 
In phyDescChild (getPartitions multiplexer s) -> 
 accessibleChildPageIsAccessibleIntoParent s -> 
 accessibleChildPageIsAccessibleIntoParent
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hlookup.
intros.
assert(Hcons: accessibleChildPageIsAccessibleIntoParent s) by trivial.
unfold accessibleChildPageIsAccessibleIntoParent in *.
intros part va pd  phypage Hpart Hpdpart Haccess.
assert(Hparts : getPartitions multiplexer s' =  getPartitions multiplexer s ).
apply getPartitionsRemoveMMUPage1  with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparts in *.
assert(Hpd : forall part, StateLib.getPd part (memory s) =
        StateLib.getPd part (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdRemoveMMUPage with entry;trivial. }
rewrite <- Hpd in *.
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
 assert(Hconfdiff : configTablesAreDifferent s)by trivial.
 assert(Hi1 : disjoint (getConfigPages phyDescChild s)
  (getConfigPages (currentPartition s) s)).
{  apply Hconfdiff;trivial. intuition. } 
assert(Hparentin :parentInPartitionList s).
{ unfold consistency in *.  intuition. }  
assert(Hor : part = phyDescChild \/ part <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor]; subst.
+ assert(Hpdeq : pd = pdChildphy).
  { symmetry. apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
  subst.
assert(Hor1 :checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaChild va level = false).
      { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild va level);intuition. }
destruct Hor1 as [Hor1 | Hor1].
-
 assert (Hnewmapp : getAccessibleMappedPage pdChildphy s' vaChild = NonePage) by
(apply mappedPageNotAccessible with phyDescChild entry ;trivial).
    assert (Hmapsfalse : getAccessibleMappedPage pdChildphy s' vaChild = 
         getAccessibleMappedPage pdChildphy s' va).
    { apply getAccessibleMappedPageEq with level;trivial.
      symmetry;trivial. }
    rewrite Hnewmapp in Hmapsfalse.    
    rewrite Haccess in Hmapsfalse.
    now contradict Hmapsfalse.
- assert(Hgoal: isAccessibleMappedPageInParent phyDescChild va phypage s = true).
  apply Hcons with pdChildphy ;trivial.
  rewrite <- Haccess.
  apply getAccessibleMappedPageRemoveSinglePage1 with level 
  (getIndexOfAddr vaChild fstLevel) (currentPartition s) phyDescChild entry;trivial.
  symmetry;trivial.
  apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
      symmetry;trivial.
  intros;split;subst;trivial.
  unfold isAccessibleMappedPageInParent.
  unfold isAccessibleMappedPageInParent in Hgoal.
 
  assert(Hi2 : getSndShadow phyDescChild (memory s') =
    getSndShadow phyDescChild (memory s)).
    { apply getSndShadowRemoveMMUPage with entry;trivial. }
  rewrite Hi2 in *.
  case_eq(getSndShadow phyDescChild (memory s));
  [intros sh2 Hsh2 | intros Hsh2];rewrite Hsh2 in *;try now contradict Hgoal.
  assert(Hgetvireq: getVirtualAddressSh2 sh2 s va = getVirtualAddressSh2 sh2 s' va).
  { apply getVirtualAddressSh2RemoveMMUPage with shadow1Child pdChildphy
      phyDescChild level entry phyDescChild;trivial. }
  rewrite <- Hgetvireq.
case_eq(getVirtualAddressSh2 sh2 s va);[intros vaInParent HvaInParent |
intros HvaInParent];rewrite HvaInParent in *;try now contradict Hgoal.
assert(Hparent' : getParent phyDescChild (memory s')  = getParent phyDescChild (memory s)).
{ apply getParentRemoveMMUPage with entry;trivial. }
rewrite Hparent' in *;clear Hparent'.
rewrite Hparent in *.
assert(Hpd' : StateLib.getPd (currentPartition s) (memory s) =
        StateLib.getPd (currentPartition s) (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdRemoveMMUPage with entry;trivial. }
rewrite <- Hpd' in *. clear Hpd'. 
case_eq(getPd (currentPartition s) (memory s));[intros currentPD Hcurrentpd|
intros Hcurrentpd];rewrite Hcurrentpd in *;try now contradict Hgoal.

assert(Haccesseq : getAccessibleMappedPage currentPD s vaInParent =
getAccessibleMappedPage currentPD s' vaInParent).
{ apply getAccessibleMappedPageRemoveMMUPage1 with 
(currentPartition s) phyDescChild
vaChild entry level;trivial.
 apply isConfigTable with vaChild;trivial.
intros;subst;split;trivial.
intros;subst;split;trivial.
intuition. }

rewrite <- Haccesseq;trivial.
+ assert(Hgoal: isAccessibleMappedPageInParent part va phypage s = true).
  apply Hcons with pd ;trivial.
  rewrite <- Haccess.
  apply getAccessibleMappedPageRemoveMMUPage1 with part phyDescChild 
  vaChild entry level;intuition.
   apply isConfigTable with vaChild;trivial.
   intros;subst;split;trivial.
  subst;trivial.
  unfold isAccessibleMappedPageInParent.
  unfold isAccessibleMappedPageInParent in Hgoal.
 
  assert(Hi2 : getSndShadow part (memory s') =
    getSndShadow part (memory s)).
    { apply getSndShadowRemoveMMUPage with entry;trivial. }
  rewrite Hi2 in *.
  case_eq(getSndShadow part (memory s));
  [intros sh2 Hsh2 | intros Hsh2];rewrite Hsh2 in *;try now contradict Hgoal.
  assert(Hgetvireq: getVirtualAddressSh2 sh2 s va = getVirtualAddressSh2 sh2 s' va).
  { apply getVirtualAddressSh2RemoveMMUPage with shadow1Child pdChildphy
      phyDescChild level entry part;trivial. }
  rewrite <- Hgetvireq.
case_eq(getVirtualAddressSh2 sh2 s va);[intros vaInParent HvaInParent |
intros HvaInParent];rewrite HvaInParent in *;try now contradict Hgoal.
assert(Hparent' : getParent part (memory s')  = getParent part (memory s)).
{ apply getParentRemoveMMUPage with entry;trivial. }
rewrite Hparent' in *;clear Hparent'.
case_eq(getParent part (memory s));
  [intros parent Hparent1 | intros Hparent1];rewrite Hparent1 in *;try now contradict Hgoal.
assert(Hpd' : StateLib.getPd parent (memory s) =
        StateLib.getPd parent (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdRemoveMMUPage with entry;trivial. }
rewrite <- Hpd' in *. clear Hpd'. 
case_eq(getPd parent (memory s));[intros pdParent HpdParent|
intros HpdParent];rewrite HpdParent in *;try now contradict Hgoal.
assert(Hor2:parent = phyDescChild \/ parent <> phyDescChild) by apply pageDecOrNot.
destruct Hor2 as [Ho2 | Hor2].
* subst.
  case_eq(getAccessibleMappedPage pdParent s vaInParent); [intros phyp Hphypage|
  intros Hphypage| intros Hphypage];rewrite Hphypage in *;try now contradict Hgoal.
  apply beq_nat_true in Hgoal.
  assert(Hpdeq : pdParent = pdChildphy).
  { symmetry. apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
  subst.
  assert(Hor1 :checkVAddrsEqualityWOOffset nbLevel vaChild vaInParent level = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaChild vaInParent level = false).
      { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild vaInParent level);intuition. }
destruct Hor1 as [Hor1 | Hor1].
  --    assert(Hnotshared : ~ isDerived phyDescChild vaChild s ).
      { apply vaNotDerived with ptVaChildFromSh1;trivial.
        unfold consistency in *;intuition.
        exists defaultVAddr;split;trivial.
        assert(defaultVAddr =vainve).
        apply beqVAddrTrueEq;trivial.
        subst. trivial.
        apply beqVAddrTrue.
        intros;split;subst;trivial. }
      assert(Hnotmapped:  ~ In (pa entry) (getMappedPages part s)).
      { apply phyNotDerived with phyDescChild pdChildphy  vaChild ptVaChildpd;trivial.
        intros;split;subst;trivial.
        unfold isEntryPage.
        rewrite Hlookup;trivial.
        assert(Hischild: isChild s);unfold consistency in *;intuition.     }
     assert(Hmappedaccess: getAccessibleMappedPage pdChildphy s vaChild = SomePage (pa entry)).
     { apply isAccessibleMappedPage2 with phyDescChild ptVaChildpd ;subst;trivial.
  unfold isEntryPage.
  rewrite Hlookup;trivial.
    intros;split;subst;trivial. }
    assert(Haccesseq : getAccessibleMappedPage pdChildphy s vaChild =
    getAccessibleMappedPage pdChildphy s vaInParent).
    {  apply getAccessibleMappedPageEq with level;trivial.
      symmetry;trivial. }
    rewrite Hmappedaccess in Haccesseq.
    rewrite Hphypage in Haccesseq.
    inversion Haccesseq;subst.
    assert(Hmapeq:getAccessibleMappedPage pd s va=getAccessibleMappedPage pd s' va).
    { apply getAccessibleMappedPageRemoveMMUPage1 with  part phyDescChild 
  vaChild entry level;intuition.    
     apply isConfigTable with vaChild;trivial.
   intros;subst;split;trivial.
  subst;trivial. }
  rewrite <- Hmapeq in Haccess.
  move Haccess at bottom.
assert(Hinfalse: In phypage (getMappedPages part s)).
{ assert(Htrue: getMappedPage pd s va = SomePage phypage) by 
(apply accessiblePAgeIsMapped;trivial). 
  unfold getMappedPages.
  rewrite Hpdpart;trivial.
  unfold getMappedPagesAux.
  apply filterOptionInIff.
  unfold getMappedPagesOption.
  apply in_map_iff.
          assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
                     StateLib.checkVAddrsEqualityWOOffset nbLevel va va1 ( CLevel (nbLevel -1) ) = true )
                     by apply AllVAddrWithOffset0.
          destruct Heqvars as (va1 & Hva1 & Hva11).
  exists va1;split;trivial.
  rewrite <- Htrue.
  symmetry.
  apply getMappedPageEq with level;symmetry;trivial.
  rewrite <- Hva11. 
f_equal.
          symmetry.  apply getNbLevelEq;trivial. }
  revert Hgoal Hinfalse Hnotmapped.
  clear.
  intros.
  contradict Hnotmapped.
  destruct phypage;simpl in *;
   destruct (pa entry) ;simpl in *;
  subst.
  assert({| p := p0; Hp := Hp0 |} ={| p := p0; Hp := Hp |}).
  f_equal.
  apply proof_irrelevance.
  subst.
  simpl in *.
  inversion H.
  rewrite H in *.
  trivial.
--

assert(Haccesseq : getAccessibleMappedPage pdChildphy s vaInParent =
getAccessibleMappedPage pdChildphy s' vaInParent).
{ apply getAccessibleMappedPageRemoveSinglePage1 with level 
  (getIndexOfAddr vaChild fstLevel) (currentPartition s) phyDescChild entry;trivial.
  symmetry;trivial.
  apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
      symmetry;trivial.
  intros;split;subst;trivial. }
rewrite <- Haccesseq;trivial.
rewrite Hphypage.
rewrite Hgoal.
symmetry.
apply beq_nat_refl.
* assert(Haccesseq : getAccessibleMappedPage pdParent s vaInParent =
getAccessibleMappedPage pdParent s' vaInParent).
{ apply getAccessibleMappedPageRemoveMMUPage1 with parent 
phyDescChild vaChild entry level;trivial.
apply Hconfdiff;trivial.
unfold parentInPartitionList in Hparentin.
apply Hparentin with part;trivial.
apply nextEntryIsPPgetParent;trivial.
intuition.
  apply isConfigTable with vaChild ;trivial.
  intros;subst;split;trivial.
  subst;trivial.
  apply Hconfdiff;trivial.
  apply Hparentin with part;trivial.
  apply nextEntryIsPPgetParent;trivial.
intuition.
 intros;split;subst;trivial.
 intuition. 
 apply Hparentin with part;trivial.
  apply nextEntryIsPPgetParent;trivial. }
rewrite <- Haccesseq;trivial.
Qed.

Lemma getAncestorsRemoveMMUPage  ( partition : page) entry s table idx :
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) ->
getAncestors partition s = getAncestors partition {|
      currentPartition := currentPartition s;
      memory :=
(add table idx
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) |}.
Proof.
intros.
revert partition.
unfold getAncestors.
induction (nbPage + 1);simpl in *;intros;trivial.
assert(Hparent : getParent partition (memory s) =
getParent partition (add table idx
           (PE
              {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex) ).
symmetry. apply getParentRemoveMMUPage with entry;trivial.
rewrite <- Hparent. clear Hparent.
destruct(getParent partition (memory s));trivial.
f_equal.
apply IHn.
Qed.

Lemma noCycleInPartitionTreeRemoveMMUPage  shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
noCycleInPartitionTree s -> 
noCycleInPartitionTree
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros.
assert(Hcons: noCycleInPartitionTree s) by trivial.
unfold noCycleInPartitionTree in *.
intros  ancestor partition Hancestor Hparent.
assert(Hparts : getPartitions multiplexer s' =  getPartitions multiplexer s ).
apply getPartitionsRemoveMMUPage1  with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparts in *.
assert(Hancestors : getAncestors partition s' =  getAncestors partition s ).
{ symmetry. apply getAncestorsRemoveMMUPage with entry;trivial. }
rewrite Hancestors in *.
apply Hcons;trivial.
Qed.

Lemma  configTablesAreDifferentRemoveMMUPage  shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
consistency s -> 
configTablesAreDifferent s -> 
configTablesAreDifferent
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
intros.
set(s':= {|  currentPartition := _ |}) in *.
intros.
assert(Hcons: configTablesAreDifferent s) by trivial.
unfold configTablesAreDifferent in *.
intros.
assert(Hconfig: forall partition, In partition (getPartitions multiplexer s) ->
  getConfigPages partition s =getConfigPages partition s').
{ intros. assert (Hor : phyDescChild = partition \/ 
    phyDescChild <> partition) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
subst.
+ apply getConfigPagesRemoveMMUPage1 with entry pdChildphy
  (currentPartition s)  vaChild level ;trivial.
+ apply getConfigPagesRemoveMMUPage with phyDescChild entry;intuition.
    apply isConfigTable with vaChild;trivial.
    intros;split;subst;trivial. }
assert(Hparts : getPartitions multiplexer s' =  getPartitions multiplexer s ).
apply getPartitionsRemoveMMUPage1  with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparts in *.
rewrite <- Hconfig;trivial.
rewrite <- Hconfig;trivial.
apply Hcons;trivial.
Qed.

Lemma isChildRemoveMMUPage  shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
parentInPartitionList s -> 
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 

isChild s -> 
isChild
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hconsparent.
intros.
assert(Hcons: isChild s) by trivial.
unfold isChild in *.
intros  partition parent Hpartition Hparent.
assert(Hparts : getPartitions multiplexer s' =  getPartitions multiplexer s ).
apply getPartitionsRemoveMMUPage1  with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparts in *.
assert(Hparent' : getParent partition (memory s')  = getParent partition (memory s)).
{ apply getParentRemoveMMUPage with entry;trivial. }
rewrite Hparent' in *;clear Hparent'.
assert(Hchildeq : getChildren parent s' =
                 getChildren parent s).
{ apply removeMappedPageGetChildren  with shadow1Child pdChildphy
   phyDescChild level entry ;subst;trivial.
   unfold parentInPartitionList in *.
   apply Hconsparent with partition;trivial.
   apply nextEntryIsPPgetParent;trivial.
 }
rewrite Hchildeq;trivial.
apply Hcons;trivial.
Qed.

Lemma  isPresentNotDefaultIffRemoveMMUPage  s   ptVaChildpd   vaChild
entry
:
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
isPresentNotDefaultIff s -> 
isPresentNotDefaultIff {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
unfold isPresentNotDefaultIff.
intros.
simpl.
intros.
 assert(Hor : (  (table <> ptVaChildpd \/
idx <>
(getIndexOfAddr vaChild fstLevel)) \/  (~ (table <> ptVaChildpd \/
idx <>
(getIndexOfAddr vaChild fstLevel))))).
{ apply classic. }
destruct Hor as [Hor | Hor];trivial.
+ assert(Hpres :StateLib.readPresent table idx
  (add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex)=
         StateLib.readPresent table idx (memory s) ).
   symmetry.
  apply readPresentRemoveMMUPage with entry;trivial.
  rewrite Hpres.
  assert(Hacces :StateLib.readPhyEntry table idx
  (add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex)=
         StateLib.readPhyEntry table idx (memory s) ).
   symmetry.
  apply readPhyEntryRemoveMMUPage with entry;trivial.
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
assert(Htrue: beqPairs (ptVaChildpd, (getIndexOfAddr vaChild fstLevel)) (ptVaChildpd, (getIndexOfAddr vaChild fstLevel)) beqPage
           beqIndex = true).
  { apply beqPairsTrue; split;trivial. }
split.
* intros. unfold StateLib.readPresent in *.
  unfold StateLib.readPhyEntry .
  simpl.
    simpl in *.
  rewrite Htrue in *.
  simpl in *.
  trivial.
* intros. 
  intros. unfold StateLib.readPresent.
  unfold StateLib.readPhyEntry in H.
    simpl in *.
  rewrite Htrue in *.
  simpl in *.
  inversion H;subst.
  trivial.
Qed.
Lemma  getVirtualAddressSh1RemoveMMUPage   shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
 forall part sh1 va, In part (getPartitions multiplexer s) ->   
getFstShadow part (memory s) = Some sh1 ->
getVirtualAddressSh1 sh1 s va = getVirtualAddressSh1 sh1 {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := false;
                     write := false;
                     exec := false;
                     present := false;
                     user := false;
                     pa := defaultPage |}) (memory s) beqPage beqIndex |} va.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros. 
unfold getVirtualAddressSh1.
unfold consistency in *;intuition.
assert(Hlevel:  StateLib.getNbLevel = Some level) by(symmetry; trivial).
rewrite Hlevel.
case_eq( getIndirection sh1 va level (nbLevel - 1) s');
[intros ind Hind | intros Hind].
+ assert (Hind' :  getIndirection sh1 va level (nbLevel - 1) s = Some ind).
  { apply getIndirectionRemoveMMUPage4 with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel)
 pdChildphy (currentPartition s)  vaChild
phyDescChild entry sh1idx part;trivial.
apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
apply nextEntryIsPPgetPd;trivial.
intros;subst;split;trivial.
subst.
apply nextEntryIsPPgetFstShadow;trivial.
right;left;trivial. }
rewrite Hind'.
destruct (defaultPage =? ind);trivial. 
assert(Hread:  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va fstLevel) (memory s') 
=  StateLib.readVirEntry ind (StateLib.getIndexOfAddr va fstLevel) (memory s)).
apply readVirEntryRemoveMMUPage with entry;trivial.
rewrite Hread;trivial.
+ assert (Hind' :  getIndirection sh1 va level (nbLevel - 1) s =None).
  { apply getIndirectionRemoveMMUPage4None with
   ptVaChildpd (getIndexOfAddr vaChild fstLevel)
 pdChildphy (currentPartition s)  vaChild
phyDescChild entry sh1idx part;subst;trivial.
   apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
   apply nextEntryIsPPgetPd;trivial.
   intros;subst;split;trivial.
   apply nextEntryIsPPgetFstShadow;trivial.
   right;left;trivial. }
rewrite Hind';trivial.
   Qed.
Lemma isDerivedRemoveMMUPage parent va ptVaChildpd vaChild entry s (shadow1Child pdChildphy
phyDescChild :page) (level : level) :
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) ->
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 
 In parent (getPartitions multiplexer s) ->   
 
~ isDerived parent va {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                     read := false;
                     write := false;
                     exec := false;
                     present := false;
                     user := false;
                     pa := defaultPage |}) (memory s) beqPage beqIndex |} -> 
~ isDerived parent va s.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hlookup.
intros.
 unfold isDerived in *.  
  assert(Hsh1 :  StateLib.getFstShadow parent (memory s') =
  StateLib.getFstShadow parent (memory s)).
  { intros. apply getFstShadowRemoveMMUPage with entry;trivial. }
  rewrite Hsh1 in *. clear Hsh1.
  case_eq(getFstShadow parent (memory s));[intros sh1 Hsh1  | intros Hsh1];
  rewrite Hsh1 in *;[|intuition].
  assert (Hgetva : getVirtualAddressSh1 sh1 s va = getVirtualAddressSh1 sh1 s' va).
  { apply getVirtualAddressSh1RemoveMMUPage with  shadow1Child pdChildphy
phyDescChild level entry parent;trivial. }
  rewrite Hgetva;trivial.
  Qed.
Lemma physicalPageNotDerivedRemoveMMUPage shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild vainve ptVaChildFromSh1:
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
isParent s -> 
noCycleInPartitionTree s -> 
configTablesAreDifferent s -> 
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
isVE ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildFromSh1 sh1idx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildFromSh1) = false-> 
beqVAddr defaultVAddr vainve = true -> 
isEntryVA ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) vainve s -> 
consistency s -> 
In phyDescChild (getPartitions multiplexer s) -> 
physicalPageNotDerived s ->
physicalPageNotDerived
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
 Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hlookup.
intros.
assert(Hderivg :forall partition va,In partition (getPartitions multiplexer s) ->   ~isDerived partition va s' -> ~ isDerived partition va s).
{ intros. apply isDerivedRemoveMMUPage with ptVaChildpd vaChild
entry shadow1Child pdChildphy phyDescChild level;trivial. }
assert(Hcons: physicalPageNotDerived s) by trivial.
unfold  physicalPageNotDerived in *.
intros parent va pdParent pageParent 
Hparent Hpdparent Hnotderivp Hmapparent.
intros child pdchild vaInChild pageChild
Hchild Hpdchild Hmapchild.
assert(Hparts : getPartitions multiplexer s' =  getPartitions multiplexer s ).
apply getPartitionsRemoveMMUPage1  with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparts in *. clear Hparts.
assert(Hpd' : forall part, StateLib.getPd part (memory s) =
        StateLib.getPd part (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdRemoveMMUPage with entry;trivial. }
rewrite <- Hpd' in *. clear Hpd'. 
assert(Hchildeq : getChildren parent s' = getChildren parent s).
{ apply removeMappedPageGetChildren  with shadow1Child pdChildphy
   phyDescChild level entry ;subst;trivial. }
rewrite Hchildeq in *;trivial.
assert(Hderiv :~ isDerived parent va s).
{ apply isDerivedRemoveMMUPage with ptVaChildpd vaChild
entry shadow1Child pdChildphy phyDescChild level;trivial. }

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
assert (Hnewmapp : getMappedPage pdChildphy s' vaChild = SomeDefault).
{    subst. 
assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
(StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some (pa entry)).
{ unfold  readPhyEntry. rewrite Hlookup;trivial. }
assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some defaultPage).
{ unfold StateLib.readPhyEntry. 
cbn.
assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
(ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
beqIndex = true); intros.
rewrite <- beqPairsTrue;split;trivial.
rewrite Hpairs.
simpl;trivial. }

 apply getMappedPageNotPresent with ptVaChildpd phyDescChild;
  trivial;fold s'. 
  + intros. 
  split. 
  apply isPERemoveMMUPage with entry;trivial.
  subst;trivial.
assert(Htblroot: getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s) by trivial.
   unfold getTableAddrRoot in Htblroot.
  destruct Htblroot as (Hidxs & Htblroot).
  split;trivial.
  intros.
  assert(Hpdphychild : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
  apply Htblroot in Hpdphychild;clear Htblroot.
  move Hpdphychild at bottom.
  destruct Hpdphychild as (nbL & HnbL & stop & Hstop & Hind1).
  exists nbL ; split ; trivial.
  exists stop;split;trivial.
  assert(tableroot = pdChildphy). 
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  apply nextEntryIsPPRemoveMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  ;trivial.
  apply nextEntryIsPPgetPd;trivial.
  subst.
  rewrite <- Hind1.
  apply getIndirectionRemoveMMUPage5 with 
pdChildphy (currentPartition s) vaChild phyDescChild entry PDidx phyDescChild;trivial.
symmetry;trivial.
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
omega.
apply getNbLevelEq in HnbL.
subst. apply nbLevelEq.

+ unfold entryPresentFlag. 
   cbn.
   subst.
   assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
      beqIndex = true).
   apply beqPairsTrue;split;trivial.
   rewrite Hpairs.
   simpl;trivial.
       
+ apply  nextEntryIsPPRemoveMMUPage with entry;trivial. }
assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
{ apply isConfigTable  with vaChild;trivial.
intros;split;subst;trivial. }
assert(Hconfdiff: configTablesAreDifferent s);trivial.
assert(Hisparent: isParent s) ;trivial.
assert(Hnocycle : noCycleInPartitionTree s) by trivial.
assert(Hparentchild : StateLib.getParent child (memory s) = Some parent).
{ apply Hisparent;trivial. }
assert(Htrue : parent <> child).
{ apply Hnocycle.
  apply childrenPartitionInPartitionList with parent;trivial.
  unfold getAncestors.
  induction (nbPage );simpl;rewrite Hparentchild;simpl;left;trivial. } 
assert( HparentphyDesc :getParent phyDescChild (memory s) = Some (currentPartition s)).
{ unfold isParent.
  apply Hisparent;trivial. }
assert(Hnoteqparentchildphy: currentPartition s<> phyDescChild).
 { apply Hnocycle;trivial.
   unfold getAncestors.
  destruct nbPage;simpl;
  rewrite HparentphyDesc;simpl;left;trivial. }

(*   assert(Hnotshared : ~ isDerived phyDescChild vaChild s ).
      { apply vaNotDerived with ptVaChildFromSh1;trivial.
        unfold consistency in *;intuition.
        exists defaultVAddr;split;trivial.
        assert(defaultVAddr =vainve).
        apply beqVAddrTrueEq;trivial.
        subst. trivial.
        apply beqVAddrTrue.
        intros;split;subst;trivial. } *)
destruct Hor3 as [(Hi1 & Hi2) | Hor3].
+ apply Hcons with parent va pdParent child pdchild vaInChild;trivial.
  rewrite <- Hmapparent.
  apply getMappedPageRemoveMMUPageEq with parent phyDescChild vaChild
  entry level;trivial.
  intuition.
  intros;split;subst;trivial.
  rewrite <- Hmapchild.
  apply getMappedPageRemoveMMUPageEq with child phyDescChild vaChild
  entry level;trivial.
  apply Hconfdiff;trivial.
  apply childrenPartitionInPartitionList with parent;trivial.
  intros;split;subst;trivial.
  apply childrenPartitionInPartitionList with parent;trivial.
+ destruct Hor3 as [Hor | Hor].
  - subst child.
    assert(Hparenteq : parent = currentPartition s).
    { apply getParentNextEntryIsPPEq with phyDescChild s;trivial.
      apply nextEntryIsPPgetParent;trivial.
    }
    subst parent.
    assert(pdChildphy = pdchild).
    apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
    subst pdchild.
    assert(Hpameq : getMappedPage pdParent s va = getMappedPage pdParent s' va ).
    { apply getMappedPageRemoveMMUPageEq with (currentPartition s) phyDescChild vaChild
        entry level;trivial.
      intuition.
      intros;split;subst;trivial.
      intuition. }
    rewrite <- Hpameq in *.
    clear Hchildeq.
       assert(Hor : checkVAddrsEqualityWOOffset nbLevel vaChild vaInChild level = true \/
    checkVAddrsEqualityWOOffset nbLevel vaChild vaInChild level = false ).
    { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild vaInChild level);intuition. }
    destruct Hor as [Hor1 | Hor1].
    * assert (Heqfalse: getMappedPage pdChildphy s' vaChild =
    getMappedPage pdChildphy s' vaInChild). 
      { apply getMappedPageEq with level;trivial.
        symmetry;trivial. }
      rewrite Hmapchild in Heqfalse.
      rewrite Hnewmapp in Heqfalse.
      now contradict Heqfalse.
   * 
    apply Hcons with (currentPartition s) va pdParent phyDescChild 
    pdChildphy vaInChild;trivial.
    rewrite <- Hmapchild.
    apply mapPageRemoveSinglePage1 with level (getIndexOfAddr vaChild fstLevel)
        (currentPartition s) phyDescChild entry;trivial.
    symmetry;trivial.
    apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
        symmetry;trivial.
        intros;split;subst;trivial.
- subst parent.
  assert(pdChildphy = pdParent).
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial.
  subst pdParent.
  assert(Hmykey : getMappedPage pdchild s vaInChild =
      getMappedPage pdchild s' vaInChild).
    { apply getMappedPageRemoveMMUPageEq with child phyDescChild
         vaChild entry level;trivial.
      apply Hconfdiff;trivial.
      apply childrenPartitionInPartitionList with phyDescChild;trivial.
      intros;split;subst;trivial.
      apply childrenPartitionInPartitionList with phyDescChild;trivial. }
  rewrite <- Hmykey in *. clear Hmykey.
  assert(Hor : checkVAddrsEqualityWOOffset nbLevel vaChild va level = true \/
    checkVAddrsEqualityWOOffset nbLevel vaChild va level = false ).
    { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild va level);intuition. }
  destruct Hor as [Hor1 | Hor1].
  * assert (Heqfalse: getMappedPage pdChildphy s' vaChild =
    getMappedPage pdChildphy s' va). 
      { apply getMappedPageEq with level;trivial.
        symmetry;trivial. }
      rewrite Hmapparent in Heqfalse.
      rewrite Hnewmapp in Heqfalse.
      now contradict Heqfalse.
  * apply Hcons  with phyDescChild va pdChildphy child pdchild vaInChild;trivial.
    rewrite <- Hmapparent.
    apply mapPageRemoveSinglePage1 with level (getIndexOfAddr vaChild fstLevel)
        (currentPartition s) phyDescChild entry;trivial.
    symmetry;trivial.
    apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
        symmetry;trivial.
        intros;split;subst;trivial.
Qed.

Lemma multiplexerWithoutParentRemoveMMUPage s vaChild  ptVaChildpd
entry
:
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
multiplexerWithoutParent s ->
multiplexerWithoutParent  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
unfold multiplexerWithoutParent.
intros.
simpl.
rewrite <- H0.
apply getParentRemoveMMUPage with entry;trivial.
Qed.
 
 Lemma isParentRemoveMMUPage  shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
parentInPartitionList s -> 
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) -> 

isParent s -> 
isParent
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hconsparent.
intros.
assert(Hcons: isParent s) by trivial.
unfold isChild in *.
intros  partition parent Hpartition Hparent.
assert(Hparts : getPartitions multiplexer s' =  getPartitions multiplexer s ).
apply getPartitionsRemoveMMUPage1  with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparts in *.
assert(Hparent' : getParent partition (memory s')  = getParent partition (memory s)).
{ apply getParentRemoveMMUPage with entry;trivial. }
rewrite Hparent' in *;clear Hparent'.
assert(Hchildeq : getChildren parent s' =
                 getChildren parent s).
{ apply removeMappedPageGetChildren  with shadow1Child pdChildphy
   phyDescChild level entry ;subst;trivial.
 }
rewrite Hchildeq in *;trivial.
apply Hcons;trivial.
Qed.

Lemma  noDupPartitionTreeRemoveMMUPage shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
noDupPartitionTree s -> 
noDupPartitionTree
{|
      currentPartition := currentPartition s;
      
      memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
                  (PE
                    {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
unfold noDupPartitionTree;simpl.
intros.
set(s' :=  {|
         currentPartition := _ |}) in *.
assert(Hparteq :getPartitions multiplexer s' = getPartitions multiplexer s).
apply getPartitionsRemoveMMUPage1 with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparteq.
trivial.
Qed.


Lemma wellFormedFstShadowRemoveMMUPage shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild vainve ptVaChildFromSh1:
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
isParent s -> 
noCycleInPartitionTree s -> 
configTablesAreDifferent s -> 
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
isVE ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildFromSh1 sh1idx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildFromSh1) = false-> 
beqVAddr defaultVAddr vainve = true -> 
isEntryVA ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) vainve s -> 
consistency s -> 
In phyDescChild (getPartitions multiplexer s) -> 
wellFormedFstShadow s ->
wellFormedFstShadow
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
 Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hlookup.
intros.
assert(Hsomedefault: getMappedPage pdChildphy s' vaChild = SomeDefault).
    { apply removeMappedPagePutSomeDefault with phyDescChild entry;trivial. }
(* assert(Hderivg :forall partition va,In partition (getPartitions multiplexer s) ->   ~isDerived partition va s' -> ~ isDerived partition va s).
{ intros. apply isDerivedRemoveMMUPage with ptVaChildpd vaChild
entry shadow1Child pdChildphy phyDescChild level;trivial. } *)
assert(Hcons: wellFormedFstShadow s) by trivial.
unfold  wellFormedFstShadow in *.
intros partition Hpartition va pg pd sh1 Hpd Hsh1 Hmapped. 
assert(Hparts : getPartitions multiplexer s' =  getPartitions multiplexer s ).
apply getPartitionsRemoveMMUPage1  with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparts in *. clear Hparts.
assert(Hpd' : forall part, StateLib.getPd part (memory s) =
        StateLib.getPd part (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdRemoveMMUPage with entry;trivial. }
rewrite <- Hpd' in *. clear Hpd'. 
assert(Hsh1s :  StateLib.getFstShadow partition (memory s') =
StateLib.getFstShadow partition (memory s)).
{ intros. apply getFstShadowRemoveMMUPage with entry;trivial. }
rewrite Hsh1s in *; clear Hsh1s.
subst.
 assert (Hgetva : getVirtualAddressSh1 sh1 s va = getVirtualAddressSh1 sh1 s' va).
  { apply getVirtualAddressSh1RemoveMMUPage with  shadow1Child pdChildphy
phyDescChild level entry partition;trivial. }
  rewrite <- Hgetva ;trivial.
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
  - assert (Heqfalse: getMappedPage pdChildphy s' vaChild =
    getMappedPage pdChildphy s' va). 
      { apply getMappedPageEq with level;trivial.
        symmetry;trivial. }
    rewrite Hmapped in Heqfalse.
    rewrite Hsomedefault in Heqfalse.
    now contradict Heqfalse.
  - assert(Hexists: exists vainparent : vaddr,
          getVirtualAddressSh1 sh1 s va = Some vainparent).
    { apply Hcons with phyDescChild pg pdChildphy;trivial.
      rewrite <- Hmapped.
      apply mapPageRemoveSinglePage1 with level (getIndexOfAddr vaChild fstLevel)
      (currentPartition s) phyDescChild entry;trivial.
      symmetry;trivial.
      apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
      symmetry;trivial.
      intros;split;subst;trivial. }
     destruct Hexists as ( vax & Hvax).
     exists vax;trivial.
+ apply Hcons with partition pg pd;trivial.
  rewrite <- Hmapped.
  assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
  { apply isConfigTable  with vaChild;trivial.
  intros;split;subst;trivial. }
  assert(Hconfdiff: configTablesAreDifferent s);trivial.
  apply getMappedPageRemoveMMUPageEq with partition phyDescChild
   vaChild entry level;trivial.
  apply Hconfdiff;trivial.
  intuition.
  intros;split;subst;trivial.
  intuition.
Qed.

Lemma wellFormedSndShadowRemoveMMUPage shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild vainve ptVaChildFromSh1:
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
isParent s -> 
noCycleInPartitionTree s -> 
configTablesAreDifferent s -> 
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
isVE ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildFromSh1 sh1idx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildFromSh1) = false-> 
beqVAddr defaultVAddr vainve = true -> 
isEntryVA ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) vainve s -> 
consistency s -> 
In phyDescChild (getPartitions multiplexer s) -> 
wellFormedSndShadow s ->
wellFormedSndShadow
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
 Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hlookup.
intros.
assert(Hsomedefault: getMappedPage pdChildphy s' vaChild = SomeDefault).
    { apply removeMappedPagePutSomeDefault with phyDescChild entry;trivial. }
(* assert(Hderivg :forall partition va,In partition (getPartitions multiplexer s) ->   ~isDerived partition va s' -> ~ isDerived partition va s).
{ intros. apply isDerivedRemoveMMUPage with ptVaChildpd vaChild
entry shadow1Child pdChildphy phyDescChild level;trivial. } *)
assert(Hcons: wellFormedSndShadow s) by trivial.
unfold  wellFormedSndShadow in *.
intros partition Hpartition Hnotmulti va pg pd sh2 Hpd Hsh2 Hmapped. 
assert(Hparts : getPartitions multiplexer s' =  getPartitions multiplexer s ).
apply getPartitionsRemoveMMUPage1  with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparts in *. clear Hparts.
assert(Hpd' : forall part, StateLib.getPd part (memory s) =
        StateLib.getPd part (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdRemoveMMUPage with entry;trivial. }
rewrite <- Hpd' in *. clear Hpd'. 
assert(Hsh1s :  StateLib.getSndShadow partition (memory s') =
StateLib.getSndShadow partition (memory s)).
{ intros. apply getSndShadowRemoveMMUPage with entry;trivial. }
rewrite Hsh1s in *; clear Hsh1s.
subst.
 assert (Hgetva : getVirtualAddressSh2 sh2 s va = getVirtualAddressSh2 sh2 s' va).
  { apply getVirtualAddressSh2RemoveMMUPage with  shadow1Child pdChildphy
phyDescChild level entry partition;trivial. }
  rewrite <- Hgetva ;trivial.
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
  - assert (Heqfalse: getMappedPage pdChildphy s' vaChild =
    getMappedPage pdChildphy s' va). 
      { apply getMappedPageEq with level;trivial.
        symmetry;trivial. }
    rewrite Hmapped in Heqfalse.
    rewrite Hsomedefault in Heqfalse.
    now contradict Heqfalse.
  - assert(Hexists: exists vainparent : vaddr,
          getVirtualAddressSh2 sh2 s va = Some vainparent /\
          beqVAddr defaultVAddr vainparent = false).
    { apply Hcons with phyDescChild pg pdChildphy;trivial.
      rewrite <- Hmapped.
      apply mapPageRemoveSinglePage1 with level (getIndexOfAddr vaChild fstLevel)
      (currentPartition s) phyDescChild entry;trivial.
      symmetry;trivial.
      apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
      symmetry;trivial.
      intros;split;subst;trivial. }
     destruct Hexists as ( vax & Hvax).
     exists vax;trivial.
+ apply Hcons with partition pg pd;trivial.
  rewrite <- Hmapped.
  assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
  { apply isConfigTable  with vaChild;trivial.
  intros;split;subst;trivial. }
  assert(Hconfdiff: configTablesAreDifferent s);trivial.
  apply getMappedPageRemoveMMUPageEq with partition phyDescChild
   vaChild entry level;trivial.
  apply Hconfdiff;trivial.
  intuition.
  intros;split;subst;trivial.
  intuition.
Qed.

Lemma wellFormedShadowsRemoveMMUPage root shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild:
(root = sh1idx \/ root = sh2idx) -> 
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
In phyDescChild (getPartitions multiplexer s) ->
wellFormedShadows root s ->
wellFormedShadows root {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hwhich Hlookup.
intros.
assert(Hcons: wellFormedShadows root s) by trivial.
assert(Hpds : forall part, StateLib.getPd part (memory s') =
StateLib.getPd part (memory s)).
{ intros. apply getPdRemoveMMUPage with entry;trivial. }
unfold wellFormedShadows in *.
intros partition Hpart pd Hpd structroot Hpp nbL stop Hlevel ind1 va Hind Hnotnull.
rewrite Hpds in *;clear Hpds.
assert(Hpartseq :getPartitions multiplexer s' = getPartitions multiplexer s).
{ apply getPartitionsRemoveMMUPage1  with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial. }
rewrite Hpartseq in *. clear Hpartseq.
assert(HppS: nextEntryIsPP partition root structroot s).
{ destruct Hwhich ;subst;  apply nextEntryIsPPRemoveMMUPage' with ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) 
  ;trivial. }
assert(HindS : getIndirection pd va nbL stop s = Some ind1).
{ apply getIndirectionRemoveMMUPage4 with ptVaChildpd (StateLib.getIndexOfAddr vaChild   fstLevel)
   pdChildphy (currentPartition s)  vaChild
  phyDescChild entry PDidx partition;trivial.
  + symmetry;trivial.
  + apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
    - apply nextEntryIsPPgetPd;trivial.
    - symmetry;trivial.
    - intros;subst;split;trivial.
  + subst. apply nextEntryIsPPgetPd;trivial.
  + left;trivial. }
assert(Hnewgoal : exists indirection2 : page,
  getIndirection structroot va nbL stop s = Some indirection2 /\
  (defaultPage =? indirection2) = false).
{ move Hcons at bottom. apply Hcons with partition pd ind1;trivial. } 
destruct Hnewgoal as (ind2 & Hind2 & Hdef).
exists ind2;split;trivial.
rewrite <- Hind2.
apply getIndirectionRemoveMMUPage5  with pdChildphy (currentPartition s)
          vaChild phyDescChild entry root partition;trivial.
        symmetry;trivial.
        apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
        apply nextEntryIsPPgetPd;trivial.
        symmetry;trivial.
          intros;subst;split;trivial.
          destruct Hwhich;subst. 
         right;left;trivial.
        do 2 right;trivial.
Qed.

Lemma wellFormedFstShadowIfNoneRemoveMMUPage shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild vainve ptVaChildFromSh1:
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) -> 
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
isParent s -> 
noCycleInPartitionTree s -> 
configTablesAreDifferent s -> 
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
isVE ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildFromSh1 sh1idx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildFromSh1) = false-> 
beqVAddr defaultVAddr vainve = true -> 
isEntryVA ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) vainve s -> 
consistency s -> 
In phyDescChild (getPartitions multiplexer s) -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfNone
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
 Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hlookup.
intros.
assert(Hsomedefault: getMappedPage pdChildphy s' vaChild = SomeDefault).
    { apply removeMappedPagePutSomeDefault with phyDescChild entry;trivial. }
(* assert(Hderivg :forall partition va,In partition (getPartitions multiplexer s) ->   ~isDerived partition va s' -> ~ isDerived partition va s).
{ intros. apply isDerivedRemoveMMUPage with ptVaChildpd vaChild
entry shadow1Child pdChildphy phyDescChild level;trivial. } *)
assert(Hcons: wellFormedFstShadowIfNone s) by trivial.
unfold  wellFormedFstShadowIfNone in *.
intros partition va pd sh1  Hpartition  Hpd Hsh1 Hmapped. 
assert(Hparts : getPartitions multiplexer s' =  getPartitions multiplexer s ).
apply getPartitionsRemoveMMUPage1  with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparts in *. clear Hparts.
assert(Hpd' : forall part, StateLib.getPd part (memory s) =
        StateLib.getPd part (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdRemoveMMUPage with entry;trivial. }
rewrite <- Hpd' in *. clear Hpd'. 
assert(Hsh1s :  StateLib.getFstShadow partition (memory s') =
StateLib.getFstShadow partition (memory s)).
{ intros. apply getFstShadowRemoveMMUPage with entry;trivial. }
rewrite Hsh1s in *; clear Hsh1s.
subst.
 assert (Hgetva : getVirtualAddressSh1 sh1 s va = getVirtualAddressSh1 sh1 s' va).
  { apply getVirtualAddressSh1RemoveMMUPage with  shadow1Child pdChildphy
phyDescChild level entry partition;trivial. }
  rewrite <- Hgetva ;trivial.
assert (Hpdflag :  getPDFlag sh1 va s' = getPDFlag sh1 va s).
{  apply getPDFlagRemoveMMUPage with shadow1Child pdChildphy
phyDescChild level entry partition;trivial.
symmetry;trivial. }
rewrite Hpdflag.
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
  - assert (Heqfalse: getMappedPage pdChildphy s' vaChild =
    getMappedPage pdChildphy s' va). 
      { apply getMappedPageEq with level;trivial.
        symmetry;trivial. }
    rewrite Hmapped in Heqfalse.
    rewrite Hsomedefault in Heqfalse.
    now contradict Heqfalse.
  - assert(Hexists: getPDFlag sh1 va s = false /\ getVirtualAddressSh1 sh1 s va = None).
    { apply Hcons with phyDescChild pdChildphy;trivial.
      rewrite <- Hmapped.
      apply mapPageRemoveSinglePage1 with level (getIndexOfAddr vaChild fstLevel)
      (currentPartition s) phyDescChild entry;trivial.
      symmetry;trivial.
      apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
      symmetry;trivial.
      intros;split;subst;trivial. }
     destruct Hexists as ( vax & Hvax).
     split;trivial.
+ apply Hcons with partition pd;trivial.
  rewrite <- Hmapped.
  assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
  { apply isConfigTable  with vaChild;trivial.
  intros;split;subst;trivial. }
  assert(Hconfdiff: configTablesAreDifferent s);trivial.
  apply getMappedPageRemoveMMUPageEq with partition phyDescChild
   vaChild entry level;trivial.
  apply Hconfdiff;trivial.
  intuition.
  intros;split;subst;trivial.
  intuition.
Qed.

Lemma wellFormedFstShadowIfDefaultValuesRemoveMMUPage shadow1Child s ptVaChildpd  pdChildphy phyDescChild
level entry vaChild vainve ptVaChildFromSh1:
lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry) ->
wellFormedFstShadow s -> 
partitionDescriptorEntry s ->
accessibleVAIsNotPartitionDescriptor s ->
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
noDupPartitionTree s -> 
wellFormedFstShadowIfNone s ->
wellFormedFstShadowIfDefaultValues s ->
partitionDescriptorEntry s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
In (currentPartition s) (getPartitions multiplexer s) ->
In phyDescChild (getChildren (currentPartition s) s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s ->
Some level = getNbLevel -> 
isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildpd) = false-> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
entryUserFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s-> 
pa entry <> defaultPage -> 
pdChildphy <> defaultPage -> 
isParent s -> 
noCycleInPartitionTree s -> 
configTablesAreDifferent s -> 
nextEntryIsPP phyDescChild sh1idx shadow1Child s -> 
isVE ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) s-> 
getTableAddrRoot ptVaChildFromSh1 sh1idx phyDescChild vaChild s-> 
(defaultPage =? ptVaChildFromSh1) = false-> 
beqVAddr defaultVAddr vainve = true -> 
isEntryVA ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) vainve s -> 
consistency s -> 
In phyDescChild (getPartitions multiplexer s) -> 
wellFormedFstShadowIfDefaultValues s ->
wellFormedFstShadowIfDefaultValues
  {|
  currentPartition := currentPartition s;
  memory := add ptVaChildpd (getIndexOfAddr vaChild fstLevel)
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
 Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hlookup.
intros.
assert(Hsomedefault: getMappedPage pdChildphy s' vaChild = SomeDefault).
    { apply removeMappedPagePutSomeDefault with phyDescChild entry;trivial. }
(* assert(Hderivg :forall partition va,In partition (getPartitions multiplexer s) ->   ~isDerived partition va s' -> ~ isDerived partition va s).
{ intros. apply isDerivedRemoveMMUPage with ptVaChildpd vaChild
entry shadow1Child pdChildphy phyDescChild level;trivial. } *)
assert(Hcons: wellFormedFstShadowIfDefaultValues s) by trivial.
unfold  wellFormedFstShadowIfDefaultValues in *.
intros partition va pd sh1  Hpartition  Hpd Hsh1 Hmapped. 
assert(Hparts : getPartitions multiplexer s' =  getPartitions multiplexer s ).
apply getPartitionsRemoveMMUPage1  with shadow1Child  pdChildphy
    phyDescChild level entry ;trivial.
rewrite Hparts in *. clear Hparts.
assert(Hpd' : forall part, StateLib.getPd part (memory s) =
        StateLib.getPd part (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdRemoveMMUPage with entry;trivial. }
rewrite <- Hpd' in *. clear Hpd'. 
assert(Hsh1s :  StateLib.getFstShadow partition (memory s') =
StateLib.getFstShadow partition (memory s)).
{ intros. apply getFstShadowRemoveMMUPage with entry;trivial. }
rewrite Hsh1s in *.
subst.
 assert (Hgetva : getVirtualAddressSh1 sh1 s va = getVirtualAddressSh1 sh1 s' va).
  { apply getVirtualAddressSh1RemoveMMUPage with  shadow1Child pdChildphy
phyDescChild level entry partition;trivial. }
rewrite <- Hgetva ;trivial.
assert (Hpdflag :  getPDFlag sh1 va s' = getPDFlag sh1 va s).
{  apply getPDFlagRemoveMMUPage with shadow1Child pdChildphy
phyDescChild level entry partition;trivial.
symmetry;trivial. }
rewrite Hpdflag.
assert (Hexistmap: getMappedPage pdChildphy s vaChild = SomePage (pa entry)).
{ apply getMappedPageGetTableRoot with  ptVaChildpd phyDescChild;trivial.
  intros;split;subst;trivial.
  unfold isEntryPage.
  rewrite Hlookup;trivial. }
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
  - split;trivial.
  assert(Hpdflagx : getPDFlag shadow1Child vaChild s = false). 
 { assert(Haccessible :getAccessibleMappedPage pdChildphy s vaChild = SomePage (pa entry)). 
   {  apply isAccessibleMappedPage2 with phyDescChild ptVaChildpd;trivial.
      apply isEntryPageReadPhyEntry2;trivial.
      unfold readPhyEntry.
      rewrite Hlookup;reflexivity.
      intros.
      split;subst;trivial. }
     assert(Hkey: accessibleVAIsNotPartitionDescriptor s) by trivial.
      unfold accessibleVAIsNotPartitionDescriptor in *. 
      apply Hkey  with phyDescChild pdChildphy (pa entry);
      trivial. apply nextEntryIsPPgetFstShadow;trivial.
       }
  assert(Hpdeq : sh1 = shadow1Child).
  { symmetry. apply getSh1NextEntryIsPPEq with phyDescChild s;trivial. }
  subst sh1.
  rewrite <- Hpdflagx.
  symmetry.
  apply getPDFlagEq with level;trivial.
  symmetry;trivial.
  assert(Hnotshared : ~ isDerived phyDescChild vaChild s ).
      { apply vaNotDerived with ptVaChildFromSh1;trivial.
        unfold consistency in *;intuition.
        exists defaultVAddr;split;trivial.
        assert(defaultVAddr =vainve).
        apply beqVAddrTrueEq;trivial.
        subst. trivial.
        apply beqVAddrTrue.
        intros;split;subst;trivial. }
  unfold isDerived in Hnotshared.
  rewrite Hsh1 in Hnotshared.
  case_eq(getVirtualAddressSh1 sh1 s vaChild);[intros vax Hvax | intros Hvax];
  rewrite Hvax in  Hnotshared.
  * apply not_false_is_true in Hnotshared.
    apply beqVAddrTrueEq in Hnotshared.
    subst.
    rewrite <- Hvax.
    symmetry.
    apply getVirtualAddressSh1Eq with level;trivial.
    symmetry;trivial.
  * assert(Hwell: wellFormedFstShadow s) by trivial.
     assert(Hkey:  exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va = Some vainparent).
     { unfold wellFormedFstShadow in Hwell.
    apply Hwell with phyDescChild (pa entry) pdChildphy ;trivial.
    rewrite <- Hexistmap.
    symmetry.
    apply getMappedPageEq with level;trivial.
    symmetry;trivial. }
    destruct Hkey as (vainparent & Hvainparent).
    assert(Heq: getVirtualAddressSh1 sh1 s vaChild = getVirtualAddressSh1 sh1 s va).
     apply getVirtualAddressSh1Eq with level;trivial.
    symmetry;trivial.
    rewrite <- Heq in Hvainparent.
    rewrite Hvax in Hvainparent.
    now contradict Hvainparent.
 - apply Hcons with phyDescChild pdChildphy;trivial.
      rewrite <- Hmapped.
      apply mapPageRemoveSinglePage1 with level (getIndexOfAddr vaChild fstLevel)
      (currentPartition s) phyDescChild entry;trivial.
      symmetry;trivial.
      apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
      symmetry;trivial.
      intros;split;subst;trivial.
+ apply Hcons with partition pd;trivial.
  rewrite <- Hmapped.
  assert(Hconfigpt : In ptVaChildpd (getConfigPages phyDescChild s)). 
  { apply isConfigTable  with vaChild;trivial.
  intros;split;subst;trivial. }
  assert(Hconfdiff: configTablesAreDifferent s);trivial.
  apply getMappedPageRemoveMMUPageEq with partition phyDescChild
   vaChild entry level;trivial.
  apply Hconfdiff;trivial.
  intuition.
  intros;split;subst;trivial.
  intuition.
Qed.


Lemma  consistencyRemoveMMUPage  s descChild (vaChild:vaddr) 
currentPart 
level 
(* currentShadow1 *)
idxDescChild
ptDescChild
(* ischild *) 
currentPD  ptDescChildFromPD 
idxDescChild1 
(* presentDescPhy *)
phyDescChild  pdChildphy 
(* idxvaChild  *)
ptVaChildpd  shadow1Child  ptVaChildFromSh1
(* childListSh1Isnull *) 
vainve 
sh2Childphy  ptVaChildsh2
vainparent 
currentShadow  ptVaInCurPart 
idxvainparent (* defaultpage *):
propagatedPropertiesRemoveVaddr s  descChild vaChild currentPart  level (* currentShadow1 *)  
idxDescChild ptDescChild (* true *) currentPD  ptDescChildFromPD 
idxDescChild1 (* true *)
phyDescChild  pdChildphy (getIndexOfAddr vaChild fstLevel) ptVaChildpd  shadow1Child  ptVaChildFromSh1 (* childListSh1Isnull *) 
vainve  sh2Childphy  ptVaChildsh2  vainparent vainparent currentShadow  ptVaInCurPart idxvainparent (* defaultVAddr *)  
(* defaultPage *) true true ->
consistency {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd  (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}. 
Proof.
(* set(s':= {|  currentPartition := _ |}) in *. *)
(* set(s':= {|  currentPartition := _ |}) in *. *)
intros.
unfold propagatedPropertiesRemoveVaddr in *.
intuition. subst.
assert (exists entry : Pentry,
      lookup  ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      intuition. }

destruct Hlookup as (entry & Hlookup).
assert((pa entry) <> defaultPage).
{ assert(Hconspresent: isPresentNotDefaultIff s). { unfold consistency in *; intuition. }
  unfold isPresentNotDefaultIff in *.
  generalize (Hconspresent ptVaChildpd (getIndexOfAddr vaChild fstLevel)); 
  clear Hconspresent; intros Hconspresent.
  destruct Hconspresent as (Hleft & Hright).
  assert(Hentry :  entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s) by trivial.
  unfold not.
  intros Htrue.
  unfold readPhyEntry in Hright.
  rewrite Hlookup in Hright.
  assert (Htmp: Some (pa entry) = Some defaultPage ); f_equal;trivial.
  apply Hright in Htmp.  
  subst.
  assert(Htmp2: entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s)
  by trivial.
  apply entryPresentFlagReadPresent in Htmp2.
  rewrite Htmp in  Htmp2.
  inversion Htmp2. }
assert(Hchildpart : In phyDescChild (getPartitions multiplexer s)).
{ unfold consistency in *.
  intuition.
  subst.
  apply childrenPartitionInPartitionList with (currentPartition s);trivial. }
assert(Hpdnotnull: pdChildphy <> defaultPage).
{ apply pdPartNotNull with phyDescChild s;trivial.
  unfold consistency in *.
  intuition. } 
  
unfold consistency in *. intuition.
+ apply partitionDescriptorEntryRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry;trivial.

+ apply dataStructurePdSh1Sh2asRootRemoveMMUPagePD with shadow1Child pdChildphy
    phyDescChild level entry;trivial.

+ apply dataStructurePdSh1Sh2asRootRemoveMMUPageSh1 with shadow1Child pdChildphy
    phyDescChild level entry;trivial.

+ apply dataStructurePdSh1Sh2asRootRemoveMMUPageSh2 with shadow1Child pdChildphy
    phyDescChild level entry;trivial.

+ apply currentPartitionInPartitionsListRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry;trivial.

+ apply noDupMappedPagesListRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry;trivial.

+ apply noDupConfigPagesListRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry;trivial;unfold consistency;intuition.

+ apply parentInPartitionListRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry;trivial.

+ apply accessibleVAIsNotPartitionDescriptorRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry;trivial.

+ apply accessibleChildPageIsAccessibleIntoParentRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry  vainve ptVaChildFromSh1;unfold consistency;intuition.

+ apply noCycleInPartitionTreeRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry;trivial.

+ apply configTablesAreDifferentRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry;unfold consistency;intuition.

+ apply isChildRemoveMMUPage  with shadow1Child pdChildphy
    phyDescChild level entry;trivial.

+ apply isPresentNotDefaultIffRemoveMMUPage with  entry;trivial.

+ apply physicalPageNotDerivedRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry  vainve ptVaChildFromSh1; unfold consistency;intuition.

+ apply multiplexerWithoutParentRemoveMMUPage with entry; trivial.

+ apply isParentRemoveMMUPage  with shadow1Child pdChildphy
    phyDescChild level entry;trivial.

+ apply noDupPartitionTreeRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry;trivial.

+ apply wellFormedFstShadowRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry  vainve ptVaChildFromSh1; unfold consistency;intuition.

+ apply wellFormedSndShadowRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry  vainve ptVaChildFromSh1; unfold consistency;intuition.

+ apply wellFormedShadowsRemoveMMUPage with  shadow1Child pdChildphy
    phyDescChild level entry;trivial;left;trivial.

+ apply wellFormedShadowsRemoveMMUPage with  shadow1Child pdChildphy
    phyDescChild level entry;trivial;right;trivial.

+ apply wellFormedFstShadowIfNoneRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry  vainve ptVaChildFromSh1; unfold consistency;intuition.

+ apply wellFormedFstShadowIfDefaultValuesRemoveMMUPage with shadow1Child pdChildphy
    phyDescChild level entry  vainve ptVaChildFromSh1; unfold consistency;intuition.
Qed.

Lemma getTableAddrRootRemoveMMUPage  vaChild s rootidx root 
(ptVaChildpd phyDescChild: page)  pdChildphy entry pt partition va: 
 (rootidx = PDidx \/ rootidx = sh1idx \/ rootidx = sh2idx) -> 
 lookup ptVaChildpd (getIndexOfAddr vaChild fstLevel) (memory s)
            beqPage beqIndex = Some (PE entry) -> 
 isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s -> 
 
(* getTableAddrRoot ptVaChildpd rootidx phyDescChild vaChild s ->  *)
nextEntryIsPP partition rootidx root s -> 


partitionDescriptorEntry s -> 
isPresentNotDefaultIff s ->
noDupConfigPagesList s -> 
configTablesAreDifferent s -> 

In (currentPartition s) (getPartitions multiplexer s) -> 

In phyDescChild (getPartitions multiplexer s) -> 

getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 

nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
In partition (getPartitions multiplexer s) -> 
(defaultPage =? ptVaChildpd) = false -> 
entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s -> 
root <> defaultPage ->
getTableAddrRoot pt rootidx partition va s -> 
getTableAddrRoot pt rootidx partition va {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd  (StateLib.getIndexOfAddr vaChild fstLevel)
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|  currentPartition := _ |}) in *.
intros Hor Hlookup Hpe (* Htblroot *) (* Hpdchild *). intros.
subst. 
assert(Htrue1 : StateLib.readPhyEntry  ptVaChildpd
(StateLib.getIndexOfAddr vaChild fstLevel) (memory s) =Some (pa entry)).
{ unfold  readPhyEntry. rewrite Hlookup;trivial. }
assert(Htrue2 : StateLib.readPhyEntry  ptVaChildpd
  (StateLib.getIndexOfAddr vaChild fstLevel) (memory s') =Some defaultPage).
{ unfold StateLib.readPhyEntry. 
cbn.
assert(Hpairs : beqPairs (ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel)
(ptVaChildpd, StateLib.getIndexOfAddr vaChild fstLevel) beqPage
beqIndex = true); intros.
rewrite <- beqPairsTrue;split;trivial.
rewrite Hpairs.
simpl;trivial. }
(* apply getAccessibleMappedPageNotPresent with ptVaChildpd phyDescChild;
  trivial. 
  + intros. 
  split. 
  apply isPERemoveMMUPage with entry;trivial.
  subst;trivial. *)
 assert(Htblroot:  getTableAddrRoot pt rootidx partition va s) by trivial.

   unfold getTableAddrRoot in Htblroot.
   unfold getTableAddrRoot.
  assert(Hpdchild2 : nextEntryIsPP partition rootidx root s) by trivial.
  destruct Htblroot as (Hidxs & Htblroot).
  assert(Hpdchild : nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
 split;trivial.
  intros.  apply Htblroot in Hpdchild2;clear Htblroot.
  move Hpdchild2 at bottom.
  destruct Hpdchild2 as (nbL & HnbL & stop & Hstop & Hind1).
  exists nbL ; split ; trivial.
  exists stop;split;trivial.
(*   destruct Hor as [Hor | [Hor | Hor]].
  * subst. *)
assert(tableroot = root). 
{ assert(Hkey : nextEntryIsPP partition rootidx tableroot s).
apply nextEntryIsPPRemoveMMUPage' with ptVaChildpd (getIndexOfAddr vaChild fstLevel)
;trivial.
assert(Hkey2: nextEntryIsPP partition rootidx root s) by trivial.
unfold nextEntryIsPP in Hkey.
unfold nextEntryIsPP in Hkey2.
destruct (Index.succ rootidx);intros;try now contradict Hkey.
destruct (lookup partition i (memory s) beqPage beqIndex);intros;try now contradict Hkey.
destruct v;intros;try now contradict Hkey.
subst;trivial. }
  subst.
  

  rewrite <- Hind1.
  apply getIndirectionRemoveMMUPage5 with  
   pdChildphy (currentPartition s)  vaChild
  phyDescChild entry rootidx partition;trivial.
  + symmetry;trivial.
  + apply pdPartNotNull with phyDescChild s;trivial.
  + apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
    - apply nextEntryIsPPgetPd;trivial.
    - symmetry;trivial.
    - intros;subst;split;trivial.

  Qed.
Lemma isEntryPageRemoveMMUPage table1 table2 idx1 idx2 p s :
table1 <> table2 \/ idx1 <> idx2 -> 
 isEntryPage table1 idx1 p s -> 
 isEntryPage table1 idx1 p {|
      currentPartition := currentPartition s;
      memory := add table2 idx2
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
unfold isEntryPage.
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
Lemma entryPresentFlagRemoveMMUPage table1 table2 idx1 idx2 p s :
table1 <> table2 \/ idx1 <> idx2 -> 
 entryPresentFlag table1 idx1 p s -> 
 entryPresentFlag table1 idx1 p {|
      currentPartition := currentPartition s;
      memory := add table2 idx2
                  (PE
                     {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := defaultPage |}) (memory s) beqPage beqIndex |}.
Proof.
unfold entryPresentFlag.
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
Lemma writePhyEntryRemoveMMUPage  descChild (vaChild:vaddr) 
currentPart 
level 
(* currentShadow1 *)
idxDescChild
ptDescChild
(* ischild *) 
currentPD  ptDescChildFromPD 
idxDescChild1 
(* presentDescPhy *)
phyDescChild  pdChildphy 
idxvaChild 
ptVaChildpd  shadow1Child  ptVaChildFromSh1
(* childListSh1Isnull *) 
vainve 
sh2Childphy  ptVaChildsh2
vainparent 
currentShadow  ptVaInCurPart 
idxvainparent defaultpage:

{{ fun s : state =>
   propagatedPropertiesRemoveVaddr s  descChild vaChild currentPart level (* currentShadow1 *)  
idxDescChild ptDescChild (* true *) currentPD  ptDescChildFromPD idxDescChild1 (* true *)
phyDescChild  pdChildphy idxvaChild ptVaChildpd  shadow1Child  ptVaChildFromSh1 (* childListSh1Isnull *) 
vainve sh2Childphy  ptVaChildsh2  vainparent vainparent currentShadow  ptVaInCurPart idxvainparent (* defaultVAddr *)  
(* defaultPage *) true true /\ (getIndexOfAddr vaChild fstLevel) = idxvaChild /\
defaultPage = defaultpage }} 
  writePhyEntry ptVaChildpd idxvaChild  defaultpage false false false false false  {{ fun _ (s : state) =>
     propagatedPropertiesRemoveVaddr s  descChild vaChild currentPart level (* currentShadow1 *)  
idxDescChild ptDescChild (* true *) currentPD  ptDescChildFromPD idxDescChild1 (* true *)
phyDescChild  pdChildphy idxvaChild ptVaChildpd  shadow1Child  ptVaChildFromSh1 (* childListSh1Isnull *) 
vainve sh2Childphy  ptVaChildsh2  vainparent vainparent currentShadow  ptVaInCurPart idxvainparent (* defaultVAddr *)  
(* defaultPage *) false false /\ getPDFlag currentShadow vainparent s = false /\ 
(exists pagetoremove, getAccessibleMappedPage currentPD s vainparent = SomePage  pagetoremove /\ 
(forall child, In child (getChildren currentPart s) -> ~In  pagetoremove (getMappedPages child s)))
}}.
Proof.
intros;subst.
eapply weaken.
eapply WP.writePhyEntry.
simpl;intros.

set(s':= {|  currentPartition := _ |}) in *.
intros.
unfold propagatedPropertiesRemoveVaddr in *.
assert (exists entry : Pentry,
      lookup  ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      intuition. }

destruct Hlookup as (entry & Hlookup).
assert((pa entry) <> defaultPage).
{ assert(Hconspresent: isPresentNotDefaultIff s). { unfold consistency in *; intuition. }
  unfold isPresentNotDefaultIff in *.
  generalize (Hconspresent ptVaChildpd (getIndexOfAddr vaChild fstLevel)); 
  clear Hconspresent; intros Hconspresent.
  destruct Hconspresent as (Hleft & Hright).
  assert(Hentry :  entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s).
  { intuition. subst;trivial. }
  unfold not.
  intros Htrue.
  unfold readPhyEntry in Hright.
  rewrite Hlookup in Hright.
  assert (Htmp: Some (pa entry) = Some defaultPage ); f_equal;trivial.
  apply Hright in Htmp.  
  subst.
  assert(Htmp2: entryPresentFlag ptVaChildpd (getIndexOfAddr vaChild fstLevel) true s)
  by trivial.
  apply entryPresentFlagReadPresent in Htmp2.
  rewrite Htmp in  Htmp2.
  inversion Htmp2. }
assert(Hchildpart : In phyDescChild (getPartitions multiplexer s)).
{ unfold consistency in *.
  intuition.
  subst.
  apply childrenPartitionInPartitionList with (currentPartition s);trivial. }
assert(Hpdnotnull: pdChildphy <> defaultPage).
{ apply pdPartNotNull with phyDescChild s;trivial.
  unfold consistency in *.
  intuition.  unfold consistency in *.
  intuition. }
assert(Hsh1notnull: shadow1Child <> defaultPage).
{ unfold consistency in *.
   apply sh1PartNotNull with phyDescChild s;intuition. }
assert(Hsh2notnull: sh2Childphy <> defaultPage).
{ unfold consistency in *.
   apply sh2PartNotNull with phyDescChild s;intuition. }
assert(Hsh1curpartnotnull: currentShadow <> defaultPage).
{ unfold consistency in *.
   apply sh1PartNotNull with (currentPartition s) s;intuition. subst;trivial. }
assert(Hpdcurpartnotnull: currentPD <> defaultPage).
{ unfold consistency in *.
   apply pdPartNotNull with (currentPartition s) s;intuition.
   subst;trivial. }
assert(Hchildeq : getChildren (currentPartition s') s' = getChildren (currentPartition s') s).
{ unfold consistency in *. 
  intuition.
  subst.  
  apply removeMappedPageGetChildren  with shadow1Child pdChildphy
  phyDescChild level entry ;subst;trivial. }

assert(currentPartitionInPartitionsList s) by (unfold consistency in *;intuition).
unfold currentPartitionInPartitionsList in *.

intuition try assumption;subst. 
+ apply partitionsIsolationRemoveMMUPage with shadow1Child (getIndexOfAddr vaChild fstLevel) phyDescChild
(currentPartition s) currentShadow descChild (getIndexOfAddr descChild fstLevel) ptDescChild currentPD
ptDescChildFromPD (getIndexOfAddr descChild fstLevel) pdChildphy level;trivial.

+ apply kernelDataIsolationRemoveMMUPage with shadow1Child (getIndexOfAddr vaChild fstLevel) phyDescChild
(currentPartition s) currentShadow descChild (getIndexOfAddr descChild fstLevel) ptDescChild currentPD
ptDescChildFromPD (getIndexOfAddr descChild fstLevel) pdChildphy level;trivial.

+ apply verticalSharingRemoveMMUPage with shadow1Child (getIndexOfAddr vaChild fstLevel) phyDescChild
(currentPartition s) currentShadow descChild (getIndexOfAddr descChild fstLevel) ptDescChild currentPD
ptDescChildFromPD (getIndexOfAddr descChild fstLevel) pdChildphy level ptVaChildFromSh1 vainve;trivial.

+ apply consistencyRemoveMMUPage with descChild (currentPartition s)level (* currentShadow1 *) (getIndexOfAddr descChild fstLevel) ptDescChild 
currentPD ptDescChildFromPD (getIndexOfAddr descChild fstLevel) phyDescChild
pdChildphy shadow1Child ptVaChildFromSh1 (* childListSh1Isnull *) vainve
sh2Childphy ptVaChildsh2 vainparent currentShadow ptVaInCurPart
(StateLib.getIndexOfAddr vainparent fstLevel);unfold propagatedPropertiesRemoveVaddr;intuition.

+ apply nextEntryIsPPRemoveMMUPage with entry;trivial.
+ apply isVERemoveMMUPage with entry;trivial.
+ unfold consistency in *. 
  apply getTableAddrRootRemoveMMUPage with currentShadow phyDescChild pdChildphy entry;intuition.  
+ apply entryPDFlagRemoveMMUPage with entry;trivial.
+ apply nextEntryIsPPRemoveMMUPage with entry;trivial.
+ apply isPERemoveMMUPage with entry;trivial.
+ unfold consistency in *. 
  apply getTableAddrRootRemoveMMUPage with currentPD phyDescChild pdChildphy entry;intuition. 
+ assert(Hinconfig1 : In ptDescChildFromPD (getConfigPages (currentPartition s) s)). 
  { apply isConfigTable with descChild ;trivial.
    unfold consistency in *;intuition.
    assert(currentPartitionInPartitionsList s) by (unfold consistency in *;intuition).
    unfold currentPartitionInPartitionsList in *;trivial.
    intros;subst;split;trivial. }
  assert(Hconfigdiff : configTablesAreDifferent s) by (unfold consistency in *;intuition).
  assert(Hinconfig2 : In ptVaChildpd (getConfigPages phyDescChild s)). 
  { apply isConfigTable with vaChild ;trivial.
    unfold consistency in *;intuition.
    intros;subst;split;trivial. }
  apply entryPresentFlagRemoveMMUPage;trivial.
  left.
  unfold configTablesAreDifferent in Hconfigdiff.
  unfold not;intros;subst.
  unfold disjoint in Hconfigdiff.
  contradict Hinconfig2.
  apply Hconfigdiff with (currentPartition s);trivial.
  
  assert(Hnocycle: noCycleInPartitionTree s) by (unfold consistency in *;intuition).
  assert( HparentphyDesc :getParent phyDescChild (memory s) = Some (currentPartition s)).
  { assert(Hisparent: isParent s) by (unfold consistency in *;intuition).
    unfold isParent in Hisparent.
    apply Hisparent;trivial. }
  apply Hnocycle;trivial.
   unfold getAncestors.
  destruct nbPage;simpl;
  rewrite HparentphyDesc;simpl;left;trivial. 
+ assert(Hinconfig1 : In ptDescChildFromPD (getConfigPages (currentPartition s) s)). 
  { apply isConfigTable with descChild ;trivial.
    unfold consistency in *;intuition.
    assert(currentPartitionInPartitionsList s) by (unfold consistency in *;intuition).
    unfold currentPartitionInPartitionsList in *;trivial.
    intros;subst;split;trivial. }
  assert(Hconfigdiff : configTablesAreDifferent s) by (unfold consistency in *;intuition).
  assert(Hinconfig2 : In ptVaChildpd (getConfigPages phyDescChild s)). 
  { apply isConfigTable with vaChild ;trivial.
    unfold consistency in *;intuition.
    intros;subst;split;trivial. }
  apply isEntryPageRemoveMMUPage;trivial.
  left.
  unfold configTablesAreDifferent in Hconfigdiff.
  unfold not;intros;subst.
  unfold disjoint in Hconfigdiff.
  contradict Hinconfig2.
  apply Hconfigdiff with (currentPartition s);trivial.
  
  assert(Hnocycle: noCycleInPartitionTree s) by (unfold consistency in *;intuition).
  assert( HparentphyDesc :getParent phyDescChild (memory s) = Some (currentPartition s)).
  { assert(Hisparent: isParent s) by (unfold consistency in *;intuition).
    unfold isParent in Hisparent.
    apply Hisparent;trivial. }
  apply Hnocycle;trivial.
   unfold getAncestors.
  destruct nbPage;simpl;
  rewrite HparentphyDesc;simpl;left;trivial.
+ rewrite Hchildeq in *;trivial.
+ apply nextEntryIsPPRemoveMMUPage with entry;trivial.
+ apply isPERemoveMMUPage with entry;trivial.
+ unfold consistency in *. 
  apply getTableAddrRootRemoveMMUPage with pdChildphy phyDescChild pdChildphy entry;intuition.  
+ unfold entryUserFlag. cbn.
  assert(Hbeqpairs: beqPairs (ptVaChildpd, getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, getIndexOfAddr vaChild fstLevel) beqPage beqIndex = true).
   apply beqPairsTrue;split;trivial.
  rewrite Hbeqpairs.
  simpl;trivial.
+ unfold entryPresentFlag. cbn.
  assert(Hbeqpairs: beqPairs (ptVaChildpd, getIndexOfAddr vaChild fstLevel)
      (ptVaChildpd, getIndexOfAddr vaChild fstLevel) beqPage beqIndex = true).
   apply beqPairsTrue;split;trivial.
  rewrite Hbeqpairs.
  simpl;trivial.
+ apply nextEntryIsPPRemoveMMUPage with entry;trivial.
+ apply isVERemoveMMUPage with entry;trivial.
+ unfold consistency in *. 
  apply getTableAddrRootRemoveMMUPage with shadow1Child phyDescChild pdChildphy entry;intuition.
+ apply isEntryVARemoveMMUPage with entry;trivial.
+ apply nextEntryIsPPRemoveMMUPage with entry;trivial.
+ apply isVARemoveMMUPage with entry;trivial.
+ unfold consistency in *. 
  apply getTableAddrRootRemoveMMUPage with sh2Childphy phyDescChild pdChildphy entry;intuition.
+ apply isVA'RemoveMMUPage with entry;trivial.
+ apply isVERemoveMMUPage with entry;subst;trivial.
+ unfold consistency in *. 
  apply getTableAddrRootRemoveMMUPage with currentShadow phyDescChild pdChildphy entry;intuition.
+ unfold consistency in *;intuition.
  assert(Hpdflageq: getPDFlag currentShadow vainparent s' =
  getPDFlag currentShadow vainparent s).
  { apply getPDFlagRemoveMMUPage with shadow1Child pdChildphy
      phyDescChild level entry (currentPartition s);subst;trivial.
    symmetry;trivial. apply nextEntryIsPPgetFstShadow;trivial. }
  rewrite Hpdflageq. 
assert(Hcons: accessibleVAIsNotPartitionDescriptor s) by trivial.
unfold accessibleVAIsNotPartitionDescriptor in *.
apply Hcons with (currentPartition s) currentPD (pa entry); trivial.
apply nextEntryIsPPgetPd;trivial.
apply nextEntryIsPPgetFstShadow;trivial.
assert(Hcons2: accessibleChildPageIsAccessibleIntoParent s) by trivial.
unfold accessibleChildPageIsAccessibleIntoParent in *. 
assert(Hcons2ded: isAccessibleMappedPageInParent phyDescChild
vaChild (pa entry) s = true).
{ apply Hcons2 with pdChildphy ;trivial.
apply nextEntryIsPPgetPd;trivial.
apply isAccessibleMappedPage2 with phyDescChild ptVaChildpd;trivial.
unfold isEntryPage.
rewrite Hlookup;trivial.
intros;split;subst;trivial. }
unfold isAccessibleMappedPageInParent in Hcons2ded.
assert(Hsh2: getSndShadow phyDescChild (memory s) = Some sh2Childphy) by (
apply nextEntryIsPPgetSndShadow; trivial).
rewrite Hsh2 in *.
assert(Hgetvainparent: getVirtualAddressSh2 sh2Childphy s vaChild = Some vainparent). 
{ apply getVirtualAddressSh2GetTableRoot with ptVaChildsh2 phyDescChild level;
trivial.
intros;split;subst;trivial. }
rewrite Hgetvainparent in *.
assert(Hparent: getParent phyDescChild (memory s) = Some (currentPartition s)).
assert(Hisparent: isParent s) by trivial.
apply Hisparent;trivial.
rewrite Hparent in *.
assert(Hcurrentpd: getPd (currentPartition s) (memory s) = Some currentPD).
apply nextEntryIsPPgetPd;trivial.
rewrite Hcurrentpd in *.
case_eq(getAccessibleMappedPage currentPD s vainparent );
[intros pg Hpg | intros Hpg |intros Hpg]; rewrite Hpg in *;
try now contradict Hcons2ded.
f_equal.
apply beq_nat_true in Hcons2ded.

symmetry;trivial.
destruct pg;simpl in *;
   destruct (pa entry) ;simpl in *;
  subst.
  assert(Hbof : {| p := p; Hp := Hp0 |} ={| p := p; Hp := Hp |}).
  f_equal.
  apply proof_irrelevance.
  subst.
  simpl in *.
  inversion Hbof.
  rewrite Hbof in *.
  trivial.
+ unfold consistency in *;intuition.
  exists (pa entry).
   assert(Hconfigdiff : configTablesAreDifferent s) by (unfold consistency in *;intuition).
  assert(Hinconfig2 : In ptVaChildpd (getConfigPages phyDescChild s)). 
  { apply isConfigTable with vaChild ;trivial.
    intros;subst;split;trivial. }  
   assert(Hconfdiff : configTablesAreDifferent s)by trivial.
  split.
  assert(Hisparent: isParent s) by trivial.
  assert( (currentPartition s) <> phyDescChild ).
      { assert(Hparent : StateLib.getParent phyDescChild (memory s) = Some (currentPartition s))by
      (apply Hisparent;trivial).
      assert (Hisances : In (currentPartition s) (getAncestors phyDescChild s)) by(
      unfold getAncestors;destruct nbPage;simpl;rewrite Hparent;simpl
      ;left;trivial).
      assert(Hnocycle : noCycleInPartitionTree s) by 
      (unfold consistency in *; intuition).
      apply Hnocycle;trivial. }
  assert(Haccess: getAccessibleMappedPage currentPD s vainparent =
  getAccessibleMappedPage currentPD s' vainparent).
  { apply getAccessibleMappedPageRemoveMMUPage1 with (currentPartition s) phyDescChild vaChild entry level;trivial.
   apply Hconfdiff;trivial.
   intuition.
  apply Hconfdiff;trivial.
  intuition.
 intros;split;subst;trivial.
 intuition.
  apply nextEntryIsPPgetPd;trivial. }
rewrite <- Haccess;trivial.
assert(Hconsaccess: accessibleChildPageIsAccessibleIntoParent s ) by trivial.
assert(Hconsisaccess : isAccessibleMappedPageInParent phyDescChild vaChild (pa entry) s = true).
unfold accessibleChildPageIsAccessibleIntoParent in *.
apply Hconsaccess with pdChildphy;trivial.
apply nextEntryIsPPgetPd;trivial.
apply isAccessibleMappedPage2 with phyDescChild ptVaChildpd;trivial.
unfold isEntryPage.
rewrite Hlookup;trivial.
intros;split;subst;trivial.
unfold isAccessibleMappedPageInParent in Hconsisaccess.
assert(Hsh2: getSndShadow phyDescChild (memory s) = Some sh2Childphy) by (
apply nextEntryIsPPgetSndShadow; trivial).
rewrite Hsh2 in *.
assert(Hgetvainparent: getVirtualAddressSh2 sh2Childphy s vaChild = Some vainparent). 
{ apply getVirtualAddressSh2GetTableRoot with ptVaChildsh2 phyDescChild level;
trivial.
intros;split;subst;trivial. }
rewrite Hgetvainparent in *.
assert(Hparent: getParent phyDescChild (memory s) = Some (currentPartition s)).

apply Hisparent;trivial.
rewrite Hparent in *.
assert(Hcurrentpd: getPd (currentPartition s) (memory s) = Some currentPD).
apply nextEntryIsPPgetPd;trivial.
rewrite Hcurrentpd in *.
case_eq(getAccessibleMappedPage currentPD s vainparent );
[intros pg Hpg | intros Hpg |intros Hpg]; rewrite Hpg in *;
try now contradict Hconsisaccess.
f_equal.
apply beq_nat_true in Hconsisaccess.

symmetry;trivial.
destruct pg;simpl in *;
   destruct (pa entry) ;simpl in *;
  subst.
  assert(Hbof : {| p := p; Hp := Hp0 |} ={| p := p; Hp := Hp |}).
  f_equal.
  apply proof_irrelevance.
  subst.
  simpl in *.
  inversion Hbof.
  rewrite Hbof in *.
  trivial.
  fold not.
  intros child Hchild Hmapped.
  assert(Hgetchild: getChildren (currentPartition s) s= getChildren (currentPartition s) s').
  symmetry.
  apply removeMappedPageGetChildren with shadow1Child pdChildphy phyDescChild level entry;unfold consistency in *;intuition.
  rewrite <- Hgetchild in *. clear Hgetchild.
  contradict Hmapped.
  assert(Hor: phyDescChild = child \/ phyDescChild <> child) by apply pageDecOrNot.
  destruct Hor as [Hor | Hor].
  - subst child. 
    assert(Hsomedefault: getMappedPage pdChildphy s' vaChild = SomeDefault).
    { apply removeMappedPagePutSomeDefault with phyDescChild entry;trivial. }
    assert (Hexistmap: getMappedPage pdChildphy s vaChild = SomePage (pa entry)).
{ apply getMappedPageGetTableRoot with  ptVaChildpd phyDescChild;trivial.
  intros;split;subst;trivial.
  unfold isEntryPage.
  rewrite Hlookup;trivial. }
  
    unfold getMappedPages.
    assert(Hpd' : StateLib.getPd phyDescChild (memory s) =
        StateLib.getPd phyDescChild (memory s')).
{ unfold s'. simpl.
  symmetry. apply getPdRemoveMMUPage with entry;trivial. }
rewrite <- Hpd' in *. clear Hpd'.
   assert(Hpd: nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
   rewrite nextEntryIsPPgetPd in Hpd.
   rewrite Hpd.
   unfold getMappedPagesAux.
   rewrite filterOptionInIff.
   unfold getMappedPagesOption.
   rewrite in_map_iff.
   unfold not;intros Hnot.
   destruct Hnot as (x & Hx & Hxx).
   assert(Hor : checkVAddrsEqualityWOOffset nbLevel vaChild x level = true \/
    checkVAddrsEqualityWOOffset nbLevel vaChild x  level = false ).
  { destruct (checkVAddrsEqualityWOOffset nbLevel vaChild x  level);intuition. }
  destruct Hor as [Hor | Hor].
  * assert (Heqfalse: getMappedPage pdChildphy s' vaChild =
    getMappedPage pdChildphy s' x). 
      { apply getMappedPageEq with level;trivial.
        symmetry;trivial. }
    rewrite Hx in Heqfalse.
    rewrite Hsomedefault in Heqfalse.
    now contradict Heqfalse.
  * assert(Hmapeq: getMappedPage pdChildphy s x = getMappedPage pdChildphy s' x). apply mapPageRemoveSinglePage1 with level (getIndexOfAddr vaChild fstLevel)
      (currentPartition s) phyDescChild entry;trivial.
      symmetry;trivial.
      apply getIndirectionGetTableRoot1 with phyDescChild;trivial.
      symmetry;trivial.
      intros;split;subst;trivial.
      rewrite <- Hmapeq in Hx.
      assert(Hfalse: (pa entry) <> (pa entry)).
      apply twoMappedPagesAreDifferent with vaChild x pdChildphy level s;
      trivial.
      assert(Hnodu: noDupMappedPagesList s) by trivial.
      unfold noDupMappedPagesList in Hnodu;trivial.
      assert(Hchildphy : In phyDescChild (getPartitions multiplexer s)). apply childrenPartitionInPartitionList with (currentPartition s);trivial.
      apply Hnodu in Hchildphy. 
      unfold getMappedPages in Hchildphy.
      assert(Hpdphy: nextEntryIsPP phyDescChild PDidx pdChildphy s) by trivial.
   rewrite nextEntryIsPPgetPd in Hpdphy.
   rewrite Hpdphy in Hchildphy.
      unfold getMappedPagesAux in *;trivial.
      symmetry;trivial.
      now contradict Hfalse.   
  - assert(Hnotshared:  getMappedPages child s = getMappedPages child s').
  intros.
  apply getMappedPagesRemoveMMUPage with phyDescChild vaChild entry level;trivial.
  apply Hconfigdiff;trivial.
  apply childrenPartitionInPartitionList with (currentPartition s) ;
  trivial.
  intros;split;subst;trivial.
  apply childrenPartitionInPartitionList with (currentPartition s) ;
  trivial.
  rewrite <- Hnotshared.
  assert(Hmapped : In (pa entry) (getMappedPages phyDescChild s)).
  { apply inGetMappedPagesGetTableRoot with vaChild ptVaChildpd pdChildphy;trivial.
  intros;split;subst;trivial.
  unfold isEntryPage.
  rewrite Hlookup;trivial. }
  assert(Hiso: partitionsIsolation s) by trivial.
  unfold partitionsIsolation in Hiso.
  assert (Hdisjoint: disjoint (getUsedPages phyDescChild s) (getUsedPages child s)).
  apply Hiso with (currentPartition s);trivial. clear Hiso.
  unfold getUsedPages in Hdisjoint.
  unfold disjoint in Hdisjoint.
  generalize (Hdisjoint (pa entry));clear Hdisjoint;intros Hdis.
  assert(Hdis1: ~ In (pa entry) (getConfigPages child s ++ getMappedPages child s)).
  apply Hdis. clear Hdis.
  simpl.
  right.
  simpl.
  apply in_app_iff.
  right;trivial.
  intuition.
Qed.





















                 