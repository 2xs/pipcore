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
    This file contains required lemmas to prove the [writePhyEntry] invariant *)
Require Import Core.Internal Isolation Consistency WeakestPreconditions 
Invariants StateLib Model.Hardware Model.ADT Model.MAL 
DependentTypeLemmas Model.Lib InternalLemmas WriteAccessibleRec.
Require Import Coq.Logic.ProofIrrelevance Omega List. 

Lemma readPhysicalUpdateMappedPageData partition table idxroot page s idx u p e w r :
(* lookup table idx (memory s) beqPage beqIndex = None ->  *)
table <> partition -> 
StateLib.readPhysical partition idxroot
  (add table idx (PE {| read := r; write := w; exec := e; present := p; user := u; pa := page |}) 
     (memory s) beqPage beqIndex) = StateLib.readPhysical partition idxroot (memory s).
Proof.
intros.
cbn.
unfold StateLib.readPhysical.
cbn.
case_eq (beqPairs (table, idx) (partition, idxroot) beqPage beqIndex); intros Hpairs.
apply beqPairsTrue in Hpairs.
destruct Hpairs as (Htable & Hidx);subst.
(* rewrite H. trivial. *) now contradict H. 
apply beqPairsFalse in Hpairs.
   assert (lookup  partition idxroot (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  partition idxroot   (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. reflexivity.
Qed.

Lemma getPdUpdateMappedPageData partition table idx s page u p e w r: 
table <> partition ->
StateLib.getPd partition
  (add table idx (PE {| read := r; write := w; exec := e; present := p; user := u; pa := page |})
     (memory s) beqPage beqIndex) = StateLib.getPd partition (memory s).
Proof.
cbn.
unfold StateLib.getPd.
case_eq (StateLib.Index.succ PDidx);trivial.
intros.
apply readPhysicalUpdateMappedPageData; trivial.
Qed. 

Lemma getFstShadowUpdateMappedPageData partition table idx s page u p e w r: 
table <> partition ->
StateLib.getFstShadow partition
  (add table idx (PE {| read := r; write := w; exec := e; present := p; user := u; pa := page |})
     (memory s) beqPage beqIndex) = StateLib.getFstShadow partition (memory s).
Proof.
cbn.
unfold StateLib.getFstShadow.
case_eq (StateLib.Index.succ sh1idx);trivial.
intros.
apply readPhysicalUpdateMappedPageData; trivial.
Qed. 

Lemma getSndShadowUpdateMappedPageData partition table idx s page u p e w r: 
table <> partition ->
StateLib.getSndShadow partition
  (add table idx (PE {| read := r; write := w; exec := e; present := p; user := u; pa := page |})
     (memory s) beqPage beqIndex) = StateLib.getSndShadow partition (memory s).
Proof.
cbn.
unfold StateLib.getSndShadow.
case_eq (StateLib.Index.succ sh2idx);trivial.
intros.
apply readPhysicalUpdateMappedPageData; trivial.
Qed.

Lemma getTrdShadowUpdateMappedPageData partition table idx s page u p e w r: 
table <> partition ->
StateLib.getConfigTablesLinkedList partition
  (add table idx (PE {| read := r; write := w; exec := e; present := p; user := u; pa := page |})
     (memory s) beqPage beqIndex) = StateLib.getConfigTablesLinkedList partition (memory s).
Proof.
cbn.
unfold StateLib.getConfigTablesLinkedList.
case_eq (StateLib.Index.succ sh3idx );trivial.
intros.
apply readPhysicalUpdateMappedPageData; trivial.
Qed.

Lemma getPdsVAddrUpdateMappedPageData partition table idx l paValue s  u p e w r: 
getPdsVAddr partition l getAllVAddr
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := paValue |}) (memory s) beqPage
              beqIndex |} =
getPdsVAddr partition l getAllVAddr s.
Proof.
unfold getPdsVAddr.
revert partition l.
induction getAllVAddr; simpl;trivial. 
intros.

Admitted.

Lemma getIndirectionUpdateMappedPageData tableRoot table idx paValue nbL
 (curlevel : level) va stop  u p e w r  s: 

Some nbL = StateLib.getNbLevel ->
curlevel <= nbL -> 
 ~ In table (getIndirectionsAux tableRoot s (S stop)  ) -> 
 getIndirection tableRoot va curlevel stop
    {|
    currentPartition := currentPartition s;
    memory := add table idx
                (PE
                   {|
                   read := u;
                   write := p;
                   exec := e;
                   present := w;
                   user := r;
                   pa := paValue |}) (memory s) beqPage beqIndex |} =  
 getIndirection tableRoot va curlevel stop s.
Proof.
intros Hlevel Hcurlevel Hii.
revert Hlevel Hcurlevel Hii.
revert tableRoot table idx paValue nbL curlevel va.
induction stop; simpl; intros.
+ f_equal.
+ case_eq (StateLib.Level.eqb curlevel fstLevel); intros;
  f_equal.  
  set (memory' := add table idx
       (PE
          {|
           read := u;
           write := p;
           exec := e;
           present := w;
           user := r;
          pa := paValue |}) (memory s) beqPage beqIndex) in *.
  set(curidx := StateLib.getIndexOfAddr va curlevel) in *.
  assert (StateLib.readPhyEntry tableRoot curidx (memory s)
  = StateLib.readPhyEntry tableRoot curidx memory' ).
  { unfold memory'.
    clear memory'.
    unfold  StateLib.readPhyEntry.
    cbn. apply Classical_Prop.not_or_and in Hii.
    destruct Hii.
    assert (Hfalse : beqPairs (table, idx) (tableRoot, curidx) beqPage beqIndex = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup tableRoot curidx (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex 
              = lookup tableRoot curidx (memory s) beqPage beqIndex) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory. reflexivity. }
  rewrite <- H0.
  clear H0.
  case_eq (StateLib.readPhyEntry tableRoot curidx (memory s));
  intros; trivial.
  case_eq (defaultPage =? p0); intros; trivial.
  f_equal.
  case_eq (StateLib.Level.pred curlevel); intros; trivial.
  apply IHstop with nbL; trivial.
  unfold StateLib.Level.pred in H2.
  destruct ( gt_dec curlevel 0).
  inversion H2.
  simpl in *.
  destruct l.
  inversion H4.
  subst. omega.
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
  exists p0.
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
  symmetry. apply CIndexEq. rewrite <- Hcidx. assumption.
  simpl. subst. left. trivial.
  rewrite in_flat_map in H4.
  unfold not  in *.
  intros.
  contradict H4.
  exists p0.
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
  symmetry. apply CIndexEq. rewrite <- Hcidx. assumption.
  simpl. subst. right. assumption.
Qed.

Lemma getMappedPagesAuxUpdateMappedPageData pd table idx listVA paValue s nbL  u p e w r :
table <> defaultPage -> pd <> defaultPage ->
~ In table (getIndirectionsAux pd s nbLevel) ->
Some nbL = StateLib.getNbLevel -> 
getMappedPagesAux pd listVA
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := paValue |}) (memory s) beqPage
              beqIndex |} =
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
                (PE {| read := r; write := w; exec := e; present := p; user := u; pa := paValue |})
                (memory s) beqPage beqIndex |} = getIndirection pd a nbL (nbLevel - 1) s).
apply getIndirectionUpdateMappedPageData with nbL; auto.
assert(0<nbLevel) by apply nbLevelNotZero.
assert( (S (nbLevel - 1)) = nbLevel) by omega.
rewrite H0.
assumption.
subst.
rewrite Hind.
case_eq (getIndirection pd a nbL (nbLevel - 1) s); intros; trivial.
cbn.            
set(curidx := (StateLib.getIndexOfAddr a fstLevel)) in *.
assert(p0 <> table).
clear IHlistVA.
unfold not in *.
intros.
subst.
apply Hindirections.
apply getIndirectionInGetIndirections with a nbL (nbLevel -1); trivial.
apply nbLevelNotZero.
apply getNbLevelLe; trivial.
assert(Hpres : StateLib.readPresent p0 curidx
    (add table idx
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := p;
          user := u;
          pa := paValue |}) (memory s) beqPage beqIndex) = 
 StateLib.readPresent p0 curidx (memory s)).
 unfold StateLib.readPresent.
 cbn.
 assert (Hfalse : beqPairs (table, idx) (p0, curidx) beqPage beqIndex = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup p0 curidx (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex 
              = lookup p0 curidx (memory s) beqPage beqIndex) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory; reflexivity.
 rewrite Hpres; trivial.
 case_eq (StateLib.readPresent p0 curidx (memory s)); intros; trivial.
 case_eq b; intros; trivial.
 unfold StateLib.readPhyEntry.
 cbn.
 assert (Hfalse : beqPairs (table, idx) (p0, curidx) beqPage beqIndex = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup p0 curidx (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex 
              = lookup p0 curidx (memory s) beqPage beqIndex) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory; reflexivity.
Qed.

Lemma getMappedPagesUpdateMappedPageData partition (table : page) idx pValue level r w e p u s: 
partitionDescriptorEntry s -> 
(defaultPage =? table) = false -> 
Some level = StateLib.getNbLevel-> 
 In partition (getPartitions multiplexer s) -> 
(forall partition1 : page,
         In partition1 (getPartitions multiplexer s) ->
         partition1 = table \/ 
         In table (getConfigPagesAux partition1 s) -> False) -> 
getMappedPages partition
  {|
  currentPartition := currentPartition s; 
  memory := add table idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := pValue |}) (memory s) beqPage beqIndex |} =
getMappedPages partition s. 
Proof.
intros Hpde Hfalse Hlevel Hpartmult Hconfig. 
set(s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE {| read := r; write := w; exec := e; present := p; user := u; pa := pValue |})
              (memory s) beqPage beqIndex |}) in *.
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
  apply Hpde  with partition PDidx in Hpartmult; clear Hpde.
  destruct Hpartmult as (_ & _ & entrypd & Hpp & Hnotnul).
  rewrite Hpdchild1 in Hpd.
  clear Hpdchild1.
  assert (Heq : entrypd = p0).
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

Lemma getAccessibleMappedPagesAuxUpdateMappedPageData pd table idx listVA paValue s nbL  
u p e w r :
table <> defaultPage -> pd <> defaultPage ->
~ In table (getIndirectionsAux pd s nbLevel) ->
Some nbL = StateLib.getNbLevel -> 
getAccessibleMappedPagesAux pd listVA
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := paValue |}) (memory s) beqPage
              beqIndex |} =
getAccessibleMappedPagesAux pd listVA s.
Proof.
intros Htablenotnull Hpdnotnull Hindirections HnbL.
unfold getAccessibleMappedPagesAux.
f_equal.
unfold getAccessibleMappedPagesOption.
revert pd Hindirections Htablenotnull Hpdnotnull.
induction listVA;simpl;intros;trivial.
rewrite IHlistVA; trivial.
f_equal.
unfold getAccessibleMappedPage.
rewrite <- HnbL.
assert(Hind : getIndirection pd a nbL (nbLevel - 1)
    {|
    currentPartition := currentPartition s;
    memory := add table idx
                (PE {| read := r; write := w; exec := e; present := p; user := u; pa := paValue |})
                (memory s) beqPage beqIndex |} = getIndirection pd a nbL (nbLevel - 1) s).
apply getIndirectionUpdateMappedPageData with nbL; auto.
assert(0<nbLevel) by apply nbLevelNotZero.
assert( (S (nbLevel - 1)) = nbLevel) by omega.
rewrite H0.
assumption.
subst.
rewrite Hind.
case_eq (getIndirection pd a nbL (nbLevel - 1) s); intros; trivial.
cbn.            
set(curidx := (StateLib.getIndexOfAddr a fstLevel)) in *.
assert(p0 <> table).
clear IHlistVA.
unfold not in *.
intros.
subst.
apply Hindirections.
apply getIndirectionInGetIndirections with a nbL (nbLevel -1); trivial.
apply nbLevelNotZero.
apply getNbLevelLe; trivial.
assert(Hpres : StateLib.readPresent p0 curidx
    (add table idx
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := p;
          user := u;
          pa := paValue |}) (memory s) beqPage beqIndex) = 
 StateLib.readPresent p0 curidx (memory s)).
 unfold StateLib.readPresent.
 cbn.
 assert (Hfalse : beqPairs (table, idx) (p0, curidx) beqPage beqIndex = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup p0 curidx (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex 
              = lookup p0 curidx (memory s) beqPage beqIndex) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory; reflexivity.
 rewrite Hpres; trivial.
 case_eq (StateLib.readPresent p0 curidx (memory s)); intros; trivial.
 case_eq b; intros; trivial.
assert(Haccess : StateLib.readAccessible p0 curidx
    (add table idx
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := p;
          user := u;
          pa := paValue |}) (memory s) beqPage beqIndex) = 
 StateLib.readAccessible p0 curidx (memory s)).
 unfold StateLib.readAccessible.
 cbn.
 assert (Hfalse : beqPairs (table, idx) (p0, curidx) beqPage beqIndex = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup p0 curidx (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex 
              = lookup p0 curidx (memory s) beqPage beqIndex) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory; reflexivity.
 rewrite Haccess; trivial.
 case_eq (StateLib.readAccessible p0 curidx (memory s)); intros; trivial.
 case_eq b0; intros; trivial. 
 
 unfold StateLib.readPhyEntry.
 cbn.
 assert (Hfalse : beqPairs (table, idx) (p0, curidx) beqPage beqIndex = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup p0 curidx (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex 
              = lookup p0 curidx (memory s) beqPage beqIndex) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory; reflexivity.
Qed.

Lemma getAccessibleMappedPagesUpdateMappedPageData partition (table : page) 
idx pValue level r w e p u s: 
partitionDescriptorEntry s -> 
(defaultPage =? table) = false -> 
Some level = StateLib.getNbLevel-> 
 In partition (getPartitions multiplexer s) -> 
(forall partition1 : page,
         In partition1 (getPartitions multiplexer s) ->
         partition1 = table \/ 
         In table (getConfigPagesAux partition1 s) -> False) -> 
getAccessibleMappedPages partition
  {|
  currentPartition := currentPartition s; 
  memory := add table idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := pValue |}) (memory s) beqPage beqIndex |} =
getAccessibleMappedPages partition s. 
Proof.
intros Hpde Hfalse Hlevel Hpartmult Hconfig. 
set(s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE {| read := r; write := w; exec := e; present := p; user := u; pa := pValue |})
              (memory s) beqPage beqIndex |}) in *.
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
apply getAccessibleMappedPagesAuxUpdateMappedPageData with level; trivial.
{ 
 apply beq_nat_false in Hfalse.
 unfold not; intros.
 apply Hfalse.
 subst;trivial. }
{ unfold consistency in *.
 unfold partitionDescriptorEntry in Hpde.
  apply Hpde  with partition PDidx in Hpartmult; clear Hpde.
  destruct Hpartmult as (_ & _ & entrypd & Hpp & Hnotnul).
  rewrite Hpdchild1 in Hpd.
  clear Hpdchild1.
  assert (Heq : entrypd = p0).
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

Lemma getChildrenUpdateMappedPageData partition table idx s page r w e p u (* nbL *) (* pd *) :
table <> defaultPage -> 
(* pd <> defaultPage ->  *)
(* Some pd = StateLib.getPd partition (memory s) ->  *)
In partition (getPartitions multiplexer s) -> 
partitionDescriptorEntry s ->
~ In table (getConfigPages partition s) -> 
(* Some nbL = StateLib.getNbLevel ->  *)
 table<>partition ->
getChildren partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE {| read := r; write := w; exec := e; present := p; user := u; pa := page |}) 
              (memory s) beqPage beqIndex |} = getChildren partition s.
Proof.
intros  Htablenotnull Hgetparts Hpde (* Hpdnotnull HgetPd *) Hind (* HnbLevel *) Hdiff.
unfold getChildren.
case_eq (StateLib.getNbLevel);intros; trivial.
assert ( StateLib.getPd partition
    (memory
       {|
       currentPartition := currentPartition s;
       memory := add table idx
                   (PE {| read := r; write := w; exec := e; present := p; user := u; pa := page |})
                   (memory s) beqPage beqIndex |}) = StateLib.getPd partition (memory s)) as Hpd.
apply getPdUpdateMappedPageData; trivial.
rewrite Hpd; clear Hpd.
f_equal.
case_eq (StateLib.getPd partition (memory s));intros; trivial.
assert(getPdsVAddr partition l getAllVAddr
     {|
     currentPartition := currentPartition s;
     memory := add table idx
                 (PE {| read := r; write := w; exec := e; present := p; user := u; pa := page |})
                 (memory s) beqPage beqIndex |} = getPdsVAddr partition l getAllVAddr s) as Hvaddrpd.
apply getPdsVAddrUpdateMappedPageData.
rewrite Hvaddrpd; clear Hvaddrpd.
apply getMappedPagesAuxUpdateMappedPageData with l; trivial.
unfold partitionDescriptorEntry in *.
apply Hpde with partition PDidx in Hgetparts;clear Hpde.
destruct Hgetparts as (Hpdidx & Hisva & Hpd  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ PDidx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex);auto.
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

Lemma getPartitionAuxUpdateMappedPageData s pgValue table idx r w e u p : 
forall partition, 
In partition (getPartitions multiplexer s) ->
(forall subpartition, In subpartition  (getPartitions multiplexer s ) ->
~ In table (getConfigPages subpartition s)) -> 
table <> defaultPage ->
partitionDescriptorEntry s ->
getPartitionAux partition {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE {| read := r; write := w; exec := e; present := p; user := u; pa := pgValue |})
              (memory s) beqPage beqIndex |} (nbPage+1) =
getPartitionAux partition s (nbPage+1).
Proof.
intros partition HgetParts Hnotconfig Htablenotnull Hpde.
revert partition HgetParts Hnotconfig .
induction (nbPage + 1).
simpl; intuition.
simpl; intros.
f_equal.
set(s':=  {|
     currentPartition := currentPartition s;
     memory := add table idx
                 (PE {| read := r; write := w; exec := e; present := p; user := u; pa := pgValue |})
                 (memory s) beqPage beqIndex |}) in *.
                 unfold s'.
rewrite getChildrenUpdateMappedPageData; auto.
fold s'.
+ assert(forall child, In child (getChildren partition s) -> 
                       In child (getPartitions  multiplexer s)).
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

Lemma getPartitionsUpdateMappedPageData partition table idx s pgValue r w e p u:
In partition (getPartitions multiplexer s) ->
(forall subpartition, In subpartition  (getPartitions multiplexer s ) ->
~ In table (getConfigPages subpartition s)) -> 
table <> defaultPage ->
partitionDescriptorEntry s ->
getPartitions partition
  {| currentPartition := currentPartition s;
     memory := add table idx (PE {| read := r; write := w; exec := e; 
     present := p; user := u; pa := pgValue |}) (memory s) beqPage beqIndex |} = 
getPartitions partition s.
Proof.
intros.
unfold getPartitions.
apply getPartitionAuxUpdateMappedPageData; trivial.
Qed.

Lemma getTablePagesUpdateMappedPageData table1 table2 idx paValue size s: 
table2 <> table1 -> 
getTablePages table1 size
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := paValue |}) (memory s) beqPage beqIndex |} =
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
                  (PE
                     {|
                     read := false;
                     write := false;
                     exec := false;
                     present := false;
                     user := false;
                     pa := paValue |}) (memory s) beqPage beqIndex |}) in *.
assert (Hfalse : beqPairs (table2, idx) (table1, CIndex size) beqPage beqIndex = false).
apply beqPairsFalse; left;trivial.
rewrite Hfalse.
  assert (lookup table1 (CIndex size) (removeDup table2 idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  table1 (CIndex size) (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. subst.  intuition. }
  rewrite  Hmemory; clear Hmemory.
  destruct (lookup table1 (CIndex size) (memory s) beqPage beqIndex); [
  destruct v | 
  apply IHsize] ; try apply IHsize.
  destruct (pa p=? defaultPage);
  [apply IHsize |
  f_equal;
  apply IHsize].
Qed.

Lemma getIndirectionsAuxUpdateMappedPageData partition table idx paValue s nbL:
~ In table (getIndirectionsAux partition s nbL) -> 
getIndirectionsAux partition
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE {| read := false; write := false; exec := false; present := false; user := false; pa := paValue |})
              (memory s) beqPage beqIndex |} nbL = getIndirectionsAux partition s nbL.
Proof. 
intros Hind.
revert table partition Hind.
induction nbL; [
simpl; trivial |].
intros.
set (s' :=   {|
currentPartition := currentPartition s;
memory := add table idx
       (PE
        {| read := false;
           write := false;
           exec := false;
           present := false;
           user := false;
           pa := paValue |}) (memory s) beqPage beqIndex |}) in *.
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

Lemma getTrdShadowsUpdateMappedPageData sh3 table idx paValue s :
~ In table (getTrdShadows sh3 s nbPage) -> 
getTrdShadows sh3
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := paValue |}) (memory s) beqPage beqIndex |} nbPage = 
getTrdShadows sh3 s nbPage.
Proof. 
revert sh3.
induction nbPage;trivial.
intros. simpl in *.
 set (s' :=    {|
        currentPartition := currentPartition s;
        memory := add table idx
                    (PE
                       {|
                       read := false;
                       write := false;
                       exec := false;
                       present := false;
                       user := false;
                       pa := paValue |}) (memory s) beqPage beqIndex |}) in *.
destruct (StateLib.getMaxIndex);trivial.
assert(sh3 <> table).
{ case_eq ( StateLib.readPhyEntry sh3 i (memory s)); intros;
  rewrite H0 in H ; [
  case_eq (p =? defaultPage); intros; rewrite H1 in H |];
   apply Classical_Prop.not_or_and in H;
destruct H as (H & _); assumption. }
assert(Hread :   StateLib.readPhyEntry sh3 i
    (add table idx
       (PE {| read := false; write := false; exec := false; 
       present := false; user := false; pa := paValue |})
       (memory s) beqPage beqIndex) = StateLib.readPhyEntry sh3 i (memory s)).
{ unfold StateLib.readPhyEntry.
  cbn.
  assert (Hfalse : beqPairs (table, idx) (sh3, i) beqPage beqIndex = false).
    apply beqPairsFalse; intuition.
    rewrite Hfalse.
    assert ( lookup sh3 i (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex 
              = lookup sh3 i (memory s) beqPage beqIndex) as Hmemory.
      { apply removeDupIdentity. subst.  intuition. }
    rewrite  Hmemory; clear Hmemory. reflexivity. }  
rewrite Hread.
case_eq ( StateLib.readPhyEntry sh3 i (memory s) ); intros; trivial.
case_eq ( p =? defaultPage); intros; trivial.
f_equal.
apply IHn.
rewrite H1 in H; trivial.
rewrite H2 in H.
simpl in H.  
apply Classical_Prop.not_or_and in H.
destruct H as (H & Hneed); assumption.
Qed.

Lemma getConfigPagesUpdateMappedPageData partition table idx paValue s : 
~ In table (getConfigPages partition s) -> 
getConfigPages partition
{| currentPartition := currentPartition s;
   memory := Lib.add  table idx
            (PE
               {| read := false; write := false; exec := false; present := false; user := false; pa := paValue |})
            (memory s) beqPage beqIndex |} = getConfigPages partition s.
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
case_eq (getFstShadow partition (memory s)); trivial.
rewrite getSndShadowUpdateMappedPageData in *;trivial.
case_eq (getSndShadow partition (memory s)); trivial.
rewrite getTrdShadowUpdateMappedPageData in *;trivial.
case_eq (getConfigTablesLinkedList partition (memory s)); trivial.
f_equal.
unfold getIndirections.
intros sh3 Hsh3 sh2 Hsh2 sh1 Hsh1 pd Hpd.
rewrite Hpd in *.
rewrite Hsh1 in *.
rewrite Hsh2 in *.
rewrite Hsh3 in *.
try repeat rewrite in_app_iff in Hconfig.
apply Classical_Prop.not_or_and in Hconfig;
destruct Hconfig; simpl in H; apply Classical_Prop.not_or_and in H;
 destruct H as (_ & Hconfigpd).
apply Classical_Prop.not_or_and in H0;
destruct H0; simpl in H; apply Classical_Prop.not_or_and in H;
 destruct H as (_ & Hconfigsh1).
apply Classical_Prop.not_or_and in H0;
destruct H0; simpl in H; apply Classical_Prop.not_or_and in H;
 destruct H as (_ & Hconfigsh2).
 simpl in H0; apply Classical_Prop.not_or_and in H0;
 destruct H0 as (_ & Hconfigsh3).
 unfold getIndirections in *. 
try repeat rewrite getIndirectionsAuxUpdateMappedPageData; f_equal; trivial.
do 6 f_equal.
apply getTrdShadowsUpdateMappedPageData; trivial.
Qed.
Lemma getConfigPagesAuxUpdateMappedPageData partition table idx paValue s : 
~ In table (getConfigPages partition s) -> 
getConfigPagesAux partition
{| currentPartition := currentPartition s;
   memory := Lib.add  table idx
            (PE
               {| read := false; write := false; exec := false; present := false; user := false; pa := paValue |})
            (memory s) beqPage beqIndex |} = getConfigPagesAux partition s.
Proof.
intros.
assert(getConfigPages partition {| currentPartition := currentPartition s;
   memory := Lib.add  table idx
            (PE
               {| read := false; write := false; exec := false; present := false; user := false; pa := paValue |})
            (memory s) beqPage beqIndex |} = getConfigPages partition s).
            apply getConfigPagesUpdateMappedPageData; trivial.
unfold getConfigPages in H0.
inversion H0. reflexivity.
Qed.

Lemma isVAUpdateMappedPageData partition table idxroot idx pValue r w e p u s: 
(forall partition : page,
          In partition (getPartitions multiplexer s) ->
          partition = table \/ In table (getConfigPagesAux partition s) ->
          False )->
(defaultPage =? table) = false ->
In partition (getPartitions multiplexer s) ->
isVA partition idxroot s -> 
isVA partition idxroot
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE {| read := r; write := w; exec := e; present := p; user := u; pa := pValue |})
              (memory s) beqPage beqIndex |}.
Proof.
intros Hconfig Hfalse Hpde Hva.
unfold isVA in *.
cbn.
assert (Hnoteq : beqPairs (table, idx) (partition, idxroot) beqPage beqIndex = false).
{ apply beqPairsFalse; intuition.
  left.
  generalize (Hconfig partition Hpde); clear Hconfig; intros Hconfig.
  apply Classical_Prop.not_or_and in Hconfig.
  destruct Hconfig.
  unfold not in *.
  intros Hf. rewrite Hf in H.
  now contradict H. }
rewrite Hnoteq.
assert ( lookup partition idxroot (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex 
              = lookup partition idxroot (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. left. 
  generalize (Hconfig partition Hpde); clear Hconfig; intros Hconfig.
  apply Classical_Prop.not_or_and in Hconfig.
  destruct Hconfig. assumption. }
rewrite  Hmemory; clear Hmemory. assumption.
Qed.

Lemma nextEntryIsPPUpdateMappedPageData partition table idxroot root idx pValue
r w e p u s: 
(forall partition : page,
          In partition (getPartitions multiplexer s) ->
          partition = table \/ In table (getConfigPagesAux partition s) ->
          False )->
(defaultPage =? table) = false ->
In partition (getPartitions multiplexer s) ->
nextEntryIsPP partition idxroot root s <-> 
nextEntryIsPP partition idxroot root
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE {| read := r; write := w; exec := e; present := p; user := u; pa := pValue |})
              (memory s) beqPage beqIndex |}.
Proof.
intros Hconfig Hfalse Hpde .
split.
+ unfold nextEntryIsPP in *.
  destruct (StateLib.Index.succ idxroot); trivial.
  cbn.
  assert (Hnoteq : beqPairs (table, idx) (partition, i) beqPage beqIndex = false).
  { apply beqPairsFalse; intuition.
    left.
    generalize (Hconfig partition Hpde); clear Hconfig; intros Hconfig.
    apply Classical_Prop.not_or_and in Hconfig.
    destruct Hconfig.
    unfold not in *.
    intros Hf. rewrite Hf in H.
    now contradict H. }
  rewrite Hnoteq.
  assert ( lookup partition i (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex 
                = lookup partition i (memory s) beqPage beqIndex) as Hmemory.
  { apply removeDupIdentity. left. 
    generalize (Hconfig partition Hpde); clear Hconfig; intros Hconfig.
    apply Classical_Prop.not_or_and in Hconfig.
    destruct Hconfig. assumption. }
  rewrite  Hmemory; clear Hmemory. trivial.
+ unfold nextEntryIsPP in *.
  destruct (StateLib.Index.succ idxroot); trivial.
  cbn in *.
  assert (Hnoteq : beqPairs (table, idx) (partition, i) beqPage beqIndex = false).
  { apply beqPairsFalse; intuition.
    left.
    generalize (Hconfig partition Hpde); clear Hconfig; intros Hconfig.
    apply Classical_Prop.not_or_and in Hconfig.
    destruct Hconfig.
    unfold not in *.
    intros Hf. rewrite Hf in H.
    now contradict H. }
  rewrite Hnoteq .
  assert ( lookup partition i (removeDup table idx (memory s) beqPage beqIndex) beqPage beqIndex 
                = lookup partition i (memory s) beqPage beqIndex) as Hmemory.
  { apply removeDupIdentity. left. 
    generalize (Hconfig partition Hpde); clear Hconfig; intros Hconfig.
    apply Classical_Prop.not_or_and in Hconfig.
    destruct Hconfig. assumption. }
  rewrite  Hmemory in *; clear Hmemory. trivial.
Qed.

Lemma partitionDescriptorEntryUpdateMappedPageData (table : page) idx pValue r w e p u s: 
(forall partition : page,
          In partition (getPartitions multiplexer s) ->
          partition = table \/ In table (getConfigPagesAux partition s) ->
          False )->
(defaultPage =? table) = false -> 
partitionDescriptorEntry s -> 
partitionDescriptorEntry
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := pValue |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hconfig Hfalse Hpde.
set (s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := pValue |}) (memory s) beqPage beqIndex |}) in *.
assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
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
generalize (Hpde partition H idxroot  H0);
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

Lemma isPEUpdateUpdateMappedPageData table1 table2 idx1 idx2 pValue r w e p u s :
table2 <> table1 -> 
isPE table1 idx1 s -> 
isPE table1 idx1
{|
currentPartition := currentPartition s;
memory := add table2 idx2
          (PE {| read := r; write := w; exec := e; present := p; user := u; pa := pValue |})
          (memory s) beqPage beqIndex |}.
Proof.
intros.
unfold isPE in *.
cbn.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex)
          beqPage beqIndex = lookup  table1 idx1 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. assumption.
Qed.

Lemma isVEUpdateMappedPageData table1 table2 idx1 idx2 pValue r w e p u s :
table2 <> table1 -> 
isVE table1 idx1 s -> 
isVE table1 idx1
{|
currentPartition := currentPartition s;
memory := add table2 idx2
          (PE {| read := r; write := w; exec := e; present := p; user := u; pa := pValue |})
          (memory s) beqPage beqIndex |}.
Proof.
intros.
unfold isVE in *.
cbn.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex)
          beqPage beqIndex = lookup  table1 idx1 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. assumption.
Qed.

Lemma isVAUpdateMappedPageData' table1 table2 idx1 idx2 pValue r w e p u s :
table2 <> table1 -> 
isVA table1 idx1 s -> 
isVA table1 idx1
{|
currentPartition := currentPartition s;
memory := add table2 idx2
          (PE {| read := r; write := w; exec := e; present := p; user := u; pa := pValue |})
          (memory s) beqPage beqIndex |}.
Proof.
intros.
unfold isVA in *.
cbn.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex)
          beqPage beqIndex = lookup  table1 idx1 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. assumption.
Qed.

Lemma dataStructurePdSh1Sh2asRootUpdateMappedPageData idxroot table idx pValue 
r w e p u s :
(idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx) -> 
(forall partition : page,
          In partition (getPartitions multiplexer s) ->
          partition = table \/ In table (getConfigPagesAux partition s) ->
          False )->
(defaultPage =? table) = false -> 
 partitionDescriptorEntry s -> 
dataStructurePdSh1Sh2asRoot idxroot s -> 
dataStructurePdSh1Sh2asRoot idxroot
  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := pValue  |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hor Hconfig Hfalse Hpde Hds.
set (s' :=  {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := pValue |}) (memory s) beqPage beqIndex |}) in *.
assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
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
  inversion HnbL. omega.
  assert(0 < nbLevel) by apply nbLevelNotZero. 
  omega. }
assert(Htable :stop <= (nbLevel -1) -> ~ In table (getIndirectionsAux entrypp s (S stop))).
intros.
{ assert (Hstop : stop < (nbLevel -1) \/ stop = (nbLevel -1) ) by omega.
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
assert(Hsnbl :  (S (nbLevel - 1)) = nbLevel) by omega.
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
{ assert (Hstop3 : stop < (nbLevel -1) \/ stop = (nbLevel -1) \/ stop > (nbLevel -1)) by omega.
  destruct Hstop3 as [Hlt | [ Heq | Hgt]].
  + apply getIndirectionUpdateMappedPageData with nbL;
    trivial. apply Htable. omega.
  + subst.
    apply getIndirectionUpdateMappedPageData with nbL ;trivial.
    apply Htable. omega.
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
      simpl in *. omega.
      assert(0 < nbLevel) by apply nbLevelNotZero. 
      omega. }
    rewrite Hgetind.
    symmetry.
    apply getIndirectionStopLevelGT with nbL; trivial.
    apply getNbLevelLe in HnbL.
    unfold CLevel in HnbL.
    case_eq (lt_dec (nbLevel - 1) nbLevel); intros;
    rewrite H0 in *.
    simpl in *.
    destruct nbL.
    simpl in *. omega.
    assert(0 < nbLevel) by apply nbLevelNotZero. 
    omega.
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
         entry <> defaultPage).
  apply Hpde; trivial.
  intuition.
  destruct H1 as ( entry & Hentry & Hnotnul).
  unfold nextEntryIsPP in * .
  destruct (StateLib.Index.succ idxroot ); 
  [| now contradict Hentry].
  destruct (lookup partition i (memory s) beqPage beqIndex);
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
r w e p u paValue s:
(forall partition0 : page,
In partition0 (getPartitions multiplexer s) ->
partition0 = table2 \/ In table2 (getConfigPagesAux partition0 s) -> False) -> 
(defaultPage =? table2) = false -> 
In partition (getPartitions multiplexer s) -> 
partitionDescriptorEntry s -> 
getTableAddrRoot table1 idxroot partition va s -> 
getTableAddrRoot table1 idxroot partition va
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := paValue |}) (memory s) beqPage beqIndex |}.
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
      omega. }
rewrite Hind.
apply getIndirectionStopLevelGT with nbL; trivial.
omega.
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
omega.
assert (0 < nbLevel) by apply nbLevelNotZero.
omega.
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
flag r w e p u paValue s: 
table2 <> table1 -> 
entryPresentFlag table1 idx1 flag s -> 
entryPresentFlag table1 idx1 flag
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := paValue |}) (memory s) beqPage beqIndex |}.
Proof.
intros.
unfold entryPresentFlag in *.
cbn.

assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex)
          beqPage beqIndex = lookup  table1 idx1 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. assumption.
Qed.

Lemma entryUserFlagUpdateMappedPageData table1 table2 idx1 idx2 
flag r w e p u paValue s: 
table2 <> table1 -> 
entryUserFlag table1 idx1 flag s -> 
entryUserFlag table1 idx1 flag
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := paValue |}) (memory s) beqPage beqIndex |}.
Proof.
intros.
unfold entryUserFlag in *.
cbn.

assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex)
          beqPage beqIndex = lookup  table1 idx1 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. assumption.
Qed.

Lemma isEntryVAUpdateMappedPageData table1 table2 idx1 idx2 va paValue 
r w e p u s :
table2 <> table1 -> 
isEntryVA table1 idx1 va s ->
isEntryVA table1 idx1 va
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := paValue |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hentryva.
unfold isEntryVA in *.
cbn.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex)
          beqPage beqIndex = lookup  table1 idx1 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. trivial.
Qed.

Lemma isEntryPageUpdateMappedPageData table1 table2 idx1 idx2 paValue phytable1
r w e p u s :
table2 <> table1 -> 
isEntryPage table1 idx1 phytable1 s ->
isEntryPage table1 idx1 phytable1
  {|
  currentPartition := currentPartition s;
  memory := add table2 idx2
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := paValue |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hentryva.
unfold isEntryPage in *.
cbn.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex)
          beqPage beqIndex = lookup  table1 idx1 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. trivial.
Qed.

Lemma readPhyEntryUpdateMappedPageData table1 table2 idx1 idx2 paValue 
r w e p u s :
table2 <> table1 -> 
StateLib.readPhyEntry table1 idx1 (memory s) =
StateLib.readPhyEntry table1 idx1 
 ( add table2 idx2
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := p;
                 user := u;
                 pa := paValue |}) (memory s) beqPage beqIndex ).
Proof.
intros Hnoteq.
unfold StateLib.readPhyEntry in *.
cbn.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) beqPage beqIndex = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex)
          beqPage beqIndex = lookup  table1 idx1 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. trivial.
Qed.

Lemma readMappedPageDataUpdateMappedPageData partition pt1 pt2 phy1 phy2 
idxVa1 idxVa2 va1 va2  level s  : 
In partition (getPartitions multiplexer s) -> 
Some level = StateLib.getNbLevel -> 
partitionDescriptorEntry s -> 
noDupMappedPagesList s ->
isEntryPage pt1 idxVa1 phy1 s -> 
isEntryPage pt2 idxVa2 phy2 s ->
StateLib.getIndexOfAddr va1 fstLevel = idxVa1 -> 
StateLib.getIndexOfAddr va2 fstLevel = idxVa2 -> 
(forall idx : index,
 StateLib.getIndexOfAddr va1 fstLevel = idx ->
 isPE pt1 idx s /\ 
 getTableAddrRoot pt1 PDidx partition va1 s) -> 
(forall idx : index,
 StateLib.getIndexOfAddr va2 fstLevel = idx ->
 isPE pt2 idx s /\ 
 getTableAddrRoot pt2 PDidx partition va2 s) ->  
false = checkVAddrsEqualityWOOffset nbLevel va1 va2 level -> 
entryPresentFlag pt1 idxVa1 true s -> 
entryPresentFlag pt2 idxVa2 true s -> 
phy1 <> phy2.
Proof.
intros Hmult Hlevel Hpde Hnodup Hep1 Hep2 Hidxva1 Hidxva2 Hget1 Hget2 Hvas
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
assert(PDidx < tableSize - 1 /\
       isVA partition PDidx s /\ 
       (exists entry : page, nextEntryIsPP partition PDidx entry s /\ 
       entry <> defaultPage)).
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
assert(Hphy2 : getMappedPage pd s va2 = Some phy2).
{ unfold getMappedPage.
  rewrite <- HnbL1.
assert(Hgetlastind2 :getIndirection pd va2 nbL1 (nbLevel - 1) s = Some pt2).
  apply getIndirectionStopLevelGT2 with (nbL1 + 1); trivial.
  omega.
  apply getNbLevelEq in HnbL1.
  rewrite HnbL1.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel); intros.
  simpl; trivial.
  assert(0 < nbLevel) by apply nbLevelNotZero.
  omega.
  rewrite Hgetlastind2.
  unfold entryPresentFlag in Hpresent2.
  unfold StateLib.readPresent.
  subst.
  destruct (lookup pt2 (StateLib.getIndexOfAddr va2 fstLevel)
             (memory s) beqPage beqIndex); try now contradict Hpresent2.
  destruct v; try now contradict Hpresent2.
  destruct (present p); try now contradict Hpresent2.
  unfold isEntryPage in Hep2.
  unfold StateLib.readPhyEntry.
  destruct(lookup pt2 
  (StateLib.getIndexOfAddr va2 fstLevel) (memory s) beqPage beqIndex);
  try now contradict Hpe2.
  destruct v; try now contradict Hpe2.
  subst. trivial. }
assert(Hphy1 :getMappedPage pd s va1 = Some phy1).
{ 
  unfold getMappedPage.
  rewrite <- HnbL1.
  assert(Hgetlastind1 :getIndirection pd va1 nbL1 (nbLevel - 1) s = Some pt1).
  apply getIndirectionStopLevelGT2 with (nbL1 + 1); trivial.
  omega.
  apply getNbLevelEq in HnbL1.
  rewrite HnbL1.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel); intros.
  simpl; trivial.
  assert(0 < nbLevel) by apply nbLevelNotZero.
  omega.
  rewrite Hgetlastind1.
  unfold entryPresentFlag in Hpresent1.
  unfold StateLib.readPresent.
  subst.
  destruct (lookup pt1 (StateLib.getIndexOfAddr va1 fstLevel)
             (memory s) beqPage beqIndex); try now contradict Hpresent1.
  destruct v; try now contradict Hpresent1.
  destruct (present p); try now contradict Hpresent1.
  unfold isEntryPage in Hep1.
  unfold StateLib.readPhyEntry.
  destruct(lookup pt1 
  (StateLib.getIndexOfAddr va1 fstLevel) (memory s) beqPage beqIndex);
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
  exists  va1.
  split; [ | apply AllVAddrAll].
  unfold getMappedPage.
  rewrite <- HnbL1.
  assert(Hgetlastind1 :getIndirection pd va1 nbL1 (nbLevel - 1) s = Some pt1).
  apply getIndirectionStopLevelGT2 with (nbL1 + 1); trivial.
  omega.
  apply getNbLevelEq in HnbL1.
  rewrite HnbL1.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel); intros.
  simpl; trivial.
  assert(0 < nbLevel) by apply nbLevelNotZero.
  omega.
  rewrite Hgetlastind1.
  unfold entryPresentFlag in Hpresent1.
  unfold StateLib.readPresent.
  subst.
  destruct (lookup pt1 (StateLib.getIndexOfAddr va1 fstLevel)
             (memory s) beqPage beqIndex); try now contradict Hpresent1.
  destruct v; try now contradict Hpresent1.
  destruct (present p); try now contradict Hpresent1.
  unfold isEntryPage in Hep1.
  unfold StateLib.readPhyEntry.
  destruct(lookup pt1 
  (StateLib.getIndexOfAddr va1 fstLevel) (memory s) beqPage beqIndex);
  try now contradict Hpe1.
  destruct v; try now contradict Hpe1.
  subst. trivial. }
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
  apply  twoMappedPagesAreDifferent with va1 va2 pd s; trivial; try apply AllVAddrAll.
  apply checkVAddrsEqualityWOOffsetEqFalse with level level;trivial.
Qed.


    
Lemma propagatedPropertiesUpdateMappedPageData curidx nullP table pdChild currentPart 
currentPD level ptRefChild descChild idxRefChild presentRefChild ptPDChild
idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 
idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList presentConfigPagesList 
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1 
derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList 
phyDescChild s :

propagatedProperties pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2
presentSh2 ptConfigPagesList idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1
derivedRefChild ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child
childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
phyDescChild s  -> 

  (forall partition : page,
  In partition (getPartitions multiplexer s) ->
  partition = table \/ In table (getConfigPagesAux partition s) -> False) -> 
  (defaultPage =? table) = false -> 
   propagatedProperties pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2
  presentSh2 ptConfigPagesList idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1
  derivedRefChild ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child
  childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
  phyDescChild   {|
                    currentPartition := currentPartition s;
                    memory := add table curidx
                              (PE
                                 {|
                                 read := false;
                                 write := false;
                                 exec := false;
                                 present := false;
                                 user := false;
                                 pa := nullP |}) (memory s) beqPage beqIndex |}.
Proof.
set (s' := {|
  currentPartition := currentPartition s;
  memory := add table curidx
              (PE
                 {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 user := false;
                 pa := nullP |}) (memory s) beqPage beqIndex |}).
   unfold propagatedProperties in *.
   split.
(** partitionsIsolation **)
   assert (Hiso : partitionsIsolation s) by intuition.
   { intuition.
     unfold partitionsIsolation in *.
     intros.
     assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
     { unfold s'.
       apply getPartitionsUpdateMappedPageData ; trivial.
       + unfold getPartitions.
         destruct nbPage;simpl;left;trivial.
       + assert(Hfalse : (defaultPage =? table) = false) by trivial.
         apply beq_nat_false in Hfalse.
         unfold not; intros.
         apply Hfalse.
         subst;trivial.
       + unfold consistency in *. intuition. }
     rewrite Hpartions in *.
     unfold getUsedPages.
     assert (Hchild1 : In child1 (getChildren parent s')) by trivial.
     assert (Hchild2 : In child2 (getChildren parent s')) by trivial.
     assert (Hchild1mult : In child1 (getPartitions multiplexer s)).
     { apply childrenPartitionInPartitionList with parent; trivial.
       unfold s' in Hchild1, Hchild2.
       rewrite getChildrenUpdateMappedPageData in Hchild1; fold s'; trivial.
       assert(Hfalse : (defaultPage =? table) = false) by trivial.
       apply beq_nat_false in Hfalse.
      unfold not; intros.
      apply Hfalse.
      subst;trivial.
      unfold consistency in *. intuition.
      assert(Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False) by trivial.
      unfold getConfigPages.
      simpl.
      unfold not.
      apply Hconfig; trivial.
      assert(Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False) by trivial.
      assert(Hparent : In parent (getPartitions multiplexer s)); trivial.
      generalize (Hconfig parent Hparent); clear Hconfig; intros Hconfig. unfold not.
      intros. apply Hconfig.
      subst.
      left; trivial. }
     assert (Hchild2mult : In child2 (getPartitions multiplexer s)).
     { apply childrenPartitionInPartitionList with parent; trivial.
       unfold s' in Hchild1, Hchild2.
       rewrite getChildrenUpdateMappedPageData in Hchild2; fold s'; trivial.
       assert(Hfalse : (defaultPage =? table) = false) by trivial.
       apply beq_nat_false in Hfalse.
       unfold not; intros.
       apply Hfalse.
       subst;trivial.
      unfold consistency in *. intuition.
      assert(Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False) by trivial.
      unfold getConfigPages.
      simpl.
      unfold not.
      apply Hconfig; trivial.
      assert(Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False) by trivial.
      assert(Hparent : In parent (getPartitions multiplexer s)); trivial.
      generalize (Hconfig parent Hparent); clear Hconfig; intros Hconfig. unfold not.
      intros. apply Hconfig.
      subst.
      left; trivial. }    
     assert (Hmapped : getMappedPages child1 s' = getMappedPages child1 s).
      apply getMappedPagesUpdateMappedPageData with level; trivial.
      unfold consistency in *; intuition.
      rewrite Hmapped; clear Hmapped.
       
      assert (Hmapped : getMappedPages child2 s' = getMappedPages child2 s).
      apply getMappedPagesUpdateMappedPageData with level; trivial.
      unfold consistency in *; intuition.
      rewrite Hmapped.
      unfold s'.
      rewrite getConfigPagesUpdateMappedPageData.
      rewrite getConfigPagesUpdateMappedPageData.
      unfold getUsedPages in Hiso.
      apply Hiso with parent; trivial.
      unfold s' in Hchild1.
      rewrite getChildrenUpdateMappedPageData in Hchild1; trivial.
      { assert(Hfalse : (defaultPage =? table) = false) by trivial.
        apply beq_nat_false in Hfalse.
        unfold not; intros.
        apply Hfalse.
        subst;trivial. }
      { unfold consistency in *; intuition. }
      {  assert(Hconfig : forall partition : page,
                     In partition (getPartitions multiplexer s) ->
                     partition = table \/ 
                     In table (getConfigPagesAux partition s) -> False) by trivial.
               unfold not. apply Hconfig; trivial. }
      { assert(Hconfig : forall partition : page,
          In partition (getPartitions multiplexer s) ->
          partition = table \/ 
          In table (getConfigPagesAux partition s) -> False) by trivial.
          assert (Hparent : In parent (getPartitions multiplexer s)) by trivial.
           generalize (Hconfig parent Hparent); clear Hconfig; intros Hconfig.
              apply Classical_Prop.not_or_and in Hconfig.
              destruct Hconfig as (Hi1 & Hi2).
               unfold not.
              intros Hfalse. rewrite Hfalse in Hi1.
              now contradict Hi1. }
      { unfold s' in Hchild2.
        rewrite getChildrenUpdateMappedPageData in Hchild2; trivial.
         { assert(Hfalse : (defaultPage =? table) = false) by trivial.
           apply beq_nat_false in Hfalse.
           unfold not; intros.
           apply Hfalse.
           subst;trivial. }
         { unfold consistency in *; intuition. }
         { assert(Hconfig : forall partition : page,
                         In partition (getPartitions multiplexer s) ->
                         partition = table \/ 
                         In table (getConfigPagesAux partition s) -> False) by trivial.
           unfold not. apply Hconfig; trivial. }
         { assert(Hconfig : forall partition : page,
              In partition (getPartitions multiplexer s) ->
              partition = table \/ 
              In table (getConfigPagesAux partition s) -> False) by trivial.
           assert (Hparent : In parent (getPartitions multiplexer s)) by trivial.
           generalize (Hconfig parent Hparent); clear Hconfig; intros Hconfig.
           apply Classical_Prop.not_or_and in Hconfig.
           destruct Hconfig as (Hi1 & Hi2).
           unfold not.
           intros Hfalse. rewrite Hfalse in Hi1.
           now contradict Hi1. } }
    assert (Hconfig : forall partition : page,
            In partition (getPartitions multiplexer s) ->
            partition = table \/ 
            In table (getConfigPagesAux partition s) -> False) by trivial.
    unfold not. apply Hconfig; trivial.
        assert (Hconfig : forall partition : page,
            In partition (getPartitions multiplexer s) ->
            partition = table \/ 
            In table (getConfigPagesAux partition s) -> False) by trivial.
    unfold not. apply Hconfig; trivial. }
  split.
(** kernelDataIsolation **)
  assert(Hiso : kernelDataIsolation s) by intuition.
  { unfold kernelDataIsolation.
    intros partition1 partition2 Hpart1 Hpart2.
    intuition.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
     { unfold s'.
       apply getPartitionsUpdateMappedPageData ; trivial.
       + unfold getPartitions.
         destruct nbPage;simpl;left;trivial.
       + assert(Hfalse : (defaultPage =? table) = false) by trivial.
         apply beq_nat_false in Hfalse.
         unfold not; intros.
         apply Hfalse.
         subst;trivial.
       + unfold consistency in *. intuition. }
    rewrite Hpartions in *.
    assert(Hpde : partitionDescriptorEntry s).
    { unfold consistency in *; intuition. }
    assert (Hallmap: getMappedPages partition1 s' = getMappedPages partition1 s).
    apply getMappedPagesUpdateMappedPageData with level; trivial.
    assert (Haccss : getAccessibleMappedPages partition1 s' = 
                     getAccessibleMappedPages partition1 s).
    apply getAccessibleMappedPagesUpdateMappedPageData with level; trivial.
    rewrite Haccss.
    unfold s'.
    rewrite getConfigPagesUpdateMappedPageData.
    apply Hiso; trivial.
    assert(Hconfig : forall partition : page,
                       In partition (getPartitions multiplexer s) ->
                       partition = table \/ 
                       In table (getConfigPagesAux partition s) -> False) by trivial.
    unfold not.
    apply Hconfig; trivial. }
(** verticalSharing **)
  split.
  assert (Hvs : verticalSharing s) by intuition.
  { unfold verticalSharing.
    intros parent child Hparentmult Hchild.
    intuition.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
       { unfold s'.
         apply getPartitionsUpdateMappedPageData ; trivial.
         + unfold getPartitions.
           destruct nbPage;simpl;left;trivial.
         + assert(Hfalse : (defaultPage =? table) = false) by trivial.
           apply beq_nat_false in Hfalse.
           unfold not; intros.
           apply Hfalse.
           subst;trivial.
         + unfold consistency in *. intuition. }
    rewrite Hpartions in *; clear Hpartions.
    assert(Hpde : partitionDescriptorEntry s).
    { unfold consistency in *; intuition. }
    assert (Hchildmult : In child (getPartitions multiplexer s)).
    { apply childrenPartitionInPartitionList with parent; trivial.
      unfold s' in Hchild.
      rewrite getChildrenUpdateMappedPageData in Hchild; fold s'; trivial.
      assert(Hfalse : (defaultPage =? table) = false) by trivial.
      apply beq_nat_false in Hfalse.
      unfold not; intros.
      apply Hfalse.
      subst;trivial.
      assert(Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False) by trivial.
      unfold getConfigPages.
      simpl.
      unfold not.
      apply Hconfig; trivial.
      assert(Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False) by trivial.
      assert(Hparent : In parent (getPartitions multiplexer s)); trivial.
      generalize (Hconfig parent Hparent); clear Hconfig; intros Hconfig. unfold not.
      intros. apply Hconfig.
      subst.
      left; trivial. }
    assert (Hmapped : getMappedPages parent s' = getMappedPages parent s).
    apply getMappedPagesUpdateMappedPageData with level; trivial.
    rewrite Hmapped; clear Hmapped.     
    unfold getUsedPages.
    assert (Hmapped : getMappedPages child s' = getMappedPages child s).
    apply getMappedPagesUpdateMappedPageData with level; trivial.      
    rewrite Hmapped; clear Hmapped.    
    unfold s'.
    rewrite getConfigPagesUpdateMappedPageData.
    apply Hvs; trivial.
    unfold s' in Hchild.
    rewrite getChildrenUpdateMappedPageData in Hchild; fold s'; trivial.
    { assert(Hfalse : (defaultPage =? table) = false) by trivial.
       apply beq_nat_false in Hfalse.
       unfold not; intros.
       apply Hfalse.
       subst;trivial. }
     { assert(Hconfig : forall partition : page,
                     In partition (getPartitions multiplexer s) ->
                     partition = table \/ 
                     In table (getConfigPagesAux partition s) -> False) by trivial.
       unfold not. apply Hconfig; trivial. }
     { assert(Hconfig : forall partition : page,
          In partition (getPartitions multiplexer s) ->
          partition = table \/ 
          In table (getConfigPagesAux partition s) -> False) by trivial.
       assert (Hparent : In parent (getPartitions multiplexer s)) by trivial.
       generalize (Hconfig parent Hparent); clear Hconfig; intros Hconfig.
       apply Classical_Prop.not_or_and in Hconfig.
       destruct Hconfig as (Hi1 & Hi2).
       unfold not.
       intros Hfalse. rewrite Hfalse in Hi1.
       now contradict Hi1. }
     { assert(Hconfig : forall partition : page,
                     In partition (getPartitions multiplexer s) ->
                     partition = table \/ 
                     In table (getConfigPagesAux partition s) -> False) by trivial.
       unfold not. apply Hconfig; trivial. } }
  split.
(** consistency **)
  assert(Hcons : consistency s ) by intuition.
  { unfold consistency in *.
    destruct Hcons as (Hpde & Hdspd & Hdssh1 & Hdssh2 & Hcurpart & Hdupmap
                        & Hdupconf & Hparent).
    assert(Hconfig : forall partition : page,
          In partition (getPartitions multiplexer s) ->
          partition = table \/ 
          In table (getConfigPagesAux partition s) -> False) by intuition.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
       { unfold s'.
         apply getPartitionsUpdateMappedPageData ; trivial.
         + unfold getPartitions.
           destruct nbPage;simpl;left;trivial.
         + assert(Hfalse : (defaultPage =? table) = false) by intuition.
           apply beq_nat_false in Hfalse.
           unfold not; intros.
           apply Hfalse.
           subst;trivial. }
    assert (Hfalse : (defaultPage =? table) = false) by intuition.
  (** partitionDescriptorEntry **)
    split.
    apply partitionDescriptorEntryUpdateMappedPageData; trivial.
  (** dataStructurePdSh1Sh2asRoot **)
    split.
    apply dataStructurePdSh1Sh2asRootUpdateMappedPageData; trivial.
    left; trivial.
  (** dataStructurePdSh1Sh2asRoot sh1idx **)
    split.
    apply dataStructurePdSh1Sh2asRootUpdateMappedPageData; trivial.
    right;left; trivial.
  (** dataStructurePdSh1Sh2asRoot sh2idx **)
    split.
    apply dataStructurePdSh1Sh2asRootUpdateMappedPageData; trivial.
    right;right;trivial.
  (** currentPartitionInPartitionsList **)
    split. 
    unfold currentPartitionInPartitionsList in *.
    rewrite Hpartions.
    unfold s'; cbn; assumption.  
  (** noDupMappedPagesList **)
    split.
    unfold noDupMappedPagesList in *; intros.
    rewrite Hpartions in *.
    assert (Hmapped : getMappedPages partition s' = getMappedPages partition s).
    assert (Some level = StateLib.getNbLevel) by intuition.
    apply getMappedPagesUpdateMappedPageData with level; trivial.
    rewrite Hmapped.
    apply Hdupmap; trivial. 
  (** noDupConfigPagesList **)
    split.
    unfold noDupConfigPagesList in *; intros.
    rewrite Hpartions in *.
    assert(Hpp : nextEntryIsPP partition idxroot root s).
    rewrite nextEntryIsPPUpdateMappedPageData; trivial.
    unfold s' in *; eassumption.
    apply Hconfig.
    apply Hfalse.
    unfold getIndirections in *.
    unfold s'.
    rewrite getIndirectionsAuxUpdateMappedPageData; trivial.
    apply Hdupconf with idxroot partition; trivial.
    destruct H2 as [Hpd | [Hsh1 | Hsh2]].
    { subst.
      apply  notConfigTableNotPdconfigTable with partition; trivial.
      generalize (Hconfig partition H3); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      apply nextEntryIsPPgetPd; trivial. }
    { subst.
      apply  notConfigTableNotSh1configTable with partition; trivial.
      generalize (Hconfig partition H3); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      apply nextEntryIsPPgetFstShadow; trivial. }
    { subst.
      apply  notConfigTableNotSh2configTable with partition; trivial.
      generalize (Hconfig partition H3); clear Hconfig; intros Hconfig.
      unfold not.
      intros.
      apply Hconfig.
      right; trivial.
      apply nextEntryIsPPgetSndShadow; trivial. }
  (** parentInPartitionList **) 
    unfold parentInPartitionList in *.
    intros.
    rewrite Hpartions in *.
    assert ( nextEntryIsPP partition PPRidx parent s).
    rewrite nextEntryIsPPUpdateMappedPageData; trivial.
    unfold s' in *; eassumption.
    apply Hconfig.
    apply Hfalse.
    apply Hparent with partition;trivial. } 
(** Propagated properties **)
  {
    unfold consistency in *.
    assert (Hcurpart : In currentPart (getPartitions multiplexer s)). 
    assert (Hcurpart : currentPartitionInPartitionsList s)by intuition.
    unfold currentPartitionInPartitionsList in *.
    assert (currentPart = currentPartition s) by intuition.
    subst. intuition.
    assert( Hpde : partitionDescriptorEntry s) by intuition.
    assert (Hnotconfig : forall partition : page,
     In partition (getPartitions multiplexer s) ->
     ~ (partition = table \/ In table (getConfigPagesAux partition s))) by intuition.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
     { unfold s'.
       apply getPartitionsUpdateMappedPageData ; trivial.
       + unfold getPartitions.
         destruct nbPage;simpl;left;trivial.
       + assert(Hfalse : (defaultPage =? table) = false) by intuition.
         apply beq_nat_false in Hfalse.
         unfold not; intros.
         apply Hfalse.
         subst;trivial. }
    intuition try assumption. 
    + apply nextEntryIsPPUpdateMappedPageData; trivial.
    + assert(Hptref : forall idx : index,
        StateLib.getIndexOfAddr descChild fstLevel = idx ->
        isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s)
        by trivial.
      apply isPEUpdateUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD descChild idxRefChild s ;
       trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
          StateLib.getIndexOfAddr descChild fstLevel = idx ->
          isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) 
      by trivial.
      assert (StateLib.getIndexOfAddr descChild fstLevel = idxRefChild) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr descChild fstLevel = idx ->
      isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s)
      by trivial.
      apply entryPresentFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD descChild idxRefChild s ;
      trivial.
    + assert(Hptref : forall idx : index,
        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
        isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s)
        by trivial.
      apply isPEUpdateUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD pdChild idxPDChild s ;
       trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
        isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) 
      by trivial.
      assert (StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial. 
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
      isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s)
      by trivial.
      apply entryPresentFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD pdChild idxPDChild s ;
      trivial.
    + assert(Hptref : forall idx : index,
        StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
        isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s)
        by trivial.
      apply isPEUpdateUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD shadow1 idxSh1 s ;
         trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
        isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) 
      by trivial.
      assert (StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
      isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s)
      by trivial.
      apply entryPresentFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD shadow1 idxSh1 s ;
      trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
      isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s)
      by trivial.
      apply isPEUpdateUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD shadow2 idxSh2 s ;
      trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
        isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) 
      by trivial.
      assert (StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial. 
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
      isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s)
      by trivial.
      apply entryPresentFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD shadow2 idxSh2 s ;
      trivial.
    + assert(Hptref : forall idx : index,
        StateLib.getIndexOfAddr list fstLevel = idx ->
        isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s)
        by trivial.
      apply isPEUpdateUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD list idxConfigPagesList s ;
           trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr list fstLevel = idx ->
        isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s) 
      by trivial.
      assert (StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial. 
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr list fstLevel = idx ->
      isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s)
      by trivial.
      apply entryPresentFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD list idxConfigPagesList s ;
      trivial.
    + apply nextEntryIsPPUpdateMappedPageData; trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr descChild fstLevel = idx ->
      isVE ptRefChildFromSh1 idx s /\ getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
        by trivial.
      apply isVEUpdateMappedPageData; trivial.
      apply mappedPageIsNotShadow1Table with currentPart currentPD currentShadow1 descChild idxRefChild s ;
           trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr descChild fstLevel = idx ->
        isVE ptRefChildFromSh1 idx s /\ getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) 
      by trivial.
      assert (StateLib.getIndexOfAddr descChild fstLevel = idxRefChild) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hvaref : exists va : vaddr, 
            isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
            beqVAddr defaultVAddr va = derivedRefChild) by trivial.
      destruct Hvaref as (vaRef & Hvaref & Hderivref).
      exists vaRef; split; trivial.
      unfold s'.
      apply isEntryVAUpdateMappedPageData; trivial.
      apply mappedPageIsNotShadow1Table with currentPart currentPD currentShadow1 descChild idxRefChild s ;
         trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
      isVE ptPDChildSh1 idx s /\ getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s)
        by trivial.
      apply isVEUpdateMappedPageData; trivial.
      apply mappedPageIsNotShadow1Table with currentPart currentPD currentShadow1 pdChild idxPDChild s ;
           trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
        isVE ptPDChildSh1 idx s /\ getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) 
      by trivial.
      assert (StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hvaref : exists va : vaddr, 
            isEntryVA ptPDChildSh1 idxPDChild va s /\ 
            beqVAddr defaultVAddr va = derivedPDChild) by trivial.
      destruct Hvaref as (vaRef & Hvaref & Hderivref).
      exists vaRef; split; trivial.
      unfold s'.
      apply isEntryVAUpdateMappedPageData; trivial.
      apply mappedPageIsNotShadow1Table with currentPart currentPD currentShadow1 pdChild idxPDChild s ;
         trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
      isVE ptSh1ChildFromSh1 idx s /\ getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s)
        by trivial.
      apply isVEUpdateMappedPageData; trivial.
      apply mappedPageIsNotShadow1Table with currentPart currentPD currentShadow1 shadow1 idxSh1 s ;
           trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
        isVE ptSh1ChildFromSh1 idx s /\ getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) 
      by trivial.
      assert (StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hvaref : exists va : vaddr, 
            isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ 
            beqVAddr defaultVAddr va = derivedSh1Child) by trivial.
      destruct Hvaref as (vaRef & Hvaref & Hderivref).
      exists vaRef; split; trivial.
      unfold s'.
      apply isEntryVAUpdateMappedPageData; trivial.
      apply mappedPageIsNotShadow1Table with currentPart currentPD currentShadow1 shadow1 idxSh1 s ;
         trivial.
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
      isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s)
        by trivial.
      apply isVEUpdateMappedPageData; trivial.
      apply mappedPageIsNotShadow1Table with currentPart currentPD currentShadow1 shadow2 idxSh2 s ;
           trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
        isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
      by trivial.
      assert (StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hvaref : exists va : vaddr, 
            isEntryVA childSh2 idxSh2 va s /\ 
            beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hvaref as (vaRef & Hvaref & Hderivref).
      exists vaRef; split; trivial.
      unfold s'.
      apply isEntryVAUpdateMappedPageData; trivial.
      apply mappedPageIsNotShadow1Table with currentPart currentPD currentShadow1 shadow2 idxSh2 s ;
         trivial. 
    + assert(Hptref : forall idx : index,
      StateLib.getIndexOfAddr list fstLevel = idx ->
      isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 sh1idx currentPart list s)
        by trivial.
      apply isVEUpdateMappedPageData; trivial.
      apply mappedPageIsNotShadow1Table with currentPart currentPD currentShadow1 list idxConfigPagesList s ;
           trivial.
      apply Hptref; trivial.
    + assert(Htblroot : forall idx : index,
        StateLib.getIndexOfAddr list fstLevel = idx ->
        isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 sh1idx currentPart list s) 
      by trivial.
      assert (StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList) 
      as Hidxref by trivial.
      apply Htblroot in Hidxref.
      destruct Hidxref as (Hperef & Hrootref).
      unfold s'.
      apply getTableAddrRootUpdateMappedPageData; trivial.
    + assert(Hvaref : exists va : vaddr, 
            isEntryVA childListSh1 idxConfigPagesList va s /\ 
            beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
      destruct Hvaref as (vaRef & Hvaref & Hderivref).
      exists vaRef; split; trivial.
      unfold s'.
      apply isEntryVAUpdateMappedPageData; trivial.
      apply mappedPageIsNotShadow1Table with currentPart currentPD currentShadow1 list 
      idxConfigPagesList s ;
         trivial.
    + apply isEntryPageUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD pdChild idxPDChild s ;
      trivial.
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions multiplexer s)) by trivial.
      generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
      apply Hconfig.
      left; assumption.
    +  assert (Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions multiplexer s)) by trivial.      
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
      In partition (getPartitions multiplexer s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False)
      by trivial.
      unfold not.
      intros Hfalse. 
      apply Hconfigpd with partition; trivial.
    + apply isEntryPageUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD shadow1 idxSh1 s ;
      trivial.
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions multiplexer s)) by trivial.
      generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
      apply Hconfig.
      left; assumption. 
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions multiplexer s)) by trivial.      
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
      In partition (getPartitions multiplexer s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False)
      by trivial.
      unfold not.
      intros Hfalse. 
      apply Hconfigpd with partition; trivial.
    + apply isEntryPageUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD shadow2 idxSh2 s ;
      trivial.
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions multiplexer s)) by trivial.
      generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
      apply Hconfig.
      left; assumption. 
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions multiplexer s)) by trivial.      
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
      In partition (getPartitions multiplexer s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False)
      by trivial.
      unfold not.
      intros Hfalse. 
      apply Hconfigpd with partition; trivial.
    + apply isEntryPageUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD list idxConfigPagesList s ;
      trivial.
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions multiplexer s)) by trivial.
      generalize (Hconfig partition Hmult); clear Hconfig; intros Hconfig.
      apply Hconfig.
      left; assumption. 
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False)
      by trivial.
      rewrite Hpartions in *.
      assert (Hmult : In partition (getPartitions multiplexer s)) by trivial.      
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
      In partition (getPartitions multiplexer s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False)
      by trivial.
      unfold not.
      intros Hfalse. 
      apply Hconfigpd with partition; trivial.
    + apply isEntryPageUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD descChild idxRefChild s ;
      trivial.
    + assert (Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False)
      by trivial.
      unfold s' in *.
      rewrite getConfigPagesUpdateMappedPageData in *.
            rewrite Hpartions in *; trivial.
      apply Hconfig with partition; trivial.
      assert (Hconfigpd : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      partition = table \/ In table (getConfigPagesAux partition s) -> False)
      by trivial.
      unfold not.
      intros Hfalse. 
      apply Hconfigpd with partition; trivial.
            rewrite Hpartions in *; trivial.
    + apply entryUserFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD pdChild idxPDChild s ;
      trivial.
    + apply entryUserFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD shadow1 idxSh1 s ;
      trivial.
    + apply entryUserFlagUpdateMappedPageData; trivial. 
      apply mappedPageIsNotPTable with currentPart currentPD shadow2 idxSh2 s ;
      trivial.
    + apply entryUserFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD list idxConfigPagesList s ;
      trivial.
    + apply entryUserFlagUpdateMappedPageData; trivial.
      apply mappedPageIsNotPTable with currentPart currentPD descChild idxRefChild s ;
      trivial. }
Qed.

       