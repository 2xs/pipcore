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

(**  * Summary 
    In this file we formalize and prove all invariants of the MAL and MALInternal functions *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.IAL Pip.Model.Lib
               Pip.Model.MAL.
Require Import Pip.Core.Internal Pip.Core.Services.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas
               Pip.Proof.Isolation Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Coq.Logic.ProofIrrelevance Lia Setoid Compare_dec EqNat List Bool.

Module WP := WeakestPreconditions.
Lemma getMultiplexer (P : state -> Prop) :
{{ fun s => P s  }} MALInternal.getMultiplexer
{{ fun val s => P s /\ val = multiplexer }}.
Proof.
   eapply WP.weaken.
   eapply WP.getMultiplexer .
   intros.
   cbn. intuition.
Qed.


Lemma getKidx (P : state -> Prop) :
{{ fun s => P s  }} MALInternal.getKidx 
{{ fun idx s => P s /\ Kidx = idx }}.
Proof.
   eapply WP.weaken.
   eapply WP.getKidx . intros.
   cbn. intuition.
Qed.

Lemma getCurPartition P :
{{fun s => P s }} MAL.getCurPartition 
{{fun (PR : page) (s : state) => P s  /\ PR = currentPartition s }}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.getCurPartition .
cbn. intros . intuition. 
Qed.

Lemma getPDidx P :
{{fun s => P s }} MALInternal.getPDidx 
{{fun (idxPD : index) (s : state) => P s  /\ idxPD = PDidx }}.
Proof.
eapply WP.weaken. 
eapply WP.getPDidx . cbn.
intros. 
intuition.
Qed.
Lemma getSh1idx P :
{{fun s => P s }} MALInternal.getSh1idx 
{{fun (idxSh1 : index) (s : state) => P s  /\ idxSh1 = sh1idx }}.
Proof.
eapply WP.weaken. 
eapply WP.getSh1idx . cbn.
intros. 
intuition.
Qed.

Lemma getSh2idx P :
{{fun s => P s }} MALInternal.getSh2idx 
{{fun (idxSh2 : index) (s : state) => P s  /\ idxSh2 = sh2idx }}.
Proof.
eapply WP.weaken. 
eapply WP.getSh2idx . cbn.
intros. 
intuition.
Qed.

Lemma getSh3idx P :
{{fun s => P s }} MALInternal.getSh3idx 
{{fun (idxsh3 : index) (s : state) => P s  /\ idxsh3 = sh3idx }}.
Proof.
eapply WP.weaken. 
eapply WP.getSh3idx . cbn.
intros. 
intuition.
Qed.

Lemma getPPRidx P :
{{fun s => P s }} MALInternal.getPPRidx 
{{fun (idxPPR : index) (s : state) => P s  /\ idxPPR = PPRidx }}.
Proof.
eapply WP.weaken. 
eapply WP.getPPRidx . cbn.
intros. 
intuition.
Qed.

Lemma getPRidx P :
{{fun s => P s }} MALInternal.getPRidx 
{{fun (idxPR : index) (s : state) => P s  /\ idxPR = PRidx }}.
Proof.
eapply WP.weaken. 
eapply WP.getPRidx . cbn.
intros. 
intuition.
Qed.

Module Index. 
Lemma eqb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Index.eqb index1 index2 
{{ fun b s => P s /\ b = StateLib.Index.eqb index1 index2}}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.Index.eqb .
intros. simpl. split;trivial.
Qed.

Lemma gtb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Index.gtb index1 index2
{{ fun b s => P s /\ b = StateLib.Index.gtb index1 index2 }}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.Index.gtb .
intros. simpl. split;trivial.
Qed.

Lemma ltb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Index.ltb index1 index2 
{{ fun b s => P s /\ b = StateLib.Index.ltb index1 index2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.ltb.
intros. simpl. split;trivial.
Qed.

Lemma leb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Index.leb index1 index2 
{{ fun b s => P s /\ b = StateLib.Index.leb index1 index2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.leb.
intros. simpl. split;trivial.
Qed.

Lemma geb index1 index2 (P : state -> Prop):
{{ fun s : state => P  s }} MALInternal.Index.geb index1 index2 
{{ fun b s => P s /\ b = StateLib.Index.geb index1 index2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.geb.
intros. simpl. split;trivial.
Qed.

Lemma zero P :
{{fun s => P s }} MALInternal.Index.zero 
{{fun (idx0 : index) (s : state) => P s  /\ idx0 = CIndex 0 }}.
Proof.
unfold MALInternal.Index.zero.
eapply WP.weaken.
eapply WP.ret .
intros. simpl.
intuition.
unfold CIndex.
case_eq (lt_dec 0 tableSize).
intros. f_equal. apply proof_irrelevance.
intuition. assert (tableSize > tableSizeLowerBound). apply tableSizeBigEnough.
unfold  tableSizeLowerBound in * . contradict H1. lia.
Qed.

Lemma succ (idx : index ) P :
{{fun s => P s  /\ idx < tableSize - 1}} MALInternal.Index.succ idx 
{{fun (idxsuc : index) (s : state) => P s  /\ StateLib.Index.succ idx = Some idxsuc }}.
Proof.
eapply WP.weaken. 
eapply  WeakestPreconditions.Index.succ.
cbn.
intros.
split.  
intuition.
intros.
split. intuition.
unfold StateLib.Index.succ.
subst.
destruct (lt_dec (idx + 1) tableSize). assert (l=l0).
apply proof_irrelevance.
subst. reflexivity.
intuition. 
Qed.
Lemma pred (idx : index ) P :
{{fun s => P s  /\ idx > 0}} MALInternal.Index.pred idx 
{{fun (idxpred : index) (s : state) => P s  /\ StateLib.Index.pred idx = Some idxpred }}.
Proof.
eapply WP.weaken. 
eapply  WeakestPreconditions.Index.pred.
cbn.
intros.
split.  
intuition.
intros.
split. intuition.
unfold StateLib.Index.pred.
subst.
destruct (gt_dec idx 0).
f_equal.
f_equal.
apply proof_irrelevance.
subst.
intuition. 
Qed.
End Index.

Module Level.
Lemma gtb level1 level2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Level.gtb level1 level2 
{{ fun b s => P s /\ b = StateLib.Level.gtb level1 level2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Level.gtb.
intros. simpl. split;trivial.
Qed.

Lemma pred (level1 : level ) P :
{{fun s => P s  /\ level1 > 0 }} MALInternal.Level.pred level1
{{fun (levelpred : level) (s : state) => P s  /\ StateLib.Level.pred level1 = Some levelpred }}.
Proof.
eapply WP.weaken. 
eapply WeakestPreconditions.Level.pred . cbn.
intros.
split.  
intuition.
intros.
split. intuition.
unfold StateLib.Level.pred.
unfold runvalue. subst. 
destruct (gt_dec level1 0).
intros. assert (Hl =  StateLib.Level.pred_obligation_1 level1 g ).
apply proof_irrelevance.
subst. reflexivity.
intuition. 
Qed.

Lemma eqb level1 level2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Level.eqb level1 level2 
{{ fun b s => P s /\  b = StateLib.Level.eqb level1 level2 }}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.Level.eqb .
intros; simpl; split;trivial.
Qed.
End Level.

Module Page. 
Lemma eqb page1 page2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Page.eqb page1 page2 
{{ fun b s => P s /\ b = StateLib.Page.eqb page1 page2}}.
Proof.
eapply WP.weaken.
eapply WP.Page.eqb .
intros. simpl. split;trivial.
Qed.
End Page.

Module VAddr. 
Lemma eqbList vaddr1 vaddr2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.VAddr.eqbList vaddr1 vaddr2 
{{ fun b s => P s /\ b = StateLib.VAddr.eqbList vaddr1 vaddr2}}.
Proof.
eapply WP.weaken.
eapply WP.VAddr.eqbList .
intros. simpl. split;trivial.
Qed.
End VAddr.

Lemma ret (A : Type) (a : A)  P :
{{fun s => P s }} Hardware.ret a
{{fun (v : A) (s : state) => P s  /\ v = a }}.
Proof.
eapply WP.weaken. 
eapply WP.ret . cbn.
intros. 
auto.
Qed.

Lemma getMaxIndex P : 
{{ fun s => P s }} MAL.getMaxIndex 
{{ fun idx s => P s /\ idx = CIndex (tableSize -1) }}.
Proof.
unfold MAL.getMaxIndex.
case_eq (gt_dec tableSize 0);
intros.
eapply WP.weaken.
eapply WP.ret . intros.
simpl. split. assumption.
unfold CIndex.
case_eq ( lt_dec (tableSize - 1) tableSize ).
intros.     
f_equal. apply proof_irrelevance.
intuition.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold  tableSizeLowerBound in * .
contradict H0. lia.
Qed.



Lemma readPhyEntry (table : page) (idx : index) (P : state -> Prop):
{{fun s => P s /\  isPE table idx s}} MAL.readPhyEntry table idx 
{{fun (page1 : page) (s : state) => P s /\ isEntryPage table idx page1 s}}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.readPhyEntry .
simpl. intros.
destruct H as (H & Hpage).
unfold isPE, isEntryPage in *.
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict Hpage.
destruct v; try now contradict Hpage.
eexists;repeat split;trivial.
Qed.

Lemma readIndex (table : page) (idx : index) (P : state -> Prop):
{{fun s => P s /\  isI table idx s}} MAL.readIndex table idx 
{{fun (ivalue : index) (s : state) => P s /\ isIndexValue table idx ivalue s}}.
Proof.
eapply WP.weaken.
eapply WP.readIndex .
simpl. intros.
destruct H as (H & Hpage).
unfold isI, isIndexValue in *.
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict Hpage.
destruct v; try now contradict Hpage.
eexists;repeat split;trivial.
Qed.


Lemma getDefaultPage P : 
{{fun s => P s}} MALInternal.getDefaultPage 
{{fun nullp s => P s /\ nullp = defaultPage}}.
Proof.
unfold MALInternal.getDefaultPage.
eapply WP.weaken.
eapply WP.ret .
intros.
simpl. intuition.
Qed.  

Lemma getDefaultVAddr P : 
{{fun s => P s}} MALInternal.getDefaultVAddr 
{{fun nullv s => P s /\ nullv = defaultVAddr }}.
Proof.
unfold MALInternal.getDefaultVAddr.
eapply WP.weaken.
eapply WP.ret .
intros.
simpl. intuition.
Qed.

Lemma removeDupIdentity  (l :  list (paddr * value)) : 
forall table1 idx1 table2 idx2 , table1 <> table2 \/ idx1 <> idx2 -> 
lookup table1 idx1 (removeDup table2 idx2 l  beqPage beqIndex) beqPage beqIndex = 
lookup table1 idx1 l beqPage beqIndex.
Proof.
intros.
induction l.
simpl. trivial.
simpl.
destruct a.
destruct p.
apply beqPairsFalse in H.
+ case_eq (beqPairs (p, i) (table2, idx2) beqPage beqIndex).
  - intros.
    unfold beqPairs in H0. cbn in H0.
    case_eq (beqPage p table2 && beqIndex i idx2 ).
    * intros.
      rewrite H1 in H0.
      unfold beqPage , beqIndex in H1.
      apply andb_true_iff in H1.
      destruct H1.
      apply beq_nat_true in H1.
      apply beq_nat_true in H2.
      assert (beqPairs (p, i) (table1, idx1) beqPage beqIndex = false).
      { destruct p, i, table2, table1, idx2, idx1. simpl in *.
      subst.
      assert (Hp = Hp0). apply proof_irrelevance. subst. 
      assert(Hi = Hi0).  apply proof_irrelevance. subst.
      unfold beqPairs in *. cbn in *.
      
      rewrite NPeano.Nat.eqb_sym.
      replace (Nat.eqb i0 i1) with (Nat.eqb i1 i0). assumption.
      rewrite NPeano.Nat.eqb_sym . trivial. }
      rewrite H3. assumption.
    * intros. rewrite H1 in H0.
      contradict H0. auto.
  - intros. simpl. 
    case_eq (beqPairs (p, i) (table1, idx1) beqPage beqIndex).
    intros. trivial.
    intros. assumption.   
Qed.

Lemma isPPLookupEq table idx res s:
isPP' table idx res s -> lookup table idx (memory s) beqPage beqIndex = Some (PP res).
Proof.
intros.
unfold isPP' in *.
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict H.
destruct v; try now contradict H.
subst ;trivial.
Qed.

Lemma getNbLevel P :
{{fun s => P s }} MAL.getNbLevel 
{{fun (level1 : level) (s : state) => P s  /\ Some level1 =StateLib.getNbLevel }}.
Proof.
eapply WP.weaken. 
eapply WeakestPreconditions.getNbLevel .
cbn.
intros. 
intuition.
apply nbLevelNotZero.
unfold StateLib.getNbLevel.
destruct (gt_dec nbLevel 0) .
simpl. assert (H0=g).
apply proof_irrelevance.
subst. reflexivity.
subst. intuition.
Qed.

Lemma comparePageToNull (page1 : page) (P : state -> Prop): 
{{fun s => P s }} Internal.comparePageToNull page1 
{{fun (isnull : bool) (s : state) => P s /\ (Nat.eqb defaultPage page1) = isnull }}. 
Proof.
unfold Internal.comparePageToNull.
eapply WP.bindRev.
+ unfold MALInternal.getDefaultPage.
  eapply WP.weaken.  
  eapply WP.ret . intros.  
  instantiate (1:= fun nullP s => P s /\ defaultPage = nullP ).
  simpl.
  intuition.
+ intro nullP. unfold MALInternal.Page.eqb. simpl.
  eapply WP.weaken. eapply WP.ret . intros. 
  simpl. intuition. subst. intuition.
Qed.

Lemma getIndexOfAddr (va : vaddr) (l: level) (P: state -> Prop) :
{{ fun s : state => P s }} MAL.getIndexOfAddr va l
{{ fun (idx : index) s => P s /\ StateLib.getIndexOfAddr va l =  idx   }}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.getIndexOfAddr .
simpl. intros.
split.
destruct l.
destruct va.
simpl. assumption.
unfold StateLib.getIndexOfAddr.
trivial.
Qed.

Lemma isPELookupEq table idx s : 
isPE table idx s -> exists entry : Pentry,
  lookup table idx (memory s) beqPage beqIndex = Some (PE entry).
Proof.
intros.  
unfold isPE in H.
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
Qed.


Lemma lookupEntryPresentFlag table idx s : 
forall entry , lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
entryPresentFlag table idx (present entry) s. 
Proof.
intros.
unfold entryPresentFlag.
rewrite H;trivial.
Qed.

Lemma lookupEntryPDFlag table idx s : 
forall entry , lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
entryPDFlag table idx (pd entry) s. 
Proof.
intros.
unfold entryPDFlag.
rewrite H;trivial.
Qed.

Lemma readPresent (table : page) (idx : index) (P : state -> Prop) : 
{{ fun s => P s /\ isPE table idx s }} MAL.readPresent table idx 
{{ fun (ispresent : bool) (s : state) => P s /\  entryPresentFlag table idx ispresent s }}.
Proof.
eapply WP.weaken. 
apply WeakestPreconditions.readPresent . simpl.
intros.
destruct H as (H & Hentry).
apply isPELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupEntryPresentFlag;trivial.
Qed.

Lemma lookupEntryUserFlag table idx s : 
forall entry , lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
entryUserFlag table idx (user entry) s. 
Proof.
intros.
unfold entryUserFlag.
rewrite H;trivial.
Qed.

Lemma readAccessible (table : page) (idx : index) (P : state -> Prop) : 
{{ fun s => P s /\ isPE table idx s  }} MAL.readAccessible table idx 
{{ fun (isaccessible : bool) (s : state) => P s /\ entryUserFlag table idx isaccessible s }}.
Proof.
eapply WP.weaken. 
apply WeakestPreconditions.readAccessible .
simpl.
intros.
destruct H as (H & Hentry).
apply isPELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupEntryUserFlag;trivial.
Qed.

Lemma isVELookupEq table idx s : 
 isVE table idx s  -> exists entry ,lookup table idx (memory s) beqPage beqIndex = Some (VE entry) . 
Proof.
intros.
unfold isVE in H.
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
Qed.
 
Lemma readVirEntry (table : page) (idx : index) (P : state -> Prop):
{{fun s => P s /\  isVE table idx s}} MAL.readVirEntry table idx 
{{fun (va : vaddr) (s : state) => P s /\ isEntryVA table idx va s}}.
Proof.
eapply WP.weaken.
eapply WP.readVirEntry .
simpl. intros.
destruct H as (H & Hva).
unfold isVE, isEntryVA in *.
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict Hva.
destruct v; try now contradict Hva.
eexists;repeat split;trivial.
Qed.

Lemma compareVAddrToNull (va : vaddr) (P : state -> Prop): 
{{fun s => P s }} compareVAddrToNull va 
{{fun (isnull : bool) (s : state) => P s /\ 
                                       (beqVAddr defaultVAddr va) = isnull }}. 
Proof.
unfold compareVAddrToNull.
eapply WP.bindRev.
+ unfold MALInternal.getDefaultVAddr.
  eapply WP.weaken.  
  eapply WP.ret . intros.  
  instantiate (1:= fun nullVa s => P s /\ beqVAddr defaultVAddr nullVa = true ).
  simpl.
  intuition.
  unfold beqVAddr.
  destruct defaultVAddr.
  simpl.
  clear Hva. 
  induction va0. simpl. trivial.
  simpl. 
  unfold beqIndex.
  case_eq(Nat.eqb a a); intros.
  apply IHva0.
  apply beq_nat_false in H0. lia.
+ intro nullva. simpl.
  unfold MALInternal.VAddr.eqbList. simpl.
  eapply WP.weaken. eapply WP.ret . intros. 
  simpl. intuition.
  f_equal.
  unfold beqVAddr in *.
   
  destruct defaultVAddr , nullva.
  simpl in *.
  assert (va0 = va1).
  clear Hva Hva0.
  revert H1.
  revert va1.
  induction va0. simpl in *.
  destruct va1;trivial.
  intros.
  now contradict H1. simpl in *.
  intros. 
  case_eq va1.
  intros.
  rewrite H in H1.
  now contradict H1.
  intros. subst.
  case_eq( beqIndex a i ); intros;
  rewrite H in H1.
  unfold beqIndex in H.
  apply beq_nat_true in H.
  f_equal; trivial. destruct i , a. simpl in *.
  subst.
  assert (Hi = Hi0) by apply proof_irrelevance.
  subst. reflexivity.
  generalize (IHva0 l H1); clear IHva0 ; intros IHva0.
  assumption.
  now contradict H1. subst.
  assert  (Hva = Hva0) by apply proof_irrelevance. subst. reflexivity.
Qed.

Lemma checkDerivation (table : page) (idx : index) (P : state -> Prop) : 
{{ fun s => P s /\ isVE table idx s }} checkDerivation table idx 
{{ fun (isderived : bool) (s : state) => P s /\ exists va, isEntryVA table idx va s /\  beqVAddr defaultVAddr va = isderived }}.
Proof.
unfold checkDerivation.
eapply WP.bindRev.
eapply WP.weaken.
eapply readVirEntry. simpl.
intros.
destruct H as (H & Hentry).
intuition. eapply H.
intros.
simpl.
eapply WP.strengthen.

eapply WP.weaken.
eapply compareVAddrToNull.
simpl.
intros.
pattern s in H.
eapply H.
intros.
simpl in *.
intuition.
exists a; intuition.
Qed.

Lemma entryPresentFlagIsPE table idx s : 
forall flag, entryPresentFlag table idx flag s -> isPE table idx s .
Proof.
intros.
unfold entryPresentFlag, isPE in *.
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
Qed.

Lemma getPd (PR : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In PR (getPartitions multiplexer s) }} 
                      Internal.getPd PR 
{{fun (pd : page) (s : state) => P s /\ nextEntryIsPP PR PDidx pd s 
                                             }}.
Proof.
unfold Internal.getPd.
eapply WP.bindRev.
(** getPDidx **)
apply getPDidx.
intro idxPD. 
simpl. 
(** MALInternal.Index.succ **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Index.succ.
intros. simpl.
split.
pattern s in H. 
eapply H.
destruct H as ((Hp & Hdescr & Hcurpart ) & Hidx). 
subst.
unfold partitionDescriptorEntry in *.
unfold currentPartitionInPartitionsList in *.
generalize (Hdescr PR Hcurpart); clear Hdescr; intros Hdescr.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx 
\/ PDidx = sh3idx \/ PDidx = PPRidx \/ PDidx = PRidx ) as Htmp by auto.
generalize (Hdescr PDidx Htmp); clear Hdescr; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (((HP & Hcons & Hcur ) &Hidx) & Hidxsucc).
subst.
unfold partitionDescriptorEntry in Hcons.
unfold currentPartitionInPartitionsList in *.
generalize (Hcons PR Hcur); clear Hcons; intros Hcons.

generalize (Hcons  PDidx); clear Hcons; intro Hpdtmp.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/ PDidx = sh3idx  \/ PDidx = PPRidx \/ PDidx = PRidx ) 
as Hpd by auto.
apply Hpdtmp in Hpd.
clear Hpdtmp. 
unfold partitionDescriptorEntry in Hpd.
destruct Hpd as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
exists page1.
repeat split; try assumption.
unfold nextEntryIsPP in Hpp; rewrite Hidxsucc in Hpp.
destruct (lookup PR idxsucc (memory s) beqPage beqIndex); try now contradict Hpp.
destruct v; try now contradict Hpp.
rewrite Hpp; trivial.
Qed.

Lemma readPhysical (table : page) (idx : index) (P : state -> Prop):
{{fun s => P s /\ isPP table idx s}} MAL.readPhysical table idx 
{{fun (page1 : page) (s : state) => P s /\ isPP' table idx page1 s}}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (H & Hpage).
unfold isPP', isPP in *.
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict Hpage.
destruct v; try now contradict Hpage.
eexists;repeat split;trivial.
Qed.

Lemma readVirtual (table : page) (idx : index) (P : state -> Prop):
{{fun s => P s /\ isVA table idx s}} MAL.readVirtual table idx 
{{fun (va : vaddr) (s : state) => P s /\ isVA' table idx va s}}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.readVirtual .
simpl. intros.
destruct H as (H & Hpage).
unfold isVA, isVA' in *.
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict Hpage.
destruct v; try now contradict Hpage.
eexists;repeat split;trivial.
Qed.

Lemma readVirtualUser (table : page) (idx : index) (P : state -> Prop):
{{fun s => P s}} MAL.readVirtualUser table idx 
{{fun (va : vaddr) (s : state) => P s /\ isVAUser table idx va s}}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.readVirtualUser .
simpl. intros.
unfold isVAUser.
destruct (lookup table idx (memory s) beqPage beqIndex);
[destruct v|]; split;trivial.
Qed.

Lemma getSndShadow (PR : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In PR (getPartitions multiplexer s) }} Internal.getSndShadow PR 
{{fun (sh2 : page) (s : state) => P s /\ nextEntryIsPP PR sh2idx sh2 s }}.
Proof.
unfold Internal.getSndShadow.
eapply WP.bindRev.
(** getSh2idx **)
apply getSh2idx.
intro idxSh2. 
simpl. 
(** MALInternal.Index.succ **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Index.succ.
intros. simpl.
split.
pattern s in H. 
eapply H.
subst.
intuition. subst.
unfold partitionDescriptorEntry in *.
generalize (H0 PR H3); clear H0; intros H0.
assert (sh2idx = PDidx \/ sh2idx = sh1idx \/ sh2idx = sh2idx \/ sh2idx = sh3idx 
\/  sh2idx  = PPRidx \/  sh2idx  = PRidx ) as Htmp by auto.
generalize (H0 sh2idx Htmp); clear H0; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as ( ((HP & Hcons & Hcur ) &Hidx) & Hidxsucc).
subst.
unfold partitionDescriptorEntry in Hcons.
generalize (Hcons PR Hcur ); clear Hcons; intros Hcons.
generalize (Hcons  sh2idx); clear Hcons; intro Hpdtmp.
assert (sh2idx = PDidx \/ sh2idx = sh1idx \/ sh2idx = sh2idx \/ sh2idx = sh3idx \/  sh2idx  = PPRidx
 \/  sh2idx  = PRidx)  
as Hpd by auto.
apply Hpdtmp in Hpd.
clear Hpdtmp. 
unfold partitionDescriptorEntry in Hpd.
destruct Hpd as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
unfold nextEntryIsPP in Hpp.
repeat split; try assumption.
unfold nextEntryIsPP in Hpp; rewrite Hidxsucc in Hpp.
destruct (lookup PR idxsucc (memory s) beqPage beqIndex); try now contradict Hpp.
destruct v; try now contradict Hpp.
rewrite Hpp; trivial.
Qed.

Lemma getFstShadow (PR : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ currentPartitionInPartitionsList s /\  PR = currentPartition s}} Internal.getFstShadow PR 
{{fun (sh1 : page) (s : state) => P s /\ nextEntryIsPP PR sh1idx sh1 s }}.
Proof.
unfold Internal.getFstShadow.
eapply WP.bindRev.
(** getPDidx **)
apply getSh1idx.
intro idxSh1. 
simpl. 
(** MALInternal.Index.succ **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Index.succ.
intros. simpl.
split.
pattern s in H. 
eapply H.
subst.
intuition. subst.
unfold partitionDescriptorEntry in *.
unfold currentPartitionInPartitionsList in *.
generalize (H0 (currentPartition s) H2); clear H0; intros H0.
assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/ sh1idx = sh3idx 
\/  sh1idx  = PPRidx \/  sh1idx  = PRidx ) as Htmp by auto.
generalize (H0 sh1idx Htmp); clear H0; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (((HP & Hcons & Hcur & Hpr) &Hidx) & Hidxsucc).
subst.
unfold partitionDescriptorEntry in Hcons.
unfold currentPartitionInPartitionsList in *.
generalize (Hcons (currentPartition s) Hcur ); clear Hcons; intros Hcons.
generalize (Hcons  sh1idx); clear Hcons; intro Hpdtmp.
assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/ sh1idx = sh3idx
 \/  sh1idx  = PPRidx \/  sh1idx  = PRidx)  
as Hpd by auto.
apply Hpdtmp in Hpd.
clear Hpdtmp. 
unfold partitionDescriptorEntry in Hpd.
destruct Hpd as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
repeat split; try assumption.
unfold nextEntryIsPP in Hpp; rewrite Hidxsucc in Hpp.
destruct (lookup (currentPartition s) idxsucc (memory s) beqPage beqIndex); try now contradict Hpp.
destruct v; try now contradict Hpp.
rewrite Hpp; trivial.
Qed.

Lemma getFstShadow1 (partition : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ 
In partition (getPartitions multiplexer s)  }} 
Internal.getFstShadow partition
{{fun (sh1 : page) (s : state) => P s /\ nextEntryIsPP partition sh1idx sh1 s }}.
Proof.
unfold Internal.getFstShadow.
eapply WP.bindRev.
(** getPDidx **)
apply getSh1idx.
intro idxSh1. 
simpl. 
(** MALInternal.Index.succ **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Index.succ.
intros. simpl.
split.
pattern s in H. 
eapply H.
subst.
intuition. subst.
unfold partitionDescriptorEntry in *.
unfold currentPartitionInPartitionsList in *.
generalize (H0 partition H3); clear H0; intros H0.
assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/ sh1idx = sh3idx 
\/  sh1idx  = PPRidx \/  sh1idx  = PRidx ) as Htmp by auto.
generalize (H0 sh1idx Htmp); clear H0; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (((HP & Hpde & Hpr) &Hidx) & Hidxsucc).
subst.
unfold partitionDescriptorEntry in *.
apply Hpde with partition sh1idx in Hpr.
destruct Hpr as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
split.
unfold nextEntryIsPP in Hpp.
destruct (StateLib.Index.succ sh1idx);inversion Hidxsucc;subst. 
destruct (lookup partition idxsucc (memory s) beqPage beqIndex);
try now contradict Hpp.
destruct v ; try now contradict Hpp.
destruct page1;destruct p;simpl in *. 
do 2 f_equal.
inversion Hpp.
subst. 
f_equal.
apply proof_irrelevance.
split;trivial.
right;left;trivial.
Qed.

Lemma getConfigTablesLinkedList  (partition : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ 
In partition (getPartitions multiplexer s)  }} 
Internal.getConfigTablesLinkedList  partition
{{fun (LL : page) (s : state) => P s /\ nextEntryIsPP partition sh3idx LL s }}.
Proof.
unfold Internal.getConfigTablesLinkedList .
eapply WP.bindRev.
(** getPDidx **)
apply getSh3idx.
intro idxSh3. 
simpl. 
(** MALInternal.Index.succ **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Index.succ.
intros. simpl.
split.
pattern s in H. 
eapply H.
subst.
intuition. subst.
unfold partitionDescriptorEntry in *.
unfold currentPartitionInPartitionsList in *.
generalize (H0 partition H3); clear H0; intros H0.
assert (sh3idx = PDidx \/ sh3idx = sh1idx \/ sh3idx = sh2idx \/ sh3idx = sh3idx 
\/  sh3idx  = PPRidx \/  sh3idx  = PRidx ) as Htmp by auto.
generalize (H0 sh3idx Htmp); clear H0; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (((HP & Hpde & Hpr) &Hidx) & Hidxsucc).
subst.
unfold partitionDescriptorEntry in *.
apply Hpde with partition sh3idx in Hpr.
destruct Hpr as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
split.
unfold nextEntryIsPP in Hpp.
destruct (StateLib.Index.succ sh3idx);inversion Hidxsucc;subst. 
destruct (lookup partition idxsucc (memory s) beqPage beqIndex);
try now contradict Hpp.
destruct v ; try now contradict Hpp.
destruct page1;destruct p;simpl in *. 
do 2 f_equal.
inversion Hpp.
subst. 
f_equal.
apply proof_irrelevance.
split;trivial.
do 3 right;left;trivial.
Qed.


Lemma checkKernelMap  (va: vaddr) (P : state -> Prop): 
{{fun s => P s }} checkKernelMap va 
{{fun isk s => P s /\ (Nat.eqb Kidx (nth (length va - (nbLevel - 1 + 2)) va defaultIndex) ) = isk}}.
Proof.
unfold checkKernelMap.
eapply WP.bindRev.
eapply getKidx.
simpl.
intros kidx.
eapply WP.bindRev.
eapply WP.weaken.
eapply getNbLevel.
simpl. intros.
pattern s in H.
eapply H.
intro l.
eapply WP.bindRev.
eapply WP.weaken.
eapply getIndexOfAddr.
intros. simpl.
pattern s in H.
eapply H.
intros idx.
simpl.
eapply WP.weaken.
eapply WP.ret .
simpl.
intros.
unfold StateLib.getIndexOfAddr in *.
intuition.
rewrite <- H1.
unfold StateLib.getNbLevel in H2.
case_eq (gt_dec nbLevel 0);
intros; rewrite H in H2.
inversion H2.
destruct l.
simpl in *. subst.  reflexivity.
assert(0 < nbLevel) by apply nbLevelNotZero.
now contradict H4.  
Qed. 

Lemma checkVAddrsEqualityWOOffset (va1 va2 : vaddr) (level1 : level) (P : state -> Prop) : 
{{fun s => P s }} Internal.checkVAddrsEqualityWOOffset va1 va2 level1 
{{fun res s => P s /\ res = checkVAddrsEqualityWOOffset nbLevel va1 va2 level1 }}.
Proof.
unfold Internal.checkVAddrsEqualityWOOffset.
revert va1 va2 level1 P.
induction nbLevel;intros.
+ simpl. eapply WP.weaken.
  eapply WP.ret . intros. simpl.  split;trivial.
+ simpl.
(** getIndexOfAddr **)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply getIndexOfAddr.
  simpl.
  intros.
  eassumption.
  intros idx1.
(** getIndexOfAddr **)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply getIndexOfAddr.
  simpl.
  intros.
  pattern s in H. 
  eassumption.
  intros idx2.
(** MALInternal.Level.eqb **)
  eapply WP.bindRev. 
  eapply WP.weaken.
  eapply Level.eqb.
  simpl. intros.
  pattern s in H.
  eassumption.
(** test *)
  intros a; simpl.
  case_eq a;intros.
  - eapply WP.strengthen.
    eapply WP.weaken. 
    eapply Index.eqb.
    simpl; intros.
    pattern s in H0.
    eassumption. simpl.
    split; intuition.
    rewrite <- H3, H4.
    subst.     
    unfold StateLib.Index.eqb.
    trivial.
  - (** MALInternal.Level.pred **) 
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply Level.pred.
    intros; simpl.
    split. 
    pattern s in H0.
    eassumption.
    destruct H0.
    symmetry in H1.
    apply levelEqBEqNatFalse0  in H1. assumption.
    intros levelpred.
(** MALInternal.Index.eqb **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply Index.eqb.
    intros; simpl.
    pattern s in H0.
    eapply H0. 
    simpl in *.
    intros. 
    case_eq a0; intros.
    eapply WP.strengthen.
    generalize (IHn va1 va2 levelpred (fun s : state => ((((P s /\ StateLib.getIndexOfAddr va1 level1 = idx1) /\ 
    StateLib.getIndexOfAddr va2 level1 = idx2) /\
     false = StateLib.Level.eqb level1 fstLevel) /\ StateLib.Level.pred level1 = Some levelpred) /\ 
   true = StateLib.Index.eqb idx1 idx2 ) ); clear IHn; intros IHn.
    eapply IHn.
    simpl.
    intros; intuition. subst.
    rewrite <- H6.
    rewrite H5.
    unfold StateLib.Index.eqb in H4.   
    rewrite <- H4. trivial.
    eapply WP.weaken.
    eapply WP.ret .
    simpl.
    intros.
    intuition.
    rewrite <- H5.
    rewrite H4. 
    unfold StateLib.Index.eqb in H3.
    subst.
    rewrite <- H3; trivial.
Qed.

Lemma readPDflag (table : page) (idx : index) (P : state -> Prop) : 
{{ fun s => P s /\ isVE table idx s }} MAL.readPDflag table idx 
{{ fun (ispd : bool) (s : state) => P s /\  entryPDFlag table idx ispd s }}.
Proof.
eapply WP.weaken. 
apply WP.readPDflag .
simpl.
intros.
destruct H as (H & Hentry).
apply isVELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupEntryPDFlag;trivial.
Qed.

Lemma getParent (PR : page) (P : state -> Prop) :
{{fun s => P s /\ consistency s /\ In PR (getPartitions multiplexer s) }} Internal.getParent PR 
{{fun (parent : page) (s : state) => P s /\ nextEntryIsPP PR PPRidx parent s }}.
Proof.
unfold Internal.getParent.
eapply WP.bindRev.
(** getPDidx **)
apply getPPRidx.
intro idxppr. 
simpl. 
(** MALInternal.Index.succ **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Index.succ.
intros. simpl.
split.
pattern s in H. 
eapply H.
destruct H as ((H1 & H2 & H3) & H4). 
subst.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
unfold currentPartitionInPartitionsList in *.
destruct H2. 
generalize (H PR H3); clear H0; intros H0.
assert (PPRidx = PDidx \/ PPRidx= sh1idx \/ PPRidx = sh2idx 
\/ PPRidx = sh3idx \/ PPRidx = PPRidx \/ PPRidx = PRidx) as Htmp.
right. right. right. right. left. auto.
generalize (H0 PPRidx Htmp); clear H0; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (((HP & Hcons  & Hpr) &Hidx) & Hidxsucc).
subst.
unfold consistency in *.
unfold partitionDescriptorEntry in Hcons.
unfold currentPartitionInPartitionsList in *.
destruct Hcons as (Hcons & _).

generalize (Hcons PR Hpr ); clear Hcons; intros Hcons.
generalize (Hcons  PPRidx); clear Hcons; intro Hpdtmp.
assert (PPRidx = PDidx \/ PPRidx= sh1idx \/ PPRidx = sh2idx \/ 
PPRidx = sh3idx \/ PPRidx = PPRidx \/ PPRidx = PRidx) as Hpd. 
right. right. right. right. left. auto. 
apply Hpdtmp in Hpd.
clear Hpdtmp. 
unfold partitionDescriptorEntry in Hpd.
destruct Hpd as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
repeat split; try assumption.
unfold nextEntryIsPP in Hpp; rewrite Hidxsucc in Hpp.
destruct (lookup PR idxsucc (memory s) beqPage beqIndex); try now contradict Hpp.
destruct v; try now contradict Hpp.
rewrite Hpp; trivial.
Qed.

Lemma checkRights r w e P : 
{{ fun s => P s }} checkRights r w e {{ fun rights s => P s  }}.
Proof. 
unfold checkRights.
case_eq (r && w && e );
intros;
eapply WP.weaken. 
eapply WP.ret.
simpl; trivial.
intros; simpl.
eapply WP.ret.
simpl; trivial.
Qed.

Lemma checkIndexPropertyLTB (userIndex : userValue) (P : state -> Prop) :
{{ fun s => P s }} IAL.checkIndexPropertyLTB userIndex {{ fun b s => (P s /\ (Nat.ltb userIndex tableSize) = b)}}.
Proof.
eapply WP.weaken.
apply WP.checkIndexPropertyLTB.
simpl.
intros. split;trivial.
Qed.

Lemma userValueToIndex (userIndex : userValue) (P : state -> Prop) :
{{ fun s => P s /\ userIndex < tableSize}} IAL.userValueToIndex userIndex {{ fun b s => P s /\ b = (CIndex userIndex)}}.
Proof.
eapply WP.weaken.
apply WP.userValueToIndex.
simpl.
intros.
destruct H.
repeat split;trivial.
Qed.

Lemma readInterruptMask (calleeVidt : page) (P : state -> Prop) :
{{ fun s => P s}} IAL.readInterruptMask calleeVidt {{ fun _ s => P s}}.
Proof.
eapply WP.weaken.
apply WP.readInterruptMask.
simpl.
trivial.
Qed.

Lemma isInterruptMasked (interruptMask : interruptMask) (targetInterrupt : index) (P : state -> Prop)  :
{{fun s => P s}}
IAL.isInterruptMasked interruptMask targetInterrupt
{{fun _ s => P s}}.
Proof.
eapply WP.weaken.
apply WP.isInterruptMasked.
simpl.
trivial.
Qed.

(*
Lemma readUserlandVAddr  (paddr : page) ( idx : index) (P : state -> Prop) :
{{fun s => P s}}
readUserlandVAddr paddr idx
{{fun vaddr s => P s}}.
Proof.
eapply WP.weaken.
apply WP.readUserlandVAddr.
simpl.
intros.
case_eq (lookup paddr idx (memory s) beqPage beqIndex); intros; try assumption.
case_eq v; intros; assumption.
Qed.
*)

Lemma getNthVAddrFrom (va : vaddr) (n : nat) (P : state -> Prop) :
{{fun s => P s}}
IAL.getNthVAddrFrom va n
{{fun _ s => P s}}.
Proof.
eapply WP.weaken.
apply WP.getNthVAddrFrom.
cbn.
trivial.
Qed.

Lemma firstVAddrGreaterThanSecond (first second : vaddr) (P : state -> Prop):
{{fun s => P s}}
IAL.firstVAddrGreaterThanSecond first second
{{fun _ s => P s}}.
Proof.
eapply WP.weaken.
apply WP.firstVAddrGreaterThanSecond.
cbn.
trivial.
Qed.

Lemma writeContext (callingContextAddr : contextAddr) (contextSaveAddr : vaddr) (flagsOnWake : interruptMask)
(P : state -> Prop) :
{{fun s => P s}}
IAL.writeContext callingContextAddr contextSaveAddr flagsOnWake
{{fun _ s => P s}}.
Proof.
eapply WP.weaken.
apply WP.writeContext.
cbn.
trivial.
Qed.

Lemma setInterruptMask (vidt : page) (mask : interruptMask)
(P : state -> Prop) :
{{fun s => P s}}
IAL.setInterruptMask vidt mask
{{fun _ s => P s}}.
Proof.
eapply WP.weaken.
apply WP.setInterruptMask.
cbn.
trivial.
Qed.
