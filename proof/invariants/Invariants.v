(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2024)                *)
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
    In this file we formalize and prove all invariants of the MAL and Ops functions *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.IAL Pip.Model.Lib
               Pip.Model.MAL.
Require Import Pip.Core.Internal Pip.Core.Services.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas
               Pip.Proof.Isolation Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Coq.Logic.ProofIrrelevance Lia Setoid Compare_dec EqNat List Bool.

Module WP := WeakestPreconditions.
Lemma getPageRootPartition (P : state -> Prop) :
{{ fun s => P s  }} Constants.getPageRootPartition
{{ fun val s => P s /\ val = pageRootPartition }}.
Proof.
   eapply WP.weaken.
   eapply WP.getPageRootPartition .
   intros.
   cbn. intuition.
Qed.


Lemma getKidx (P : state -> Prop) :
{{ fun s => P s  }} getIdxKernel 
{{ fun idx s => P s /\ idxKernel = idx }}.
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
{{fun s => P s }} getIdxPageDir
{{fun (idxPD : index) (s : state) => P s  /\ idxPD = idxPageDir }}.
Proof.
eapply WP.weaken. 
eapply WP.getPDidx . cbn.
intros. 
intuition.
Qed.
Lemma getSh1idx P :
{{fun s => P s }} getIdxShadow1
{{fun (idxSh1 : index) (s : state) => P s  /\ idxSh1 = idxShadow1 }}.
Proof.
eapply WP.weaken. 
eapply WP.getSh1idx . cbn.
intros. 
intuition.
Qed.

Lemma getSh2idx P :
{{fun s => P s }} getIdxShadow2
{{fun (idxSh2 : index) (s : state) => P s  /\ idxSh2 = idxShadow2 }}.
Proof.
eapply WP.weaken. 
eapply WP.getSh2idx . cbn.
intros. 
intuition.
Qed.

Lemma getSh3idx P :
{{fun s => P s }} getIdxShadow3
{{fun (idxsh3 : index) (s : state) => P s  /\ idxsh3 = idxShadow3 }}.
Proof.
eapply WP.weaken. 
eapply WP.getSh3idx . cbn.
intros. 
intuition.
Qed.

Lemma getPPRidx P :
{{fun s => P s }} getIdxParentDesc
{{fun (idxPPR : index) (s : state) => P s  /\ idxPPR = idxParentDesc }}.
Proof.
eapply WP.weaken. 
eapply WP.getPPRidx . cbn.
intros. 
intuition.
Qed.

Lemma getPRidx P :
{{fun s => P s }} getIdxPartDesc
{{fun (idxPR : index) (s : state) => P s  /\ idxPR = idxPartDesc }}.
Proof.
eapply WP.weaken. 
eapply WP.getPRidx . cbn.
intros. 
intuition.
Qed.

Module Index. 
Lemma eqb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} idxEqM index1 index2 
{{ fun b s => P s /\ b = idxEq index1 index2}}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.Index.eqb .
intros. simpl. split;trivial.
Qed.

Lemma gtb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} idxGtM index1 index2
{{ fun b s => P s /\ b = idxGt index1 index2 }}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.Index.gtb .
intros. simpl. split;trivial.
Qed.

Lemma ltb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} idxLtM index1 index2 
{{ fun b s => P s /\ b = idxLt index1 index2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.ltb.
intros. simpl. split;trivial.
Qed.

Lemma leb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} idxLeM index1 index2 
{{ fun b s => P s /\ b = idxLe index1 index2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.leb.
intros. simpl. split;trivial.
Qed.

Lemma geb index1 index2 (P : state -> Prop):
{{ fun s : state => P  s }} idxGeM index1 index2 
{{ fun b s => P s /\ b = idxGe index1 index2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.geb.
intros. simpl. split;trivial.
Qed.

Lemma zero P :
{{fun s => P s }} getIdx0 
{{fun (idx0 : index) (s : state) => P s  /\ idx0 = CIndex 0 }}.
Proof.
unfold getIdx0.
eapply WP.weaken.
eapply WP.ret .
intros. simpl.
intuition.
Qed.

Lemma succ (idx : index ) P :
{{fun s => P s  /\ idx < tableSize - 1}} idxSuccM idx 
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
{{fun s => P s  /\ idx > 0}} idxPredM idx 
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
{{ fun s : state => P s }} levelGtM level1 level2 
{{ fun b s => P s /\ b = levelGt level1 level2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Level.gtb.
intros. simpl. split;trivial.
Qed.

Lemma pred (level1 : level ) P :
{{fun s => P s  /\ level1 > 0 }} levelPredM level1
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
{{ fun s : state => P s }} levelEqM level1 level2 
{{ fun b s => P s /\  b = levelEq level1 level2 }}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.Level.eqb .
intros; simpl; split;trivial.
Qed.
End Level.

Module Page. 
Lemma eqb page1 page2 (P : state -> Prop):
{{ fun s : state => P s }} pageEqM page1 page2 
{{ fun b s => P s /\ b = pageEq page1 page2}}.
Proof.
eapply WP.weaken.
eapply WP.Page.eqb .
intros. simpl. split;trivial.
Qed.
End Page.

Module VAddr. 
Lemma eqbList vaddr1 vaddr2 (P : state -> Prop):
{{ fun s : state => P s }} vaddrEqM vaddr1 vaddr2 
{{ fun b s => P s /\ b = vaddrEq vaddr1 vaddr2}}.
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
destruct (lookup table idx (memory s) pageEq idxEq); try now contradict Hpage.
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
destruct (lookup table idx (memory s) pageEq idxEq); try now contradict Hpage.
destruct v; try now contradict Hpage.
eexists;repeat split;trivial.
Qed.


Lemma getDefaultPage P : 
{{fun s => P s}} getPageDefault
{{fun nullp s => P s /\ nullp = pageDefault}}.
Proof.
unfold getPageDefault.
eapply WP.weaken.
eapply WP.ret .
intros.
simpl. intuition.
Qed.  

Lemma getDefaultVAddr P : 
{{fun s => P s}} getVaddrDefault 
{{fun nullv s => P s /\ nullv = vaddrDefault }}.
Proof.
unfold getVaddrDefault.
eapply WP.weaken.
eapply WP.ret .
intros.
simpl. intuition.
Qed.

Lemma removeDupIdentity  (l :  list (paddr * value)) : 
forall table1 idx1 table2 idx2 , table1 <> table2 \/ idx1 <> idx2 -> 
lookup table1 idx1 (removeDup table2 idx2 l  pageEq idxEq) pageEq idxEq = 
lookup table1 idx1 l pageEq idxEq.
Proof.
intros.
induction l.
simpl. trivial.
simpl.
destruct a.
destruct p.
apply beqPairsFalse in H.
+ case_eq (beqPairs (p, i) (table2, idx2) pageEq idxEq).
  - intros.
    unfold beqPairs in H0. cbn in H0.
    case_eq (pageEq p table2 && idxEq i idx2 ).
    * intros.
      rewrite H1 in H0.
      unfold pageEq , idxEq in H1.
      apply andb_true_iff in H1.
      destruct H1.
      apply beq_nat_true in H1.
      apply beq_nat_true in H2.
      assert (beqPairs (p, i) (table1, idx1) pageEq idxEq = false).
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
    case_eq (beqPairs (p, i) (table1, idx1) pageEq idxEq).
    intros. trivial.
    intros. assumption.   
Qed.

Lemma isPPLookupEq table idx res s:
isPP' table idx res s -> lookup table idx (memory s) pageEq idxEq = Some (PP res).
Proof.
intros.
unfold isPP' in *.
destruct (lookup table idx (memory s) pageEq idxEq); try now contradict H.
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
{{fun (isnull : bool) (s : state) => P s /\ (Nat.eqb pageDefault page1) = isnull }}. 
Proof.
unfold Internal.comparePageToNull.
eapply WP.bindRev.
+ unfold getPageDefault.
  eapply WP.weaken.  
  eapply WP.ret . intros.  
  instantiate (1:= fun nullP s => P s /\ pageDefault = nullP ).
  simpl.
  intuition.
+ intro nullP. unfold pageEqM. simpl.
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
  lookup table idx (memory s) pageEq idxEq = Some (PE entry).
Proof.
intros.  
unfold isPE in H.
destruct (lookup table idx (memory s) pageEq idxEq); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
Qed.


Lemma lookupEntryPresentFlag table idx s : 
forall entry , lookup table idx (memory s) pageEq idxEq = Some (PE entry) -> 
entryPresentFlag table idx (present entry) s. 
Proof.
intros.
unfold entryPresentFlag.
rewrite H;trivial.
Qed.

Lemma lookupEntryPDFlag table idx s : 
forall entry , lookup table idx (memory s) pageEq idxEq = Some (VE entry) -> 
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
forall entry , lookup table idx (memory s) pageEq idxEq = Some (PE entry) -> 
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
 isVE table idx s  -> exists entry ,lookup table idx (memory s) pageEq idxEq = Some (VE entry) . 
Proof.
intros.
unfold isVE in H.
destruct (lookup table idx (memory s) pageEq idxEq); try now contradict H.
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
destruct (lookup table idx (memory s) pageEq idxEq); try now contradict Hva.
destruct v; try now contradict Hva.
eexists;repeat split;trivial.
Qed.

Lemma compareVAddrToNull (va : vaddr) (P : state -> Prop): 
{{fun s => P s }} compareVAddrToNull va 
{{fun (isnull : bool) (s : state) => P s /\ 
                                       (vaddrEq vaddrDefault va) = isnull }}. 
Proof.
unfold compareVAddrToNull.
eapply WP.bindRev.
+ unfold getVaddrDefault.
  eapply WP.weaken.  
  eapply WP.ret . intros.  
  instantiate (1:= fun nullVa s => P s /\ vaddrEq vaddrDefault nullVa = true ).
  simpl.
  intuition.
  unfold vaddrEq.
  destruct vaddrDefault.
  simpl.
  clear Hva. 
  induction va0. simpl. trivial.
  simpl. 
  unfold idxEq.
  case_eq(Nat.eqb a a); intros.
  apply IHva0.
  apply beq_nat_false in H0. lia.
+ intro nullva. simpl.
  unfold vaddrEqM. simpl.
  eapply WP.weaken. eapply WP.ret . intros. 
  simpl. intuition.
  f_equal.
  unfold vaddrEq in *.
   
  destruct vaddrDefault , nullva.
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
  case_eq( idxEq a i ); intros;
  rewrite H in H1.
  unfold idxEq in H.
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
{{ fun (isderived : bool) (s : state) => P s /\ exists va, isEntryVA table idx va s /\  vaddrEq vaddrDefault va = isderived }}.
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
destruct (lookup table idx (memory s) pageEq idxEq); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
Qed.

Lemma getPd (PR : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In PR (getPartitions pageRootPartition s) }} 
                      Internal.getPd PR 
{{fun (pd : page) (s : state) => P s /\ nextEntryIsPP PR idxPageDir pd s 
                                             }}.
Proof.
unfold Internal.getPd.
eapply WP.bindRev.
(** getPDidx **)
apply getPDidx.
intro idxPD. 
simpl. 
(* idxSuccM *)
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
assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2 
\/ idxPageDir = idxShadow3 \/ idxPageDir = idxParentDesc \/ idxPageDir = idxPartDesc ) as Htmp by auto.
generalize (Hdescr idxPageDir Htmp); clear Hdescr; intros H0.
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

generalize (Hcons  idxPageDir); clear Hcons; intro Hpdtmp.
assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2 \/ idxPageDir = idxShadow3  \/ idxPageDir = idxParentDesc \/ idxPageDir = idxPartDesc ) 
as Hpd by auto.
apply Hpdtmp in Hpd.
clear Hpdtmp. 
unfold partitionDescriptorEntry in Hpd.
destruct Hpd as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
exists page1.
repeat split; try assumption.
unfold nextEntryIsPP in Hpp; rewrite Hidxsucc in Hpp.
destruct (lookup PR idxsucc (memory s) pageEq idxEq); try now contradict Hpp.
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
destruct (lookup table idx (memory s) pageEq idxEq); try now contradict Hpage.
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
destruct (lookup table idx (memory s) pageEq idxEq); try now contradict Hpage.
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
destruct (lookup table idx (memory s) pageEq idxEq);
[destruct v|]; split;trivial.
Qed.

Lemma getSndShadow (PR : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In PR (getPartitions pageRootPartition s) }} Internal.getSndShadow PR 
{{fun (sh2 : page) (s : state) => P s /\ nextEntryIsPP PR idxShadow2 sh2 s }}.
Proof.
unfold Internal.getSndShadow.
eapply WP.bindRev.
(** getSh2idx **)
apply getSh2idx.
intro idxSh2. 
simpl. 
(* idxSuccM *)
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
assert (idxShadow2 = idxPageDir \/ idxShadow2 = idxShadow1 \/ idxShadow2 = idxShadow2 \/ idxShadow2 = idxShadow3 
\/  idxShadow2  = idxParentDesc \/  idxShadow2  = idxPartDesc ) as Htmp by auto.
generalize (H0 idxShadow2 Htmp); clear H0; intros H0.
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
generalize (Hcons  idxShadow2); clear Hcons; intro Hpdtmp.
assert (idxShadow2 = idxPageDir \/ idxShadow2 = idxShadow1 \/ idxShadow2 = idxShadow2 \/ idxShadow2 = idxShadow3 \/  idxShadow2  = idxParentDesc
 \/  idxShadow2  = idxPartDesc)  
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
destruct (lookup PR idxsucc (memory s) pageEq idxEq); try now contradict Hpp.
destruct v; try now contradict Hpp.
rewrite Hpp; trivial.
Qed.

Lemma getFstShadow (PR : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ currentPartitionInPartitionsList s /\  PR = currentPartition s}} Internal.getFstShadow PR 
{{fun (sh1 : page) (s : state) => P s /\ nextEntryIsPP PR idxShadow1 sh1 s }}.
Proof.
unfold Internal.getFstShadow.
eapply WP.bindRev.
(** getPDidx **)
apply getSh1idx.
intro idxSh1. 
simpl. 
(* idxSuccM *)
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
assert (idxShadow1 = idxPageDir \/ idxShadow1 = idxShadow1 \/ idxShadow1 = idxShadow2 \/ idxShadow1 = idxShadow3 
\/  idxShadow1  = idxParentDesc \/  idxShadow1  = idxPartDesc ) as Htmp by auto.
generalize (H0 idxShadow1 Htmp); clear H0; intros H0.
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
generalize (Hcons  idxShadow1); clear Hcons; intro Hpdtmp.
assert (idxShadow1 = idxPageDir \/ idxShadow1 = idxShadow1 \/ idxShadow1 = idxShadow2 \/ idxShadow1 = idxShadow3
 \/  idxShadow1  = idxParentDesc \/  idxShadow1  = idxPartDesc)  
as Hpd by auto.
apply Hpdtmp in Hpd.
clear Hpdtmp. 
unfold partitionDescriptorEntry in Hpd.
destruct Hpd as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
repeat split; try assumption.
unfold nextEntryIsPP in Hpp; rewrite Hidxsucc in Hpp.
destruct (lookup (currentPartition s) idxsucc (memory s) pageEq idxEq); try now contradict Hpp.
destruct v; try now contradict Hpp.
rewrite Hpp; trivial.
Qed.

Lemma getFstShadow1 (partition : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ 
In partition (getPartitions pageRootPartition s)  }} 
Internal.getFstShadow partition
{{fun (sh1 : page) (s : state) => P s /\ nextEntryIsPP partition idxShadow1 sh1 s }}.
Proof.
unfold Internal.getFstShadow.
eapply WP.bindRev.
(** getPDidx **)
apply getSh1idx.
intro idxSh1. 
simpl. 
(* idxSuccM *)
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
assert (idxShadow1 = idxPageDir \/ idxShadow1 = idxShadow1 \/ idxShadow1 = idxShadow2 \/ idxShadow1 = idxShadow3 
\/  idxShadow1  = idxParentDesc \/  idxShadow1  = idxPartDesc ) as Htmp by auto.
generalize (H0 idxShadow1 Htmp); clear H0; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (((HP & Hpde & Hpr) &Hidx) & Hidxsucc).
subst.
unfold partitionDescriptorEntry in *.
apply Hpde with partition idxShadow1 in Hpr.
destruct Hpr as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
split.
unfold nextEntryIsPP in Hpp.
destruct (StateLib.Index.succ idxShadow1);inversion Hidxsucc;subst. 
destruct (lookup partition idxsucc (memory s) pageEq idxEq);
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
In partition (getPartitions pageRootPartition s)  }} 
Internal.getConfigTablesLinkedList  partition
{{fun (LL : page) (s : state) => P s /\ nextEntryIsPP partition idxShadow3 LL s }}.
Proof.
unfold Internal.getConfigTablesLinkedList .
eapply WP.bindRev.
(** getPDidx **)
apply getSh3idx.
intro idxSh3. 
simpl. 
(* idxSuccM *)
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
assert (idxShadow3 = idxPageDir \/ idxShadow3 = idxShadow1 \/ idxShadow3 = idxShadow2 \/ idxShadow3 = idxShadow3 
\/  idxShadow3  = idxParentDesc \/  idxShadow3  = idxPartDesc ) as Htmp by auto.
generalize (H0 idxShadow3 Htmp); clear H0; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (((HP & Hpde & Hpr) &Hidx) & Hidxsucc).
subst.
unfold partitionDescriptorEntry in *.
apply Hpde with partition idxShadow3 in Hpr.
destruct Hpr as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
split.
unfold nextEntryIsPP in Hpp.
destruct (StateLib.Index.succ idxShadow3);inversion Hidxsucc;subst. 
destruct (lookup partition idxsucc (memory s) pageEq idxEq);
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
{{fun isk s => P s /\ (Nat.eqb idxKernel (nth (length va - (nbLevel - 1 + 2)) va idxDefault) ) = isk}}.
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
(* levelEqM *)
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
    unfold idxEq.
    trivial.
  - (* levelPredM *)
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
(* idxEqM *)
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
     false = levelEq level1 levelMin) /\ StateLib.Level.pred level1 = Some levelpred) /\ 
   true = idxEq idx1 idx2 ) ); clear IHn; intros IHn.
    eapply IHn.
    simpl.
    intros; intuition. subst.
    rewrite <- H6.
    rewrite H5.
    unfold idxEq in H4.   
    rewrite <- H4. trivial.
    eapply WP.weaken.
    eapply WP.ret .
    simpl.
    intros.
    intuition.
    rewrite <- H5.
    rewrite H4. 
    unfold idxEq in H3.
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
{{fun s => P s /\ consistency s /\ In PR (getPartitions pageRootPartition s) }} Internal.getParent PR 
{{fun (parent : page) (s : state) => P s /\ nextEntryIsPP PR idxParentDesc parent s }}.
Proof.
unfold Internal.getParent.
eapply WP.bindRev.
(** getPDidx **)
apply getPPRidx.
intro idxppr. 
simpl. 
(* idxSuccM *)
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
assert (idxParentDesc = idxPageDir \/ idxParentDesc= idxShadow1 \/ idxParentDesc = idxShadow2 
\/ idxParentDesc = idxShadow3 \/ idxParentDesc = idxParentDesc \/ idxParentDesc = idxPartDesc) as Htmp.
right. right. right. right. left. auto.
generalize (H0 idxParentDesc Htmp); clear H0; intros H0.
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
generalize (Hcons  idxParentDesc); clear Hcons; intro Hpdtmp.
assert (idxParentDesc = idxPageDir \/ idxParentDesc= idxShadow1 \/ idxParentDesc = idxShadow2 \/ 
idxParentDesc = idxShadow3 \/ idxParentDesc = idxParentDesc \/ idxParentDesc = idxPartDesc) as Hpd. 
right. right. right. right. left. auto. 
apply Hpdtmp in Hpd.
clear Hpdtmp. 
unfold partitionDescriptorEntry in Hpd.
destruct Hpd as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
repeat split; try assumption.
unfold nextEntryIsPP in Hpp; rewrite Hidxsucc in Hpp.
destruct (lookup PR idxsucc (memory s) pageEq idxEq); try now contradict Hpp.
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

Lemma setInterruptMask (mask : interruptMask)
(P : state -> Prop) :
{{fun s => P s}}
IAL.setInterruptMask mask
{{fun _ s => P s}}.
Proof.
eapply WP.weaken.
apply WP.setInterruptMask.
cbn.
trivial.
Qed.

Lemma updateMMURoot (MMURoot : page)
(P : state -> Prop) :
{{fun s => P s}}
IAL.updateMMURoot MMURoot
{{fun _ s => P s}}.
Proof.
eapply WP.weaken.
apply WP.updateMMURoot.
cbn.
trivial.
Qed.

Lemma getInterruptMaskFromCtx (context : contextAddr)
(P : state -> Prop) :
{{fun s => P s}}
IAL.getInterruptMaskFromCtx context
{{fun _ s => P s}}.
Proof.
eapply WP.weaken.
apply WP.getInterruptMaskFromCtx.
cbn.
trivial.
Qed.

Lemma noInterruptRequest (flags : interruptMask)
(P: state -> Prop) :
{{fun s => P s}}
IAL.noInterruptRequest flags
{{fun _ s => P s}}.
Proof.
eapply WP.weaken.
apply WP.noInterruptRequest.
cbn.
trivial.
Qed.

Lemma vaddrToContextAddr (contextVAddr : vaddr)
(P: state -> Prop) :
{{fun s => P s}}
IAL.vaddrToContextAddr contextVAddr
{{fun _ s => P s}}.
Proof.
eapply WP.weaken.
apply WP.vaddrToContextAddr.
cbn.
trivial.
Qed.

Lemma loadContext (contextToLoad : contextAddr) (enforce_interrupt : bool)
(P : state -> Prop) :
{{fun s => P s}}
IAL.loadContext contextToLoad enforce_interrupt
{{fun _ s => P s}}.
Proof.
eapply WP.weaken.
apply WP.loadContext.
cbn.
trivial.
Qed.

Lemma getVaddrVIDT (P : state -> Prop) :
{{ fun s => P s  }} Constants.getVaddrVIDT
{{ fun val s => P s /\ val = vaddrVIDT }}.
Proof.
   eapply WP.weaken.
   eapply WP.getVaddrVIDT.
   intros.
   cbn. intuition.
Qed.
