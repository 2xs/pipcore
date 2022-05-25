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
    This file contains required lemmas to prove the [writeAccessibleRec] invariants used to prove the prepare service *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL Pip.Model.Constants Pip.Model.Ops.
Require Import Pip.Core.Internal.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.InternalLemmas
Pip.Proof.Isolation Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Invariants GetTableAddr Lib WriteAccessible WriteAccessibleFalse PropagatedProperties.
Import Coq.Logic.ProofIrrelevance Lia List EqNat.
Import List.ListNotations.
(************************* MOVE into InternalLemmas ****************************)

(*****************************************************************************)

 
Lemma WriteAccessibleRecSchema (va:vaddr) (descParent phypage pt:page) currentPart :  
{{ fun s : state => writeAccessibleRecRecurtionInvariantConj va descParent phypage pt currentPart s }} 
Internal.writeAccessibleRecAux (nbPage +1) va descParent false
{{ fun res  s  => True }}.
Proof.
unfold writeAccessibleRecRecurtionInvariantConj.
 revert va descParent  pt phypage .
induction (nbPage + 1).
intros;simpl.
eapply weaken.
eapply WP.ret. simpl.
(** PROVE YOUR POSTCONDITION : True **)
intuition.  
intros.
simpl.
eapply bindRev.
(** getPageRootPartition **)
eapply weaken.
eapply Invariants.getPageRootPartition.
intros; simpl.
pattern s in H.
eapply H.
simpl. 
intros multiplexer.
eapply bindRev.
(** Page.eqb **)
eapply weaken.
eapply Invariants.Page.eqb.
simpl.
intros.
pattern s in H.
eapply H.
simpl.
intros isMultiplexer.
case_eq isMultiplexer.
(** case_eq isMultiplexer true **)
+ intros isMultiplexerT.
  (** ret **)
  eapply weaken.
  eapply WP.ret.
  intros;trivial.
  simpl;trivial. (* admit.  *) (** PROVE YOUR POSTCONDITION : true **)
(** case_eq isMultiplexer false **)
+ intros isMultiplexerF.
  eapply bindRev.
  (** getSndShadow **)
  eapply weaken.
  eapply Invariants.getSndShadow.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
 unfold consistency in H;intuition.
 (** In descParent (getPartitions MALInternal.multiplexer s)**)
  intros sh2; simpl.
  eapply bindRev.
  (** getNbLevel **)
  eapply weaken.
  eapply Invariants.getNbLevel.
  intros; simpl.
  pattern s in H.
  eapply H.
  intros L; simpl. 
  (** getIndexOfAddr **) 
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getIndexOfAddr.
  simpl; intros.
  pattern s in H.
  eapply H.
  intros lastIndex.
  simpl.
  (** getTableAddr **)
  eapply bindRev.
  eapply weaken.
  eapply GetTableAddr.getTableAddr with (currentPart:= descParent) (idxroot:= idxShadow2).
  simpl. 
  intros.
  split.
  pattern s in H.
  eapply H.
  split.
  intuition.
  split.
  intuition.
  split. 
  intuition.
  exists sh2.
  split. intuition.
  split.
  apply sh2PartNotNull with descParent s;intuition.
  unfold consistency in *;intuition.
  left; split; intuition.
  intros ptsh2. simpl.  
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2:{
  intros.
  destruct H as (H0 & H1).
  assert( (getTableAddrRoot' ptsh2 idxShadow2 descParent va s /\ ptsh2 = pageDefault) \/
  (  isVA ptsh2 (StateLib.getIndexOfAddr va levelMin ) s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s)).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right.
      destruct H1 as (Hget  & Hnew & H1).
      generalize (H1 (StateLib.getIndexOfAddr va levelMin ) );clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(Hpe &Htrue) | (_&Hfalse)]];trivial.
       - contradict Hfalse.
         apply idxSh2idxSh1notEq.
      - split;trivial.
      - contradict Hfalse.
        symmetrynot.
        apply idxPDidxSh2notEq.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP. } 
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptsh2Isnull. simpl.
  case_eq ptsh2Isnull.
  intros.
  eapply WP.weaken.
  eapply WP.ret .
  intros;trivial.
  simpl;trivial. (* admit.  *) (** PROVE YOUR POSTCONDITION : true **)
  intros Hptsh2NotNull.
  (** readVirtual **)
  eapply bindRev. 
  eapply weaken.
  2: {  
  intros.
  destruct H as ((H & Hstrong) & Htrue).
  assert(Heqv:  (isVA ptsh2 (StateLib.getIndexOfAddr va levelMin) s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s)).
  { destruct Hstrong as [Hor|Hor].   
    assert(Hfalse: (Nat.eqb pageDefault pageDefault) = false) by (intuition;subst;trivial).
    apply beq_nat_false in Hfalse.
    now contradict Hfalse.
    intuition; subst;trivial. }
  clear Hstrong.
  assert (Hnew:= conj (conj H Heqv) Htrue).
  eapply Hnew. }
  eapply weaken.
  eapply Invariants.readVirtual.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
  subst.
  intuition;
  subst;trivial.
  intros vaInAncestor.
  simpl.
  subst.
  (** getParent **)
  eapply bindRev.
  eapply weaken. 
  eapply Invariants.getParent.
  intros.
  simpl. 
  split.
  pattern s in H.
  eapply H.
  unfold propagatedProperties in *.  
  intuition.
  intros ancestor; simpl.
  (** getPd **)
   eapply bindRev.
  eapply weaken.
  eapply Invariants.getPd.
  simpl; intros.
  split.
  pattern s in H.
  eapply H. split.
  unfold propagatedProperties in H.
  unfold consistency in H.
  intuition.
  destruct H.
  unfold propagatedProperties in H.
  assert (Hparent:  parentInPartitionList s) by (unfold consistency in *;  intuition).
  unfold parentInPartitionList in *.
  apply Hparent with descParent; intuition.
    intros pdAncestor. 
(** setAccessible **)
  unfold setAccessible.
  eapply bindRev.
  (** getDefaultVAddr **)
  eapply weaken.
  eapply Invariants.getDefaultVAddr.
  simpl.
  intros.
  pattern s in H.
  eapply H.
  intros defaultV.
  simpl.
  eapply bindRev.
  (**   VAddr.eqbList **)
  eapply weaken.
  eapply Invariants.VAddr.eqbList.
  simpl.
  intros.
  pattern s in H.
  eapply H.
  intros isdefaultVA.
  (** case negb isdefaultVA **)
  case_eq (isdefaultVA).
  intros.
  eapply weaken.
  eapply WP.ret.
  intros;trivial.
  simpl;trivial. (* admit.  *) (** PROVE YOUR POSTCONDITION : true **)
  intros isdefaultVAT.
  eapply bindRev.
  (** getTableAddr **)
  eapply WP.weaken. 
  apply getTableAddr with (currentPart:= ancestor) (idxroot:= idxPageDir).
  simpl.
  intros s H.
  split.
  pattern s in H. 
  eapply H.
  assert(Hancestor: In ancestor (getPartitions pageRootPartition s)).
  { assert(Hparent : parentInPartitionList s) by (unfold consistency in *;intuition).
    apply Hparent with descParent; intuition. }
  split;[intuition|].
  split;[intuition|].      
  split;[intuition|].
  exists pdAncestor.
  split. intuition.
  split.
  apply pdPartNotNull with ancestor s;trivial. 
  intuition.
  unfold consistency in *.
  intuition.
  subst. left. split;intuition.
  intro ptvaInAncestor. simpl.
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2:{
  intros.
  destruct H as (H0 & H1).
  assert( (getTableAddrRoot' ptvaInAncestor idxPageDir ancestor vaInAncestor s /\ ptvaInAncestor = pageDefault) \/
   (isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) s /\ getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s)).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right.
      destruct H1 as (Hget  & Hnew & H1).
      split. 
      generalize (H1 (StateLib.getIndexOfAddr vaInAncestor levelMin ) );clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]];trivial.
       - contradict Hfalse.
         apply idxPDidxSh1notEq.
       - contradict Hfalse.
        apply idxPDidxSh2notEq.
       - assumption.  }  
  assert (HP :=conj H0 H).
  pattern s in HP.
  eapply HP. }
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptvaInAncestorIsnull. simpl.
  case_eq ptvaInAncestorIsnull.
  (** va not mapped in ancestor : ret false **)
  intros HptvaInAncestorIsnulll.
  eapply weaken.
  eapply WP.ret.
  intros;trivial.
  simpl;trivial. (* admit.  *) (** PROVE YOUR POSTCONDITION : true **)
  intros HptvaInAncestorIsnulll.
  (** va mapped in ancestor **)
  (** StateLib.getIndexOfAddr **)                
  eapply WP.bindRev.
  eapply WP.weaken.
  2:{ intros.
      destruct H as ((H & [(Hptchild& Hnull) | Hptchild] ) & Hptchildnotnull) .
    + subst.  apply beq_nat_false in Hptchildnotnull. intuition.
    + assert (HP := conj (conj H Hptchild) Hptchildnotnull).
      pattern s in HP.
      eapply HP.  }
  eapply weaken.
  apply Invariants.getIndexOfAddr.
  simpl;intros.
  eapply H.
  intros idxva.
  simpl.
  intros.
  eapply bindRev; simpl;[|intros []].
 (** writeAccessible **)
  eapply WP.weaken.
  eapply WP.writeAccessible.
  intros. simpl.
  assert (exists entry0 : Pentry,
    lookup ptvaInAncestor idxva (memory s) pageEq idxEq = Some (PE entry0)) as Hlookup.
  { apply isPELookupEq.
    intuition;subst;trivial. }
  destruct Hlookup as (entry & Hlookup).
  exists entry ; split;trivial. 
  repeat rewrite and_assoc in H.
  destruct H as ((* Hprecond & : YOUR precondition (if exists) to prove the postcondition *) Hfalse & Hrest). 
  (** prove that the same page is mapped in the parent and associated to the va stored into the second shadow structure **)
  assert(Heqphy : phypage = pa entry). {
  intuition;subst.
  apply isAccessibleMappedPageGetTableRoot with sh2 descParent ptsh2 va pdAncestor
  ancestor vaInAncestor ptvaInAncestor s;trivial. }
  (** prove that the page is accessible into the parent **)
  assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true). {
  assert(Hcons : consistency s) by (unfold propagatedProperties in *;intuition).
  subst.
  unfold consistency in Hcons.
  apply isAccessibleMappedPageInParentTrue with descParent va (pa entry) ptvaInAncestor ptsh2 pdAncestor;
  intuition;subst;trivial. }
  assert(Hx:= conj Htrue Hrest ).    
  assert(Hprecond :True) by trivial.  
  assert (H:= conj Hprecond Hx).
  pattern s in H.
  (** add the propeties about writeAccessible post conditions **)
  match type of H with 
  | ?HT s => instantiate (1 := fun tt s => HT s /\ 
              entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) false s /\
              isEntryPage ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) phypage s /\
              entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) true s  ) 
  end.
  simpl.
  set (s' := {| currentPartition := _ |}).  
  rewrite and_assoc.
  split. 
  simpl;trivial. (* admit.  *) (** PROVE YOUR POSTCONDITION : true **)
  intros;trivial.
   simpl in *.
  assert(Hmult : multiplexer = pageRootPartition) by intuition. 
  subst.
  assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartitions 
        by (apply getPartitionsUpdateUserFlag; trivial).
  (** Prove the POSTCONDITION **)
  (* admit *)
  (** Prove the recursion invariant **)
  apply WriteAccessibleRecRecursionInvariant.
  intuition;subst;trivial.
  unfold writeAccessibleRecInternalPropertiesPrepare;intuition;trivial.
(** RECURSION **)
  intros; simpl; subst.
  eapply weaken.
  eapply IHn with (phypage:= phypage) (pt:= ptvaInAncestor). 
  intros;intuition;subst;trivial.
  unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) by apply pageDecOrNot.
  destruct Hor as [Hor | Hor];[left;trivial|right].
  assert (His : isAncestor currentPart ancestor s).
  { unfold consistency in *;
    apply isAncestorTrans with descParent;intuition. 
    apply nextEntryIsPPgetParent;trivial. }
    unfold isAncestor in *;intuition.
  assert(Hpp :nextEntryIsPP descParent idxParentDesc ancestor s); intuition.
  rewrite nextEntryIsPPgetParent in Hpp.
  unfold consistency in *.
  apply ancestorInPartitionTree with descParent;trivial.
  intuition. intuition.
  unfold getAncestors.
  destruct nbPage;simpl;  rewrite Hpp;
  simpl;left;trivial.
Qed. 

Lemma WriteAccessibleRecPropagatePrepareProperties currentPart pt phypage descParent va  ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
     currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child trdVA
     nextVA vaToPrepare sndVA fstVA (l nbLgen : level)idxFstVA idxSndVA idxTrdVA b1 b2 b3 zeroI LLroot LLChildphy newLastLLable minFI indMMUToPreparebool:
{{ fun s : state => 
(propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
     currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart  trdVA
     nextVA vaToPrepare sndVA fstVA nbLgen l  b1 b2 b3 true true true idxFstVA idxSndVA idxTrdVA zeroI minFI
     /\  isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA )
/\ writeAccessibleRecRecurtionInvariantConj va descParent phypage pt currentPart s 
}} 
Internal.writeAccessibleRecAux (nbPage +1) va descParent false
{{ fun _ s =>
   propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
     currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA
     nextVA vaToPrepare sndVA fstVA nbLgen l  b1 b2 b3 true true true idxFstVA idxSndVA idxTrdVA zeroI minFI
     /\ isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA}}.
Proof.
unfold writeAccessibleRecRecurtionInvariantConj.
 revert va descParent  pt phypage .
induction (nbPage + 1).
intros;simpl.
eapply weaken.
eapply WP.ret. simpl.
intuition.  
intros.
simpl.
eapply bindRev.
(** getPageRootPartition **)
eapply weaken.
eapply Invariants.getPageRootPartition.
intros; simpl.
pattern s in H.
eapply H.
simpl. 
intros multiplexer.
eapply bindRev.
(** Page.eqb **)
eapply weaken.
eapply Invariants.Page.eqb.
simpl.
intros.
pattern s in H.
eapply H.
simpl.
intros isMultiplexer.
case_eq isMultiplexer.
(** case_eq isMultiplexer true **)
+ intros isMultiplexerT.
  (** ret **)
  eapply weaken.
  eapply WP.ret.
  simpl;intros;trivial.
  intuition.  (** PROVE YOUR POSTCONDITION : propagatedPropertiesPrepare **)
(** case_eq isMultiplexer false **)
+ intros isMultiplexerF.
  eapply bindRev.
  (** getSndShadow **)
  eapply weaken.
  eapply Invariants.getSndShadow.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
 unfold consistency in H;intuition.
 (** In descParent (getPartitions MALInternal.multiplexer s)**)
  intros sh2; simpl.
  eapply bindRev.
  (** getNbLevel **)
  eapply weaken.
  eapply Invariants.getNbLevel.
  intros; simpl.
  pattern s in H.
  eapply H.
  intros L; simpl. 
  (** getIndexOfAddr **) 
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getIndexOfAddr.
  simpl; intros.
  pattern s in H.
  eapply H.
  intros lastIndex.
  simpl.
  (** getTableAddr **)
  eapply bindRev.
  eapply weaken.
  eapply GetTableAddr.getTableAddr with (currentPart:= descParent) (idxroot:= idxShadow2).
  simpl. 
  intros.
  split.
  pattern s in H.
  eapply H.
  split.
  intuition.
  split.
  intuition.
  split. 
  intuition.
  exists sh2.
  split. intuition.
  split.
  apply sh2PartNotNull with descParent s;intuition.
  unfold consistency in *;intuition.
  left; split; intuition.
  intros ptsh2. simpl.  
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2:{
  intros.
  destruct H as (H0 & H1).
  assert( (getTableAddrRoot' ptsh2 idxShadow2 descParent va s /\ ptsh2 = pageDefault) \/
  (  isVA ptsh2 (StateLib.getIndexOfAddr va levelMin ) s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s)).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right.
      destruct H1 as (Hget  & Hnew & H1).
      generalize (H1 (StateLib.getIndexOfAddr va levelMin ) );clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(Hpe &Htrue) | (_&Hfalse)]];trivial.
       - contradict Hfalse.
         apply idxSh2idxSh1notEq.
      - split;trivial.
      - contradict Hfalse.
        symmetrynot.
        apply idxPDidxSh2notEq.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP. } 
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptsh2Isnull. simpl.
  case_eq ptsh2Isnull.
  intros.
  eapply WP.weaken.
  eapply WP.ret .
  simpl. intros;trivial.
  intuition.  (** PROVE YOUR POSTCONDITION : propagatedPropertiesPrepare **)
  intros Hptsh2NotNull.
  (** readVirtual **)
  eapply bindRev. 
  eapply weaken.
  2: {  
  intros.
  destruct H as ((H & Hstrong) & Htrue).
  assert(Heqv:  (isVA ptsh2 (StateLib.getIndexOfAddr va levelMin) s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s)).
  { destruct Hstrong as [Hor|Hor].   
    assert(Hfalse: (Nat.eqb pageDefault pageDefault) = false) by (intuition;subst;trivial).
    apply beq_nat_false in Hfalse.
    now contradict Hfalse.
    intuition; subst;trivial. }
  clear Hstrong.
  assert (Hnew:= conj (conj H Heqv) Htrue).
  eapply Hnew. }
  eapply weaken.
  eapply Invariants.readVirtual.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
  subst.
  intuition;
  subst;trivial.
  intros vaInAncestor.
  simpl.
  subst.
  (** getParent **)
  eapply bindRev.
  eapply weaken. 
  eapply Invariants.getParent.
  intros.
  simpl. 
  split.
  pattern s in H.
  eapply H.
  unfold propagatedProperties in *.  
  intuition.
  intros ancestor; simpl.
  (** getPd **)
   eapply bindRev.
  eapply weaken.
  eapply Invariants.getPd.
  simpl; intros.
  split.
  pattern s in H.
  eapply H. split.
  unfold propagatedProperties in H.
  unfold consistency in H.
  intuition.
  destruct H.
  unfold propagatedProperties in H.
  assert (Hparent:  parentInPartitionList s) by (unfold consistency in *;  intuition).
  unfold parentInPartitionList in *.
  apply Hparent with descParent; intuition.
    intros pdAncestor. 
(** setAccessible **)
  unfold setAccessible.
  eapply bindRev.
  (** getDefaultVAddr **)
  eapply weaken.
  eapply Invariants.getDefaultVAddr.
  simpl.
  intros.
  pattern s in H.
  eapply H.
  intros defaultV.
  simpl.
  eapply bindRev.
  (**   VAddr.eqbList **)
  eapply weaken.
  eapply Invariants.VAddr.eqbList.
  simpl.
  intros.
  pattern s in H.
  eapply H.
  intros isdefaultVA.
  (** case negb isdefaultVA **)
  case_eq (isdefaultVA).
  intros.
  eapply weaken.
  eapply WP.ret.
  simpl. intros;trivial. 
  intuition. (** PROVE YOUR POSTCONDITION : propagatedPropertiesPrepare **)
  intros isdefaultVAT.
  eapply bindRev.
  (** getTableAddr **)
  eapply WP.weaken. 
  apply getTableAddr with (currentPart:= ancestor) (idxroot:= idxPageDir).
  simpl.
  intros s H.
  split.
  pattern s in H. 
  eapply H.
  assert(Hancestor: In ancestor (getPartitions pageRootPartition s)).
  { assert(Hparent : parentInPartitionList s) by (unfold consistency in *;intuition).
    apply Hparent with descParent; intuition. }
  split;[intuition|].
  split;[intuition|].      
  split;[intuition|].
  exists pdAncestor.
  split. intuition.
  split.
  apply pdPartNotNull with ancestor s;trivial. 
  intuition.
  unfold consistency in *.
  intuition.
  subst. left. split;intuition.
  intro ptvaInAncestor. simpl.
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2:{
  intros.
  destruct H as (H0 & H1).
  assert( (getTableAddrRoot' ptvaInAncestor idxPageDir ancestor vaInAncestor s /\ ptvaInAncestor = pageDefault) \/
   (isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) s /\ getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s)).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right.
      destruct H1 as (Hget  & Hnew & H1).
      split. 
      generalize (H1 (StateLib.getIndexOfAddr vaInAncestor levelMin ) );clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]];trivial.
       - contradict Hfalse.
         apply idxPDidxSh1notEq.
       - contradict Hfalse.
        apply idxPDidxSh2notEq.
       - assumption.  }  
  assert (HP :=conj H0 H).
  pattern s in HP.
  eapply HP. }
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptvaInAncestorIsnull. simpl.
  case_eq ptvaInAncestorIsnull.
  (** va not mapped in ancestor : ret false **)
  intros HptvaInAncestorIsnulll.
  eapply weaken.
  eapply WP.ret.
  simpl;intros.
  trivial. 
  intuition. (** PROVE YOUR POSTCONDITION : propagatedPropertiesPrepare **)
  intros HptvaInAncestorIsnulll.
  (** va mapped in ancestor **)
  (** StateLib.getIndexOfAddr **)
  eapply WP.bindRev.
  eapply WP.weaken.
  2:{ intros.
      destruct H as ((H & [(Hptchild& Hnull) | Hptchild] ) & Hptchildnotnull) .
    + subst.  apply beq_nat_false in Hptchildnotnull. intuition.
    + assert (HP := conj (conj H Hptchild) Hptchildnotnull).
      pattern s in HP.
      eapply HP.  }
  eapply weaken.
  apply Invariants.getIndexOfAddr.
  simpl;intros.
  eapply H.
  intros idxva.
  simpl.
  intros.
  eapply bindRev; simpl;[|intros []].
 (** writeAccessible **)
  eapply WP.weaken.
  eapply WP.writeAccessible.
  intros. simpl.
  assert (exists entry0 : Pentry,
    lookup ptvaInAncestor idxva (memory s) pageEq idxEq = Some (PE entry0)) as Hlookup.
  { apply isPELookupEq.
    intuition;subst;trivial. }
  destruct Hlookup as (entry & Hlookup).
  exists entry ; split;trivial. 
  repeat rewrite and_assoc in H.
  destruct H as (Hpostcondition & Hnotpd (* : YOUR precondition to prove the postcondition *) & Hfalse & Hrest). 
  (** prove that the same page is mapped in the parent and associated to the va stored into the second shadow structure **)
  assert(Heqphy : phypage = pa entry). {
  intuition;subst.
  apply isAccessibleMappedPageGetTableRoot with sh2 descParent ptsh2 va pdAncestor
  ancestor vaInAncestor ptvaInAncestor s;trivial. }
  (** prove that the page is accessible into the parent **)
  assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true). {
  assert(Hcons : consistency s) by (unfold propagatedProperties in *;intuition).
  subst.
  unfold consistency in Hcons.
  apply isAccessibleMappedPageInParentTrue with descParent va (pa entry) ptvaInAncestor ptsh2 pdAncestor;
  intuition;subst;trivial. }
  assert(Hx':= conj Htrue Hrest).    
  assert(Hx:= conj Hnotpd Hx').
 (*  assert(Hpostcondition :True) by trivial. *)  
  assert (H:= conj Hpostcondition Hx).
  pattern s in H.
  (** add the propeties about writeAccessible post conditions **)
  match type of H with 
  | ?HT s => instantiate (1 := fun tt s => HT s /\ 
              entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) false s /\
              isEntryPage ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) phypage s /\
              entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) true s  ) 
  end.
  simpl.
  set (s' := {| currentPartition := _ |}).  
  rewrite and_assoc.
  split. 
  trivial.  
  subst.
  (** PROVE YOUR Precondition required to prove the postcondition : propagatedPropertiesPrepare **)
  assert(In ancestor (getPartitions pageRootPartition s)). {
    assert(isAncestor currentPart ancestor s). {
  unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) by apply pageDecOrNot.
  destruct Hor as [Hor | Hor];[left;trivial|right].
  assert (His : isAncestor currentPart ancestor s).
  { unfold consistency in *;
    apply isAncestorTrans with descParent;intuition. 
    apply nextEntryIsPPgetParent;trivial. }
    unfold isAncestor in *;intuition. }
  assert(Hpp :nextEntryIsPP descParent idxParentDesc ancestor s); intuition.
  rewrite nextEntryIsPPgetParent in Hpp.
  unfold consistency in *.
  apply ancestorInPartitionTree with descParent;trivial.
  intuition. intuition.
  unfold getAncestors.
  destruct nbPage;simpl;  rewrite Hpp;
  simpl;left;trivial. }
  intuition.
  subst idxva.
  apply propagatedPropertiesPrepareUpdateUserFlag  with descParent pt sh2 lastIndex ancestor pdAncestor ptsh2
  defaultV va (StateLib.getIndexOfAddr vaInAncestor levelMin);intuition;
  subst;trivial.
  unfold propagatedPropertiesPrepare in *;intuition.
  (** accessibleVAIsNotPartitionDescriptor **)
  apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag  with L ancestor   
        pdAncestor;trivial;
  unfold consistency in *;intuition.
  apply nextEntryIsPPgetPd;trivial.
  apply getAccessibleMappedPageInAncestor with descParent va sh2 ptsh2 ancestor;trivial.
  (** Prove the recursion invariant **)
   simpl in *.
  assert(Hmult : multiplexer = pageRootPartition) by intuition. 
  subst.
  assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartitions 
        by (apply getPartitionsUpdateUserFlag; trivial).
  rewrite  and_assoc.
  split.
  unfold isPartitionFalseAll in *;
  unfold isPartitionFalse; unfold s'; cbn.
  repeat rewrite readPDflagUpdateUserFlag;trivial.
  apply WriteAccessibleRecRecursionInvariant.
  intuition;subst;trivial.
  unfold writeAccessibleRecInternalPropertiesPrepare;intuition;trivial.
  simpl.
(** RECURSION **)
  intros; simpl; subst.
  eapply weaken.
  eapply IHn with (phypage:= phypage) (pt:= ptvaInAncestor). 
  intros;intuition;subst;trivial.
  unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) by apply pageDecOrNot.
  destruct Hor as [Hor | Hor];[left;trivial|right].
  assert (His : isAncestor currentPart ancestor s).
  { unfold consistency in *;
    apply isAncestorTrans with descParent;intuition. 
    apply nextEntryIsPPgetParent;trivial. }
    unfold isAncestor in *;intuition.
  assert(Hpp :nextEntryIsPP descParent idxParentDesc ancestor s); intuition.
  rewrite nextEntryIsPPgetParent in Hpp.
  unfold consistency in *.
  apply ancestorInPartitionTree with descParent;trivial.
  intuition. intuition.
  unfold getAncestors.
  destruct nbPage;simpl;  rewrite Hpp;
  simpl;left;trivial.
Qed.

Definition preconditionToProveWriteAccessibleRecNewProperty s part1  parentpart1 part2 pdpart2 vapart2 pg:=
StateLib.getParent part1 (memory s) =Some  parentpart1
/\ StateLib.getPd part2 (memory s) = Some pdpart2
/\ getMappedPage pdpart2 s vapart2 =  pg 
/\ noDupMappedPagesList s
/\ In part2 (getPartitions pageRootPartition s)
/\ getAccessibleMappedPage pdpart2 s vapart2 = NonePage.
Lemma WriteAccessibleRecGetParent (va:vaddr) (descParent phypage pt:page) currentPart n part1  parentpart1 part2 pdpart2 vapart2 pg:  
{{ fun s : state => preconditionToProveWriteAccessibleRecNewProperty s part1  parentpart1 part2 pdpart2 vapart2 pg
/\ writeAccessibleRecRecurtionInvariantConj va descParent phypage pt currentPart s }} 
  Internal.writeAccessibleRecAux n va descParent false {{
    fun _ s  => preconditionToProveWriteAccessibleRecNewProperty s part1  parentpart1 part2 pdpart2 vapart2 pg
     }}.
Proof.
unfold writeAccessibleRecRecurtionInvariantConj.
 revert va descParent  pt phypage .
induction n.
intros;simpl.
eapply weaken.
eapply WP.ret. simpl.
(** PROVE YOUR POSTCONDITION : True **)
intuition.  
intros.
simpl.
eapply bindRev.
(** getPageRootPartition **)
eapply weaken.
eapply Invariants.getPageRootPartition.
intros; simpl.
pattern s in H.
eapply H.
simpl. 
intros multiplexer.
eapply bindRev.
(** Page.eqb **)
eapply weaken.
eapply Invariants.Page.eqb.
simpl.
intros.
pattern s in H.
eapply H.
simpl.
intros isMultiplexer.
case_eq isMultiplexer.
(** case_eq isMultiplexer true **)
+ intros isMultiplexerT.
  (** ret **)
  eapply weaken.
  eapply WP.ret.
  intros;trivial.
  simpl;trivial.
  intuition. (** PROVE YOUR POSTCONDITION : true **)
(** case_eq isMultiplexer false **)
+ intros isMultiplexerF.
  eapply bindRev.
  (** getSndShadow **)
  eapply weaken.
  eapply Invariants.getSndShadow.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
 unfold consistency in H;intuition.
 (** In descParent (getPartitions MALInternal.multiplexer s)**)
  intros sh2; simpl.
  eapply bindRev.
  (** getNbLevel **)
  eapply weaken.
  eapply Invariants.getNbLevel.
  intros; simpl.
  pattern s in H.
  eapply H.
  intros L; simpl. 
  (** getIndexOfAddr **) 
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getIndexOfAddr.
  simpl; intros.
  pattern s in H.
  eapply H.
  intros lastIndex.
  simpl.
  (** getTableAddr **)
  eapply bindRev.
  eapply weaken.
  eapply GetTableAddr.getTableAddr with (currentPart:= descParent) (idxroot:= idxShadow2).
  simpl. 
  intros.
  split.
  pattern s in H.
  eapply H.
  split.
  intuition.
  split.
  intuition.
  split. 
  intuition.
  exists sh2.
  split. intuition.
  split.
  apply sh2PartNotNull with descParent s;intuition.
  unfold consistency in *;intuition.
  left; split; intuition.
  intros ptsh2. simpl.  
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2:{
  intros.
  destruct H as (H0 & H1).
  assert( (getTableAddrRoot' ptsh2 idxShadow2 descParent va s /\ ptsh2 = pageDefault) \/
  (  isVA ptsh2 (StateLib.getIndexOfAddr va levelMin ) s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s)).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right.
      destruct H1 as (Hget  & Hnew & H1).
      generalize (H1 (StateLib.getIndexOfAddr va levelMin ) );clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(Hpe &Htrue) | (_&Hfalse)]];trivial.
       - contradict Hfalse.
         apply idxSh2idxSh1notEq.
      - split;trivial.
      - contradict Hfalse.
        symmetrynot.
        apply idxPDidxSh2notEq.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP. } 
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptsh2Isnull. simpl.
  case_eq ptsh2Isnull.
  intros.
  eapply WP.weaken.
  eapply WP.ret .
  intros;trivial.
  simpl;trivial.
  intuition. (** PROVE YOUR POSTCONDITION : true **)
  intros Hptsh2NotNull.
  (** readVirtual **)
  eapply bindRev. 
  eapply weaken.
  2: {  
  intros.
  destruct H as ((H & Hstrong) & Htrue).
  assert(Heqv:  (isVA ptsh2 (StateLib.getIndexOfAddr va levelMin) s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s)).
  { destruct Hstrong as [Hor|Hor].   
    assert(Hfalse: (Nat.eqb pageDefault pageDefault) = false) by (intuition;subst;trivial).
    apply beq_nat_false in Hfalse.
    now contradict Hfalse.
    intuition; subst;trivial. }
  clear Hstrong.
  assert (Hnew:= conj (conj H Heqv) Htrue).
  eapply Hnew. }
  eapply weaken.
  eapply Invariants.readVirtual.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
  subst.
  intuition;
  subst;trivial.
  intros vaInAncestor.
  simpl.
  subst.
  (** getParent **)
  eapply bindRev.
  eapply weaken. 
  eapply Invariants.getParent.
  intros.
  simpl. 
  split.
  pattern s in H.
  eapply H.
  unfold propagatedProperties in *.  
  intuition.
  intros ancestor; simpl.
  (** getPd **)
   eapply bindRev.
  eapply weaken.
  eapply Invariants.getPd.
  simpl; intros.
  split.
  pattern s in H.
  eapply H. split.
  unfold propagatedProperties in H.
  unfold consistency in H.
  intuition.
  destruct H.
  unfold propagatedProperties in H.
  assert (Hparent:  parentInPartitionList s) by (unfold consistency in *;  intuition).
  unfold parentInPartitionList in *.
  apply Hparent with descParent; intuition.
    intros pdAncestor. 
(** setAccessible **)
  unfold setAccessible.
  eapply bindRev.
  (** getDefaultVAddr **)
  eapply weaken.
  eapply Invariants.getDefaultVAddr.
  simpl.
  intros.
  pattern s in H.
  eapply H.
  intros defaultV.
  simpl.
  eapply bindRev.
  (**   VAddr.eqbList **)
  eapply weaken.
  eapply Invariants.VAddr.eqbList.
  simpl.
  intros.
  pattern s in H.
  eapply H.
  intros isdefaultVA.
  (** case negb isdefaultVA **)
  case_eq (isdefaultVA).
  intros.
  eapply weaken.
  eapply WP.ret.
  intros;trivial.
  simpl;trivial.
  intuition. (** PROVE YOUR POSTCONDITION : true **)
  intros isdefaultVAT.
  eapply bindRev.
  (** getTableAddr **)
  eapply WP.weaken. 
  apply getTableAddr with (currentPart:= ancestor) (idxroot:= idxPageDir).
  simpl.
  intros s H.
  split.
  pattern s in H. 
  eapply H.
  assert(Hancestor: In ancestor (getPartitions pageRootPartition s)).
  { assert(Hparent : parentInPartitionList s) by (unfold consistency in *;intuition).
    apply Hparent with descParent; intuition. }
  split;[intuition|].
  split;[intuition|].      
  split;[intuition|].
  exists pdAncestor.
  split. intuition.
  split.
  apply pdPartNotNull with ancestor s;trivial. 
  intuition.
  unfold consistency in *.
  intuition.
  subst. left. split;intuition.
  intro ptvaInAncestor. simpl.
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2:{
  intros.
  destruct H as (H0 & H1).
  assert( (getTableAddrRoot' ptvaInAncestor idxPageDir ancestor vaInAncestor s /\ ptvaInAncestor = pageDefault) \/
   (isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) s /\ getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s)).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right.
      destruct H1 as (Hget  & Hnew & H1).
      split. 
      generalize (H1 (StateLib.getIndexOfAddr vaInAncestor levelMin ) );clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]];trivial.
       - contradict Hfalse.
         apply idxPDidxSh1notEq.
       - contradict Hfalse.
        apply idxPDidxSh2notEq.
       - assumption.  }  
  assert (HP :=conj H0 H).
  pattern s in HP.
  eapply HP. }
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptvaInAncestorIsnull. simpl.
  case_eq ptvaInAncestorIsnull.
  (** va not mapped in ancestor : ret false **)
  intros HptvaInAncestorIsnulll.
  eapply weaken.
  eapply WP.ret.
  intros;trivial.
  simpl;trivial.
  intuition. (** PROVE YOUR POSTCONDITION : true **)
  intros HptvaInAncestorIsnulll.
  (** va mapped in ancestor **)
  (** StateLib.getIndexOfAddr **)                
  eapply WP.bindRev.
  eapply WP.weaken.
  2:{ intros.
      destruct H as ((H & [(Hptchild& Hnull) | Hptchild] ) & Hptchildnotnull) .
    + subst.  apply beq_nat_false in Hptchildnotnull. intuition.
    + assert (HP := conj (conj H Hptchild) Hptchildnotnull).
      pattern s in HP.
      eapply HP.  }
  eapply weaken.
  apply Invariants.getIndexOfAddr.
  simpl;intros.
  eapply H.
  intros idxva.
  simpl.
  intros.
  eapply bindRev; simpl;[|intros []].
 (** writeAccessible **)
  eapply WP.weaken.
  eapply WP.writeAccessible.
  intros. simpl.
  assert (exists entry0 : Pentry,
    lookup ptvaInAncestor idxva (memory s) pageEq idxEq = Some (PE entry0)) as Hlookup.
  { apply isPELookupEq.
    intuition;subst;trivial. }
  destruct Hlookup as (entry & Hlookup).
  exists entry ; split;trivial. 
  repeat rewrite and_assoc in H.
  destruct H as ( Hprecond & (*: YOUR precondition (if exists) to prove the postcondition *) Hfalse & Hrest). 
  (** prove that the same page is mapped in the parent and associated to the va stored into the second shadow structure **)
  assert(Heqphy : phypage = pa entry). {
  intuition;subst.
  apply isAccessibleMappedPageGetTableRoot with sh2 descParent ptsh2 va pdAncestor
  ancestor vaInAncestor ptvaInAncestor s;trivial. }
  (** prove that the page is accessible into the parent **)
  assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true). {
  assert(Hcons : consistency s) by (unfold propagatedProperties in *;intuition).
  subst.
  unfold consistency in Hcons.
  apply isAccessibleMappedPageInParentTrue with descParent va (pa entry) ptvaInAncestor ptsh2 pdAncestor;
  intuition;subst;trivial. }
  assert(Hx:= conj Htrue Hrest ).    
(*   assert(Hprecond :True) by trivial.   *)
  assert (H:= conj Hprecond Hx).
  pattern s in H.
  (** add the propeties about writeAccessible post conditions **)
  match type of H with 
  | ?HT s => instantiate (1 := fun tt s => HT s /\ 
              entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) false s /\
              isEntryPage ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) phypage s /\
              entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) true s  ) 
  end.
  simpl.
  set (s' := {| currentPartition := _ |}).  
  rewrite and_assoc.
  split.
 (* admit.  *) (** PROVE YOUR POSTCONDITION : true **)
  (** Prove the POSTCONDITION **)
  unfold  preconditionToProveWriteAccessibleRecNewProperty in *;simpl.   
  assert(Hmult : multiplexer = pageRootPartition) by intuition. 
  subst.
  assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartitions 
        by (apply getPartitionsUpdateUserFlag; trivial).
  rewrite getParentUpdateUserFlag;intuition.
  rewrite getPdUpdateUserFlag;intuition.
  unfold s'; rewrite getMappedPageUpdateUserFlag;trivial.
  unfold s';subst; apply noDupMappedPagesListUpdateUserFlag;trivial.
  rewrite Hpartitions;trivial.
  subst.
  apply getAccessibleMappedPageNoneUpdateUserFlagFalse;trivial.
  (** Prove the recursion invariant **)
   simpl in *.
  assert(Hmult : multiplexer = pageRootPartition) by intuition. 
  subst.
  assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartitions 
        by (apply getPartitionsUpdateUserFlag; trivial).
  apply WriteAccessibleRecRecursionInvariant.
  intuition;subst;trivial.
  unfold writeAccessibleRecInternalPropertiesPrepare;intuition;trivial.
(** RECURSION **)
  intros; simpl; subst.
  eapply weaken.
  eapply IHn with (phypage:= phypage) (pt:= ptvaInAncestor). 
  intros;intuition;subst;trivial.
  unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) by apply pageDecOrNot.
  destruct Hor as [Hor | Hor];[left;trivial|right].
  assert (His : isAncestor currentPart ancestor s).
  { unfold consistency in *;
    apply isAncestorTrans with descParent;intuition. 
    apply nextEntryIsPPgetParent;trivial. }
    unfold isAncestor in *;intuition.
  assert(Hpp :nextEntryIsPP descParent idxParentDesc ancestor s); intuition.
  rewrite nextEntryIsPPgetParent in Hpp.
  unfold consistency in *.
  apply ancestorInPartitionTree with descParent;trivial.
  intuition. intuition.
  unfold getAncestors.
  destruct nbPage;simpl;  rewrite Hpp;
  simpl;left;trivial.
Qed. 

Lemma WriteAccessibleRecPrepareNewProperty va descParent phypage pt currentPart :
{{ fun s : state =>  writeAccessibleRecRecurtionInvariantConj va descParent phypage pt currentPart s }} 
Internal.writeAccessibleRecAux (nbPage +1) va descParent false
{{ fun _ s  => writeAccessibleRecPreparePostcondition  descParent phypage s }}.
Proof.
unfold writeAccessibleRecRecurtionInvariantConj.
unfold writeAccessibleRecPreparePostcondition.
 revert va descParent  pt phypage  (* descPart phy *) .
  unfold getAncestors.
induction (nbPage + 1).
intros;simpl.
eapply weaken.
eapply WP.ret. simpl;intros.
intuition. (** PROVE YOUR POSTCONDITION : ~ In phypage (getAccessibleMappedPages partition s) **) 
intros.
simpl.
eapply bindRev.
(** getPageRootPartition **)
eapply weaken.
eapply Invariants.getPageRootPartition.
intros; simpl.
pattern s in H.
eapply H.
simpl. 
intros multiplexer.
eapply bindRev.
(** Page.eqb **)
eapply weaken.
eapply Invariants.Page.eqb.
simpl.
intros.
pattern s in H.
eapply H.
simpl.
intros isMultiplexer.
case_eq isMultiplexer.
(** case_eq isMultiplexer true **)
+ intros isMultiplexerT.
  (** ret **) 
  eapply weaken.
  eapply WP.ret.
  intros;trivial.
  (** PROVE YOUR POSTCONDITION : ~In phypage (getAccessibleMappedPages partition s) **)
  simpl.
(*   split. intuition. *)
  unfold not; intros partition Hfalse.
  intuition subst.
  assert(Hmult: StateLib.getParent descParent (memory s) = None).
  apply parentMultNone;trivial.
  rewrite Hmult in *.
  contradiction.
(** case_eq isMultiplexer false **)
+ intros isMultiplexerF.
  eapply bindRev.
  (** getSndShadow **)
  eapply weaken.
  eapply Invariants.getSndShadow.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
 unfold consistency in H;intuition.
 (** In descParent (getPartitions MALInternal.multiplexer s)**)
  intros sh2; simpl.
  eapply bindRev.
  (** getNbLevel **)
  eapply weaken.
  eapply Invariants.getNbLevel.
  intros; simpl.
  pattern s in H.
  eapply H.
  intros L; simpl. 
  (** getIndexOfAddr **) 
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getIndexOfAddr.
  simpl; intros.
  pattern s in H.
  eapply H.
  intros lastIndex.
  simpl.
  (** getTableAddr **)
  eapply bindRev.
  eapply weaken.
  eapply GetTableAddr.getTableAddr with (currentPart:= descParent) (idxroot:= idxShadow2).
  simpl. 
  intros.
  split.
  pattern s in H.
  eapply H.
  split.
  intuition.
  split.
  intuition.
  split. 
  intuition.
  exists sh2.
  split. intuition.
  split.
  apply sh2PartNotNull with descParent s;intuition.
  unfold consistency in *;intuition.
  left; split; intuition.
  intros ptsh2. simpl.  
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2:{
  intros.
  destruct H as (H0 & H1).
  assert( (getTableAddrRoot' ptsh2 idxShadow2 descParent va s /\ ptsh2 = pageDefault) \/
  (  isVA ptsh2 (StateLib.getIndexOfAddr va levelMin ) s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s)).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right.
      destruct H1 as (Hget  & Hnew & H1).
      generalize (H1 (StateLib.getIndexOfAddr va levelMin ) );clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(Hpe &Htrue) | (_&Hfalse)]];trivial.
       - contradict Hfalse.
         apply idxSh2idxSh1notEq.
      - split;trivial.
      - contradict Hfalse.
        symmetrynot.
        apply idxPDidxSh2notEq.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP. } 
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptsh2Isnull. simpl.
  case_eq ptsh2Isnull.
  intros.
  eapply WP.weaken.
  eapply WP.ret .
  intros;trivial.
  simpl.
  (** PROVE YOUR POSTCONDITION : ~In phypage (getAccessibleMappedPages partition s)  **)
  assert(Hptsh2NotNulltrue : (Nat.eqb pageDefault ptsh2) = false ).
  { assert(Hwellformed :wellFormedShadows idxShadow2 s) by (unfold consistency in *;intuition).
    unfold wellFormedShadows in Hwellformed.
    assert(Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
    assert(Hpdedesc : (exists entry : page,
            nextEntryIsPP descParent idxPageDir entry s /\ entry <> pageDefault)).
    { apply Hpde;trivial. intuition. left;trivial. }
    destruct Hpdedesc as (pdparent & Hentry1 & Hentry2).
    assert(Hmult : multiplexer = pageRootPartition ) by intuition.
    subst.
    assert(Htrue : getIndirection sh2 va L (nbLevel -1) s = Some ptsh2 /\
              (Nat.eqb pageDefault ptsh2) = false).
    { assert(Hexist : exists indirection2 : page,
                getIndirection sh2 va L (nbLevel - 1) s = Some indirection2 /\
                (Nat.eqb pageDefault indirection2) = false). 
      { apply Hwellformed with descParent pdparent pt;trivial. 
        + intuition.      
        + assert( false = pageEq descParent pageRootPartition) as Hnotmul by 
                     intuition.
          unfold pageEq in *.
          unfold not;intros ; subst.
          symmetry in Hnotmul.
          apply beq_nat_false in Hnotmul.
          apply nextEntryIsPPgetPd;trivial.
        + intuition.
        + unfold propagatedProperties in *.
          intuition.
        + apply getIndirectionGetTableRoot1 with descParent; trivial.
          apply nextEntryIsPPgetPd;intuition.
          unfold propagatedProperties in *.
          intuition.
          intuition;subst;trivial.
        + intuition. }
       destruct Hexist as (indirection2 & Hin1 & Hin2).
       assert(getIndirection sh2 va L (nbLevel - 1) s = Some ptsh2).
        { assert( (getTableAddrRoot' ptsh2 idxShadow2 descParent va s /\ ptsh2 = pageDefault \/
                isVA ptsh2 (StateLib.getIndexOfAddr va levelMin) s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s) /\
               (Nat.eqb pageDefault ptsh2) = true
              /\ nextEntryIsPP descParent idxShadow2 sh2 s) as (Hor & Hx & Hxx) by intuition.
          assert(Hlevel  : Some L = StateLib.getNbLevel )by intuition.
          clear H0.
        destruct Hor as [Hor|Hor].
      * unfold getTableAddrRoot' in *.
        destruct Hor as ((_ & Hor) & Hsub).
        apply Hor in Hxx. clear Hor.
        destruct Hxx as (l & Hl & stop & Hstop1 & Hstop2 & Hind).
        rewrite <- Hl in Hlevel.
        inversion Hlevel.
        subst l.
        subst.
        apply getIndirectionNbLevelEq with stop;trivial.
        apply getNbLevelEq in Hl.
        subst. apply nbLevelEq.
      * apply getIndirectionGetTableRoot2 with descParent;trivial.
        apply nextEntryIsPPgetSndShadow;trivial.
        intuition. intros;subst;split;trivial; intuition.  }
      split;trivial.
      rewrite  H in Hin1.
      inversion Hin1;subst indirection2;trivial. }
   intuition.  }
  intuition subst.
  apply beq_nat_false in Hptsh2NotNulltrue.
  now contradict Hptsh2NotNulltrue. 
  rewrite Hptsh2NotNulltrue in *.
  intuition.
  intros Hptsh2NotNull.
  (** readVirtual **)
  eapply bindRev. 
  eapply weaken.
  2: {  
  intros.
  destruct H as ((H & Hstrong) & Htrue).
  assert(Heqv:  (isVA ptsh2 (StateLib.getIndexOfAddr va levelMin) s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s)).
  { destruct Hstrong as [Hor|Hor].   
    assert(Hfalse: (Nat.eqb pageDefault pageDefault) = false) by (intuition;subst;trivial).
    apply beq_nat_false in Hfalse.
    now contradict Hfalse.
    intuition; subst;trivial. }
  clear Hstrong.
  assert (Hnew:= conj (conj H Heqv) Htrue).
  eapply Hnew. }
  eapply weaken.
  eapply Invariants.readVirtual.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
  subst.
  intuition;
  subst;trivial.
  intros vaInAncestor.
  simpl.
  subst.
  (** getParent **)
  eapply bindRev.
  eapply weaken. 
  eapply Invariants.getParent.
  intros.
  simpl. 
  split.
  pattern s in H.
  eapply H.
  unfold propagatedProperties in *.  
  intuition.
  intros ancestor; simpl.
  (** getPd **)
   eapply bindRev.
  eapply weaken.
  eapply Invariants.getPd.
  simpl; intros.
  split.
  pattern s in H.
  eapply H. split.
  unfold propagatedProperties in H.
  unfold consistency in H.
  intuition.
  destruct H.
  unfold propagatedProperties in H.
  assert (Hparent:  parentInPartitionList s) by (unfold consistency in *;  intuition).
  unfold parentInPartitionList in *.
  apply Hparent with descParent; intuition.
    intros pdAncestor. 
(** setAccessible **)
  unfold setAccessible.
  eapply bindRev.
  (** getDefaultVAddr **)
  eapply weaken.
  eapply Invariants.getDefaultVAddr.
  simpl.
  intros.
  pattern s in H.
  eapply H.
  intros defaultV.
  simpl.
  eapply bindRev.
  (**   VAddr.eqbList **)
  eapply weaken.
  eapply Invariants.VAddr.eqbList.
  simpl.
  intros.
  pattern s in H.
  eapply H.
  intros isdefaultVA.
  (** case negb isdefaultVA **)
  case_eq (isdefaultVA).
  intros.
  eapply weaken.
  eapply WP.ret.
  intros;trivial.
  (** PROVE YOUR POSTCONDITION : ~In phypage (getAccessibleMappedPages partition s)  **)
  subst.
  simpl;intros.
  assert(Hptsh2NotNulltrue : (Nat.eqb pageDefault ptsh2) = false ) by intuition.
  assert(Hfalse : true = vaddrEq defaultV vaInAncestor) by intuition.
  assert(Htrue :  false = vaddrEq defaultV vaInAncestor).
  { assert(Hwellformed1 : wellFormedSndShadow s ).
  unfold propagatedProperties in *.
  unfold consistency in *.
  intuition.
  unfold wellFormedSndShadow in *.
  assert(Hpde : partitionDescriptorEntry s). 
  { unfold propagatedProperties in *.
    unfold consistency in *.
    intuition. }
  assert(Hpdedesc : (exists entry : page,
  nextEntryIsPP descParent idxPageDir entry s /\ entry <> pageDefault)).
  { 
  apply Hpde;trivial.
  intuition.
  left;trivial. }
  destruct Hpdedesc as (pdparent & Hentry1 & Hentry2).
  assert( getMappedPage pdparent s va = SomePage phypage  ) as Hmap.
  apply getMappedPageGetTableRoot with pt descParent;intuition; subst;trivial.
  assert(Hmult : multiplexer = pageRootPartition ) by intuition.
  subst. 
  assert(exists vainparent : vaddr, getVirtualAddressSh2 sh2 s va = Some vainparent  
  /\  vaddrEq vaddrDefault vainparent = false ) as Hexits . 
  apply Hwellformed1 with  descParent phypage pdparent .
  intuition.      
  assert( false = pageEq descParent pageRootPartition) as Hnotmul by 
     intuition.
  unfold pageEq in *.
  unfold not;intros ; subst.
  symmetry in Hnotmul.
  apply beq_nat_false in Hnotmul.
  now contradict Hnotmul.
  apply nextEntryIsPPgetPd;trivial.
  apply nextEntryIsPPgetSndShadow;intuition.
  apply getMappedPageGetTableRoot with pt descParent;intuition;subst;trivial.
  destruct Hexits as (vainparent & Hgetva & Hvanotdef).
  assert (Heqva : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
  {
  apply getVirtualAddressSh2GetTableRoot with ptsh2 descParent 
  L;trivial.
  + intuition; subst; trivial.
  + intuition;subst;trivial.
  + apply nextEntryIsPPgetSndShadow;intuition.
  + unfold propagatedProperties in *; intuition. }
  rewrite Heqva in Hgetva.
  inversion Hgetva.
  subst.      
  unfold vaddrEq .
  assert(defaultV = vaddrDefault) by intuition.
  subst.  
  rewrite <- Hvanotdef;trivial. }
  rewrite <- Htrue in Hfalse.
  now contradict Hfalse.
  (** vaddr in parent not default **)
  intros isdefaultVAT.
  eapply bindRev.
  (** getTableAddr **)
  eapply WP.weaken. 
  apply getTableAddr with (currentPart:= ancestor) (idxroot:= idxPageDir).
  simpl.
  intros s H.
  split.
  pattern s in H. 
  eapply H.
  assert(Hancestor: In ancestor (getPartitions pageRootPartition s)).
  { assert(Hparent : parentInPartitionList s) by (unfold consistency in *;intuition).
    apply Hparent with descParent; intuition. }
  split;[intuition|].
  split;[intuition|].      
  split;[intuition|].
  exists pdAncestor.
  split. intuition.
  split.
  apply pdPartNotNull with ancestor s;trivial. 
  intuition.
  unfold consistency in *.
  intuition.
  subst. left. split;intuition.
  intro ptvaInAncestor. simpl.
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2:{
  intros.
  destruct H as (H0 & H1).
  assert( (getTableAddrRoot' ptvaInAncestor idxPageDir ancestor vaInAncestor s /\ ptvaInAncestor = pageDefault) \/
   (isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) s /\ getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s)).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right.
      destruct H1 as (Hget  & Hnew & H1).
      split. 
      generalize (H1 (StateLib.getIndexOfAddr vaInAncestor levelMin ) );clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]];trivial.
       - contradict Hfalse.
         apply idxPDidxSh1notEq.
       - contradict Hfalse.
        apply idxPDidxSh2notEq.
       - assumption.  }  
  assert (HP :=conj H0 H).
  pattern s in HP.
  eapply HP. }
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptvaInAncestorIsnull. simpl.
  case_eq ptvaInAncestorIsnull.
  (** va not mapped in ancestor : ret false **)
  intros HptvaInAncestorIsnulll.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl.
(*   split. intuition. *)
  (** PROVE YOUR POSTCONDITION : ~In phypage (getAccessibleMappedPages partition s)  **)
  assert(Ha3:Some L = StateLib.getNbLevel ) by intuition.
  assert(Htrue : (Nat.eqb pageDefault ptvaInAncestor) = false).
  { assert(Ha17:isAccessibleMappedPageInParent descParent va phypage s = true) by intuition.
    unfold isAccessibleMappedPageInParent in Ha17.
    assert (  Hsh2 : nextEntryIsPP descParent idxShadow2 sh2 s) by intuition.
    rewrite nextEntryIsPPgetSndShadow in *.
    rewrite Hsh2 in *.
    assert(Hgetvainparent : getVirtualAddressSh2 sh2 s va = Some  vaInAncestor).
    { subst.
      apply  getVirtualAddressSh2GetTableRoot with ptsh2 descParent L; intuition;
      subst;trivial. }
    rewrite Hgetvainparent in *.
    assert(Hparent : nextEntryIsPP descParent idxParentDesc ancestor s) by intuition.
    rewrite nextEntryIsPPgetParent in *.
    rewrite Hparent in *.
    assert(Hpd :  nextEntryIsPP ancestor idxPageDir pdAncestor s) by intuition.
    rewrite nextEntryIsPPgetPd in Hpd.
    rewrite Hpd in *.          
    case_eq (getAccessibleMappedPage pdAncestor s vaInAncestor) ;
    [intros p Hp |intros Hp|intros Hp]; rewrite Hp in *;
    try now contradict Ha17.
    apply beq_nat_true in Ha17.
    subst.
    assert(Ha6: (getTableAddrRoot' ptvaInAncestor idxPageDir ancestor vaInAncestor s /\ ptvaInAncestor = pageDefault \/
      isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) s /\
      getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s)) by intuition.
    unfold getTableAddrRoot' in Ha6. 
    unfold getTableAddrRoot in Ha6.
    destruct Ha6 as [Ha6 | Ha6].
    + destruct Ha6 as (Ha6 & _).
      destruct Ha6 as (_ & Ha6).
      rewrite <- nextEntryIsPPgetPd in Hpd.
      apply Ha6 in Hpd. clear Ha6.
      destruct Hpd as (nbL & HnbL & Hpd).
      destruct Hpd as (stop & Hstop1 & Hstop2 & Hind).
      rewrite <- HnbL in *.
      inversion Ha3;subst.
      clear IHn.
      unfold getAccessibleMappedPage in *.
      rewrite <- HnbL in *.
      case_eq(getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s);
      [intros pt1 Hpt1 | intros Hpt1]; 
      rewrite Hpt1 in *; try now contradict Hp.
      case_eq(Nat.eqb pageDefault pt1);intros Hisnull;
      rewrite Hisnull in *;try now contradict Hp.
      clear Hp.
      apply getNbLevelEq in HnbL.
      subst.
      apply getIndirectionRetNotDefaultLtNbLevel with (nbLevel - 1)  
      stop (CLevel (nbLevel - 1)) pdAncestor pt1 vaInAncestor s;trivial;[|rewrite nbLevelEq;trivial].
      assert(Hpde : partitionDescriptorEntry s). 
      { unfold propagatedProperties in *.
        unfold consistency in *.
        intuition. }
      unfold partitionDescriptorEntry in *.
      assert(Hpdedesc : (exists entry : page,
            nextEntryIsPP descParent idxParentDesc entry s /\ entry <> pageDefault)).
      { apply Hpde;trivial.
      intuition. intuition. }
      destruct Hpdedesc as (entry & Hentry1 & Hentry2).
      assert(entry = ancestor)by(apply getParentNextEntryIsPPEq with descParent s;trivial).
      subst.
      apply pdPartNotNull' with ancestor s;trivial.
      assert(Hparentpart : parentInPartitionList s) by 
        (unfold propagatedProperties in *; unfold consistency in *; intuition).
      unfold parentInPartitionList in *.
      apply Hparentpart with descParent;trivial.
      intuition. intuition.
    + rename Ha6 into Ha5.
      destruct Ha5 as (_ & Ha5).
      rewrite <- nextEntryIsPPgetPd in Hpd.
      apply Ha5 in Hpd. clear Ha5.
      destruct Hpd as (nbL & HnbL & Hpd).
      destruct Hpd as (stop & Hstop1 &  Hind).
      rewrite <- HnbL in *.
      inversion Ha3;subst.
      unfold getAccessibleMappedPage in *.
      rewrite <- HnbL in *.
      case_eq(getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s);
      [intros pt1 Hpt1 | intros Hpt1]; 
      rewrite Hpt1 in *; try now contradict Hp.
      case_eq(Nat.eqb pageDefault pt1);intros Hisnull;
      rewrite Hisnull in *;try now contradict Hp.
      clear Hp.
      apply getNbLevelEq in HnbL.
      subst.
      assert(Hindeq : getIndirection pdAncestor vaInAncestor 
      (CLevel (nbLevel - 1)) (nbLevel - 1)s = Some ptvaInAncestor).
      apply getIndirectionStopLevelGT2 with (CLevel (nbLevel - 1) + 1); 
      try lia;trivial.
      apply nbLevelEq.
      rewrite Hindeq in *.
      inversion Hpt1.
      subst.
      trivial.   } 
  intuition subst.
  apply beq_nat_false in Htrue;
  now contradict Htrue.
  rewrite Htrue in *.
  intuition. 
  intros HptvaInAncestorIsnulll.
  (** va mapped in ancestor **)
  (** StateLib.getIndexOfAddr **)                
  eapply WP.bindRev.
  eapply WP.weaken.
  2:{ intros.
      destruct H as ((H & [(Hptchild& Hnull) | Hptchild] ) & Hptchildnotnull) .
    + subst.  apply beq_nat_false in Hptchildnotnull. intuition.
    + assert (HP := conj (conj H Hptchild) Hptchildnotnull).
      pattern s in HP.
      eapply HP.  }
  eapply weaken.
  apply Invariants.getIndexOfAddr.
  simpl;intros.
  eapply H.
  intros idxva.
  simpl.
  intros.
  eapply bindRev; simpl;[|intros []].
 (** writeAccessible **)
  eapply WP.weaken.
  eapply WP.writeAccessible.
  intros. simpl.
  assert (exists entry0 : Pentry,
    lookup ptvaInAncestor idxva (memory s) pageEq idxEq = Some (PE entry0)) as Hlookup.
  { apply isPELookupEq.
    intuition;subst;trivial. }
  destruct Hlookup as (entry & Hlookup).
  exists entry ; split;trivial. 
  repeat rewrite and_assoc in H.
  destruct H as ((*Hprecond & : YOUR precondition (if exists) to prove the postcondition *) Hfalse & Hrest). 
  (** prove that the same page is mapped in the parent and associated to the va stored into the second shadow structure **)
  assert(Heqphy : phypage = pa entry). {
  intuition;subst.
  apply isAccessibleMappedPageGetTableRoot with sh2 descParent ptsh2 va pdAncestor
  ancestor vaInAncestor ptvaInAncestor s;trivial. }
  (** prove that the page is accessible into the parent **)
  assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true). {
  assert(Hcons : consistency s) by (unfold propagatedProperties in *;intuition).
  subst.
  unfold consistency in Hcons.
  apply isAccessibleMappedPageInParentTrue with descParent va (pa entry) ptvaInAncestor ptsh2 pdAncestor;
  intuition;subst;trivial. }
  assert(Hx:= conj Htrue Hrest ).    
  assert(Hprecond :True) by trivial. 
  assert (H:= conj Hprecond Hx).
  pattern s in H.
  (** add the propeties about writeAccessible post conditions **)
  match type of H with 
  | ?HT s => instantiate (1 := fun tt s => HT s /\ 
              entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) false s /\
              isEntryPage ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) phypage s /\
              entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) true s  ) 
  end.
  simpl.
  set (s' := {| currentPartition := _ |}).  
  rewrite and_assoc.
   split. 
 trivial.  (** PROVE YOUR Precondition required to prove the postcondition : True **)
  (** Prove the recursion invariant **)
   simpl in *.
  assert(Hmult : multiplexer = pageRootPartition) by intuition. 
  subst.
  assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartitions 
        by (apply getPartitionsUpdateUserFlag; trivial).
  apply WriteAccessibleRecRecursionInvariant.
  intuition;subst;trivial.
  unfold writeAccessibleRecInternalPropertiesPrepare;intuition;trivial.
(** RECURSION **)
  intros; simpl; subst.
  unfold hoareTriple in *.
  intros.
  assert(isAncestor currentPart ancestor s).
  { unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) by apply pageDecOrNot.
  destruct Hor as [Hor | Hor];[left;trivial|right].
  assert (His : isAncestor currentPart ancestor s).
  { unfold consistency in *;
    apply isAncestorTrans with descParent;intuition. 
    apply nextEntryIsPPgetParent;trivial. }
    unfold isAncestor in *;intuition. }
  assert(In ancestor (getPartitions pageRootPartition s)).
  { unfold consistency in *.
      assert(Hpp :nextEntryIsPP descParent idxParentDesc ancestor s) by  intuition.
    rewrite nextEntryIsPPgetParent in Hpp.
    apply ancestorInPartitionTree with descParent;trivial.
    intuition. intuition.
    intuition.
    unfold getAncestors.
    destruct nbPage;simpl; rewrite Hpp;
    simpl;left;trivial. }
  case_eq (writeAccessibleRecAux n vaInAncestor ancestor false s);[intros b Hp|intros b s' Hp];
  generalize (IHn vaInAncestor ancestor ptvaInAncestor phypage (* descParent (Some ancestor) *) s) ;clear IHn;intros IHn;[| rewrite Hp in *;
  apply IHn;intuition].
  destruct b;simpl.
  intros partition Hpost.
  match type of IHn with 
    | ?HT -> ?IHnx => assert(IHnx) as Hx
  end.
  apply IHn;intuition.

  clear IHn.
  rewrite Hp in *.
  pose proof WriteAccessibleRecGetParent as Hgetparent.
  assert(Hnextpp: StateLib.getParent descParent (memory s) = Some ancestor)by (
   apply nextEntryIsPPgetParent;intuition).
  assert(Hancestor: StateLib.getPd ancestor (memory s) = Some pdAncestor) by (apply 
  nextEntryIsPPgetPd;intuition).
  assert( StateLib.getParent descParent (memory s0) = StateLib.getParent descParent (memory s) 
         /\ StateLib.getPd ancestor (memory s0) =  StateLib.getPd ancestor (memory s)
         /\ getMappedPage pdAncestor s0 vaInAncestor = getMappedPage pdAncestor s vaInAncestor
         /\ noDupMappedPagesList s0
         /\ In ancestor (getPartitions pageRootPartition s0)
         /\ getAccessibleMappedPage pdAncestor s0 vaInAncestor = NonePage) as (HparentEq & Hpdeq & HaccessEq & HnodupS0 & HnodupS & Htrue).
   { generalize (Hgetparent vaInAncestor ancestor phypage ptvaInAncestor  currentPart n descParent ancestor
       ancestor pdAncestor vaInAncestor (getMappedPage pdAncestor s vaInAncestor) s);
     clear Hgetparent;intros Hgetparent.
     rewrite Hp in Hgetparent.
     destruct Hgetparent as (Hparent0 & Hpd0 & Hi1 & Hi2 & Hi3).
     unfold writeAccessibleRecRecurtionInvariantConj, preconditionToProveWriteAccessibleRecNewProperty,
     consistency in *.
     intuition.
     assert(Hnone: getAccessibleMappedPage pdAncestor s vaInAncestor = NonePage). 
     { apply getMappedPageNotAccessible with ptvaInAncestor ancestor phypage;
        intuition;subst;trivial. }
     trivial.
     rewrite Hparent0.
     rewrite Hpd0.
     split. symmetry.  trivial.
     split. symmetry.  trivial.
     split;trivial.
     split;trivial. } 
    rewrite <- HparentEq in Hnextpp.
    rewrite Hnextpp in Hpost. 
    simpl in *.
    destruct Hpost as [Hpost|Hpost];[|
    apply Hx;trivial].
    subst partition.
   assert(Hnone: getAccessibleMappedPage pdAncestor s vaInAncestor = NonePage). 
  { apply getMappedPageNotAccessible with ptvaInAncestor ancestor phypage;
  intuition;subst;trivial. }
  assert(Hmapped: getMappedPage pdAncestor s vaInAncestor = SomePage phypage).
  { apply getMappedPageGetTableRoot with ptvaInAncestor ancestor;
  intuition;subst;trivial.  }
  unfold getAccessibleMappedPages.
  assert(Hpdanc : StateLib.getPd ancestor (memory s) = Some pdAncestor).
   { apply nextEntryIsPPgetPd;intuition. }
  rewrite Hpdeq.
  rewrite Hpdanc.
  unfold getAccessibleMappedPagesAux.
  rewrite filterOptionInIff.
  unfold getAccessibleMappedPagesOption.
  rewrite in_map_iff.
  unfold not;intros Hfalse.
  destruct Hfalse as (x & Hx1 & Hx2).
  assert(getMappedPage pdAncestor s0 x = SomePage phypage).
   { apply accessiblePAgeIsMapped; trivial. }
  contradict Hx1.
  assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
    StateLib.checkVAddrsEqualityWOOffset nbLevel vaInAncestor va1 ( CLevel (nbLevel -1) ) = true ) by apply AllVAddrWithOffset0.
  destruct Heqvars as (va1 & Hva1 & Hva11).
  assert (va1 = x). 
  { apply eqMappedPagesEqVaddrs with phypage pdAncestor s0;trivial.
    rewrite <- Hmapped.
    symmetry.
    rewrite  <-HaccessEq .
    apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
    apply getNbLevelEqOption.
    unfold noDupMappedPagesList in *. 
    assert(Hparentpart : parentInPartitionList s).
    { unfold propagatedProperties in *.
      unfold consistency in *. intuition. }
   assert(In ancestor (getPartitions pageRootPartition s)).
   { unfold parentInPartitionList in *.
     apply  Hparentpart with descParent; trivial.
     intuition.
     apply nextEntryIsPPgetParent;intuition.
      rewrite <- HparentEq;trivial. }
    apply HnodupS0 in HnodupS.
    unfold getMappedPages in HnodupS.
    rewrite Hpdeq in *.
    rewrite Hpdanc in *.
    unfold getMappedPagesAux in *. 
    unfold getMappedPagesOption in *;trivial. }
 subst x.
 assert(Hnewhyp : getAccessibleMappedPage pdAncestor s0 vaInAncestor = 
     getAccessibleMappedPage pdAncestor s0 va1).
 { apply getAccessibleMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
   apply getNbLevelEqOption. }
 rewrite <- Hnewhyp.
 rewrite Htrue.
 unfold not; intros Hfalse; now contradict Hfalse.
Qed.
 
Lemma WriteAccessibleRecPreparePropagateNewProperty va descParent phypage pt currentPart pg:
{{ fun s : state =>
writeAccessibleRecPreparePostcondition  currentPart pg s 
/\ writeAccessibleRecRecurtionInvariantConj va descParent phypage pt currentPart s 
    }} 
Internal.writeAccessibleRecAux (nbPage +1) va descParent false
{{ fun _ s  =>  writeAccessibleRecPreparePostcondition  currentPart pg s  }}.
Proof.
unfold writeAccessibleRecRecurtionInvariantConj, writeAccessibleRecPreparePostcondition.
 revert va descParent  pt phypage .
induction (nbPage + 1).
intros;simpl.
eapply weaken.
eapply WP.ret. simpl.
(** PROVE YOUR POSTCONDITION : True **)
intuition.  
intros.
simpl.
eapply bindRev.
(** getPageRootPartition **)
eapply weaken.
eapply Invariants.getPageRootPartition.
intros; simpl.
pattern s in H.
eapply H.
simpl. 
intros multiplexer.
eapply bindRev.
(** Page.eqb **)
eapply weaken.
eapply Invariants.Page.eqb.
simpl.
intros.
pattern s in H.
eapply H.
simpl.
intros isMultiplexer.
case_eq isMultiplexer.
(** case_eq isMultiplexer true **)
+ intros isMultiplexerT.
  (** ret **)
  eapply weaken.
  eapply WP.ret.
  intros;trivial.
  simpl;trivial.
  intuition. (** PROVE YOUR POSTCONDITION : ~ In pg (getAccessibleMappedPages partition s) **)
(** case_eq isMultiplexer false **)
+ intros isMultiplexerF.
  eapply bindRev.
  (** getSndShadow **)
  eapply weaken.
  eapply Invariants.getSndShadow.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
 unfold consistency in H;intuition.
 (** In descParent (getPartitions MALInternal.multiplexer s)**)
  intros sh2; simpl.
  eapply bindRev.
  (** getNbLevel **)
  eapply weaken.
  eapply Invariants.getNbLevel.
  intros; simpl.
  pattern s in H.
  eapply H.
  intros L; simpl. 
  (** getIndexOfAddr **) 
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getIndexOfAddr.
  simpl; intros.
  pattern s in H.
  eapply H.
  intros lastIndex.
  simpl.
  (** getTableAddr **)
  eapply bindRev.
  eapply weaken.
  eapply GetTableAddr.getTableAddr with (currentPart:= descParent) (idxroot:= idxShadow2).
  simpl. 
  intros.
  split.
  pattern s in H.
  eapply H.
  split.
  intuition.
  split.
  intuition.
  split. 
  intuition.
  exists sh2.
  split. intuition.
  split.
  apply sh2PartNotNull with descParent s;intuition.
  unfold consistency in *;intuition.
  left; split; intuition.
  intros ptsh2. simpl.  
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2:{
  intros.
  destruct H as (H0 & H1).
  assert( (getTableAddrRoot' ptsh2 idxShadow2 descParent va s /\ ptsh2 = pageDefault) \/
  (  isVA ptsh2 (StateLib.getIndexOfAddr va levelMin ) s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s)).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right.
      destruct H1 as (Hget  & Hnew & H1).
      generalize (H1 (StateLib.getIndexOfAddr va levelMin ) );clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(Hpe &Htrue) | (_&Hfalse)]];trivial.
       - contradict Hfalse.
         apply idxSh2idxSh1notEq.
      - split;trivial.
      - contradict Hfalse.
        symmetrynot.
        apply idxPDidxSh2notEq.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP. } 
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptsh2Isnull. simpl.
  case_eq ptsh2Isnull.
  intros.
  eapply WP.weaken.
  eapply WP.ret .
  intros;trivial.
  simpl;trivial. 
  intuition. (** PROVE YOUR POSTCONDITION : true **)
  intros Hptsh2NotNull.
  (** readVirtual **)
  eapply bindRev. 
  eapply weaken.
  2: {  
  intros.
  destruct H as ((H & Hstrong) & Htrue).
  assert(Heqv:  (isVA ptsh2 (StateLib.getIndexOfAddr va levelMin) s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s)).
  { destruct Hstrong as [Hor|Hor].   
    assert(Hfalse: (Nat.eqb pageDefault pageDefault) = false) by (intuition;subst;trivial).
    apply beq_nat_false in Hfalse.
    now contradict Hfalse.
    intuition; subst;trivial. }
  clear Hstrong.
  assert (Hnew:= conj (conj H Heqv) Htrue).
  eapply Hnew. }
  eapply weaken.
  eapply Invariants.readVirtual.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
  subst.
  intuition;
  subst;trivial.
  intros vaInAncestor.
  simpl.
  subst.
  (** getParent **)
  eapply bindRev.
  eapply weaken. 
  eapply Invariants.getParent.
  intros.
  simpl. 
  split.
  pattern s in H.
  eapply H.
  unfold propagatedProperties in *.  
  intuition.
  intros ancestor; simpl.
  (** getPd **)
   eapply bindRev.
  eapply weaken.
  eapply Invariants.getPd.
  simpl; intros.
  split.
  pattern s in H.
  eapply H. split.
  unfold propagatedProperties in H.
  unfold consistency in H.
  intuition.
  destruct H.
  unfold propagatedProperties in H.
  assert (Hparent:  parentInPartitionList s) by (unfold consistency in *;  intuition).
  unfold parentInPartitionList in *.
  apply Hparent with descParent; intuition.
    intros pdAncestor. 
(** setAccessible **)
  unfold setAccessible.
  eapply bindRev.
  (** getDefaultVAddr **)
  eapply weaken.
  eapply Invariants.getDefaultVAddr.
  simpl.
  intros.
  pattern s in H.
  eapply H.
  intros defaultV.
  simpl.
  eapply bindRev.
  (**   VAddr.eqbList **)
  eapply weaken.
  eapply Invariants.VAddr.eqbList.
  simpl.
  intros.
  pattern s in H.
  eapply H.
  intros isdefaultVA.
  (** case negb isdefaultVA **)
  case_eq (isdefaultVA).
  intros.
  eapply weaken.
  eapply WP.ret.
  intros;trivial.
  simpl;trivial. 
  intuition. (** PROVE YOUR POSTCONDITION : ~ In pg (getAccessibleMappedPages partition s) **)
  intros isdefaultVAT.
  eapply bindRev.
  (** getTableAddr **)
  eapply WP.weaken. 
  apply getTableAddr with (currentPart:= ancestor) (idxroot:= idxPageDir).
  simpl.
  intros s H.
  split.
  pattern s in H. 
  eapply H.
  assert(Hancestor: In ancestor (getPartitions pageRootPartition s)).
  { assert(Hparent : parentInPartitionList s) by (unfold consistency in *;intuition).
    apply Hparent with descParent; intuition. }
  split;[intuition|].
  split;[intuition|].      
  split;[intuition|].
  exists pdAncestor.
  split. intuition.
  split.
  apply pdPartNotNull with ancestor s;trivial. 
  intuition.
  unfold consistency in *.
  intuition.
  subst. left. split;intuition.
  intro ptvaInAncestor. simpl.
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2:{
  intros.
  destruct H as (H0 & H1).
  assert( (getTableAddrRoot' ptvaInAncestor idxPageDir ancestor vaInAncestor s /\ ptvaInAncestor = pageDefault) \/
   (isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) s /\ getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s)).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right.
      destruct H1 as (Hget  & Hnew & H1).
      split. 
      generalize (H1 (StateLib.getIndexOfAddr vaInAncestor levelMin ) );clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]];trivial.
       - contradict Hfalse.
         apply idxPDidxSh1notEq.
       - contradict Hfalse.
        apply idxPDidxSh2notEq.
       - assumption.  }  
  assert (HP :=conj H0 H).
  pattern s in HP.
  eapply HP. }
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptvaInAncestorIsnull. simpl.
  case_eq ptvaInAncestorIsnull.
  (** va not mapped in ancestor : ret false **)
  intros HptvaInAncestorIsnulll.
  eapply weaken.
  eapply WP.ret.
  intros;trivial.
  simpl;trivial.
  intuition. (** PROVE YOUR POSTCONDITION : true **)
  intros HptvaInAncestorIsnulll.
  (** va mapped in ancestor **)
  (** StateLib.getIndexOfAddr **)                
  eapply WP.bindRev.
  eapply WP.weaken.
  2:{ intros.
      destruct H as ((H & [(Hptchild& Hnull) | Hptchild] ) & Hptchildnotnull) .
    + subst.  apply beq_nat_false in Hptchildnotnull. intuition.
    + assert (HP := conj (conj H Hptchild) Hptchildnotnull).
      pattern s in HP.
      eapply HP.  }
  eapply weaken.
  apply Invariants.getIndexOfAddr.
  simpl;intros.
  eapply H.
  intros idxva.
  simpl.
  intros.
  eapply bindRev; simpl;[|intros []].
 (** writeAccessible **)
  eapply WP.weaken.
  eapply WP.writeAccessible.
  intros. simpl.
  assert (exists entry0 : Pentry,
    lookup ptvaInAncestor idxva (memory s) pageEq idxEq = Some (PE entry0)) as Hlookup.
  { apply isPELookupEq.
    intuition;subst;trivial. }
  destruct Hlookup as (entry & Hlookup).
  exists entry ; split;trivial. 
  repeat rewrite and_assoc in H.
  destruct H as (Hprecond & (*: DEFINE THE PRECONDITION (if exists) REQUIRED TO PROVE YOUR POSTCONDITION *) Hfalse & Hrest). 
  (** prove that the same page is mapped in the parent and associated to the va stored into the second shadow structure **)
  assert(Heqphy : phypage = pa entry). {
  intuition;subst.
  apply isAccessibleMappedPageGetTableRoot with sh2 descParent ptsh2 va pdAncestor
  ancestor vaInAncestor ptvaInAncestor s;trivial. }
  (** prove that the page is accessible into the parent **)
  assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true). {
  assert(Hcons : consistency s) by (unfold propagatedProperties in *;intuition).
  subst.
  unfold consistency in Hcons.
  apply isAccessibleMappedPageInParentTrue with descParent va (pa entry) ptvaInAncestor ptsh2 pdAncestor;
  intuition;subst;trivial. }
  assert(Hx:= conj Htrue Hrest ).    
(*   assert(Hprecond :True) by trivial. *)  (** DEFINE THE PRECONDITION REQUIRED TO PROVE YOUR POSTCONDITION **)
  assert (H:= conj Hprecond Hx).
  pattern s in H.
  (** add the propeties about writeAccessible post conditions **)
  match type of H with 
  | ?HT s => instantiate (1 := fun tt s => HT s /\ 
              entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) false s /\
              isEntryPage ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) phypage s /\
              entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) true s  ) 
  end.
    clear H.
  simpl.
  set (s' := {| currentPartition := _ |}).  
  rewrite and_assoc.
  split. 
  simpl;trivial.
  (** PROVE YOUR POSTCONDITION : ~ In pg (getAccessibleMappedPages partition s') **)
  intros partition Hpg.
  assert(Hanc: getAncestors currentPart s' = getAncestors currentPart s) by
  (apply getAncestorsUpdateUserFlag; trivial).
  rewrite Hanc in *.
  assert(~ In pg (getAccessibleMappedPages partition s)).
  { unfold not; intros. apply Hprecond with partition; trivial. }
  assert(Hincl : incl (getAccessibleMappedPages partition s') (getAccessibleMappedPages partition s)).
  apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
  unfold incl in *.
  unfold not;intros Hii.
  assert(Htrue1 : ~ In pg (getAccessibleMappedPages partition s)) by 
  trivial.
  apply Htrue1.
  apply Hincl;trivial.
  (** Prove the recursion invariant **)
   simpl in *.
  assert(Hmult : multiplexer = pageRootPartition) by intuition. 
  subst.
  assert(getPartitions pageRootPartition s' = getPartitions pageRootPartition s) as Hpartitions 
        by (apply getPartitionsUpdateUserFlag; trivial).
  apply WriteAccessibleRecRecursionInvariant.
  intuition;subst;trivial.
  unfold writeAccessibleRecInternalPropertiesPrepare;intuition;trivial.
(** RECURSION **)
  intros; simpl; subst.
  eapply weaken.
  eapply IHn with (phypage:= phypage) (pt:= ptvaInAncestor). 
  intros;intuition;subst;trivial.
  unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) by apply pageDecOrNot.
  destruct Hor as [Hor | Hor];[left;trivial|right].
  assert (His : isAncestor currentPart ancestor s).
  { unfold consistency in *;
    apply isAncestorTrans with descParent;intuition. 
    apply nextEntryIsPPgetParent;trivial. }
    unfold isAncestor in *;intuition.
  assert(Hpp :nextEntryIsPP descParent idxParentDesc ancestor s); intuition.
  rewrite nextEntryIsPPgetParent in Hpp.
  unfold consistency in *.
  apply ancestorInPartitionTree with descParent;trivial.
  intuition. intuition.
  unfold getAncestors.
  destruct nbPage;simpl;  rewrite Hpp;
  simpl;left;trivial.
Qed.
