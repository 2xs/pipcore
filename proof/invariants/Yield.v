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


Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Services Pip.Core.Internal.

Require Import Coq.Classes.RelationClasses.
Require Import Lia.

From Pip.Proof Require Import
CheckChild Consistency DependentTypeLemmas GetTableAddr InternalLemmas Invariants Isolation
updateCurPartition WeakestPreconditions.

Lemma switchContextCont (targetPartDesc : page)
                        (targetPageDir  : page)
                        (flagsOnYield   : interruptMask)
                        (targetContext  : contextAddr)
                        :

{{ (* Preconditions *)
  fun s =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s /\
  List.In targetPartDesc (StateLib.getPartitions pageRootPartition s) /\
  targetPartDesc <> pageDefault
}}

switchContextCont targetPartDesc targetPageDir flagsOnYield targetContext

{{ (* Postconditions *)
  fun _ s  =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s
}}.
Proof.

unfold switchContextCont.
(* setInterruptMask *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.setInterruptMask.
cbn.
intros.
apply H.
cbn.
intro u; clear u.

(* updateMMURoot *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.updateMMURoot.
cbn.
intros.
apply H.
cbn.
intro u; clear u.

(* updateCurPartition *)
eapply WP.bindRev.
eapply WP.weaken.
apply updateCurPartitionToPartition.
cbn.
trivial.
cbn.
intro u; clear u.

(* getInterruptMaskFromCtx targetContext *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.getInterruptMaskFromCtx.
cbn.
intros s precondition.
apply precondition.
cbn.
intro interruptMask.

(* setInterruptMask interruptMask *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.setInterruptMask.
intros s precondition.
apply precondition.
cbn.
intro u; clear u.


(* rootPartition := MALInternal.getPageRootPartition *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.getPageRootPartition.
intros s precondition.
apply precondition.
cbn.
intro rootPartition.

(* targetIsRoot := MALInternal.Page.eqb rootPartition targetPartDesc *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.Page.eqb.
intros s precondition.
apply precondition.
cbn.
intro targetPartDescIsRootPartition.

(* targetReqNoInterrupt := IAL.noInterruptRequest interruptMask *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.noInterruptRequest.
intros s precondition.
apply precondition.
cbn.
intro targetReqNoInterrupt.

(*if (targetPartDescIsRootPartition && targetReqNoInterrupt)%bool
  then IAL.loadContext targetContext false
  else IAL.loadContext targetContext true *)
eapply WP.bindRev.
eapply WP.weaken.
case_eq (targetPartDescIsRootPartition && targetReqNoInterrupt)%bool;
  intro H; clear H;
  apply Invariants.loadContext.
intros s precondition.
apply precondition.
cbn.
intro u; clear u.

(* Hardware.ret IAL.SUCCESS *)
eapply WP.weaken.
apply ret.
cbn.
intros s precondition.
intuition.
Qed.

Definition saveSourceContextCont (targetPartDesc           : page)
                                 (targetPageDir            : page)
                                 (sourcePageDir            : page)
                                 (sourceContextSaveVAddr   : vaddr)
                                 (nbL                      : level)
                                 (flagsOnYield             : interruptMask)
                                 (flagsOnWake              : interruptMask)
                                 (sourceInterruptedContext : contextAddr)
                                 (targetContext            : contextAddr)
                                 (* Needed by the proof *)
                                 (sourcePartDesc           : page)
                                 :
{{ (* Preconditions *)
  fun s =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s /\
  List.In targetPartDesc (StateLib.getPartitions pageRootPartition s) /\
  targetPartDesc <> pageDefault /\
  Some nbL = StateLib.getNbLevel /\
  List.In sourcePartDesc (StateLib.getPartitions pageRootPartition s) /\
  StateLib.nextEntryIsPP sourcePartDesc idxPageDir sourcePageDir s
}}

saveSourceContextCont targetPartDesc targetPageDir sourcePageDir
                      sourceContextSaveVAddr nbL flagsOnYield
                      flagsOnWake sourceInterruptedContext
                      targetContext
{{ (* Postconditions *)
  fun _ s  =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s
}}.
Proof.
unfold saveSourceContextCont.

(* sourceCtxLastMMUPage := getTableAddr sourcePageDir sourceContextSaveVAddr nbL *)
eapply WP.bindRev.
eapply WP.weaken.
eapply (getTableAddr sourcePageDir sourceContextSaveVAddr nbL _ sourcePartDesc idxPageDir).
cbn.
intros s preconditions.
split.
apply preconditions.
destruct preconditions as ( _ & _ & _ & H_cons & _ & _ & H_nbL & H_srcPartDesc & H_srcPageDir ).
do 3 (split; trivial).
intuition.
exists sourcePageDir.
split; try assumption.
split;[ | intuition ].
clear H_nbL.

unfold consistency in H_cons.
unfold partitionDescriptorEntry in H_cons.
destruct H_cons as (H_partDescEntry & _).
generalize (H_partDescEntry sourcePartDesc H_srcPartDesc); clear H_partDescEntry; intro H_partDescEntry.
clear H_srcPartDesc.
assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2 \/  idxPageDir  = idxShadow3
  \/  idxPageDir  = idxParentDesc \/  idxPageDir = idxPartDesc) as H_idxMatch by intuition.
generalize (H_partDescEntry idxPageDir H_idxMatch); clear H_partDescEntry; intro H_partDescEntry.
clear H_idxMatch.
destruct H_partDescEntry as ( H_validIdx & _ & H_entry ).
destruct H_entry as (page1 & Hpd & Hnotnull).
unfold StateLib.nextEntryIsPP in *.
destruct (StateLib.Index.succ idxPageDir); try now contradict H_srcPageDir.
destruct (lookup sourcePartDesc i (memory s) pageEq idxEq);
         try now contradict H_srcPageDir.
destruct v ; try now contradict H_srcPageDir.
subst; assumption.

cbn.
intro sourceCtxLastMMUPage.
(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as (H_initPreconditions & H_addProp).
  assert ( StateLib.getTableAddrRoot' sourceCtxLastMMUPage idxPageDir sourcePartDesc sourceContextSaveVAddr s
           /\ sourceCtxLastMMUPage = pageDefault
        \/ StateLib.getTableAddrRoot sourceCtxLastMMUPage idxPageDir sourcePartDesc sourceContextSaveVAddr s
           /\ sourceCtxLastMMUPage <> pageDefault /\
            (forall idx : index,
             StateLib.getIndexOfAddr sourceContextSaveVAddr levelMin = idx ->
             StateLib.isPE sourceCtxLastMMUPage idx s)) as H_cleanedPost.
  {
    destruct H_addProp as [ ( H_getTableAddr & H_nullSrcCtxLastMMUPage )
                          | ( H_getTableAddr & H_notNullSrcCtxLastMMUPage & H_entryType) ].
    + left. split; trivial.
    + right. do 2 (try split; trivial).
      intros idx H_getIndexAddr.
      generalize (H_entryType idx H_getIndexAddr); clear H_entryType; intro H_entryType.
      destruct H_entryType as [ ( _ & Hfalse ) | [ ( _ & Hfalse ) | ( H_PE & _ ) ] ].
      - contradict Hfalse.
        apply InternalLemmas.idxPDidxSh1notEq.
      - contradict Hfalse.
        apply DependentTypeLemmas.idxPDidxSh2notEq.
      - assumption.
  }
  clear H_addProp.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  pattern s in H_newPost.
  eapply H_newPost.
}

(* sourceCtxLastMMUPageIsNull := comparePageToNull sourceCtxLastMMUPage *)
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro sourceCtxLastMMUPageIsNull. cbn.
case_eq sourceCtxLastMMUPageIsNull.
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_srcCtxLastMMUPageIsNotNull.
subst.

(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as ( (H_initPreconditions & H_postGetTableAddr ) & H_srcCtxLastMMUPageIsNotNull).
  apply EqNat.beq_nat_false in H_srcCtxLastMMUPageIsNotNull.
  assert (StateLib.getTableAddrRoot sourceCtxLastMMUPage idxPageDir sourcePartDesc sourceContextSaveVAddr s
       /\ sourceCtxLastMMUPage <> pageDefault
       /\ (forall idx : index,
          StateLib.getIndexOfAddr sourceContextSaveVAddr levelMin = idx ->
          StateLib.isPE sourceCtxLastMMUPage idx s)) as H_cleanedPost.
  {
    destruct H_postGetTableAddr as
      [ ( H_getTableAddr & H_nullSrcCtxLastMMUPage )
      | ( H_getTableAddr & H_notNullSrcCtxLastMMUPage & H_entryType) ].
    + symmetry in H_nullSrcCtxLastMMUPage.
      contradict H_srcCtxLastMMUPageIsNotNull.
      f_equal. assumption.
    + do 2 (try split; trivial).
  }
  clear H_postGetTableAddr H_srcCtxLastMMUPageIsNotNull.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  repeat rewrite and_assoc in H_newPost.
  pattern s in H_newPost.
  eapply H_newPost.
}

(* idxSourceCtxInLastMMUPage := MAL.getIndexOfAddr sourceContextSaveVAddr fstLevel *)
eapply bindRev.
apply Invariants.getIndexOfAddr.
intro idxSourceCtxInLastMMUPage.
cbn.

(* sourceCtxPageIsPresent := MAL.readPresent sourceCtxLastMMUPage idxSourceCtxInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.readPresent.
cbn.

intros s preconditions.
try repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as ((_ & H_isPE) & H_getIdxOfAddr).
apply H_isPE; assumption.

intro sourceCtxPageIsPresent.
cbn.

(* if negb sourceCtxPageIsPresent
   then Hardware.ret IAL.FAIL_CALLER_CONTEXT_SAVE *)
case_eq (negb sourceCtxPageIsPresent).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_srcCtxPageIsPresent.
apply Bool.negb_false_iff in H_srcCtxPageIsPresent.
subst.

(* sourceCtxPageIsAccessible := MAL.readAccessible sourceCtxLastMMUPage idxSourceCtxInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.readAccessible.
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as (((_ & H_isPE) & H_getIdxOfAddr) & _).
apply H_isPE; assumption.

intro sourceCtxPageIsAccessible.
cbn.

(* if negb sourceCtxPageIsAccessible
   then Hardware.ret IAL.FAIL_CALLER_CONTEXT_SAVE *)
case_eq (negb sourceCtxPageIsAccessible).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}

intro H_sourceCtxPageIsAccessible.
apply Bool.negb_false_iff in H_sourceCtxPageIsAccessible.
subst.

(* sourceContextEndSaveVAddr := IAL.getNthVAddrFrom sourceContextSaveVAddr IAL.contextSizeMinusOne *)
eapply bindRev.
eapply weaken.
apply Invariants.getNthVAddrFrom.
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
apply preconditions.
cbn.
intro sourceContextEndSaveVAddr.

(* endAddrOverflow := IAL.firstVAddrGreaterThanSecond sourceContextSaveVAddr sourceContextEndSaveVAddr *)
eapply bindRev.
eapply weaken.
apply Invariants.firstVAddrGreaterThanSecond.
cbn.
intros s preconditions.
apply preconditions.
cbn.
intro endAddrOverflow.

(* if endAddrOverflow
   then Hardware.ret IAL.FAIL_CALLER_CONTEXT_SAVE *)
case_eq endAddrOverflow.
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intro H_noVAddrOverflow.
subst.

(* sourceCtxEndLastMMUPage := Internal.getTableAddr sourcePageDir sourceContextEndSaveVAddr nbL *)
eapply bindRev.
eapply weaken.
eapply (getTableAddr sourcePageDir sourceContextEndSaveVAddr nbL _ sourcePartDesc idxPageDir).
cbn.
intros s preconditions.
split.
apply preconditions.
destruct preconditions as ( _ & _ & _ & H_cons & _ & _ & H_nbL & H_srcPartDesc & H_srcPageDir & _ ).
do 3 (split; trivial).
intuition.
exists sourcePageDir.
split; try assumption.
split;[ | intuition ].
clear H_nbL.

unfold consistency in H_cons.
unfold partitionDescriptorEntry in H_cons.
destruct H_cons as (H_partDescEntry & _).
generalize (H_partDescEntry sourcePartDesc H_srcPartDesc); clear H_partDescEntry; intro H_partDescEntry.
clear H_srcPartDesc.
assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2 \/  idxPageDir  = idxShadow3
  \/  idxPageDir  = idxParentDesc \/  idxPageDir = idxPartDesc) as H_idxMatch by intuition.
generalize (H_partDescEntry idxPageDir H_idxMatch); clear H_partDescEntry; intro H_partDescEntry.
clear H_idxMatch.
destruct H_partDescEntry as ( H_validIdx & _ & H_entry ).
destruct H_entry as (page1 & Hpd & Hnotnull).
unfold StateLib.nextEntryIsPP in *.
destruct (StateLib.Index.succ idxPageDir); try now contradict H_srcPageDir.
destruct (lookup sourcePartDesc i (memory s) pageEq idxEq);
         try now contradict H_srcPageDir.
destruct v ; try now contradict H_srcPageDir.
subst; assumption.

cbn.
intro sourceCtxEndLastMMUPage.
(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as (H_initPreconditions & H_addProp).
  assert ( StateLib.getTableAddrRoot' sourceCtxEndLastMMUPage idxPageDir sourcePartDesc sourceContextEndSaveVAddr s
           /\ sourceCtxEndLastMMUPage = pageDefault
        \/ StateLib.getTableAddrRoot sourceCtxEndLastMMUPage idxPageDir sourcePartDesc sourceContextEndSaveVAddr s
           /\ sourceCtxEndLastMMUPage <> pageDefault /\
            (forall idx : index,
             StateLib.getIndexOfAddr sourceContextEndSaveVAddr levelMin = idx ->
             StateLib.isPE sourceCtxEndLastMMUPage idx s)) as H_cleanedPost.
  {
    destruct H_addProp as [ ( H_getTableAddr & H_nullSrcCtxLastMMUPage )
                          | ( H_getTableAddr & H_notNullSrcCtxLastMMUPage & H_entryType) ].
    + left. split; trivial.
    + right. do 2 (try split; trivial).
      intros idx H_getIndexAddr.
      generalize (H_entryType idx H_getIndexAddr); clear H_entryType; intro H_entryType.
      destruct H_entryType as [ ( _ & Hfalse ) | [ ( _ & Hfalse ) | ( H_PE & _ ) ] ].
      - contradict Hfalse.
        apply InternalLemmas.idxPDidxSh1notEq.
      - contradict Hfalse.
        apply DependentTypeLemmas.idxPDidxSh2notEq.
      - assumption.
  }
  clear H_addProp.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  pattern s in H_newPost.
  eapply H_newPost.
}

(* sourceCtxEndLastMMUPageIsNull := comparePageToNull sourceCtxEndLastMMUPage *)
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro sourceCtxEndLastMMUPageIsNull. cbn.
case_eq sourceCtxEndLastMMUPageIsNull.
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_srcCtxEndLastMMUPageIsNotNull.
subst.

(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as ( (H_initPreconditions & H_postGetTableAddr ) & H_srcCtxEndLastMMUPageIsNotNull).
  apply EqNat.beq_nat_false in H_srcCtxEndLastMMUPageIsNotNull.
  assert (StateLib.getTableAddrRoot sourceCtxEndLastMMUPage idxPageDir sourcePartDesc sourceContextEndSaveVAddr s
       /\ sourceCtxEndLastMMUPage <> pageDefault
       /\ (forall idx : index,
          StateLib.getIndexOfAddr sourceContextEndSaveVAddr levelMin = idx ->
          StateLib.isPE sourceCtxEndLastMMUPage idx s)) as H_cleanedPost.
  {
    destruct H_postGetTableAddr as
      [ ( H_getTableAddr & H_nullSrcCtxEndLastMMUPage )
      | ( H_getTableAddr & H_notNullSrcCtxEndLastMMUPage & H_entryType) ].
    + symmetry in H_nullSrcCtxEndLastMMUPage.
      contradict H_srcCtxEndLastMMUPageIsNotNull.
      f_equal. assumption.
    + do 2 (try split; trivial).
  }
  clear H_postGetTableAddr H_srcCtxEndLastMMUPageIsNotNull.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  repeat rewrite and_assoc in H_newPost.
  pattern s in H_newPost.
  eapply H_newPost.
}

(* idxSourceCtxEndInLastMMUPage := MAL.getIndexOfAddr sourceContextEndSaveVAddr fstLevel *)
eapply bindRev.
apply Invariants.getIndexOfAddr.
intro idxSourceCtxEndInLastMMUPage.
cbn.

(* sourceCtxEndPageIsPresent := MAL.readPresent sourceCtxEndLastMMUPage idxSourceCtxEndInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.readPresent.
cbn.

intros s preconditions.
try repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as ((_ & H_isPE) & H_getIdxOfAddr).
apply H_isPE; assumption.

intro sourceCtxEndPageIsPresent.
cbn.

(* if negb sourceCtxEndPageIsPresent
   then Hardware.ret IAL.FAIL_CALLER_CONTEXT_SAVE *)
case_eq (negb sourceCtxEndPageIsPresent).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_srcCtxEndPageIsPresent.
apply Bool.negb_false_iff in H_srcCtxEndPageIsPresent.
subst.

(* sourceCtxEndPageIsAccessible := MAL.readAccessible sourceCtxEndLastMMUPage idxSourceCtxEndInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.readAccessible.
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as (((_ & H_isPE) & H_getIdxOfAddr) & _ ).
apply H_isPE; assumption.

intro sourceCtxEndPageIsAccessible.
cbn.

(* if negb sourceCtxEndPageIsAccessible
   then Hardware.ret IAL.FAIL_CALLER_CONTEXT_SAVE *)
case_eq (negb sourceCtxEndPageIsAccessible).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}

intro H_sourceCtxEndPageIsAccessible.
apply Bool.negb_false_iff in H_sourceCtxEndPageIsAccessible.
subst.

(* IAL.writeContext sourceInterruptedContext sourceContextSaveVAddr flagsOnWake *)
eapply bindRev.
eapply weaken.
apply Invariants.writeContext.
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
destruct preconditions as (H_part & H_kern & H_vert & H_cons & H_targetPartDescInPartList
                         & H_targetPartNotDef & _).
assert (preconditions := conj H_part
                        (conj H_kern
                        (conj H_vert
                        (conj H_cons
                        (conj H_targetPartDescInPartList
                              H_targetPartNotDef
                        ))))
       ).
pattern s in preconditions.
apply preconditions.
cbn.
intro u; clear u.

eapply WP.weaken.
apply switchContextCont.
cbn.
trivial.
Qed.

Lemma getTargetContextCont (targetPartDesc : page)
			                     (targetPageDir  : page)
			                     (targetVidt     : page)
			                     (sourcePageDir  : page)
                           (sourceContextSaveVaddr : vaddr)
			                     (targetInterrupt : index)
			                     (nbL : level)
			                     (flagsOnYield   : interruptMask)
			                     (flagsOnWake    : interruptMask)
			                     (sourceInterruptedContext : contextAddr)
                           (* Needed by the proof *)
                           (sourcePartDesc           : page)
                           :
{{ (* Preconditions *)
  fun s =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s /\
  List.In targetPartDesc (StateLib.getPartitions pageRootPartition s) /\
  StateLib.nextEntryIsPP targetPartDesc idxPageDir targetPageDir s /\
  targetPartDesc <> pageDefault /\
  Some nbL = StateLib.getNbLevel /\
  List.In sourcePartDesc (StateLib.getPartitions pageRootPartition s) /\
  StateLib.nextEntryIsPP sourcePartDesc idxPageDir sourcePageDir s
}}

getTargetContextCont targetPartDesc targetPageDir targetVidt sourcePageDir
                     sourceContextSaveVaddr targetInterrupt nbL flagsOnYield
			               flagsOnWake sourceInterruptedContext
{{ (* Postconditions *)
  fun _ s  =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s
}}.
Proof.
unfold getTargetContextCont.

(* targetContextVAddr := MAL.readVirtualUser targetVidt targetInterrupt *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.readVirtualUser.
cbn.
intros s preconditions.
apply preconditions.
cbn.
intro targetContextVAddr.

(* targetContextLastMMUPage := Internal.getTableAddr targetPageDir targetContextVAddr nbL *)
eapply WP.bindRev.
eapply WP.weaken.
eapply (getTableAddr targetPageDir targetContextVAddr nbL _ targetPartDesc idxPageDir).
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
destruct preconditions as ( _ & _ & _ & H_cons & H_tgtPartDesc & H_tgtPageDir & _ & H_nbL & _ ).
do 3 (split; trivial).
intuition.
exists targetPageDir.
split; try assumption.
split;[ | intuition ].
clear H_nbL.

unfold consistency in H_cons.
unfold partitionDescriptorEntry in H_cons.
destruct H_cons as (H_partDescEntry & _).
generalize (H_partDescEntry targetPartDesc H_tgtPartDesc); clear H_partDescEntry; intro H_partDescEntry.
clear H_tgtPartDesc.
assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2 \/  idxPageDir  = idxShadow3
  \/  idxPageDir  = idxParentDesc \/  idxPageDir = idxPartDesc) as H_idxMatch by intuition.
generalize (H_partDescEntry idxPageDir H_idxMatch); clear H_partDescEntry; intro H_partDescEntry.
clear H_idxMatch.
destruct H_partDescEntry as ( H_validIdx & _ & H_entry ).
destruct H_entry as (page1 & Hpd & Hnotnull).
unfold StateLib.nextEntryIsPP in *.
destruct (StateLib.Index.succ idxPageDir); try now contradict H_tgtPageDir.
destruct (lookup targetPartDesc i (memory s) pageEq idxEq);
         try now contradict H_tgtPageDir.
destruct v ; try now contradict H_tgtPageDir.
subst; assumption.

cbn.
intro targetContextLastMMUPage.
(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as (H_initPreconditions & H_addProp).
  assert ( StateLib.getTableAddrRoot' targetContextLastMMUPage idxPageDir targetPartDesc targetContextVAddr s
           /\ targetContextLastMMUPage = pageDefault
        \/ StateLib.getTableAddrRoot targetContextLastMMUPage idxPageDir targetPartDesc targetContextVAddr s
           /\ targetContextLastMMUPage <> pageDefault /\
            (forall idx : index,
             StateLib.getIndexOfAddr targetContextVAddr levelMin = idx ->
             StateLib.isPE targetContextLastMMUPage idx s)) as H_cleanedPost.
  {
    destruct H_addProp as [ ( H_getTableAddr & H_nullTgtCtxLastMMUPage )
                          | ( H_getTableAddr & H_notNullTgtCtxLastMMUPage & H_entryType) ].
    + left. split; trivial.
    + right. do 2 (try split; trivial).
      intros idx H_getIndexAddr.
      generalize (H_entryType idx H_getIndexAddr); clear H_entryType; intro H_entryType.
      destruct H_entryType as [ ( _ & Hfalse ) | [ ( _ & Hfalse ) | ( H_PE & _ ) ] ].
      - contradict Hfalse.
        apply InternalLemmas.idxPDidxSh1notEq.
      - contradict Hfalse.
        apply DependentTypeLemmas.idxPDidxSh2notEq.
      - assumption.
  }
  clear H_addProp.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  pattern s in H_newPost.
  eapply H_newPost.
}

(* targetContextLastMMUPageisNull := Internal.comparePageToNull targetContextLastMMUPage *)
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro targetContextLastMMUPageIsNull. cbn.
case_eq targetContextLastMMUPageIsNull.
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_targetContextLastMMUPageIsNull.
subst.

(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as ( (H_initPreconditions & H_postGetTableAddr ) & H_targetContextLastMMUPageIsNotNull).
  apply EqNat.beq_nat_false in H_targetContextLastMMUPageIsNotNull.
  assert (StateLib.getTableAddrRoot targetContextLastMMUPage idxPageDir targetPartDesc targetContextVAddr s
       /\ targetContextLastMMUPage <> pageDefault
       /\ (forall idx : index,
          StateLib.getIndexOfAddr targetContextVAddr levelMin = idx ->
          StateLib.isPE targetContextLastMMUPage idx s)) as H_cleanedPost.
  {
    destruct H_postGetTableAddr as
      [ ( H_getTableAddr & H_nullTgtCtxLastMMUPage )
      | ( H_getTableAddr & H_notNullTgtCtxLastMMUPage & H_entryType) ].
    + symmetry in H_nullTgtCtxLastMMUPage.
      contradict H_targetContextLastMMUPageIsNotNull.
      f_equal. assumption.
    + do 2 (try split; trivial).
  }
  clear H_postGetTableAddr H_targetContextLastMMUPageIsNotNull.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  repeat rewrite and_assoc in H_newPost.
  pattern s in H_newPost.
  eapply H_newPost.
}

(* idxTargetContextPageInLastMMUPage := MAL.getIndexOfAddr targetContextVAddr fstLevel *)
eapply WP.bindRev.
eapply Invariants.getIndexOfAddr.
cbn.
intro idxTargetContextPageInLastMMUPage.

(* targetContextPageIsPresent := MAL.readPresent targetContextLastMMUPage idxTargetContextPageInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.readPresent.
cbn.

intros s preconditions.
try repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as ((_ & H_isPE) & H_getIdxOfAddr).
apply H_isPE; assumption.

intro targetContextPageIsPresent.
cbn.

(* if negb targetContextPageIsPresent
   then Hardware.ret IAL.FAIL_UNAVAILABLE_TARGET_CTX *)
case_eq (negb targetContextPageIsPresent).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_targetContextPageIsPresent.
apply Bool.negb_false_iff in H_targetContextPageIsPresent.
subst.

(* targetContextPageIsAccessible := MAL.readAccessible targetContextLastMMUPage idxTargetContextPageInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.readAccessible.
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as (((_ & H_isPE) & H_getIdxOfAddr) & _ ).
apply H_isPE; assumption.

intro targetContextPageIsAccessible.
cbn.

(* if negb targetContextPageIsAccessible
   then Hardware.ret IAL.FAIL_UNAVAILABLE_TARGET_CTX *)
case_eq (negb targetContextPageIsAccessible).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}

intro H_targetContextPageIsAccessible.
apply Bool.negb_false_iff in H_targetContextPageIsAccessible.
subst.

(* targetContextEndVAddr := IAL.getNthVAddrFrom targetContextVAddr IAL.contextSizeMinusOne *)
eapply bindRev.
eapply weaken.
apply Invariants.getNthVAddrFrom.
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
apply preconditions.
cbn.
intro targetContextEndVAddr.

(* targetContextEndVAddrOverflow := IAL.firstVAddrGreaterThanSecond targetContextVAddr targetContextEndVAddr *)
eapply bindRev.
eapply weaken.
apply Invariants.firstVAddrGreaterThanSecond.
cbn.
intros s preconditions.
apply preconditions.
cbn.
intro endAddrOverflow.

(* if endAddrOverflow
   then Hardware.ret IAL.FAIL_UNAVAILABLE_TARGET_CTX *)
case_eq endAddrOverflow.
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intro H_noVAddrOverflow.
subst.

(* targetContextEndLastMMUPage := Internal.getTableAddr targetPageDir targetContextEndVAddr nbL *)
eapply bindRev.
eapply weaken.
eapply (getTableAddr targetPageDir targetContextEndVAddr nbL _ targetPartDesc idxPageDir).
cbn.
intros s preconditions.
split.
apply preconditions.
destruct preconditions as ( _ & _ & _ & H_cons & H_tgtPartDesc & H_tgtPageDir & _ & H_nbL & _ ).
do 3 (split; trivial).
intuition.
exists targetPageDir.
split; try assumption.
split;[ | intuition ].
clear H_nbL.

unfold consistency in H_cons.
unfold partitionDescriptorEntry in H_cons.
destruct H_cons as (H_partDescEntry & _).
generalize (H_partDescEntry targetPartDesc H_tgtPartDesc); clear H_partDescEntry; intro H_partDescEntry.
clear H_tgtPartDesc.
assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2 \/  idxPageDir  = idxShadow3
  \/  idxPageDir  = idxParentDesc \/  idxPageDir = idxPartDesc) as H_idxMatch by intuition.
generalize (H_partDescEntry idxPageDir H_idxMatch); clear H_partDescEntry; intro H_partDescEntry.
clear H_idxMatch.
destruct H_partDescEntry as ( H_validIdx & _ & H_entry ).
destruct H_entry as (page1 & Hpd & Hnotnull).
unfold StateLib.nextEntryIsPP in *.
destruct (StateLib.Index.succ idxPageDir); try now contradict H_tgtPageDir.
destruct (lookup targetPartDesc i (memory s) pageEq idxEq);
         try now contradict H_tgtPageDir.
destruct v ; try now contradict H_tgtPageDir.
subst; assumption.

cbn.
intro targetContextEndLastMMUPage.
(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as (H_initPreconditions & H_addProp).
  assert ( StateLib.getTableAddrRoot' targetContextEndLastMMUPage idxPageDir targetPartDesc targetContextEndVAddr s
           /\ targetContextEndLastMMUPage = pageDefault
        \/ StateLib.getTableAddrRoot targetContextEndLastMMUPage idxPageDir targetPartDesc targetContextEndVAddr s
           /\ targetContextEndLastMMUPage <> pageDefault /\
            (forall idx : index,
             StateLib.getIndexOfAddr targetContextEndVAddr levelMin = idx ->
             StateLib.isPE targetContextEndLastMMUPage idx s)) as H_cleanedPost.
  {
    destruct H_addProp as [ ( H_getTableAddr & H_nullTgtCtxEndLastMMUPage )
                          | ( H_getTableAddr & H_notNullTgtCtxEndLastMMUPage & H_entryType) ].
    + left. split; trivial.
    + right. do 2 (try split; trivial).
      intros idx H_getIndexAddr.
      generalize (H_entryType idx H_getIndexAddr); clear H_entryType; intro H_entryType.
      destruct H_entryType as [ ( _ & Hfalse ) | [ ( _ & Hfalse ) | ( H_PE & _ ) ] ].
      - contradict Hfalse.
        apply InternalLemmas.idxPDidxSh1notEq.
      - contradict Hfalse.
        apply DependentTypeLemmas.idxPDidxSh2notEq.
      - assumption.
  }
  clear H_addProp.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  pattern s in H_newPost.
  eapply H_newPost.
}

(* targetContextEndLastMMUPageisNull := Internal.comparePageToNull targetContextEndLastMMUPage *)
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro targetContextEndLastMMUPageisNull. cbn.
case_eq targetContextEndLastMMUPageisNull.
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_tgtCtxEndLastMMUPageIsNotNull.
subst.

(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as ( (H_initPreconditions & H_postGetTableAddr ) & H_tgtCtxEndLastMMUPageIsNotNull).
  apply EqNat.beq_nat_false in H_tgtCtxEndLastMMUPageIsNotNull.
  assert (StateLib.getTableAddrRoot targetContextEndLastMMUPage idxPageDir targetPartDesc targetContextEndVAddr s
       /\ targetContextEndLastMMUPage <> pageDefault
       /\ (forall idx : index,
          StateLib.getIndexOfAddr targetContextEndVAddr levelMin = idx ->
          StateLib.isPE targetContextEndLastMMUPage idx s)) as H_cleanedPost.
  {
    destruct H_postGetTableAddr as
      [ ( H_getTableAddr & H_nullTgtCtxEndLastMMUPage )
      | ( H_getTableAddr & H_notNullTgtCtxEndLastMMUPage & H_entryType) ].
    + symmetry in H_nullTgtCtxEndLastMMUPage.
      contradict H_tgtCtxEndLastMMUPageIsNotNull.
      f_equal. assumption.
    + do 2 (try split; trivial).
  }
  clear H_postGetTableAddr H_tgtCtxEndLastMMUPageIsNotNull.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  repeat rewrite and_assoc in H_newPost.
  pattern s in H_newPost.
  eapply H_newPost.
}

(* idxTargetContextEndPageInLastMMUPage := MAL.getIndexOfAddr targetContextEndVAddr fstLevel *)
eapply bindRev.
apply Invariants.getIndexOfAddr.
intro idxTargetContextEndPageInLastMMUPage.
cbn.

(* targetContextEndPageIsPresent := MAL.readPresent targetContextEndLastMMUPage idxSourceCtxEndInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.readPresent.
cbn.

intros s preconditions.
try repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as ((_ & H_isPE) & H_getIdxOfAddr).
apply H_isPE; assumption.

intro targetContextEndPageIsPresent.
cbn.

(* if negb targetContextEndPageIsPresent
   then Hardware.ret IAL.FAIL_UNAVAILABLE_TARGET_CTX *)
case_eq (negb targetContextEndPageIsPresent).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_targetContextEndPageIsPresent.
apply Bool.negb_false_iff in H_targetContextEndPageIsPresent.
subst.

(* targetContextEndPageIsAccessible := MAL.readAccessible targetContextEndLastMMUPage idxTargetContextEndPageInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.readAccessible.
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as (((_ & H_isPE) & H_getIdxOfAddr) & _ ).
apply H_isPE; assumption.

intro targetContextEndPageIsAccessible.
cbn.

(* if negb targetContextEndPageIsAccessible
   then Hardware.ret IAL.FAIL_UNAVAILABLE_TARGET_CTX *)
case_eq (negb targetContextEndPageIsAccessible).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}

intro H_targetContextEndPageIsAccessible.
apply Bool.negb_false_iff in H_targetContextEndPageIsAccessible.
subst.

(* targetContext := IAL.vaddrToContextAddr targetContextVAddr *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.vaddrToContextAddr.
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
apply preconditions.
cbn.

intro targetContext.

(* sourceContextSaveVaddrIsNull := Internal.compareVAddrToNull sourceContextSaveVaddr *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.compareVAddrToNull.
cbn.
intros s preconditions.
apply preconditions.
intro sourceContextSaveVaddrIsNull. cbn.
case_eq sourceContextSaveVaddrIsNull.
{ intros.
  eapply WP.weaken.
  apply (switchContextCont targetPartDesc targetPageDir flagsOnYield targetContext).
  intros s preconditions.
  cbn.
  intuition.
}
{
  intros.
  eapply WP.weaken.
  apply (saveSourceContextCont targetPartDesc targetPageDir sourcePageDir sourceContextSaveVaddr nbL
         flagsOnYield flagsOnWake sourceInterruptedContext targetContext sourcePartDesc).
  intros s preconditions.
  cbn.
  intuition.
}
Qed.

Lemma getTargetVidtCont (targetPartDesc : page)
	                      (sourcePageDir : page)
		                    (vidtVAddr : vaddr)
		                    (sourceContextSaveVAddr : vaddr)
		                    (targetInterrupt : index)
		                    (nbL : level)
		                    (idxVidtInLastMMUPage : index)
		                    (flagsOnYield : interruptMask)
		                    (flagsOnWake : interruptMask)
		                    (sourceInterruptedContext : contextAddr)
                        (* Needed by the proof *)
                        (sourcePartDesc           : page)
                        :
{{ (* Preconditions *)
  fun s =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s /\
  List.In targetPartDesc (StateLib.getPartitions pageRootPartition s) /\
  targetPartDesc <> pageDefault /\
  Some nbL = StateLib.getNbLevel /\
  StateLib.getIndexOfAddr vidtVAddr levelMin = idxVidtInLastMMUPage /\
  List.In sourcePartDesc (StateLib.getPartitions pageRootPartition s) /\
  StateLib.nextEntryIsPP sourcePartDesc idxPageDir sourcePageDir s
}}

getTargetVidtCont targetPartDesc sourcePageDir vidtVAddr sourceContextSaveVAddr targetInterrupt
                  nbL idxVidtInLastMMUPage flagsOnYield flagsOnWake sourceInterruptedContext

{{ (* Postconditions *)
  fun _ s  =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s
}}.
Proof.
unfold getTargetVidtCont.

(* targetPageDir := Internal.getPd targetPartDesc *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.getPd.
cbn.
intros s preconditions.
split.
apply preconditions.
split; unfold consistency in preconditions; try intuition.

intro targetPageDir.
cbn.

(* targetVidtLastMMUPage := Internal.getTableAddr targetPageDir vidtVAddr nbL *)
eapply WP.bindRev.
eapply WP.weaken.
eapply (getTableAddr targetPageDir vidtVAddr nbL _ targetPartDesc idxPageDir).
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
destruct preconditions as ( _ & _ & _ & H_cons & H_tgtPartDesc & _ & H_nbL & _ & _ & _ & H_tgtPageDir ).
do 3 (split; trivial).
intuition.
exists targetPageDir.
split; try assumption.
split;[ | intuition ].
clear H_nbL.

unfold consistency in H_cons.
unfold partitionDescriptorEntry in H_cons.
destruct H_cons as (H_partDescEntry & _).
generalize (H_partDescEntry targetPartDesc H_tgtPartDesc); clear H_partDescEntry; intro H_partDescEntry.
clear H_tgtPartDesc.
assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2 \/  idxPageDir  = idxShadow3
  \/  idxPageDir  = idxParentDesc \/  idxPageDir = idxPartDesc) as H_idxMatch by intuition.
generalize (H_partDescEntry idxPageDir H_idxMatch); clear H_partDescEntry; intro H_partDescEntry.
clear H_idxMatch.
destruct H_partDescEntry as ( H_validIdx & _ & H_entry ).
destruct H_entry as (page1 & Hpd & Hnotnull).
unfold StateLib.nextEntryIsPP in *.
destruct (StateLib.Index.succ idxPageDir); try now contradict H_tgtPageDir.
destruct (lookup targetPartDesc i (memory s) pageEq idxEq);
         try now contradict H_tgtPageDir.
destruct v ; try now contradict H_tgtPageDir.
subst; assumption.

cbn.
intro targetVidtLastMMUPage.
(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as (H_initPreconditions & H_addProp).
  assert ( StateLib.getTableAddrRoot' targetVidtLastMMUPage idxPageDir targetPartDesc vidtVAddr s
           /\ targetVidtLastMMUPage = pageDefault
        \/ StateLib.getTableAddrRoot targetVidtLastMMUPage idxPageDir targetPartDesc vidtVAddr s
           /\ targetVidtLastMMUPage <> pageDefault /\
            (forall idx : index,
             StateLib.getIndexOfAddr vidtVAddr levelMin = idx ->
             StateLib.isPE targetVidtLastMMUPage idx s)) as H_cleanedPost.
  {
    destruct H_addProp as [ ( H_getTableAddr & H_nullTgtCtxLastMMUPage )
                          | ( H_getTableAddr & H_notNullTgtCtxLastMMUPage & H_entryType) ].
    + left. split; trivial.
    + right. do 2 (try split; trivial).
      intros idx H_getIndexAddr.
      generalize (H_entryType idx H_getIndexAddr); clear H_entryType; intro H_entryType.
      destruct H_entryType as [ ( _ & Hfalse ) | [ ( _ & Hfalse ) | ( H_PE & _ ) ] ].
      - contradict Hfalse.
        apply InternalLemmas.idxPDidxSh1notEq.
      - contradict Hfalse.
        apply DependentTypeLemmas.idxPDidxSh2notEq.
      - assumption.
  }
  clear H_addProp.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  pattern s in H_newPost.
  eapply H_newPost.
}

(* targetVidtLastMMUPageisNull := Internal.comparePageToNull targetVidtLastMMUPage *)
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro targetVidtLastMMUPageisNull. cbn.
case_eq targetVidtLastMMUPageisNull.
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_targetVidtLastMMUPageisNull.
subst.

(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as ( (H_initPreconditions & H_postGetTableAddr ) & H_targetVidtLastMMUPageisNotNull).
  apply EqNat.beq_nat_false in H_targetVidtLastMMUPageisNotNull.
  assert (StateLib.getTableAddrRoot targetVidtLastMMUPage idxPageDir targetPartDesc vidtVAddr s
       /\ targetVidtLastMMUPage <> pageDefault
       /\ (forall idx : index,
          StateLib.getIndexOfAddr vidtVAddr levelMin = idx ->
          StateLib.isPE targetVidtLastMMUPage idx s)) as H_cleanedPost.
  {
    destruct H_postGetTableAddr as
      [ ( H_getTableAddr & H_nullTgtVidtLastMMUPage )
      | ( H_getTableAddr & H_notNullTgtVidtLastMMUPage & H_entryType) ].
    + symmetry in H_nullTgtVidtLastMMUPage.
      contradict H_targetVidtLastMMUPageisNotNull.
      f_equal. assumption.
    + do 2 (try split; trivial).
  }
  clear H_postGetTableAddr H_targetVidtLastMMUPageisNotNull.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  repeat rewrite and_assoc in H_newPost.
  pattern s in H_newPost.
  eapply H_newPost.
}

(* targetVidtIsPresent := MAL.readPresent targetVidtLastMMUPage idxVidtInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.readPresent.
cbn.

intros s preconditions.
try repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as ((((((( _ & H_getIdxOfAddr ) & _ ) & _ ) & _ ) & _ ) & _ ) & H_isPE).
apply H_isPE; assumption.

intro targetVidtIsPresent.
cbn.

(* if negb targetVidtIsPresent
   then Hardware.ret IAL.FAIL_UNAVAILABLE_TARGET_VIDT *)
case_eq (negb targetVidtIsPresent).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_targetVidtIsPresent.
apply Bool.negb_false_iff in H_targetVidtIsPresent.
subst.

(* targetVidtIsAccessible := MAL.readAccessible targetVidtLastMMUPage idxVidtInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.readAccessible.
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as (((((((( _ & H_getIdxOfAddr ) & _ ) & _ ) & _ ) & _ ) & _ ) & H_isPE) & _ ).
apply H_isPE; assumption.

intro targetVidtIsAccessible.
cbn.

(* if negb targetVidtIsAccessible
   then Hardware.ret IAL.FAIL_UNAVAILABLE_TARGET_VIDT *)
case_eq (negb targetVidtIsAccessible).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_targetVidtIsAccessible.
apply Bool.negb_false_iff in H_targetVidtIsAccessible.
subst.


(* targetVidt := MAL.readPhyEntry targetVidtLastMMUPage idxVidtInLastMMUPage *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.readPhyEntry.
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split. apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as ((((((((( _ & H_getIdxOfAddr ) & _ ) & _ ) & _ ) & _ ) & _ ) & H_isPE ) & _ ) & _ ).
apply H_isPE; assumption.

intro targetVidt.
cbn.

(* getTargetContextCont targetPartDesc targetPageDir targetVidt sourcePageDir sourceContextSaveVAddr
                        targetInterrupt nbL flagsOnYield flagsOnWake sourceInterruptedContext *)
eapply WP.weaken.
apply (getTargetContextCont targetPartDesc targetPageDir targetVidt sourcePageDir sourceContextSaveVAddr
			                      targetInterrupt nbL flagsOnYield flagsOnWake sourceInterruptedContext sourcePartDesc).
intros s preconditions.
cbn.
intuition.
Qed.

Lemma getSourceVidtCont (targetPartDesc : page)
                        (sourcePageDir  : page)
                        (targetInterrupt : index)
                        (sourceContextSaveIndex : index)
                        (nbL                    : level)
                        (flagsOnYield : interruptMask)
                        (flagsOnWake  : interruptMask)
                        (sourceInterruptedContext : contextAddr)
                        (* Needed by the proof *)
                        (sourcePartDesc           : page)
                        :
{{ (* Preconditions *)
  fun s =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s /\
  List.In targetPartDesc (StateLib.getPartitions pageRootPartition s) /\
  targetPartDesc <> pageDefault /\
  Some nbL = StateLib.getNbLevel /\
  List.In sourcePartDesc (StateLib.getPartitions pageRootPartition s) /\
  StateLib.nextEntryIsPP sourcePartDesc idxPageDir sourcePageDir s
}}

getSourceVidtCont targetPartDesc sourcePageDir targetInterrupt sourceContextSaveIndex nbL
				          flagsOnYield flagsOnWake sourceInterruptedContext
{{ (* Postconditions *)
  fun _ s  =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s
}}.
Proof.
unfold getSourceVidtCont.

(* vidtVAddr := getVaddrVIDT *)
eapply WP.bindRev.
eapply Invariants.getVaddrVIDT.
intro vidtVAddr.
cbn.

(* idxVidtInLastMMUPage := MAL.getIndexOfAddr vidtVAddr fstLevel *)
eapply bindRev.
apply Invariants.getIndexOfAddr.
intro idxVidtInLastMMUPage.
cbn.

(* sourceVidtLastMMUPage := Internal.getTableAddr sourcePageDir vidtVAddr nbL *)
eapply WP.bindRev.
eapply WP.weaken.
eapply (getTableAddr sourcePageDir vidtVAddr nbL _ sourcePartDesc idxPageDir).
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
destruct preconditions as ( _ & _ & _ & H_cons & _ & _ & H_nbL & H_srcPartDesc & H_srcPageDir & _ ).
do 3 (split; trivial).
intuition.
exists sourcePageDir.
split; try assumption.
split;[ | intuition ].
clear H_nbL.

unfold consistency in H_cons.
unfold partitionDescriptorEntry in H_cons.
destruct H_cons as (H_partDescEntry & _).
generalize (H_partDescEntry sourcePartDesc H_srcPartDesc); clear H_partDescEntry; intro H_partDescEntry.
clear H_srcPartDesc.
assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2 \/  idxPageDir  = idxShadow3
  \/  idxPageDir  = idxParentDesc \/  idxPageDir = idxPartDesc) as H_idxMatch by intuition.
generalize (H_partDescEntry idxPageDir H_idxMatch); clear H_partDescEntry; intro H_partDescEntry.
clear H_idxMatch.
destruct H_partDescEntry as ( H_validIdx & _ & H_entry ).
destruct H_entry as (page1 & Hpd & Hnotnull).
unfold StateLib.nextEntryIsPP in *.
destruct (StateLib.Index.succ idxPageDir); try now contradict H_srcPageDir.
destruct (lookup sourcePartDesc i (memory s) pageEq idxEq);
         try now contradict H_srcPageDir.
destruct v ; try now contradict H_srcPageDir.
subst; assumption.

cbn.
intro sourceVidtLastMMUPage.
(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as (H_initPreconditions & H_addProp).
  assert ( StateLib.getTableAddrRoot' sourceVidtLastMMUPage idxPageDir sourcePartDesc vidtVAddr s
           /\ sourceVidtLastMMUPage = pageDefault
        \/ StateLib.getTableAddrRoot sourceVidtLastMMUPage idxPageDir sourcePartDesc vidtVAddr s
           /\ sourceVidtLastMMUPage <> pageDefault /\
            (forall idx : index,
             StateLib.getIndexOfAddr vidtVAddr levelMin = idx ->
             StateLib.isPE sourceVidtLastMMUPage idx s)) as H_cleanedPost.
  {
    destruct H_addProp as [ ( H_getTableAddr & H_nullSrcVidtLastMMUPage )
                          | ( H_getTableAddr & H_notNullSrcVidtLastMMUPage & H_entryType) ].
    + left. split; trivial.
    + right. do 2 (try split; trivial).
      intros idx H_getIndexAddr.
      generalize (H_entryType idx H_getIndexAddr); clear H_entryType; intro H_entryType.
      destruct H_entryType as [ ( _ & Hfalse ) | [ ( _ & Hfalse ) | ( H_PE & _ ) ] ].
      - contradict Hfalse.
        apply InternalLemmas.idxPDidxSh1notEq.
      - contradict Hfalse.
        apply DependentTypeLemmas.idxPDidxSh2notEq.
      - assumption.
  }
  clear H_addProp.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  pattern s in H_newPost.
  eapply H_newPost.
}

(* sourceVidtLastMMUPageisNull := Internal.comparePageToNull sourceVidtLastMMUPage *)
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro sourceVidtLastMMUPageisNull. cbn.
case_eq sourceVidtLastMMUPageisNull.
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_sourceVidtLastMMUPageisNull.
subst.

(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as ( (H_initPreconditions & H_postGetTableAddr ) & H_sourceVidtLastMMUPageisNotNull).
  apply EqNat.beq_nat_false in H_sourceVidtLastMMUPageisNotNull.
  assert (StateLib.getTableAddrRoot sourceVidtLastMMUPage idxPageDir sourcePartDesc vidtVAddr s
       /\ sourceVidtLastMMUPage <> pageDefault
       /\ (forall idx : index,
          StateLib.getIndexOfAddr vidtVAddr levelMin = idx ->
          StateLib.isPE sourceVidtLastMMUPage idx s)) as H_cleanedPost.
  {
    destruct H_postGetTableAddr as
      [ ( H_getTableAddr & H_nullSrcVidtLastMMUPage )
      | ( H_getTableAddr & H_notNullSrcVidtLastMMUPage & H_entryType) ].
    + symmetry in H_nullSrcVidtLastMMUPage.
      contradict H_sourceVidtLastMMUPageisNotNull.
      f_equal. assumption.
    + do 2 (try split; trivial).
  }
  clear H_postGetTableAddr H_sourceVidtLastMMUPageisNotNull.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  repeat rewrite and_assoc in H_newPost.
  pattern s in H_newPost.
  eapply H_newPost.
}

(* sourceVidtIsPresent := MAL.readPresent sourceVidtLastMMUPage idxVidtInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.readPresent.
cbn.

intros s preconditions.
try repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as (((( _ & H_getIdxOfAddr ) & _ ) & _ ) & H_isPE).
apply H_isPE; assumption.

intro sourceVidtIsPresent.
cbn.

(* if negb sourceVidtIsPresent
   then Hardware.ret IAL.FAIL_UNAVAILABLE_CALLER_VIDT *)
case_eq (negb sourceVidtIsPresent).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_sourceVidtIsPresent.
apply Bool.negb_false_iff in H_sourceVidtIsPresent.
subst.

(* sourceVidtIsAccessible := MAL.readAccessible sourceVidtLastMMUPage idxVidtInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.readAccessible.
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as ((((( _ & H_getIdxOfAddr ) & _ ) & _ ) & H_isPE) & _ ).
apply H_isPE; assumption.

intro sourceVidtIsAccessible.
cbn.

(* if negb sourceVidtIsAccessible
   then Hardware.ret IAL.FAIL_UNAVAILABLE_CALLER_VIDT *)
case_eq (negb sourceVidtIsAccessible).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_sourceVidtIsAccessible.
apply Bool.negb_false_iff in H_sourceVidtIsAccessible.
subst.


(* sourceVidt := MAL.readPhyEntry sourceVidtLastMMUPage idxVidtInLastMMUPage *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.readPhyEntry.
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split. apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as (((((( _ & H_getIdxOfAddr ) & _ ) & _ ) & H_isPE ) & _ ) & _ ).
apply H_isPE; assumption.

intro sourceVidt.
cbn.

(* sourceContextSaveVAddr := MAL.readVirtualUser sourceVidt sourceContextSaveIndex *)
eapply WP.bindRev.
apply Invariants.readVirtualUser.
intro sourceContextSaveVAddr.

(* getTargetVidtCont targetPartDesc sourcePageDir vidtVAddr sourceContextSaveVAddr
                     targetInterrupt nbL idxVidtInLastMMUPage flagsOnYield flagsOnWake *)
eapply WP.weaken.
apply (getTargetVidtCont targetPartDesc sourcePageDir vidtVAddr sourceContextSaveVAddr
       targetInterrupt nbL idxVidtInLastMMUPage flagsOnYield flagsOnWake sourceInterruptedContext
       sourcePartDesc).
intros s preconditions.
cbn.
intuition.
Qed.

Lemma getParentPartDescCont (sourcePartDesc : page)
                            (sourcePageDir : page)
                            (targetInterrupt : index)
                            (sourceContextSaveIndex : index)
                            (nbL : level)
                            (flagsOnYield : interruptMask)
                            (flagsOnWake : interruptMask)
                            (sourceInterruptedContext : contextAddr)
                            :
{{ (* Preconditions *)
  fun s =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s /\
  Some nbL = StateLib.getNbLevel /\
  List.In sourcePartDesc (StateLib.getPartitions pageRootPartition s) /\
  StateLib.nextEntryIsPP sourcePartDesc idxPageDir sourcePageDir s
}}

getParentPartDescCont sourcePartDesc sourcePageDir targetInterrupt sourceContextSaveIndex
                      nbL flagsOnYield flagsOnWake sourceInterruptedContext
{{ (* Postconditions *)
  fun _ s  =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s
}}.
Proof.
unfold getParentPartDescCont.

(* rootPartition := MALInternal.getPageRootPartition *)
eapply WP.bindRev.
eapply Invariants.getPageRootPartition.
intro rootPartition.
cbn.

(* sourcePartitionIsRoot := MALInternal.Page.eqb rootPartition sourcePartDesc *)
eapply WP.bindRev.
apply Invariants.Page.eqb.
intro sourcePartitionIsRoot.
cbn.

(* if sourcePartitionIsRoot
   then Hardware.ret IAL.FAIL_ROOT_CALLER *)
case_eq sourcePartitionIsRoot.
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_sourcePartitionIsRoot.
subst.

(* targetPartDesc := Internal.getParent sourcePartDesc *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.getParent.
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
split; intuition.

intro targetPartDesc.
cbn.

(* getSourceVidtCont targetPartDesc sourcePageDir targetInterrupt sourceContextSaveIndex nbL
                     flagsOnYield flagsOnWake sourceInterruptedContext *)
eapply WP.weaken.
apply (getSourceVidtCont targetPartDesc sourcePageDir targetInterrupt sourceContextSaveIndex nbL
                        flagsOnYield flagsOnWake sourceInterruptedContext sourcePartDesc).
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split. intuition.
split. intuition.
split. intuition.
split. intuition.
rewrite <- and_assoc.
split.
destruct preconditions as ( _ & _ & _ & H_cons & _ & H_srcPartDesc & _ & H_rootPart & H_sourcePartNotRoot & H_isPP).
unfold consistency in H_cons.
destruct H_cons as (H_partDescEntry & _ & _ & _ & _ & _ & _ & H_parentInPartitionList & _ ).
unfold partitionDescriptorEntry in H_partDescEntry.
unfold parentInPartitionList in H_parentInPartitionList.
pose (H_speParentInPartitionList := H_parentInPartitionList sourcePartDesc H_srcPartDesc targetPartDesc H_isPP).
split. assumption.
assert (idxParentDesc = idxPageDir \/ idxParentDesc = idxShadow1 \/ idxParentDesc = idxShadow2 \/ idxParentDesc = idxShadow3 \/
        idxParentDesc = idxParentDesc \/ idxParentDesc = idxPartDesc) as H_idxRefl by intuition.
pose (H_spePartDescEntry := H_partDescEntry sourcePartDesc H_srcPartDesc idxParentDesc H_idxRefl).
destruct H_spePartDescEntry as ( _ & _ & H_existsTargetPartDesc).
destruct H_existsTargetPartDesc.
destruct H.
unfold StateLib.nextEntryIsPP in H_isPP.
unfold StateLib.nextEntryIsPP in H.
clear H_partDescEntry H_parentInPartitionList H_srcPartDesc H_rootPart H_sourcePartNotRoot H_speParentInPartitionList H_idxRefl.
destruct (StateLib.Index.succ idxParentDesc); try congruence.
destruct (lookup sourcePartDesc i (memory s) pageEq idxEq); try congruence.
destruct v; congruence.
intuition.
Qed.

Definition getChildPartDescCont (sourcePartDesc : page)
				                        (sourcePageDir : page)
				                        (targetPartDescVAddr : vaddr)
				                        (targetInterrupt : index)
				                        (sourceContextSaveIndex : index)
				                        (nbL : level)
				                        (flagsOnYield : interruptMask)
				                        (flagsOnWake : interruptMask)
				                        (sourceInterruptedContext : contextAddr)
                                :
{{ (* Preconditions *)
  fun s =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s /\
  Some nbL = StateLib.getNbLevel /\
  sourcePartDesc = currentPartition s /\
  List.In sourcePartDesc (StateLib.getPartitions pageRootPartition s) /\
  StateLib.nextEntryIsPP sourcePartDesc idxPageDir sourcePageDir s
}}

getChildPartDescCont sourcePartDesc sourcePageDir targetPartDescVAddr targetInterrupt
				             sourceContextSaveIndex nbL flagsOnYield flagsOnWake sourceInterruptedContext

{{ (* Postconditions *)
  fun _ s  =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s
}}.
Proof.
unfold getChildPartDescCont.

(* childLastMMUTable := Internal.getTableAddr sourcePageDir targetPartDescVAddr nbL *)
eapply WP.bindRev.
eapply WP.weaken.
eapply (getTableAddr sourcePageDir targetPartDescVAddr nbL _ sourcePartDesc idxPageDir).
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
destruct preconditions as ( _ & _ & _ & H_cons & H_nbL & _ & H_srcPartDesc & H_srcPageDir).
do 3 (split; trivial).
intuition.
exists sourcePageDir.
split; try assumption.
split;[ | intuition ].
clear H_nbL.

unfold consistency in H_cons.
unfold partitionDescriptorEntry in H_cons.
destruct H_cons as (H_partDescEntry & _).
generalize (H_partDescEntry sourcePartDesc H_srcPartDesc); clear H_partDescEntry; intro H_partDescEntry.
clear H_srcPartDesc.
assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2 \/  idxPageDir  = idxShadow3
  \/  idxPageDir  = idxParentDesc \/  idxPageDir = idxPartDesc) as H_idxMatch by intuition.
generalize (H_partDescEntry idxPageDir H_idxMatch); clear H_partDescEntry; intro H_partDescEntry.
clear H_idxMatch.
destruct H_partDescEntry as ( H_validIdx & _ & H_entry ).
destruct H_entry as (page1 & Hpd & Hnotnull).
unfold StateLib.nextEntryIsPP in *.
destruct (StateLib.Index.succ idxPageDir); try now contradict H_srcPageDir.
destruct (lookup sourcePartDesc i (memory s) pageEq idxEq);
         try now contradict H_srcPageDir.
destruct v ; try now contradict H_srcPageDir.
subst; assumption.

cbn.
intro childLastMMUTable.
(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as (H_initPreconditions & H_addProp).
  assert ( StateLib.getTableAddrRoot' childLastMMUTable idxPageDir sourcePartDesc targetPartDescVAddr s
           /\ childLastMMUTable = pageDefault
        \/ StateLib.getTableAddrRoot childLastMMUTable idxPageDir sourcePartDesc targetPartDescVAddr s
           /\ childLastMMUTable <> pageDefault /\
              (forall idx : index,
                  StateLib.getIndexOfAddr targetPartDescVAddr levelMin = idx ->
                  StateLib.isPE childLastMMUTable idx s)
         ) as H_cleanedPost.
  {
    destruct H_addProp as [ ( H_getTableAddr & H_nullChildLastMMUTable )
                          | ( H_getTableAddr & H_notNullChildLastMMUTable & H_entryType) ].
    + left. split; trivial.
    + right. do 2 (try split; trivial).
      intros idx H_getIndexAddr.
      generalize (H_entryType idx H_getIndexAddr); clear H_entryType; intro H_entryType.
      destruct H_entryType as [ ( _ & Hfalse ) | [ ( _ & Hfalse ) | ( H_PE & _ ) ] ].
      - contradict Hfalse.
        apply InternalLemmas.idxPDidxSh1notEq.
      - contradict Hfalse.
        apply DependentTypeLemmas.idxPDidxSh2notEq.
      - assumption.
  }
  clear H_addProp.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  pattern s in H_newPost.
  eapply H_newPost.
}

(* childLastMMUTableisNull := Internal.comparePageToNull childLastMMUTable *)
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro sourceVidtLastMMUPageisNull. cbn.
case_eq sourceVidtLastMMUPageisNull.
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_childLastMMUTableisNull.
subst.

(* Postcondition simplification *)
eapply WP.weaken.
2: {
  intros s postconditions.
  destruct postconditions as ( (H_initPreconditions & H_postGetTableAddr ) & H_childLastMMUTableisNotNull).
  apply EqNat.beq_nat_false in H_childLastMMUTableisNotNull.
  assert (StateLib.getTableAddrRoot childLastMMUTable idxPageDir sourcePartDesc targetPartDescVAddr s
       /\ childLastMMUTable <> pageDefault
       /\ (forall idx : index,
          StateLib.getIndexOfAddr targetPartDescVAddr levelMin = idx ->
          StateLib.isPE childLastMMUTable idx s)) as H_cleanedPost.
  {
    destruct H_postGetTableAddr as
      [ ( H_getTableAddr & H_nullChildLastMMUTable )
      | ( H_getTableAddr & H_notNullChildLastMMUTable & H_entryType) ].
    + symmetry in H_nullChildLastMMUTable.
      contradict H_childLastMMUTableisNotNull.
      f_equal. assumption.
    + do 2 (try split; trivial).
  }
  clear H_postGetTableAddr H_childLastMMUTableisNotNull.
  assert (H_newPost := conj H_initPreconditions H_cleanedPost).
  repeat rewrite and_assoc in H_newPost.
  pattern s in H_newPost.
  eapply H_newPost.
}

(* idxChildPartDesc := MAL.getIndexOfAddr targetPartDescVAddr fstLevel *)
eapply bindRev.
apply Invariants.getIndexOfAddr.
intro idxChildPartDesc.
cbn.

(* childPartDescIsPresent := MAL.readPresent childLastMMUTable idxChildPartDesc *)
eapply bindRev.
eapply weaken.
apply Invariants.readPresent.
cbn.

intros s preconditions.
try repeat rewrite and_assoc in preconditions.
split.
apply preconditions.
repeat rewrite <- and_assoc in preconditions.
destruct preconditions as (( _ & H_isPE ) & H_getIdxOfAddr ).
apply H_isPE; assumption.

intro childPartDescIsPresent.
cbn.

(* if negb childPartDescIsPresent
   then Hardware.ret IAL.FAIL_INVALID_CHILD *)
case_eq (negb childPartDescIsPresent).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_childPartDescIsPresent.
apply Bool.negb_false_iff in H_childPartDescIsPresent.
subst.

(* validChild := checkChild sourcePartDesc nbL targetPartDescVAddr *)
eapply WP.bindRev.
eapply WP.weaken.
apply checkChild.

intros s preconditions.
repeat rewrite and_assoc in preconditions.
split. apply preconditions.
split; intuition.
intro validChild.
cbn.

(* if negb validChild
   then Hardware.ret IAL.FAIL_INVALID_CHILD *)
case_eq (negb validChild).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_validChild.
apply Bool.negb_false_iff in H_validChild.
subst.

(* targetPartDesc := MAL.readPhyEntry childLastMMUTable idxChildPartDesc *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.readPhyEntry.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split. apply preconditions.

repeat rewrite <- and_assoc in preconditions.
destruct preconditions as (((( _ & H_isPE ) & H_getIdxOfAddr ) & _ ) & _ ).
apply H_isPE. assumption.
intro targetPartDesc.
cbn.

(* getSourceVidtCont targetPartDesc sourcePageDir targetInterrupt sourceContextSaveIndex
                     nbL flagsOnYield flagsOnWake sourceInterruptedContext *)
eapply WP.weaken.
apply (getSourceVidtCont targetPartDesc sourcePageDir targetInterrupt sourceContextSaveIndex
                         nbL flagsOnYield flagsOnWake sourceInterruptedContext sourcePartDesc).
cbn.
intros s preconditions.
repeat rewrite and_assoc in preconditions.
split. intuition.
split. intuition.
split. intuition.
split. intuition.
destruct preconditions as (_ & _ & _ & H_cons & H_nbL & H_curPart & H_srcPartDesc & H_srcPageDir &
                           H_tblAddr & H_MMUTableNotDef & H_isPE & H_getIdxOfAddr & H_present &
                           H_checkChild & H_entry).
split.
apply (childInPartTree targetPartDesc sourcePartDesc sourcePageDir childLastMMUTable s nbL 
                       targetPartDescVAddr idxChildPartDesc); intuition.
split.
2: intuition.
clear H_nbL H_curPart H_srcPartDesc H_srcPageDir H_tblAddr H_MMUTableNotDef H_isPE H_getIdxOfAddr
      H_checkChild.
unfold consistency in H_cons.
destruct H_cons as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H_notPresentIfDefaultIff
                      & _ ).
apply isEntryPageReadPhyEntry1 in H_entry.
apply entryPresentFlagReadPresent in H_present.
assert (H_notDefault := isPresentNotDefaultIffTrue s childLastMMUTable idxChildPartDesc
                        H_notPresentIfDefaultIff H_present).
clear H_notPresentIfDefaultIff H_present.
destruct StateLib.readPhyEntry; congruence.
Qed.

Lemma checkCtxSaveIdxCont (targetPartDescVAddr : vaddr)
				                  (targetInterrupt : index)
				                  (userSourceContextSaveIndex : userValue)
				                  (flagsOnYield : interruptMask)
				                  (flagsOnWake : interruptMask)
				                  (sourceInterruptedContext : contextAddr)
                          :
{{ (* Preconditions *)
  fun s =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s
}}

checkCtxSaveIdxCont targetPartDescVAddr targetInterrupt userSourceContextSaveIndex
				            flagsOnYield flagsOnWake sourceInterruptedContext

{{ (* Postconditions *)
  fun _ s  =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s
}}.
Proof.
unfold checkCtxSaveIdxCont.

(* sourceContextSaveIndexIsValid := IAL.checkIndexPropertyLTB userSourceContextSaveIndex *)
eapply WP.bindRev.
eapply Invariants.checkIndexPropertyLTB.
intro sourceContextSaveIndexIsValid.
simpl.

(* if negb sourceContextSaveIndexIsValid
   then Hardware.ret IAL.FAIL_INVALID_CTX_SAVE_INDEX *)
case_eq (negb sourceContextSaveIndexIsValid).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_validsourceContextSaveIndex.
apply Bool.negb_false_iff in H_validsourceContextSaveIndex.
subst.

(* sourceContextSaveIndex := IAL.userValueToIndex userSourceContextSaveIndex *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.userValueToIndex.
simpl.
intros s preconditions.
split.
repeat rewrite and_assoc in preconditions. apply preconditions.
destruct preconditions as (_ & H_idxLT).
apply NPeano.Nat.ltb_lt. assumption.
intro sourceContextSaveIndex.
simpl.

(* sourcePartDesc := MAL.getCurPartition *)
eapply WP.bindRev.
apply Invariants.getCurPartition.
intro sourcePartDesc.
simpl.

(* sourcePageDir := Internal.getPd sourcePartDesc *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.getPd.
intros s preconditions.
simpl.
split. repeat rewrite and_assoc in preconditions.
apply preconditions.
destruct preconditions as (preconditions & H_sourcePartDescIsCurrent).
rewrite H_sourcePartDescIsCurrent.
unfold consistency in preconditions.
unfold currentPartitionInPartitionsList in preconditions.
intuition.
simpl.

intro sourcePageDir.

(* nbL := MAL.getNbLevel *)
eapply WP.bindRev.
apply Invariants.getNbLevel.
simpl.

intro nbL.
simpl.

(* targetPartDescVAddrIsDefault := Internal.compareVAddrToNull targetPartDescVAddr *)
eapply WP.bindRev.
apply Invariants.compareVAddrToNull.

intro targetPartDescVAddrIsDefault.
simpl.

(* if targetPartDescVAddrIsDefault *)
case_eq targetPartDescVAddrIsDefault.

(* getParentPartDescCont sourcePartDesc sourcePageDir targetInterrupt sourceContextSaveIndex
                         nbL flagsOnYield flagsOnWake sourceInterruptedContext *)
{
  intros.
  eapply WP.weaken.
  apply (getParentPartDescCont sourcePartDesc sourcePageDir targetInterrupt sourceContextSaveIndex
         nbL flagsOnYield flagsOnWake sourceInterruptedContext).
  intros s preconditions.
  repeat rewrite and_assoc in preconditions.
  destruct preconditions as (H_iso & H_kern & H_vert & H_cons & _ & _ & H_srcIsCurrent
                           & H_isPP & H_nbL & _ ).
  intuition.
  unfold consistency in H_cons.
  unfold currentPartitionInPartitionsList in H_cons.
  rewrite H_srcIsCurrent.
  intuition.
}
{
  intros.
  eapply WP.weaken.
  apply (getChildPartDescCont sourcePartDesc sourcePageDir targetPartDescVAddr targetInterrupt
                              sourceContextSaveIndex nbL flagsOnYield flagsOnWake
                              sourceInterruptedContext).
  intros s preconditions.
  repeat rewrite and_assoc in preconditions.
  destruct preconditions as (H_iso & H_kern & H_vert & H_cons & _ & _ & H_srcIsCurrent
                           & H_isPP & H_nbL & _ ).
  intuition.
  unfold consistency in H_cons.
  unfold currentPartitionInPartitionsList in H_cons.
  rewrite H_srcIsCurrent.
  intuition.
}
Qed.

Lemma yield (targetPartDescVAddr : vaddr)
				    (userTargetInterrupt : userValue)
				    (userSourceContextSaveIndex : userValue)
				    (flagsOnYield : interruptMask)
				    (flagsOnWake : interruptMask)
				    (sourceInterruptedContext : contextAddr)
            :
{{ (* Preconditions *)
  fun s =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s
}}

checkIntLevelCont targetPartDescVAddr userTargetInterrupt userSourceContextSaveIndex
                  flagsOnYield flagsOnWake sourceInterruptedContext

{{ (* Postconditions *)
  fun _ s  =>
  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s
}}.
Proof.
unfold checkIntLevelCont.

(* userTargetInterruptIsValidIndex := IAL.checkIndexPropertyLTB userTargetInterrupt *)
eapply WP.bindRev.
eapply Invariants.checkIndexPropertyLTB.
intro userTargetInterruptIsValidIndex.
simpl.

(* if negb userTargetInterruptIsValidIndex
   then Hardware.ret IAL.FAIL_INVALID_CTX_SAVE_INDEX *)
case_eq (negb userTargetInterruptIsValidIndex).
{ intros.
  eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
intros H_validUserTargetInterrupt.
apply Bool.negb_false_iff in H_validUserTargetInterrupt.
subst.

(* targetInterrupt := IAL.userValueToIndex userTargetInterrupt *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.userValueToIndex.
simpl.
intros s preconditions.
split.
repeat rewrite and_assoc in preconditions. apply preconditions.
destruct preconditions as (_ & H_idxLT).
apply NPeano.Nat.ltb_lt. assumption.
intro targetInterrupt.
simpl.

(* checkCtxSaveIdxCont targetPartDescVAddr targetInterrupt userSourceContextSaveIndex flagsOnYield
                       flagsOnWake sourceInterruptedContext *)
eapply WP.weaken.
apply (checkCtxSaveIdxCont targetPartDescVAddr targetInterrupt userSourceContextSaveIndex
                           flagsOnYield flagsOnWake sourceInterruptedContext).
simpl.
intros s preconditions.
intuition.
Qed.

