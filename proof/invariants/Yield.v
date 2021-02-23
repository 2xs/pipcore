(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2017)                 *)
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
    This file contains the invariant of [yield]. 
    We prove that this PIP service preserves the isolation property *)

Require Import Model.ADT Model.Hardware Model.Lib Model.MALInternal Model.MAL Core.Services Activate CheckChild Consistency DependentTypeLemmas Model.IAL InternalLemmas Invariants Isolation PropagatedProperties StateLib WeakestPreconditions GetTableAddr.
Import Omega List Bool Nat.

Lemma switchContext
      (userTargetInterrupt userCallerContextSaveIndex : userValue)
      (targetInterrupt callerContextSaveIndex idxVidtInLastMMUPage : index)
      (callerPartDesc callerPageDir callerVidtLastMMUPage callerVidt : page)
      (calleePartDesc calleePageDir calleeVidtLastMMUPage calleeVidt : page)
      (calleeContextVAddr calleeContextEndVAddr (* callerContextSaveVAddr *) : vaddr)
      (calleeContextLastMMUPage calleeContextEndLastMMUPage : page)
      (idxCalleeContextPageInLastMMUPage idxCalleeContextEndPageInLastMMUPage : index)
      ((* flagsOnWake *) flagsOnYield : interruptMask)
      (nbL             : level)
      (* (callerInterruptedContext : contextAddr) *)
:
{{fun s : state =>
  yieldPreWritingProperties s
  userTargetInterrupt userCallerContextSaveIndex
  targetInterrupt callerContextSaveIndex idxVidtInLastMMUPage
  callerPartDesc callerPageDir callerVidtLastMMUPage callerVidt
  calleePartDesc calleePageDir calleeVidtLastMMUPage calleeVidt
  calleeContextVAddr calleeContextEndVAddr
  calleeContextLastMMUPage calleeContextEndLastMMUPage
  idxCalleeContextPageInLastMMUPage idxCalleeContextEndPageInLastMMUPage
  nbL
}}
switchContext callerVidt
              flagsOnYield
              calleePartDesc
              calleePageDir
{{fun (_ : yield_checks) (s' : state) =>
   partitionsIsolation s' /\
   kernelDataIsolation s' /\
   verticalSharing s' /\
   consistency s' }}.

Proof.
unfold switchContext.

(** setInterruptMask *)
eapply bindRev.
eapply weaken.
apply Invariants.setInterruptMask.
cbn.
intros.
apply H.
cbn.
intro useless; destruct useless.

(** updateCurPartAndActivate *)
eapply bindRev.
unfold yieldPreWritingProperties.
eapply weaken.
unfold IAL.updateCurPartAndActivate.
apply (Activate.activatePartition calleePartDesc).
cbn.
intros.
intuition.
cbn.
intro useless; destruct useless.
eapply weaken.
eapply ret.
cbn.
intros.
intuition.
Qed.

Lemma saveCallerContext
      (userTargetInterrupt userCallerContextSaveIndex : userValue)
      (targetInterrupt callerContextSaveIndex idxVidtInLastMMUPage : index)
      (callerPartDesc callerPageDir callerVidtLastMMUPage callerVidt : page)
      (calleePartDesc calleePageDir calleeVidtLastMMUPage calleeVidt : page)
      (calleeContextVAddr calleeContextEndVAddr callerContextSaveVAddr : vaddr)
      (calleeContextLastMMUPage calleeContextEndLastMMUPage : page)
      (idxCalleeContextPageInLastMMUPage idxCalleeContextEndPageInLastMMUPage : index)
      (flagsOnWake flagsOnYield : interruptMask)
      (nbL             : level)
      (callerInterruptedContext : contextAddr)
:
{{fun s : state =>
  yieldPreWritingProperties s
  userTargetInterrupt userCallerContextSaveIndex
  targetInterrupt callerContextSaveIndex idxVidtInLastMMUPage
  callerPartDesc callerPageDir callerVidtLastMMUPage callerVidt
  calleePartDesc calleePageDir calleeVidtLastMMUPage calleeVidt
  calleeContextVAddr calleeContextEndVAddr
  calleeContextLastMMUPage calleeContextEndLastMMUPage
  idxCalleeContextPageInLastMMUPage idxCalleeContextEndPageInLastMMUPage
  nbL
}}
saveCallerContext callerPageDir
                  callerVidt
                  callerContextSaveIndex
                  callerContextSaveVAddr
                  flagsOnYield
                  flagsOnWake
                  callerInterruptedContext
                  calleePartDesc
                  calleePageDir
                  nbL
                  fstLevel
{{fun (_ : yield_checks) (s' : state) =>
   partitionsIsolation s' /\
   kernelDataIsolation s' /\
   verticalSharing s' /\
   consistency s' }}.
Proof.
unfold saveCallerContext.

(** getTableAddr - ctxLastMMUPage *)
eapply bindRev.
eapply weaken.
apply getTableAddr.
cbn.
intros.
split.
apply H.
unfold yieldPreWritingProperties in H.
split.
intuition.
instantiate (1:= PDidx).
instantiate (1:= callerPartDesc).
unfold consistency in *.
unfold currentPartitionInPartitionsList in *.
split.
intuition.
subst.
assumption.
split.
left. trivial.
exists callerPageDir.
split.
intuition.
split.
apply pdPartNotNull with callerPartDesc s; intuition; subst; assumption.
left.
split.
trivial.
intuition.
cbn.
intro ctxLastMMUPage.

(** comparePageToNull - ctxLastMMUPageisNull *)
eapply bindRev.
eapply Invariants.comparePageToNull.
intro ctxLastMMUPageisNull.
cbn.

(** case_eq ctxLastMMUPageisNull *)
case_eq ctxLastMMUPageisNull.
intros.
eapply weaken.
eapply ret.
intros.
cbn.
unfold yieldPreWritingProperties in *.
intuition.
intros.
subst.

(** hypotheses cleanup *)
eapply weaken.
2: {
intros.
destruct H.
destruct H.
apply beq_nat_false in H0.
(** simplify the new precondition **)
assert (getTableAddrRoot ctxLastMMUPage PDidx callerPartDesc callerContextSaveVAddr s /\
     (forall idx : index,
      StateLib.getIndexOfAddr callerContextSaveVAddr fstLevel = idx ->
      isPE ctxLastMMUPage idx s)).
{ destruct H1 as [(Htar1 & Hqzdzqd) |(Hi & Hi1 & H1)].
  + contradict H0. symmetry. apply pageEqNatEqEquiv. trivial.
  + split.
    - apply Hi.
    - intros idx Hidx.
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(_&Hfalse) | (Hpe &Htrue) ]].
      * contradict Hfalse.
        apply idxPDidxSh1notEq.
      * contradict Hfalse.
        apply idxPDidxSh2notEq.
      * assumption.
}
rewrite pageEqNatEqEquiv in H0.
assert (HP := conj (conj H H0) H2).
apply HP.
}

(** getIndexOfAddr - idxCtxInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.getIndexOfAddr.
cbn.
intros.
apply H.

cbn.
intro idxCtxInLastMMUPage.

(** readPresent - ctxPageIsPresent *)
eapply bindRev.
eapply weaken.
apply Invariants.readPresent.
intros.
cbn.
split.
apply H.
intuition.
cbn.
intro ctxPageIsPresent.

(** case_eq negb ctxPageIsPresent *)
case_eq (negb ctxPageIsPresent).
intros.
eapply weaken.
eapply ret.
intros.
cbn.
unfold yieldPreWritingProperties in *.
intuition.

intros.
apply negb_false_iff in H.
subst.

(** readAccessible - ctxPageIsAccessible *)
eapply bindRev.
eapply weaken.
apply Invariants.readAccessible.
cbn.
intros.
split.
apply H.
intuition.
cbn.
intro ctxPageIsAccessible.

(** case_eq negb ctxPageIsAccessible *)
case_eq (negb ctxPageIsAccessible).
intro.
eapply weaken.
eapply ret.
cbn.
intros.
unfold yieldPreWritingProperties in H0.
intuition.

intro.
apply negb_false_iff in H.
subst.

(** getNthVAddrFrom - callerContextEndSaveVAddr *)
eapply bindRev.
eapply weaken.
eapply Invariants.getNthVAddrFrom.
cbn.
intros.
apply H.
cbn.
intro callerContextEndSaveVAddr.

(** firstVAddrGreaterThanSecond - endAddrOverflow *)
eapply bindRev.
eapply weaken.
apply Invariants.firstVAddrGreaterThanSecond.
cbn.
intros.
apply H.
cbn.
intro endAddrOverflow.

(** case_eq endAddrOverflow *)
case_eq endAddrOverflow.
intro.
eapply weaken.
eapply ret.
cbn.
intros.
unfold yieldPreWritingProperties in H0.
intuition.
intro.
subst.

(** getTableAddr - callerCtxEndLastMMUPage *)
eapply bindRev.
eapply weaken.
apply getTableAddr.
cbn.
intros.
split.
apply H.
unfold yieldPreWritingProperties in H.
split.
intuition.
instantiate (1:= PDidx).
instantiate (1:= callerPartDesc).
unfold consistency in *.
unfold currentPartitionInPartitionsList in *.
split.
intuition.
subst.
assumption.
split.
left. trivial.
exists callerPageDir.
split.
intuition.
split.
apply pdPartNotNull with callerPartDesc s; intuition; subst; assumption.
left.
split.
trivial.
intuition.
cbn.
intro ctxEndLastMMUPage.

(** comparePageToNull - ctxEndLastMMUPageisNull *)
eapply bindRev.
eapply Invariants.comparePageToNull.
intro ctxEndLastMMUPageisNull.
cbn.

(** case_eq ctxEndLastMMUPageisNull *)
case_eq ctxEndLastMMUPageisNull.
intros.
eapply weaken.
eapply ret.
intros.
cbn.
unfold yieldPreWritingProperties in *.
intuition.
intros.
subst.

(** hypotheses cleanup *)
eapply weaken.
2: {
intros.
destruct H.
destruct H.
apply beq_nat_false in H0.
(** simplify the new precondition **)
assert (getTableAddrRoot ctxEndLastMMUPage PDidx callerPartDesc callerContextEndSaveVAddr s /\
     (forall idx : index,
      StateLib.getIndexOfAddr callerContextEndSaveVAddr fstLevel = idx ->
      isPE ctxEndLastMMUPage idx s)).
{ destruct H1 as [(Htar1 & Hqzdzqd) |(Hi & Hi1 & H1)].
  + contradict H0. symmetry. apply pageEqNatEqEquiv. trivial.
  + split.
    - apply Hi.
    - intros idx Hidx.
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(_&Hfalse) | (Hpe &Htrue) ]].
      * contradict Hfalse.
        apply idxPDidxSh1notEq.
      * contradict Hfalse.
        apply idxPDidxSh2notEq.
      * assumption.
}
rewrite pageEqNatEqEquiv in H0.
assert (HP := conj (conj H H0) H2).
apply HP.
}

(** getIndexOfAddr - idxCtxEndInLastMMUPage *)
eapply bindRev.
eapply weaken.
apply Invariants.getIndexOfAddr.
cbn.
intros.
apply H.

cbn.
intro idxCtxEndInLastMMUPage.

(** readPresent - ctxPageIsPresent *)
eapply bindRev.
eapply weaken.
apply Invariants.readPresent.
intros.
cbn.
split.
apply H.
intuition.
cbn.
intro ctxEndPageIsPresent.

(** case_eq negb ctxPageIsPresent *)
case_eq (negb ctxEndPageIsPresent).
intros.
eapply weaken.
eapply ret.
intros.
cbn.
unfold yieldPreWritingProperties in *.
intuition.

intros.
apply negb_false_iff in H.
subst.

(** readAccessible - ctxPageIsAccessible *)
eapply bindRev.
eapply weaken.
apply Invariants.readAccessible.
cbn.
intros.
split.
apply H.
intuition.
cbn.
intro ctxPageIsAccessible.

(** case_eq negb ctxPageIsAccessible *)
case_eq (negb ctxPageIsAccessible).
intro.
eapply weaken.
eapply ret.
cbn.
intros.
unfold yieldPreWritingProperties in H0.
intuition.

intro.
apply negb_false_iff in H.
subst.

(** writeContext *)
eapply bindRev.
eapply weaken.
apply Invariants.writeContext.
cbn.
intros.
apply H.
cbn.
intro useless; destruct useless.

eapply weaken.
apply switchContext with (userTargetInterrupt := userTargetInterrupt)
                             (userCallerContextSaveIndex := userCallerContextSaveIndex)
                             (targetInterrupt := targetInterrupt)
                             (callerContextSaveIndex := callerContextSaveIndex)
                             (idxVidtInLastMMUPage := idxVidtInLastMMUPage)
                             (callerPartDesc := callerPartDesc)
                             (callerPageDir := callerPageDir)
                             (callerVidtLastMMUPage := callerVidtLastMMUPage)
                             (callerVidt := callerVidt)
                             (calleePartDesc := calleePartDesc)
                             (calleePageDir := calleePageDir)
                             (calleeVidtLastMMUPage := calleeVidtLastMMUPage)
                             (calleeVidt := calleeVidt)
                             (calleeContextVAddr := calleeContextVAddr)
                             (calleeContextEndVAddr := calleeContextEndVAddr)
                             (* (callerContextSaveVAddr := callerContextSaveVAddr) *)
                             (calleeContextLastMMUPage := calleeContextLastMMUPage)
                             (calleeContextEndLastMMUPage := calleeContextEndLastMMUPage)
                             (idxCalleeContextPageInLastMMUPage := idxCalleeContextPageInLastMMUPage)
                             (idxCalleeContextEndPageInLastMMUPage := idxCalleeContextEndPageInLastMMUPage)
                             (* (flagsOnWake := flagsOnWake) *)
                             (flagsOnYield := flagsOnYield)
                             (nbL := nbL)
                             (* (callerInterruptedContext := callerInterruptedContext) *).
cbn.
intros.
intuition.
Qed.

Lemma calleeContextChecks (userTargetInterrupt userCallerContextSaveIndex : userValue)
                          (targetInterrupt callerContextSaveIndex idxVidtInLastMMUPage : index)
                          (callerPartDesc callerPageDir callerVidtLastMMUPage callerVidt calleePartDesc : page)
                          (flagsOnWake flagsOnYield : interruptMask)
                          (nbL             : level)
                          (callerInterruptedContext : contextAddr) :
{{ fun s : state =>
   postConditionYieldBlock1 s userTargetInterrupt userCallerContextSaveIndex
                            targetInterrupt callerContextSaveIndex idxVidtInLastMMUPage
                            callerPartDesc callerPageDir callerVidtLastMMUPage callerVidt
                            nbL /\
   In calleePartDesc (getPartitions multiplexer s) /\
   calleePartDesc <> defaultPage }}

checkCalleeContext calleePartDesc callerPageDir callerVidt nbL idxVidtInLastMMUPage
                   targetInterrupt callerContextSaveIndex callerInterruptedContext
                   flagsOnYield flagsOnWake

{{ fun (_ : yield_checks) (s' : state) =>
   partitionsIsolation s' /\
   kernelDataIsolation s' /\
   verticalSharing s' /\
   consistency s' }}.
Proof.
unfold checkCalleeContext.
(** getPd - calleePageDir *)
eapply bindRev.
eapply weaken.
eapply Invariants.getPd.
simpl.
intros.
split.
apply H.
split.
unfold postConditionYieldBlock1 in H.
intuition.
unfold consistency in *.
intuition.
intuition.
simpl.
intro calleePageDir.
(** getTableAddr - calleeVidtLastMMUPage *)
eapply bindRev.
eapply weaken.
apply getTableAddr with (currentPart := calleePartDesc) (idxroot := PDidx).
simpl.
intros.
split.
apply H.
split.
unfold postConditionYieldBlock1 in *.
intuition.
split.
intuition.
split.
left. trivial.
exists calleePageDir.
split.
intuition.
split.
apply pdPartNotNull with calleePartDesc s;
intuition.
unfold postConditionYieldBlock1 in *; unfold consistency in *; intuition.
left.
split.
trivial.
unfold postConditionYieldBlock1 in *.
intuition.
cbn.
intro calleeVidtLastMMUPage.

(** comparePageToNull - calleeVidtLastMMUPageisNull *)
eapply bindRev.
eapply Invariants.comparePageToNull.
intro calleeVidtLastMMUPageisNull.
simpl.

(** case_eq calleeVidtLastMMUPageisNull *)
case_eq calleeVidtLastMMUPageisNull.
intro Htrue.
eapply weaken.
eapply ret.
subst.
intros.
simpl.
unfold postConditionYieldBlock1 in H.
intuition.
intro HnotNull.
subst.

(** hypotheses cleanup *)
eapply weaken.
2: {
intros.
destruct H.
destruct H.
apply beq_nat_false in H0.
(** simplify the new precondition **)
assert (getTableAddrRoot calleeVidtLastMMUPage PDidx calleePartDesc vidtVAddr s /\
     (forall idx : index,
      StateLib.getIndexOfAddr vidtVAddr fstLevel = idx ->
      isPE calleeVidtLastMMUPage idx s)).
{ destruct H1 as [(Htar1 & Hqzdzqd) |(Hi & Hi1 & H1)].
  + contradict H0. symmetry. apply pageEqNatEqEquiv. trivial.
  + split.
    - apply Hi.
    - intros idx Hidx.
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(_&Hfalse) | (Hpe &Htrue) ]].
      * contradict Hfalse.
        apply idxPDidxSh1notEq.
      * contradict Hfalse.
        apply idxPDidxSh2notEq.
      * assumption.
}
rewrite pageEqNatEqEquiv in H0.
assert (HP := conj (conj H H0) H2).
apply HP.
}

(** readPresent - calleeVidtIsPresent *)
eapply bindRev.
eapply weaken.
eapply Invariants.readPresent.
simpl.
intros.
split.
apply H.
unfold postConditionYieldBlock1 in H.
destruct H.
destruct H0.
apply H1.
intuition.
simpl.
intro calleeVidtIsPresent.

(** case_eq calleeVidtIsPresent *)
case_eq (negb calleeVidtIsPresent).
intro HnotPresent.
subst.
eapply weaken.
eapply ret.
simpl.
intros.
unfold postConditionYieldBlock1 in H.
intuition.
intro vidtPresent.
apply negb_false_iff in vidtPresent.
subst.

(** readAccessible - calleeVidtIsAccessible *)
eapply bindRev.
eapply weaken.
eapply Invariants.readAccessible.
simpl.
intros.
split.
apply H.
destruct H.
destruct H.
destruct H1.
apply H2.
unfold postConditionYieldBlock1 in H.
intuition.
simpl.
intro calleeVidtIsAccessible.

(** case_eq negb calleeVidtIsAccessible *)
case_eq (negb calleeVidtIsAccessible).
intro HnotAccessible.
eapply weaken.
eapply ret.
simpl.
unfold postConditionYieldBlock1.
intros.
intuition.
intro HvidtAccessible.
apply negb_false_iff in HvidtAccessible.
subst.

(** readPhyEntry - calleeVidt *)
eapply bindRev.
eapply weaken.
eapply Invariants.readPhyEntry.
simpl.
intros.
split.
apply H.
destruct H.
destruct H.
destruct H.
apply H2.
unfold postConditionYieldBlock1 in H.
intuition.
intro calleeVidt.
simpl.

(** calleeInterruptMask := IAL.readInterruptMask *)
eapply bindRev.
eapply weaken.
eapply Invariants.readInterruptMask.
simpl.
intros.
apply H.
simpl.
intro calleeInterruptMask.

(** calleeMaskedInterrupt := IAL.isInterruptMasked *)
eapply bindRev.
eapply weaken.
apply Invariants.isInterruptMasked.
simpl.
intros.
apply H.
simpl.
intro calleeMaskedInterrupt.

(** case_eq calleeMaskedInterrupt *)
case_eq calleeMaskedInterrupt.
intros.
eapply weaken.
eapply ret.
intros.
simpl.
unfold postConditionYieldBlock1 in H0.
intuition.
intros.
subst.

(** readUserlandVAddr - calleeContextVAddr *)
eapply bindRev.
eapply weaken.
eapply Invariants.readUserlandVAddr.
simpl.
intros.
apply H.
simpl.
intro calleeContextVAddr.

(** getTableAddr - calleeContextLastMMUPage *)
eapply bindRev.
eapply weaken.
apply getTableAddr with (currentPart := calleePartDesc) (idxroot := PDidx).
simpl.
intros s H.
split. 
apply H.
unfold postConditionYieldBlock1 in H.
split.
intuition. subst.
unfold currentPartitionInPartitionsList in *.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some nbL = StateLib.getNbLevel) by intuition.
assert (HnEIPP : nextEntryIsPP calleePartDesc PDidx calleePageDir s) by intuition.
assert (HpartDesc : In calleePartDesc (getPartitions multiplexer s)) by intuition.
split. assumption. 
split. intuition.
exists calleePageDir.
split. assumption.

unfold consistency in *.
destruct Hcons as (Hpd & _).
split.
apply pdPartNotNull with calleePartDesc s ; assumption.
left. split; [trivial | assumption].
intro calleeContextLastMMUPage. cbn.

(** comparePageToNull - calleeContextLastMMUPageisNull *)
eapply bindRev.
eapply weaken.
eapply Invariants.comparePageToNull.
simpl.
intros.
apply H.
intro calleeContextLastMMUPageisNull.
simpl.

(** case_eq calleeContextLastMMUPageisNull *)
case_eq calleeContextLastMMUPageisNull.
intros.
subst.
eapply weaken.
eapply ret.
simpl.
intros.
unfold postConditionYieldBlock1 in H.
intuition.

intro.
subst.

(** simplify the new precondition **)
eapply WP.weaken.
intros.
2: {
intros.
destruct H as ((H0 & H1) & H2).
assert (getTableAddrRoot calleeContextLastMMUPage PDidx calleePartDesc
        calleeContextVAddr s /\
        calleeContextLastMMUPage <> defaultPage /\
        (forall idx : index,
          StateLib.getIndexOfAddr calleeContextVAddr fstLevel = idx ->
          isPE calleeContextLastMMUPage idx s)).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + contradict H2.
    destruct H1.
    apply not_false_iff_true.
    apply Nat.eqb_eq.
    symmetry.
    apply pageEqNatEqEquiv.
    assumption.
  + split. assumption.
    split. assumption.
    intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(_& Hfalse) | [(_&Hfalse) | (Hpe &Htrue) ]].
    - contradict Hfalse.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - assumption.
}
assert (HP := conj H0 H).
pattern s in HP.
eapply HP.
}

(** getIndexOfAddr - idxCalleeContextPageInLastMMUPage *)
eapply bindRev.
eapply weaken.
eapply Invariants.getIndexOfAddr.
simpl.
intros.
apply H.
intro idxCalleeContextPageInLastMMUPage.
simpl.

(** readPresent - calleeContextPageIsPresent *)
eapply bindRev.
eapply weaken.
eapply Invariants.readPresent.
simpl.
intros.
split. apply H.
destruct H as ((Hgen & H0) & Husef).
destruct H0 as (_ & _ & Husef2).
apply Husef2. assumption.

intro calleeContextPageIsPresent.
simpl.

(** case_eq negb calleeContextPageIsPresent *)
case_eq (negb calleeContextPageIsPresent).
intro.
rewrite negb_true_iff in H.
eapply weaken.
eapply ret.
intros.
simpl.
unfold postConditionYieldBlock1 in H0.
intuition.
intros.
rewrite negb_false_iff in H.
subst.

(** readAccessible - calleeContextPageIsAccessible *)
eapply bindRev.
eapply weaken.
eapply Invariants.readAccessible.
simpl.
intros.
split.
apply H.

destruct H as (((Hgen & (_ & (_ & H))) & H1) & _).
apply H.
assumption.
simpl.
intro calleeContextPageIsAccessible.

(** case_eq negb calleeContextPageIsAccessible *)
case_eq (negb calleeContextPageIsAccessible).
intro.
rewrite negb_true_iff in H.
eapply weaken.
eapply ret.
intros.
simpl.
unfold postConditionYieldBlock1 in H0.
intuition.
intros.
rewrite negb_false_iff in H.
subst.

(** getNthVAddrFrom - calleeContextEndVaddr *)
eapply bindRev.
eapply weaken.
apply Invariants.getNthVAddrFrom.
simpl.
intros.
apply H.
simpl.
intro calleeContextEndVAddr.

(** firstVAddrGreaterThanSecond - calleeContextEndVAddrOverflow *)
eapply bindRev.
eapply weaken.
eapply Invariants.firstVAddrGreaterThanSecond.
cbn.
intros.
apply H.
cbn.
intro calleeContextEndVAddrOverflow.

(** case_eq calleeContextEndVAddrOverflow *)
case_eq calleeContextEndVAddrOverflow.
intros.
eapply weaken.
eapply ret.
cbn.
intros.
unfold postConditionYieldBlock1 in H0.
intuition.
intros.
subst.


(** getTableAddr - calleeContextEndLastMMUPage *)
eapply bindRev.
eapply weaken.
apply getTableAddr.
cbn.
intros s H.
split. 
apply H.
unfold postConditionYieldBlock1 in H.
instantiate (1:= PDidx).
instantiate (1:= calleePartDesc).
intuition. subst.
unfold  currentPartitionInPartitionsList in *. 
intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some nbL = StateLib.getNbLevel) by intuition.
assert (HnEIPP : nextEntryIsPP calleePartDesc PDidx calleePageDir s) by intuition.
exists calleePageDir.
split. intuition.

split.
unfold consistency in *;
apply pdPartNotNull with calleePartDesc s;
intuition.
left. split; trivial.
cbn.
intro calleeContextEndLastMMUPage.

(** comparePageToNull - calleeContextEndLastMMUPageisNull *)
eapply bindRev.
eapply weaken.
eapply Invariants.comparePageToNull.
simpl.
intros.
apply H.
intro calleeContextEndLastMMUPageisNull.
simpl.

(** case_eq calleeContextEndLastMMUPageisNull *)
case_eq calleeContextEndLastMMUPageisNull.
intros.
eapply weaken.
eapply ret.
cbn.
intros.
unfold postConditionYieldBlock1 in H0.
intuition.

intros.
subst.

(** simplify the new precondition **)
eapply WP.weaken.
intros.
2: {
intros.
destruct H as ((H0 & H1) & H2).
assert (getTableAddrRoot calleeContextEndLastMMUPage PDidx calleePartDesc
        calleeContextEndVAddr s /\
        calleeContextEndLastMMUPage <> defaultPage /\
        (forall idx : index,
          StateLib.getIndexOfAddr calleeContextEndVAddr fstLevel = idx ->
          isPE calleeContextEndLastMMUPage idx s)).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + contradict H2.
    destruct H1.
    apply not_false_iff_true.
    apply Nat.eqb_eq.
    symmetry.
    apply pageEqNatEqEquiv.
    assumption.
  + split. assumption.
    split. assumption.
    intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(_& Hfalse) | [(_&Hfalse) | (Hpe &Htrue) ]].
    - contradict Hfalse.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - assumption.
}
assert (HP := conj H0 H).
pattern s in HP.
eapply HP.
}

(** getIndexOfAddr - idxCalleeContextEndPageInLastMMUPage *)
eapply bindRev.
eapply weaken.
eapply Invariants.getIndexOfAddr.
simpl.
intros.
apply H.
intro idxCalleeContextEndPageInLastMMUPage.
cbn.

(** readPresent - calleeContextEndPageIsPresent *)
eapply bindRev.
eapply weaken.
eapply Invariants.readPresent.
simpl.
intros.
split. apply H.
destruct H as ((Hgen & H0) & H).
destruct H0 as (_ & _ & H2).
apply H2. assumption.

intro calleeContextEndPageIsPresent.
cbn.

(** case_eq negb calleeContextPageIsPresent *)
case_eq (negb calleeContextEndPageIsPresent).
intro.
rewrite negb_true_iff in H.
eapply weaken.
eapply ret.
intros.
cbn.
unfold postConditionYieldBlock1 in H0.
intuition.
intros.
rewrite negb_false_iff in H.
subst.

(** readAccessible - calleeContextPageIsAccessible *)
eapply bindRev.
eapply weaken.
eapply Invariants.readAccessible.
simpl.
intros.
split.
apply H.

destruct H as (((Hgen & (_ & (_ & H))) & H1) & _).
apply H.
assumption.
cbn.
intro calleeContextEndPageIsAccessible.

(** case_eq negb calleeContextEndPageIsAccessible *)
case_eq (negb calleeContextEndPageIsAccessible).
intro.
rewrite negb_true_iff in H.
eapply weaken.
eapply ret.
intros.
cbn.
unfold postConditionYieldBlock1 in H0.
intuition.
intros.
rewrite negb_false_iff in H.
subst.

(** readUserlandVAddr - callerContextSaveVAddr *)
eapply bindRev.
eapply weaken.
eapply Invariants.readUserlandVAddr.
cbn.
intros.
apply H.
cbn.
intro callerContextSaveVAddr.

(** compareVAddrToNull - callerWantsToSaveItsContext *)
eapply bindRev.
eapply weaken.
eapply Invariants.compareVAddrToNull.
cbn.
intros.
apply H.
cbn.
intro callerWantsToDropItsContext.

(** case_eq callerWantsToSaveItsContext *)
case_eq (negb callerWantsToDropItsContext).
intros.
unfold postConditionYieldBlock1.
eapply weaken.
apply saveCallerContext with (userTargetInterrupt := userTargetInterrupt)
                             (userCallerContextSaveIndex := userCallerContextSaveIndex)
                             (targetInterrupt := targetInterrupt)
                             (callerContextSaveIndex := callerContextSaveIndex)
                             (idxVidtInLastMMUPage := idxVidtInLastMMUPage)
                             (callerPartDesc := callerPartDesc)
                             (callerPageDir := callerPageDir)
                             (callerVidtLastMMUPage := callerVidtLastMMUPage)
                             (callerVidt := callerVidt)
                             (calleePartDesc := calleePartDesc)
                             (calleePageDir := calleePageDir)
                             (calleeVidtLastMMUPage := calleeVidtLastMMUPage)
                             (calleeVidt := calleeVidt)
                             (calleeContextVAddr := calleeContextVAddr)
                             (calleeContextEndVAddr := calleeContextEndVAddr)
                             (callerContextSaveVAddr := callerContextSaveVAddr)
                             (calleeContextLastMMUPage := calleeContextLastMMUPage)
                             (calleeContextEndLastMMUPage := calleeContextEndLastMMUPage)
                             (idxCalleeContextPageInLastMMUPage := idxCalleeContextPageInLastMMUPage)
                             (idxCalleeContextEndPageInLastMMUPage := idxCalleeContextEndPageInLastMMUPage)
                             (flagsOnWake := flagsOnWake)
                             (flagsOnYield := flagsOnYield)
                             (nbL := nbL)
                             (callerInterruptedContext := callerInterruptedContext).
intros.
unfold yieldPreWritingProperties.
intuition.

intros.
unfold postConditionYieldBlock1.
eapply weaken.
apply switchContext with (userTargetInterrupt := userTargetInterrupt)
                             (userCallerContextSaveIndex := userCallerContextSaveIndex)
                             (targetInterrupt := targetInterrupt)
                             (callerContextSaveIndex := callerContextSaveIndex)
                             (idxVidtInLastMMUPage := idxVidtInLastMMUPage)
                             (callerPartDesc := callerPartDesc)
                             (callerPageDir := callerPageDir)
                             (callerVidtLastMMUPage := callerVidtLastMMUPage)
                             (callerVidt := callerVidt)
                             (calleePartDesc := calleePartDesc)
                             (calleePageDir := calleePageDir)
                             (calleeVidtLastMMUPage := calleeVidtLastMMUPage)
                             (calleeVidt := calleeVidt)
                             (calleeContextVAddr := calleeContextVAddr)
                             (calleeContextEndVAddr := calleeContextEndVAddr)
                             (* (callerContextSaveVAddr := callerContextSaveVAddr) *)
                             (calleeContextLastMMUPage := calleeContextLastMMUPage)
                             (calleeContextEndLastMMUPage := calleeContextEndLastMMUPage)
                             (idxCalleeContextPageInLastMMUPage := idxCalleeContextPageInLastMMUPage)
                             (idxCalleeContextEndPageInLastMMUPage := idxCalleeContextEndPageInLastMMUPage)
                             (* (flagsOnWake := flagsOnWake) *)
                             (flagsOnYield := flagsOnYield)
                             (nbL := nbL)
                             (* (callerInterruptedContext := callerInterruptedContext) *).
unfold yieldPreWritingProperties.
intuition.
Qed.


Lemma childRelatedChecks (userTargetInterrupt userCallerContextSaveIndex : userValue)
                         (targetInterrupt callerContextSaveIndex idxVidtInLastMMUPage : index)
                         (callerPartDesc callerPageDir callerVidtLastMMUPage callerVidt : page)
                         (calleePartDescVAddr: vaddr)
                         (flagsOnWake flagsOnYield : interruptMask)
                         (nbL             : level)
                         (callerInterruptedContext : contextAddr) :
{{ fun s : state =>
   postConditionYieldBlock1 s userTargetInterrupt userCallerContextSaveIndex
                            targetInterrupt callerContextSaveIndex idxVidtInLastMMUPage
                            callerPartDesc callerPageDir callerVidtLastMMUPage callerVidt
                            nbL /\
   beqVAddr defaultVAddr calleePartDescVAddr = false }} 
  childRelatedChecks calleePartDescVAddr callerPartDesc callerPageDir
    callerVidt nbL idxVidtInLastMMUPage targetInterrupt callerContextSaveIndex
    callerInterruptedContext flagsOnWake flagsOnYield {{ fun 
                                                     (_ : yield_checks)
                                                     (s' : state) =>
                                                   partitionsIsolation s' /\
                                                   kernelDataIsolation s' /\
                                                   verticalSharing s' /\
                                                   consistency s' }}.
Proof.

(** getTableAddr - childLastMMUTable *)
eapply bindRev.
eapply weaken.
apply getTableAddr.
simpl.
intros s H.
split.
destruct H.
pattern s in H. 
eexact H.
unfold postConditionYieldBlock1 in H.
instantiate (1:= PDidx).
instantiate (1:= callerPartDesc).
intuition. subst.
unfold consistency in *. 
unfold  currentPartitionInPartitionsList in *. 
intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some nbL = StateLib.getNbLevel) by intuition. 
assert(Hcp : callerPartDesc = currentPartition s) by intuition.
assert (HnEIPP : nextEntryIsPP callerPartDesc PDidx callerPageDir s) by intuition.
exists callerPageDir.
split. intuition.

unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/  PDidx  = sh3idx
\/  PDidx  = PPRidx \/  PDidx = PRidx) as Htmp 
by auto.
generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry).
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
unfold nextEntryIsPP in *.
destruct (StateLib.Index.succ PDidx); try now contradict H0.
destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex) ; try now contradict H0.
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro childLastMMUPage. simpl.
(** simplify the new precondition **)
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' childLastMMUPage PDidx callerPartDesc calleePartDescVAddr s /\ childLastMMUPage = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr calleePartDescVAddr fstLevel = idx ->
isPE childLastMMUPage idx s /\ getTableAddrRoot childLastMMUPage PDidx callerPartDesc calleePartDescVAddr s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial.
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(_& Hfalse) | [(_&Hfalse) | (Hpe &Htrue) ]].
    - contradict Hfalse.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - split; assumption.
}
assert (HP := conj H0 H).
pattern s in HP.
eapply HP.
}

(** comparePageToNull - childLastMMUTableIsNull *)
eapply bindRev.
eapply Invariants.comparePageToNull.
simpl.
intro childLastMMUTableIsNull.
simpl.
case_eq childLastMMUTableIsNull.
{ intros.
  eapply WP.weaken.
  eapply WP.ret .
  simpl. intros.
  unfold postConditionYieldBlock1 in H0.
  intuition. }
intros. 
subst.
(** hypothese cleanup *)
eapply weaken.
2: {
intros.
destruct H as ((Hexec & Hconj) & Hlast).
destruct Hconj as [HFalse | HTrue].
destruct HFalse.
subst.
rewrite Nat.eqb_refl in Hlast.
now contradict Hlast.
destruct HTrue with (StateLib.getIndexOfAddr calleePartDescVAddr fstLevel).
trivial.
apply beq_nat_false in Hlast.
assert (Hdef:= conj (conj (conj Hexec H) H0) Hlast).
pattern s in Hdef.
apply Hdef.
}

(** getIndexOfAddr - idxChildPartDesc *)
eapply bindRev.
eapply Invariants.getIndexOfAddr.
simpl.
intro idxChildPartDesc.

(** readPresent - childPartDescIsPresent *)
eapply bindRev.
eapply weaken.
eapply Invariants.readPresent.
intros.
simpl.
split.
apply H.
intuition.
subst.
trivial.
simpl.
intro childPartDescIsPresent.
(** case_eq childPartDescIsPresent *)
case_eq (negb childPartDescIsPresent).
intros.
eapply weaken.
eapply WP.ret.
intros.
unfold postConditionYieldBlock1 in H0.
intuition.
intros.
rewrite negb_false_iff in H.
subst.

(** checkChild - validChild *)
eapply bindRev.
eapply weaken.
eapply CheckChild.checkChild.
intros.
simpl.
split.
apply H.
unfold postConditionYieldBlock1 in H.
intuition.
simpl.
intro validChild.

(** case_eq - validChild *)
case_eq (negb validChild).
intro.
eapply weaken.
eapply ret.
intros.
simpl.
unfold postConditionYieldBlock1 in H0.
intuition.
intro.
rewrite negb_false_iff in H.
subst.

(** readPhyEntry - calleePartDesc *)
eapply bindRev.
eapply weaken.
eapply Invariants.readPhyEntry.
simpl.
intros.
split.
apply H.
intuition.
subst.
trivial.
simpl.
intro calleePartDesc.

(** hypotheses restructure *)
eapply weaken.
2: {
unfold postConditionYieldBlock1.
intros.
assert (In calleePartDesc (getPartitions multiplexer s)).
intuition.
apply CheckChild.childInPartTree with callerPartDesc callerPageDir
        childLastMMUPage nbL calleePartDescVAddr  idxChildPartDesc; try assumption.
symmetry; assumption.
assert (Hcoer : p defaultPage <> p childLastMMUPage) by trivial.
contradict Hcoer.
rewrite Hcoer.
reflexivity.
assert (calleePartDesc <> defaultPage).
rewrite <- pageNeqNatNeqEquiv.
apply Nat.eqb_neq.
rewrite Nat.eqb_sym.
apply phyPageNotDefault with childLastMMUPage idxChildPartDesc s.
unfold consistency in *.
intuition.
intuition.
intuition.
assert (HpC : postConditionYieldBlock1 s userTargetInterrupt userCallerContextSaveIndex
                            targetInterrupt callerContextSaveIndex idxVidtInLastMMUPage
                            callerPartDesc callerPageDir callerVidtLastMMUPage callerVidt
                            nbL) by (unfold postConditionYieldBlock1; intuition).
assert (HP := conj HpC (conj H0 H1)).
apply HP.
}
apply calleeContextChecks.
Qed.

Lemma parentCallRelatedChecks (userTargetInterrupt userCallerContextSaveIndex : userValue)
                              (targetInterrupt callerContextSaveIndex idxVidtInLastMMUPage : index)
                              (callerPartDesc callerPageDir callerVidtLastMMUPage callerVidt : page)
                              (flagsOnWake flagsOnYield : interruptMask)
                              (nbL             : level)
                              (callerInterruptedContext : contextAddr) :
{{ fun s : state =>
   postConditionYieldBlock1 s userTargetInterrupt userCallerContextSaveIndex
                            targetInterrupt callerContextSaveIndex idxVidtInLastMMUPage
                            callerPartDesc callerPageDir callerVidtLastMMUPage callerVidt
                            nbL}} 
  parentCallRelatedChecks callerPartDesc callerPageDir
    callerVidt nbL idxVidtInLastMMUPage targetInterrupt callerContextSaveIndex
    callerInterruptedContext flagsOnWake flagsOnYield {{ fun 
                                                     (_ : yield_checks)
                                                     (s' : state) =>
                                                   partitionsIsolation s' /\
                                                   kernelDataIsolation s' /\
                                                   verticalSharing s' /\
                                                   consistency s' }}.
Proof.
unfold parentCallRelatedChecks.
(** getMultiplexer - rootPartition *)
eapply bindRev.
eapply weaken.
eapply Invariants.getMultiplexer.
simpl.
intros.
eapply H.
simpl.
intro rootPartition.

(** Page.eqb currentPartitionIsRoot *)
eapply bindRev.
eapply weaken.
eapply Invariants.Page.eqb.
simpl.
intros.
apply H.
simpl.
intro currentPartitionIsRoot.

(** case_eq currentPartitionIsRoot *)
case_eq currentPartitionIsRoot.
intros.
eapply weaken.
eapply ret.
simpl.
intros.
unfold postConditionYieldBlock1 in H0.
intuition.
intro.
subst.

(** getParent - calleePartDesc *)
eapply bindRev.
eapply weaken.
eapply Invariants.getParent.
simpl.
intros.
split.
apply H.
unfold postConditionYieldBlock1 in H.
intuition.
subst.
unfold consistency in H4.
intuition.
simpl.
intro calleePartDesc.

(** Hypotheses cleanup *)
eapply weaken.
2: {
intros.
destruct H as (((HpC & _) & _) & HnEIPP).
assert (HpIPT : In calleePartDesc (getPartitions multiplexer s)).
{ unfold postConditionYieldBlock1 in HpC.
  unfold consistency in HpC.
  assert (HpIPL : parentInPartitionList s) by intuition.
  unfold parentInPartitionList in HpIPL.
  intuition.
  apply HpIPL with (currentPartition s);
  subst;
  unfold currentPartitionInPartitionsList in *; intuition.
}
assert (HpNotDef : calleePartDesc <> defaultPage).
{ apply rootStructNotNull with callerPartDesc s PPRidx.
  - right. right. right. right. left. reflexivity.
  - unfold postConditionYieldBlock1 in HpC.
    unfold consistency in HpC.
    intuition.
  - assumption.
  - unfold postConditionYieldBlock1 in HpC.
    unfold consistency in HpC.
    intuition.
    unfold currentPartitionInPartitionsList in *.
    subst.
    assumption.
}
assert (HP := conj HpC (conj HpIPT HpNotDef)).
apply HP.
}
apply calleeContextChecks.
Qed.

Lemma yield      (calleePartDescVAddr: vaddr)
                 (userTargetInterrupt : userValue)
                 (userCallerContextSaveIndex : userValue)
                 (flagsOnWake : interruptMask)
                 (flagsOnYield : interruptMask)
                 (callerInterruptedContext : contextAddr) :
(* Precondition *)
{{fun (s : state) => partitionsIsolation s /\ 
                     kernelDataIsolation s /\
                     verticalSharing s /\
                     consistency s }}
(* fonction monadique *)
yield calleePartDescVAddr userTargetInterrupt userCallerContextSaveIndex flagsOnWake flagsOnYield callerInterruptedContext
(* Postcondition *)
{{fun _ (s' : state) => partitionsIsolation s' /\
                       kernelDataIsolation s' /\
                       verticalSharing s' /\
                       consistency s' }}.
Proof.
unfold yield.
eapply bindRev.
(** checkIndexPropertyLTB *)
eapply weaken.
apply Invariants.checkIndexPropertyLTB.
simpl.
intros. eapply H. simpl.
intro userTargetInterruptIsValid.
case_eq (negb userTargetInterruptIsValid).
intro. eapply weaken. eapply ret. simpl. intros. intuition.
rewrite Bool.negb_false_iff. intro HuserTargetInterruptIsValid. subst.
eapply bindRev.
(** getIndexFromUserValue *)
eapply WP.weaken.
eapply Invariants.userValueToIndex.
simpl.
intros.
split.
rewrite Nat.ltb_lt in H.
apply H.
rewrite Nat.ltb_lt in H.
destruct H.
trivial.
simpl.
intro targetInterrupt.
eapply bindRev.
(** getCurPartition *)
eapply weaken.
eapply Invariants.getCurPartition.
simpl.
intros.
eapply H.
simpl. intro callerPartDesc.
eapply bindRev.
(** getPd *)
eapply weaken.
eapply Invariants.getPd.
simpl.
intros.
split.
apply H.
  (* First Property *)
  split.
  unfold consistency in *.
  intuition.
  (* Second Property *)
  assert (currentPartitionInPartitionsList s) as HcallerPartDescInPartList.
  unfold consistency in H.
  intuition.
  destruct H. subst.
  apply HcallerPartDescInPartList.
intro callerPageDir.
simpl.
eapply bindRev.
(** getNbLevel *)
eapply Invariants.getNbLevel.
simpl. intro nbL.
(** checkIndexPropertyLTB - callerContextSaveIndexIsValid *)
eapply bindRev.
eapply weaken.
apply Invariants.checkIndexPropertyLTB.
simpl.
intro s. intro preconditions. apply preconditions.
simpl.
intro callerContextSaveIndexIsValid.
case_eq (negb callerContextSaveIndexIsValid);
intro HcallerContextSaveIndexIsValid.
eapply weaken. eapply ret. simpl. intuition.
rewrite Bool.negb_false_iff in HcallerContextSaveIndexIsValid. subst.
(** getIndexFromUserValue - callerContextSaveIndex **)
eapply bindRev.
eapply weaken.
eapply Invariants.userValueToIndex.
simpl.
intros.
rewrite Nat.ltb_lt in H.
split.
apply H.
destruct H.
apply H0.
intro callerContextSaveIndex.
(** vidtVaddr - getVidtVAddr **)
simpl.
eapply bindRev.
eapply weaken.
eapply Invariants.ret.
simpl.
intros.
apply H.
simpl.
intro vidtVAddr.
(** getTableAddr - callerVidtLastMMUPage **)
eapply WP.bindRev.
eapply WP.weaken.
apply getTableAddr.
simpl.
intros s H.
split.
destruct H.
pattern s in H. 
eexact H. subst.
split. 
intuition.
split.
instantiate (1:= callerPartDesc).
intuition. 
subst.
unfold consistency in *. 
unfold  currentPartitionInPartitionsList in *. 
intuition.
instantiate (1:= PDidx).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some nbL = StateLib.getNbLevel) by intuition. 
assert(Hcp : callerPartDesc = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP callerPartDesc PDidx callerPageDir s) by intuition.
exists callerPageDir.
split. intuition.

unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/  PDidx  = sh3idx
\/  PDidx  = PPRidx \/  PDidx = PRidx) as Htmp 
by auto.
generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry).
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
unfold nextEntryIsPP in *. 
destruct (StateLib.Index.succ PDidx); try now contradict H0.
destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex) ; try now contradict H0.
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro callerVidtLastMMUPage. simpl.
(** simplify the new precondition **)
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' callerVidtLastMMUPage PDidx callerPartDesc MALInternal.vidtVAddr s /\ callerVidtLastMMUPage = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr MALInternal.vidtVAddr fstLevel = idx ->
isPE callerVidtLastMMUPage idx s /\ getTableAddrRoot callerVidtLastMMUPage PDidx callerPartDesc MALInternal.vidtVAddr s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(_& Hfalse) | [(_&Hfalse) | (Hpe &Htrue) ]].
    - contradict Hfalse.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - split; assumption.
}
assert (HP := conj H0 H).
pattern s in HP.
eapply HP.
}

(** comparePageToNull - vidtLastMMUPageisNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro vidtLastMMUPageisNull. simpl.
case_eq vidtLastMMUPageisNull.
{ intros.
  eapply WP.weaken.
  eapply WP.ret .
  simpl. intros.
  intuition. }
intros. 
subst.
(** hypotheses cleanup *)
eapply weaken.
2: {
intros.
destruct H as ((Hexec & Hconj) & Hlast).
destruct Hconj as [HFalse | HTrue].
destruct HFalse.
subst.
rewrite Nat.eqb_refl in Hlast.
now contradict Hlast.
destruct HTrue with (StateLib.getIndexOfAddr MALInternal.vidtVAddr fstLevel).
trivial.
apply beq_nat_false in Hlast.
assert (Hdef:= conj (conj (conj Hexec H) H0) Hlast).
pattern s in Hdef.
apply Hdef.
}
(** getIndexOfAddr - idxVidtInLastMMUPage *)
eapply bindRev.
eapply Invariants.getIndexOfAddr.
simpl.
intro idxVidtInLastMMUPage.
(** readPresent - callerVidtIsPresent *)
eapply bindRev.
eapply weaken.
eapply Invariants.readPresent.
intros.
simpl.
split.
apply H.
intuition.
subst.
trivial.
simpl.
intro callerVidtIsPresent.
(** negb callerVidtIsPresent *)
case_eq (negb callerVidtIsPresent).
intro callerVidtIsNotPresent.
eapply weaken.
eapply ret.
simpl.
intros.
intuition.
intro.
apply negb_false_iff in H.
subst.

(** readAccessible - callerVidtIsAccessible *)
eapply bindRev.
eapply weaken.
eapply Invariants.readAccessible.
simpl.
intros.
split.
apply H.
intuition.
subst.
trivial.
simpl.
intro callerVidtIsAccessible.

(** negb callerVidtIsAccessible *)
case_eq (negb callerVidtIsAccessible).
intro.
eapply weaken.
eapply ret.
simpl.
intros.
intuition.
intro.
apply negb_false_iff in H.
subst.

(** readPhyEntry - callerVidt *)
eapply bindRev.
eapply weaken.
eapply Invariants.readPhyEntry.
simpl.
intros.
split.
apply H.
intuition.
subst.
trivial.
simpl.
intro callerVidt.

(** compareVAddrToNull - calleePartDescVAddrIsDefault *)
eapply bindRev.
eapply Invariants.compareVAddrToNull.
simpl.
intro calleePartDescVAddrIsDefault.

(** calleePartDescVAddrIsDefault *)
case_eq calleePartDescVAddrIsDefault;intro;subst;eapply weaken;
[apply parentCallRelatedChecks|trivial|apply childRelatedChecks|trivial];
intros;
simpl;
unfold postConditionYieldBlock1;
instantiate (1:=callerVidtLastMMUPage);
instantiate (1:=userCallerContextSaveIndex);
instantiate (1:=userTargetInterrupt);
intuition;trivial;
subst;
contradiction.
Qed.
