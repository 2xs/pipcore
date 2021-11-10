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

Require Import Lia.

From Pip.Proof Require Import
Consistency GetTableAddr Invariants Isolation updateCurPartition WeakestPreconditions.
(* Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.Isolation
               Pip.Proof.InternalLemmas Pip.Proof.InternalLemmas2 Pip.Proof.StateLib
               Pip.Proof.WeakestPreconditions.
Require Import Invariants GetTableAddr LinkedListConfig PropagatedProperties
               WriteAccessibleFalse WriteAccessibleRecPrepare InitPEntryTable
               UpdateMappedPageContent InitFstShadow InitSndShadow
               UpdateShadow1StructurePrepare InsertEntryIntoLL. *)

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
Admitted.

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
  consistency s (* /\
  List.In sourcePartDesc (StateLib.getPartitions multiplexer s0) /\
   *)
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
eapply (getTableAddr sourcePageDir sourceContextSaveVAddr nbL _ sourcePartDesc PDidx).
Admitted.

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
  List.In targetPartDesc (StateLib.getPartitions multiplexer s) /\
  targetPartDesc <> defaultPage
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


(* rootPartition := MALInternal.getMultiplexer *)
eapply WP.bindRev.
eapply WP.weaken.
apply Invariants.getMultiplexer.
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

(* 
set (H_isolation := (fun s : state =>
            partitionsIsolation s /\ kernelDataIsolation s /\
            verticalSharing s /\ consistency s
         )).
eapply WP.bindRev.
instantiate (1:= fun _ s => H_isolation s).
eapply WP.weaken.
apply Invariants.updateCurPartition.

cbn.
intro s.
set (s' := {| currentPartition := targetPartDesc; memory := memory s |}).
apply updateCurPartitionToPartition.

(* proof that changing the current partition in the state does not break isolation *)
intros H_s_isolation.
unfold H_isolation in *.
destruct H_s_isolation as [H_part [H_kern [H_vert H_cons]]].
assert (memory s = memory s') as H_same_mem by trivial.
split; try split; try split; clear H_isolation.
- clear H_kern H_vert H_cons.
  apply partitionsIsolationActivate.
  trivial.
- clear H_part H_vert H_cons.
  apply kernelDataIsolationActivate.
  trivial.
- clear H_part H_kern H_cons.
  apply verticalSharingActivate.
  trivial.
- clear H_part H_kern H_vert.
  apply consistencyActivate.

  unfold partitionsIsolation in *.
  intros parent child1 child2 H_parent_in_part_list H_child1 H_child2 H_diff_children.
  assert (forall child, StateLib.getUsedPages child s' = StateLib.getUsedPages child s)
    as H_same_used_pages by admit.
  replace (StateLib.getUsedPages child1 s') with (StateLib.getUsedPages child1 s)
    by (rewrite H_same_used_pages; reflexivity).
  replace (StateLib.getUsedPages child2 s') with (StateLib.getUsedPages child2 s)
    by (rewrite H_same_used_pages; reflexivity).
  clear H_same_used_pages.
  apply H_part with parent; trivial.
  + assert (forall multiplexer, StateLib.getPartitions multiplexer s' = StateLib.getPartitions multiplexer s)
      as H_same_part_tree.
      intro multiplexer.
      cbn.
      replace s with {| currentPartition := (currentPartition s); memory := memory s |} by (destruct s; trivial).
      cbn.
      unfold s'.
  unfold StateLib.getPartitions.
  destruct (nbPage + 1).
  reflexivity.
  cbn.
  f_equal.
  unfold StateLib.getChildren.
  destruct StateLib.getNbLevel; trivial.
  replace (StateLib.getPd multiplexer (memory {| currentPartition := targetPartDesc; memory := memory s |}))
     with (StateLib.getPd multiplexer (memory {| currentPartition := currentPartition s; memory := memory s |})) by admit.
  destruct (StateLib.getPd multiplexer (memory {| currentPartition := currentPartition s; memory := memory s |})); trivial.
  cbn.
  unfold StateLib.checkChild.
  destruct (nbLevel - 1).
  cbn.
  reflexivity.
  unfold StateLib.getIndirection. , StateLib.getMappedPage .
  cbn.
  replace (StateLib.getIndirection p va level (nbLevel - 1) {| currentPartition := targetPartDesc; memory := memory s |}) with
  (StateLib.getIndirection p va level (nbLevel - 1) {| currentPartition := (currentPartition s); memory := memory s |}).
  unfold StateLib.getIndirection.
  cbn.
  simpl.
  reflexivity.


    replace (StateLib.getPartitions multiplexer s) with (StateLib.getPartitions multiplexer s')
      by (rewrite H_same_part_tree; reflexivity).
    trivial.
  + assert (forall parent, StateLib.getChildren parent s' = StateLib.getChildren parent s)
      as H_same_children by admit.
    replace (StateLib.getChildren parent s) with (StateLib.getChildren parent s')
      by (rewrite H_same_children; reflexivity).
    trivial.
  + assert (forall parent, StateLib.getChildren parent s' = StateLib.getChildren parent s)
      as H_same_children by admit.
    replace (StateLib.getChildren parent s) with (StateLib.getChildren parent s')
      by (rewrite H_same_children; reflexivity).
    trivial.
(* kernel Isolation *)
- unfold kernelDataIsolation in *.
  intros part1 part2.

Admitted.
 *)





