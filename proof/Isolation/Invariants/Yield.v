(* From Pip.Model.Meta Require Import TypesModel StateModel StateAgnosticMonad InterfaceModel. *)
From Pip.Model.Isolation Require Import IsolationTypes IsolationState IsolationInterface.
From Pip.Core Require Import ModelAgnosticCode.

(* From Pip.Proof.Isolation Require Import IsolationProperties.
 *)
Import IsolationTypes.
Import IsolationInterface.SAMM.

(* Require Import Coq.Classes.RelationClasses.
Require Import Lia.

From Pip.Proof Require Import
CheckChild Consistency DependentTypeLemmas GetTableAddr InternalLemmas Invariants Isolation
updateCurPartition WeakestPreconditions.
 *)
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