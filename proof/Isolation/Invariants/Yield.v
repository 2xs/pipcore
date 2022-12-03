From Pip.Model.Isolation Require Import IsolationTypes IsolationState IsolationInterface.
From Pip.Core Require Import ModelAgnosticCode.

From Pip.Proof.Isolation Require Import ModelExclusiveFunctions IsolationProperties ConsistencyProperties.

Import IsolationTypes.
Import IsolationInterface.SAMM.

Module IsolationSpecificCode := ModelAgnosticCode IsolationTypes IsolationState IsolationInterface.
Import IsolationSpecificCode.

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
  List.In targetPartDesc (getPartitions pageRootPartition s) /\
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
Admitted.