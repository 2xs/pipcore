Require Import Coq.Strings.String Lia NPeano.

From Pip.Model Require Import CoreTypes MonadInterfaceParameters StateParameter StateParameterizedMonadType.
Require Import Arith Bool List.
Import List.ListNotations.


Module AbstractState <: StateParameter.

  Parameter state : Type.

End AbstractState.

Module AbstractMonad <: MonadInterfaceParameters AbstractState.

  Module SPMT := StateParameterizedMonadType AbstractState.
  Export SPMT.

  Parameter getCurPartition : SPM page.
  Parameter updateCurPartition : page -> SPM unit.
  Parameter readVirtual    : page -> index -> SPM vaddr.
  Parameter readPhysical    : page -> index -> SPM page.
  Parameter readVirEntry    : page -> index -> SPM vaddr.
  Parameter readPhyEntry    : page -> index -> SPM page.
  Parameter writeVirtual    : page -> index -> vaddr -> SPM unit.
  Parameter writePhysical    : page -> index -> page -> SPM unit.
  Parameter writeVirEntry    : page -> index -> vaddr -> SPM unit.
  Parameter writePhyEntry    : page -> index -> page -> bool -> bool -> bool -> bool -> bool -> SPM unit.
  Parameter mapKernel    : page -> index -> SPM unit.
  Parameter readAccessible    : page -> index -> SPM bool.
  Parameter writeAccessible    : page -> index -> bool -> SPM unit.
  Parameter readPresent    : page -> index -> SPM bool.
  Parameter writePresent    : page -> index -> bool -> SPM unit.
  Parameter readPDflag    : page -> index -> SPM bool.
  Parameter writePDflag    : page -> index -> bool -> SPM unit.
  Parameter readIndex    : page -> index -> SPM index.
  Parameter writeIndex    : page -> index -> index -> SPM unit.
  Parameter getMaxIndex    : SPM index.
  Parameter checkRights    : bool -> bool -> bool -> SPM bool.
  Parameter maxFreeLL    : SPM index.
  Parameter getIndexOfAddr    : vaddr -> level -> SPM index.
  Parameter getNbLevel    : SPM level.
  Parameter prepareType    : bool -> vaddr -> SPM boolvaddr.
  Parameter getPd    : page -> SPM page.
  Parameter readVirtualUser    : page -> index -> SPM vaddr.
  Parameter fetchVirtual    : vaddr -> index -> SPM vaddr.
  Parameter storeVirtual    : vaddr -> index -> vaddr -> SPM unit.
  Parameter setInterruptMask    : interruptMask -> SPM unit.
  Parameter getInterruptMaskFromCtx    : contextAddr -> SPM interruptMask.
  Parameter noInterruptRequest : interruptMask -> SPM bool.
  Parameter updateMMURoot    : page -> SPM unit.
  Parameter getMultiplexer    : SPM page.
  Parameter page_eqb    : page -> page -> SPM bool.
  Parameter loadContext    : contextAddr -> bool -> SPM unit.

End AbstractMonad.
