From Pip.Model.Meta Require Import TypesModel StateModel InterfaceModel StateAgnosticMonad.
Require Import Bool.

Module HollowTypes <: TypesModel.

  Parameter index : Type.
  Parameter index_d : index.
  Parameter page  : Type.
  Parameter page_d : page.
  Parameter paddr : Type.
  Parameter vaddr : Type.
  Parameter level : Type.
  Parameter level_d : level.
  Parameter count : Type.
  Parameter count_d : count.
  Parameter boolvaddr : Type.
  Parameter userValue : Type.
  Parameter contextAddr : Type.
  Parameter interruptMask : Type.
  Parameter int_mask_d : interruptMask.

  Inductive yield_checks : Type :=
| FAIL_INVALID_INT_LEVEL
| FAIL_INVALID_CTX_SAVE_INDEX
| FAIL_CALLER_CONTEXT_SAVE
| FAIL_UNAVAILABLE_TARGET_VIDT
| FAIL_UNAVAILABLE_TARGET_CTX
| FAIL_UNAVAILABLE_CALLER_VIDT
| FAIL_ROOT_CALLER
| FAIL_INVALID_CHILD
| FAIL_MASKED_INTERRUPT
| SUCCESS.

End HollowTypes.

Module HollowState <: StateModel.

  Parameter state : Type.

End HollowState.

Module HollowInterface <: (InterfaceModel HollowTypes HollowState).

  Module SAMM := StateAgnosticMonad HollowState.
  Export SAMM.
  Import HollowTypes.

  Parameter getCurPartition : SAM page.
  Parameter updateCurPartition : page -> SAM unit.
  Parameter readVirtual    : page -> index -> SAM vaddr.
  Parameter readPhysical    : page -> index -> SAM page.
  Parameter readVirEntry    : page -> index -> SAM vaddr.
  Parameter readPhyEntry    : page -> index -> SAM page.
  Parameter writeVirtual    : page -> index -> vaddr -> SAM unit.
  Parameter writePhysical    : page -> index -> page -> SAM unit.
  Parameter writeVirEntry    : page -> index -> vaddr -> SAM unit.
  Parameter writePhyEntry    : page -> index -> page -> bool -> bool -> bool -> bool -> bool -> SAM unit.
  Parameter mapKernel    : page -> index -> SAM unit.
  Parameter readAccessible    : page -> index -> SAM bool.
  Parameter writeAccessible    : page -> index -> bool -> SAM unit.
  Parameter readPresent    : page -> index -> SAM bool.
  Parameter writePresent    : page -> index -> bool -> SAM unit.
  Parameter readPDflag    : page -> index -> SAM bool.
  Parameter writePDflag    : page -> index -> bool -> SAM unit.
  Parameter readIndex    : page -> index -> SAM index.
  Parameter writeIndex    : page -> index -> index -> SAM unit.
  Parameter getMaxIndex    : SAM index.
  Parameter checkRights    : bool -> bool -> bool -> SAM bool.
  Parameter maxFreeLL    : SAM index.
  Parameter getIndexOfAddr    : vaddr -> level -> SAM index.
  Parameter getNbLevel    : SAM level.
  Parameter prepareType    : bool -> vaddr -> SAM boolvaddr.
  Parameter getPd    : page -> SAM page.
  Parameter readVirtualUser    : page -> index -> SAM vaddr.
  Parameter fetchVirtual    : vaddr -> index -> SAM vaddr.
  Parameter storeVirtual    : vaddr -> index -> vaddr -> SAM unit.
  Parameter setInterruptMask    : interruptMask -> SAM unit.
  Parameter getInterruptMaskFromCtx    : contextAddr -> SAM interruptMask.
  Parameter noInterruptRequest : interruptMask -> SAM bool.
  Parameter updateMMURoot    : page -> SAM unit.
  Parameter getMultiplexer    : SAM page.
  Parameter page_eqb    : page -> page -> SAM bool.
  Parameter loadContext    : contextAddr -> bool -> SAM unit.

End HollowInterface.
