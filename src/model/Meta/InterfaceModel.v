From Pip.Model.Meta Require Import TypesModel StateModel StateAgnosticMonad.

Module Type InterfaceModel (Export Types : TypesModel)
                           (Export State : StateModel).

  Module SAMM := StateAgnosticMonad State.
  Export SAMM.
  (* Monad Interface *)

  Parameter getCurPartition : SAM page.
  Parameter updateCurPartition : page -> SAM unit.
  Parameter readVirtual : page -> index -> SAM vaddr.
  Parameter readPhysical : page -> index -> SAM page.
  Parameter readVirEntry : page -> index -> SAM vaddr.
  Parameter readPhyEntry : page -> index -> SAM page.
  Parameter writeVirtual : page -> index -> vaddr -> SAM unit.
  Parameter writePhysical : page -> index -> page -> SAM unit.
  Parameter writeVirEntry : page -> index -> vaddr -> SAM unit.
  Parameter writePhyEntry : page -> index -> page -> bool -> bool -> bool -> bool -> bool -> SAM unit.
  Parameter mapKernel : page -> index -> SAM unit.
  Parameter readAccessible : page -> index -> SAM bool.
  Parameter writeAccessible : page -> index -> bool -> SAM unit.
  Parameter readPresent : page -> index -> SAM bool.
  Parameter writePresent : page -> index -> bool -> SAM unit.
  Parameter readPDflag : page -> index -> SAM bool.
  Parameter writePDflag : page -> index -> bool -> SAM unit.
  Parameter readIndex : page -> index -> SAM index.
  Parameter writeIndex : page -> index -> index -> SAM unit.
  Parameter getMaxIndex : SAM index.
  Parameter checkRights : bool -> bool -> bool -> SAM bool.
  Parameter maxFreeLL : SAM index.
  Parameter getIndexOfAddr : vaddr -> level -> SAM index.
  Parameter getNbLevel : SAM level.
  Parameter prepareType : bool -> vaddr -> SAM boolvaddr.
  Parameter getPd : page -> SAM page.
  Parameter readVirtualUser : page -> index -> SAM vaddr.
  Parameter fetchVirtual : vaddr -> index -> SAM vaddr.
  Parameter storeVirtual : vaddr -> index -> vaddr -> SAM unit.
  Parameter setInterruptMask : interruptMask -> SAM unit.
  Parameter getInterruptMaskFromCtx : contextAddr -> SAM interruptMask.
  Parameter noInterruptRequest : interruptMask -> SAM bool.
  Parameter updateMMURoot : page -> SAM unit.
  Parameter getMultiplexer : SAM page.
  Parameter page_eqb : page -> page -> SAM bool.
  Parameter loadContext : contextAddr -> bool -> SAM unit.

End InterfaceModel.