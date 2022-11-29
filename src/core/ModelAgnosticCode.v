From Pip.Model.Meta Require Import TypesModel StateModel InterfaceModel.
Require Import Bool.

Module ModelAgnosticCode (Export Types : TypesModel)
                         (Export State : StateModel)
                         (Export Interface : InterfaceModel Types State).


Definition switchContextCont (targetPartDesc : page)
                             (targetPageDir  : page)
                             (flagsOnYield   : interruptMask)
                             (targetContext  : contextAddr)
                             : SAM yield_checks :=

  setInterruptMask flagsOnYield ;;
  updateMMURoot targetPageDir ;;
  updateCurPartition targetPartDesc ;;
  perform flagsOnWake := getInterruptMaskFromCtx targetContext in
  setInterruptMask flagsOnWake ;;
  (* allow root partition to prevent Pip from enforcing interrupts *)
  perform rootPartition := getMultiplexer in
  perform targetIsRoot := page_eqb rootPartition targetPartDesc in
  perform targetReqNoInterrupt := noInterruptRequest flagsOnWake in
  (
  if (targetIsRoot && targetReqNoInterrupt)
  then
    loadContext targetContext false
  else
    loadContext targetContext true
  ) ;;
  (* Actually never reached *)
  ret SUCCESS.

End ModelAgnosticCode.