From Pip.Model Require Import CoreTypes.
From Pip.Model Require Import StateParameter.
From Pip.Model Require Import StateParameterizedMonadType.
From Pip.Model Require Import MonadInterfaceParameters.

Require Import Bool.

Module MonadDependentCode (State : StateParameter)
                          (Export MonadInterface : MonadInterfaceParameters State).


Definition switchContextCont (targetPartDesc : page)
                             (targetPageDir  : page)
                             (flagsOnYield   : interruptMask)
                             (targetContext  : contextAddr)
                             : SPM yield_checks :=

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

End MonadDependentCode.