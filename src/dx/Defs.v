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

From Coq Require Import ZArith.
From Coq Require Import List String.
Import ListNotations.

Close Scope nat_scope.
Open Scope Z_scope.

From compcert.cfrontend Require Csyntax Ctypes Cop.
From compcert.common Require Values.
From compcert.lib Require Integers.

From dx      Require Import CoqIR IR IRtoC ResultMonad.
From dx.Type Require Bool Nat.

Import UserIdentNotations.

From Pip.Model Require Hardware ADT Constants Ops MAL IAL.
From Pip.Core  Require Internal Services.
From Pip.Arch  Require DataTypes.

Definition funIndexIndexBoolType :=
  MkCompilableSymbolType
    [ DataTypes.indexCompilableType; DataTypes.indexCompilableType ]
    (Some Bool.boolCompilableType).

Definition funVAddrVAddrBoolType :=
  MkCompilableSymbolType
    [ DataTypes.vaddrCompilableType; DataTypes.vaddrCompilableType ]
    (Some Bool.boolCompilableType).

Definition funPagePageBoolType :=
  MkCompilableSymbolType
    [ DataTypes.pageCompilableType; DataTypes.pageCompilableType ]
    (Some Bool.boolCompilableType).

Definition funLevelLevelBoolType :=
  MkCompilableSymbolType
    [ DataTypes.levelCompilableType; DataTypes.levelCompilableType ]
    (Some Bool.boolCompilableType).

Definition yieldChecksSymbolType :=
  MkCompilableSymbolType [] (Some DataTypes.yieldChecksType).

Definition cval n :=
  Csyntax.Eval (Values.Vint (Integers.Int.repr n)) DataTypes.constantsT.

Definition cBinOp o es :=
  match es with
  | [e1;e2] => Ok (Csyntax.Ebinop o e1 e2 Ctypes.type_bool)
  | _       => Err PrimitiveEncodingFailed
  end.

Definition cEq := cBinOp Cop.Oeq.
Definition cGe := cBinOp Cop.Oge.
Definition cGt := cBinOp Cop.Ogt.
Definition cLe := cBinOp Cop.Ole.
Definition cLt := cBinOp Cop.Olt.

Module PipPrimitives.
  Definition idxEqPrim   := MkPrimitive funIndexIndexBoolType Ops.idxEq   cEq.
  Definition idxGePrim   := MkPrimitive funIndexIndexBoolType Ops.idxGe   cGe.
  Definition idxGtPrim   := MkPrimitive funIndexIndexBoolType Ops.idxGt   cGt.
  Definition idxLePrim   := MkPrimitive funIndexIndexBoolType Ops.idxLe   cLe.
  Definition idxLtPrim   := MkPrimitive funIndexIndexBoolType Ops.idxLt   cLt.
  Definition vaddrEqPrim := MkPrimitive funVAddrVAddrBoolType Ops.vaddrEq cEq.
  Definition pageEqPrim  := MkPrimitive funPagePageBoolType   Ops.pageEq  cEq.
  Definition levelEqPrim := MkPrimitive funLevelLevelBoolType Ops.levelEq cEq.
  Definition levelGtPrim := MkPrimitive funLevelLevelBoolType Ops.levelGt cGt.

  Definition yieldSuccessPrim :=
    constant yieldChecksSymbolType Hardware.SUCCESS_Cons (cval 0).
  Definition yieldFailInvalidIntLevel :=
    constant yieldChecksSymbolType Hardware.FAIL_INVALID_INT_LEVEL_Cons (cval 1).
  Definition yieldFailInvalidCtxSaveIndex :=
    constant yieldChecksSymbolType Hardware.FAIL_INVALID_CTX_SAVE_INDEX_Cons (cval 2).
  Definition yieldFailRootCaller :=
    constant yieldChecksSymbolType Hardware.FAIL_ROOT_CALLER_Cons (cval 3).
  Definition yieldFailInvalidChild :=
    constant yieldChecksSymbolType Hardware.FAIL_INVALID_CHILD_Cons (cval 4).
  Definition yieldFailUnavailableTargetVIDT :=
    constant yieldChecksSymbolType Hardware.FAIL_UNAVAILABLE_TARGET_VIDT_Cons (cval 5).
  Definition yieldFailUnavailableCallerVIDT :=
    constant yieldChecksSymbolType Hardware.FAIL_UNAVAILABLE_CALLER_VIDT_Cons (cval 6).
  Definition yieldFailMaskedInterrupt :=
    constant yieldChecksSymbolType Hardware.FAIL_MASKED_INTERRUPT_Cons (cval 7).
  Definition yieldFailUnavailableTargetCtx :=
    constant yieldChecksSymbolType Hardware.FAIL_UNAVAILABLE_TARGET_CTX_Cons (cval 8).
  Definition yieldFailCallerContextSave :=
    constant yieldChecksSymbolType Hardware.FAIL_CALLER_CONTEXT_SAVE_Cons (cval 9).

  Definition yieldSuccessPrim' :=
    constant yieldChecksSymbolType IAL.SUCCESS (cval 0).
  Definition yieldFailInvalidIntLevel' :=
    constant yieldChecksSymbolType IAL.FAIL_INVALID_INT_LEVEL (cval 1).
  Definition yieldFailInvalidCtxSaveIndex' :=
    constant yieldChecksSymbolType IAL.FAIL_INVALID_CTX_SAVE_INDEX (cval 2).
  Definition yieldFailRootCaller' :=
    constant yieldChecksSymbolType IAL.FAIL_ROOT_CALLER (cval 3).
  Definition yieldFailInvalidChild' :=
    constant yieldChecksSymbolType IAL.FAIL_INVALID_CHILD (cval 4).
  Definition yieldFailUnavailableTargetVIDT' :=
    constant yieldChecksSymbolType IAL.FAIL_UNAVAILABLE_TARGET_VIDT (cval 5).
  Definition yieldFailUnavailableCallerVIDT' :=
    constant yieldChecksSymbolType IAL.FAIL_UNAVAILABLE_CALLER_VIDT (cval 6).
  Definition yieldFailMaskedInterrupt' :=
    constant yieldChecksSymbolType IAL.FAIL_MASKED_INTERRUPT (cval 7).
  Definition yieldFailUnavailableTargetCtx' :=
    constant yieldChecksSymbolType IAL.FAIL_UNAVAILABLE_TARGET_CTX (cval 8).
  Definition yieldFailCallerContextSave' :=
    constant yieldChecksSymbolType IAL.FAIL_CALLER_CONTEXT_SAVE (cval 9).
End PipPrimitives.

GenerateIntermediateRepresentation
  InternalHIRSyms
  Hardware.LLI Hardware.bind Hardware.ret

  Bool.Exports
  Nat.Exports

  DataTypes.Exports

  Internal
  .

Definition dxModuleInternalH := makeDXModuleWithDefaults InternalHIRSyms.

GenerateIntermediateRepresentation
  InternalIRSyms
  Hardware.LLI Hardware.bind Hardware.ret

  Bool.Exports
  Nat.Exports

  DataTypes.Exports
  PipPrimitives

  Constants

  Ops.idxPredM
  Ops.idxSuccM
  Ops.levelPredM
  Ops.levelSuccM
  Ops.countSuccM
  Ops.countFromLevelM

  MAL

  ADT.nbLevel
  ADT.boundNbLevel
  ADT.tableSize
  ADT.nbPage
  ADT.boundNbPages
  ADT.maxVint
  ADT.contextSize

  __

  Internal
  .

Definition dxModuleInternal := makeDXModuleWithDefaults InternalIRSyms.

GenerateIntermediateRepresentation
  ServicesHIRSyms
  Hardware.LLI Hardware.bind Hardware.ret

  Bool.Exports
  Nat.Exports

  DataTypes.Exports
  PipPrimitives

  Constants

  Ops.idxPredM
  Ops.idxSuccM
  Ops.levelPredM
  Ops.levelSuccM
  Ops.countSuccM
  Ops.countFromLevelM

  MAL

  IAL.setInterruptMask
  IAL.getInterruptMaskFromCtx
  IAL.noInterruptRequest
  IAL.writeContext
  IAL.vaddrToContextAddr
  IAL.checkIndexPropertyLTB
  IAL.userValueToIndex
  IAL.updateMMURoot

  ADT.nbLevel
  ADT.tableSize
  ADT.nbPage
  ADT.maxVint
  ADT.contextSize

  Services
  .

Definition dxModuleServicesH := makeDXModuleWithUserIds DataTypes.composites DataTypes.structIds ServicesHIRSyms.

GenerateIntermediateRepresentation
  ServicesIRSyms
  Hardware.LLI Hardware.bind Hardware.ret

  Bool.Exports
  Nat.Exports

  DataTypes.Exports
  PipPrimitives

  Constants

  Ops.idxPredM
  Ops.idxSuccM
  Ops.levelPredM
  Ops.levelSuccM
  Ops.countSuccM
  Ops.countFromLevelM

  MAL

  IAL.setInterruptMask
  IAL.getInterruptMaskFromCtx
  IAL.noInterruptRequest
  IAL.writeContext
  IAL.vaddrToContextAddr
  IAL.checkIndexPropertyLTB
  IAL.userValueToIndex
  IAL.loadContext
  IAL.getNthVAddrFrom
  IAL.contextSizeMinusOne
  IAL.firstVAddrGreaterThanSecond
  IAL.updateMMURoot

  ADT.nbLevel
  ADT.boundNbLevel
  ADT.tableSize
  ADT.nbPage
  ADT.boundNbPages
  ADT.maxVint
  ADT.contextSize

  Internal

  __

  Services
  .

Definition dxModuleServices := makeDXModuleWithUserIds DataTypes.composites DataTypes.structIds ServicesIRSyms.
