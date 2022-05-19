(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2022)                *)
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

(* Architecture-dependent data types *)
(* This module defines how the Pip abstract data types are mapped to actual C
   types *)

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

From Pip.Model Require Hardware ADT Constants Ops MALInternal MAL IAL.
From Pip.Core  Require Internal Services.

Definition uint32 : Ctypes.type :=
  Ctypes.Tint Ctypes.I32 Ctypes.Unsigned Ctypes.noattr.

Definition constantsT := uint32.

Definition userContextId := "user_ctx_s".
Definition userContextT := Ctypes.Tstruct $userContextId Ctypes.noattr.
Definition userContextPtr := Ctypes.Tpointer userContextT Ctypes.noattr.

Definition userContextComposite :=
  Ctypes.Composite
    $userContextId
    Ctypes.Struct
    [ Ctypes.Member_plain $"spsr"     uint32
    ; Ctypes.Member_plain $"reg"      (Ctypes.Tarray uint32 16 Ctypes.noattr)
    ; Ctypes.Member_plain $"pipflags" uint32
    ; Ctypes.Member_plain $"valid"    uint32
    ]
    Ctypes.noattr.

Definition composites := [ userContextComposite ].

Definition structIds :=
  [ userContextId
  ; "spsr"
  ; "reg"
  ; "pipflags"
  ; "valid"
  ].

Definition indexCompilableType         := MkCompilableType ADT.index uint32.
Definition pageCompilableType          := MkCompilableType ADT.page uint32.
Definition paddrCompilableType         := MkCompilableType ADT.paddr uint32.
Definition vaddrCompilableType         := MkCompilableType ADT.vaddr uint32.
Definition levelCompilableType         := MkCompilableType ADT.level uint32.
Definition countCompilableType         := MkCompilableType ADT.count uint32.
Definition boolvaddrCompilableType     := MkCompilableType ADT.boolvaddr uint32.
Definition userValueCompilableType     := MkCompilableType ADT.userValue uint32.
Definition vintCompilableType          := MkCompilableType ADT.vint uint32.
Definition contextAddrCompilableType   := MkCompilableType ADT.contextAddr userContextPtr.
Definition interruptMaskCompilableType := MkCompilableType ADT.interruptMask uint32.
Definition yieldChecksType             := MkCompilableType Hardware.yield_checks uint32.

Module Exports.
  Definition indexCompilableType         := indexCompilableType.
  Definition pageCompilableType          := pageCompilableType.
  Definition paddrCompilableType         := paddrCompilableType.
  Definition vaddrCompilableType         := vaddrCompilableType.
  Definition levelCompilableType         := levelCompilableType.
  Definition countCompilableType         := countCompilableType.
  Definition boolvaddrCompilableType     := boolvaddrCompilableType.
  Definition userValueCompilableType     := userValueCompilableType.
  Definition vintCompilableType          := vintCompilableType.
  Definition contextAddrCompilableType   := contextAddrCompilableType.
  Definition interruptMaskCompilableType := interruptMaskCompilableType.
  Definition yieldChecksType             := yieldChecksType.
End Exports.
