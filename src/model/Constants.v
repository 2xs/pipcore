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

Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib.
Require Import List Arith Lia.
Import ListNotations.

Definition idxDefault := CIndex 0.
(* TODO: Use semantical names rather than factual? *)
Definition idx0 := CIndex 0.
Definition idx3 := CIndex 3.

(** Define the second parameter value of store and fetch *)
Definition idxStoreFetch := CIndex 0.

(** Define the entry position of the kernel mapping into the first indirection
    of partitions *)
Definition idxKernel := CIndex 1.

(** Fix virtual addresses positions into the partition descriptor
    of the partition (+1 to get the physical page position) *)
Definition idxPartDesc   := CIndex 0.  (* descriptor *)
Definition idxPageDir    := CIndex 2.  (* page directory *)
Definition idxShadow1    := CIndex 4.  (* shadow1 *)
Definition idxShadow2    := CIndex 6.  (* shadow2 *)
Definition idxShadow3    := CIndex 8.  (* configuration pages list*)
Definition idxParentDesc := CIndex 10. (* parent (virtual address is null) *)

Definition vaddrDefault := CVaddr (repeat (CIndex 0) (nbLevel+1)).
Definition vaddrMax     := CVaddr (repeat (CIndex (tableSize - 1)) (nbLevel+1)).
Definition vaddrVIDT    := CVaddr (repeat (CIndex (tableSize - 1)) nbLevel ++ [CIndex 0]).

Definition pageDefault       := CPage 0.
Definition pageRootPartition := CPage 1.

Definition levelMin     := CLevel 0.
Definition count0       := CCount 0.


(* Monadic getters *)

Definition getIdxDefault        := ret idxDefault.
Definition getIdx0              := ret idx0.
Definition getIdx3              := ret idx3.
Definition getIdxStoreFetch     := ret idxStoreFetch.
Definition getIdxKernel         := ret idxKernel.
Definition getIdxPartDesc       := ret idxPartDesc.
Definition getIdxPageDir        := ret idxPageDir.
Definition getIdxShadow1        := ret idxShadow1.
Definition getIdxShadow2        := ret idxShadow2.
Definition getIdxShadow3        := ret idxShadow3.
Definition getIdxParentDesc     := ret idxParentDesc.
Definition getVaddrDefault      := ret vaddrDefault.
Definition getVaddrMax          := ret vaddrMax.
Definition getVaddrVIDT         := ret vaddrVIDT.
Definition getPageDefault       := ret pageDefault.
Definition getPageRootPartition := ret pageRootPartition.
Definition getCount0            := ret count0.
