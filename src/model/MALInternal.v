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

(** * Summary 
    This file contains the definition of some constants and its monadic getters;
    and the module definition of each abstract data type in which we define required
    monadic functions  *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib.
Require Import List Arith Lia.

Require Import Pip.Model.Constants Pip.Model.Ops.

#[deprecated(note="Use idxDefault instead")]
Notation defaultIndex := idxDefault (only parsing).
#[deprecated(note="Use vaddrDefault instead")]
Notation defaultVAddr := vaddrDefault (only parsing).
#[deprecated(note="Use vaddrMax instead")]
Notation lastVAddr := vaddrMax (only parsing).
#[deprecated(note="Use vaddrVIDT instead")]
Notation vidtVAddr := vaddrVIDT (only parsing).
#[deprecated(note="Use pageDefault instead")]
Notation defaultPage := pageDefault (only parsing).
#[deprecated(note="Use pageMultiplexer instead")]
Notation multiplexer := pageMultiplexer (only parsing).
#[deprecated(note="Use levelMin instead")]
Notation fstLevel := levelMin (only parsing).
#[deprecated(note="Use idxStoreFetch instead")]
Notation storeFetchIndex := idxStoreFetch (only parsing).
#[deprecated(note="Use idxKernel instead")]
Notation Kidx := idxKernel (only parsing).
#[deprecated(note="Use idxPartDesc instead")]
Notation PRidx := idxPartDesc (only parsing).
#[deprecated(note="Use idxPageDir instead")]
Notation PDidx := idxPageDir (only parsing).
#[deprecated(note="sh1idx deprecated, use idxShadow1 instead")]
Notation sh1idx := idxShadow1 (only parsing).
#[deprecated(note="sh2idx deprecated, use idxShadow2 instead")]
Notation sh2idx := idxShadow2 (only parsing).
#[deprecated(note="sh3idx deprecated, use idxShadow3 instead")]
Notation sh3idx := idxShadow3 (only parsing).
#[deprecated(note="Use idxParentDesc instead")]
Notation PPRidx := idxParentDesc (only parsing).
#[deprecated(note="Use getPageMultiplexer instead")]
Notation getMultiplexer := getPageMultiplexer (only parsing).


(** Define getter for each constant *)
#[deprecated(note="Use getVaddrDefault instead")]
Notation getDefaultVAddr := getVaddrDefault (only parsing).
#[deprecated(note="Use getVaddrMax instead")]
Notation getLastVAddr := getVaddrMax (only parsing).
#[deprecated(note="Use getPageDefault instead")]
Notation getDefaultPage := getPageDefault (only parsing).
#[deprecated(note="Use getIdxStoreFetch instead")]
Notation getStoreFetchIndex := getIdxStoreFetch (only parsing).
#[deprecated(note="Use getIdxKernel instead")]
Notation getKidx := getIdxKernel (only parsing).
#[deprecated(note="Use getIdxPartDesc instead")]
Notation getPRidx := getIdxPartDesc (only parsing).
#[deprecated(note="Use getIdxPageDir instead")]
Notation getPDidx := getIdxPageDir (only parsing).
#[deprecated(note="Use getIdxShadow1 instead")]
Notation getSh1idx := getIdxShadow1 (only parsing).
#[deprecated(note="Use getIdxShadow2 instead")]
Notation getSh2idx := getIdxShadow2 (only parsing).
#[deprecated(note="Use getIdxShadow3 instead")]
Notation getSh3idx := getIdxShadow3 (only parsing).
#[deprecated(note="Use getIdxParentDesc instead")]
Notation getPPRidx := getIdxParentDesc (only parsing).

#[deprecated(note="Use idxEq instead.")]
Notation beqIndex := idxEq (only parsing).
#[deprecated(note="Use pageEq instead.")]
Notation beqPage := pageEq (only parsing).
#[deprecated(note="Use vaddrEq instead.")]
Notation beqVAddr := vaddrEq (only parsing).

Module Index.
  #[deprecated(note="Use idxGeM instead.")]
  Notation geb := idxGeM (only parsing).
  #[deprecated(note="Use idxLeM instead.")]
  Notation leb := idxLeM (only parsing).
  #[deprecated(note="Use idxLtM instead.")]
  Notation ltb := idxLtM (only parsing).
  #[deprecated(note="Use idxGtM instead.")]
  Notation gtb := idxGtM (only parsing).
  #[deprecated(note="Use idxEqM instead.")]
  Notation eqb := idxEqM (only parsing).

  #[deprecated(note="Use getIdx0 instead.")]
  Notation zero := getIdx0 (only parsing).
  #[deprecated(note="Use getIdx3 instead.")]
  Notation const3 := getIdx3 (only parsing).

  #[deprecated(note="Use idxPredM instead.")]
  Notation pred := idxPredM (only parsing).
  #[deprecated(note="Use idxSuccM instead.")]
  Notation succ := idxSuccM (only parsing).
End Index.

Module Page.
  #[deprecated(note="Use pageEqM instead.")]
  Notation eqb := pageEqM (only parsing).
End Page.

Module Level.
  #[deprecated(note="Use levelGtM instead.")]
  Notation gtb := levelGtM (only parsing).
  #[deprecated(note="Use levelEqM instead.")]
  Notation eqb := levelEqM (only parsing).
  #[deprecated(note="Use levelPredM instead.")]
  Notation pred := levelPredM (only parsing).
  #[deprecated(note="Use levelSuccM instead.")]
  Notation succ := levelSuccM (only parsing).
End Level.

Module VAddr.
  #[deprecated(note="Use vaddrEqM instead.")]
  Notation eqbList := vaddrEqM (only parsing).
End VAddr.

Module Count.
  #[deprecated(note="Use countGeM instead.")]
  Notation geb := countGeM (only parsing).
  #[deprecated(note="Use countEqM instead.")]
  Notation eqb := countEqM (only parsing).
  #[deprecated(note="Use getCount0 instead.")]
  Notation zero := getCount0 (only parsing).
  #[deprecated(note="Use countSuccM instead.")]
  Notation succ := countSuccM (only parsing).
  #[deprecated(note="Use countFromLevelM instead.")]
  Notation mul3 := countFromLevelM (only parsing).
End Count.
