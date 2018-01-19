(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2017)                 *)
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
     Memory Management Unit : the specification of the translation of 
     virtual memory addresses to physical addresses *)

Require Import Model.ADT Model.Hardware Model.Lib Model.MALInternal .
Require Import Arith Bool NPeano List Omega.
(** The 'comparePageToNull' returns true if the given page is equal to the fixed
    default page (null) *) 
Definition comparePageToNull (p :page) : LLI bool :=
  perform nullPaddr := getDefaultPage in
  MALInternal.Page.eqb nullPaddr p.
(** The 'getIndexOfAddr' function returns the index of va that corresponds to l *)
Definition getIndexOfAddr (va : vaddr) (l : level) : LLI index:=
  ret ( nth ((length va) - (l + 2)) va defaultIndex ).

Definition readPhyEntry (paddr : page) (idx : index) : LLI page :=
  perform s := get in
  let entry :=  lookup paddr idx s.(memory) beqPage beqIndex  in
  match entry with
  | Some (PE a) => ret a.(pa)
  | Some _ => undefined 9
  | None => undefined 8
  end.

(** The 'getTableAddrAux' returns the reference to the last page table  *)
Fixpoint translateAux timeout (pd : page) (va : vaddr) (l : level) :=
  match timeout with
  | 0 => getDefaultPage
  |S timeout1 =>
  perform isFstLevel := MALInternal.Level.eqb l fstLevel in 
    if isFstLevel 
    then  ret pd 
    else
      perform idx :=  getIndexOfAddr va l in
      perform addr :=  readPhyEntry pd idx in 
      perform isNull := comparePageToNull addr in
      if isNull then getDefaultPage else
      perform p := MALInternal.Level.pred l in
      translateAux timeout1 addr va p
  end .

(** The 'translate' *)
Definition  translate (pd : page) (va : vaddr) (l : level)  :=
  perform lastTable := translateAux nbLevel pd va l in 
  perform isNull := comparePageToNull lastTable in
  if isNull then getDefaultPage else
  perform idx :=  getIndexOfAddr va fstLevel in
  readPhyEntry lastTable idx.