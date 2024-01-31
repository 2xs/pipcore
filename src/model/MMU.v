(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2024)                *)
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

Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.Constants Pip.Model.Ops.
Require Import Arith Bool NPeano List.
(** The 'comparePageToNull' returns true if the given page is equal to the fixed
    default page (null) *) 
Definition comparePageToNull (p :page) : LLI bool :=
  perform nullPaddr := getPageDefault in
  pageEqM nullPaddr p.
(** The 'getIndexOfAddr' function returns the index of va that corresponds to l *)
Definition getIndexOfAddr (va : vaddr) (l : level) : LLI index:=
  ret ( nth ((length va) - (l + 2)) va idxDefault ).

Definition readPhyEntry (paddr : page) (idx : index) : LLI page :=
  perform s := get in
  let entry :=  lookup paddr idx s.(memory) pageEq idxEq  in
  match entry with
  | Some (PE a) => ret a.(pa)
  | Some _ => undefined 9
  | None => undefined 8
  end.

Definition readPresent  (paddr : page) (idx : index) : LLI bool:=
perform s := get in
let entry :=  lookup paddr idx s.(memory) pageEq idxEq in
match entry with
  | Some (PE a) => ret a.(present)
  | Some _ => undefined 18
  | None => undefined 17
end.

Definition readAccessible  (paddr : page) (idx : index) : LLI bool:=
perform s := get in
let entry :=  lookup paddr idx s.(memory) pageEq idxEq in
match entry with
  | Some (PE a) => ret a.(user)
  | Some _ => undefined 12
  | None => undefined 11
end.

(** The 'getTableAddrAux' returns the reference to the last page table  *)
Fixpoint translateAux timeout (pd : page) (va : vaddr) (l : level) :=
  match timeout with
  | 0 => getPageDefault
  |S timeout1 =>
  perform isFstLevel := levelEqM l levelMin in 
    if isFstLevel 
    then  ret pd 
    else
      perform idx :=  getIndexOfAddr va l in
      perform addr :=  readPhyEntry pd idx in 
      perform isNull := comparePageToNull addr in
      if isNull then getPageDefault else
      perform p := levelPredM l in
      translateAux timeout1 addr va p
  end .

(** The 'translate' *)
Definition  translate (pd : page) (va : vaddr) (l : level) : LLI (option page)  :=
  perform lastTable := translateAux nbLevel pd va l in 
  perform isNull := comparePageToNull lastTable in
  if isNull then ret None else
  perform idx :=  getIndexOfAddr va levelMin in
  perform ispresent := readPresent lastTable idx in 
  perform isaccessible := readAccessible lastTable idx in
  if (ispresent && isaccessible) then  
  perform phypage := readPhyEntry lastTable idx in 
  ret (Some phypage)
  else ret None.
