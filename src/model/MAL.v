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
     Memory Abstraction Layer : is the interface exposed to services to read and
    write data into physical memory  *)
Require Export Model.MALInternal. 
Require Import Model.ADT Model.Hardware Model.Lib Model.MMU.
Require Import Arith Bool NPeano List Omega.

(** Memory access : read and write functions for each data type "vaddr", "page", 
    "index", "Count", "level", "bool" (control flags) *)

Definition readVirtual (paddr : page) (idx : index) : LLI vaddr:=
  perform s := get in
  let entry :=  lookup paddr idx s.(memory) beqPage beqIndex  in
  match entry with
  | Some (VA a) => ret a
  | Some _ => undefined 3
  | None => undefined 2
  end.

Definition readPhysical (paddr : page) ( idx : index)  : LLI page:=
  perform s := get in
  let entry :=  lookup paddr idx s.(memory) beqPage beqIndex  in
  match entry with
  | Some (PP a) => ret a
  | Some _ => undefined 5
  | None => undefined 4
  end.

Definition readVirEntry (paddr : page) (idx : index) : LLI vaddr :=
  perform s := get in
  let entry :=  lookup paddr idx s.(memory) beqPage beqIndex  in
  match entry with
  | Some (VE a) => ret a.(va)
  | Some _ => undefined 7
  | None => undefined 6
  end.

Definition readPhyEntry (paddr : page) (idx : index) : LLI page :=
  perform s := get in
  let entry :=  lookup paddr idx s.(memory) beqPage beqIndex  in
  match entry with
  | Some (PE a) => ret a.(pa)
  | Some _ => undefined 9
  | None => undefined 8
  end.

Definition writeVirtual (paddr : page) (idx : index) (va : vaddr) : LLI unit:=
  modify (fun s => {| currentPartition := s.(currentPartition);
  memory :=   add paddr idx (VA va)  s.(memory) beqPage beqIndex|} ).

Definition writePhysical (paddr : page) (idx : index) (addr : page)  : LLI unit:=
  modify (fun s => {| currentPartition := s.(currentPartition);
  memory :=   add paddr idx (PP addr)  s.(memory) beqPage beqIndex|} ).

Definition writeVirEntry (paddr : page) (idx : index)(addr : vaddr) :=
  let newEntry := {| pd := false ; va := addr |} in
  modify (fun s => {|
  currentPartition := s.(currentPartition);
  memory :=   add paddr idx (VE newEntry) s.(memory) beqPage beqIndex|} ).

Definition writePhyEntry (paddr : page) (idx : index)(addr : page) (p u r w e: bool) :=
  modify (fun s => {| currentPartition := s.(currentPartition);
  memory :=   add paddr idx (PE {| read := r; write := w ; exec := e; present := p ; user := u ; pa := addr|})  s.(memory) beqPage beqIndex|} ).

Definition writeKernelPhyEntry (paddr : page) (idx : index)(addr : page) ( p u r w e: bool) :=
  modify (fun s => {| currentPartition := s.(currentPartition);
  memory :=   add paddr idx (PE {| read := r; write := w ; exec := e; present := p ; user := u ; pa := addr|})  
  s.(memory) beqPage beqIndex|} ).


Definition readAccessible  (paddr : page) (idx : index) : LLI bool:=
  perform s := get in
  let entry :=  lookup paddr idx  s.(memory) beqPage beqIndex in
  match entry with
  | Some (PE a) => ret a.(user)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeAccessible  (paddr : page) (idx : index) (flag : bool) : LLI unit:=
perform s := get in
let entry :=  lookup paddr idx s.(memory) beqPage beqIndex in
match entry with
| Some (PE a) => let newEntry := {| read := a.(read) ; write := a.(write) ; exec := a.(exec); present := a.(present); user:= flag;
  pa := a.(pa) |} in
  modify (fun s => {|
  currentPartition := s.(currentPartition);
  memory := add paddr idx (PE newEntry)  s.(memory) beqPage beqIndex |} )
| Some _ => undefined 14
| None => undefined 13
end.

Definition writePresent (paddr : page) (idx : index) (flag : bool) : LLI unit:=
perform s := get in
let entry :=  lookup paddr idx s.(memory) beqPage beqIndex in
match entry with
| Some (PE a) => let newEntry := {| read := a.(read) ; write := a.(write) ; exec := a.(exec); present := flag; user:= a.(user);
  pa := a.(pa) |} in
  modify (fun s => {|
  currentPartition := s.(currentPartition);
  memory := add paddr idx (PE newEntry)  s.(memory) beqPage beqIndex|} )

| Some _ => undefined 16
| None => undefined 15
end.

Definition readPresent  (paddr : page) (idx : index) : LLI bool:=
perform s := get in
let entry :=  lookup paddr idx s.(memory) beqPage beqIndex in
match entry with
  | Some (PE a) => ret a.(present)
  | Some _ => undefined 18
  | None => undefined 17
end.

Definition writePDflag (paddr : page) (idx : index) (flag : bool) : LLI unit:=
perform s := get in
let entry :=  lookup paddr idx s.(memory) beqPage beqIndex in
match entry with
  | Some (VE a) =>  let newEntry := {| pd := flag; va := a.(va) |} in
    modify (fun s => {|
    currentPartition := s.(currentPartition);
    memory := add paddr idx (VE newEntry) s.(memory) beqPage beqIndex|} )
  | Some _ => undefined 20
  | None => undefined 19
end.

Definition readPDflag  (paddr : page) (idx : index) : LLI bool:=
perform s := get in
let entry :=  lookup paddr idx s.(memory) beqPage beqIndex in
match entry with
  | Some (VE a) =>  ret a.(pd)
  | Some _ => undefined 21
  | None => undefined 22
end.

Definition writeIndex  (paddr : page) (idx : index) (count : index) : LLI unit:=
perform s := get in
modify (fun s => {|
    currentPartition := s.(currentPartition);
    memory :=   add paddr idx (I count)  s.(memory) beqPage beqIndex|} ).

Definition readIndex  (paddr : page) (idx : index) : LLI index:=
  perform s := get in
  let entry := lookup paddr idx s.(memory) beqPage beqIndex in
  match entry with
  | Some (I e) =>  ret e
  | Some _ => undefined 24
  | None => undefined 23
  end.

Definition checkRights (r w e : bool):= 
if (r && w && e) 
then  
ret true
else ret (true || w).
(*** End memory access *)

(** The 'getMaxIndex' function returns the physical page size (minus 1) *)
Program Definition getMaxIndex : LLI index:=
if gt_dec tableSize 0
then
  ret (Build_index (tableSize - 1) _)
else undefined 36.

(* BEGIN NOT SIMULATION *)

Next Obligation.
omega.
Qed.

(* END NOT SIMULATION *)

(** The 'getIndexOfAddr' function returns the index of va that corresponds to l *)
Definition getIndexOfAddr (va : vaddr) (l : level) : LLI index:=
  ret ( nth ((length va) - (l + 2)) va defaultIndex ).

Definition preVaddrToVaddr preVaddr : LLI vaddr :=
ret (CVaddr (map CIndex preVaddr)). 

Definition extractPreIndex (va : preVaddr) (pos : preLevel) : LLI preIndex :=
 ret (nth pos va preIndex_d).


(** The 'getNbLevel' function returns the number of levels of the MMU *)
Program Definition getNbLevel : LLI level:=
if gt_dec nbLevel 0
then
  ret (Build_level (nbLevel -1) _ ) else undefined 35.
(* BEGIN NOT SIMULATION *)
Next Obligation.
omega.
Qed.
(* END NOT SIMULATION *)

(** The 'getCurPartition' function returns the current Partition from the current state *)
Definition getCurPartition : LLI page:=
  perform s := get in  ret s.(currentPartition).

(** The 'activate' function update the current Partition *)
Definition activate (phyPartition : page) : LLI unit := 
  modify (fun s => {| currentPartition := phyPartition;
  memory := s.(memory)|} ).

(***************************** STORE AND FETCH ****************************)
(* (** The 'comparePageToNull' returns true if the given page is equal to the fixed
    default page (null) *) 
Definition comparePageToNull (p :page) : LLI bool :=
  perform nullPaddr := getDefaultPage in
  MALInternal.Page.eqb nullPaddr p.
  
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
  readPhyEntry lastTable idx. *)

(** The 'getPd' function returns the page directory of a given partition *)
Definition getPd partition :=
  perform idxPD := getPDidx in
  perform idx := MALInternal.Index.succ idxPD in
  readPhysical partition idx.

(** The 'fetchVirtual' function translates the given virtual address to physical address in the 
    current partition and read the value stored into the physical address. This value is a 
    virtual address  *)
Definition fetchVirtual ( va : vaddr) (idx : index)  : LLI vaddr:=
  perform currentPartition := getCurPartition in 
  perform currentPD := getPd currentPartition in 
  perform nbL := getNbLevel in 
  perform phyPage := translate currentPD va nbL in
  perform isNull := comparePageToNull phyPage in
  if isNull then getDefaultVAddr else
  readVirtual phyPage idx.
  
(** The 'storeVirtual' function translates the given virtual address to physical address in the 
    current partition and stores a value into the physical address. *)
Definition storeVirtual (va : vaddr) (idx : index) (vaToStore : vaddr) : LLI unit:=
  perform currentPartition := getCurPartition in 
  perform currentPD := getPd currentPartition in 
  perform nbL := getNbLevel in 
  perform phyPage := translate currentPD va nbL in 
  writeVirtual phyPage idx vaToStore.