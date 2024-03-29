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
     Memory Abstraction Layer : is the interface exposed to services to read and
    write data into physical memory  *)
Require Export Pip.Model.Constants Pip.Model.Ops.
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MMU.
Require Import Arith Bool NPeano List Lia.

(** Memory access : read and write functions for each data type "vaddr", "page", 
    "index", "Count", "level", "bool" (control flags) *)

Definition readVirtual (paddr : page) (idx : index) : LLI vaddr:=
  perform s := get in
  let entry :=  lookup paddr idx s.(memory) pageEq idxEq  in
  match entry with
  | Some (VA a) => ret a
  | Some _ => undefined 3
  | None => undefined 2
  end.

Definition readPhysical (paddr : page) ( idx : index)  : LLI page:=
  perform s := get in
  let entry :=  lookup paddr idx s.(memory) pageEq idxEq  in
  match entry with
  | Some (PP a) => ret a
  | Some _ => undefined 5
  | None => undefined 4
  end.

Definition readVirEntry (paddr : page) (idx : index) : LLI vaddr :=
  perform s := get in
  let entry :=  lookup paddr idx s.(memory) pageEq idxEq  in
  match entry with
  | Some (VE a) => ret a.(va)
  | Some _ => undefined 7
  | None => undefined 6
  end.

Definition readPhyEntry (paddr : page) (idx : index) : LLI page :=
  perform s := get in
  let entry :=  lookup paddr idx s.(memory) pageEq idxEq  in
  match entry with
  | Some (PE a) => ret a.(pa)
  | Some _ => undefined 9
  | None => undefined 8
  end.

Definition writeVirtual (paddr : page) (idx : index) (va : vaddr) : LLI unit:=
  modify (fun s => {| currentPartition := s.(currentPartition);
  memory :=   add paddr idx (VA va)  s.(memory) pageEq idxEq|} ).

Definition writePhysical (paddr : page) (idx : index) (addr : page)  : LLI unit:=
  modify (fun s => {| currentPartition := s.(currentPartition);
  memory :=   add paddr idx (PP addr)  s.(memory) pageEq idxEq|} ).

Definition writeVirEntry (paddr : page) (idx : index)(addr : vaddr) :=
  let newEntry := {| pd := false ; va := addr |} in
  modify (fun s => {|
  currentPartition := s.(currentPartition);
  memory :=   add paddr idx (VE newEntry) s.(memory) pageEq idxEq|} ).

Definition writePhyEntry (paddr : page) (idx : index)(addr : page) (p u r w e: bool) :=
  modify (fun s => {| currentPartition := s.(currentPartition);
  memory :=   add paddr idx (PE {| read := r; write := w ; exec := e; present := p ; user := u ; pa := addr|})  s.(memory) pageEq idxEq|} ).

(** This function is a model of the real function that will map the kernel into a partition's virtual memory
    Note that the model inserts a dummy physical entry that is totally neutral to the model (its 'present' flag
    is set to false).

    This function's model is in contradiction with the real world, where the actual flags written may not be the
    same as below, and the page mapped may also not be the same (or may not even exist).

    The kernel model explicitly omits memory that is not available to the root partition.
    As such, the kernel's stack, code and the root partition configuration pages are out of the scope of the proof.

    Because the preconfigured kernel MMU page is a part of the root partition configuration pages, the page is not
    inside the model, and we cannot talk about it. Furthermore, even if we *could* talk about it, it would break a
    fundamental property (partitionIsolation) saying that pages mapped in a partition are not shared with its
    siblings (that property remains true if we only consider the memory that is available to the root partition).

    Nonetheless, the kernel expects its kernel/boot environment memory to be located at a specific place in memory,
    to be able to check if it is not overwriting its own code/stack/setup configuration.
    Thus, this function has args so that the kernel provides the expected location in the MMU table.
*)
Definition mapKernel (paddr : page) (idx : index) :=
  modify (fun s =>
  {|
    currentPartition := s.(currentPartition);
    memory :=
      add paddr idx (
      PE {|
        read := false;
        write := false;
        exec := false;
        present := false;
        user := false;
        pa := pageDefault
      |})
      s.(memory) pageEq idxEq
  |}).


Definition readAccessible  (paddr : page) (idx : index) : LLI bool:=
  perform s := get in
  let entry :=  lookup paddr idx  s.(memory) pageEq idxEq in
  match entry with
  | Some (PE a) => ret a.(user)
  | Some _ => undefined 12
  | None => undefined 11
  end.

Definition writeAccessible  (paddr : page) (idx : index) (flag : bool) : LLI unit:=
perform s := get in
let entry :=  lookup paddr idx s.(memory) pageEq idxEq in
match entry with
| Some (PE a) => let newEntry := {| read := a.(read) ; write := a.(write) ; exec := a.(exec); present := a.(present); user:= flag;
  pa := a.(pa) |} in
  modify (fun s => {|
  currentPartition := s.(currentPartition);
  memory := add paddr idx (PE newEntry)  s.(memory) pageEq idxEq |} )
| Some _ => undefined 14
| None => undefined 13
end.

Definition writePresent (paddr : page) (idx : index) (flag : bool) : LLI unit:=
perform s := get in
let entry :=  lookup paddr idx s.(memory) pageEq idxEq in
match entry with
| Some (PE a) => let newEntry := {| read := a.(read) ; write := a.(write) ; exec := a.(exec); present := flag; user:= a.(user);
  pa := a.(pa) |} in
  modify (fun s => {|
  currentPartition := s.(currentPartition);
  memory := add paddr idx (PE newEntry)  s.(memory) pageEq idxEq|} )

| Some _ => undefined 16
| None => undefined 15
end.

Definition readPresent  (paddr : page) (idx : index) : LLI bool:=
perform s := get in
let entry :=  lookup paddr idx s.(memory) pageEq idxEq in
match entry with
  | Some (PE a) => ret a.(present)
  | Some _ => undefined 18
  | None => undefined 17
end.

Definition writePDflag (paddr : page) (idx : index) (flag : bool) : LLI unit:=
perform s := get in
let entry :=  lookup paddr idx s.(memory) pageEq idxEq in
match entry with
  | Some (VE a) =>  let newEntry := {| pd := flag; va := a.(va) |} in
    modify (fun s => {|
    currentPartition := s.(currentPartition);
    memory := add paddr idx (VE newEntry) s.(memory) pageEq idxEq|} )
  | Some _ => undefined 20
  | None => undefined 19
end.

Definition readPDflag  (paddr : page) (idx : index) : LLI bool:=
perform s := get in
let entry :=  lookup paddr idx s.(memory) pageEq idxEq in
match entry with
  | Some (VE a) =>  ret a.(pd)
  | Some _ => undefined 21
  | None => undefined 22
end.

Definition writeIndex  (paddr : page) (idx : index) (count : index) : LLI unit:=
perform s := get in
modify (fun s => {|
    currentPartition := s.(currentPartition);
    memory :=   add paddr idx (I count)  s.(memory) pageEq idxEq|} ).

Definition readIndex  (paddr : page) (idx : index) : LLI index:=
  perform s := get in
  let entry := lookup paddr idx s.(memory) pageEq idxEq in
  match entry with
  | Some (I e)  => ret e
  | Some (VA _) => undefined 240
  | Some _ => undefined 24
  | None => undefined 23
  end.

Definition checkRights (r w e : bool) :=
  ret true.
(*** End memory access *)

(** The 'getMaxIndex' function returns the physical page size (minus 1) *)
Program Definition getMaxIndex : LLI index:=
if gt_dec tableSize 0
then
  ret (Build_index (tableSize - 1) _)
else undefined 36.

Next Obligation.
lia.
Qed.

(** The 'maxFreeLL' function returns the maximum number of entrie (phy/vaddr) into LL table
*) 
Program Definition maxFreeLL : LLI index := 
ret (Build_index ((Coq.Init.Nat.div2 tableSize) - 2) _).
Next Obligation.
assert (tableSize > tableSizeLowerBound) by apply tableSizeBigEnough.
assert (tableSize > 0).
unfold tableSizeLowerBound in *.
lia.
assert(Hkey : Init.Nat.div2 tableSize < tableSize). 
apply NPeano.Nat.lt_div2; trivial.
lia.
Qed.


(** The 'getIndexOfAddr' function returns the index of va that corresponds to l *)
Definition getIndexOfAddr (va : vaddr) (l : level) : LLI index:=
  ret ( nth ((length va) - (l + 2)) va idxDefault ).

(** The 'getNbLevel' function returns the number of levels of the MMU *)
(* TODO: Either change the name of nbLevel or of getNbLevel or the code of getNbLevel *)
(* TODO: Propagate this fix to the C code *)
Program Definition getNbLevel : LLI level:=
if gt_dec nbLevel 0
then
  ret (Build_level (nbLevel -1) _ ) else undefined 35.
Next Obligation.
lia.
Qed.

Definition prepareType (val1 : bool) (val2 : vaddr) : LLI boolvaddr :=
ret (Build_boolvaddr val1 val2).

(** The 'getCurPartition' function returns the current Partition from the current state *)
Definition getCurPartition : LLI page:=
  perform s := get in  ret s.(currentPartition).

(** The 'updateCurPartition' function update the current Partition *)
Definition updateCurPartition (phyPartition : page) : LLI unit := 
  modify (fun s => {| currentPartition := phyPartition;
  memory := s.(memory)|} ).

(***************************** STORE AND FETCH ****************************)

(** The 'internalGetPageDir' function returns the page directory of a given partition *)
Definition internalGetPageDir partition :=
  perform idxPD := getIdxPageDir in
  perform idx := idxSuccM idxPD in
  readPhysical partition idx.

(* TODO use uservalues *)
Definition readVirtualUser paddr idx : LLI vaddr :=
  perform s := get in
  let entry :=  lookup paddr idx s.(memory) pageEq idxEq  in
  match entry with
  | Some (VA a) => ret a
  | Some _ => getVaddrDefault
  | None => getVaddrDefault
  end.
(** The 'readTableVirtual' function translates the given virtual address to physical address in the
    current partition and read the value stored into the physical address. This value is a
    virtual address  *)
Definition readTableVirtual (va : vaddr) (idx : index) : LLI vaddr :=
  perform currentPartition := getCurPartition in 
  perform currentPD := internalGetPageDir currentPartition in
  perform nbL := getNbLevel in 
  perform optionphyPage := translate currentPD va nbL in
  match optionphyPage with 
  | None => getVaddrDefault
  | Some phyPage => readVirtualUser phyPage idx
  end.
  
(** The 'storeVirtual' function translates the given virtual address to physical address in the 
    current partition and stores a value into the physical address. *)
Definition storeVirtual (va : vaddr) (idx : index) (vaToStore : vaddr) : LLI unit:=
  perform currentPartition := getCurPartition in 
  perform currentPD := internalGetPageDir currentPartition in
  perform nbL := getNbLevel in 
  perform optionphyPage := translate currentPD va nbL in
  match optionphyPage with 
  | None => ret tt
  | Some phyPage => writeVirtual phyPage idx vaToStore
  end.

