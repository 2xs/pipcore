From Pip.Model.Meta Require Import TypesModel StateModel StateAgnosticMonad InterfaceModel.
From Pip.Model.Isolation Require Import IsolationTypes IsolationState.

Require Import Coq.Strings.String Lia NPeano.
Require Import Arith Bool List.
Import List.ListNotations.

Module IsolationInterface <: InterfaceModel IsolationTypes IsolationState.

  Module SAMM := StateAgnosticMonad IsolationState.
  Export SAMM.

  Fixpoint eqList {A : Type} (l1 l2 : list A) (eq : A -> A -> bool) : bool :=
  match l1, l2 with
  | nil, nil       => true
  | a::l1', b::l2' => if eq a b then eqList l1' l2' eq else false
  | _ , _          => false
  end.

  Definition beqIndex (a b : index) : bool := a =? b.
  Definition beqPage (a b : page) : bool := a =? b.
  Definition beqVAddr (a b : vaddr) : bool := eqList a b beqIndex.

  Definition beqPairs {A B: Type} (a : (A * B)) (b : (A * B))
                                  (eqA : A -> A -> bool) (eqB : B -> B -> bool) :=
    if (eqA (fst a) (fst b)) && (eqB (snd a) (snd b)) then
      true
    else false.

  Fixpoint lookup {A B C: Type} (k : A) (i : B) (assoc : list ((A * B) * C))
                                (eqA : A -> A -> bool) (eqB : B -> B -> bool) :=
  match assoc with
  | nil => None
  | (a, b) :: assoc' =>
    if beqPairs a (k,i) eqA eqB then
      Some b
    else
      lookup k i assoc' eqA eqB
  end.

  Definition getCurPartition : SAM page :=
    perform s := get in ret (currentPartition s).

  Definition updateCurPartition (p : page) : SAM unit :=
    modify (fun s => {| currentPartition := p; memory := s.(memory) |}).

  Definition readVirtual (p : page) (idx : index) : SAM vaddr :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (VA a) => ret a
  | Some _      => undefined "Error : expected to find a virtual address, but found another type"
  | None        => undefined "Error : no value at this address"
  end.

  Definition readPhysical (p : page) (idx : index) : SAM page :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (PP page) => ret page
  | Some _      => undefined "Error : expected to find a physical page, but found another type"
  | None        => undefined "Error : no value at this address"
  end.

  Definition readVirEntry (p : page) (idx : index) : SAM vaddr :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (VE vir_entry) => ret (va vir_entry)
  | Some _      => undefined "Error : expected to find a virtual entry, but found another type"
  | None        => undefined "Error : no value at this address"
  end.

  Definition readPhyEntry (p : page) (idx : index) : SAM page :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (PE phy_entry) => ret (pa phy_entry)
  | Some _      => undefined "Error : expected to find a physical entry, but found another type"
  | None        => undefined "Error : no value at this address"
  end.

  Fixpoint removeDup {A B C: Type} (k : A) (i : B) (assoc : list ((A * B) * C))
                                   (eqA : A -> A -> bool) (eqB : B -> B -> bool) :=
  match assoc with
    | nil => nil
    | (a, b) :: assoc' => if beqPairs a (k,i) eqA eqB then
                            removeDup k i assoc' eqA eqB
                          else (a, b) :: (removeDup k i assoc' eqA eqB)
  end.

  Definition add {A B C: Type} (k : A) (i : B) (v : C) (assoc : list ((A * B) * C))
                               (eqA : A -> A -> bool) (eqB : B -> B -> bool) :=
    (k, i, v) :: removeDup k i assoc eqA eqB.

  Definition writeVirtual (paddr : page) (idx : index) (va : vaddr) : SAM unit :=
  modify (fun s => {|
    currentPartition := s.(currentPartition);
    memory := add paddr idx (VA va) (memory s) beqPage beqIndex
  |}).

  Definition writePhysical (paddr : page) (idx : index) (p : page) : SAM unit :=
  modify (fun s => {|
    currentPartition := s.(currentPartition);
    memory := add paddr idx (PP p) (memory s) beqPage beqIndex
  |}).

  Definition writeVirEntry (paddr : page) (idx : index) (va : vaddr) : SAM unit :=
  let vir_entry := {| pd := false ; va := va |} in
  modify (fun s => {|
    currentPartition := s.(currentPartition);
    memory := add paddr idx (VE vir_entry) (memory s) beqPage beqIndex
  |}).

  Definition writePhyEntry (paddr : page) (idx : index) (pa : page) (p u r w e : bool) :=
  let phy_entry := {| read := r; write := w ; exec := e; present := p ; user := u ; pa := pa |} in
  modify (fun s => {|
    currentPartition := (currentPartition s) ;
    memory := add paddr idx (PE phy_entry) (memory s) beqPage beqIndex
  |}).

  Definition defaultPage := CPage 0.

  Definition mapKernel (paddr : page) (idx : index) :=
  let kernel_entry := {| read := false;
                         write := false;
                         exec := false;
                         present := false;
                         user := false;
                         pa := defaultPage
                      |} in
  modify (fun s =>
  {|
    currentPartition := (currentPartition s) ;
    memory := add paddr idx (PE kernel_entry) (memory s) beqPage beqIndex
  |}).

  Definition readAccessible (p : page) (idx : index) : SAM bool :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (PE phy_entry) => ret (user phy_entry)
  | Some _              => undefined "Error : expected to find a physical entry, but found another type"
  | None                => undefined "Error : no value at this address"
  end.

  Definition writeAccessible (p : page) (idx : index) (flag : bool) : SAM unit:=
  perform s := get in
  let entry :=  lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (PE phy_entry) =>
    let newEntry :=
      {|
        read    := (read    phy_entry);
        write   := (write   phy_entry);
        exec    := (exec    phy_entry);
        present := (present phy_entry);
        user    := flag;
        pa      := (pa      phy_entry)
      |} in
    modify (fun s =>
      {|
        currentPartition := (currentPartition s);
        memory := add p idx (PE newEntry) (memory s) beqPage beqIndex
      |})
  | Some _ => undefined "Error : expected to find a physical entry, but found another type"
  | None   => undefined "Error : no value at this address"
  end.

  Definition readPresent (p : page) (idx : index) : SAM bool :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (PE phy_entry) => ret (present phy_entry)
  | Some _              => undefined "Error : expected to find a physical entry, but found another type"
  | None                => undefined "Error : no value at this address"
  end.

  Definition writePresent (p : page) (idx : index) (flag : bool) : SAM unit:=
  perform s := get in
  let entry :=  lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (PE phy_entry) =>
    let newEntry :=
      {|
        read    := (read  phy_entry);
        write   := (write phy_entry);
        exec    := (exec  phy_entry);
        present := flag             ;
        user    := (user  phy_entry);
        pa      := (pa    phy_entry)
      |} in
    modify (fun s =>
      {|
        currentPartition := (currentPartition s);
        memory := add p idx (PE newEntry) (memory s) beqPage beqIndex
      |})
  | Some _ => undefined "Error : expected to find a physical entry, but found another type"
  | None   => undefined "Error : no value at this address"
  end.

  Definition readPDflag (p : page) (idx : index) : SAM bool :=
  perform s := get in
  let entry :=  lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (VE vir_entry) => ret (pd vir_entry)
  | Some _              => undefined "Error : expected to find a virtual entry, but found another type"
  | None                => undefined "Error : no value at this address"
  end.

  Definition writePDflag (p : page) (idx : index) (flag : bool) : SAM unit :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (VE vir_entry) =>
    let updated_entry := {| pd := flag; va := (va vir_entry) |} in
    modify (fun s => {|
      currentPartition := (currentPartition s);
      memory := add p idx (VE updated_entry) (memory s) beqPage beqIndex
    |})
  | Some _ => undefined "Error : expected to find a virtual entry, but found another type"
  | None   => undefined "Error : no value at this address"
  end.

  Definition readIndex (p : page) (idx : index) : SAM index :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (I i)  => ret i
  | Some (VA _) => undefined "Error : expected to find an index, but found a virtual address"
  | Some _      => undefined "Error : expected to find an index, but found another type"
  | None        => undefined "Error : no value at this address"
  end.

  Definition writeIndex (p : page) (idx : index) (idx_to_write : index) : SAM unit :=
  perform s := get in
  modify (fun s => {|
    currentPartition := (currentPartition s);
    memory := add p idx (I idx_to_write) (memory s) beqPage beqIndex
  |}).

  Program Definition getMaxIndex : SAM index:=
  if gt_dec tableSize 0
  then
    ret (Build_index_s (tableSize - 1) _)
  else undefined "Error : tableSize is negative, can not build maxIndex".

  Definition checkRights (r w e : bool) :=
  if (r && w && e)
  then
    ret true
  else ret (true || w).


  Definition tableSizeLowerBound := 14.
  Axiom tableSizeBigEnough : tableSize > tableSizeLowerBound.
  Program Definition maxFreeLL : SAM index := 
  ret (Build_index_s ((Coq.Init.Nat.div2 tableSize) - 2) _).
  Next Obligation.
  lia.
  Qed.
  Next Obligation.
  assert(Init.Nat.div2 tableSize < tableSize).
  apply Nat.lt_div2.
  assert(tableSize > tableSizeLowerBound) by apply tableSizeBigEnough.
  unfold tableSizeLowerBound in H.
  lia.
  lia.
  Qed.

  Definition defaultIndex := CIndex 0.

  Definition getIndexOfAddr (va : vaddr) (l : level) : SAM index :=
    ret ( nth ((length va) - (l + 2)) va defaultIndex ).

  Program Definition getNbLevel : SAM level:=
  if gt_dec nbLevel 0
  then
    ret (Build_level_s (nbLevel -1) _ )
  else
    undefined "Error : nbLevel is negative, can not return a neagative number".
  Next Obligation.
  lia.
  Qed.

  Definition prepareType (val1 : bool) (val2 : vaddr) : SAM boolvaddr :=
  ret (Build_boolvaddr_s val1 val2).

  Definition PDidx := CIndex 2.   (* page directory *)
  Definition getPDidx : SAM index := ret PDidx.

  Program Definition index_succ (n : index) : SAM index :=
  let isucc := n+1 in
  if (lt_dec isucc tableSize )
  then
    ret (Build_index_s isucc _ )
  else  undefined "Error : provided index is bigger than the maximum expected index".

  Definition getPd partition : SAM page :=
  perform idxPD := getPDidx in
  perform idx := index_succ idxPD in
  readPhysical partition idx.

  Definition defaultVAddr := CVaddr (repeat (CIndex 0) (nbLevel+1)).

  Definition readVirtualUser (p : page) (idx : index) : SAM vaddr :=
  perform s := get in
  let entry :=  lookup p idx (memory s) beqPage beqIndex  in
  match entry with
  | Some (VA vaddr) => ret vaddr
  | Some _      => ret defaultVAddr
  | None        => ret defaultVAddr
  end.

  Definition level_eqb (a b : level) : SAM bool := ret (a =? b).
  Definition fstLevel :=  CLevel 0.

  Definition page_eqb (p1 : page) (p2 : page) : SAM bool := ret (p1 =? p2).

  Definition comparePageToNull (p : page) : SAM bool :=
  perform nullPaddr := ret defaultPage in
  page_eqb nullPaddr p.

  Program Definition level_pred (n : level) : SAM level :=
  if gt_dec n 0
  then
  let ipred := n-1 in
  ret (Build_level_s ipred _ )
  else undefined "Error : level is less than zero, cannot get the preceding level".
  Next Obligation.
  destruct n; cbn; lia.
  Qed.

  (** The 'getTableAddrAux' returns the reference to the last page table  *)
  Fixpoint translateAux timeout (pd : page) (va : vaddr) (l : level) :=
  match timeout with
  | 0          => ret defaultPage
  | S timeout1 =>
    perform isFstLevel := level_eqb l fstLevel in
    if isFstLevel
    then ret pd
    else
      perform idx := getIndexOfAddr va l in
      perform addr := readPhyEntry pd idx in
      perform isNull := comparePageToNull addr in
      if isNull
      then ret defaultPage
      else
        perform p := level_pred l in
        translateAux timeout1 addr va p
  end.

  (** The 'translate' *)
  Definition  translate (pd : page) (va : vaddr) (l : level) : SAM (option page)  :=
  perform lastTable := translateAux nbLevel pd va l in 
  perform isNull := comparePageToNull lastTable in
  if isNull then ret None else
  perform idx :=  getIndexOfAddr va fstLevel in
  perform ispresent := readPresent lastTable idx in 
  perform isaccessible := readAccessible lastTable idx in
  if (ispresent && isaccessible) then  
  perform phypage := readPhyEntry lastTable idx in 
  ret (Some phypage)
  else ret None.


  Definition fetchVirtual (va : vaddr) (idx : index) : SAM vaddr :=
  perform currentPartition := getCurPartition in
  perform currentPD := getPd currentPartition in
  perform nbL := getNbLevel in
  perform optionphyPage := translate currentPD va nbL in
  match optionphyPage with 
  | None         => ret defaultVAddr
  | Some phyPage => readVirtualUser phyPage idx
  end.

  Definition storeVirtual (va : vaddr) (idx : index) (vaToStore : vaddr) : SAM unit:=
  perform currentPartition := getCurPartition in
  perform currentPD := getPd currentPartition in
  perform nbL := getNbLevel in
  perform optionphyPage := translate currentPD va nbL in
  match optionphyPage with
  | None => ret tt
  | Some phyPage => writeVirtual phyPage idx vaToStore
  end.

  Definition setInterruptMask (mask : interruptMask) : SAM unit :=
  ret tt.

  Definition getInterruptMaskFromCtx (context : contextAddr) : SAM interruptMask :=
  ret int_mask_d.

  Definition noInterruptRequest (flags : interruptMask) : SAM bool :=
  ret true.

  Definition updateMMURoot(pageDir : page) : SAM unit :=
  ret tt.

  Definition multiplexer := CPage 1.
  Definition getMultiplexer : SAM page :=
  ret multiplexer.

  Definition loadContext (contextToLoad : contextAddr) (enforce_interrupt : bool) : SAM unit :=
  ret tt.

End IsolationInterface.
