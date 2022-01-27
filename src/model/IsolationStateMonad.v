Require Import Coq.Strings.String Lia NPeano.

From Pip.Model Require Import CoreTypes MonadInterfaceParameters StateParameter StateParameterizedMonadType.
Require Import Arith Bool List.
Import List.ListNotations.


Module IsolationState <: StateParameter.

  Record Pentry : Type:=
  {
    read    : bool;
    write   : bool;
    exec    : bool;
    present : bool;
    user    : bool;
    pa      : page
  }.

  Record Ventry : Type:=
  {
    pd : bool;
    va : vaddr
  }.

  Inductive value : Type := 
  |PE : Pentry -> value
  |VE : Ventry -> value
  |PP : page -> value
  |VA : vaddr -> value
  |I  : index -> value
  |U  : userValue -> value.

  Record IsolationState : Type := {
    currentPartition : page;
    memory : list (paddr * value)
  }.

  Definition state := IsolationState.

End IsolationState.

Module IsolationStateMonad <: MonadInterfaceParameters IsolationState.

  Module SPMT := StateParameterizedMonadType IsolationState.
  Export SPMT.

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

(*  Ltac solve_wp :=
    intros ;
    match goal with
    | |- {{ fun s : state => let (_, _) := ?F ?a s in _ }} ?M ?a {{ _ }}
      => unfold F; unfold M
    | |- {{ fun s : state => let (_, _) := ?F    s in _ }} ?M    {{ _ }}
      => unfold F; unfold M
    end ;
    unfold hoareTriple ;
    cbn ;
    trivial. *)

  Definition getCurPartition : SPM page :=
    perform s := get in ret (currentPartition s).
(*   Definition PF_getCurPartition : state -> (page * state) :=
    fun s => (currentPartition s, s).
  Lemma WP_getCurPartition : forall (P : page -> state -> Prop),
    {{ fun (s : state) =>
       let (r, s') := PF_getCurPartition s in
         P r s'
    }}
      getCurPartition
    {{ P }}.
  Proof.
  solve_wp.
  Qed. *)

  Definition updateCurPartition (p : page) : SPM unit :=
    modify (fun s => {| currentPartition := p; memory := s.(memory) |}).
(*   Definition PF_updateCurPartition (p : page) : state -> (unit * state) :=
    fun s => (tt, {| currentPartition := p; memory := memory s |}).
  Lemma WP_updateCurPartition : forall (P : unit -> state -> Prop),
    forall (p : page),
    {{ fun (s : state) =>
       let (r, s') := (PF_updateCurPartition p s) in
         P r s'
    }}
      updateCurPartition p
    {{ P }}.
  Proof.
  solve_wp.
  Qed. *)

  Definition readVirtual (p : page) (idx : index) : SPM vaddr :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (VA a) => ret a
  | Some _      => undefined "Error : expected to find a virtual address, but found another type"
  | None        => undefined "Error : no value at this address"
  end.
(*   Definition PF_readVirtual (p : page) (idx : index) := state -> (vaddr * state).
    fun s => exists (entry : vaddr),
             lookup table idx s.(memory) beqPage beqIndex = Some (VA entry)
          /\  s }}
             readVirtual table idx {{P}}.
  Lemma WP_readVirtual : forall (P : vaddr -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readVirtual p idx s) in
         P r s'
    }}
      readVirtual p idx
    {{ P }}.
  Proof.
  solve_wp.
  Qed.
*)
  Definition readPhysical (p : page) (idx : index) : SPM page :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (PP page) => ret page
  | Some _      => undefined "Error : expected to find a physical page, but found another type"
  | None        => undefined "Error : no value at this address"
  end.

  Definition readVirEntry (p : page) (idx : index) : SPM vaddr :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (VE vir_entry) => ret (va vir_entry)
  | Some _      => undefined "Error : expected to find a virtual entry, but found another type"
  | None        => undefined "Error : no value at this address"
  end.
(*   Parameter PF_readVirEntry : page -> index -> state -> (vaddr * state).
  Axiom WP_readVirEntry : forall (P : vaddr -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readVirEntry p idx s) in
         P r s'
    }}
      readVirEntry p idx
    {{ P }}.
*)

  Definition readPhyEntry (p : page) (idx : index) : SPM page :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (PE phy_entry) => ret (pa phy_entry)
  | Some _      => undefined "Error : expected to find a physical entry, but found another type"
  | None        => undefined "Error : no value at this address"
  end.
(*   Parameter PF_readPhyEntry : page -> index -> state -> (page * state).
  Axiom WP_readPhyEntry : forall (P : page -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readPhyEntry p idx s) in
         P r s'
    }}
      readPhyEntry p idx
    {{ P }}. *)
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

  Definition writeVirtual (paddr : page) (idx : index) (va : vaddr) : SPM unit :=
  modify (fun s => {|
    currentPartition := s.(currentPartition);
    memory := add paddr idx (VA va) (memory s) beqPage beqIndex
  |}).
(*   Parameter PF_writeVirtual : page -> index -> vaddr -> state -> (unit * state).
  Axiom WP_writeVirtual : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index), forall (va : vaddr),
    {{ fun (s : state) =>
       let (r, s') := (PF_writeVirtual p idx va s) in
         P r s'
    }}
      writeVirtual p idx va
    {{ P }}. *)

  Definition writePhysical (paddr : page) (idx : index) (p : page) : SPM unit :=
  modify (fun s => {|
    currentPartition := s.(currentPartition);
    memory := add paddr idx (PP p) (memory s) beqPage beqIndex
  |}).
(*   Parameter PF_writePhysical : page -> index -> page -> state -> (unit * state).
  Axiom WP_writePhysical : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index), forall (paddr : page),
    {{ fun (s : state) =>
       let (r, s') := (PF_writePhysical p idx paddr s) in
         P r s'
    }}
      writePhysical p idx paddr
    {{ P }}. *)

  Definition writeVirEntry (paddr : page) (idx : index) (va : vaddr) : SPM unit :=
  let vir_entry := {| pd := false ; va := va |} in
  modify (fun s => {|
    currentPartition := s.(currentPartition);
    memory := add paddr idx (VE vir_entry) (memory s) beqPage beqIndex
  |}).
(*   Parameter PF_writeVirEntry : page -> index -> vaddr -> state -> (unit * state).
  Axiom WP_writeVirEntry : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index), forall (ve : vaddr),
    {{ fun (s : state) =>
       let (r, s') := (PF_writeVirEntry p idx ve s) in
         P r s'
    }}
      writeVirEntry p idx ve
    {{ P }}.
 *)
  Definition writePhyEntry (paddr : page) (idx : index) (pa : page) (p u r w e : bool) :=
  let phy_entry := {| read := r; write := w ; exec := e; present := p ; user := u ; pa := pa |} in
  modify (fun s => {|
    currentPartition := (currentPartition s) ;
    memory := add paddr idx (PE phy_entry) (memory s) beqPage beqIndex
  |}).
(*   Parameter PF_writePhyEntry : page -> index -> page -> bool -> bool -> bool -> bool -> bool -> state -> (unit * state).
  Axiom WP_writePhyEntry : forall (P : unit -> state -> Prop),
    forall (pa : page), forall (idx : index), forall (pe : page), forall (p u r w e : bool),
    {{ fun (s : state) =>
       let (r, s') := (PF_writePhyEntry pa idx pe p u r w e s) in
         P r s'
    }}
      writePhyEntry pa idx pe p u r w e
    {{ P }}. *)
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
(*   Parameter PF_mapKernel : page -> index -> state -> (unit * state).
  Axiom WP_mapKernel : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_mapKernel p idx s) in
         P r s'
    }}
      mapKernel p idx
    {{ P }}. *)

  Definition readAccessible (p : page) (idx : index) : SPM bool :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (PE phy_entry) => ret (user phy_entry)
  | Some _              => undefined "Error : expected to find a physical entry, but found another type"
  | None                => undefined "Error : no value at this address"
  end.
(*   Parameter PF_readAccessible : page -> index -> state -> (bool * state).
  Axiom WP_readAccessible : forall (P : bool -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readAccessible p idx s) in
         P r s'
    }}
      readAccessible p idx
    {{ P }}. *)

  Definition writeAccessible (p : page) (idx : index) (flag : bool) : SPM unit:=
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
(*   Parameter PF_writeAccessible : page -> index -> bool -> state -> (unit * state).
  Axiom WP_writeAccessible : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index), forall (b : bool),
    {{ fun (s : state) =>
       let (r, s') := (PF_writeAccessible p idx b s) in
         P r s'
    }}
      writeAccessible p idx b
    {{ P }}. *)

  Definition readPresent (p : page) (idx : index) : SPM bool :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (PE phy_entry) => ret (present phy_entry)
  | Some _              => undefined "Error : expected to find a physical entry, but found another type"
  | None                => undefined "Error : no value at this address"
  end.
(*   Parameter PF_readPresent : page -> index -> state -> (bool * state).
  Axiom WP_readPresent : forall (P : bool -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readPresent p idx s) in
         P r s'
    }}
      readPresent p idx
    {{ P }}. *)

  Definition writePresent (p : page) (idx : index) (flag : bool) : SPM unit:=
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
(*   Parameter PF_writePresent : page -> index -> bool -> state -> (unit * state).
  Axiom WP_writePresent : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index), forall (b : bool),
    {{ fun (s : state) =>
       let (r, s') := (PF_writePresent p idx b s) in
         P r s'
    }}
      writePresent p idx b
    {{ P }}. *)

  Definition readPDflag (p : page) (idx : index) : SPM bool :=
  perform s := get in
  let entry :=  lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (VE vir_entry) => ret (pd vir_entry)
  | Some _              => undefined "Error : expected to find a virtual entry, but found another type"
  | None                => undefined "Error : no value at this address"
  end.
(*   Parameter PF_readPDflag : page -> index -> state -> (bool * state).
  Axiom WP_readPDflag : forall (P : bool -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readPDflag p idx s) in
         P r s'
    }}
      readPDflag p idx
    {{ P }}. *)

  Definition writePDflag (p : page) (idx : index) (flag : bool) : SPM unit :=
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
(*   Parameter PF_writePDflag : page -> index -> bool -> state -> (unit * state).
  Axiom WP_writePDflag : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index), forall (b : bool),
    {{ fun (s : state) =>
       let (r, s') := (PF_writePDflag p idx b s) in
         P r s'
    }}
      writePDflag p idx b
    {{ P }}. *)

  Definition readIndex (p : page) (idx : index) : SPM index :=
  perform s := get in
  let entry := lookup p idx (memory s) beqPage beqIndex in
  match entry with
  | Some (I i)  => ret i
  | Some (VA _) => undefined "Error : expected to find an index, but found a virtual address"
  | Some _      => undefined "Error : expected to find an index, but found another type"
  | None        => undefined "Error : no value at this address"
  end.
(*   Parameter PF_readIndex : page -> index -> state -> (index * state).
  Axiom WP_readIndex : forall (P : index -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readIndex p idx s) in
         P r s'
    }}
      readIndex p idx
    {{ P }}. *)

  Definition writeIndex (p : page) (idx : index) (idx_to_write : index) : SPM unit :=
  perform s := get in
  modify (fun s => {|
    currentPartition := (currentPartition s);
    memory := add p idx (I idx_to_write) (memory s) beqPage beqIndex
  |}).
(*   Parameter PF_writeIndex : page -> index -> index -> state -> (unit * state).
  Axiom WP_writeIndex : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index), forall (idx_w : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_writeIndex p idx idx_w s) in
         P r s'
    }}
      writeIndex p idx idx_w
    {{ P }}. *)

  Program Definition getMaxIndex : SPM index:=
  if gt_dec tableSize 0
  then
    ret (Build_index (tableSize - 1) _)
  else undefined "Error : tableSize is negative, can not build maxIndex".
(*   Parameter PF_getMaxIndex : state -> (index * state).
  Axiom WP_getMaxIndex : forall (P : index -> state -> Prop),
    {{ fun (s : state) =>
       let (r, s') := (PF_getMaxIndex s) in
         P r s'
    }}
      getMaxIndex
    {{ P }}. *)

  Definition checkRights (r w e : bool) :=
  if (r && w && e)
  then
    ret true
  else ret (true || w).
(*   Parameter PF_checkRights : bool -> bool -> bool -> state -> (bool * state).
  Axiom WP_checkRights : forall (P : bool -> state -> Prop),
    forall (r w e : bool),
    {{ fun (s : state) =>
       let (r, s') := (PF_checkRights r w e s) in
         P r s'
    }}
      checkRights r w e
    {{ P }}. *)
  Program Definition maxFreeLL : SPM index := 
  ret (Build_index ((Coq.Init.Nat.div2 tableSize) - 2) _).
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
(*   Parameter PF_maxFreeLL : state -> (index * state).
  Axiom WP_maxFreeLL : forall (P : index -> state -> Prop),
    {{ fun (s : state) =>
       let (r, s') := (PF_maxFreeLL s) in
         P r s'
    }}
      maxFreeLL
    {{ P }}. *)

  Definition defaultIndex := CIndex 0.

  Definition getIndexOfAddr (va : vaddr) (l : level) : SPM index :=
    ret ( nth ((length va) - (l + 2)) va defaultIndex ).
(*   Parameter PF_getIndexOfAddr : vaddr -> level -> state -> (index * state).
  Axiom WP_getIndexOfAddr : forall (P : index -> state -> Prop),
    forall (va : vaddr), forall (l : level),
    {{ fun (s : state) =>
       let (r, s') := (PF_getIndexOfAddr va l s) in
         P r s'
    }}
      getIndexOfAddr va l
    {{ P }}. *)
  Program Definition getNbLevel : SPM level:=
  if gt_dec nbLevel 0
  then
    ret (Build_level (nbLevel -1) _ )
  else
    undefined "Error : nbLevel is negative, can not return a neagative number".
  (* BEGIN NOT SIMULATION *)
  Next Obligation.
  lia.
  Qed.
(*   Parameter PF_getNbLevel : state -> (level * state).
  Axiom WP_getNbLevel : forall (P : level -> state -> Prop),
    {{ fun (s : state) =>
       let (r, s') := (PF_getNbLevel s) in
         P r s'
    }}
      getNbLevel
    {{ P }}. *)

  Definition prepareType (val1 : bool) (val2 : vaddr) : SPM boolvaddr :=
  ret (Build_boolvaddr val1 val2).
(*   Parameter PF_prepareType : bool -> vaddr -> state -> (boolvaddr * state).
  Axiom WP_prepareType : forall (P : boolvaddr -> state -> Prop),
    forall (b : bool), forall (va : vaddr),
    {{ fun (s : state) =>
       let (r, s') := (PF_prepareType b va s) in
         P r s'
    }}
      prepareType b va
    {{ P }}. *)

  Definition PDidx := CIndex 2.   (* page directory *)
  Definition getPDidx : SPM index := ret PDidx.

  Program Definition index_succ (n : index) : SPM index :=
  let isucc := n+1 in
  if (lt_dec isucc tableSize )
  then
    ret (Build_index isucc _ )
  else  undefined "Error : provided index is bigger than the maximum expected index".

  Definition getPd partition : SPM page :=
  perform idxPD := getPDidx in
  perform idx := index_succ idxPD in
  readPhysical partition idx.
(*   Parameter PF_getPd : page -> state -> (page * state).
  Axiom WP_getPd : forall (P : page -> state -> Prop),
    forall (p : page),
    {{ fun (s : state) =>
       let (r, s') := (PF_getPd p s) in
         P r s'
    }}
      getPd p
    {{ P }}. *)


  Definition defaultVAddr := CVaddr (repeat (CIndex 0) (nbLevel+1)).

  Definition readVirtualUser (p : page) (idx : index) : SPM vaddr :=
  perform s := get in
  let entry :=  lookup p idx (memory s) beqPage beqIndex  in
  match entry with
  | Some (VA vaddr) => ret vaddr
  | Some _      => ret defaultVAddr
  | None        => ret defaultVAddr
  end.
(*   Parameter PF_readVirtualUser : page -> index -> state -> (vaddr * state).
  Axiom WP_readVirtualUser : forall (P : vaddr -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readVirtualUser p idx s) in
         P r s'
    }}
      readVirtualUser p idx
    {{ P }}. *)

  Definition level_eqb (a b : level) : SPM bool := ret (a =? b).
  Definition fstLevel :=  CLevel 0.

  Definition page_eqb (p1 : page) (p2 : page) : SPM bool := ret (p1 =? p2).
(*   Parameter PF_page_eqb : page -> page -> state -> (bool * state).
  Axiom WP_page_eqb : forall (P : bool -> state -> Prop),
    forall (p1 : page), forall (p2 : page),
    {{ fun (s : state) =>
       let (r, s') := (PF_page_eqb p1 p2 s) in
         P r s'
    }}
      page_eqb p1 p2
    {{ P }}. *)


  Definition comparePageToNull (p : page) : SPM bool :=
  perform nullPaddr := ret defaultPage in
  page_eqb nullPaddr p.

  Program Definition level_pred (n : level) : SPM level :=
  if gt_dec n 0
  then
  let ipred := n-1 in
  ret (Build_level ipred _ )
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
  Definition  translate (pd : page) (va : vaddr) (l : level) : SPM (option page)  :=
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


  Definition fetchVirtual (va : vaddr) (idx : index) : SPM vaddr :=
  perform currentPartition := getCurPartition in
  perform currentPD := getPd currentPartition in
  perform nbL := getNbLevel in
  perform optionphyPage := translate currentPD va nbL in
  match optionphyPage with 
  | None         => ret defaultVAddr
  | Some phyPage => readVirtualUser phyPage idx
  end.
(*   Parameter PF_fetchVirtual : vaddr -> index -> state -> (vaddr * state).
  Axiom WP_fetchVirtual : forall (P : vaddr -> state -> Prop),
    forall (va : vaddr), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_fetchVirtual va idx s) in
         P r s'
    }}
      fetchVirtual va idx
    {{ P }}. *)

  Definition storeVirtual (va : vaddr) (idx : index) (vaToStore : vaddr) : SPM unit:=
  perform currentPartition := getCurPartition in
  perform currentPD := getPd currentPartition in
  perform nbL := getNbLevel in
  perform optionphyPage := translate currentPD va nbL in
  match optionphyPage with
  | None => ret tt
  | Some phyPage => writeVirtual phyPage idx vaToStore
  end.
(*   Parameter PF_storeVirtual : vaddr -> index -> vaddr -> state -> (unit * state).
  Axiom WP_storeVirtual : forall (P : unit -> state -> Prop),
    forall (va : vaddr), forall (idx : index), forall (va_w : vaddr),
    {{ fun (s : state) =>
       let (r, s') := (PF_storeVirtual va idx va_w s) in
         P r s'
    }}
      storeVirtual va idx va_w
    {{ P }}. *)

  Definition setInterruptMask (mask : interruptMask) : SPM unit :=
  ret tt.
  (*   Parameter PF_setInterruptMask : interruptMask -> state -> (unit * state).
  Axiom WP_setInterruptMask : forall (P : unit -> state -> Prop),
    forall (intmask : interruptMask),
    {{ fun (s : state) =>
       let (r, s') := (PF_setInterruptMask intmask s) in
         P r s'
    }}
      setInterruptMask intmask
    {{ P }}. *)

  Definition getInterruptMaskFromCtx (context : contextAddr) : SPM interruptMask :=
  ret int_mask_d.
(*   Parameter PF_getInterruptMaskFromCtx : contextAddr -> state -> (interruptMask * state).
  Axiom WP_getInterruptMaskFromCtx : forall (P : interruptMask -> state -> Prop),
    forall (ctx_addr : contextAddr),
    {{ fun (s : state) =>
       let (r, s') := (PF_getInterruptMaskFromCtx ctx_addr s) in
         P r s'
    }}
      getInterruptMaskFromCtx ctx_addr
    {{ P }}. *)

  Definition noInterruptRequest (flags : interruptMask) : SPM bool :=
  ret true.
(*   Parameter PF_noInterruptRequest : interruptMask -> state -> (bool * state).
  Axiom WP_noInterruptRequest : forall (P : bool -> state -> Prop),
    forall (intmask : interruptMask),
    {{ fun (s : state) =>
       let (r, s') := (PF_noInterruptRequest intmask s) in
         P r s'
    }}
      noInterruptRequest intmask
    {{ P }}. *)

  Definition updateMMURoot(pageDir : page) : SPM unit :=
  ret tt.
(*   Parameter PF_updateMMURoot : page -> state -> (unit * state).
  Axiom WP_updateMMURoot : forall (P : unit -> state -> Prop),
    forall (mmuroot : page),
    {{ fun (s : state) =>
       let (r, s') := (PF_updateMMURoot mmuroot s) in
         P r s'
    }}
      updateMMURoot mmuroot
    {{ P }}. *)

  Definition multiplexer := CPage 1.
  Definition getMultiplexer : SPM page :=
  ret multiplexer.
(*   Parameter PF_getMultiplexer : state -> (page * state).
  Axiom WP_getMultiplexer : forall (P : page -> state -> Prop),
    {{ fun (s : state) =>
       let (r, s') := (PF_getMultiplexer s) in
         P r s'
    }}
      getMultiplexer
    {{ P }}. *)

  Definition loadContext (contextToLoad : contextAddr) (enforce_interrupt : bool) : SPM unit :=
  ret tt.

End IsolationStateMonad.
