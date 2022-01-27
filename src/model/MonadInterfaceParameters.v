From Pip.Model Require Import CoreTypes.
From Pip.Model Require Import StateParameter.
From Pip.Model Require Import StateParameterizedMonadType.

Module Type MonadInterfaceParameters (Export StateType : StateParameter).

  Module SPMT := StateParameterizedMonadType StateType.
  Export SPMT.
  (* Monad Interface *)
  Parameter getCurPartition : SPM page.
(*   Parameter PF_getCurPartition : state -> (page * state).
  Axiom WP_getCurPartition : forall (P : page -> state -> Prop),
    {{ fun (s : state) =>
       let (r, s') := PF_getCurPartition s in
         P r s'
    }}
      getCurPartition
    {{ P }}. *)

  Parameter updateCurPartition : page -> SPM unit.
(*   Parameter PF_updateCurPartition : page -> state -> (unit * state).
  Axiom WP_updateCurPartition : forall (P : unit -> state -> Prop),
    forall (p : page),
    {{ fun (s : state) =>
       let (r, s') := (PF_updateCurPartition p s) in
         P r s'
    }}
      updateCurPartition p
    {{ P }}. *)

  Parameter readVirtual    : page -> index -> SPM vaddr.
(*   Parameter PF_readVirtual : page -> index -> state -> (vaddr * state).
  Axiom WP_readVirtual : forall (P : vaddr -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readVirtual p idx s) in
         P r s'
    }}
      readVirtual p idx
    {{ P }}. *)

  Parameter readPhysical    : page -> index -> SPM page.
(*   Parameter PF_readPhysical : page -> index -> state -> (page * state).
  Axiom WP_readPhysical : forall (P : page -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readPhysical p idx s) in
         P r s'
    }}
      readPhysical p idx
    {{ P }}. *)

  Parameter readVirEntry    : page -> index -> SPM vaddr.
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
  Parameter readPhyEntry    : page -> index -> SPM page.
(*   Parameter PF_readPhyEntry : page -> index -> state -> (page * state).
  Axiom WP_readPhyEntry : forall (P : page -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readPhyEntry p idx s) in
         P r s'
    }}
      readPhyEntry p idx
    {{ P }}. *)

  Parameter writeVirtual    : page -> index -> vaddr -> SPM unit.
(*   Parameter PF_writeVirtual : page -> index -> vaddr -> state -> (unit * state).
  Axiom WP_writeVirtual : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index), forall (va : vaddr),
    {{ fun (s : state) =>
       let (r, s') := (PF_writeVirtual p idx va s) in
         P r s'
    }}
      writeVirtual p idx va
    {{ P }}. *)

  Parameter writePhysical    : page -> index -> page -> SPM unit.
(*   Parameter PF_writePhysical : page -> index -> page -> state -> (unit * state).
  Axiom WP_writePhysical : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index), forall (paddr : page),
    {{ fun (s : state) =>
       let (r, s') := (PF_writePhysical p idx paddr s) in
         P r s'
    }}
      writePhysical p idx paddr
    {{ P }}. *)

  Parameter writeVirEntry    : page -> index -> vaddr -> SPM unit.
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
  Parameter writePhyEntry    : page -> index -> page -> bool -> bool -> bool -> bool -> bool -> SPM unit.
(*   Parameter PF_writePhyEntry : page -> index -> page -> bool -> bool -> bool -> bool -> bool -> state -> (unit * state).
  Axiom WP_writePhyEntry : forall (P : unit -> state -> Prop),
    forall (pa : page), forall (idx : index), forall (pe : page), forall (p u r w e : bool),
    {{ fun (s : state) =>
       let (r, s') := (PF_writePhyEntry pa idx pe p u r w e s) in
         P r s'
    }}
      writePhyEntry pa idx pe p u r w e
    {{ P }}. *)

  Parameter mapKernel    : page -> index -> SPM unit.
(*   Parameter PF_mapKernel : page -> index -> state -> (unit * state).
  Axiom WP_mapKernel : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_mapKernel p idx s) in
         P r s'
    }}
      mapKernel p idx
    {{ P }}. *)

  Parameter readAccessible    : page -> index -> SPM bool.
(*   Parameter PF_readAccessible : page -> index -> state -> (bool * state).
  Axiom WP_readAccessible : forall (P : bool -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readAccessible p idx s) in
         P r s'
    }}
      readAccessible p idx
    {{ P }}. *)

  Parameter writeAccessible    : page -> index -> bool -> SPM unit.
(*   Parameter PF_writeAccessible : page -> index -> bool -> state -> (unit * state).
  Axiom WP_writeAccessible : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index), forall (b : bool),
    {{ fun (s : state) =>
       let (r, s') := (PF_writeAccessible p idx b s) in
         P r s'
    }}
      writeAccessible p idx b
    {{ P }}. *)

  Parameter readPresent    : page -> index -> SPM bool.
(*   Parameter PF_readPresent : page -> index -> state -> (bool * state).
  Axiom WP_readPresent : forall (P : bool -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readPresent p idx s) in
         P r s'
    }}
      readPresent p idx
    {{ P }}. *)

  Parameter writePresent    : page -> index -> bool -> SPM unit.
(*   Parameter PF_writePresent : page -> index -> bool -> state -> (unit * state).
  Axiom WP_writePresent : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index), forall (b : bool),
    {{ fun (s : state) =>
       let (r, s') := (PF_writePresent p idx b s) in
         P r s'
    }}
      writePresent p idx b
    {{ P }}. *)

  Parameter readPDflag    : page -> index -> SPM bool.
(*   Parameter PF_readPDflag : page -> index -> state -> (bool * state).
  Axiom WP_readPDflag : forall (P : bool -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readPDflag p idx s) in
         P r s'
    }}
      readPDflag p idx
    {{ P }}. *)

  Parameter writePDflag    : page -> index -> bool -> SPM unit.
(*   Parameter PF_writePDflag : page -> index -> bool -> state -> (unit * state).
  Axiom WP_writePDflag : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index), forall (b : bool),
    {{ fun (s : state) =>
       let (r, s') := (PF_writePDflag p idx b s) in
         P r s'
    }}
      writePDflag p idx b
    {{ P }}. *)

  Parameter readIndex    : page -> index -> SPM index.
(*   Parameter PF_readIndex : page -> index -> state -> (index * state).
  Axiom WP_readIndex : forall (P : index -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readIndex p idx s) in
         P r s'
    }}
      readIndex p idx
    {{ P }}. *)

  Parameter writeIndex    : page -> index -> index -> SPM unit.
(*   Parameter PF_writeIndex : page -> index -> index -> state -> (unit * state).
  Axiom WP_writeIndex : forall (P : unit -> state -> Prop),
    forall (p : page), forall (idx : index), forall (idx_w : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_writeIndex p idx idx_w s) in
         P r s'
    }}
      writeIndex p idx idx_w
    {{ P }}. *)

  Parameter getMaxIndex    : SPM index.
(*   Parameter PF_getMaxIndex : state -> (index * state).
  Axiom WP_getMaxIndex : forall (P : index -> state -> Prop),
    {{ fun (s : state) =>
       let (r, s') := (PF_getMaxIndex s) in
         P r s'
    }}
      getMaxIndex
    {{ P }}. *)

  Parameter checkRights    : bool -> bool -> bool -> SPM bool.
(*   Parameter PF_checkRights : bool -> bool -> bool -> state -> (bool * state).
  Axiom WP_checkRights : forall (P : bool -> state -> Prop),
    forall (r w e : bool),
    {{ fun (s : state) =>
       let (r, s') := (PF_checkRights r w e s) in
         P r s'
    }}
      checkRights r w e
    {{ P }}. *)

  Parameter maxFreeLL    : SPM index.
(*   Parameter PF_maxFreeLL : state -> (index * state).
  Axiom WP_maxFreeLL : forall (P : index -> state -> Prop),
    {{ fun (s : state) =>
       let (r, s') := (PF_maxFreeLL s) in
         P r s'
    }}
      maxFreeLL
    {{ P }}. *)

  Parameter getIndexOfAddr    : vaddr -> level -> SPM index.
(*   Parameter PF_getIndexOfAddr : vaddr -> level -> state -> (index * state).
  Axiom WP_getIndexOfAddr : forall (P : index -> state -> Prop),
    forall (va : vaddr), forall (l : level),
    {{ fun (s : state) =>
       let (r, s') := (PF_getIndexOfAddr va l s) in
         P r s'
    }}
      getIndexOfAddr va l
    {{ P }}. *)

  Parameter getNbLevel    : SPM level.
(*   Parameter PF_getNbLevel : state -> (level * state).
  Axiom WP_getNbLevel : forall (P : level -> state -> Prop),
    {{ fun (s : state) =>
       let (r, s') := (PF_getNbLevel s) in
         P r s'
    }}
      getNbLevel
    {{ P }}. *)

  Parameter prepareType    : bool -> vaddr -> SPM boolvaddr.
(*   Parameter PF_prepareType : bool -> vaddr -> state -> (boolvaddr * state).
  Axiom WP_prepareType : forall (P : boolvaddr -> state -> Prop),
    forall (b : bool), forall (va : vaddr),
    {{ fun (s : state) =>
       let (r, s') := (PF_prepareType b va s) in
         P r s'
    }}
      prepareType b va
    {{ P }}. *)

  Parameter getPd    : page -> SPM page.
(*   Parameter PF_getPd : page -> state -> (page * state).
  Axiom WP_getPd : forall (P : page -> state -> Prop),
    forall (p : page),
    {{ fun (s : state) =>
       let (r, s') := (PF_getPd p s) in
         P r s'
    }}
      getPd p
    {{ P }}. *)

  Parameter readVirtualUser    : page -> index -> SPM vaddr.
(*   Parameter PF_readVirtualUser : page -> index -> state -> (vaddr * state).
  Axiom WP_readVirtualUser : forall (P : vaddr -> state -> Prop),
    forall (p : page), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_readVirtualUser p idx s) in
         P r s'
    }}
      readVirtualUser p idx
    {{ P }}. *)

  Parameter fetchVirtual    : vaddr -> index -> SPM vaddr.
(*   Parameter PF_fetchVirtual : vaddr -> index -> state -> (vaddr * state).
  Axiom WP_fetchVirtual : forall (P : vaddr -> state -> Prop),
    forall (va : vaddr), forall (idx : index),
    {{ fun (s : state) =>
       let (r, s') := (PF_fetchVirtual va idx s) in
         P r s'
    }}
      fetchVirtual va idx
    {{ P }}. *)

  Parameter storeVirtual    : vaddr -> index -> vaddr -> SPM unit.
(*   Parameter PF_storeVirtual : vaddr -> index -> vaddr -> state -> (unit * state).
  Axiom WP_storeVirtual : forall (P : unit -> state -> Prop),
    forall (va : vaddr), forall (idx : index), forall (va_w : vaddr),
    {{ fun (s : state) =>
       let (r, s') := (PF_storeVirtual va idx va_w s) in
         P r s'
    }}
      storeVirtual va idx va_w
    {{ P }}. *)

  Parameter setInterruptMask    : interruptMask -> SPM unit.
(*   Parameter PF_setInterruptMask : interruptMask -> state -> (unit * state).
  Axiom WP_setInterruptMask : forall (P : unit -> state -> Prop),
    forall (intmask : interruptMask),
    {{ fun (s : state) =>
       let (r, s') := (PF_setInterruptMask intmask s) in
         P r s'
    }}
      setInterruptMask intmask
    {{ P }}. *)

  Parameter getInterruptMaskFromCtx    : contextAddr -> SPM interruptMask.
(*   Parameter PF_getInterruptMaskFromCtx : contextAddr -> state -> (interruptMask * state).
  Axiom WP_getInterruptMaskFromCtx : forall (P : interruptMask -> state -> Prop),
    forall (ctx_addr : contextAddr),
    {{ fun (s : state) =>
       let (r, s') := (PF_getInterruptMaskFromCtx ctx_addr s) in
         P r s'
    }}
      getInterruptMaskFromCtx ctx_addr
    {{ P }}. *)

  Parameter noInterruptRequest : interruptMask -> SPM bool.
(*   Parameter PF_noInterruptRequest : interruptMask -> state -> (bool * state).
  Axiom WP_noInterruptRequest : forall (P : bool -> state -> Prop),
    forall (intmask : interruptMask),
    {{ fun (s : state) =>
       let (r, s') := (PF_noInterruptRequest intmask s) in
         P r s'
    }}
      noInterruptRequest intmask
    {{ P }}. *)

  Parameter updateMMURoot    : page -> SPM unit.
(*   Parameter PF_updateMMURoot : page -> state -> (unit * state).
  Axiom WP_updateMMURoot : forall (P : unit -> state -> Prop),
    forall (mmuroot : page),
    {{ fun (s : state) =>
       let (r, s') := (PF_updateMMURoot mmuroot s) in
         P r s'
    }}
      updateMMURoot mmuroot
    {{ P }}. *)

  Parameter getMultiplexer    : SPM page.
(*   Parameter PF_getMultiplexer : state -> (page * state).
  Axiom WP_getMultiplexer : forall (P : page -> state -> Prop),
    {{ fun (s : state) =>
       let (r, s') := (PF_getMultiplexer s) in
         P r s'
    }}
      getMultiplexer
    {{ P }}. *)

  Parameter page_eqb    : page -> page -> SPM bool.
(*   Parameter PF_page_eqb : page -> page -> state -> (bool * state).
  Axiom WP_page_eqb : forall (P : bool -> state -> Prop),
    forall (p1 : page), forall (p2 : page),
    {{ fun (s : state) =>
       let (r, s') := (PF_page_eqb p1 p2 s) in
         P r s'
    }}
      page_eqb p1 p2
    {{ P }}. *)

  Parameter loadContext    : contextAddr -> bool -> SPM unit.
(*   Parameter PF_loadContext : contextAddr -> bool -> state -> (unit * state).
  Axiom WP_loadContext : forall (P : unit -> state -> Prop),
    forall (ctx : contextAddr), forall (cli : bool),
    {{ fun (s : state) =>
       let (r, s') := (PF_loadContext ctx cli s) in
         P r s'
    }}
      loadContext ctx cli
    {{ P }}. *)

End MonadInterfaceParameters.