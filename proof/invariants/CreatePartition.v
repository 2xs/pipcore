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
    This file contains the invariant of [createPartition]. 
    We prove that this PIP service preserves the isolation property *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL Pip.Model.Lib.
Require Import Pip.Core.Services.

Require Import Pip.Proof.WeakestPreconditions Pip.Proof.StateLib Pip.Proof.InternalLemmas
               Pip.Proof.DependentTypeLemmas.

Require Import Isolation Consistency Invariants GetTableAddr WriteAccessible WritePhyEntry
               PropagatedProperties WriteAccessibleRec InitConfigPagesList InitPEntryTable
               UpdateMappedPageContent UpdatePartitionDescriptor PropagatedProperties
               UpdateShadow1Structure InitFstShadow InitSndShadow UpdatePDFlagTrue.

Require Import Lia Bool  Coq.Logic.ProofIrrelevance List EqNat Compare_dec.

Lemma andPreAndPost :
 forall (A : Type) (P: state -> Prop) 
 (Q1 Q2  :  state -> Prop) (m : LLI A),
{{fun s => P s /\ Q1 s}} m {{fun _ => Q1}} -> 
{{fun s => P s /\ Q2 s}} m {{fun _ =>  Q2}} -> 
{{fun s => P s /\ Q1 s /\ Q2 s}} m {{fun _ s =>  Q1 s /\ Q2 s}}.
Proof.
intros.
unfold hoareTriple in *.
intros.
assert( P s /\ Q1 s) by intuition.
apply H in H2.

assert( P s /\ Q2 s) by intuition.
apply H0 in H3.
destruct (m s); trivial.
destruct p.
split; trivial.
Qed.
Lemma levelDecOrNot : 
      forall p1 p2 : level, p1 <> p2 \/ p1 = p2. 
Proof.
destruct p1;simpl in *;subst;destruct p2;simpl in *;subst.
assert (Heq :l<>l0 \/ l = l0) by abstract lia.
destruct Heq as [Heq|Heq].

left. unfold not;intros.
inversion H.
subst.
now contradict Heq.
subst.
right;f_equal. apply proof_irrelevance.
Qed.

Lemma mapKernel  table idx (P : unit -> state -> Prop) :
{{fun  s => P tt {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE {| read := false; write := false; exec := false; present := false; user := false; pa := pageDefault |})
              (memory s) pageEq idxEq |} }} MAL.writePhyEntry table idx pageDefault false false false false false {{P}}.
Proof.
unfold mapKernel.
eapply weaken.
eapply modify.
intros. simpl.
assumption.
Qed.

Lemma createPartition (descChild pdChild shadow1 shadow2 list : vaddr) :
{{fun s => partitionsIsolation s  /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }} 
createPartition descChild pdChild shadow1 shadow2 list  
{{fun _ s  => partitionsIsolation s  /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold createPartition.
case_eq(vaddrEq vaddrDefault descChild);
intros HdescChildDefault.
eapply weaken.
eapply WP.ret.
simpl;intros;trivial.
eapply WP.bindRev.
eapply WP.weaken. 
(** getNbLevel **)
eapply Invariants.getNbLevel.
simpl. intros.
pattern s in H.
eapply H.
intros level.
(** Vaddrs Eq **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.checkVAddrsEqualityWOOffset.
simpl.
intros.
pattern s in H.
eapply H.
intros. 
repeat (eapply WP.bindRev; [ eapply WP.weaken ; 
              [ apply Invariants.checkVAddrsEqualityWOOffset | intros ; simpl; pattern s in H; eapply H ] 
                                | simpl; intros  ]).
case_eq (a || a0 || a1 || a2 || a3 || a4 || a5 || a6 || a7 || a8); intros Hvaddrs.
eapply WP.weaken.
eapply WP.ret.
intros.
simpl. intuition.
try repeat rewrite orb_false_iff in Hvaddrs.
try repeat rewrite and_assoc in Hvaddrs.
intuition.
subst.
(** Kernel map **)
eapply WP.bindRev.
eapply WP.weaken.   
eapply Invariants.checkKernelMap.
intros. simpl.
pattern s in H. eapply H. 
intro.
repeat (eapply WP.bindRev; [ eapply WP.weaken ; 
              [ apply Invariants.checkKernelMap | intros; simpl; pattern s in H; eapply H ]
                                | simpl; intro ]).
                                simpl.
 repeat (eapply WP.bindRev; [ eapply WP.weaken ; 
              [ apply Invariants.compareVAddrToNull | intros; simpl; pattern s in H; eapply H ]
                                | simpl; intro ]).
                                simpl.                               
case_eq ( negb a && negb a0 && negb a1 && negb a2 && negb a3 && negb a4 && negb a5 && negb a6 && negb a7).
intro Hkmap.
repeat rewrite andb_true_iff in Hkmap.
try repeat rewrite and_assoc in Hkmap.
repeat rewrite negb_true_iff in Hkmap. 
intuition.
subst.
eapply WP.bindRev. 
(** getCurPartition **)
      { eapply WP.weaken. 
        eapply Invariants.getCurPartition .
        cbn. 
        intros. 
        pattern s in H. 
        eapply H. }
      intro currentPart.   simpl.   
(** getPd **)  
      eapply WP.bindRev. 
        { eapply WP.weaken. 
          eapply Invariants.getPd.
          simpl.
          intros.
          split.
          (* try repeat rewrite and_assoc in H. *)
          pattern s in H. eapply H.
          unfold consistency in *.
          unfold partitionDescriptorEntry in *.
          unfold currentPartitionInPartitionsList in *.
          intuition          subst. trivial. 
          }
      intro currentPD. simpl. 
(* (** getNbLevel **)      
      eapply WP.bindRev.
      { eapply WP.weaken.
        eapply Invariants.getNbLevel.
        simpl.
        intros.
        try repeat rewrite and_assoc in H.
        pattern s in H.
        eapply H.
        }  intro level.  *)  
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      try repeat rewrite and_assoc in H.
      split.
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition . 
      instantiate (1:= currentPart). subst. assumption.
      instantiate (1:= idxPageDir).
      split. intuition.
      assert(consistency s /\
              Some level = StateLib.getNbLevel /\ 
              currentPart = currentPartition s /\ 
              nextEntryIsPP currentPart idxPageDir currentPD s) as (Hcons & Hlevel & Hcp & Hrootpd)
      by intuition.
      clear H.     (* 
      destruct H as ( _ & _ & _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ & 
      _ &_ & _ & _ & _ &_ &_ & _ &_ & _& _& Hcp & Hrootpd ). *)
      exists currentPD.
      split. assumption.
      split.
      unfold consistency in *.
      assert(partitionDescriptorEntry s /\ currentPartitionInPartitionsList s) as (Hpd &Hpr)
      by intuition. clear Hcons.
(*       destruct Hcons as (Hpd & _ & _ &_  & Hpr  & _).  *)
      unfold partitionDescriptorEntry in Hpd.
      unfold currentPartitionInPartitionsList in *.
      subst.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.     
      assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2\/ idxPageDir = idxShadow3 \/ idxPageDir = idxParentDesc  \/ idxPageDir = idxPartDesc ) as Htmp 
      by auto.
      generalize (Hpd idxPageDir Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ idxPageDir); [|now contradict Hrootpd];
      destruct (lookup (currentPartition s) i (memory s) pageEq idxEq); [|now contradict Hrootpd];
      destruct v ; try now contradict Hrootpd.
      subst; assumption.
      subst. 
      left. 
      split;trivial.
      intro ptRefChild. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2: {
      intros.
      destruct H as (H0 & H1).
      assert( (getTableAddrRoot' ptRefChild idxPageDir currentPart descChild s /\   ptRefChild = pageDefault) \/
     (forall idx : index,
      StateLib.getIndexOfAddr descChild levelMin = idx ->
      isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild idxPageDir currentPart descChild s)).
      { 
      destruct H1 as [H1 |H1].
      + left. trivial. 
      + right. intros idx Hidx.
        destruct H1 as (Hget  & Hnew & H1).
        split. 
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse.
          apply idxPDidxSh1notEq.
       - contradict Hfalse. apply idxPDidxSh2notEq.      -
       assumption.
     - assumption.  } 
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP. }
(** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptRefChildIsnull. simpl.
      case_eq ptRefChildIsnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
(** StateLib.getIndexOfAddr **)                
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros.
        destruct H as ((H & [(Hptchild& Hnull) | Hptchild]) & Hptchildnotnull).
        + subst. contradict Hptchildnotnull. intro Hnull.
          apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
          try repeat rewrite and_assoc in HP.
          pattern s in HP.
          eapply HP.  }
       intro idxRefChild. simpl.
(**readPresent **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readPresent. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         destruct H as (H & Hidx).
         assert (forall idx : index,
         StateLib.getIndexOfAddr descChild levelMin = idx -> isPE ptRefChild idx s/\ getTableAddrRoot ptRefChild idxPageDir currentPart descChild s).  
         intuition.
         apply H0 in Hidx. destruct Hidx. assumption.
       }
       intro presentRefChild. simpl.
(**readAccessible **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readAccessible. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         apply entryPresentFlagIsPE with presentRefChild;intuition. 
        }
       intros accessibleChild. simpl.
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      try repeat rewrite and_assoc in H.
      split.
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart).
      intuition. subst. unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. intuition.
      instantiate (1:= idxPageDir).
      split. intuition.
      assert(consistency s /\
              Some level = StateLib.getNbLevel /\ 
              currentPart = currentPartition s /\ 
              nextEntryIsPP currentPart idxPageDir currentPD s) as (Hcons & Hlevel & Hcp & Hrootpd)
      by intuition.
      clear H.  
      exists currentPD.
      split. assumption.
      split.
      unfold consistency in *.
      assert(partitionDescriptorEntry s /\ currentPartitionInPartitionsList s) as (Hpd &Hpr)
      by intuition. clear Hcons. 
      unfold partitionDescriptorEntry in Hpd.
      unfold currentPartitionInPartitionsList in *.
      subst.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.     
      assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2 \/idxPageDir = idxShadow3 \/ idxPageDir = idxParentDesc  \/ idxPageDir = idxPartDesc ) as Htmp 
      by auto.
      generalize (Hpd idxPageDir Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ idxPageDir); [|now contradict Hrootpd];
      destruct (lookup (currentPartition s) i (memory s) pageEq idxEq); [|now contradict Hrootpd];
      destruct v ; try now contradict Hrootpd.
      subst; assumption.
      subst. left. split;trivial.
           intro ptPDChild. simpl. 
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2: {
      intros.
      destruct H as (H0 & H1).
      assert( (getTableAddrRoot'  ptPDChild idxPageDir currentPart pdChild s /\    ptPDChild = pageDefault) \/
     (forall idx : index,
      StateLib.getIndexOfAddr pdChild levelMin = idx ->
      isPE  ptPDChild idx s /\ getTableAddrRoot ptPDChild  idxPageDir currentPart pdChild s)).
      { 
      destruct H1 as [H1 |H1].
      + left. trivial. 
      + right. intros idx Hidx.
      
        destruct H1 as (Hget  & Hnew & H1).

        split. 
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse.
          apply idxPDidxSh1notEq.
       - contradict Hfalse. apply idxPDidxSh2notEq.
      -
       assumption.
     - assumption.  } 
    assert (HP := conj H0 H).

        pattern s in HP.
        eapply HP. }     
(** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptPDChildIsnull. simpl.
      case_eq ptPDChildIsnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
(** StateLib.getIndexOfAddr         *)        
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros. 
        destruct H as ((H & [(Hptchild & Hnull) | Hptchild]) & Hptchildnotnull).
        + subst. contradict Hptchildnotnull. intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          pattern s in HP.
          eapply HP.  }
       intro idxPDChild. simpl.
(**readPresent **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readPresent. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         destruct H as (H & Hidx).
         assert (forall idx : index,
         StateLib.getIndexOfAddr pdChild levelMin = idx -> isPE ptPDChild idx s
         /\ getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s).  
         { intuition. }
         
         apply H0 in Hidx. destruct Hidx; assumption.
       }
       intro presentPDChild. simpl.
(**readAccessible **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readAccessible. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         apply entryPresentFlagIsPE with presentPDChild;intuition. }
       intros accessiblePDChild. simpl.  
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      try repeat rewrite and_assoc in H.
      split.
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart). 
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= idxPageDir).
      split. intuition.
      assert(consistency s /\
              Some level = StateLib.getNbLevel /\ 
              currentPart = currentPartition s /\ 
              nextEntryIsPP currentPart idxPageDir currentPD s) as (Hcons & Hlevel & Hcp & Hrootpd)
      by intuition.
      clear H. 
      exists currentPD.
      split. assumption.
      split.
      unfold consistency in *.
      assert(partitionDescriptorEntry s /\ currentPartitionInPartitionsList s) as (Hpd &Hpr)
      by intuition. clear Hcons. 

      unfold partitionDescriptorEntry in Hpd.
      assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2\/idxPageDir = idxShadow3\/ idxPageDir = idxParentDesc \/ idxPageDir = idxPartDesc ) as Htmp
          by auto.
      subst.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.     
       generalize (Hpd idxPageDir Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ idxPageDir); [|now contradict Hrootpd];
      destruct (lookup (currentPartition s) i (memory s) pageEq idxEq); [|now contradict Hrootpd];
      destruct v ; try now contradict Hrootpd.
      subst; assumption.
      subst. left. split;intuition.
     intro ptSh1Child. simpl.

 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2: {
      intros.
      destruct H as (H0 & H1).
      assert(( getTableAddrRoot' ptSh1Child idxPageDir currentPart shadow1 s /\  ptSh1Child = pageDefault) \/
     (forall idx : index,
      StateLib.getIndexOfAddr shadow1 levelMin = idx ->
      isPE ptSh1Child idx s/\
     getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s)).
      {
      destruct H1 as [H1 |(Hnew & Hi & H1)].
      + left. trivial. 
      + right. intros idx Hidx.
      
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse. apply idxPDidxSh1notEq.
       - contradict Hfalse. apply idxPDidxSh2notEq.
      -split;
       assumption. }
       
       assert (HP := conj H0 H).
       pattern s in HP.
       eapply HP. }
(** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptSh1Isnull. simpl.
      case_eq ptSh1Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
(** StateLib.getIndexOfAddr    *)             
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros. 
        destruct H as ((H & [(Hptchild & Hi)| Hptchild]) & Hptchildnotnull).
        + subst. contradict Hptchildnotnull. intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in H. *)
          pattern s in HP.
          eapply HP.  }
       intro idxSh1. simpl.
(**readPresent **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readPresent. simpl.
         intros.
         split. 
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         destruct H as (H & Hidx).
         assert (forall idx : index,
         StateLib.getIndexOfAddr shadow1 levelMin = idx -> isPE ptSh1Child idx s /\
     getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s).  
         { intuition. }
         
         apply H0 in Hidx. destruct Hidx; assumption.
       }
       intro presentSh1. simpl.
(**readAccessible **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readAccessible. simpl.
         intros.
         split.
         
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         apply entryPresentFlagIsPE with presentSh1 ;intuition. }
       intros accessibleSh1. simpl.   
(** getTableAddr **)

      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      try repeat rewrite and_assoc in H.
      split.
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart).
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= idxPageDir).
      split. intuition.
      
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & 
      b_ & _ & _ &_ & _ & _ & _ &_ & _&_ & _ &_ & _& Hcp & Hrootpd & H).
      exists currentPD.
      split. intuition.
      split.
      unfold consistency in *.
             destruct Hcons as (Hpd & _ & _ &_  & Hpr  & _). 
      unfold partitionDescriptorEntry in Hpd.
       assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2\/idxPageDir = idxShadow3\/ idxPageDir = idxParentDesc \/ idxPageDir = idxPartDesc ) as Htmp 
          by auto.
          subst.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd idxPageDir Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ idxPageDir); [|now contradict Hrootpd];
      destruct (lookup (currentPartition s) i (memory s) pageEq idxEq); [|now contradict Hrootpd];
      destruct v ; try now contradict Hrootpd.
      subst; assumption.
      subst. left. split;intuition.
      intro ptSh2Child. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2: {
      intros.
      destruct H as (H0 & H1).
      assert( ( getTableAddrRoot' ptSh2Child idxPageDir currentPart shadow2 s /\ ptSh2Child = pageDefault) \/
     (forall idx : index,
      StateLib.getIndexOfAddr shadow2 levelMin = idx ->
      isPE ptSh2Child idx s/\
     getTableAddrRoot ptSh2Child idxPageDir currentPart shadow2 s)).
      {
      destruct H1 as [H1 |(Hi  & Hnew & H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
         - contradict Hfalse.
           apply idxPDidxSh1notEq.
         - contradict Hfalse.  apply idxPDidxSh2notEq.
      - split;
       assumption. }
       assert (HP := conj H0 H).
       pattern s in HP.
       eapply HP. } 
(** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptSh2Isnull. simpl.
      case_eq ptSh2Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
(** StateLib.getIndexOfAddr         *)        
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        + subst. contradict Hptchildnotnull. intro Hnull. destruct Hptchild.
            apply beq_nat_false in Hnull. subst. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          pattern s in HP.
          eapply HP. }
       intro idxSh2. simpl.
(**readPresent **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readPresent. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         destruct H as (H & Hidx).
         assert (forall idx : index,
         StateLib.getIndexOfAddr shadow2 levelMin = idx -> isPE ptSh2Child idx s /\
     getTableAddrRoot ptSh2Child idxPageDir currentPart shadow2 s).  
         { intuition. }
         
         apply H0 in Hidx. destruct Hidx;assumption.
       }
       intro presentSh2. simpl.
(**readAccessible **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readAccessible. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         apply entryPresentFlagIsPE with presentSh2 ;intuition. }
       intros accessibleSh2. simpl.
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      try repeat rewrite and_assoc in H.
      split.
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart).
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= idxPageDir).
      split. intuition.
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_  & _ & _ & _ &_ & _& _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).

      exists currentPD.
      split. intuition.
      split.
      unfold consistency in *.
      destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2\/ idxPageDir = idxShadow3
       \/ idxPageDir = idxParentDesc \/ idxPageDir = idxPartDesc) as Htmp 
      by auto.
            generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd idxPageDir Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ idxPageDir); [|now contradict Hrootpd];
      destruct (lookup (currentPartition s) i (memory s) pageEq idxEq); [|now contradict Hrootpd];
      destruct v ; try now contradict Hrootpd.
      subst; assumption.
      subst. left. split;intuition.
      intro ptConfigPagesList. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2: {
      intros.
      destruct H as (H0 & H1).
       assert( ( getTableAddrRoot' ptConfigPagesList idxPageDir currentPart list s /\ ptConfigPagesList = pageDefault) \/
     (forall idx : index,
      StateLib.getIndexOfAddr list levelMin = idx ->
      isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList idxPageDir currentPart list s)).
      {
      destruct H1 as [H1 |(Hi & Hi1 &H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
       - contradict Hfalse.
           apply idxPDidxSh1notEq.
         - contradict Hfalse.  apply idxPDidxSh2notEq.
      - split;
       assumption. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP. }
(** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptConfigPagesListIsnull. simpl.
      case_eq ptConfigPagesListIsnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
(** getIndexOfAddr *)                 
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        + destruct Hptchild. subst. contradict Hptchildnotnull.
          intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          pattern s in HP.
          eapply HP. }
       intro idxConfigPagesList. simpl.
(**readPresent **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readPresent. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         destruct H as (H & Hidx).
         assert (forall idx : index,
         StateLib.getIndexOfAddr list levelMin = idx -> isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList idxPageDir currentPart list s).  
         { intuition. }
         
         apply H0 in Hidx. destruct Hidx;assumption.
       }
       intro presentConfigPagesList. simpl.
(**readAccessible **)
       eapply WP.bindRev.
       { eapply WP.weaken.
         eapply Invariants.readAccessible. simpl.
         intros.
         split.
(*          try repeat rewrite and_assoc in H. *)
         pattern s in H.
         eapply H. 
         subst.
         apply entryPresentFlagIsPE with presentConfigPagesList ;intuition. }
      intros accessibleList. simpl.    
(** case present && accessible **)
      case_eq (presentRefChild && accessibleChild && presentPDChild && accessiblePDChild &&
               presentConfigPagesList && accessibleList && presentSh1 && accessibleSh1 && 
               presentSh2 && accessibleSh2).
(** fst case : accessible and present **)
      { intro Hlegit.
(** getFstShadow **)
      eapply WP.bindRev.
        { eapply WP.weaken. 
            eapply Invariants.getFstShadow. cbn.
            intros s H.
            split.
(*              try repeat rewrite and_assoc in H.  *)
            pattern s in H.
            eapply H.
            unfold consistency in *.
           unfold partitionDescriptorEntry in *.
          intuition.   }
      intro currentShadow1.
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      split.
(*       try repeat rewrite and_assoc in H. *)
      
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart).
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= idxShadow1).
      split. intuition. (*
      destruct H as ( (_ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& 
      _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H) & H0). *)
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart idxPageDir currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart idxShadow1 currentShadow1 s) by intuition.
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.
      destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (idxShadow1 = idxPageDir \/ idxShadow1 = idxShadow1 \/ idxShadow1 = idxShadow2 
      \/  idxShadow1  = idxShadow3 \/ idxShadow1  = idxParentDesc \/  idxShadow1 = idxPartDesc) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd idxShadow1 Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.
      unfold nextEntryIsPP in *. 
      destruct (StateLib.Index.succ idxShadow1); try now contradict Hrootpd.
      destruct (lookup (currentPartition s) i (memory s) pageEq idxEq) ; try now contradict Hrootpd.
      destruct v ; try now contradict Hrootpd.
      subst; assumption.
      subst. left. split;intuition.
      intro ptRefChildFromSh1.
      simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2: {
      intros.
      destruct H as (H0 & H1).
      assert ( (getTableAddrRoot' ptRefChildFromSh1 idxShadow1 currentPart descChild s /\ ptRefChildFromSh1 = pageDefault) \/
     (forall idx : index,
      StateLib.getIndexOfAddr descChild levelMin = idx ->
      isVE ptRefChildFromSh1 idx s /\  getTableAddrRoot ptRefChildFromSh1 idxShadow1 currentPart descChild s)).
      { destruct H1 as [H1 |(Hi & Hi1 & H1 )].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
        - contradict Hfalse. 
         symmetrynot. apply idxSh2idxSh1notEq.
       - contradict Hfalse. 
          symmetrynot. apply idxPDidxSh1notEq. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP. }
(** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptRefChildFromSh1Isnull. simpl.
      case_eq ptRefChildFromSh1Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
      
(** derived **)
      eapply WP.bindRev.
      { eapply WP.weaken.
        eapply Invariants.checkDerivation. simpl.
        simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        + destruct Hptchild. subst. contradict Hptchildnotnull.
          intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          split.
          eapply HP. 
          subst.
          assert ( StateLib.getIndexOfAddr descChild levelMin = idxRefChild) as Hidxchild.
          intuition.
          apply Hptchild in Hidxchild. destruct Hidxchild; assumption. }
      simpl. intros derivedRefChild.
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
(*       try repeat rewrite and_assoc in H. *)
      split.
(*       try repeat rewrite and_assoc in H. *)
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart). 
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= idxShadow1).
      split. intuition.
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart idxPageDir currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart idxShadow1 currentShadow1 s) by intuition.
      (*
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).
      assert (nextEntryIsPP currentPart sh1idx currentShadow1 s ). intuition. *)
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.

        destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (idxShadow1 = idxPageDir \/ idxShadow1 = idxShadow1 \/ idxShadow1 = idxShadow2 \/  idxShadow1  = idxShadow3
      \/  idxShadow1  = idxParentDesc \/  idxShadow1 = idxPartDesc) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd idxShadow1 Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.
      unfold nextEntryIsPP in *. 
      destruct (StateLib.Index.succ idxShadow1); try now contradict Hrootpd.
      destruct (lookup (currentPartition s) i (memory s) pageEq idxEq) ; try now contradict Hrootpd.
      destruct v ; try now contradict Hrootpd.
      subst; assumption.
      subst. left. split;intuition.
      intro ptPDChildSh1. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2: {
      intros.
      destruct H as (H0 & H1).
          
      assert (  (getTableAddrRoot' ptPDChildSh1 idxShadow1 currentPart pdChild s /\ ptPDChildSh1 = pageDefault) \/
     (forall idx : index,
      StateLib.getIndexOfAddr pdChild levelMin = idx ->
      isVE ptPDChildSh1 idx s /\
     getTableAddrRoot ptPDChildSh1 idxShadow1 currentPart pdChild s )).
      { destruct H1 as [H1 |( Hi & Hi1  &H1 )].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
        - contradict Hfalse. 
         symmetrynot. apply idxSh2idxSh1notEq.
       - contradict Hfalse. 
          symmetrynot. apply idxPDidxSh1notEq.  }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP. }
(** comparePageToNull **) 

      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptPDChildSh1Isnull. simpl.

      case_eq ptPDChildSh1Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
      
(** derived **)
      eapply WP.bindRev.
      {  eapply WP.weaken.
        eapply Invariants.checkDerivation. simpl.
        simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        +  destruct Hptchild. subst. contradict Hptchildnotnull.
          intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          split.
          eapply HP. 
          subst.
          assert ( StateLib.getIndexOfAddr pdChild levelMin = idxPDChild) as Hidxchild.
          intuition. 
          apply Hptchild in Hidxchild. destruct Hidxchild;assumption. }
      simpl. intros derivedPDChild.
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
    (*   try repeat rewrite and_assoc in H. *)
      split.
(*       try repeat rewrite and_assoc in H. *)
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart).
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= idxShadow1).
      split. intuition.
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart idxPageDir currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart idxShadow1 currentShadow1 s) by intuition.
      (*
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ 
      & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).
      assert (nextEntryIsPP currentPart sh1idx currentShadow1 s ). intuition. *)
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.
        destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (idxShadow1 = idxPageDir \/ idxShadow1 = idxShadow1 \/ idxShadow1 = idxShadow2 \/  idxShadow1  = idxShadow3
      \/  idxShadow1  = idxParentDesc \/  idxShadow1 = idxPartDesc) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd idxShadow1 Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.
      unfold nextEntryIsPP in *. 
      destruct (StateLib.Index.succ idxShadow1); try now contradict Hrootpd.
      destruct (lookup (currentPartition s) i (memory s) pageEq idxEq) ; try now contradict Hrootpd.
      destruct v ; try now contradict Hrootpd.
      subst; assumption.
      subst. left. split;intuition.
      intro ptSh1ChildFromSh1. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2: {
      intros.
      destruct H as (H0 & H1).
      assert ( (getTableAddrRoot' ptSh1ChildFromSh1 idxShadow1 currentPart shadow1 s /\  ptSh1ChildFromSh1 = pageDefault) \/
     (forall idx : index,
      StateLib.getIndexOfAddr shadow1 levelMin = idx ->
      isVE ptSh1ChildFromSh1 idx s /\ getTableAddrRoot ptSh1ChildFromSh1 idxShadow1 currentPart shadow1 s)).
      { destruct H1 as [H1 |(Hi & Hi1 &H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
        - contradict Hfalse. 
         symmetrynot. apply idxSh2idxSh1notEq.
       - contradict Hfalse. 
          symmetrynot. apply idxPDidxSh1notEq.  }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP. }
(** comparePageToNull **) 

      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro childSh1Isnull. simpl.

      case_eq childSh1Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
      
(** derived **)
      eapply WP.bindRev.
      { eapply WP.weaken.
        eapply Invariants.checkDerivation. simpl.
        simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        + destruct Hptchild. subst. contradict Hptchildnotnull.
          intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          split.
          eapply HP. 
          subst.
          assert ( StateLib.getIndexOfAddr shadow1 levelMin = idxSh1) as Hidxchild.
          intuition.
          apply Hptchild in Hidxchild. destruct Hidxchild.
          assumption. }
      simpl. intros derivedSh1Child.
(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
(*       try repeat rewrite and_assoc in H. *)
      split.
(*       try repeat rewrite and_assoc in H. *)
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart). 
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= idxShadow1).
      split. intuition.
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart idxPageDir currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart idxShadow1 currentShadow1 s) by intuition.
      (*
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ 
      & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H).
      assert (nextEntryIsPP currentPart sh1idx currentShadow1 s ). intuition.*)
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.
              destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (idxShadow1 = idxPageDir \/ idxShadow1 = idxShadow1 \/ idxShadow1 = idxShadow2 \/  idxShadow1  = idxShadow3
      \/  idxShadow1  = idxParentDesc \/  idxShadow1 = idxPartDesc) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd idxShadow1 Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.
      unfold nextEntryIsPP in *. 
      destruct (StateLib.Index.succ idxShadow1); try now contradict Hrootpd.
      destruct (lookup (currentPartition s) i (memory s) pageEq idxEq) ; try now contradict Hrootpd.
      destruct v ; try now contradict Hrootpd.
      subst; assumption.
      subst. left. split;intuition.
      intro childSh2. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2: {
      intros.
      destruct H as (H0 & H1).
      assert (  (getTableAddrRoot' childSh2 idxShadow1 currentPart shadow2 s /\ childSh2 = pageDefault) \/
     (forall idx : index,
      StateLib.getIndexOfAddr shadow2 levelMin = idx ->
      isVE childSh2 idx s /\ getTableAddrRoot childSh2 idxShadow1 currentPart shadow2 s )).
      { destruct H1 as [H1 |(Hi & Hi1 &H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
- contradict Hfalse. 
         symmetrynot. apply idxSh2idxSh1notEq.
       - contradict Hfalse. 
          symmetrynot. apply idxPDidxSh1notEq. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP. }
(** comparePageToNull **) 

      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro childSh2Isnull. simpl.

      case_eq childSh2Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
      
(** derived **)
      eapply WP.bindRev.
      { eapply WP.weaken.
        eapply Invariants.checkDerivation. simpl.
        simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        + destruct Hptchild. subst. contradict Hptchildnotnull.
          intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP. *)
          split.
          eapply HP. 
          subst.
          assert ( StateLib.getIndexOfAddr shadow2 levelMin = idxSh2) as Hidxchild.
          intuition. 
          apply Hptchild in Hidxchild. destruct Hidxchild; assumption. }
      simpl. intros derivedSh2Child.


(** getTableAddr **)
      eapply WP.bindRev.
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
(*       try repeat rewrite and_assoc in H. *)
      split.
(*       try repeat rewrite and_assoc in H.  *)
      pattern s in H. 
      eapply H. subst.
      split. 
      intuition.
      split. 
      instantiate (1:= currentPart).
      intuition. 
      subst.
      unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. 
      intuition.
      instantiate (1:= idxShadow1).
      split. intuition.
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart idxPageDir currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart idxShadow1 currentShadow1 s) by intuition.
      (*
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& 
      _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).
      assert (nextEntryIsPP currentPart sh1idx currentShadow1 s ). intuition. *)
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.
      
              destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (idxShadow1 = idxPageDir \/ idxShadow1 = idxShadow1 \/ idxShadow1 = idxShadow2 \/  idxShadow1  = idxShadow3
      \/  idxShadow1  = idxParentDesc \/  idxShadow1 = idxPartDesc) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd idxShadow1 Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.
      unfold nextEntryIsPP in *. 
      destruct (StateLib.Index.succ idxShadow1); try now contradict Hrootpd.
      destruct (lookup (currentPartition s) i (memory s) pageEq idxEq) ; try now contradict Hrootpd.
      destruct v ; try now contradict Hrootpd.
      subst; assumption.
      subst. left. split;intuition.
      intro childListSh1. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2: {
      intros.
      destruct H as (H0 & H1).
      assert ( (getTableAddrRoot' childListSh1 idxShadow1 currentPart list s /\ childListSh1 = pageDefault) \/
     (forall idx : index,
      StateLib.getIndexOfAddr list levelMin = idx ->
      isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 idxShadow1 currentPart list s  )).
      { destruct H1 as [H1 |(Hi & Hi1 & H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
- contradict Hfalse. 
         symmetrynot. apply idxSh2idxSh1notEq.
       - contradict Hfalse. 
          symmetrynot. apply idxPDidxSh1notEq.  }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP. }
(** comparePageToNull **) 

      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro childListSh1Isnull. simpl.

      case_eq childListSh1Isnull.
      { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
      intros HptRefChildNotNull. clear HptRefChildNotNull.
      
(** derived **)
      eapply WP.bindRev.
      { eapply WP.weaken.
        eapply Invariants.checkDerivation. simpl.
        simpl. intros. 
        destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
        + destruct Hptchild. subst. contradict Hptchildnotnull.
          intro Hnull.  apply beq_nat_false in Hnull. intuition.
        + subst.
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
(*           try repeat rewrite and_assoc in HP.  *)
          split.
          eapply HP. 
          subst.
          assert ( StateLib.getIndexOfAddr list levelMin = idxConfigPagesList) as Hidxchild.
          intuition.  
          apply Hptchild in Hidxchild. destruct Hidxchild; assumption.  }
      simpl. intros derivedRefChildListSh1.
(** Derivation Test **) 
    case_eq ( derivedRefChild && derivedPDChild && derivedSh1Child && derivedSh2Child && derivedRefChildListSh1).
    - intros. 
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split.
    pattern s in H0.
    eapply H0. 
    subst.
    
    unfold propagatedProperties in *.  
    assert (Hpe : forall idx : index,
      StateLib.getIndexOfAddr pdChild levelMin = idx ->
      isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s) by intuition.
    apply Hpe.
    intuition.
    simpl.
    intros phyPDChild.
(* (** comparePageToNull **) 
    eapply WP.bindRev.
    eapply Invariants.comparePageToNull.
    intro phyPDChildIsnull.
    simpl.
    case_eq phyPDChildIsnull.
    { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
    intros phyPDChildNotNull.  *)   
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split.
    assert(Hnotnull : (Nat.eqb pageDefault phyPDChild) = false).
    { unfold consistency in *.
      assert(Hcons : isPresentNotDefaultIff s) by intuition.
      assert(Hpresent : entryPresentFlag ptPDChild idxPDChild presentPDChild s) by intuition.
      apply phyPageNotDefault with ptPDChild idxPDChild s;intuition.
      repeat rewrite andb_true_iff in Hlegit;intuition.
      subst. trivial. }
    
    assert(Hphy : forall partition, In partition (getPartitions pageRootPartition s) ->
    ~ In phyPDChild (getConfigPages partition s) ).
    { intros. try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as (_ & _ & presentPD & accessPD & _).
       unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial. 
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold Lib.disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptPDChild pdChild idxPDChild 
      accessiblePDChild level presentPDChild currentPD; subst; intuition.
    }   
    assert(Hnew := conj (conj H0 Hnotnull) Hphy).    
    pattern s in Hnew.
    apply Hnew. 
    subst.
     unfold propagatedProperties in *. 
    assert (Hpe : forall idx : index,
                   StateLib.getIndexOfAddr shadow1 levelMin = idx ->
                   isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child idxPageDir 
                   currentPart shadow1 s) by intuition.
    apply Hpe.
    intuition.
    simpl.
    intros phySh1Child.
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split.
    assert(Hnotnull : (Nat.eqb pageDefault phySh1Child) = false).
    { unfold consistency in *.
      assert(Hcons : isPresentNotDefaultIff s) by intuition.
      assert(Hpresent : entryPresentFlag ptSh1Child idxSh1 presentSh1 s) by intuition.
      apply phyPageNotDefault with ptSh1Child idxSh1 s;intuition.
      repeat rewrite andb_true_iff in Hlegit;intuition.
      subst. trivial. }
      
    assert(Hphy : forall partition, In partition (getPartitions pageRootPartition s) -> 
    ~ In phySh1Child  (getConfigPages partition s) ).
    { intros. try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as (_ & _ & _ & _ & _ & _ &  presentPD & accessPD & _).
      unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial.
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold Lib.disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptSh1Child shadow1 idxSh1 accessibleSh1
       level presentSh1 currentPD ; subst;intuition . }
    assert(Hnew := conj (conj H0 Hnotnull) Hphy).    
    pattern s in Hnew.
    eapply Hnew. 
    subst.
     unfold propagatedProperties in *. 
    assert (Hpe : forall idx : index,
                     StateLib.getIndexOfAddr shadow2 levelMin = idx ->
                     isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child 
                     idxPageDir currentPart shadow2 s) by intuition.
    apply Hpe.
    intuition. 
    simpl.
    intros phySh2Child.
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split.
    assert(Hnotnull : (Nat.eqb pageDefault phySh2Child) = false).
    { unfold consistency in *.
      assert(Hcons : isPresentNotDefaultIff s) by intuition.
      assert(Hpresent : entryPresentFlag ptSh2Child idxSh2 presentSh2 s) by intuition.
      apply phyPageNotDefault with ptSh2Child idxSh2 s;intuition.
      repeat rewrite andb_true_iff in Hlegit;intuition.
      subst. trivial. }
    assert(Hphy : forall partition, In partition (getPartitions pageRootPartition s) ->
    ~ In phySh2Child (getConfigPages partition s)).
    { intros. try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as (_ & _ & _ & _ & _ & _ & _ & _ &  presentPD & accessPD ).
      unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial.
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold Lib.disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptSh2Child shadow2 idxSh2 accessibleSh2
       level presentSh2 currentPD ; subst;intuition. }
    assert(Hnew := conj (conj H0 Hnotnull) Hphy).     
    pattern s in Hnew.
    eapply Hnew. 
    subst.
 unfold propagatedProperties in *.  
    assert (Hpe : forall idx : index,
                       StateLib.getIndexOfAddr list levelMin = idx ->
                       isPE ptConfigPagesList idx s /\
                       getTableAddrRoot ptConfigPagesList idxPageDir currentPart list s) 
    by intuition.
    apply Hpe.
    intuition.
    simpl.
    intros phyConfigPagesList.
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split.
     assert(Hnotnull : (Nat.eqb pageDefault phyConfigPagesList) = false).
    { unfold consistency in *.
      assert(Hcons : isPresentNotDefaultIff s) by intuition.
      assert(Hpresent : entryPresentFlag ptConfigPagesList idxConfigPagesList presentConfigPagesList s) by intuition.
      apply phyPageNotDefault with ptConfigPagesList idxConfigPagesList s;intuition.
      repeat rewrite andb_true_iff in Hlegit;intuition.
      subst. trivial. }
    assert(Hphy : forall partition, In partition (getPartitions pageRootPartition s) ->
    ~ In phyConfigPagesList (getConfigPages partition s)).
    { intros. try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as (_ & _ & _ & _ & presentPD & accessPD & _ ).
       unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial.
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold Lib.disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptConfigPagesList list idxConfigPagesList 
      accessibleList level presentConfigPagesList currentPD; subst;intuition. }
    assert(Hnew := conj (conj H0 Hnotnull) Hphy).    
    pattern s in Hnew.
    eapply Hnew. 
    subst.
 unfold propagatedProperties in *.  
    assert (Hpe : forall idx : index,
                         StateLib.getIndexOfAddr descChild levelMin = idx ->
                         isPE ptRefChild idx s /\
                         getTableAddrRoot ptRefChild idxPageDir currentPart descChild s)
    by intuition.
    apply Hpe.
    intuition.
    simpl.
    intros phyDescChild.
(** writeAccessible : pdChild **)
    eapply WP.bindRev.
    eapply WP.weaken.
    assert(Htrue : accessiblePDChild = true).
    try repeat rewrite  andb_true_iff in Hlegit.  intuition.
    rewrite Htrue in Hlegit.
    eapply writePhyEntry1.
    eapply Hlegit.
    eassumption.
    intros.
    simpl.
    assert(Htrue : accessiblePDChild = true).
    try repeat rewrite  andb_true_iff in Hlegit.  intuition.
    rewrite Htrue in H0.
    try repeat rewrite and_assoc in H0.
    eapply H0.  
    intros [].
(** writeAccessibleRec : pdChild **)
    eapply bindRev.
    eapply weaken.
    eapply postAnd.
    eapply WriteAccessibleRec.
    eapply WriteAccessibleRecPostCondition.
    simpl.
    intros.
    split. 
    destruct H0 as ((((H0 & Ha1 ) & Ha2) & Ha3) &Ha4).
    repeat rewrite <- and_assoc in Ha3.
    destruct Ha3 as (Ha3 & Hfalse).
    repeat rewrite and_assoc in Ha3.    
    assert(Hnew :=  conj ( conj ( conj ( conj H0 Ha4 ) Ha1 ) Ha2 ) Ha3).
    repeat rewrite and_assoc in Hnew.
    unfold propagatedProperties.
    eapply Hnew.
    instantiate(1:= phyPDChild).
    instantiate(1:= idxPDChild).
    instantiate(1:= ptPDChild).
    intuition.
    unfold isAncestor.
    left;trivial.
    subst.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in*.
    intuition.
    subst.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    intros.
    simpl.    
(** writeAccessible : shadow1 **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply writePhyEntry2.
    assert(Htrue : accessiblePDChild = true).
    try repeat rewrite  andb_true_iff in Hlegit.  intuition.
    rewrite Htrue in Hlegit.
    eapply Hlegit.
    eapply H.
    intros s Hpre.
    simpl.
    eapply Hpre.
    simpl.
    intros [].
(** writeAccessibleRec : shadow 1 **)
    eapply bindRev. (* 
    apply preAndPost. *) 
    eapply weaken.
    eapply postAnd.
    apply preAndPost.
    eapply WriteAccessibleRec.
    instantiate (1:= fun s => (forall partition : page,
      In partition (getAncestors currentPart s) ->
      ~ In phyPDChild (getAccessibleMappedPages partition s))).
    simpl.    
    eapply weaken.
    eapply WriteAccessibleRecPropagateNewProp.
    simpl; intros.
    destruct H0 as (H0 & H1).
    destruct H0 as (H0 & H2).
    destruct H2 as (H2 &H3).
    split.
    eassumption.
    split. eassumption.
    split;eassumption.
    simpl.
    eapply preAnd.    
    eapply WriteAccessibleRecPostCondition. 
    simpl.
    intros.
    split. split.
    destruct H0 as (((Ha & Hb) & Hc) & Hd ).
    eassumption.
    (*instantiate (41 := false). 
        destruct H0 as ((((H0  & Huserpd) & Hnewrec ) & Haccesssh1) & Husersh1 ).
    assert(H0new := conj( conj H0 Husersh1) Huserpd ). 
      repeat rewrite and_assoc in H0new.
    unfold propagatedProperties.
    eapply H0new.**)
        instantiate(1:= phySh1Child).
    instantiate(1:= idxSh1).
    instantiate(1:= ptSh1Child).
    unfold propagatedProperties in *.
    intuition;subst;trivial.
        unfold isAncestor.
    left;trivial.
    subst.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in*.
    intuition.
    subst.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    intuition.
    simpl.    
    intros.
(** writeAccessible : shadow 2 **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply writePhyEntry3.
   assert(Htrue : accessiblePDChild = true).
    try repeat rewrite  andb_true_iff in Hlegit.  intuition.
    rewrite Htrue in Hlegit.
    eapply Hlegit.
    eapply H.
    intros s Hpre.
    simpl.
    eapply Hpre.
    simpl.
   intros [].
(** writeAccessibleRec : shadow 2 **)
    eapply bindRev.
    eapply weaken.
    eapply postAnd.
    apply preAndPost.    
    eapply WriteAccessibleRec.
    simpl.


    eapply andPreAndPost.
    instantiate (1:= fun s => (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phyPDChild (getAccessibleMappedPages partition s)) ).
    simpl.
    { eapply weaken.
      eapply WriteAccessibleRecPropagateNewProp.
      simpl; intros.
      destruct H0 as (H0 & H1).
      destruct H0 as (H0 & H2).
      destruct H2 as (H2 &H3).
      split.
      eassumption.
      split. eassumption.
      split;eassumption. }
    simpl.
    instantiate (1:= fun s => (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phySh1Child (getAccessibleMappedPages partition s))).
    { eapply weaken.
      eapply WriteAccessibleRecPropagateNewProp.
      simpl; intros.
      destruct H0 as (H0 & H1).
      destruct H0 as (H0 & H2).
      destruct H2 as (H2 &H3).
      split.
      eassumption.
      split. eassumption.
      split;eassumption. } 
    simpl.
    eapply preAnd.
    simpl.
    eapply WriteAccessibleRecPostCondition.
    simpl.
    intros.
    split. split.  
    instantiate (41 := false).
    instantiate (40 := false).
    destruct H0 as (((((* ( *)H0  & Huserpd) & Hnewrec ) & Haccesssh1) &  Haccesssh2(* ) &Husersh1  *) ). (* 
    assert(H0new := conj( conj H0 Husersh1) Huserpd ).
    repeat rewrite and_assoc in H0new.
    unfold propagatedProperties.
   *)  eapply H0.
    instantiate(1:= phySh2Child).
    instantiate(1:= idxSh2).
    instantiate(1:= ptSh2Child).
    unfold propagatedProperties in *.
    intuition.
    unfold isAncestor;left;trivial.
    subst.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in*.
    intuition.
    subst.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    intuition.
    intros.
    simpl.
(** writeAccessible : list  **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply writeInaccessibleConfigList.
    assert(Htrue : accessiblePDChild= true).
    try repeat rewrite  andb_true_iff in Hlegit.  intuition.
    rewrite Htrue in Hlegit.
    eapply Hlegit.
    eapply H.
    intros s Hpre.
    simpl.
    eapply Hpre.
    simpl.
    intros [].
(** writeAccessibleRec : list **)
    eapply bindRev.
    eapply weaken.
    eapply postAnd.
    apply preAndPost.    
    eapply WriteAccessibleRec.
    simpl.
    eapply andPreAndPost.
     eapply andPreAndPost.
    instantiate (1:= fun s => (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phyPDChild (getAccessibleMappedPages partition s)) ).
    simpl.
    { eapply weaken.
      eapply WriteAccessibleRecPropagateNewProp.
      simpl; intros.
      destruct H0 as (H0 & H1).
      destruct H0 as (H0 & H2).
      destruct H2 as (H2 &H3).
      split.
      eassumption.
      split. eassumption.
      split;eassumption. } 
    simpl.
    instantiate (1:= fun s => (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phySh1Child (getAccessibleMappedPages partition s))).
    simpl.
   { eapply weaken.
      eapply WriteAccessibleRecPropagateNewProp.
      simpl; intros.
      destruct H0 as (H0 & H1).
      destruct H0 as (H0 & H2).
      destruct H2 as (H2 &H3).
      split.
      eassumption.
      split. eassumption.
      split;eassumption. }  
    simpl.
    instantiate (1:= fun s => (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phySh2Child (getAccessibleMappedPages partition s))).
    simpl.
    { eapply weaken.
      eapply WriteAccessibleRecPropagateNewProp.
      simpl; intros.
      destruct H0 as (H0 & H1).
      destruct H0 as (H0 & H2).
      destruct H2 as (H2 &H3).
      split.
      eassumption.
      split. eassumption.
      split;eassumption. }  
    simpl.    
    eapply preAnd.
    eapply WriteAccessibleRecPostCondition.
    simpl.
    intros.
    split. split.  
    instantiate (41 := false).
    instantiate (40 := false).
    instantiate (39 := false).
    destruct H0 as ((((H0  & Huserpd) & Hnewrec ) & Haccesssh1) & Husersh1 ).
(*     destruct H0 as (H0 & Hsplit). 
    assert(H0new := conj( conj H0 Husersh1) Hsplit ).
    repeat rewrite and_assoc in H0new.
    unfold propagatedProperties. *)
    eapply H0.
    instantiate(1:= phyConfigPagesList).
    instantiate(1:= idxConfigPagesList).
    instantiate(1:= ptConfigPagesList).
    unfold propagatedProperties in *.
    intuition.
    unfold isAncestor;left;trivial.
    subst.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in*.
    intuition.
    subst.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    intuition.
    intros.
    simpl.
(** writeAccessible : descChild  **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply writeInaccessibleDescChild.
 assert(Htrue : accessiblePDChild= true).
    try repeat rewrite  andb_true_iff in Hlegit.  intuition.
    rewrite Htrue in Hlegit.
    eapply Hlegit.
    eapply H.
    intros s Hpre.
    simpl.
    eapply Hpre.
    simpl.
    intros [].    
(** writeAccessibleRec : descChild **)
    eapply bindRev.
    eapply weaken.
    eapply postAnd.
    apply preAndPost.    
    eapply WriteAccessibleRec.
    simpl.
    eapply andPreAndPost.
     eapply andPreAndPost.
     eapply andPreAndPost.
    instantiate (1:= fun s => (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phyPDChild (getAccessibleMappedPages partition s)) ).
    { eapply weaken.
      eapply WriteAccessibleRecPropagateNewProp.
      simpl; intros.
      destruct H0 as (H0 & H1).
      destruct H0 as (H0 & H2).
      destruct H2 as (H2 &H3).
      split.
      eassumption.
      split. eassumption.
      split;eassumption. } 
    simpl.
    instantiate (1:= fun s => (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phySh1Child (getAccessibleMappedPages partition s))).
    { eapply weaken.
      eapply WriteAccessibleRecPropagateNewProp.
      simpl; intros.
      destruct H0 as (H0 & H1).
      destruct H0 as (H0 & H2).
      destruct H2 as (H2 &H3).
      split.
      eassumption.
      split. eassumption.
      split;eassumption. }  
    simpl.
    instantiate (1:= fun s => (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phySh2Child (getAccessibleMappedPages partition s))).
    { eapply weaken.
      eapply WriteAccessibleRecPropagateNewProp.
      simpl; intros.
      destruct H0 as (H0 & H1).
      destruct H0 as (H0 & H2).
      destruct H2 as (H2 &H3).
      split.
      eassumption.
      split. eassumption.
      split;eassumption. }  
    simpl.
    instantiate (1:= fun s => (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In phyConfigPagesList (getAccessibleMappedPages partition s))).
    { eapply weaken.
      eapply WriteAccessibleRecPropagateNewProp.
      simpl; intros.
      destruct H0 as (H0 & H1).
      destruct H0 as (H0 & H2).
      destruct H2 as (H2 &H3).
      split.
      eassumption.
      split. eassumption.
      split;eassumption. }  
    simpl.        
    eapply preAnd.
    eapply WriteAccessibleRecPostCondition.
    simpl.
    intros.
    split.    
    split. 
    instantiate (42 := false).
    instantiate (41 := false).
    instantiate (40 := false).
    instantiate (39 := false).
    destruct H0 as ((((H0  & Huserpd) & Hnewrec ) & Haccesssh1) & Husersh1 ).
 (*   destruct H0 as (H0 & Hsplit). 
    assert(H0new := conj( conj H0 Husersh1) Hsplit ).
    repeat rewrite and_assoc in H0new. *)
    eapply H0.
     unfold propagatedProperties in *.
    instantiate(1:= phyDescChild).
    instantiate(1:= idxRefChild).
    instantiate(1:= ptRefChild).
    intuition.
    unfold isAncestor;left;trivial.
    subst.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in*.
    intuition.
    subst.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst;trivial.
    intuition.
    intros.
    simpl.
(** IndexZero **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply Invariants.Index.zero.
    simpl.
    intros.
    pattern s in H0.
    eassumption.
    intros zero. simpl. 
(** initPEntryTable **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply initPEntryTablePropagateProperties1.
    eapply initPEntryTableNewPropertyL.
    { intros. simpl.
      split. split.
       repeat rewrite  and_assoc in H0.
       repeat rewrite and_assoc. 
      eassumption.
      unfold propagatedProperties in *.
      split. intuition. intuition.
      intros.
      assert (zero = CIndex 0) as Hzero.
      intuition.
      unfold initPEntryTablePreconditionToProveNewProperty.
      intros.
      subst.
      unfold CIndex in H1.
      case_eq (lt_dec 0 tableSize).
      intros.
      rewrite H2 in H1.
      simpl in *. lia.
      intros.
      contradict H2.
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia. }
    intros resinittablepd.
    simpl.
    (** getKidx **)
  eapply WP.bindRev.
  eapply WP.weaken.
  apply  Invariants.getKidx.
  simpl.
  intros.
  eapply H0.
  simpl.
  intros kidx.
(** writeKernelPhyEntry **)
    eapply WP.bindRev.
    intros.
    eapply WP.weaken.

    eapply mapKernel.
    simpl.
    intros.
    pattern s in H0.
    match type of H0 with 
    | ?HT s => instantiate (1 := fun tt s => HT s )
    end.
    simpl.
    set (s' :=  {|
     currentPartition := currentPartition s;
     memory := add phyPDChild kidx
                 (PE {| read := false; write := false; exec := false; present := false; user := false; pa := pageDefault |})
                 (memory s) pageEq idxEq |}) in *.
   simpl in *.
   destruct H0 as ((H0 & Ha1 ) & Ha3).
split.
split.
split.
destruct H0. 
apply propagatedPropertiesUpdateMappedPageData; trivial.
   apply isPresentNotDefaultIffRightValue.
   unfold propagatedProperties in * .
   unfold consistency in *.
   intuition.
   unfold propagatedProperties in * .
   intuition.
   unfold propagatedProperties in * .
   intuition.
   {
  repeat rewrite and_assoc.
   unfold propagatedProperties in *.
   unfold isWellFormedMMUTables in *.
   assert(Hcurpart : In currentPart (getPartitions pageRootPartition s)).
   {unfold consistency in *.
   intuition.
   subst.
   unfold currentPartitionInPartitionsList in *.
   subst;intuition. }
   try repeat split;trivial; try (
    apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition).
    destruct H0.
    destruct H1. trivial. }
   intuition.
   unfold isWellFormedMMUTables.
   intros.
   unfold StateLib.readPhyEntry, StateLib.readPresent  in *.
   cbn.
   case_eq(beqPairs (phyPDChild, kidx) (phyPDChild, idx) pageEq idxEq
   );intros.
   simpl.
   subst;split;trivial.
   assert( lookup phyPDChild idx (removeDup phyPDChild kidx (memory s)
    pageEq idxEq) pageEq idxEq =
    lookup phyPDChild idx (memory s) pageEq idxEq).
    apply removeDupIdentity.
    apply beqPairsFalse in H0.
    intuition.
    rewrite H8.
    apply Ha1.
    trivial.
    subst.
    trivial.
intros [].
(** initPEntryTable **)

    eapply weaken.
    instantiate(1:= fun s : state => 
    (propagatedProperties false false false false pdChild currentPart
        currentPD level ptRefChild descChild idxRefChild presentRefChild
        ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1
        presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList
        idxConfigPagesList presentConfigPagesList currentShadow1
        ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild
        ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child
        childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
        phySh2Child phyConfigPagesList phyDescChild s /\ ((((forall partition : page,
          In partition (getAncestors currentPart s) ->
          ~ In phyPDChild (getAccessibleMappedPages partition s)) /\
         (forall partition : page,
          In partition (getAncestors currentPart s) ->
          ~ In phySh1Child (getAccessibleMappedPages partition s))) /\
        (forall partition : page,
         In partition (getAncestors currentPart s) ->
         ~ In phySh2Child (getAccessibleMappedPages partition s))) /\
       (forall partition : page,
        In partition (getAncestors currentPart s) ->
        ~ In phyConfigPagesList (getAccessibleMappedPages partition s)) /\
       (forall partition : page,
        In partition (getAncestors currentPart s) ->
        ~ In phyDescChild (getAccessibleMappedPages partition s))) /\
      zero = CIndex 0) /\
     (forall idx : index,
      StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\ 
      StateLib.readPresent phyPDChild idx (memory s) = Some false)).
      2: {
      simpl;
      intuition.  }
      eapply WP.bindRev.
    eapply preAndPost.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply initFstShadowTablePropagateProperties1.
    eapply initFstShadowNewProperty.
    { intros. simpl.
      split. split.
      eassumption.
      unfold propagatedProperties in *.
      split. intuition. intuition.
      intros.
      assert (zero = CIndex 0) as Hzero.
      intuition.
      subst.

      assert(Hor : level <> levelMin \/ level = levelMin ) by apply levelDecOrNot.
      destruct Hor as [Ho | Hor].
      left;intros.
      split;trivial.
      intros.
      unfold CIndex in H1.
      case_eq (lt_dec 0 tableSize).
      intros.
      rewrite H2 in H1.
      simpl in *. lia.
      intros.
      contradict H2.
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.
      right.
      split;trivial.
      intros.
      unfold CIndex in H1.
      case_eq (lt_dec 0 tableSize).
      intros.
      rewrite H2 in H1.
      simpl in *. lia.
      intros.
      contradict H2.
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.
       }
    eapply weaken.
    eapply initFstShadowPropagateProperties2.
    intros.
    simpl.
    destruct H0 as ((H0 & Hzero) & Hphypd).
    split.
    split;
    eassumption.
    unfold propagatedProperties in *.
    assert(Hget1 :forall idx : index,
      StateLib.getIndexOfAddr shadow1 levelMin = idx ->
      isPE ptSh1Child idx s /\ 
      getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s) by intuition.
    assert(Hget2 : forall idx : index,
      StateLib.getIndexOfAddr pdChild levelMin = idx ->
      isPE ptPDChild idx s /\ 
      getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s) by intuition.
    intuition trivial.
    instantiate (1:= ptSh1Child); assumption.
    instantiate (1:= ptPDChild); assumption.
    instantiate (1:= currentPart); assumption.
    subst.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    intuition.
    instantiate (1 := shadow1).
    subst.
    assumption.
    instantiate (1 := pdChild).
    subst.
    assumption.
    apply Hget1; trivial.
    assert(Hidx : StateLib.getIndexOfAddr shadow1 levelMin = idxSh1) by trivial.
    generalize (Hget1 idxSh1 Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
    apply Hget2; trivial.
    assert(Hidx : StateLib.getIndexOfAddr pdChild levelMin = idxPDChild) by trivial.
    generalize (Hget2 idxPDChild Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
    assumption.
    assert (presentSh1 = true).
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption.
    simpl.
(** initPEntryTable **) 
    intros []. simpl.
    eapply WP.bindRev.
    { eapply preAndPost.
      + eapply preAndPost.
        - eapply WP.weaken.
          eapply conjPrePost.
          eapply initSndShadowTablePropagateProperties1.
          eapply initSndShadowNewProperty.
          { intros. simpl.
            split. split.
            eassumption.
            unfold propagatedProperties in *.
            split. intuition. intuition.
            intros.
            assert (zero = CIndex 0) as Hzero.
            intuition.
            subst.
            assert(Hor : level <> levelMin \/ level = levelMin ) by apply levelDecOrNot.
            destruct Hor as [Ho | Hor].
            left;intros.
            split;trivial.
            intros.
            unfold CIndex in H1.
            case_eq (lt_dec 0 tableSize).
            intros.
            rewrite H2 in H1.
            simpl in *. lia.
            intros.
            contradict H2.
            assert (tableSize > tableSizeLowerBound).
            apply tableSizeBigEnough.
            unfold tableSizeLowerBound in *.
            lia.
            right.
            split;trivial.
            intros.
            unfold CIndex in H1.
            case_eq (lt_dec 0 tableSize).
            intros.
            rewrite H2 in H1.
            simpl in *. lia.
            intros.
            contradict H2.
            assert (tableSize > tableSizeLowerBound).
            apply tableSizeBigEnough.
            unfold tableSizeLowerBound in *.
            lia.
             }
        - eapply weaken.
          eapply initSndShadowPropagateProperties3.
          intros.
          simpl.
          destruct H0 as ((H0 & Hzero) & Hphypd).
          split.
          split;
          eassumption.
          unfold propagatedProperties in *.
          assert(Hget1 :forall idx : index,
            StateLib.getIndexOfAddr shadow2 levelMin = idx ->
            isPE ptSh2Child idx s /\ 
            getTableAddrRoot ptSh2Child idxPageDir currentPart shadow2 s) by intuition.
          assert(Hget2 : forall idx : index,
            StateLib.getIndexOfAddr shadow1 levelMin = idx ->
            isPE ptSh1Child idx s /\ 
            getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s) by intuition.
          intuition trivial.
          instantiate (1:= ptSh2Child); assumption.
          instantiate (1:= ptSh1Child); assumption.
          instantiate (1:= currentPart); assumption.
          subst.
          unfold consistency in *.
          unfold currentPartitionInPartitionsList in *.
          intuition.
          instantiate (1 := shadow2).
          subst.
          assumption.
          instantiate (1 := shadow1).
          subst.
          assumption.
          apply Hget1; trivial.
          assert(Hidx : StateLib.getIndexOfAddr shadow2 levelMin = idxSh2) by trivial.
          generalize (Hget1 idxSh2 Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
          apply Hget2; trivial.
          assert(Hidx : StateLib.getIndexOfAddr shadow1 levelMin = idxSh1) by trivial.
          generalize (Hget2 idxSh1 Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
          assumption.
          assert (presentSh2 = true).
          repeat rewrite andb_true_iff in Hlegit.
          intuition.
          subst.
          assumption.
          repeat rewrite andb_true_iff in Hlegit.
          intuition.
          subst.
          assumption.          
    + rewrite andAssocHT .
      apply permutHT.
      rewrite  <- andAssocHT.
      apply preAnd.
      eapply weaken.
      eapply initSndShadowPropagateProperties2.
      intros.
      simpl.
      destruct H0 as ((H0  & Hzero) & Hphypd).
      split.
      split;
      eassumption.
      unfold propagatedProperties in *.
      assert(Hget1 :forall idx : index,
        StateLib.getIndexOfAddr shadow2 levelMin = idx ->
        isPE ptSh2Child idx s /\ 
        getTableAddrRoot ptSh2Child idxPageDir currentPart shadow2 s) by intuition.
      assert(Hget2 : forall idx : index,
        StateLib.getIndexOfAddr pdChild levelMin = idx ->
        isPE ptPDChild idx s /\ 
        getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s) by intuition.
      intuition trivial.
      instantiate (1:= ptSh2Child); assumption.
      instantiate (1:= ptPDChild); assumption.
      instantiate (1:= currentPart); assumption.
      subst.
      unfold consistency in *.
      unfold currentPartitionInPartitionsList in *.
      intuition.
      instantiate (1 := shadow2).
      subst.
      assumption.
      instantiate (1 := pdChild).
      subst.
      assumption.
      apply Hget1; trivial.
      assert(Hidx : StateLib.getIndexOfAddr shadow2 levelMin = idxSh2) by trivial.
      generalize (Hget1 idxSh2 Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
      apply Hget2; trivial.
      assert(Hidx : StateLib.getIndexOfAddr pdChild levelMin = idxPDChild) by trivial.
      generalize (Hget2 idxPDChild Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
      assumption.
      assert (presentSh2 = true).
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.
      assumption.
      repeat rewrite andb_true_iff in Hlegit.
      intuition.
      subst.
      assumption. }

    intros []. simpl.
(** initConfigPagesList **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply initConfigPagesListPropagateProperties.
    intuition.
    eapply initConfigPagesListNewProperty.
    simpl; intros.
    split.
    rewrite <- and_assoc.
    split.
    repeat rewrite andb_true_iff in Hlegit.
    repeat rewrite and_assoc in Hlegit.
    destruct Hlegit as (H1 & _ & H2 & _ & H3 & _ & H4 & _ & H5 & _ ).
    subst.
    apply H0.
    intuition.
    subst.
    unfold CIndex.
    case_eq(lt_dec 0 tableSize);intros.
    simpl.
    unfold PeanoNat.Nat.Even.
    exists 0.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    intros.
    assert(PeanoNat.Nat.Even zero).
    { intuition. subst.
    unfold CIndex.
    case_eq(lt_dec 0 tableSize);intros.
    simpl.
    unfold PeanoNat.Nat.Even.
    exists 0.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia. }
    split;trivial.
    split;intros;intuition;subst.
    intuition.
    subst.
    unfold CIndex in H5.
    case_eq (lt_dec 0 tableSize).
    intros.
    rewrite H6 in H5.
    simpl in *. lia.
    intros.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.

    unfold CIndex in H5.
    case_eq (lt_dec 0 tableSize).
    intros.
    rewrite H6 in H5.
    simpl in *. lia.
    intros.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.

    intros [].
    simpl.
(** getDefaultVAddr **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getDefaultVAddr.
    intros.
    simpl.
    pattern s in H0.
    eapply H0.
    simpl.
    intros nullv.
(** getPRidx **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getPRidx.
    intros.
    simpl.
    pattern s in H0.
    eapply H0.
    simpl.
    intros idxPR.
(** getPDidx **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getPDidx.
    intros.
    simpl.
    repeat rewrite and_assoc in H0. 
    pattern s in H0.
    eapply H0.
    simpl.
    intros idxPD.
(** getSh1idx **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getSh1idx.
    intros.
    simpl.
    repeat rewrite and_assoc in H0. 
    pattern s in H0.
    eapply H0.
    simpl.
    intros idxSH1.
(** getSh2idx **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getSh2idx.
    intros.
    simpl.
    repeat rewrite and_assoc in H0. 
    pattern s in H0.
    eapply H0.
    simpl.
    intros idxSH2.
(** getSh3idx **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getSh3idx.
    intros.
    simpl.
    repeat rewrite and_assoc in H0. 
    pattern s in H0.
    eapply H0.
    simpl.
    intros idxSH3.
(** getPRPidx **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.getPPRidx.
    intros.
    simpl.
    repeat rewrite and_assoc in H0. 
    pattern s in H0.
    eapply H0.
    simpl.
    intros idxPPR.
(** updatePartitionDescriptor : add the partition descriptor itself *)
    eapply bindRev.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply updatePartitionDescriptorPropagatedProperties.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    eapply updatePartitionDescriptorNewProperty.
    simpl.
    intros.
    split.
    rewrite <- and_assoc.
    split.
    eassumption.
    trivial.
    simpl.
    instantiate(1:= ptRefChild).
    instantiate(1:= descChild).
    instantiate(1:=  idxRefChild).
    unfold propagatedProperties in *.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s) by intuition.
    intuition.
    apply Hget1; trivial.
    assert(Hidx : StateLib.getIndexOfAddr descChild levelMin = idxRefChild) by trivial.
    generalize (Hget1 idxRefChild Hidx);clear Hget1 ; intros (_ & Hhet1).
    subst. assumption.
    subst. assumption.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  idxPartDesc in Hcur.
    intuition.
    repeat right; trivial.
    assert (idxPR = idxPartDesc) by intuition.
    subst.
    unfold propagatedProperties in *.
    unfold consistency in *.
    assert (Hpde : partitionDescriptorEntry s) by intuition.
    unfold partitionDescriptorEntry in *.
    intuition.
    subst.
    assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
    unfold currentPartitionInPartitionsList in *. 
    intuition.
    apply Hpde with (currentPartition s) idxPartDesc   in Hcur.
    intuition.
    try repeat right; trivial.
    intros [].
(** updatePartitionDescriptor : add the page directory into the partition descriptor *)
    eapply WP.bindRev.
    eapply preAndPost.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply updatePartitionDescriptorPropagatedProperties.
    intuition.
    eapply updatePartitionDescriptorNewProperty.
    simpl.
    intros.
    split.
    split.
    destruct H0.
    eassumption.
    split.
    destruct H0.
    eassumption.
    instantiate(1:= ptRefChild).
    instantiate(1:= descChild).
    instantiate(1:=  idxRefChild).
    unfold propagatedProperties in *.
    intuition.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s) by intuition.
    intuition.
    apply Hget1; trivial.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s) by intuition.
    intuition.
    assert(Hidx : StateLib.getIndexOfAddr descChild levelMin = idxRefChild) by trivial.
    generalize (Hget1 idxRefChild Hidx);clear Hget1 ; intros (_ & Hhet1).
    subst. assumption.
    subst. assumption.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  idxPageDir in Hcur.
    intuition.
    left; trivial.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  idxPageDir in Hcur.
    intuition.
    left; trivial.
    simpl.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPD < tableSize - 1 /\ idxPR < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) idxPageDir   in Hcur.
      intuition.
      left; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) idxPartDesc   in Hcur.
      intuition.
      try repeat right; trivial. }
    destruct H0.
    destruct H0.
    destruct H0 as (H0 & _ & H4).
    intuition.

    assert(Hnoteq : idxPR <> idxPD).
    { subst.
      apply idxPRidxPDNotEq. }
    now contradict Hnoteq.
    subst.
    apply idxPRsucNotEqidxPD.  abstract lia.

    assert(Hnoteq : idxPR <> idxPD).

    { subst.  apply  idxPRidxPDNotEq. }
    subst.

    apply idxPDsucNotEqidxPR;trivial. abstract lia.
    simpl.
    intros [].
(** updatePartitionDescriptor : add the page directory into the partition descriptor *)
eapply WP.bindRev.
    eapply preAndPost.
        eapply preAndPost.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply updatePartitionDescriptorPropagatedProperties.
    intuition.
    eapply updatePartitionDescriptorNewProperty.
    simpl.
    intros.
    repeat rewrite and_assoc in H0.
    repeat rewrite and_assoc.
    destruct H0.
    destruct H1.
    split. 
    eapply H0.
    instantiate(1:= ptRefChild).
    instantiate(1:= descChild).
    instantiate(1:=  idxRefChild).
    instantiate(1:=  idxPPR).
    instantiate(1:= idxSH3).
    instantiate(1:= idxSH2).
    instantiate(1:=  idxSH1).
    instantiate(1:=  idxPD).
    instantiate(1:=  idxPR).
    instantiate(1:=  nullv).
    instantiate(1:=  zero).
    unfold propagatedProperties in *.
    intuition.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s) by intuition.
    intuition.
    apply Hget1; trivial.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s) by intuition.
    intuition.
    assert(Hidx : StateLib.getIndexOfAddr descChild levelMin = idxRefChild) by trivial.
    generalize (Hget1 idxRefChild Hidx);clear Hget1 ; intros (_ & Hhet1).
    subst. assumption.
    subst. assumption.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  idxShadow1 in Hcur.
    intuition.
    right;left; trivial.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s) idxShadow1  in Hcur.
    intuition.
    right; left; trivial.
    simpl.
    simpl.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPD < tableSize - 1 /\ idxSH1 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) idxPageDir   in Hcur.
      intuition.
      left; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxShadow1   in Hcur.
      intuition.
      right;left;trivial. }
    destruct H0.
    destruct H0.
    destruct H0 as (H0 &  H4).
    intuition.
    assert(Hnoteq : idxPD <> idxSH1).
    { subst. apply idxPDidxSh1notEq.  }
    now contradict Hnoteq.
    subst.
    apply idxPDsucNotEqidxSh1; abstract lia.
    assert(Hnoteq : idxPR <> idxPD).
    {  subst. apply idxPRidxPDNotEq. }
    subst.

    apply idxSh1succNotEqidxPD. abstract lia.
      eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPR < tableSize - 1 /\ idxSH1 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxPartDesc   in Hcur.
      intuition.
      repeat right ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxShadow1   in Hcur.
      intuition.
      right;left;trivial. }
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H0 as (H0 &  H5).
    intuition.
    assert(Hnoteq : idxPR <> idxSH1).
    { subst.  apply idxPRidxSh1NotEq. }
    now contradict Hnoteq.
    subst.
    apply idxPRsuccNotEqidxSh1.  abstract lia.

    assert(Hnoteq : idxPR <> idxSH1).
    { subst. apply idxPRidxSh1NotEq. }
    subst.

    apply idxSh1succNotEqidxPR;trivial.
    simpl.
    intros [].
(** updatePartitionDescriptor : add the page directory into the partition descriptor *)
    eapply WP.bindRev.
    eapply preAndPost.
    eapply preAndPost.
    eapply preAndPost.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply updatePartitionDescriptorPropagatedProperties.
    intuition.
    eapply updatePartitionDescriptorNewProperty.
    simpl.
    intros.
    repeat rewrite and_assoc in H0.
    repeat rewrite and_assoc.
    destruct H0.
    destruct H1.
    split.
    eapply H0.
    instantiate(1:= ptRefChild).
    instantiate(1:= descChild).
    instantiate(1:=  idxRefChild).
    instantiate(1:=  idxPPR).
    instantiate(1:= idxSH3).
    instantiate(1:= idxSH2).
    instantiate(1:=  idxSH1).
    instantiate(1:=  idxPD).
    instantiate(1:=  idxPR).
        instantiate(1:=  nullv).
    instantiate(1:=  zero).
    unfold propagatedProperties in *.
    intuition.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s) by intuition.
    intuition.
    apply Hget1; trivial.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s) by intuition.
    intuition.
    assert(Hidx : StateLib.getIndexOfAddr descChild levelMin = idxRefChild) by trivial.
    generalize (Hget1 idxRefChild Hidx);clear Hget1 ; intros (_ & Hhet1).
    subst. assumption.
    subst. assumption.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  idxShadow2 in Hcur.
    subst.
    intuition.
    right;right;left; trivial.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s) idxShadow2  in Hcur.
    intuition.
    right;right; left; trivial.
    simpl.
    simpl.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH2 < tableSize - 1 /\ idxSH1 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxShadow2   in Hcur.
      intuition.
      right;right;left; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxShadow1   in Hcur.
      intuition.
      right;left;trivial. }
    destruct H0.
    destruct H0.
     destruct H0 as (H0 &  H4).
    intuition.
    assert(Hnoteq : idxSH2 <> idxSH1).
    { subst.
      apply idxSh2idxSh1notEq.  }
    now contradict Hnoteq.
    subst.
 apply idxSh1succNotEqidxSh2; trivial.
    assert(Hnoteq : idxSH1 <> idxSH2).
    { subst.
   symmetrynot.    apply idxSh2idxSh1notEq. }

    subst.

    apply idxSh2succNotEqidxSh1;trivial.

      eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH2 < tableSize - 1 /\ idxPD < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxShadow2   in Hcur.
      intuition.
      right;right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxPageDir   in Hcur.
      intuition.
      left;trivial. }
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H0 as (H0 &  H5).
    intuition.
    assert(Hnoteq : idxPD <> idxSH2).
    { subst.  apply idxPDidxSh2notEq.  }
    now contradict Hnoteq.
    subst.
    apply idxPDsucNotEqidxSh2;trivial.

    assert(Hnoteq : idxPD <> idxSH2).
    { subst. apply idxPDidxSh2notEq. }
    subst.
    apply idxSh2succNotEqidxPD;trivial.
          eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH2 < tableSize - 1 /\ idxPR < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxShadow2   in Hcur.
      intuition.
      right;right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxPartDesc   in Hcur.
      intuition.
      repeat right;trivial. }
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H0.

    destruct H0 as (H0 & _ & H6).
    intuition.
    assert(Hnoteq : idxPR <> idxSH2).
    { subst. 
    apply idxPRidxSh2NotEq. }
    now contradict Hnoteq.
    subst.

    apply idxPRsuccNotEqidxSh2; trivial.
    assert(Hnoteq : idxPR <> idxSH2).
    { subst. apply idxPRidxSh2NotEq. }
    subst.
    apply idxSh2succNotEqidxPR;trivial.
    simpl; intros [].
    (** updatePartitionDescriptor : add the config list into the partition descriptor *)
    eapply WP.bindRev.
    eapply preAndPost.
    eapply preAndPost.
    eapply preAndPost.
    eapply preAndPost.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply updatePartitionDescriptorPropagatedProperties.
    intuition.
    eapply updatePartitionDescriptorNewProperty.
    simpl.
    intros.
    repeat rewrite and_assoc in H0.
    repeat rewrite and_assoc.
    destruct H0.
    destruct H1.
    split.
    eapply H0.
    instantiate(1:= ptRefChild).
    instantiate(1:= descChild).
    instantiate(1:=  idxRefChild).
    instantiate(1:=  idxPPR).
    instantiate(1:= idxSH3).
    instantiate(1:= idxSH2).
    instantiate(1:=  idxSH1).
    instantiate(1:=  idxPD).
    instantiate(1:=  idxPR).
       instantiate(1:=  nullv).
    instantiate(1:=  zero).
    unfold propagatedProperties in *.
    intuition.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s) by intuition.
    intuition.
    apply Hget1; trivial.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s) by intuition.
    intuition.
    assert(Hidx : StateLib.getIndexOfAddr descChild levelMin = idxRefChild) by trivial.
    generalize (Hget1 idxRefChild Hidx);clear Hget1 ; intros (_ & Hhet1).
    subst. assumption.
    subst. assumption.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  idxShadow3 in Hcur.
    subst.
    intuition.
    do 3 right;left; trivial.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s) idxShadow3  in Hcur.
    intuition.
    do 3 right; left; trivial.
    simpl.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH2 < tableSize - 1 /\ idxSH3 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) idxShadow2   in Hcur.
      intuition.
      right;right;left; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxShadow3   in Hcur.
      intuition.
      do 3 right;left;trivial. }
    destruct H0.
    destruct H0.

    destruct H0 as (H0 &  H4).
    intuition.
    assert(Hnoteq : idxSH2 <> idxSH3).
    { subst.  apply idxSh2idxSh3notEq. }
    now contradict Hnoteq.
    subst.
    apply idxSh2succNotEqidxSh3; assumption. 
    assert(Hnoteq : idxSH3 <> idxSH2).
    { subst. symmetrynot. apply idxSh2idxSh3notEq. }
    subst.
 apply idxSh3succNotEqidxSh2;trivial.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH1 < tableSize - 1 /\ idxSH3 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxShadow1   in Hcur.
      intuition.
      right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxShadow3   in Hcur.
      intuition.
      do 3 right;left;trivial. }
    destruct H0.
    destruct H0.
    destruct H0.

    destruct H0 as (H0 &  H5).
    intuition.
    assert(Hnoteq : idxSH1 <> idxSH3).
    { subst.
     apply idxSh1idxSh3notEq. }
    now contradict Hnoteq.
    subst.
     apply sh1idxSh3idxNotEq ; trivial.
    assert(Hnoteq : idxSH3 <> idxSH1).
    { subst. symmetrynot. apply idxSh1idxSh3notEq. }
    subst.
 apply idxSh3succNotEqidxSh1;trivial.
          eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH3 < tableSize - 1 /\ idxPD < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxShadow3   in Hcur.
      intuition.
      do 3 right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxPageDir   in Hcur.
      intuition.
      left;trivial. }
    do 4 destruct H0.

    destruct H0 as (H0 &  H6).
    intuition.
    assert(Hnoteq : idxPD <> idxSH3).
    { subst.
       apply idxPDidxSh3notEq. }
    now contradict Hnoteq.
    subst.
 apply idxPDsucNotEqidxSh3;trivial.
    assert(Hnoteq : idxSH3 <> idxPD).
    { subst. symmetrynot. apply idxPDidxSh3notEq. }
    subst.
 apply idxSh3succNotEqidxPDidx;trivial.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxSH3 < tableSize - 1 /\ idxPR < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) idxShadow3   in Hcur.
      intuition.
      do 3 right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) idxPartDesc in Hcur.
      intuition.
      repeat right;trivial. }
    do 5 destruct H0.
    destruct H0 as (H0 &  H7).
    intuition.
    assert(Hnoteq : idxPR <> idxSH3).
    { subst.
       apply idxPRidxSh3NotEq.
      }
    now contradict Hnoteq.
    subst.
    apply idxPRsuccNotEqidxSh3;trivial.
    assert(Hnoteq : idxSH3 <> idxPR).
    { subst. symmetrynot. apply idxPRidxSh3NotEq. }
    subst.

    apply idxSh3succNotEqPRidx;trivial.
simpl.
intros [].
      (** updatePartitionDescriptor : add the config list into the partition descriptor *)
    eapply WP.bindRev.
    eapply preAndPost.
    eapply preAndPost.
    eapply preAndPost.
    eapply preAndPost.
    eapply preAndPost.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply updatePartitionDescriptorPropagatedProperties.
    intuition.
    eapply updatePartitionDescriptorNewProperty.
    simpl.
    intros.
    repeat rewrite and_assoc in H0.
    repeat rewrite and_assoc.
    destruct H0.
    destruct H1.
    split.
    eapply H0.
    instantiate(1:= ptRefChild).
    instantiate(1:= descChild).
    instantiate(1:=  idxRefChild).
    instantiate(1:=  idxPPR).
    instantiate(1:= idxSH3).
    instantiate(1:= idxSH2).
    instantiate(1:=  idxSH1).
    instantiate(1:=  idxPD).
    instantiate(1:=  idxPR).
       instantiate(1:=  nullv).
    instantiate(1:=  zero).
    unfold propagatedProperties in *.
    intuition.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s) by intuition.
    intuition.
    apply Hget1; trivial.
    assert(Hget1 :forall idx : index,
                  StateLib.getIndexOfAddr descChild levelMin = idx ->
                  isPE ptRefChild idx s /\ 
                  getTableAddrRoot ptRefChild idxPageDir currentPart descChild s) by intuition.
    intuition.
    assert(Hidx : StateLib.getIndexOfAddr descChild levelMin = idxRefChild) by trivial.
    generalize (Hget1 idxRefChild Hidx);clear Hget1 ; intros (_ & Hhet1).
    subst. assumption.
    subst. assumption.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s)  idxParentDesc in Hcur.
    subst.
    intuition.
    do 4 right;left; trivial.
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    subst.
    assert (Hpde : partitionDescriptorEntry s) by trivial.
    unfold  partitionDescriptorEntry in *.
    assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
    unfold currentPartitionInPartitionsList in *.
    intuition.
    apply Hpde with (currentPartition s) idxParentDesc  in Hcur.
    intuition.
    do 4 right; left; trivial.
    simpl.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPPR < tableSize - 1 /\ idxSH3 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxParentDesc   in Hcur.
      intuition.
      do 4 right ;left; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxShadow3   in Hcur.
      intuition.
      do 3 right;left;trivial. }
    do 2 destruct H0.
    destruct H0 as (H0 &  H4).
    intuition.
    assert(Hnoteq : idxPPR <> idxSH3).
    { subst. apply idxPPRidxSh3NotEq.  }
    now contradict Hnoteq.
    subst.
    apply idxSh3succNotEqPPRidx;trivial.
    assert(Hnoteq : idxSH3 <> idxPPR).
    { subst.  symmetrynot. apply idxPPRidxSh3NotEq. }
    subst.
apply idxPPRsuccNotEqidxSh3;trivial.
      eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPPR < tableSize - 1 /\ idxSH2 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) idxParentDesc   in Hcur.
      intuition.
      do 4 right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) idxShadow2   in Hcur.
      intuition.
      do 2 right;left;trivial. }
        do 3 destruct H0.
    destruct H0 as (H0 &  H5).
    intuition.
    assert(Hnoteq : idxSH2 <> idxPPR).
    { subst. 
      apply idxSh2idxPPRnotEq;trivial.  }
    now contradict Hnoteq.
    subst.
apply idxSh2succNotEqidxPPR;trivial.
    assert(Hnoteq : idxPPR <> idxSH2).
    { subst.   apply idxPPRidxSh2NotEq. }
    subst.
apply idxPPRsuccNotEqidxSh2;trivial.
          eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPPR < tableSize - 1 /\ idxSH1 < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) idxParentDesc   in Hcur.
      intuition.
      do 4 right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) idxShadow1   in Hcur.
      intuition.
      right;left;trivial. }
        do 4 destruct H0.
    destruct H0 as (H0 &  H6).

    intuition.

    assert(Hnoteq : idxSH1 <> idxPPR).
    { subst.  apply idxSh1idxPPRnotEq.  }
    now contradict Hnoteq.
    subst.

    apply idxSh1succNotEqidxPPR;trivial.
    assert(Hnoteq : idxPPR <> idxSH1).
    { subst.    apply idxPPRidxSh1NotEq.  }
    subst.
    apply idxPPRsuccNotEqidxSh1;trivial.
              eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPPR < tableSize - 1 /\ idxPD < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxParentDesc   in Hcur.
      intuition.
      do 4 right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *.
      intuition.
      apply Hpde with (currentPartition s) idxPageDir in Hcur.
      intuition.
      left;trivial. }
       do 5 destruct H0.
    destruct H0 as (H0 &  H7).

    intuition.
    assert(Hnoteq : idxPD <> idxPPR).
    { subst. apply idxPDidxPPRNotEq.  }
    now contradict Hnoteq.
    subst.
 apply idxPDsucNotEqidxPPR;trivial.
    assert(Hnoteq : idxPPR <> idxPD).
    { subst. 
      apply idxPPRidxPDNotEq. }
    subst.
    apply idxPPRsuccNotEqidxPD;trivial.
    eapply weaken.
    apply updatePartitionDescriptorPropagatedProperties2.
    simpl.
    intros.
    assert(idxPPR < tableSize - 1 /\ idxPR < tableSize - 1).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      assert (Hpde : partitionDescriptorEntry s) by intuition.
      unfold partitionDescriptorEntry in *.
      intuition.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) idxParentDesc   in Hcur.
      intuition.
      do 4 right;left ; trivial.
      subst.
      assert (Hcur : In (currentPartition s) (getPartitions pageRootPartition s)).
      unfold currentPartitionInPartitionsList in *. 
      intuition.
      apply Hpde with (currentPartition s) idxPartDesc in Hcur.
      intuition.
      repeat right;trivial. }
       do 6 destruct H0.
    destruct H0 as (H0 &  H8).
    intuition.
    assert(Hnoteq : idxPR <> idxPPR).
    { subst. apply idxPRidxPPRNotEq.  }
    now contradict Hnoteq.
    subst.

    apply idxPRsucNotEqidxPPR;trivial.
    assert(Hnoteq : idxPPR <> idxPR).
    { subst. symmetrynot. apply idxPRidxPPRNotEq. }
    subst.
    apply idxPPRsuccNotEqidxPR;trivial.
    simpl.
    intros [].

(**  writeVirEntry **)
    eapply bindRev.
     eapply weaken.
    eapply writeVirEntryPD;trivial.
    eapply H.
    intros.
    simpl.
    repeat rewrite and_assoc  in H0.
    destruct H0.
    split.
   unfold propagatedProperties in *.
   eassumption.
   unfold newPropagatedProperties.
    assert( initConfigPagesListPostCondition phyConfigPagesList s) as (Hi1 & Hi2 & Hi3 & Hi4) by intuition.
   intuition; try eassumption;subst;trivial.
 intros [].
 (**  writeVirEntry **)
    eapply bindRev.
    eapply weaken.
    eapply writeVirEntrySh1;trivial.
    eapply H.
    intros.
    simpl.
    repeat rewrite and_assoc  in H0.
    destruct H0.
    split.
   unfold propagatedProperties in *.
   eassumption.
   eapply H1.
 intros [].
 (**  writeVirEntry **)
    eapply bindRev.
    eapply weaken.
    eapply writeVirEntrySh2;trivial.
    eapply H.
    intros.
    simpl.
    repeat rewrite and_assoc  in H0.
    destruct H0.
    split.
   unfold propagatedProperties in *.
   eassumption.
   eapply H1.
 intros [].
 (**  writeVirEntry **)
    eapply bindRev.
    eapply weaken.
    eapply writeVirEntryList;trivial.
    eapply H.
    intros.
    simpl.
    repeat rewrite and_assoc  in H0.
    destruct H0.
    split.
   unfold propagatedProperties in *.
   eassumption.
   eapply H1.
 intros [].
(**  writePDflag **)
eapply WP.bindRev.
eapply weaken.
eapply WP.writePDflag.
simpl.
intros. 
assert(Hget : forall idx : index,
          StateLib.getIndexOfAddr descChild levelMin = idx ->
          isVE ptRefChildFromSh1 idx s /\
          getTableAddrRoot ptRefChildFromSh1 idxShadow1 currentPart descChild s).
{
unfold propagatedProperties in *.
unfold newPropagatedProperties in *.  intuition. }
assert (Hve :isVE ptRefChildFromSh1 idxRefChild s).
{
unfold propagatedProperties in *.
unfold newPropagatedProperties in *. 
apply Hget.
intuition. }
unfold isVE in Hve.
case_eq( lookup ptRefChildFromSh1 idxRefChild (memory s) pageEq idxEq);
intros; rewrite H1 in *; try now contradict Hve.
case_eq v ; intros;rewrite H2 in *; try now contradict Hve.
exists v0;split;trivial.
subst.
instantiate(1:= fun _ s =>  partitionsIsolation s /\
kernelDataIsolation s /\
verticalSharing s /\
consistency s).
simpl.

    apply createPartitionPostcondition with 
    pdChild
currentPart currentPD level ptRefChild descChild ptPDChild idxPDChild ptSh1Child shadow1 idxSh1 ptSh2Child
shadow2 idxSh2 ptConfigPagesList idxConfigPagesList currentShadow1 derivedRefChild ptPDChildSh1 ptSh1ChildFromSh1
childSh2 childListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild ;intuition;subst;trivial.
   intros []. 
   eapply WP.weaken. eapply WP.ret .
   simpl. intuition.
 - intros HNotlegit. 
   eapply WP.weaken. eapply WP.ret .
   simpl. intuition.
      }
      intros. eapply WP.weaken. eapply WP.ret .
      simpl. intuition.
      intros. eapply WP.weaken. eapply WP.ret .
      simpl. intuition.
Qed.
