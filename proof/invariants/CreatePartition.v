(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2016)                 *)
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
Require Import Model.ADT Model.Hardware Core.Services Isolation
Consistency Invariants WeakestPreconditions Model.Lib StateLib
Model.MAL InitPEntryTable DependentTypeLemmas GetTableAddr 
WriteAccessible WriteAccessibleRec WritePhyEntry InternalLemmas  
InitConfigPagesList Lib.
 Require Import Omega Bool  Coq.Logic.ProofIrrelevance List.

Lemma createPartition (descChild pdChild shadow1 shadow2 list : vaddr) :
{{fun s => partitionsIsolation s  /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }} 
createPartition descChild pdChild shadow1 shadow2 list  
{{fun _ s  => partitionsIsolation s  /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold createPartition.
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
case_eq (negb a && negb a0 && negb a1 && negb a2 && negb a3).
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
      instantiate (1:= PDidx).
      split. intuition.
      destruct H as ( _ & _ & _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd ).
      exists currentPD.
      split. assumption.
      split.
      unfold consistency in *.
      destruct Hcons as (Hpd & _ & _ &_  & Hpr  & _). 
      unfold partitionDescriptorEntry in Hpd.
      unfold currentPartitionInPartitionsList in *.
      subst.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx\/ PDidx = sh3idx \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
      by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | now contradict Hrootpd | 
       subst ; assumption| now contradict Hrootpd| now contradict Hrootpd ]  |now contradict Hrootpd] | now contradict Hrootpd].
      subst. 
      left. 
      split;trivial.
      intro ptRefChild. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert( (getTableAddrRoot' ptRefChild PDidx currentPart descChild s /\   ptRefChild = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr descChild fstLevel = idx ->
      isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s)).
      { 
      destruct H1 as [H1 |H1].
      + left. trivial. 
      + right. intros idx Hidx.
        destruct H1 as (Hget  & Hnew & H1).
        split. 
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse.
           unfold PDidx. unfold sh1idx.
           apply indexEqFalse ;
           assert (tableSize > tableSizeLowerBound).
           apply tableSizeBigEnough.
           unfold tableSizeLowerBound in *.
           omega.  apply tableSizeBigEnough.
           unfold tableSizeLowerBound in *.
           omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh2idx.
         apply indexEqFalse;
         assert (tableSize > tableSizeLowerBound).
         apply tableSizeBigEnough.
         unfold tableSizeLowerBound in *.
         omega.  apply tableSizeBigEnough.
         unfold tableSizeLowerBound in *.
         omega. apply tableSizeBigEnough. omega.
      -
       assumption.
     - assumption.  } 
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP.
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
         StateLib.getIndexOfAddr descChild fstLevel = idx -> isPE ptRefChild idx s/\ getTableAddrRoot ptRefChild PDidx currentPart descChild s).  
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
      instantiate (1:= currentPart). intuition. subst. unfold consistency in *. 
      unfold  currentPartitionInPartitionsList in *. intuition.
      instantiate (1:= PDidx).
      split. intuition.
       destruct H as ( _ & _ & _& Hcons  & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H).
      exists currentPD.
      split. assumption.
      split.
      unfold consistency in *.
      destruct Hcons as (Hpd & _ & _ &_  & Hpr  & _). 
      unfold partitionDescriptorEntry in Hpd.
      unfold currentPartitionInPartitionsList in *.
      subst.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/PDidx = sh3idx \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
      by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | now contradict Hrootpd | 
       subst ; assumption| now contradict Hrootpd| now contradict Hrootpd ]  |now contradict Hrootpd] | now contradict Hrootpd].

      subst. left. split;trivial.
           intro ptPDChild. simpl. 
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert( (getTableAddrRoot'  ptPDChild PDidx currentPart pdChild s /\    ptPDChild = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
      isPE  ptPDChild idx s /\ getTableAddrRoot ptPDChild  PDidx currentPart pdChild s)).
      { 
      destruct H1 as [H1 |H1].
      + left. trivial. 
      + right. intros idx Hidx.
      
        destruct H1 as (Hget  & Hnew & H1).

        split. 
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse.
         
       unfold PDidx. unfold sh1idx.
       apply indexEqFalse ;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh2idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
      -
       assumption.
     - assumption.  } 
    assert (HP := conj H0 H).

        pattern s in HP.
        eapply HP.      
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
         StateLib.getIndexOfAddr pdChild fstLevel = idx -> isPE ptPDChild idx s
         /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s).  
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
      instantiate (1:= PDidx).
      split. intuition.
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).
      exists currentPD.
      split. intuition.
      split.
      unfold consistency in *.
      destruct Hcons as (Hpd & _ & _ &_  & Hpr  & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx\/PDidx = sh3idx\/ PDidx = PPRidx \/ PDidx = PRidx ) as Htmp
          by auto.
      subst.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.     
       generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | now contradict Hrootpd | 
       subst ; assumption| now contradict Hrootpd| now contradict Hrootpd ]  |now contradict Hrootpd] | now contradict Hrootpd].

      subst. left. split;intuition.
     intro ptSh1Child. simpl.

 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert(( getTableAddrRoot' ptSh1Child PDidx currentPart shadow1 s /\  ptSh1Child = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
      isPE ptSh1Child idx s/\
     getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s)).
      {
      destruct H1 as [H1 |(Hnew & Hi & H1)].
      + left. trivial. 
      + right. intros idx Hidx.
      
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse.
         
       unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh2idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
      -split;
       assumption. }
       
       assert (HP := conj H0 H).
       pattern s in HP.
       eapply HP.   
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
         StateLib.getIndexOfAddr shadow1 fstLevel = idx -> isPE ptSh1Child idx s /\
     getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s).  
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
      instantiate (1:= PDidx).
      split. intuition.
      
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & 
      b_ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H).
      exists currentPD.
      split. intuition.
      split.
      unfold consistency in *.
             destruct Hcons as (Hpd & _ & _ &_  & Hpr  & _). 
      unfold partitionDescriptorEntry in Hpd.
       assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx\/PDidx = sh3idx\/ PDidx = PPRidx \/ PDidx = PRidx ) as Htmp 
          by auto.
          subst.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | now contradict Hrootpd | 
       subst ; assumption| now contradict Hrootpd| now contradict Hrootpd ]  |now contradict Hrootpd] | now contradict Hrootpd].
      subst. left. split;intuition.
      intro ptSh2Child. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert( ( getTableAddrRoot' ptSh2Child PDidx currentPart shadow2 s /\ ptSh2Child = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
      isPE ptSh2Child idx s/\
     getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s)).
      {
      destruct H1 as [H1 |(Hi  & Hnew & H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse.
         
       unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh2idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
      - split;
       assumption. }
       assert (HP := conj H0 H).
       pattern s in HP.
       eapply HP.  
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
         StateLib.getIndexOfAddr shadow2 fstLevel = idx -> isPE ptSh2Child idx s /\
     getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s).  
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
      instantiate (1:= PDidx).
      split. intuition.
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).

      exists currentPD.
      split. intuition.
      split.
      unfold consistency in *.
      destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx\/ PDidx = sh3idx
       \/ PDidx = PPRidx \/ PDidx = PRidx) as Htmp 
      by auto.
            generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | now contradict Hrootpd | 
       subst ; assumption| now contradict Hrootpd| now contradict Hrootpd ]  |now contradict Hrootpd] | now contradict Hrootpd].

      subst. left. split;intuition.
      intro ptConfigPagesList. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
       assert( ( getTableAddrRoot' ptConfigPagesList PDidx currentPart list s /\ ptConfigPagesList = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr list fstLevel = idx ->
      isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s)).
      {
      destruct H1 as [H1 |(Hi & Hi1 &H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(_& Hfalse) | [(_&Hfalse) |(Hpe &Htrue)]].
        - contradict Hfalse.
         
       unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh2idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
      - split;
       assumption. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP.
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
         StateLib.getIndexOfAddr list fstLevel = idx -> isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s).  
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
      instantiate (1:= sh1idx).
      split. intuition. (*
      destruct H as ( (_ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& 
      _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H) & H0). *)
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.
      destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx 
      \/  sh1idx  = sh3idx \/ sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.     
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh1idx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | 
       now contradict Hrootpd | 
       subst;assumption | now contradict Hrootpd| now contradict Hrootpd ]  
       |now contradict Hrootpd] | now contradict Hrootpd].
      subst. left. split;intuition.
      intro ptRefChildFromSh1.
      simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert ( (getTableAddrRoot' ptRefChildFromSh1 sh1idx currentPart descChild s /\ ptRefChildFromSh1 = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr descChild fstLevel = idx ->
      isVE ptRefChildFromSh1 idx s /\  getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)).
      { destruct H1 as [H1 |(Hi & Hi1 & H1 )].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
        - contradict Hfalse.
         
       unfold sh2idx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP. 
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
          assert ( StateLib.getIndexOfAddr descChild fstLevel = idxRefChild) as Hidxchild.
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
      instantiate (1:= sh1idx).
      split. intuition.
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
      (*
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).
      assert (nextEntryIsPP currentPart sh1idx currentShadow1 s ). intuition. *)
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.

        destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/  sh1idx  = sh3idx
      \/  sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.     
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh1idx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | 
       now contradict Hrootpd | 
       subst;assumption | now contradict Hrootpd| now contradict Hrootpd ]  
       |now contradict Hrootpd] | now contradict Hrootpd].
      subst. left. split;intuition.
      intro ptPDChildSh1. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
          
      assert (  (getTableAddrRoot' ptPDChildSh1 sh1idx currentPart pdChild s /\ ptPDChildSh1 = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
      isVE ptPDChildSh1 idx s /\
     getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s )).
      { destruct H1 as [H1 |( Hi & Hi1  &H1 )].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
        - contradict Hfalse.
          unfold sh2idx. unfold sh1idx.
          apply indexEqFalse;
          assert (tableSize > tableSizeLowerBound).
          apply tableSizeBigEnough.
          unfold tableSizeLowerBound in *.
          omega.  apply tableSizeBigEnough.
          unfold tableSizeLowerBound in *.
          omega. apply tableSizeBigEnough. omega.
           - contradict Hfalse.
             unfold PDidx. unfold sh1idx.
             apply indexEqFalse;
             assert (tableSize > tableSizeLowerBound).
             apply tableSizeBigEnough.
             unfold tableSizeLowerBound in *.
             omega.  apply tableSizeBigEnough.
             unfold tableSizeLowerBound in *.
             omega. apply tableSizeBigEnough. omega. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP.
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
          assert ( StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild) as Hidxchild.
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
      instantiate (1:= sh1idx).
      split. intuition.
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
      (*
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ & _ 
      & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).
      assert (nextEntryIsPP currentPart sh1idx currentShadow1 s ). intuition. *)
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.
        destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/  sh1idx  = sh3idx
      \/  sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.     
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh1idx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | 
       now contradict Hrootpd | 
       subst;assumption | now contradict Hrootpd| now contradict Hrootpd ]  
       |now contradict Hrootpd] | now contradict Hrootpd].
      subst. left. split;intuition.
      intro ptSh1ChildFromSh1. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert ( (getTableAddrRoot' ptSh1ChildFromSh1 sh1idx currentPart shadow1 s /\  ptSh1ChildFromSh1 = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
      isVE ptSh1ChildFromSh1 idx s /\ getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s)).
      { destruct H1 as [H1 |(Hi & Hi1 &H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
        - contradict Hfalse.
         
       unfold sh2idx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP.
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
          assert ( StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1) as Hidxchild.
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
      instantiate (1:= sh1idx).
      split. intuition.
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
      (*
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& _ & _ 
      & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H).
      assert (nextEntryIsPP currentPart sh1idx currentShadow1 s ). intuition.*)
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.
              destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/  sh1idx  = sh3idx
      \/  sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.     
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh1idx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | 
       now contradict Hrootpd | 
       subst;assumption | now contradict Hrootpd| now contradict Hrootpd ]  
       |now contradict Hrootpd] | now contradict Hrootpd].
      subst. left. split;intuition.
      intro childSh2. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert (  (getTableAddrRoot' childSh2 sh1idx currentPart shadow2 s /\ childSh2 = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
      isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s )).
      { destruct H1 as [H1 |(Hi & Hi1 &H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
        - contradict Hfalse.
         
       unfold sh2idx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP.
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
          assert ( StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2) as Hidxchild.
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
      instantiate (1:= sh1idx).
      split. intuition.
      assert(Hcons : consistency s) by intuition.
      assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
      assert (Hrootpd : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
      assert(Hcp : currentPart = currentPartition s) by intuition.
      assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
      (*
      destruct H as ( _ & _& _ & Hcons & Hlevel  & _ & _ & _ &_ & _& 
      _ & _ & _ & _ &_ & _ & _ & _ &_ & _& Hcp & Hrootpd & H ).
      assert (nextEntryIsPP currentPart sh1idx currentShadow1 s ). intuition. *)
      exists currentShadow1.
      split. intuition.
      unfold consistency in *.
      
              destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
      unfold partitionDescriptorEntry in Hpd.
      assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/  sh1idx  = sh3idx
      \/  sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
      by auto.
          generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
      generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry). 
      destruct Hentry as (page1 & Hpd & Hnotnull).
      subst.
      split.     
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh1idx);
       [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootpd | 
       now contradict Hrootpd | 
       subst;assumption | now contradict Hrootpd| now contradict Hrootpd ]  
       |now contradict Hrootpd] | now contradict Hrootpd].
      subst. left. split;intuition.
      intro childListSh1. simpl.
 (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert ( (getTableAddrRoot' childListSh1 sh1idx currentPart list s /\ childListSh1 = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr list fstLevel = idx ->
      isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 sh1idx currentPart list s  )).
      { destruct H1 as [H1 |(Hi & Hi1 & H1)].
      + left. trivial. 
      + right. intros idx Hidx.
        generalize (H1 idx Hidx);clear H1;intros H1.
        destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
        - split; assumption.
        - contradict Hfalse.
         
       unfold sh2idx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega.
       - contradict Hfalse.
          unfold PDidx. unfold sh1idx.
       apply indexEqFalse;
       assert (tableSize > tableSizeLowerBound).
       apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega.  apply tableSizeBigEnough.
       unfold tableSizeLowerBound in *.
       omega. apply tableSizeBigEnough. omega. }
    assert (HP := conj H0 H).
    pattern s in HP.
    eapply HP.
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
          assert ( StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList) as Hidxchild.
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
      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
      isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by intuition.
    apply Hpe.
    intuition.
    simpl.
    intros phyPDChild.
(** comparePageToNull **) 
    eapply WP.bindRev.
    eapply Invariants.comparePageToNull.
    intro phyPDChildIsnull.
    simpl.
    case_eq phyPDChildIsnull.
    { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
    intros phyPDChildNotNull.    
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split. 
    assert(Hphy : forall partition, In partition (getPartitions multiplexer s) ->
    ~ In phyPDChild (getConfigPages partition s) ).
    { intros. try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as (_ & _ & presentPD & accessPD & _).
       unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial. 
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptPDChild pdChild idxPDChild 
      accessiblePDChild level presentPDChild currentPD; subst; intuition.
    }
    assert(Hnew := conj H0 Hphy).    
    pattern s in Hnew.
    eapply Hnew. 
    subst.
    unfold propagatedProperties in *.
    assert (Hpe : forall idx : index,
                   StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                   isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx 
                   currentPart shadow1 s) by intuition.
    apply Hpe.
    intuition.
    simpl.
    intros phySh1Child.
(** comparePageToNull **) 
    eapply WP.bindRev.
    eapply Invariants.comparePageToNull.
    intro phySh1ChildIsnull.
    simpl.
    case_eq phySh1ChildIsnull.
    { intros.
      eapply WP.weaken.
      eapply WP.ret .
      simpl.
      intros.
      intuition. }
    intros phySh1ChildNotNull.
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split.
    assert(Hphy : forall partition, In partition (getPartitions multiplexer s) -> 
    ~ In phySh1Child  (getConfigPages partition s) ).
    { intros. try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as (_ & _ & _ & _ & _ & _ &  presentPD & accessPD & _).
      unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial.
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptSh1Child shadow1 idxSh1 accessibleSh1
       level presentSh1 currentPD ; subst;intuition . }
    assert(Hnew := conj H0 Hphy).    
    pattern s in Hnew.
    eapply Hnew. 
    subst.
    unfold propagatedProperties in *.
    assert (Hpe : forall idx : index,
                     StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                     isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child 
                     PDidx currentPart shadow2 s) by intuition.
    apply Hpe.
    intuition. 
    simpl.
    intros phySh2Child.
(** comparePageToNull **) 
    eapply WP.bindRev.
    eapply Invariants.comparePageToNull.
    intro phySh2ChildIsnull.
    simpl.
    case_eq phySh2ChildIsnull.
    { intros.
      eapply WP.weaken.
      eapply WP.ret .
      simpl.
      intros.
      intuition. }
    intros phySh2ChildNotNull.
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split.
    assert(Hphy : forall partition, In partition (getPartitions multiplexer s) ->
    ~ In phySh2Child (getConfigPages partition s)).
    { intros. try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as (_ & _ & _ & _ & _ & _ & _ & _ &  presentPD & accessPD ).
      unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial.
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptSh2Child shadow2 idxSh2 accessibleSh2
       level presentSh2 currentPD ; subst;intuition. }
    assert(Hnew := conj H0 Hphy).    
    pattern s in Hnew.
    eapply Hnew. 
    subst.
    unfold propagatedProperties in *.
    assert (Hpe : forall idx : index,
                       StateLib.getIndexOfAddr list fstLevel = idx ->
                       isPE ptConfigPagesList idx s /\
                       getTableAddrRoot ptConfigPagesList PDidx currentPart list s) 
    by intuition.
    apply Hpe.
    intuition.
    simpl.
    intros phyConfigPagesList.
(** comparePageToNull **) 
    eapply WP.bindRev.
    eapply Invariants.comparePageToNull.
    intro phyConfigPagesListIsnull.
    simpl.
    case_eq phyConfigPagesListIsnull.
    { intros.
      eapply WP.weaken.
      eapply WP.ret .
      simpl.
      intros.
      intuition. }
    intros phyConfigPagesListNotNull.
(** readPhyEntry **)
    eapply WP.bindRev.
    eapply WP.weaken.  
    eapply Invariants.readPhyEntry.
    simpl. intros.
    split.
    assert(Hphy : forall partition, In partition (getPartitions multiplexer s) ->
    ~ In phyConfigPagesList (getConfigPages partition s)).
    { intros. try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as (_ & _ & _ & _ & presentPD & accessPD & _ ).
       unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial.
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptConfigPagesList list idxConfigPagesList 
      accessibleList level presentConfigPagesList currentPD; subst;intuition. }
    assert(Hnew := conj H0 Hphy).    
    pattern s in Hnew.
    eapply Hnew. 
    subst.
    unfold propagatedProperties in *.
    assert (Hpe : forall idx : index,
                         StateLib.getIndexOfAddr descChild fstLevel = idx ->
                         isPE ptRefChild idx s /\
                         getTableAddrRoot ptRefChild PDidx currentPart descChild s)
    by intuition.
    apply Hpe.
    intuition.
    simpl.
    intros phyDescChild.
(** comparePageToNull **) 
    eapply WP.bindRev.
    eapply Invariants.comparePageToNull.
    intro phyDescChildIsnull.
    simpl.
    case_eq phyDescChildIsnull.
    { intros.
      eapply WP.weaken.
      eapply WP.ret .
      simpl.
      intros.
      intuition. }
    intros phyDescChildNotNull.
(** writeAccessible **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
    assert (exists entry : Pentry,
      lookup ptPDChild idxPDChild (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      assert (forall idx : index,
          StateLib.getIndexOfAddr pdChild fstLevel = idx ->
          isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) as H1 by intuition.
      generalize (H1  idxPDChild);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild ) as H2 by intuition.
      apply H1 in H2. intuition. }
    destruct Hlookup as (entry & Hlookup).
    exists entry ; split;trivial. 
    destruct H0 as (H0 & Hnew).
    try repeat rewrite and_assoc in H0.
    do 31 rewrite <- and_assoc in H0.
    destruct H0 as (H0 & Hsplit).
    subst. 
    destruct H0 as (H0 & Hfalse). 
    try repeat rewrite and_assoc in H0.
    assert (Hpost := conj (conj H0 Hsplit)  Hnew).
     assert(Hphy :forall partition, In partition (getPartitions multiplexer s) ->
      ~ In phyDescChild  (getConfigPages partition s)).
    { intros. clear H0 Hsplit Hnew.
      try repeat rewrite  andb_true_iff in Hlegit.
      try repeat rewrite and_assoc in Hlegit.
      destruct Hlegit as ( presentPD & accessPD & _ ).
       unfold  consistency in *.
      assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
      unfold currentPartitionInPartitionsList in *; trivial.
      assert (Hkernel : kernelDataIsolation s) by intuition.
      unfold kernelDataIsolation in Hkernel.
      unfold disjoint in Hkernel.
      apply Hkernel with (currentPartition s); trivial.
      intuition.
      apply physicalPageIsAccessible with ptRefChild descChild 
      idxRefChild accessibleChild level presentRefChild currentPD; subst; intuition. }
(*     try repeat rewrite and_assoc in Hpost.   *)
    assert(Hnewpost := conj Hpost Hphy).
    pattern s in Hnewpost.
    match type of Hnewpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptPDChild idxPDChild false s)
    end.
    simpl.
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add ptPDChild idxPDChild
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
   do 4 apply and_assoc.
    split.
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    clear Hpost Hsplit H0.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartions. clear Hpartions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    apply and_assoc.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartions in *.
    clear Hpartions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H3; trivial.
    apply and_assoc.
    split.
  (** Vertical Sharing **)
    unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    clear Hpost Hsplit H0.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartions. clear Hpartions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    apply and_assoc.
    split.
  (** Consistency **) 
    assert (Hcons : consistency s) by intuition. 
    clear Hpost Hsplit H0.     
    unfold consistency in *.
    split. apply partitionDescriptorEntryUpdateUserFlag;trivial.
    intuition.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent).
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    unfold currentPartitionInPartitionsList in *.
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartions. assumption.
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    apply Hnodupmapped;assumption.
    apply getIndirectionsNoDupUpdateUserFlag; trivial.
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    clear Hpost.
    rename H into Hcond. 
    assert (H := conj (conj (conj H0 Hfalse) Hsplit)  Hnew).
    clear H0 Hfalse Hsplit Hnew.
(** Propagated properties **)
    {  intuition try eassumption.     
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);  intros (Htableroot & _). 
        apply isPEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'.
        assert(ptRefChild <> ptPDChild \/ idxRefChild  <>idxPDChild).
        apply toApplyPageTablesOrIndicesAreDifferent with descChild pdChild currentPart
          currentPD level s; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
     
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
         generalize (Hi idx Hi1); intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(ptSh1Child  <> ptPDChild \/ idxSh1  <>idxPDChild).      
        apply toApplyPageTablesOrIndicesAreDifferent with  shadow1 pdChild currentPart
        currentPD level s; trivial.
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
         generalize (Hi1 idx Hi2); intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert( ptSh2Child <> ptPDChild \/ idxSh2 <> idxPDChild).
        apply toApplyPageTablesOrIndicesAreDifferent with shadow2
        pdChild   currentPart
        currentPD level s ;trivial.
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(ptConfigPagesList <> ptPDChild \/ idxConfigPagesList <> idxPDChild ).
        apply toApplyPageTablesOrIndicesAreDifferent with list
        pdChild   currentPart
        currentPD level s ;trivial.
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind. 
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * 
(*       assert( Hget : getPartitionAux multiplexer s' (nbPage + 1) = getPartitionAux multiplexer s (nbPage + 1)).
      apply getPartitionAuxUpdateUserFlag; trivial.
      rewrite Hget. intuition. *)
(** New property **) 
    unfold entryUserFlag. unfold s'.
    cbn.
    assert( beqPairs (ptPDChild, idxPDChild) (ptPDChild, idxPDChild)
    beqPage beqIndex = true) as Hpairs.
    apply beqPairsTrue.  split;trivial.
    rewrite Hpairs.  cbn. reflexivity.  }
    intros [].
(** writeAccessible **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
    assert (exists entry : Pentry,
      lookup ptSh1Child idxSh1 (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      assert (forall idx : index,
       StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
       isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) as H1 by intuition.
      generalize (H1  idxSh1);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1 ) as H2 by intuition.
      apply H1 in H2. intuition. }
    destruct Hlookup as (entry & Hlookup).
    exists entry ; split;trivial.
     
    destruct H0 as (((H0 & Hii) & Hnew )& Hnew').
    destruct H0 as (H0 & Hi).
    do 4 rewrite <- and_assoc in Hi.
    destruct Hi as (Hi & Hsplit). 
    destruct Hi as (Hi & Hfalse). 
    try repeat rewrite and_assoc in Hi.
    assert (Hpost := (conj (conj (conj (conj (conj H0 Hi) Hsplit) Hii) Hnew) Hnew')). 
    pattern s in Hpost.
    match type of Hpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptSh1Child idxSh1 false s)
    end.
    simpl.
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add ptSh1Child idxSh1
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
    do 6 apply and_assoc.             
    split. 
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    clear Hpost Hsplit H0.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartions. clear Hpartions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    apply and_assoc.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartions in *.
    clear Hpartions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H3; trivial.
(** Vertical Sharing **)
    apply and_assoc.
    split. unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    clear Hpost Hsplit H0.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartions. clear Hpartions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    apply and_assoc.
    split.
  (** Consistency **) 
    assert (Hcons : consistency s) by intuition. 
    clear Hpost Hsplit H0.     
    unfold consistency in *.
    split. apply partitionDescriptorEntryUpdateUserFlag;trivial.
    intuition.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent).
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    unfold currentPartitionInPartitionsList in *.
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartions. assumption.
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    apply Hnodupmapped;assumption.
    apply getIndirectionsNoDupUpdateUserFlag; trivial.
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    clear Hpost.
    rename H into Hcond. 
    assert (H := conj (conj (conj H0 Hfalse) Hsplit)  Hnew).
    clear H0 Hfalse Hsplit Hnew.
(** Propagated properties **)
    {
      intuition try eassumption. 
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); clear H23; intros (H23 & _). 
        apply isPEUpdateUserFlag; assumption.
      *  assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'.
        assert(ptRefChild <> ptSh1Child \/ idxRefChild  <>idxSh1).
        apply toApplyPageTablesOrIndicesAreDifferent with descChild shadow1 currentPart
          currentPD level s; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'. assert( ptSh2Child <> ptSh1Child \/ idxSh2 <> idxSh1).
        apply toApplyPageTablesOrIndicesAreDifferent with shadow2
        shadow1   currentPart
        currentPD level s ;trivial.
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(ptConfigPagesList <> ptSh1Child \/ idxConfigPagesList <> idxSh1 ).
        apply toApplyPageTablesOrIndicesAreDifferent with list
        shadow1   currentPart
        currentPD level s ;trivial.
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply entryUserFlagUpdateUserFlagSameValue; trivial.
(** New property **) 
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptSh1Child, idxSh1) (ptSh1Child, idxSh1) beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. } 
    intros [].
(** writeAccessible **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
    assert (exists entry : Pentry,
      lookup ptSh2Child idxSh2 (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      assert (forall idx : index,
       StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
       isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) as H1 by intuition.
      generalize (H1  idxSh2);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2 ) as H2 by intuition.
      apply H1 in H2. intuition. }
    destruct Hlookup as (entry & Hlookup).
    exists entry ; split;trivial.
     destruct H0 as (((((H0 & Hp1)& Hp2) & Hp3) & Hnew )& Hnew').
    do 4 rewrite <- and_assoc in Hp1.
    destruct Hp1 as (Hp1 & Hsplit). 
    destruct Hp1 as (Hp1 & Hfalse). 
    try repeat rewrite and_assoc in Hp1.
    assert (Hpost := (conj (conj (conj (conj (conj (conj H0 Hp1) 
    Hsplit) Hp2) Hp3) Hnew) Hnew')). 
    pattern s in Hpost.
    match type of Hpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptSh2Child idxSh2 false s)
    end.
    simpl.
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add ptSh2Child idxSh2
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
    do 8 apply and_assoc.
    split.
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    clear Hpost Hsplit H0.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartions. clear Hpartions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    apply and_assoc.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartions in *.
    clear Hpartions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H3; trivial.
    apply and_assoc.
  (** Vertical Sharing **)
    split. unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    clear Hpost Hsplit H0.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartions. clear Hpartions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    apply and_assoc.
    split.
  (** Consistency **) 
    assert (Hcons : consistency s) by intuition. 
    clear Hpost Hsplit H0.     
    unfold consistency in *.
    split. apply partitionDescriptorEntryUpdateUserFlag;trivial.
    intuition.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent).
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    unfold currentPartitionInPartitionsList in *.
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartions. assumption.
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    apply Hnodupmapped;assumption.
    apply getIndirectionsNoDupUpdateUserFlag; trivial.
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    clear Hpost.
    rename H into Hcond. 
    assert (H := conj (conj (conj H0 Hfalse) Hsplit)  Hnew).
    clear H0 Hfalse Hsplit Hnew.
(** Propagated properties **)
    { intuition try eassumption. 
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); clear H23; intros (H23 & _). 
        apply isPEUpdateUserFlag; assumption.
      *  assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'.
        assert(ptRefChild <> ptSh2Child \/ idxRefChild  <>idxSh2).
        apply toApplyPageTablesOrIndicesAreDifferent with descChild shadow2 currentPart
          currentPD level s; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial.  
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(ptConfigPagesList <> ptSh2Child \/ idxConfigPagesList <> idxSh2 ).
        apply toApplyPageTablesOrIndicesAreDifferent with list
        shadow2   currentPart
        currentPD level s ;trivial.
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply entryUserFlagUpdateUserFlagSameValue; trivial.
      * apply entryUserFlagUpdateUserFlagSameValue; trivial.
(** New property **)  
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptSh2Child, idxSh2) (ptSh2Child, idxSh2)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. }
    intros [].
(** writeAccessible **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
    assert (exists entry : Pentry,
      lookup ptConfigPagesList idxConfigPagesList (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      assert (forall idx : index,
       StateLib.getIndexOfAddr list fstLevel = idx ->
       isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s) as H1 by intuition.
      generalize (H1  idxConfigPagesList);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList ) as H2 by intuition.
      apply H1 in H2. intuition. }
    destruct Hlookup as (entry & Hlookup).
    exists entry ; split;trivial. 
     destruct H0 as (((((((H0 & Hp1)& Hp2) & Hp3)& Hp4)& Hp5) & Hnew )& Hnew').
    do 4 rewrite <- and_assoc in Hp2.
    destruct Hp2 as (Hp2 & Hsplit). 
    destruct Hp2 as (Hp2 & Hfalse). 
    try repeat rewrite and_assoc in Hp2.
    assert (Hpost := (conj(conj (conj (conj (conj (conj (conj (conj H0 Hp1) 
     Hp2) Hsplit) Hp3) Hp4) Hp5) Hnew) Hnew')).
    pattern s in Hpost.
    match type of Hpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptConfigPagesList idxConfigPagesList false s)
    end.
    simpl.
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add ptConfigPagesList idxConfigPagesList
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
    do 10 apply and_assoc.
    split. 
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    clear Hpost Hsplit H0.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartions. clear Hpartions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    apply and_assoc.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartions in *.
    clear Hpartions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H3; trivial.
    apply and_assoc.
  (** Vertical Sharing **)
    split. unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    clear Hpost Hsplit H0.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartions. clear Hpartions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    apply and_assoc.
    split.
  (** Consistency **) 
    assert (Hcons : consistency s) by intuition. 
    clear Hpost Hsplit H0.     
    unfold consistency in *.
    split. apply partitionDescriptorEntryUpdateUserFlag;trivial.
    intuition.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent).
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    unfold currentPartitionInPartitionsList in *.
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartions. assumption.
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    apply Hnodupmapped;assumption.
    apply getIndirectionsNoDupUpdateUserFlag; trivial.
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    clear Hpost.
    rename H into Hcond. 
    assert (H := conj (conj (conj H0 Hfalse) Hsplit)  Hnew).
    clear H0 Hfalse Hsplit Hnew.
(** Propagated properties **)
    { intuition try eassumption. 
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); clear H23; intros (H23 & _). 
        apply isPEUpdateUserFlag; assumption.
      *  assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * unfold s'.
        assert(ptRefChild <> ptConfigPagesList \/ idxRefChild  <>idxConfigPagesList).
        apply toApplyPageTablesOrIndicesAreDifferent with descChild list currentPart
          currentPD level s; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply entryUserFlagUpdateUserFlagSameValue; trivial. 
      * apply entryUserFlagUpdateUserFlagSameValue; trivial.
      * apply entryUserFlagUpdateUserFlagSameValue; trivial.
(** New property **) 
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptConfigPagesList, idxConfigPagesList) (ptConfigPagesList, idxConfigPagesList)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. }
    intros [].
(** writeAccessible **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply WP.writeAccessible.
    intros. simpl.
    assert (exists entry : Pentry,
      lookup ptRefChild idxRefChild (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
    { apply isPELookupEq.
      assert (forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) as H1 by intuition.
      generalize (H1  idxRefChild);clear H1; intros H1.
      assert (StateLib.getIndexOfAddr descChild fstLevel = idxRefChild ) as H2 by intuition.
      apply H1 in H2. intuition. }
    destruct Hlookup as (entry & Hlookup).
    exists entry ; split;trivial.
    destruct H0 as ((((((((((H0 & Hp1)& Hp2) & Hp3)& Hp4)& Hp5) &Hp6) &Hp7) & Hp8) & Hnew )& Hnew').
    do 26 rewrite <- and_assoc in H0.
    destruct H0 as (H0 & Hsplit). 
    destruct H0 as (H0 & Hfalse). 
    try repeat rewrite and_assoc in H0.
    assert (Hpost := (conj (conj (conj (conj(conj (conj (conj (conj (conj (conj (conj H0 Hsplit) Hp1) 
     Hp2)  Hp3) Hp4) Hp5) Hp6) Hp7) Hp8) Hnew) Hnew')).
    pattern s in Hpost.
    match type of Hpost with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                entryUserFlag ptRefChild idxRefChild false s)
    end.
    simpl.
    set (s' := {|
    currentPartition := currentPartition s;
    memory := add ptRefChild idxRefChild
              (PE
                 {|
                 read := read entry;
                 write := write entry;
                 exec := exec entry;
                 present := present entry;
                 user := false;
                 pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
    do 12 apply and_assoc. 
    split. 
  (** partitionsIsolation **) 
    assert (partitionsIsolation s ) as Hiso. intuition.
    clear Hpost Hsplit H0.
    unfold partitionsIsolation in *.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartions. clear Hpartions.
    intros.
    generalize (Hiso parent child1 child2); clear Hiso; intros Hiso. 
    assert(getChildren parent s' = getChildren parent s) as Hchildren.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite Hchildren in H2, H1. clear Hchildren.
    assert (getUsedPages child1 s'= getUsedPages child1 s) as Hch1used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch1used. clear Hch1used.
    assert (getUsedPages child2 s' = getUsedPages child2 s) as Hch2used.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite Hch2used. clear Hch2used.
    apply Hiso; trivial.
    apply and_assoc.
    split.
  (** kernelDataIsolation **)
    assert (kernelDataIsolation s) as HAncesiso. intuition.
    unfold kernelDataIsolation in *.
    intros.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial. 
    rewrite Hpartions in *.
    clear Hpartions.
    assert(  (getConfigPages partition2 s') = (getConfigPages partition2 s)) as Hconfig.
    apply getConfigPagesUpdateUserFlag; trivial.
    rewrite Hconfig. clear Hconfig.
    assert (incl (getAccessibleMappedPages partition1 s') (getAccessibleMappedPages partition1 s)).
    apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
    unfold disjoint in *.
    intros.
    unfold incl in *.
    apply HAncesiso with partition1; trivial.
    apply H3; trivial.
    apply and_assoc.
  (** Vertical Sharing **)
    split. unfold verticalSharing in *.
    assert (Hvs : verticalSharing s)  by intuition.
    clear Hpost Hsplit H0.
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartions. clear Hpartions.
    intros.
    generalize (Hvs parent child); clear Hvs; intros Hvs.
    assert (getUsedPages child s' = getUsedPages child s) as Husedpage.
    apply getUsedPagesUpdateUserFlag;trivial.
    rewrite   Husedpage.
    assert ( getMappedPages parent s' = getMappedPages parent s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd parent (memory s') = StateLib.getPd parent (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd parent (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. apply Hvs;trivial.
    assert (getChildren parent s' = getChildren parent s) as Hchild.
    apply getChildrenUpdateFlagUser;trivial.
    rewrite <- Hchild. assumption.
    apply and_assoc.
    split.
  (** Consistency **) 
    assert (Hcons : consistency s) by intuition. 
    clear Hpost Hsplit H0.     
    unfold consistency in *.
    split. apply partitionDescriptorEntryUpdateUserFlag;trivial.
    intuition.
    destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
    Hnodupmapped & Hnodupconfig & Hparent).
    repeat split; try  apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
    unfold currentPartitionInPartitionsList in *.
    simpl in *. subst. 
    assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite Hpartions. assumption.
    unfold noDupMappedPagesList in *.
    intros partition HgetPartnewstate.
    assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
    unfold getMappedPages.
    assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
    apply getPdUpdateUserFlag;trivial.
    rewrite HgetPd.
    destruct (StateLib.getPd partition (memory s)) ;trivial.
    apply getMappedPagesAuxUpdateUserFlag;trivial.
    rewrite Hmaps. 
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag;trivial.
    rewrite HgetPart in HgetPartnewstate.
    apply Hnodupmapped;assumption.
    apply getIndirectionsNoDupUpdateUserFlag; trivial.
    unfold parentInPartitionList in *.
    assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
    apply getPartitionsUpdateUserFlag; trivial.
    rewrite HgetPart.
    intros partition HgetParts parent Hroot.
    generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
    apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
    apply Hparent; trivial.
    clear Hpost.
    rename H into Hcond. 
    assert (H := conj (conj (conj H0 Hfalse) Hsplit)  Hnew).
    clear H0 Hfalse Hsplit Hnew.
(** Propagated properties **)
    { intuition try eassumption. 
      * apply nextEntryIsPPUpdateUserFlag ; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP); clear H23; intros (H23 & _). 
        apply isPEUpdateUserFlag; assumption.
      *  assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isPE ptRefChild idx s /\ 
                    getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi3 : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi3 idx HP);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;  assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isPE ptPDChild idx s /\ 
                      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
        assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
        intuition.
        generalize (Hi idx HP);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial.  
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi: forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isPE ptSh1Child idx s /\ 
                    getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);clear H7;intros (H7 & _).
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi1 : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isPE ptSh2Child idx s /\ 
                      getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi1 idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isPEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isPE ptConfigPagesList idx s /\ 
                      getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * apply entryPresentFlagUpdateUserFlag;assumption.
(*       * assert(ptConfigPagesList <> ptSh2Child \/ idxConfigPagesList <> idxSh2 ).
        apply toApplyPageTablesOrIndicesAreDifferent with list
        shadow2   currentPart
        currentPD level s ;trivial.
        rewrite checkVAddrsEqualityWOOffsetPermut; trivial. 
        apply entryUserFlagUpdateUserFlagRandomValue; assumption. *)
      * apply nextEntryIsPPUpdateUserFlag;assumption.  
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
        apply isVEUpdateUserFlag; assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr descChild fstLevel = idx ->
                    isVE ptRefChildFromSh1 idx s /\
                    getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
        assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                      isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChild)
                      by intuition.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                    isVE ptPDChildSh1 idx s /\ 
                    getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
                    isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                    beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                    isVE ptSh1ChildFromSh1 idx s /\ 
                    getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
        assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
        generalize (Hi idx Hi1);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr,
        isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
        by trivial.
        destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                    isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                    by trivial. 
        assert(Hi2 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                    beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
      destruct Hi as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);clear H7;intros (H7 & H7').
        apply isVEUpdateUserFlag;assumption.
      * assert(Hi : forall idx : index,
                    StateLib.getIndexOfAddr list fstLevel = idx ->
                    isVE childListSh1 idx s /\ 
                    getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
        assert(Hi2 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
        generalize (Hi idx Hi2);intros (_ & Htableroot).         
        unfold getTableAddrRoot in *.
        destruct Htableroot as (Htrue & Htableroot).
        split; trivial.
        intros tableroot Hi3.
        apply nextEntryIsPPUpdateUserFlag' in Hi3.
        generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
        destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
        exists nbL. split;trivial.
        exists stop. split; trivial.
        rewrite <- Hind.
        apply getIndirectionUpdateUserFlag;trivial. 
      * assert( Hi5 : exists va : vaddr,
                      isEntryVA childListSh1 idxConfigPagesList va s /\ 
                      beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
        destruct Hi5 as  (va & Hv& Hnotnull).
        exists va. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial.
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply isEntryPageUpdateUserFlag; trivial. 
      * assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      * assert (Hfalse : In phyDescChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        unfold getConfigPages in Hconfig.
        inversion Hconfig as [Hconfiginv].
        rewrite Hconfiginv.
        unfold not.
        intros.
        assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption. right; assumption.
      * apply entryUserFlagUpdateUserFlagSameValue; trivial. 
      * apply entryUserFlagUpdateUserFlagSameValue; trivial.
      * apply entryUserFlagUpdateUserFlagSameValue; trivial.
      * apply entryUserFlagUpdateUserFlagSameValue; trivial.
(** New property **) 
      * unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptRefChild, idxRefChild) (ptRefChild, idxRefChild)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. }
    intros [].
(** writeAccessibleRec **)
    eapply bindRev.
    eapply weaken.
    eapply WriteAccessibleRec.
    simpl.
    intros.
    split. 
    unfold propagatedProperties.
    try repeat rewrite and_assoc in H0.
    eapply H0. 
    intuition.
    unfold consistency in *. 
    assert (Hcur : currentPartitionInPartitionsList s ) by intuition.
    unfold currentPartitionInPartitionsList in Hcur.
    subst; trivial.
    simpl.
    intros. 
(** writeAccessibleRec **)
    eapply bindRev.
    eapply weaken.
    eapply WriteAccessibleRec.
    simpl.
    intros.
    split.
    eassumption. 
    unfold propagatedProperties in * . 
    intuition.
    unfold consistency in *. 
    assert (Hcur : currentPartitionInPartitionsList s ) by intuition.
    unfold currentPartitionInPartitionsList in Hcur.
    subst; trivial.
    simpl.
    intros.
(** writeAccessibleRec **)
    eapply bindRev.
    eapply weaken.
    eapply WriteAccessibleRec.
    simpl.
    intros.
    split.
    eassumption.
    unfold propagatedProperties in * . 
    intuition.
    unfold consistency in *. 
    assert (Hcur : currentPartitionInPartitionsList s ) by intuition.
    unfold currentPartitionInPartitionsList in Hcur.
    subst; trivial.
    simpl.
    intros.
(** writeAccessibleRec **)
    eapply bindRev.
    eapply weaken.
    eapply WriteAccessibleRec.
    simpl.
    intros.
    split.
    eassumption.
    unfold propagatedProperties in * . 
    intuition.
    unfold consistency in *. 
    assert (Hcur : currentPartitionInPartitionsList s ) by intuition.
    unfold currentPartitionInPartitionsList in Hcur.
    subst; trivial.
    simpl.
    intros. 
(** writeAccessibleRec **)
    eapply bindRev.
    eapply weaken.
    eapply WriteAccessibleRec.
    simpl.
    intros.
    split.
    eassumption.
    unfold propagatedProperties in * . 
    intuition.
    unfold consistency in *. 
    assert (Hcur : currentPartitionInPartitionsList s ) by intuition.
    unfold currentPartitionInPartitionsList in Hcur.
    subst; trivial.
    simpl.
    intros.  
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
    eapply initPEntryTableNewProperty.
    { intros. simpl.
      split. split.
      eassumption.
      unfold propagatedProperties in *.
      split. intuition. intuition.
      intros.
      assert (zero = CIndex 0) as Hzero.
      intuition.
      subst.
      unfold CIndex in H1.
      case_eq (lt_dec 0 tableSize).
      intros.
      rewrite H2 in H1.
      simpl in *. omega.
      intros.
      contradict H2.
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. }
    intros resinittablepd. simpl.
(** initPEntryTable **)    
    eapply WP.bindRev.
    eapply preAndPost.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply initPEntryTablePropagateProperties1.
    eapply initPEntryTableNewProperty.
    { intros. simpl.
      split. split.
      eassumption.
      unfold propagatedProperties in *.
      split. intuition. intuition.
      intros.
      assert (zero = CIndex 0) as Hzero.
      intuition.
      subst.
      unfold CIndex in H1.
      case_eq (lt_dec 0 tableSize).
      intros.
      rewrite H2 in H1.
      simpl in *. omega.
      intros.
      contradict H2.
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      omega. }
    eapply weaken.
    eapply initPEntryTablePropagateProperties2.
    intros.
    simpl.
    destruct H0 as ((H0 & Hzero) & Hphypd).
    split.
    split;
    eassumption.
    unfold propagatedProperties in *.
    assert(Hget1 :forall idx : index,
      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
      isPE ptSh1Child idx s /\ 
      getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
    assert(Hget2 : forall idx : index,
      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
      isPE ptPDChild idx s /\ 
      getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by intuition.
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
    assert(Hidx : StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1) by trivial.
    generalize (Hget1 idxSh1 Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
    apply Hget2; trivial.
    assert(Hidx : StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild) by trivial.
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
(** initPEntryTable **) 
    intros resinittablesh1. simpl.
    eapply WP.bindRev.
    { eapply preAndPost.
      + eapply preAndPost.
        - eapply WP.weaken.
          eapply conjPrePost.
          eapply initPEntryTablePropagateProperties1.
          eapply initPEntryTableNewProperty.
          { intros. simpl.
            split. split.
            eassumption.
            unfold propagatedProperties in *.
            split. intuition. intuition.
            intros.
            assert (zero = CIndex 0) as Hzero.
            intuition.
            subst.
            unfold CIndex in H1.
            case_eq (lt_dec 0 tableSize).
            intros.
            rewrite H2 in H1.
            simpl in *. omega.
            intros.
            contradict H2.
            assert (tableSize > tableSizeLowerBound).
            apply tableSizeBigEnough.
            unfold tableSizeLowerBound in *.
            omega. }
        - eapply weaken.
          eapply initPEntryTablePropagateProperties2.
          intros.
          simpl.
          destruct H0 as ((H0 & Hzero) & Hphypd).
          split.
          split;
          eassumption.
          unfold propagatedProperties in *.
          assert(Hget1 :forall idx : index,
            StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
            isPE ptSh2Child idx s /\ 
            getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by intuition.
          assert(Hget2 : forall idx : index,
            StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
            isPE ptSh1Child idx s /\ 
            getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
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
          assert(Hidx : StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2) by trivial.
          generalize (Hget1 idxSh2 Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
          apply Hget2; trivial.
          assert(Hidx : StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1) by trivial.
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
      eapply initPEntryTablePropagateProperties2.
      intros.
      simpl.
      destruct H0 as ((H0 & Hzero) & Hphypd).
      split.
      split;
      eassumption.
      unfold propagatedProperties in *.
      assert(Hget1 :forall idx : index,
        StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
        isPE ptSh2Child idx s /\ 
        getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by intuition.
      assert(Hget2 : forall idx : index,
        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
        isPE ptPDChild idx s /\ 
        getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by intuition.
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
      assert(Hidx : StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2) by trivial.
      generalize (Hget1 idxSh2 Hidx);clear Hget1 ; intros (_ & Hhet1); assumption.
      apply Hget2; trivial.
      assert(Hidx : StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild) by trivial.
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
    intros resinittablesh2. simpl.
(** initConfigPagesList **)

    admit.
(*    eapply bindRev. 
    admit. *)
(** TODO : To be finished *)

 - 
    intros HNotlegit. 
      eapply WP.weaken. eapply WP.ret .
      simpl. intuition.
      } 
      intros. eapply WP.weaken. eapply WP.ret .
      simpl. intuition.
      intros. eapply WP.weaken. eapply WP.ret .
      simpl. intuition.
Admitted.
