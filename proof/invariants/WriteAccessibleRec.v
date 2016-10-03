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
    This file contains the invariant of [writeAccessibleRec] *)
Require Import Core.Internal Isolation Consistency WeakestPreconditions 
Invariants StateLib Model.Hardware Model.ADT DependentTypeLemmas
GetTableAddr Model.MAL Model.Lib Lib InternalLemmas WriteAccessible.
Require Import Coq.Logic.ProofIrrelevance Omega List.
Import List.ListNotations.

Lemma WriteAccessibleRec0 nbPage (va : vaddr) (descParent : page)  currentPD tabledesc: 
{{ fun s : state => partitionsIsolation s /\ kernelDataIsolation s /\ 
verticalSharing s /\ consistency s /\ 
 In descParent (getPartitions MALInternal.multiplexer s) /\
nextEntryIsPP tabledesc PDidx currentPD s 

 }} 
  Internal.writeAccessibleRec nbPage va descParent false {{ fun b s => 
    partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s  /\
     nextEntryIsPP tabledesc PDidx currentPD s  
   }}.
Proof.
revert va descParent.
induction nbPage.
intros;simpl.
eapply weaken.
eapply WP.ret. simpl. intuition.
(*  exists tabledesc; trivial. *)
intros.
simpl.
eapply bindRev.
(** getMultiplexer **)
eapply weaken.
eapply Invariants.getMultiplexer.
intros; simpl.
pattern s in H.
eapply H.
simpl. 
intros multiplexer.
eapply bindRev.
(** Page.eqb **)
eapply weaken.
eapply Invariants.Page.eqb.
simpl.
intros.
pattern s in H.
eapply H.
simpl.
intros isMultiplexer.
case_eq isMultiplexer.
(** case_eq isMultiplexer true **)
+ intros isMultiplexerT.
  (** ret **)
  eapply weaken.
  eapply WP.ret.
  simpl. 
  intros.
  intuition.
(* exists descParent; trivial.
 exists tabledesc; trivial.
 *)
(** case_eq isMultiplexer false **)
+ intros isMultiplexerF.
  eapply bindRev.
  (** getSndShadow **)
  eapply weaken.
  eapply Invariants.getSndShadow.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
  unfold consistency in H;intuition.
  intros sh2; simpl.
  eapply bindRev.
  (** getNbLevel **)
  eapply weaken.
  eapply Invariants.getNbLevel.
  intros; simpl.
  pattern s in H.
  eapply H.
  intros L; simpl. 
  (** getIndexOfAddr **) 
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getIndexOfAddr.
  simpl; intros.
  pattern s in H.
  eapply H.
  intros lastIndex.
  simpl.
  (** getTableAddr **)
  eapply bindRev.
  eapply weaken.
  eapply GetTableAddr.getTableAddr.
  simpl. 
  intros.
  split.
  pattern s in H.
  eapply H.
  instantiate (1 :=  sh2idx).
  try repeat rewrite and_assoc in H.
  destruct H as (Hiso & Hancs & Hvs & Hcons & Hcurpart & Htttttt & Hmult & 
                 Hnotmult & Hsh2root & HnblL & Hidxaddr).
  intuition.
  eapply Hcurpart.
  exists sh2.
  split; trivial.
  split. 
  unfold consistency in *.
  destruct Hcons as (Hprdesc & _ & _  & _ & Hpr  & _). 
  unfold partitionDescriptorEntry in Hprdesc.
  generalize (Hprdesc descParent Hcurpart); clear Hprdesc; intros Hprdesc.     
  assert (sh2idx = PDidx \/ sh2idx = sh1idx \/ sh2idx = sh2idx \/sh2idx = sh3idx
   \/ sh2idx = PPRidx  \/ sh2idx = PRidx ) as Htmp 
  by auto.
  generalize (Hprdesc sh2idx Htmp); clear Hprdesc; intros Hprdesc.
  destruct Hprdesc as (Hidxsh2 & _& Hentry).
  destruct Hentry as (page1 & Hpd & Hnotnull).
  subst.
  unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh2idx);
   [destruct (lookup descParent i (memory s) beqPage beqIndex)
   as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hsh2root | 
   now contradict Hsh2root | 
   subst ; assumption| 
   now contradict Hsh2root| 
   now contradict Hsh2root ]  
   |now contradict Hsh2root] | now contradict Hsh2root].
  left; split; trivial.
  intros ptsh2. simpl.  
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  Focus 2.
  intros.
  destruct H as (H0 & H1).
  assert( (getTableAddrRoot' ptsh2 sh2idx descParent va s /\ ptsh2 = defaultPage) \/
  (forall idx : index,
  StateLib.getIndexOfAddr va fstLevel = idx ->
   isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s)).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right. intros idx Hidx.
      destruct H1 as (Hget  & Hnew & H1).
      split. 
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(Hpe &Htrue) | (_&Hfalse)]].
       - contradict Hfalse.
         unfold sh2idx, sh1idx.
         apply indexEqFalse ;
         assert (tableSize > tableSizeLowerBound).
         apply tableSizeBigEnough.
         unfold tableSizeLowerBound in *.
         omega.  apply tableSizeBigEnough.
         unfold tableSizeLowerBound in *.
         omega. apply tableSizeBigEnough. omega.
      - assumption.
      - contradict Hfalse.
        unfold PDidx. unfold sh2idx.
        apply indexEqFalse;
        assert (tableSize > tableSizeLowerBound).
        apply tableSizeBigEnough.
        unfold tableSizeLowerBound in *.
        omega.  apply tableSizeBigEnough.
        unfold tableSizeLowerBound in *.
        omega. apply tableSizeBigEnough. omega.
      - assumption.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP.
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptsh2Isnull. simpl.
  case_eq ptsh2Isnull.
  intros. eapply WP.weaken.  eapply WP.ret . simpl. intros.
  intuition.
(* exists descParent; trivial.
 exists tabledesc; trivial. *)
 
(* exists descParent; trivial.
 exists tabledesc; trivial. *)
  intros Hptsh2NotNull.
  (** readVirtual **)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.readVirtual.
  simpl; intros.
  split.
  pattern s in H.
  eapply H. 
  intuition.
  subst.
  apply beq_nat_false in H1.
  now contradict H1.
  apply H11; trivial.
  intros vaInAncestor.
  simpl.
  (** getParent **)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getParent.
  intros.
  simpl.
  split.
  pattern s in H.
  eapply H.  
  intuition.
  intros ancestor; simpl.
  (** getPd **)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getPd.
  simpl; intros.
  split.
  pattern s in H.
  eapply H. split.
  unfold consistency in H.
  intuition.
  destruct H.
  try repeat rewrite and_assoc in H.
  destruct H as (Hiso & Hancs & Hvs & Hcons & Ha &  Httt & Hb & Hc & Hd & He & Hf
  &  [(Hi & Hfalse) | Hi] & Hj & Hk ).
  subst. apply beq_nat_false in Hj.
  now contradict Hj.
  unfold consistency in Hcons.
  destruct Hcons as (_ & _& _& _ & _ & _ & _ & Hparent ).
  unfold parentInPartitionList in *.
  apply Hparent with descParent; trivial.
  intros pdAncestor.
  simpl.
  eapply bindRev.
(** setAccessible **)
  unfold setAccessible.
  { eapply bindRev.
    (** getDefaultVAddr **)
    eapply weaken.
    eapply Invariants.getDefaultVAddr.
    simpl.
    intros.
    pattern s in H.
    eapply H.
    intros defaultV.
    simpl.
    eapply bindRev.
    (**   VAddr.eqbList **)
    eapply weaken.
    eapply Invariants.VAddr.eqbList.
    simpl.
    intros.
    pattern s in H.
    eapply H.
    intros isdefaultVA.
    (** case negb isdefaultVA **)
    case_eq (negb isdefaultVA).
    + intros isdefaultVAT.
      eapply bindRev.
      (** getTableAddr **)
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      split.
      try repeat rewrite and_assoc in H.
      pattern s in H. 
      eapply H.      split. 
      intuition.
                        try repeat rewrite and_assoc in H.   
      destruct H as ( Hiso & Hancs & Hvs & Hcons & HdescParentListPart & Hmult & Hnotmult &
      Hrootsh2 & Hlevel & Hidx & Hroot & Hnotnull & Hva & HrootParent & Hrootances & Hdef &
      Hvanull ).
      unfold consistency in *.
      split.
      destruct Hcons as (_ & _& _& _ & _ & _ & _ & Hparent).
      unfold parentInPartitionList in *.
      instantiate (1:= ancestor).
      apply Hparent with descParent; trivial. 
      instantiate (1:= PDidx).
      split. intuition.
      exists pdAncestor.
      split. assumption.
      split.
      unfold consistency in *.
      destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent). 
      unfold partitionDescriptorEntry in Hpd.
      unfold parentInPartitionList in *.
      subst.
      assert(Hpartancestor : In ancestor (getPartitions MALInternal.multiplexer s)).
      {       apply Hparent with descParent; trivial. } 
      generalize (Hpd ancestor Hpartancestor); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/PDidx = sh3idx
       \/  PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
      by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hancesnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup ancestor i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootances |
        now contradict Hrootances | 
       subst ; assumption| now contradict Hrootances| now contradict Hrootances ]  
       |now contradict Hrootances] | now contradict Hrootances].
      subst. left. split;trivial.
      intro ptvaInAncestor. simpl.
       (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert( (getTableAddrRoot' ptvaInAncestor PDidx ancestor vaInAncestor s /\ ptvaInAncestor = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s)).
      { destruct H1 as [H1 |H1].
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
           - assumption.
           - assumption.  } 
      do 10 rewrite <- and_assoc in H0.
      destruct H0 as (H0 & Hor &  Htrue & Hrest).
      destruct Hor as [( _ & Hfalse) |Htableroot].
      rewrite Hfalse in Htrue.
      apply beq_nat_false in Htrue.
      now contradict Htrue.
      clear H1.
      do 2 rewrite <- and_assoc in Hrest.
      destruct Hrest as (Hrest & Hdef & Hvanotnull).
      rewrite Hdef in Hvanotnull. clear Hdef.
      try repeat rewrite and_assoc in H0.
      assert (HP :=conj(conj (conj(conj (conj H0 Htableroot) Htrue )Hrest) H) isdefaultVAT).
      pattern s in HP.
      eapply HP.
  (** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptvaInAncestorIsnull. simpl.
      case_eq ptvaInAncestorIsnull.
      Focus 2.
      intros HptvaInAncestorIsnulll.
  (** StateLib.getIndexOfAddr **)                
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros.
        do 2 rewrite  and_assoc in H.
        destruct H as (H & [(Hptchild& Hnull) | Hptchild] & Hptchildnotnull).
        + subst. contradict Hptchildnotnull. intro Hnull.
          destruct Hnull.
          apply beq_nat_false in H1. intuition.
        +
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
          try repeat rewrite and_assoc in HP.
          pattern s in HP.
          eapply HP.  }
      intros idxva.
      eapply bindRev.
   (** writeAccessible **)
      eapply WP.weaken.
      eapply WP.writeAccessible.
      intros. simpl.
      assert (exists entry : Pentry,
        lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
      { apply isPELookupEq.
        assert (forall idx : index,
        StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
        isPE ptvaInAncestor idx s /\
        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s ) as H2 by intuition.
        destruct H. 
        apply H2 in H0. intuition. }
      destruct Hlookup as (entry & Hlookup).
      exists entry ; split;trivial. 
      try repeat rewrite and_assoc in H.
      pattern s in H.
      match type of H with 
      | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                  entryUserFlag ptvaInAncestor idxva false s)
      end.
      simpl.
      set (s' := {|
      currentPartition := currentPartition s;
      memory := add ptvaInAncestor idxva
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
                   simpl in *. 
      assert(Hmult : multiplexer = MALInternal.multiplexer) by intuition.
      subst.
      split. split. 
    (** partitionsIsolation **) 
      assert (partitionsIsolation s) as Hiso. intuition.
      unfold partitionsIsolation in *.
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      subst. 
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
      apply H2; trivial.
    (** Vertical Sharing **)
      split. unfold verticalSharing in *.
      assert (Hvs : verticalSharing s)  by intuition.
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
      split.
    (** Consistency **) 
      assert (Hcons : consistency s) by intuition.  
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
      rename H into Hcond. 
  (** Propagated properties **)
      { assert(Hi2 : StateLib.getIndexOfAddr va fstLevel = lastIndex) by intuition.
        try repeat split;intuition. 
        * assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
          apply getPartitionsUpdateUserFlag; trivial.
          rewrite Hpartions. assumption.
        *  apply nextEntryIsPPUpdateUserFlag; intuition.
        * apply  nextEntryIsPPUpdateUserFlag; trivial.
        * apply isVAUpdateUserFlag; trivial.
          assert( Hisva :  forall idx : index,
                      StateLib.getIndexOfAddr va fstLevel = idx ->
                      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
                      apply Hisva; trivial.
        * assert ( Hi : forall idx : index,
                  StateLib.getIndexOfAddr va fstLevel = idx ->
                  isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
          
          generalize (Hi lastIndex Hi2); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in H7.
          assert(Hi3 : nextEntryIsPP descParent sh2idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          destruct H7 as (_ & Htableroot).         
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        * apply isVA'UpdateUserFlag; trivial.
        * apply  nextEntryIsPPUpdateUserFlag; trivial.
        * apply  nextEntryIsPPUpdateUserFlag; trivial.
        * assert(Hi :forall idx : index,
              StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
              isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) 
              by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption.
        * assert(Hi : forall idx : index,
          StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
          isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in H7.
          assert(Hi4 : nextEntryIsPP ancestor PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.
          destruct H7 as (_ & Htableroot).         
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. }
  (** WriteAccessible property **) 
      unfold entryUserFlag. unfold s'.
      cbn.
      assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
      beqPage beqIndex = true) as Hpairs.
      apply beqPairsTrue.  split;trivial.
      rewrite Hpairs.  cbn. reflexivity. 
      intros [].
      eapply weaken.
      eapply WP.ret.
      intros.
      instantiate(1:= fun b s =>partitionsIsolation s /\
     kernelDataIsolation s /\
     verticalSharing s /\
     consistency s /\
     In descParent (getPartitions MALInternal.multiplexer s) /\
     nextEntryIsPP tabledesc PDidx currentPD s /\
     multiplexer = MALInternal.multiplexer /\
     false = StateLib.Page.eqb descParent multiplexer /\
     nextEntryIsPP descParent sh2idx sh2 s /\
     Some L = StateLib.getNbLevel /\
     StateLib.getIndexOfAddr va fstLevel = lastIndex /\
     (forall idx : index,
      StateLib.getIndexOfAddr va fstLevel = idx ->
      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) /\
     (defaultPage =? ptsh2) = false /\
     isVA' ptsh2 lastIndex vaInAncestor s /\
     nextEntryIsPP descParent PPRidx ancestor s /\
     nextEntryIsPP ancestor PDidx pdAncestor s  ).
      simpl. intuition.
      intros.
      eapply weaken.
      eapply WP.ret.
      simpl. intuition.
    + intros.
      eapply weaken.
      eapply WP.ret.
      simpl.
      intros.
      intuition.
      subst.
      apply beq_nat_false in H7.
      now contradict H7.
      subst.
      apply beq_nat_false in H7.
      now contradict H7. }
    intros. simpl.
    case_eq a.
    intros. subst.
    eapply weaken.
(** recursion **)
    eapply IHnbPage.
    simpl. intuition.
    unfold consistency in H2.
    assert (Hparent : parentInPartitionList s) by intuition.
    unfold parentInPartitionList in *.
    apply Hparent with descParent; trivial.
     
    
(** setAccessible failed **)
    intros.    eapply weaken.
    eapply WP.ret.
    intros.
    simpl. intuition.
    Qed.
    
Definition propagatedProperties  pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
 ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
idxConfigPagesList presentConfigPagesList 
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2
derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s : Prop :=
partitionsIsolation s /\
kernelDataIsolation s /\
verticalSharing s /\
consistency s /\
Some level = StateLib.getNbLevel /\
false = checkVAddrsEqualityWOOffset nbLevel descChild pdChild level /\
false = checkVAddrsEqualityWOOffset nbLevel descChild shadow1 level /\
false = checkVAddrsEqualityWOOffset nbLevel descChild shadow2 level /\
false = checkVAddrsEqualityWOOffset nbLevel descChild list level /\
false = checkVAddrsEqualityWOOffset nbLevel pdChild shadow1 level /\
false = checkVAddrsEqualityWOOffset nbLevel pdChild shadow2 level /\
false = checkVAddrsEqualityWOOffset nbLevel pdChild list level /\
false = checkVAddrsEqualityWOOffset nbLevel shadow1 shadow2 level /\
false = checkVAddrsEqualityWOOffset nbLevel shadow1 list level /\
false = checkVAddrsEqualityWOOffset nbLevel shadow2 list level /\
(Kidx =? nth (length descChild - (nbLevel - 1 + 2)) descChild defaultIndex) = false /\
(Kidx =? nth (length pdChild - (nbLevel - 1 + 2)) pdChild defaultIndex) = false /\
(Kidx =? nth (length shadow1 - (nbLevel - 1 + 2)) shadow1 defaultIndex) = false /\
(Kidx =? nth (length shadow2 - (nbLevel - 1 + 2)) shadow2 defaultIndex) = false /\
(Kidx =? nth (length list - (nbLevel - 1 + 2)) list defaultIndex) = false /\
currentPart = currentPartition s /\
nextEntryIsPP currentPart PDidx currentPD s /\
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) /\
(defaultPage =? ptRefChild) = false /\
StateLib.getIndexOfAddr descChild fstLevel = idxRefChild /\
entryPresentFlag ptRefChild idxRefChild presentRefChild s /\
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) /\
(defaultPage =? ptPDChild) = false /\
StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild /\
entryPresentFlag ptPDChild idxPDChild presentPDChild s /\
(forall idx : index,
StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) /\
(defaultPage =? ptSh1Child) = false /\
StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1 /\
entryPresentFlag ptSh1Child idxSh1 presentSh1 s /\
(forall idx : index,
StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) /\
(defaultPage =? ptSh2Child) = false /\
StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2 /\ entryPresentFlag ptSh2Child idxSh2 presentSh2 s /\
(forall idx : index,
StateLib.getIndexOfAddr list fstLevel = idx ->
isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s) /\
(defaultPage =? ptConfigPagesList) = false /\
StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList /\
entryPresentFlag ptConfigPagesList idxConfigPagesList presentConfigPagesList s /\
nextEntryIsPP currentPart sh1idx currentShadow1 s /\
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isVE ptRefChildFromSh1 idx s /\ getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) /\
(defaultPage =? ptRefChildFromSh1) = false /\
(exists va : vaddr, isEntryVA ptRefChildFromSh1 idxRefChild va s /\ beqVAddr defaultVAddr va = derivedRefChild) /\
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isVE ptPDChildSh1 idx s /\ getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) /\
(defaultPage =? ptPDChildSh1) = false /\
(exists va : vaddr, isEntryVA ptPDChildSh1 idxPDChild va s /\ beqVAddr defaultVAddr va = derivedPDChild) /\
(forall idx : index,
StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
isVE ptSh1ChildFromSh1 idx s /\ getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) /\
(defaultPage =? ptSh1ChildFromSh1) = false /\
(exists va : vaddr, isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) /\
(forall idx : index,
StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) /\
(defaultPage =? childSh2) = false /\
(exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ beqVAddr defaultVAddr va = derivedSh2Child) /\
(forall idx : index,
StateLib.getIndexOfAddr list fstLevel = idx ->
isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 sh1idx currentPart list s) /\
(defaultPage =? childListSh1) = false /\
(exists va : vaddr,
isEntryVA childListSh1 idxConfigPagesList va s /\ beqVAddr defaultVAddr va = derivedRefChildListSh1) /\
isEntryPage ptPDChild idxPDChild phyPDChild s /\
(defaultPage =? phyPDChild) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s))) /\
isEntryPage ptSh1Child idxSh1 phySh1Child s /\
(defaultPage =? phySh1Child) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s))) /\
isEntryPage ptSh2Child idxSh2 phySh2Child s /\
(defaultPage =? phySh2Child) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s))) /\
isEntryPage ptConfigPagesList idxConfigPagesList phyConfigPagesList s /\
(defaultPage =? phyConfigPagesList) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s))) /\
isEntryPage ptRefChild idxRefChild phyDescChild s /\ (defaultPage =? phyDescChild) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) -> ~ In phyDescChild (getConfigPages partition s)) /\
entryUserFlag ptPDChild idxPDChild false s /\ entryUserFlag ptSh1Child idxSh1 false s /\
entryUserFlag ptSh2Child idxSh2 false s /\ entryUserFlag ptConfigPagesList idxConfigPagesList false s /\
entryUserFlag ptRefChild idxRefChild false s.


Lemma WriteAccessibleRec descParent va pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild: 
{{  fun s : state =>
 propagatedProperties  
 pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s /\ 
    In descParent (getPartitions MALInternal.multiplexer s) 
    }} 
  Internal.writeAccessibleRec nbPage va descParent false {{
    fun _ s  =>
     propagatedProperties  
 pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s 
     }}.
Proof.
revert va descParent.
induction nbPage.
intros;simpl.
eapply weaken.
eapply WP.ret. simpl. intuition.
intros.
simpl.
eapply bindRev.
(** getMultiplexer **)
eapply weaken.
eapply Invariants.getMultiplexer.
intros; simpl.
pattern s in H.
eapply H.
simpl. 
intros multiplexer.
eapply bindRev.
(** Page.eqb **)
eapply weaken.
eapply Invariants.Page.eqb.
simpl.
intros.
pattern s in H.
eapply H.
simpl.
intros isMultiplexer.
case_eq isMultiplexer.
(** case_eq isMultiplexer true **)
+ intros isMultiplexerT.
  (** ret **)
  eapply weaken.
  eapply WP.ret.
  simpl. 
  intros.
  intuition.
(** case_eq isMultiplexer false **)
+ intros isMultiplexerF.
  eapply bindRev.
  (** getSndShadow **)
  eapply weaken.
  eapply Invariants.getSndShadow.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
  unfold propagatedProperties in H.
  unfold consistency in H;intuition.
 (** In descParent (getPartitions MALInternal.multiplexer s)**)
  intros sh2; simpl.
  eapply bindRev.
  (** getNbLevel **)
  eapply weaken.
  eapply Invariants.getNbLevel.
  intros; simpl.
  pattern s in H.
  eapply H.
  intros L; simpl. 
  (** getIndexOfAddr **) 
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getIndexOfAddr.
  simpl; intros.
  pattern s in H.
  eapply H.
  intros lastIndex.
  simpl.
  (** getTableAddr **)
  eapply bindRev.
  eapply weaken.
  eapply GetTableAddr.getTableAddr.
  simpl. 
  intros.
  split.
  pattern s in H.
  eapply H.
  instantiate (1 :=  sh2idx).
  unfold propagatedProperties in H.
  split.
  intuition.
  
(*   try repeat rewrite and_assoc in H. *)
  destruct H as (((((((Hiso & Hancs & Hvs & Hcons &  HPrecond ) 
  & Hcurpart)
   & Hmult) & 
                 Hnotmult) & Hsh2root) & HnblL) & Hidxaddr).
  intuition.
  eapply Hcurpart.
  exists sh2.
  split; trivial.
  split. 
  unfold consistency in *.
  destruct Hcons as (Hprdesc & _ & _  & _ & Hpr  & _). 
  unfold partitionDescriptorEntry in Hprdesc.
  generalize (Hprdesc descParent Hcurpart); clear Hprdesc; intros Hprdesc.     
  assert (sh2idx = PDidx \/ sh2idx = sh1idx \/ sh2idx = sh2idx \/ sh2idx = sh3idx
   \/ sh2idx = PPRidx  \/ sh2idx = PRidx ) as Htmp 
  by auto.
  generalize (Hprdesc sh2idx Htmp); clear Hprdesc; intros Hprdesc.
  destruct Hprdesc as (Hidxsh2 & _& Hentry).
  destruct Hentry as (page1 & Hpd & Hnotnull).
  subst.
  unfold nextEntryIsPP in *; destruct (StateLib.Index.succ sh2idx);
   [destruct (lookup descParent i (memory s) beqPage beqIndex)
   as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hsh2root | 
   now contradict Hsh2root | 
   subst ; assumption| 
   now contradict Hsh2root| 
   now contradict Hsh2root ]  
   |now contradict Hsh2root] | now contradict Hsh2root].
  left; split; trivial.
  intros ptsh2. simpl.  
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  Focus 2.
  intros.
  destruct H as (H0 & H1).
  assert( (getTableAddrRoot' ptsh2 sh2idx descParent va s /\ ptsh2 = defaultPage) \/
  (forall idx : index,
  StateLib.getIndexOfAddr va fstLevel = idx ->
   isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s)).
  { destruct H1 as [H1 |H1].
    + left. trivial. 
    + right. intros idx Hidx.
      destruct H1 as (Hget  & Hnew & H1).
      split. 
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(_& Hfalse) | [(Hpe &Htrue) | (_&Hfalse)]].
       - contradict Hfalse.
         unfold sh2idx, sh1idx.
         apply indexEqFalse ;
         assert (tableSize > tableSizeLowerBound).
         apply tableSizeBigEnough.
         unfold tableSizeLowerBound in *.
         omega.  apply tableSizeBigEnough.
         unfold tableSizeLowerBound in *.
         omega. apply tableSizeBigEnough. omega.
      - assumption.
      - contradict Hfalse.
        unfold PDidx. unfold sh2idx.
        apply indexEqFalse;
        assert (tableSize > tableSizeLowerBound).
        apply tableSizeBigEnough.
        unfold tableSizeLowerBound in *.
        omega.  apply tableSizeBigEnough.
        unfold tableSizeLowerBound in *.
        omega. apply tableSizeBigEnough. omega.
      - assumption.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP.
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptsh2Isnull. simpl.
  case_eq ptsh2Isnull.
  intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition.
  intros Hptsh2NotNull.
  (** readVirtual **)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.readVirtual.
  simpl; intros.
  split.
  pattern s in H.
  eapply H. 
  intuition.
  subst.
  apply beq_nat_false in H1.
  now contradict H1.
  assert( Hva : forall idx : index,
      StateLib.getIndexOfAddr va fstLevel = idx ->
      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial. 
  apply Hva; trivial.
  intros vaInAncestor.
  simpl.
  (** getParent **)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getParent.
  intros.
  simpl.
  split.
  pattern s in H.
  eapply H. unfold propagatedProperties in *.  
  intuition.
  intros ancestor; simpl.
  (** getPd **)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getPd.
  simpl; intros.
  split.
  pattern s in H.
  eapply H. split.
  unfold propagatedProperties in H.
  unfold consistency in H.
  intuition.
  destruct H.
  unfold propagatedProperties in H.
  assert(Hkk : partitionsIsolation s /\
              kernelDataIsolation s /\
              verticalSharing s /\
              consistency s /\ In descParent (getPartitions MALInternal.multiplexer s) /\
           multiplexer = MALInternal.multiplexer /\ 
           false = StateLib.Page.eqb descParent multiplexer /\
         nextEntryIsPP descParent sh2idx sh2 s /\ Some L = StateLib.getNbLevel /\
       StateLib.getIndexOfAddr va fstLevel = lastIndex /\
      (getTableAddrRoot' ptsh2 sh2idx descParent va s /\ ptsh2 = defaultPage \/
       (forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx -> 
        isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s)) /\ 
        (defaultPage =? ptsh2) = false /\ isVA' ptsh2 lastIndex vaInAncestor s) by intuition.
         
   destruct Hkk as (Hiso & Hancs & Hvs & Hcons  & Ha & Hb & Hc & Hd & He & Hf
  &  [(Hi & Hfalse) | Hi] & Hj & Hk ).
  subst. apply beq_nat_false in Hj.
  now contradict Hj.
  unfold consistency in Hcons.
  destruct Hcons as (_ & _& _& _ & _ & _ & _ & Hparent ).
  unfold parentInPartitionList in *.
  apply Hparent with descParent; trivial.
  intros pdAncestor.
  simpl.
  eapply bindRev.
(** setAccessible **)
  unfold setAccessible.
  { eapply bindRev.
    (** getDefaultVAddr **)
    eapply weaken.
    eapply Invariants.getDefaultVAddr.
    simpl.
    intros.
    pattern s in H.
    eapply H.
    intros defaultV.
    simpl.
    eapply bindRev.
    (**   VAddr.eqbList **)
    eapply weaken.
    eapply Invariants.VAddr.eqbList.
    simpl.
    intros.
    pattern s in H.
    eapply H.
    intros isdefaultVA.
    (** case negb isdefaultVA **)
    case_eq (negb isdefaultVA).
    + intros isdefaultVAT.
      eapply bindRev.
      (** getTableAddr **)
      eapply WP.weaken. 
      apply getTableAddr.
      simpl.
      intros s H.
      split.
      try repeat rewrite and_assoc in H.
      pattern s in H. 
      eapply H. 
      unfold propagatedProperties in H. 
      split.

      intuition.
      assert(   partitionsIsolation s /\
                  kernelDataIsolation s /\
                  verticalSharing s /\
                  consistency s /\
                  In descParent (getPartitions MALInternal.multiplexer s) /\
               multiplexer = MALInternal.multiplexer /\
              false = StateLib.Page.eqb descParent multiplexer /\
             nextEntryIsPP descParent sh2idx sh2 s /\ Some L = StateLib.getNbLevel /\
           StateLib.getIndexOfAddr va fstLevel = lastIndex /\
          (getTableAddrRoot' ptsh2 sh2idx descParent va s /\ ptsh2 = defaultPage \/
           (forall idx : index,
            StateLib.getIndexOfAddr va fstLevel = idx ->
            isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s)) /\
         (defaultPage =? ptsh2) = false /\ isVA' ptsh2 lastIndex vaInAncestor s /\
       nextEntryIsPP descParent PPRidx ancestor s /\ nextEntryIsPP ancestor PDidx pdAncestor s /\
     defaultV = defaultVAddr /\
    isdefaultVA = StateLib.VAddr.eqbList defaultV vaInAncestor) by intuition.
    clear H.
 
      destruct H0 as ( Hiso & Hancs & Hvs & Hcons & HdescParentListPart & Hmult & Hnotmult &
      Hrootsh2 & Hlevel & Hidx & Hroot & Hnotnull & Hva & HrootParent & Hrootances & Hdef &
      Hvanull ).
      unfold consistency in *.
      split.
      destruct Hcons as (_ & _& _& _ & _ & _ & _ & Hparent).
      unfold parentInPartitionList in *.
      instantiate (1:= ancestor).
      apply Hparent with descParent; trivial. 
      instantiate (1:= PDidx).
      split. intuition.
      exists pdAncestor.
      split. assumption.
      split.
      unfold consistency in *.
      destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent). 
      unfold partitionDescriptorEntry in Hpd.
      unfold parentInPartitionList in *.
      subst.
      assert(Hpartancestor : In ancestor (getPartitions MALInternal.multiplexer s)).
      {       apply Hparent with descParent; trivial. } 
      generalize (Hpd ancestor Hpartancestor); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/PDidx = sh3idx
       \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
      by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hancesnotnull).
      subst.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup ancestor i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootances |
        now contradict Hrootances | 
       subst ; assumption| now contradict Hrootances| now contradict Hrootances ]  
       |now contradict Hrootances] | now contradict Hrootances].
      subst. left. split;trivial.
      intro ptvaInAncestor. simpl.
       (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      Focus 2.
      intros.
      destruct H as (H0 & H1).
      assert( (getTableAddrRoot' ptvaInAncestor PDidx ancestor vaInAncestor s /\ ptvaInAncestor = defaultPage) \/
     (forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s)).
      { destruct H1 as [H1 |H1].
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
           - assumption.
           - assumption.  }  

      do 6 rewrite <- and_assoc in H0.
      destruct H0 as (H0 & Hor &  Htrue & Hrest).
      destruct Hor as [( _ & Hfalse) |Htableroot].
      rewrite Hfalse in Htrue.
      apply beq_nat_false in Htrue.
      now contradict Htrue.
      clear H1.
      do 2 rewrite <- and_assoc in Hrest.
      destruct Hrest as (Hrest & Hdef & Hvanotnull).
      rewrite Hdef in Hvanotnull. clear Hdef.
      try repeat rewrite and_assoc in H0.
      assert (HP :=conj(conj (conj(conj (conj H0 Htableroot) Htrue )Hrest) H) isdefaultVAT).
      pattern s in HP.
      eapply HP.
  (** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptvaInAncestorIsnull. simpl.
      case_eq ptvaInAncestorIsnull.
      Focus 2.
      intros HptvaInAncestorIsnulll.
  (** StateLib.getIndexOfAddr **)                
      eapply WP.bindRev.
      eapply WP.weaken.
      eapply Invariants.getIndexOfAddr.
      { simpl. intros.
        do 2 rewrite  and_assoc in H.
        destruct H as (H & [(Hptchild& Hnull) | Hptchild] & Hptchildnotnull).
        + subst. contradict Hptchildnotnull. intro Hnull.
          destruct Hnull.
          apply beq_nat_false in H1. intuition.
        +
          assert (HP := conj (conj H Hptchild) Hptchildnotnull).
          try repeat rewrite and_assoc in HP.
          pattern s in HP.
          eapply HP.  }
      intros idxva.
      eapply bindRev.
   (** writeAccessible **)
      eapply WP.weaken.
      eapply WP.writeAccessible.
      intros. simpl.
      assert (exists entry : Pentry,
        lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry)) as Hlookup.
      { apply isPELookupEq.
        assert (forall idx : index,
        StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
        isPE ptvaInAncestor idx s /\
        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s ) as H2 by intuition.
        destruct H. 
        apply H2 in H0. intuition. }
      destruct Hlookup as (entry & Hlookup).
      exists entry ; split;trivial. 
      try repeat rewrite and_assoc in H.
      pattern s in H.
      match type of H with 
      | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                  entryUserFlag ptvaInAncestor idxva false s)
      end.
      simpl.
      set (s' := {|
      currentPartition := currentPartition s;
      memory := add ptvaInAncestor idxva
                (PE
                   {|
                   read := read entry;
                   write := write entry;
                   exec := exec entry;
                   present := present entry;
                   user := false;
                   pa := pa entry |}) (memory s) beqPage beqIndex |}) in *.
                   simpl in *. 
      assert(Hmult : multiplexer = MALInternal.multiplexer) by intuition.
      subst.
      split. split. 
      unfold propagatedProperties in *. split. 
    (** partitionsIsolation **) 
      assert (partitionsIsolation s) as Hiso. intuition.
      unfold partitionsIsolation in *.
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      subst. 
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
      apply H2; trivial.
    (** Vertical Sharing **)
      split. unfold verticalSharing in *.
      assert (Hvs : verticalSharing s)  by intuition.
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
      split.
    (** Consistency **) 
      assert (Hcons : consistency s) by intuition.  
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
      rename H into Hcond. 
  (** Propagated properties **)
      assert(Hi2 : StateLib.getIndexOfAddr va fstLevel = lastIndex) by intuition.
      { try repeat split;intuition try eassumption. 
        + apply nextEntryIsPPUpdateUserFlag ; assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr descChild fstLevel = idx ->
                      isPE ptRefChild idx s /\ 
                      getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
          assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
          intuition.
          generalize (Hi idx HP); clear H23; intros (H23 & _). 
          apply isPEUpdateUserFlag; assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr descChild fstLevel = idx ->
                      isPE ptRefChild idx s /\ 
                      getTableAddrRoot ptRefChild PDidx currentPart descChild s) by trivial.
          assert(HP : StateLib.getIndexOfAddr descChild fstLevel = idx) by
          intuition.
          generalize (Hi idx HP); clear H23; intros (_ & H23).         
          unfold getTableAddrRoot in H23.
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          destruct H23 as (_ & Htableroot).         
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + (* unfold s'.
          assert(ptRefChild <> ptvaInAncestor).
          { (** disjoint (getConfigPages ancestor s) (getConfigPages child s) **) 
            admit. }
          apply entryUserFlagUpdateUserFlagRandomValue; trivial.
          left; assumption.
        + *) assert(Hi3 : forall idx : index,
                        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                        isPE ptPDChild idx s /\ 
                        getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
          assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
          intuition.
          generalize (Hi3 idx HP);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;  assumption.
        + assert(Hi3 : forall idx : index,
                        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                        isPE ptPDChild idx s /\ 
                        getTableAddrRoot ptPDChild PDidx currentPart pdChild s) by trivial.
          assert(HP : StateLib.getIndexOfAddr pdChild fstLevel = idx) by
          intuition.
          generalize (Hi3 idx HP); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in H7.
          assert(Hi4 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.
          destruct H7 as (_ & Htableroot).         
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + assert(Hi: forall idx : index,
                      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                      isPE ptSh1Child idx s /\ 
                      getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
          assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
          generalize (Hi idx Hi1);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption.
        + assert(Hi: forall idx : index,
                      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                      isPE ptSh1Child idx s /\ 
                      getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) by intuition.
          assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
          assert (Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          destruct H7' as (_ & Htableroot).         
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
       (*  + assert(ptSh1Child <> ptvaInAncestor).
          { (** disjoint (getConfigPages ancestor s) (getConfigPages child s) **) 
          admit. }
          apply entryUserFlagUpdateUserFlagRandomValue; trivial.
          left; assumption. *)
        + assert(Hi1 : forall idx : index,
                        StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                        isPE ptSh2Child idx s /\ 
                        getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
          assert(Hi4 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
          generalize (Hi1 idx Hi4);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption.
        + assert(Hi1 : forall idx : index,
                        StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                        isPE ptSh2Child idx s /\ 
                        getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) by trivial.
          assert(Hi4 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
          generalize (Hi1 idx Hi4);clear H7;intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          destruct H7' as (_ & Htableroot).         
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        (* + assert(ptSh2Child <> ptvaInAncestor).
          { (** disjoint (getConfigPages ancestor s) (getConfigPages child s) **) 
          admit. }
          apply entryUserFlagUpdateUserFlagRandomValue; trivial.
          left; assumption. *)
        + assert(Hi : forall idx : index,
                        StateLib.getIndexOfAddr list fstLevel = idx ->
                        isPE ptConfigPagesList idx s /\ 
                        getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
          assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          apply isPEUpdateUserFlag;assumption.
        + assert(Hi : forall idx : index,
                        StateLib.getIndexOfAddr list fstLevel = idx ->
                        isPE ptConfigPagesList idx s /\ 
                        getTableAddrRoot ptConfigPagesList PDidx currentPart list s) by trivial.
          assert(Hi1 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          destruct H7' as (_ & Htableroot).         
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
       (*  + assert(ptConfigPagesList <> ptvaInAncestor).
          { (** disjoint (getConfigPages ancestor s) (getConfigPages child s) **) 
          admit. }
          apply entryUserFlagUpdateUserFlagRandomValue; trivial.
          left; assumption . *)
        + apply nextEntryIsPPUpdateUserFlag;assumption.  
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr descChild fstLevel = idx ->
                      isVE ptRefChildFromSh1 idx s /\
                      getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
          assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
          generalize (Hi idx Hi1); clear H7; intros (H7 & H7').      
          apply isVEUpdateUserFlag; assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr descChild fstLevel = idx ->
                      isVE ptRefChildFromSh1 idx s /\
                      getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by trivial.
          assert(Hi1 :StateLib.getIndexOfAddr descChild fstLevel = idx) by trivial.
          generalize (Hi idx Hi1); clear H7; intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
          assert(Hi4 : nextEntryIsPP currentPart sh1idx tableroot s') by intuition.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.
          destruct H7' as (_ & Htableroot).         
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial. 
          apply getIndirectionUpdateUserFlag;trivial.
        + assert(Hi : exists va : vaddr,
                        isEntryVA ptRefChildFromSh1 idxRefChild va s /\ 
                        beqVAddr defaultVAddr va = derivedRefChild)
                        by intuition.
          destruct Hi as  (va0 & Hv& Hnotnull).
          exists va0. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isVE ptPDChildSh1 idx s /\ 
                      getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
          assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          apply isVEUpdateUserFlag;assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr pdChild fstLevel = idx ->
                      isVE ptPDChildSh1 idx s /\ 
                      getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) by trivial.
          assert(Hi1 : StateLib.getIndexOfAddr pdChild fstLevel = idx) by trivial. 
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          destruct H7' as (_ & Htableroot).         
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + assert(Hi : exists va : vaddr,
                      isEntryVA ptPDChildSh1 idxPDChild va s /\ 
                      beqVAddr defaultVAddr va = derivedPDChild) by trivial. 
          destruct Hi as  (va0 & Hv& Hnotnull).
          exists va0. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                      isVE ptSh1ChildFromSh1 idx s /\ 
                      getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
          assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          apply isVEUpdateUserFlag;assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
                      isVE ptSh1ChildFromSh1 idx s /\ 
                      getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) by trivial.
          assert(Hi1 : StateLib.getIndexOfAddr shadow1 fstLevel = idx) by trivial.
          generalize (Hi idx Hi1);clear H7;intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          destruct H7' as (_ & Htableroot).         
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + assert(Hi : exists va : vaddr,
          isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) 
          by trivial.
          destruct Hi as  (va0 & Hv& Hnotnull).
          exists va0. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                      by trivial. 
          assert(Hi4 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
          generalize (Hi idx Hi4);clear H7;intros (H7 & H7').
          apply isVEUpdateUserFlag;assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
                      isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) 
                      by trivial. 
          assert(Hi4 : StateLib.getIndexOfAddr shadow2 fstLevel = idx) by trivial.
          generalize (Hi idx Hi4);clear H7;intros (H7 & H7').
          unfold getTableAddrRoot in H7'.
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          destruct H7' as (_ & Htableroot).         
          generalize(Htableroot tableroot Hi3);clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + assert(Hi : exists va : vaddr, isEntryVA childSh2 idxSh2 va s /\ 
                      beqVAddr defaultVAddr va = derivedSh2Child) by trivial.
          destruct Hi as  (va0 & Hv& Hnotnull).
          exists va0. split; [ apply isEntryVAUpdateUserFlag | ];trivial. 
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isVE childListSh1 idx s /\ 
                      getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
          assert(Hi4 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
          generalize (Hi idx Hi4);clear H7;intros (H7 & H7').
          apply isVEUpdateUserFlag;assumption.
        + assert(Hi : forall idx : index,
                      StateLib.getIndexOfAddr list fstLevel = idx ->
                      isVE childListSh1 idx s /\ 
                      getTableAddrRoot childListSh1 sh1idx currentPart list s) by trivial.
          assert(Hi4 : StateLib.getIndexOfAddr list fstLevel = idx) by trivial.
          generalize (Hi idx Hi4);clear H7;intros (H7 & H7'). 
          unfold getTableAddrRoot in H7'.
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          destruct H7' as (_ & Htableroot).         
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + trivial. assert(Hi : exists va : vaddr,
          isEntryVA childListSh1 idxConfigPagesList va s /\
          beqVAddr defaultVAddr va = derivedRefChildListSh1) by trivial.
                      intuition.
          destruct Hi as  (va0 & Hv& Hnotnull).
          exists va0. split; [ apply isEntryVAUpdateUserFlag | ];trivial.
      + apply isEntryPageUpdateUserFlag; trivial.
      + assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      + assert (Hfalse : In phyPDChild (getConfigPagesAux partition s')); trivial.
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
      + apply isEntryPageUpdateUserFlag; trivial.
      + assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      + assert (Hfalse : In phySh1Child (getConfigPagesAux partition s')); trivial.
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
      + apply isEntryPageUpdateUserFlag; trivial.
      + assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      + assert (Hfalse : In phySh2Child (getConfigPagesAux partition s')); trivial.
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
      + apply isEntryPageUpdateUserFlag; trivial.
      + assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) ->
        partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        left;trivial.
      + assert (Hfalse : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
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
      + apply isEntryPageUpdateUserFlag; trivial. 
      + assert(Hi : forall partition : page,
        In partition (getPartitions multiplexer s) -> In phyDescChild (getConfigPages partition s) -> False) 
        by trivial.
        apply Hi with partition.
        assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. assumption.
        assert(  (getConfigPages partition s') = 
        (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        rewrite Hconfig in *.
        assumption.
      + apply entryUserFlagUpdateUserFlagSameValue; intuition.
      + apply entryUserFlagUpdateUserFlagSameValue; intuition.
      + apply entryUserFlagUpdateUserFlagSameValue; intuition.
      + apply entryUserFlagUpdateUserFlagSameValue; intuition.
      + apply entryUserFlagUpdateUserFlagSameValue; intuition. }
(** Internal properties to propagate **)      
        + destruct H.  
        unfold propagatedProperties in *.
        assert(Hi2 : StateLib.getIndexOfAddr va fstLevel = lastIndex) by intuition.
        clear H. intuition.
        { assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
          apply getPartitionsUpdateUserFlag; trivial.
          rewrite Hpartions; assumption. }
        { apply nextEntryIsPPUpdateUserFlag; assumption. }
        { apply isVAUpdateUserFlag; intuition.
          assert( Hisva :  forall idx : index,
                      StateLib.getIndexOfAddr va fstLevel = idx ->
                      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
                      apply Hisva; trivial. }
        { assert ( Hi : forall idx : index,
                  StateLib.getIndexOfAddr va fstLevel = idx ->
                  isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
          generalize (Hi lastIndex Hi2); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          (* assert(Hi3 : nextEntryIsPP descParent sh2idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3. *)
          destruct H7 as (Htrue & Htableroot).
          split; trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.      
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          unfold getTableAddrRoot.
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. }
        { apply isVA'UpdateUserFlag; trivial. }
        { apply  nextEntryIsPPUpdateUserFlag; trivial. }
        { apply  nextEntryIsPPUpdateUserFlag; trivial. }
        { assert(Hi :forall idx : index,
              StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
              isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) 
              by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption. }
        { assert(Hi : forall idx : index,
          StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
          isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Htrue & Htableroot).
          split;trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.         
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. }
      (** WriteAccessible property **) 
      + unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity.
(** ret true after writeAccessible **) 
    intros [].
    eapply weaken.
    eapply WP.ret.
    intros.
    instantiate(1:= fun b s =>propagatedProperties pdChild currentPart currentPD level ptRefChild descChild idxRefChild
       presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1
       ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList presentConfigPagesList
       currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild ptSh1ChildFromSh1
       derivedSh1Child childSh2 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild
       phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
     In descParent (getPartitions MALInternal.multiplexer s) /\
     multiplexer = MALInternal.multiplexer /\
     false = StateLib.Page.eqb descParent multiplexer /\
     nextEntryIsPP descParent sh2idx sh2 s /\
     Some L = StateLib.getNbLevel /\
     StateLib.getIndexOfAddr va fstLevel = lastIndex /\
     (forall idx : index,
      StateLib.getIndexOfAddr va fstLevel = idx ->
      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) /\
     (defaultPage =? ptsh2) = false /\
     isVA' ptsh2 lastIndex vaInAncestor s /\
     nextEntryIsPP descParent PPRidx ancestor s /\
     nextEntryIsPP ancestor PDidx pdAncestor s ).
    simpl. intuition.
(** return false if the page table is null **)
    intros.
    eapply weaken.
    eapply WP.ret.
    simpl. intuition.
(** return false if the virtual address is null **)
  + intros.
    eapply weaken.
    eapply WP.ret.
    simpl. intuition.   
    intuition.
    subst.
    apply beq_nat_false in H7.
    now contradict H7.
    subst.
    apply beq_nat_false in H7.
    now contradict H7. }
  intros. simpl.
  case_eq a.
(** setAccessible success **)
  intros. subst.
  (** recursion **)
  eapply weaken.
  eapply IHn.
  simpl. intuition.
  unfold propagatedProperties in *.
  unfold consistency in * .
  assert (Hparent : parentInPartitionList s) by intuition.
  unfold parentInPartitionList in *.
  apply Hparent with descParent; trivial.
(** setAccessible failed **)
  intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition. 
Qed.

