(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2018)                 *)
(*                                                                             *)
(*  This software is a computer program whose purpose is to run a minimal,     *)
(*  hypervisor relying on proven properties such as memory isolation.          *)
(*                                                                            *)
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
Require Import Core.Internal Isolation Consistency WeakestPreconditions StateLib
Model.Hardware Model.ADT Invariants  DependentTypeLemmas
GetTableAddr Model.MAL Model.Lib Lib InternalLemmas WriteAccessible
PropagatedProperties.
Require Import Coq.Logic.ProofIrrelevance Omega List.
Import List.ListNotations.

   Lemma getParentWriteAccessibleRec n descPart phy 

accessibleChild accessibleSh1 accessibleSh2 accessibleList 
descParent (va : vaddr) pt (phypage : page) idxvaparent pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild: 
{{  fun s : state =>
 propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
 pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s /\
 
isAncestor  currentPart descParent s /\
 ( In descParent (getPartitions MALInternal.multiplexer s)  /\
     (defaultPage =? phypage) = false /\
    (forall idx : index,
StateLib.getIndexOfAddr va fstLevel = idx ->
isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) /\
(defaultPage =? pt) = false /\
StateLib.getIndexOfAddr va fstLevel = idxvaparent /\
entryPresentFlag pt idxvaparent true s /\
entryUserFlag pt idxvaparent false s /\
    isEntryPage pt idxvaparent phypage s /\
    isAccessibleMappedPageInParent descParent va phypage s = true )
  /\ StateLib.getParent descPart (memory s) = phy
    }} 
  Internal.writeAccessibleRecAux n va descParent false {{
    fun _ s  => StateLib.getParent descPart (memory s) = phy
     }}.
Proof.

revert va descParent  pt phypage idxvaparent .
induction n.
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
                  destruct Hcurpart as ( Hancestors & (Hcurpart & Hnewprops) & Hnewpost).
                  clear Hancestors. 
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
  2:{
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
  eapply HP. }
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
  destruct H as 
  ((((((((Hprops & Hi ) & Hcurpart)& Hmult) & Hnotmult) & Hsh2root) & HnblL)
           & Hidxaddr)& H).
           
  destruct Hi as (  Hkk & Hnewprops).
 intuition.
  subst.
  apply beq_nat_false in H.
  now contradict H.
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
  intros pdAncestor. (* 
  unfold setAccessible.
  simpl.
  eapply bindRev.
(** setAccessible **)
  unfold setAccessible.
  { *) eapply bindRev.
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
    case_eq (isdefaultVA).
    -  intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition. 
    - intros isdefaultVAT.
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
      assert(Hcons : consistency s) by intuition.
      unfold consistency in *.
      destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent & _ & _).
      unfold parentInPartitionList in *. 
      instantiate (2:= ancestor).
      split.
      apply Hparent with descParent; intuition.
       
      instantiate (1:= PDidx).
      split. intuition.
      exists pdAncestor.
      split. intuition.
      split. 
      unfold consistency in *.
(*       destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent).  *)
      unfold partitionDescriptorEntry in Hpd.
      unfold parentInPartitionList in *.
      subst.
      assert(Hpartancestor : In ancestor (getPartitions MALInternal.multiplexer s)).
      {       apply Hparent with descParent; intuition. } 
      generalize (Hpd ancestor Hpartancestor); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/PDidx = sh3idx
              \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
            by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hancesnotnull).
      subst.
      assert (Hrootances : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup ancestor i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootances |
        now contradict Hrootances | 
       subst ; assumption| now contradict Hrootances| now contradict Hrootances ]  
       |now contradict Hrootances] | now contradict Hrootances].
      subst. left. split;intuition.
      intro ptvaInAncestor. simpl.
       (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
     2:{
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
      do  16 (* 6 *) rewrite <- and_assoc in H0.
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
      eapply HP. }
  (** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptvaInAncestorIsnull. simpl.
      case_eq ptvaInAncestorIsnull.
      2:{
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
      simpl.
      eapply bindRev; simpl;[|intros []].
      (** writeAccessible **)
      eapply WP.weaken.
      eapply WP.writeAccessible.
      intros. simpl.
      assert (exists entry0 : Pentry,
        lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry0)) as Hlookup.
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
      do 9 rewrite <- and_assoc in H.
      destruct H as (Hsplit & Hfalse & Hrest).
      assert(Heqphy : phypage = pa entry).
      {    destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (Hnew & Hll & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
         intuition. subst.
        unfold isAccessibleMappedPageInParent in *.
        assert (HgetVirt : getVirtualAddressSh2 sh2 s va  = Some vaInAncestor).
        apply isVaInParent with descParent ptsh2;trivial.
        apply nextEntryIsPPgetSndShadow in Hppsh2.
        rewrite Hppsh2 in *.
        rewrite HgetVirt in *.
        rewrite nextEntryIsPPgetParent in * .
        rewrite Hppparent in *. 
        apply nextEntryIsPPgetPd in Hpppd .
        rewrite Hpppd in *.
        case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor);
        intros * Hacce;
        rewrite Hacce in *;try now contradict Hfalse.
        unfold getAccessibleMappedPage in Hacce.
        assert( isPE ptvaInAncestor  (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) as (Hve & Hroot ).
        apply Hgetroot2;trivial.
        unfold getTableAddrRoot in *.
        destruct Hroot as (_ & Hroot).
        rewrite <- nextEntryIsPPgetPd in *.
        apply Hroot in  Hpppd.
        clear Hroot.
        destruct Hpppd as (nbL & HnbL & stop & Hstop & Hind).
        subst.
        rewrite <- HnbL in *.
        assert(Hgetind : getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s  
        = Some ptvaInAncestor).
        apply getIndirectionStopLevelGT2 with (nbL+1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind in *.
        rewrite H in *.
        destruct ( StateLib.readPresent ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s));try now contradict Hacce.
        destruct b;try now contradict Hacce.
        destruct ( StateLib.readAccessible ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s)); try now contradict Hacce.
        destruct b; try now contradict Hacce.
        unfold StateLib.readPhyEntry in *. 
        rewrite Hlookup in *.
        apply beq_nat_true in Hfalse.
        inversion Hacce.
        subst.
        destruct phypage; destruct (pa entry).
        simpl in *.
        subst.
        f_equal; apply proof_irrelevance. }
      assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true).
      { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        rewrite Heqphy.
        destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
        apply isAccessibleMappedPageInParentTrue with descParent va phypage ptvaInAncestor ptsh2 pdAncestor;
        subst;intuition.
        subst;assumption. }
      repeat rewrite and_assoc in Hsplit.
      destruct Hsplit as (Hprops & Hsplit).
(*       unfold propagatedProperties in *.
      do 73 rewrite <- and_assoc in Hprops.
      destruct Hprops as (Hprops & xx & Hprops2). 
            repeat rewrite and_assoc in Hprops. *)
      assert (Hnewprops := conj  Hprops  Hsplit).
      assert (H := conj (conj Hnewprops Htrue) Hrest).
      simpl.
      clear Hnewprops.
    (*   repeat rewrite and_assoc in H. *)
      pattern s in H.
      match type of H with 
      | ?HT s => instantiate (1 := fun tt s => HT s  /\ 
                  entryUserFlag ptvaInAncestor idxva false s /\
                  isEntryPage ptvaInAncestor idxva phypage s /\
                  entryPresentFlag ptvaInAncestor idxva true s  ) 
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
      simpl.
      unfold propagatedProperties in *. 
      do 7 rewrite and_assoc.
      clear Hrest  Hsplit  Hprops.
      split.
      
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
      split.
      (** partitionDescriptorEntry **)
      apply partitionDescriptorEntryUpdateUserFlag;trivial.
      intuition.
      (** dataStructurePdSh1Sh2asRoot **)
      destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
      Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct(*  & Hn1 & Hn2 & Hn3 & Hn4 & Hn5 & Hn6
      & Hn7 & Hn8 & Hn9 & Hn10 & Hn11 & Hn12 & Hn13 *)).
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      (** currentPartitionInPartitionsList **)
      split.
      unfold currentPartitionInPartitionsList in *.
      simpl in *. subst. 
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite Hpartions. assumption.
      (** noDupMappedPagesList **)  
      split.    
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
      split.
      (** noDupConfigPagesList **)
      apply getIndirectionsNoDupUpdateUserFlag; trivial.
      split.
      (** parentInPartitionList **)
      unfold parentInPartitionList in *.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart.
      intros partition HgetParts parent Hroot.
      generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
      apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
      apply Hparent; trivial.
      split.
      (** accessibleVAIsNotPartitionDescriptor **)
     unfold s'.
      subst.
      clear IHn.
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (_ & Hi).
      intuition.
      subst.
      apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag  with level ancestor   
        pdAncestor;trivial.
      assert(Hparentpart : parentInPartitionList s) by trivial.
      unfold parentInPartitionList in *.
      apply Hparent with descParent;trivial. 
       assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
      assert(  isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s ) as (_ & Hroot).
      apply Hget;split;trivial.
      assumption.
      apply nextEntryIsPPgetPd;trivial.
      subst.
      assert(HaccessInParent : isAccessibleMappedPageInParent descParent va (pa entry) s = true)
       by trivial.
       unfold isAccessibleMappedPageInParent in HaccessInParent.
       (** Here we use the property already present into the precondition : 
            *)
       assert(Hcursh2 : nextEntryIsPP descParent sh2idx sh2 s ) by trivial.
      apply nextEntryIsPPgetSndShadow in Hcursh2.
      rewrite Hcursh2 in HaccessInParent.
      assert(Hvainparent : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
      { assert(Hxx : forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx ->
        isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
        assert(Hgetva : isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\ 
        getTableAddrRoot ptsh2 sh2idx descParent va s).
        apply Hxx;trivial. clear Hxx.
        destruct Hgetva as (Hva & Hgetva).
        assert(Hisva : isVA' ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s) 
        by trivial.
        unfold getVirtualAddressSh2.
        unfold getTableAddrRoot in Hgetva.
        destruct Hgetva as (_ & Hgetva).
        assert(HcurSh2 : nextEntryIsPP descParent sh2idx sh2 s).
        rewrite  nextEntryIsPPgetSndShadow ;trivial.
        apply Hgetva in HcurSh2.
        destruct HcurSh2 as (nbL & HnbL & stop & Hstop & Hind).
        rewrite <- HnbL.
        subst.
        assert(Hgetind : getIndirection sh2 va nbL (nbLevel - 1) s = Some ptsh2).
        apply getIndirectionStopLevelGT2 with (nbL + 1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind.
        assert (Hptnotnull : (defaultPage =? ptsh2) = false) by trivial.
        rewrite Hptnotnull.
        unfold  isVA' in *. 
        unfold StateLib.readVirtual.
        destruct(lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ); 
        try now contradict Hisva.
        destruct v;try now contradict Hisva.
        subst. trivial. }
      rewrite Hvainparent in *.
      assert(Hgetparent : StateLib.getParent descParent (memory s) = Some ancestor).
      { apply nextEntryIsPPgetParent;trivial. }
      rewrite Hgetparent in *.
      assert(Hgetpdparent : StateLib.getPd ancestor (memory s) = Some pdAncestor).
      { apply nextEntryIsPPgetPd;trivial. }
      rewrite Hgetpdparent in *.
      case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor ); intros * Hi .
      rewrite Hi in *.
      unfold getAccessibleMappedPage in Hi.
      case_eq (StateLib.getNbLevel);intros * Hi2 ; rewrite Hi2 in *;
       try now contradict Hi.
      assert(Hancestor : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by 
      trivial.
      assert(Hget : isPE ptvaInAncestor ( StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\
            getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s).
      apply Hancestor; clear Hancestor;
      trivial.
      destruct Hget as (Hva & Hget).
      unfold getTableAddrRoot in Hget.
      destruct Hget as (_ & Hget).
      apply nextEntryIsPPgetPd in Hgetpdparent.
      apply Hget in Hgetpdparent.
      destruct Hgetpdparent as (nbL & HnbL & stop & Hstop & Hgettable).
      clear Hget.
      rewrite <- HnbL in *.
      inversion Hi2.
      subst.
      assert(Hind :getIndirection pdAncestor vaInAncestor l (nbLevel - 1) s = Some ptvaInAncestor).
      apply getIndirectionStopLevelGT2 with (l+1);trivial.
      omega.
      apply getNbLevelEq in HnbL.
      rewrite HnbL.
      unfold CLevel.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      simpl;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      rewrite Hind in *.
      assert (Hnotnull : (defaultPage =? ptvaInAncestor) = false) by trivial.
      rewrite Hnotnull in *.
      destruct (StateLib.readPresent ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b; try now contradict Hi.
      destruct(StateLib.readAccessible ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b.
      unfold StateLib.readPhyEntry in *.
      rewrite Hlookup in *.
      symmetry; assumption.
      now contradict Hi.
      rewrite Hi in *. 
      now contradict HaccessInParent.
            rewrite Hi in *. 
      now contradict HaccessInParent.
   (* accessibleChildPageIsAccessibleIntoParent *)
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (Hancestor & Hi).
      unfold s'.
      intuition. 
      subst.
      clear IHn.
      apply accessibleChildPageIsAccessibleIntoParentUpdateUserFlagFlase
      with level ancestor pdAncestor va ptsh2 descParent pt;trivial.
      assert(Hparentpart : parentInPartitionList s).
      unfold consistency in *; intuition.
      unfold parentInPartitionList in *.
      apply Hparentpart with descParent;trivial.
      (* noCycleInPartitionTree *)
      assert(Hdiff : noCycleInPartitionTree s) by trivial.
      unfold noCycleInPartitionTree in *.
      intros parent partition Hparts Hparentpart.
      simpl in *.
      assert (getPartitions multiplexer {|
              currentPartition := currentPartition s;
              memory := add ptvaInAncestor idxva
                          (PE
                             {|
                             read := read entry;
                             write := write entry;
                             exec := exec entry;
                             present := present entry;
                             user := false;
                             pa := pa entry |}) (memory s) beqPage beqIndex |}
               = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(HgetParent : getAncestors partition
                {|
                   currentPartition := currentPartition s;
                   memory := add ptvaInAncestor idxva
                               (PE
                                  {|
                                  read := read entry;
                                  write := write entry;
                                  exec := exec entry;
                                  present := present entry;
                                  user := false;
                                  pa := pa entry |}) (memory s) beqPage beqIndex |} = 
                      getAncestors partition  s).
      apply getAncestorsUpdateUserFlag;trivial.
      rewrite HgetParent in *; clear HgetParent.
      apply Hdiff;trivial.
      (* configTablesAreDifferent *)
      assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
      unfold configTablesAreDifferent in *.
      simpl in *.
      fold s'.
      intros partition1 partition2 Hpart1 Hpart2 Hdiff.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      apply Hconfigdiff;trivial.
      rename H into Hcond.
      (** isChild **)
      assert(Hchid : isChild s) by intuition.
      unfold isChild in *.
      simpl in *.
      intros partition parent Hparts Hgetparent.
      rewrite getPartitionsUpdateUserFlag in *;trivial.
      rewrite getParentUpdateUserFlag in *;trivial.
      rewrite getChildrenUpdateFlagUser;trivial.
      apply Hchid;trivial.
          (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    (** physicalPageNotDerived **)
    apply physicalPageNotDerivedUpdateUserFlag;trivial.
    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by trivial.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.  
    (** isParent  *)
    assert(Hisparent : isParent s) by trivial.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by trivial.
    unfold noDupPartitionTree in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by trivial.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va0 = Some vainparent).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by trivial.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh0 s va0 = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    apply getVirtualAddressSh2UpdateUserFlag;trivial.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    
    (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by trivial.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by trivial.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.
  (** Propagated properties **)
      assert(Hi2 : StateLib.getIndexOfAddr va fstLevel = lastIndex) by intuition.
      {  intuition trivial. 
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
          unfold getTableAddrRoot.
          destruct H23 as (Hor & Htableroot).
          split;trivial.
          intros.         
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          left.
          clear IHn.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }

            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            { apply Hconfigdiff;trivial. 
              assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial. }
            assert(Hin1 : In ptRefChild (getConfigPages descParent s)).
            { apply isConfigTable with descChild;trivial.
            intuition. subst. trivial. }
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            { apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            subst.
           apply Hparet with (currentPartition s);trivial. }
            unfold disjoint in *.
            unfold not; intros. subst.             
            apply Hdisjoint with ptvaInAncestor;trivial.
          - unfold consistency in *.
            subst.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
            {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
             unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages (currentPartition s) s)).
            apply isConfigTable with descChild;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.

            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
(** partitions are diffrent then config pages are different *)
        + assert(Hi3 : forall idx : index,
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
           unfold getTableAddrRoot.
          destruct H7 as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi4 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.
        
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagSameValue;trivial.
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert (Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
                  assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            { apply Hconfigdiff;trivial. 
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial. }
            assert(Hin1 : In ptSh1Child (getConfigPages descParent s)).
            { apply isConfigTable with shadow1;trivial.
              intuition. subst;trivial.  }
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            { apply isConfigTable with vaInAncestor;trivial.
              intuition.
              assert(Hparet : parentInPartitionList s) by intuition.
              unfold parentInPartitionList in *.
              apply Hparet with descParent;trivial. }
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages (currentPartition s) s)).
            apply isConfigTable with shadow1;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.       
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.

        assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
        unfold isAncestor in *.
        destruct Hisancestor as [Hisancestor | Hisancestor].
        - subst currentPart.
          clear IHn.
          rewrite Hisancestor in *.
          left.
          unfold consistency in *.
          assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *.
          assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages descParent s)).
          { apply isConfigTable with shadow2;trivial.
          intuition. }
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2.
        - unfold consistency in *.
          subst.
          clear IHn.
          assert(In (currentPartition s) (getPartitions multiplexer s)).
          unfold currentPartitionInPartitionsList in *.
          intuition.
          assert((currentPartition s) <> ancestor).
          { unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *. 
          assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages (currentPartition s) s)).
          apply isConfigTable with shadow2;trivial.
          intuition.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          left.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
            rewrite Hisancestor in *.
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages descParent s)).
            apply isConfigTable with list;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages (currentPartition s) s)).
            apply isConfigTable with list;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi4 : nextEntryIsPP currentPart sh1idx tableroot s') by intuition.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.      
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
         
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.

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
      + assert (Hfalse' : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. 
        assert((getConfigPages partition s') = 
             (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        rewrite Hconfig in *.
        assert(Hii : forall partition : page,
            In partition (getPartitions multiplexer s) -> 
            In phyDescChild (getConfigPages partition s) -> False) by trivial.
        assert(Hfalse' : In phyDescChild (getConfigPages partition s)) by trivial.
        apply Hii in Hfalse';trivial. 
      + unfold isPartitionFalse. 
         unfold s'.
         cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
         
(** Internal properties to propagate **)      
      + unfold s'.
        apply isAncestorUpdateUserFlag;trivial. 
      + destruct H.  
        unfold propagatedProperties in *.
        { assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
          apply getPartitionsUpdateUserFlag; trivial.
          rewrite Hpartions; assumption. }
       
      + apply isPEUpdateUserFlag;trivial. 
          assert(Hpe : forall idx : index,
                StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ 
                getTableAddrRoot pt PDidx descParent va s) 
          by trivial.
           apply Hpe;trivial.
      +  assert(Hroot : isPE pt (StateLib.getIndexOfAddr va fstLevel ) s /\
          getTableAddrRoot pt PDidx descParent va s).
          assert(Hpe : forall idx : index,
           StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) 
            by trivial.
          apply Hpe;trivial.
          destruct Hroot as (Hve & Hroot). 
          unfold getTableAddrRoot in *.
          destruct Hroot as (Hor & Hroot).
          split;trivial.
          intros root Hpp.
          unfold s' in Hpp.
          apply nextEntryIsPPUpdateUserFlag' in Hpp.
          apply Hroot in Hpp.
          destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
          exists nbL ; split;trivial.
          exists stop;split;trivial.
          rewrite <- Hind.
          unfold s'.
          apply getIndirectionUpdateUserFlag;trivial. 
       +  apply entryPresentFlagUpdateUserFlag;trivial. 
       + apply entryUserFlagUpdateUserFlagSameValue;trivial.
       +  apply isEntryPageUpdateUserFlag;trivial. 
       +  subst. clear IHn.       
          assert(HisAccess : isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s' =
          isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow ancestor (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt : getVirtualAddressSh2 p
                             {| currentPartition := currentPartition s;
                              memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                              (PE
                                 {|
                                 read := read entry;
                                 write := write entry;
                                 exec := exec entry;
                                 present := present entry;
                                 user := false;
                                 pa := pa entry |}) (memory s) beqPage beqIndex |} vaInAncestor =
                            getVirtualAddressSh2 p s vaInAncestor).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some L = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p vaInAncestor L (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s vaInAncestor );
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent ancestor (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
                          {|
                          currentPartition := currentPartition s;
                          memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                                      (PE
                                         {|
                                         read := read entry;
                                         write := write entry;
                                         exec := exec entry;
                                         present := present entry;
                                         user := false;
                                         pa := pa entry |}) (memory s) beqPage beqIndex |} v = 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In ancestor (getPartitions multiplexer s)).
                apply Hparentpart with descParent;trivial.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions with ancestor p0;trivial.
                unfold consistency in *.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
                        isPE ptvaInAncestor idx s /\ 
                        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                as (Hpe & Hroot);
                trivial.
                apply Hparentpart with ancestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdiff1 : p0 <> ancestor).
                              assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                              apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              assert(Hparentinpart : parentInPartitionList s) by intuition.
              unfold parentInPartitionList in *.
              apply Hparentinpart with ancestor;trivial.
              rewrite nextEntryIsPPgetParent;trivial.
              unfold not;intros Hfalsei;subst.
              now contradict Hdiff1.
              }
              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold partitionDescriptorEntry in *.
              assert(exists entry : page, nextEntryIsPP descParent PDidx entry s /\
                      entry <> defaultPage) as (pdParent & Hpp & Hnotnull).
              apply Hpde;trivial.
              left;trivial.
              clear Hpde.
              apply nextEntryIsPPgetPd in Hpp.
              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
        + assert(Heq : StateLib.getParent descPart
                      (add ptvaInAncestor idxva
                         (PE
                            {|
                            read := read entry;
                            write := write entry;
                            exec := exec entry;
                            present := present entry;
                            user := false;
                            pa := pa entry |}) (memory s) beqPage beqIndex) = StateLib.getParent descPart
                      (memory s)). apply getParentUpdateUserFlag; trivial.
                      rewrite Heq in *;trivial. 
        + apply nextEntryIsPPUpdateUserFlag; assumption. 
        + apply isVAUpdateUserFlag; intuition.
          assert( Hisva :  forall idx : index,
                      StateLib.getIndexOfAddr va fstLevel = idx ->
                      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
                      apply Hisva; trivial. 
        + assert ( Hi : forall idx : index,
                  StateLib.getIndexOfAddr va fstLevel = idx ->
                  isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
          generalize (Hi lastIndex Hi2); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split; trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.      
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          unfold getTableAddrRoot.
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply isVA'UpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + assert(Hi :forall idx : index,
              StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
              isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) 
              by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption. 
        + assert(Hi : forall idx : index,
          StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
          isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split;trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.         
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
      (** WriteAccessible property **) 
      + unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. 
      + unfold isEntryPage.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  cbn. reflexivity.
      + unfold entryPresentFlag.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  
        cbn.
        unfold consistency in *.
        assert(Hpres : isPresentNotDefaultIff s ) by intuition.
        symmetry.
        apply phyPageIsPresent with ptvaInAncestor idxva s;trivial. }

(** setAccessible success **)
  simpl. subst. 
  (** recursion **)
  eapply weaken.
  eapply IHn.
  simpl. intros.
  assert(Hancestorpart : In ancestor (getPartitions MALInternal.multiplexer s)).
  { unfold propagatedProperties in *.
    unfold consistency in * .
    assert (Hparent : parentInPartitionList s) by intuition.
    unfold parentInPartitionList in *.
    apply Hparent with descParent; intuition. }
  assert (Hparentchild : In descParent (getChildren ancestor s)).
  unfold propagatedProperties in *.
  unfold consistency in *.
  assert(Hchildren : isChild s) by intuition.
  unfold isChild in *.
      apply Hchildren;trivial.
      intuition.
      apply nextEntryIsPPgetParent;intuition.
  assert(Hvs : verticalSharing s).
   { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. }
    unfold verticalSharing in *.
  assert(Hvsall : incl (getUsedPages descParent s) (getMappedPages ancestor s)).
  apply Hvs;trivial.
  clear Hvs.
  apply verticalSharing2 in Hvsall.
  unfold incl in *.
  generalize(Hvsall phypage);clear Hvsall; intros Hvs.
  assert(Hdescpage : In phypage (getMappedPages descParent s)).
  { intuition.
    subst.
    assert(Hpde : partitionDescriptorEntry s).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. } 
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP descParent PDidx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    left;trivial.
    destruct Hentrypd as (pdParent & Hpp & Hnotnul).
    apply inGetMappedPagesGetTableRoot with va pt pdParent ;trivial.

}

apply Hvs in Hdescpage.
clear Hvs.
unfold getMappedPages in *.
assert(HpdAncestor : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
rewrite nextEntryIsPPgetPd in *.
rewrite HpdAncestor in *.
unfold getMappedPagesAux in *.

apply filterOptionInIff in Hdescpage.
unfold getMappedPagesOption in *.
apply in_map_iff in Hdescpage.
destruct Hdescpage as (newVA & Hmapped & Hinvas).
unfold getMappedPage in Hmapped.
assert(Hlevel : Some L = StateLib.getNbLevel) by intuition.
rewrite <- Hlevel in *.
case_eq(getIndirection pdAncestor newVA L (nbLevel - 1) s);[intros ptAncestor HptAncestor |
intros HptAncestor];rewrite HptAncestor in *;try now contradict Hmapped.
case_eq(defaultPage =? ptAncestor);intros Hb;rewrite Hb in *;try now contradict Hmapped.
case_eq(StateLib.readPresent ptAncestor (StateLib.getIndexOfAddr newVA fstLevel) (memory s));
[intros present Hpresent |
intros Hpresent];rewrite Hpresent in *;try now contradict Hmapped.

destruct present;[| inversion Hmapped;subst;
 rewrite isNotDefaultPageFalse in Hnotdef;
 now contradict Hnotdef].

(* assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaInAncestor va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).   *)
(* assert(va1 = newVA).
{ destruct H as (((((Ha & Hk )& Hi ) & Hj ) & Hl ) & Hm).
  intuition.
  clear IHn.
  subst.
  apply eqMappedPagesEqVaddrs with phypage pdAncestor s;trivial.
  assert(Hnewgoal : getMappedPage pdAncestor s vaInAncestor = Some phypage).
  apply getMappedPageGetTableRoot with ptvaInAncestor ancestor;trivial.
  rewrite nextEntryIsPPgetPd in *;trivial.
  rewrite <- Hnewgoal.
  symmetry.
  apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
  apply getNbLevelEqOption.
  apply getMappedPageGetIndirection with ancestor ptAncestor L;trivial.
    rewrite nextEntryIsPPgetPd in *;trivial.
  assert (Hnodupmapped : noDupMappedPagesList s).
  unfold consistency in *;intuition.
  unfold noDupMappedPagesList in *.
  assert(Hnewnodup : NoDup (getMappedPages ancestor s)).
  apply Hnodupmapped;trivial.
  unfold getMappedPages in Hnewnodup.
  rewrite HpdAncestor in *.
  unfold getMappedPagesAux  in *.
  assumption. } *)
instantiate(1:= phypage).
instantiate (1:= StateLib.getIndexOfAddr vaInAncestor fstLevel).
instantiate (1:= ptvaInAncestor).

  split.
 intuition.
 split.
 assert(Hisancestor : isAncestor currentPart descParent s) by intuition.
 rewrite nextEntryIsPPgetParent in *.
unfold propagatedProperties in *. 
unfold consistency in *. 
apply isAncestorTrans with descParent;intuition.
unfold propagatedProperties in *. 
             unfold consistency in *. intuition.
(* unfold propagatedProperties in *. 
             unfold consistency in *. intuition.
              *)
            unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition.
            
intuition.
 subst;trivial.
   subst;trivial.
  subst;trivial. 
    
}

(** setAccessible failed **)
 intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition.

Qed.



Lemma getMappedPageWriteAccessibleRec n  pd va1  X
accessibleChild accessibleSh1 accessibleSh2 accessibleList 
descParent (va : vaddr) pt (phypage : page) idxvaparent pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild: 
{{  fun s : state =>
 propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
 pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s /\
 
isAncestor  currentPart descParent s /\
 ( In descParent (getPartitions MALInternal.multiplexer s)  /\
     (defaultPage =? phypage) = false /\
    (forall idx : index,
StateLib.getIndexOfAddr va fstLevel = idx ->
isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) /\
(defaultPage =? pt) = false /\
StateLib.getIndexOfAddr va fstLevel = idxvaparent /\
entryPresentFlag pt idxvaparent true s /\
entryUserFlag pt idxvaparent false s /\
    isEntryPage pt idxvaparent phypage s /\
    isAccessibleMappedPageInParent descParent va phypage s = true )
  /\ getMappedPage pd  s va1 = X
    }} 
  Internal.writeAccessibleRecAux n va descParent false {{
    fun _ s  => getMappedPage pd s va1 = X
     }}.
Proof.
revert va descParent  pt phypage idxvaparent .
induction n.
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
                  destruct Hcurpart as ( Hancestors & (Hcurpart & Hnewprops) & Hnewpost).
                  clear Hancestors. 
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
  2:{
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
  } (** comparePageToNull **) 
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
  destruct H as 
  ((((((((Hprops & Hi ) & Hcurpart)& Hmult) & Hnotmult) & Hsh2root) & HnblL)
           & Hidxaddr) & H).
           
  destruct Hi as (  Hkk & Hnewprops).
 intuition.
  subst.
  apply beq_nat_false in H.
  now contradict H.
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
  intros pdAncestor. (* 
  unfold setAccessible.
  simpl.
  eapply bindRev.
(** setAccessible **)
  unfold setAccessible.
  { *) eapply bindRev.
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
    case_eq (isdefaultVA).
    -  intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition. 
    - intros isdefaultVAT.
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
      assert(Hcons : consistency s) by intuition.
      unfold consistency in *.
      destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent & _ & _).
      unfold parentInPartitionList in *. 
      instantiate (2:= ancestor).
      split.
      apply Hparent with descParent; intuition.
       
      instantiate (1:= PDidx).
      split. intuition.
      exists pdAncestor.
      split. intuition.
      split. 
      unfold consistency in *.
(*       destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent).  *)
      unfold partitionDescriptorEntry in Hpd.
      unfold parentInPartitionList in *.
      subst.
      assert(Hpartancestor : In ancestor (getPartitions MALInternal.multiplexer s)).
      {       apply Hparent with descParent; intuition. } 
      generalize (Hpd ancestor Hpartancestor); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/PDidx = sh3idx
              \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
            by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hancesnotnull).
      subst.
      assert (Hrootances : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup ancestor i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootances |
        now contradict Hrootances | 
       subst ; assumption| now contradict Hrootances| now contradict Hrootances ]  
       |now contradict Hrootances] | now contradict Hrootances].
      subst. left. split;intuition.
      intro ptvaInAncestor. simpl.
       (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2:{
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
      do  16 (* 6 *) rewrite <- and_assoc in H0.
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
  } (** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptvaInAncestorIsnull. simpl.
      case_eq ptvaInAncestorIsnull.
      2:{
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
      simpl.
      eapply bindRev; simpl;[|intros []].
      (** writeAccessible **)
      eapply WP.weaken.
      eapply WP.writeAccessible.
      intros. simpl.
      assert (exists entry0 : Pentry,
        lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry0)) as Hlookup.
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
      do 9 rewrite <- and_assoc in H.
      destruct H as (Hsplit & Hfalse & Hrest).
      assert(Heqphy : phypage = pa entry).
      {    destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (Hnew & Hll & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
         intuition. subst.
        unfold isAccessibleMappedPageInParent in *.
        assert (HgetVirt : getVirtualAddressSh2 sh2 s va  = Some vaInAncestor).
        apply isVaInParent with descParent ptsh2;trivial.
        apply nextEntryIsPPgetSndShadow in Hppsh2.
        rewrite Hppsh2 in *.
        rewrite HgetVirt in *.
        rewrite nextEntryIsPPgetParent in * .
        rewrite Hppparent in *. 
        apply nextEntryIsPPgetPd in Hpppd .
        rewrite Hpppd in *.
        case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor);
        intros * Hacce;
        rewrite Hacce in *;try now contradict Hfalse.
        unfold getAccessibleMappedPage in Hacce.
        assert( isPE ptvaInAncestor  (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) as (Hve & Hroot ).
        apply Hgetroot2;trivial.
        unfold getTableAddrRoot in *.
        destruct Hroot as (_ & Hroot).
        rewrite <- nextEntryIsPPgetPd in *.
        apply Hroot in  Hpppd.
        clear Hroot.
        destruct Hpppd as (nbL & HnbL & stop & Hstop & Hind).
        subst.
        rewrite <- HnbL in *.
        assert(Hgetind : getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s  
        = Some ptvaInAncestor).
        apply getIndirectionStopLevelGT2 with (nbL+1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind in *.
        rewrite H in *.
        destruct ( StateLib.readPresent ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s));try now contradict Hacce.
        destruct b;try now contradict Hacce.
        destruct ( StateLib.readAccessible ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s)); try now contradict Hacce.
        destruct b; try now contradict Hacce.
        unfold StateLib.readPhyEntry in *. 
        rewrite Hlookup in *.
        apply beq_nat_true in Hfalse.
        inversion Hacce.
        subst.
        destruct phypage; destruct (pa entry).
        simpl in *.
        subst.
        f_equal; apply proof_irrelevance. }
      assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true).
      { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        rewrite Heqphy.
        destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
        apply isAccessibleMappedPageInParentTrue with descParent va phypage ptvaInAncestor ptsh2 pdAncestor;
        subst;intuition.
        subst;assumption. }
      repeat rewrite and_assoc in Hsplit.
      destruct Hsplit as (Hprops & Hsplit).
(*       unfold propagatedProperties in *.
      do 73 rewrite <- and_assoc in Hprops.
      destruct Hprops as (Hprops & xx & Hprops2). 
            repeat rewrite and_assoc in Hprops. *)
      assert (Hnewprops := conj  Hprops  Hsplit).
      assert (H := conj (conj Hnewprops Htrue) Hrest).
      simpl.
      clear Hnewprops.
    (*   repeat rewrite and_assoc in H. *)
      pattern s in H.
      match type of H with 
      | ?HT s => instantiate (1 := fun tt s => HT s  /\ 
                  entryUserFlag ptvaInAncestor idxva false s /\
                  isEntryPage ptvaInAncestor idxva phypage s /\
                  entryPresentFlag ptvaInAncestor idxva true s  ) 
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
      simpl.
      unfold propagatedProperties in *. 
      do 7 rewrite and_assoc.
      clear Hrest  Hsplit  Hprops.
      split.
      
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
      split.
      (** partitionDescriptorEntry **)
      apply partitionDescriptorEntryUpdateUserFlag;trivial.
      intuition.
      (** dataStructurePdSh1Sh2asRoot **)
      destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
      Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      (** currentPartitionInPartitionsList **)
      split.
      unfold currentPartitionInPartitionsList in *.
      simpl in *. subst. 
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite Hpartions. assumption.
      (** noDupMappedPagesList **)  
      split.    
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
      split.
      (** noDupConfigPagesList **)
      apply getIndirectionsNoDupUpdateUserFlag; trivial.
      split.
      (** parentInPartitionList **)
      unfold parentInPartitionList in *.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart.
      intros partition HgetParts parent Hroot.
      generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
      apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
      apply Hparent; trivial.
      split.
      (** accessibleVAIsNotPartitionDescriptor **)
     unfold s'.
      subst.
      clear IHn.
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (_ & Hi).
      intuition.
      subst.
      apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag  with level ancestor   
        pdAncestor;trivial.
      assert(Hparentpart : parentInPartitionList s) by trivial.
      unfold parentInPartitionList in *.
      apply Hparent with descParent;trivial. 
       assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
      assert(  isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s ) as (_ & Hroot).
      apply Hget;split;trivial.
      assumption.
      apply nextEntryIsPPgetPd;trivial.
      subst.
      assert(HaccessInParent : isAccessibleMappedPageInParent descParent va (pa entry) s = true)
       by trivial.
       unfold isAccessibleMappedPageInParent in HaccessInParent.
       (** Here we use the property already present into the precondition : 
            *)
       assert(Hcursh2 : nextEntryIsPP descParent sh2idx sh2 s ) by trivial.
      apply nextEntryIsPPgetSndShadow in Hcursh2.
      rewrite Hcursh2 in HaccessInParent.
      assert(Hvainparent : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
      { assert(Hxx : forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx ->
        isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
        assert(Hgetva : isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\ 
        getTableAddrRoot ptsh2 sh2idx descParent va s).
        apply Hxx;trivial. clear Hxx.
        destruct Hgetva as (Hva & Hgetva).
        assert(Hisva : isVA' ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s) 
        by trivial.
        unfold getVirtualAddressSh2.
        unfold getTableAddrRoot in Hgetva.
        destruct Hgetva as (_ & Hgetva).
        assert(HcurSh2 : nextEntryIsPP descParent sh2idx sh2 s).
        rewrite  nextEntryIsPPgetSndShadow ;trivial.
        apply Hgetva in HcurSh2.
        destruct HcurSh2 as (nbL & HnbL & stop & Hstop & Hind).
        rewrite <- HnbL.
        subst.
        assert(Hgetind : getIndirection sh2 va nbL (nbLevel - 1) s = Some ptsh2).
        apply getIndirectionStopLevelGT2 with (nbL + 1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind.
        assert (Hptnotnull : (defaultPage =? ptsh2) = false) by trivial.
        rewrite Hptnotnull.
        unfold  isVA' in *. 
        unfold StateLib.readVirtual.
        destruct(lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ); 
        try now contradict Hisva.
        destruct v;try now contradict Hisva.
        subst. trivial. }
      rewrite Hvainparent in *.
      assert(Hgetparent : StateLib.getParent descParent (memory s) = Some ancestor).
      { apply nextEntryIsPPgetParent;trivial. }
      rewrite Hgetparent in *.
      assert(Hgetpdparent : StateLib.getPd ancestor (memory s) = Some pdAncestor).
      { apply nextEntryIsPPgetPd;trivial. }
      rewrite Hgetpdparent in *.
      case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor ); intros * Hi .
      rewrite Hi in *.
      unfold getAccessibleMappedPage in Hi.
      case_eq (StateLib.getNbLevel);intros * Hi2 ; rewrite Hi2 in *;
       try now contradict Hi.
      assert(Hancestor : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by 
      trivial.
      assert(Hget : isPE ptvaInAncestor ( StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\
            getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s).
      apply Hancestor; clear Hancestor;
      trivial.
      destruct Hget as (Hva & Hget).
      unfold getTableAddrRoot in Hget.
      destruct Hget as (_ & Hget).
      apply nextEntryIsPPgetPd in Hgetpdparent.
      apply Hget in Hgetpdparent.
      destruct Hgetpdparent as (nbL & HnbL & stop & Hstop & Hgettable).
      clear Hget.
      rewrite <- HnbL in *.
      inversion Hi2.
      subst.
      assert(Hind :getIndirection pdAncestor vaInAncestor l (nbLevel - 1) s = Some ptvaInAncestor).
      apply getIndirectionStopLevelGT2 with (l+1);trivial.
      omega.
      apply getNbLevelEq in HnbL.
      rewrite HnbL.
      unfold CLevel.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      simpl;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      rewrite Hind in *.
      assert (Hnotnull : (defaultPage =? ptvaInAncestor) = false) by trivial.
      rewrite Hnotnull in *.
      destruct (StateLib.readPresent ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b; try now contradict Hi.
      destruct(StateLib.readAccessible ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b.
      unfold StateLib.readPhyEntry in *.
      rewrite Hlookup in *.
      symmetry; assumption.
      now contradict Hi.
      rewrite Hi in *. 
      now contradict HaccessInParent.
            rewrite Hi in *. 
      now contradict HaccessInParent.
   (* accessibleChildPageIsAccessibleIntoParent *)
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (Hancestor & Hi).
      unfold s'.
      intuition. 
      subst.
      clear IHn.
      apply accessibleChildPageIsAccessibleIntoParentUpdateUserFlagFlase
      with level ancestor pdAncestor va ptsh2 descParent pt;trivial.
      assert(Hparentpart : parentInPartitionList s).
      unfold consistency in *; intuition.
      unfold parentInPartitionList in *.
      apply Hparentpart with descParent;trivial.
      (* noCycleInPartitionTree *)
      assert(Hdiff : noCycleInPartitionTree s) by trivial.
      unfold noCycleInPartitionTree in *.
      intros parent partition Hparts Hparentpart.
      simpl in *.
      assert (getPartitions multiplexer {|
              currentPartition := currentPartition s;
              memory := add ptvaInAncestor idxva
                          (PE
                             {|
                             read := read entry;
                             write := write entry;
                             exec := exec entry;
                             present := present entry;
                             user := false;
                             pa := pa entry |}) (memory s) beqPage beqIndex |}
               = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(HgetParent : getAncestors partition
                {|
                   currentPartition := currentPartition s;
                   memory := add ptvaInAncestor idxva
                               (PE
                                  {|
                                  read := read entry;
                                  write := write entry;
                                  exec := exec entry;
                                  present := present entry;
                                  user := false;
                                  pa := pa entry |}) (memory s) beqPage beqIndex |} = 
                      getAncestors partition  s).
      apply getAncestorsUpdateUserFlag;trivial.
      rewrite HgetParent in *; clear HgetParent.
      apply Hdiff;trivial.
      (* configTablesAreDifferent *)
      assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
      unfold configTablesAreDifferent in *.
      simpl in *.
      fold s'.
      intros partition1 partition2 Hpart1 Hpart2 Hdiff.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      apply Hconfigdiff;trivial.
      rename H into Hcond.
      (** isChild **)
      assert(Hchid : isChild s) by intuition.
      unfold isChild in *.
      simpl in *.
      intros partition parent Hparts Hgetparent.
      rewrite getPartitionsUpdateUserFlag in *;trivial.
      rewrite getParentUpdateUserFlag in *;trivial.
      rewrite getChildrenUpdateFlagUser;trivial.
      apply Hchid;trivial.
          (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    (** physicalPageNotDerived **)
    apply physicalPageNotDerivedUpdateUserFlag;trivial.
    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by trivial.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.  
    (** isParent  *)
    assert(Hisparent : isParent s) by trivial.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by trivial.
    unfold noDupPartitionTree in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by trivial.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va0 = Some vainparent).
    apply Hwell with partition pg pd0;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by trivial.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh0 s va0 = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg pd0;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    apply getVirtualAddressSh2UpdateUserFlag;trivial.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by trivial.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd0;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by trivial.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd0;trivial.
  (** Propagated properties **)
      assert(Hi2 : StateLib.getIndexOfAddr va fstLevel = lastIndex) by intuition.
      {  intuition trivial. 
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
          unfold getTableAddrRoot.
          destruct H23 as (Hor & Htableroot).
          split;trivial.
          intros.         
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          left.
          clear IHn.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
(*             rewrite Hisancestor in *. *)
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages descParent s)).
            apply isConfigTable with descChild;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
            {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages (currentPartition s) s)).
            apply isConfigTable with descChild;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.

            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
(** partitions are diffrent then config pages are different *)
        + assert(Hi3 : forall idx : index,
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
           unfold getTableAddrRoot.
          destruct H7 as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi4 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.
        
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagSameValue;trivial.
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert (Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
                  assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages descParent s)).
            apply isConfigTable with shadow1;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages (currentPartition s) s)).
            apply isConfigTable with shadow1;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.       
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.

        assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
        unfold isAncestor in *.
        destruct Hisancestor as [Hisancestor | Hisancestor].
        - subst currentPart.
          clear IHn.
(*           rewrite Hisancestor in *. *)
          left.
          unfold consistency in *.
          assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *.
          assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages descParent s)).
          apply isConfigTable with shadow2;trivial.
          intuition. subst;trivial.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2.
        - unfold consistency in *.
          subst.
          clear IHn.
          assert(In (currentPartition s) (getPartitions multiplexer s)).
          unfold currentPartitionInPartitionsList in *.
          intuition.
          assert((currentPartition s) <> ancestor).
          { unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *. 
          assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages (currentPartition s) s)).
          apply isConfigTable with shadow2;trivial.
          intuition.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          left.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages descParent s)).
            apply isConfigTable with list;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages (currentPartition s) s)).
            apply isConfigTable with list;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi4 : nextEntryIsPP currentPart sh1idx tableroot s') by intuition.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.      
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
         
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.

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
      + assert (Hfalse' : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. 
        assert((getConfigPages partition s') = 
             (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        rewrite Hconfig in *.
        assert(Hii : forall partition : page,
            In partition (getPartitions multiplexer s) -> 
            In phyDescChild (getConfigPages partition s) -> False) by trivial.
        assert(Hfalse' : In phyDescChild (getConfigPages partition s)) by trivial.
        apply Hii in Hfalse';trivial. 
      + unfold isPartitionFalse. 
         unfold s'.
         cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
         
(** Internal properties to propagate **)      
      + unfold s'.
        apply isAncestorUpdateUserFlag;trivial. 
      + destruct H.  
        unfold propagatedProperties in *.
        { assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
          apply getPartitionsUpdateUserFlag; trivial.
          rewrite Hpartions; assumption. }
       
      + apply isPEUpdateUserFlag;trivial. 
          assert(Hpe : forall idx : index,
                StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ 
                getTableAddrRoot pt PDidx descParent va s) 
          by trivial.
           apply Hpe;trivial.
      +  assert(Hroot : isPE pt (StateLib.getIndexOfAddr va fstLevel ) s /\
          getTableAddrRoot pt PDidx descParent va s).
          assert(Hpe : forall idx : index,
           StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) 
            by trivial.
          apply Hpe;trivial.
          destruct Hroot as (Hve & Hroot). 
          unfold getTableAddrRoot in *.
          destruct Hroot as (Hor & Hroot).
          split;trivial.
          intros root Hpp.
          unfold s' in Hpp.
          apply nextEntryIsPPUpdateUserFlag' in Hpp.
          apply Hroot in Hpp.
          destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
          exists nbL ; split;trivial.
          exists stop;split;trivial.
          rewrite <- Hind.
          unfold s'.
          apply getIndirectionUpdateUserFlag;trivial. 
       +  apply entryPresentFlagUpdateUserFlag;trivial. 
       + apply entryUserFlagUpdateUserFlagSameValue;trivial.
       +  apply isEntryPageUpdateUserFlag;trivial. 
       +  subst. clear IHn.       
          assert(HisAccess : isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s' =
          isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow ancestor (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt : getVirtualAddressSh2 p
                             {| currentPartition := currentPartition s;
                              memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                              (PE
                                 {|
                                 read := read entry;
                                 write := write entry;
                                 exec := exec entry;
                                 present := present entry;
                                 user := false;
                                 pa := pa entry |}) (memory s) beqPage beqIndex |} vaInAncestor =
                            getVirtualAddressSh2 p s vaInAncestor).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some L = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p vaInAncestor L (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s vaInAncestor );
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent ancestor (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
                          {|
                          currentPartition := currentPartition s;
                          memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                                      (PE
                                         {|
                                         read := read entry;
                                         write := write entry;
                                         exec := exec entry;
                                         present := present entry;
                                         user := false;
                                         pa := pa entry |}) (memory s) beqPage beqIndex |} v = 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In ancestor (getPartitions multiplexer s)).
                apply Hparentpart with descParent;trivial.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions with ancestor p0;trivial.
                unfold consistency in *.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
                        isPE ptvaInAncestor idx s /\ 
                        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                as (Hpe & Hroot);
                trivial.
                apply Hparentpart with ancestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdiff1 : p0 <> ancestor).
                              assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                              apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              assert(Hparentinpart : parentInPartitionList s) by intuition.
              unfold parentInPartitionList in *.
              apply Hparentinpart with ancestor;trivial.
              rewrite nextEntryIsPPgetParent;trivial.
              unfold not;intros Hfalsei;subst.
              now contradict Hdiff1.
              }
              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold partitionDescriptorEntry in *.
              assert(exists entry : page, nextEntryIsPP descParent PDidx entry s /\
                      entry <> defaultPage) as (pdParent & Hpp & Hnotnull).
              apply Hpde;trivial.
              left;trivial.
              clear Hpde.
              apply nextEntryIsPPgetPd in Hpp.
              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
        + assert(Heq : getMappedPage pd s va1 = X) by trivial. 
          revert Heq Hlookup.
          clear.
          intros.
          unfold getMappedPage in *.
          destruct (StateLib.getNbLevel); trivial.
          assert(Hind : getIndirection pd va1 l (nbLevel - 1) s' =
          getIndirection pd va1 l (nbLevel - 1) s) by ( 
          apply getIndirectionUpdateUserFlag; trivial).
          rewrite Hind in *.            
          destruct (getIndirection pd va1 l (nbLevel - 1) s);trivial.
          destruct ( defaultPage =? p);trivial.
          assert(Hread :  StateLib.readPresent p (StateLib.getIndexOfAddr va1 fstLevel) (memory s')=
          StateLib.readPresent p (StateLib.getIndexOfAddr va1 fstLevel) (memory s))
          by (apply readPresentUpdateUserFlag; trivial).
          rewrite Hread in *.
          destruct (StateLib.readPresent p (StateLib.getIndexOfAddr va1 fstLevel) (memory s));
          trivial. destruct b;trivial.
          unfold StateLib.readAccessible in *.
          simpl in *.
 
          rewrite readPhyEntryUpdateUserFlag; trivial.  
        + apply nextEntryIsPPUpdateUserFlag; assumption. 
        + apply isVAUpdateUserFlag; intuition.
          assert( Hisva :  forall idx : index,
                      StateLib.getIndexOfAddr va fstLevel = idx ->
                      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
                      apply Hisva; trivial. 
        + assert ( Hi : forall idx : index,
                  StateLib.getIndexOfAddr va fstLevel = idx ->
                  isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
          generalize (Hi lastIndex Hi2); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split; trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.      
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          unfold getTableAddrRoot.
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply isVA'UpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + assert(Hi :forall idx : index,
              StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
              isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) 
              by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption. 
        + assert(Hi : forall idx : index,
          StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
          isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split;trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.         
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
      (** WriteAccessible property **) 
      + unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. 
      + unfold isEntryPage.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  cbn. reflexivity.
      + unfold entryPresentFlag.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  
        cbn.
        unfold consistency in *.
        assert(Hpres : isPresentNotDefaultIff s ) by intuition.
        symmetry.
        apply phyPageIsPresent with ptvaInAncestor idxva s;trivial. }

(** setAccessible success **)
  simpl. subst. 
  (** recursion **)
  eapply weaken.
  eapply IHn.
  simpl. intros.
  assert(Hancestorpart : In ancestor (getPartitions MALInternal.multiplexer s)).
  { unfold propagatedProperties in *.
    unfold consistency in * .
    assert (Hparent : parentInPartitionList s) by intuition.
    unfold parentInPartitionList in *.
    apply Hparent with descParent; intuition. }
  assert (Hparentchild : In descParent (getChildren ancestor s)).
  unfold propagatedProperties in *.
  unfold consistency in *.
  assert(Hchildren : isChild s) by intuition.
  unfold isChild in *.
      apply Hchildren;trivial.
      intuition.
      apply nextEntryIsPPgetParent;intuition.
  assert(Hvs : verticalSharing s).
   { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. }
    unfold verticalSharing in *.
  assert(Hvsall : incl (getUsedPages descParent s) (getMappedPages ancestor s)).
  apply Hvs;trivial.
  clear Hvs.
  apply verticalSharing2 in Hvsall.
  unfold incl in *.
  generalize(Hvsall phypage);clear Hvsall; intros Hvs.
  assert(Hdescpage : In phypage (getMappedPages descParent s)).
  { intuition.
    subst.
    assert(Hpde : partitionDescriptorEntry s).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. } 
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP descParent PDidx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    left;trivial.
    destruct Hentrypd as (pdParent & Hpp & Hnotnul).
    apply inGetMappedPagesGetTableRoot with va pt pdParent ;trivial.
    
}

apply Hvs in Hdescpage.
clear Hvs.
unfold getMappedPages in *.
assert(HpdAncestor : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
rewrite nextEntryIsPPgetPd in *.
rewrite HpdAncestor in *.
unfold getMappedPagesAux in *.
apply filterOptionInIff in Hdescpage.
unfold getMappedPagesOption in *.
apply in_map_iff in Hdescpage.
destruct Hdescpage as (newVA & Hmapped & Hinvas).
unfold getMappedPage in Hmapped.
assert(Hlevel : Some L = StateLib.getNbLevel) by intuition.
rewrite <- Hlevel in *.
case_eq(getIndirection pdAncestor newVA L (nbLevel - 1) s);[intros ptAncestor HptAncestor |
intros HptAncestor];rewrite HptAncestor in *;try now contradict Hmapped.
case_eq(defaultPage =? ptAncestor);intros Hb;rewrite Hb in *;try now contradict Hmapped.
case_eq(StateLib.readPresent ptAncestor (StateLib.getIndexOfAddr newVA fstLevel) (memory s));
[intros present Hpresent |
intros Hpresent];rewrite Hpresent in *;try now contradict Hmapped.

destruct present;[| inversion Hmapped;subst;
 rewrite isNotDefaultPageFalse in Hnotdef;
 now contradict Hnotdef].
(* assert(vaInAncestor = newVA).
{ destruct H as (((((Ha & Hk )& Hi ) & Hj ) & Hl ) & Hm).
  intuition.
  clear IHn.
  subst.
  apply eqMappedPagesEqVaddrs with phypage pdAncestor s;trivial.
  apply getMappedPageGetTableRoot with ptvaInAncestor ancestor;trivial.
  rewrite nextEntryIsPPgetPd in *;trivial.
  apply AllVAddrAll.
  apply getMappedPageGetIndirection with ancestor ptAncestor L;trivial.
    rewrite nextEntryIsPPgetPd in *;trivial.
  assert (Hnodupmapped : noDupMappedPagesList s).
  unfold consistency in *;intuition.
  unfold noDupMappedPagesList in *.
  assert(Hnewnodup : NoDup (getMappedPages ancestor s)).
  apply Hnodupmapped;trivial.
  unfold getMappedPages in Hnewnodup.
  rewrite HpdAncestor in *.
  unfold getMappedPagesAux  in *.
  assumption. } *)
  instantiate(1:= phypage).
  instantiate (1:= StateLib.getIndexOfAddr vaInAncestor fstLevel).
  instantiate (1:= ptvaInAncestor).
  split.
  intuition.
  split.
  assert(Hisancestor : isAncestor currentPart descParent s) by intuition.
  rewrite nextEntryIsPPgetParent in *.
  unfold propagatedProperties in *.
  unfold consistency in *.  
  apply isAncestorTrans with descParent;intuition.
               unfold consistency in *. intuition.
               
            unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition.    
  intuition.
  intuition.
  subst;trivial.
  subst;trivial.
  subst;trivial. }
(** setAccessible failed **)
 intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition.

Qed.


   Lemma getPdWriteAccessibleRec n descPart phy 

accessibleChild accessibleSh1 accessibleSh2 accessibleList 
descParent (va : vaddr) pt (phypage : page) idxvaparent pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild: 
{{  fun s : state =>
 propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
 pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s /\
 
isAncestor  currentPart descParent s /\
 ( In descParent (getPartitions MALInternal.multiplexer s)  /\
     (defaultPage =? phypage) = false /\
    (forall idx : index,
StateLib.getIndexOfAddr va fstLevel = idx ->
isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) /\
(defaultPage =? pt) = false /\
StateLib.getIndexOfAddr va fstLevel = idxvaparent /\
entryPresentFlag pt idxvaparent true s /\
entryUserFlag pt idxvaparent false s /\
    isEntryPage pt idxvaparent phypage s /\
    isAccessibleMappedPageInParent descParent va phypage s = true )
  /\ StateLib.getPd descPart (memory s) = phy
    }} 
  Internal.writeAccessibleRecAux n va descParent false {{
    fun _ s  => StateLib.getPd descPart (memory s) = phy
     }}.
Proof.
revert va descParent  pt phypage idxvaparent .
induction n.
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
                  destruct Hcurpart as ( Hancestors & (Hcurpart & Hnewprops) & Hnewpost).
                  clear Hancestors. 
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
  2:{
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
  } (** comparePageToNull **) 
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
  destruct H as 
  ((((((((Hprops & Hi ) & Hcurpart)& Hmult) & Hnotmult) & Hsh2root) & HnblL)
           & Hidxaddr) & H).
           
  destruct Hi as (  Hkk & Hnewprops).
 intuition.
  subst.
  apply beq_nat_false in H.
  now contradict H.
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
  intros pdAncestor. (* 
  unfold setAccessible.
  simpl.
  eapply bindRev.
(** setAccessible **)
  unfold setAccessible.
  { *) eapply bindRev.
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
    case_eq (isdefaultVA).
    -  intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition. 
    - intros isdefaultVAT.
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
      assert(Hcons : consistency s) by intuition.
      unfold consistency in *.
      destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent & _ & _).
      unfold parentInPartitionList in *. 
      instantiate (2:= ancestor).
      split.
      apply Hparent with descParent; intuition.
       
      instantiate (1:= PDidx).
      split. intuition.
      exists pdAncestor.
      split. intuition.
      split. 
      unfold consistency in *.
(*       destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent).  *)
      unfold partitionDescriptorEntry in Hpd.
      unfold parentInPartitionList in *.
      subst.
      assert(Hpartancestor : In ancestor (getPartitions MALInternal.multiplexer s)).
      {       apply Hparent with descParent; intuition. } 
      generalize (Hpd ancestor Hpartancestor); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/PDidx = sh3idx
              \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
            by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hancesnotnull).
      subst.
      assert (Hrootances : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup ancestor i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootances |
        now contradict Hrootances | 
       subst ; assumption| now contradict Hrootances| now contradict Hrootances ]  
       |now contradict Hrootances] | now contradict Hrootances].
      subst. left. split;intuition.
      intro ptvaInAncestor. simpl.
       (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2:{
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
      do  16 (* 6 *) rewrite <- and_assoc in H0.
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
  } (** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptvaInAncestorIsnull. simpl.
      case_eq ptvaInAncestorIsnull.
      2:{
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
      simpl.
      eapply bindRev; simpl;[|intros []].
      (** writeAccessible **)
      eapply WP.weaken.
      eapply WP.writeAccessible.
      intros. simpl.
      assert (exists entry0 : Pentry,
        lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry0)) as Hlookup.
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
      do 9 rewrite <- and_assoc in H.
      destruct H as (Hsplit & Hfalse & Hrest).
      assert(Heqphy : phypage = pa entry).
      {    destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (Hnew & Hll & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
         intuition. subst.
        unfold isAccessibleMappedPageInParent in *.
        assert (HgetVirt : getVirtualAddressSh2 sh2 s va  = Some vaInAncestor).
        apply isVaInParent with descParent ptsh2;trivial.
        apply nextEntryIsPPgetSndShadow in Hppsh2.
        rewrite Hppsh2 in *.
        rewrite HgetVirt in *.
        rewrite nextEntryIsPPgetParent in * .
        rewrite Hppparent in *. 
        apply nextEntryIsPPgetPd in Hpppd .
        rewrite Hpppd in *.
        case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor);
        intros * Hacce;
        rewrite Hacce in *;try now contradict Hfalse.
        unfold getAccessibleMappedPage in Hacce.
        assert( isPE ptvaInAncestor  (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) as (Hve & Hroot ).
        apply Hgetroot2;trivial.
        unfold getTableAddrRoot in *.
        destruct Hroot as (_ & Hroot).
        rewrite <- nextEntryIsPPgetPd in *.
        apply Hroot in  Hpppd.
        clear Hroot.
        destruct Hpppd as (nbL & HnbL & stop & Hstop & Hind).
        subst.
        rewrite <- HnbL in *.
        assert(Hgetind : getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s  
        = Some ptvaInAncestor).
        apply getIndirectionStopLevelGT2 with (nbL+1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind in *.
        rewrite H in *.
        destruct ( StateLib.readPresent ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s));try now contradict Hacce.
        destruct b;try now contradict Hacce.
        destruct ( StateLib.readAccessible ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s)); try now contradict Hacce.
        destruct b; try now contradict Hacce.
        unfold StateLib.readPhyEntry in *. 
        rewrite Hlookup in *.
        apply beq_nat_true in Hfalse.
        inversion Hacce.
        subst.
        destruct phypage; destruct (pa entry).
        simpl in *.
        subst.
        f_equal; apply proof_irrelevance. }
      assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true).
      { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        rewrite Heqphy.
        destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
        apply isAccessibleMappedPageInParentTrue with descParent va phypage ptvaInAncestor ptsh2 pdAncestor;
        subst;intuition.
        subst;assumption. }
      repeat rewrite and_assoc in Hsplit.
      destruct Hsplit as (Hprops & Hsplit).
(*       unfold propagatedProperties in *.
      do 73 rewrite <- and_assoc in Hprops.
      destruct Hprops as (Hprops & xx & Hprops2). 
            repeat rewrite and_assoc in Hprops. *)
      assert (Hnewprops := conj  Hprops  Hsplit).
      assert (H := conj (conj Hnewprops Htrue) Hrest).
      simpl.
      clear Hnewprops.
    (*   repeat rewrite and_assoc in H. *)
      pattern s in H.
      match type of H with 
      | ?HT s => instantiate (1 := fun tt s => HT s  /\ 
                  entryUserFlag ptvaInAncestor idxva false s /\
                  isEntryPage ptvaInAncestor idxva phypage s /\
                  entryPresentFlag ptvaInAncestor idxva true s  ) 
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
      simpl.
      unfold propagatedProperties in *. 
      do 7 rewrite and_assoc.
      clear Hrest  Hsplit  Hprops.
      split.
      
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
      split.
      (** partitionDescriptorEntry **)
      apply partitionDescriptorEntryUpdateUserFlag;trivial.
      intuition.
      (** dataStructurePdSh1Sh2asRoot **)
      destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
      Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      (** currentPartitionInPartitionsList **)
      split.
      unfold currentPartitionInPartitionsList in *.
      simpl in *. subst. 
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite Hpartions. assumption.
      (** noDupMappedPagesList **)  
      split.    
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
      split.
      (** noDupConfigPagesList **)
      apply getIndirectionsNoDupUpdateUserFlag; trivial.
      split.
      (** parentInPartitionList **)
      unfold parentInPartitionList in *.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart.
      intros partition HgetParts parent Hroot.
      generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
      apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
      apply Hparent; trivial.
      split.
      (** accessibleVAIsNotPartitionDescriptor **)
     unfold s'.
      subst.
      clear IHn.
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (_ & Hi).
      intuition.
      subst.
      apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag  with level ancestor   
        pdAncestor;trivial.
      assert(Hparentpart : parentInPartitionList s) by trivial.
      unfold parentInPartitionList in *.
      apply Hparent with descParent;trivial. 
       assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
      assert(  isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s ) as (_ & Hroot).
      apply Hget;split;trivial.
      assumption.
      apply nextEntryIsPPgetPd;trivial.
      subst.
      assert(HaccessInParent : isAccessibleMappedPageInParent descParent va (pa entry) s = true)
       by trivial.
       unfold isAccessibleMappedPageInParent in HaccessInParent.
       (** Here we use the property already present into the precondition : 
            *)
       assert(Hcursh2 : nextEntryIsPP descParent sh2idx sh2 s ) by trivial.
      apply nextEntryIsPPgetSndShadow in Hcursh2.
      rewrite Hcursh2 in HaccessInParent.
      assert(Hvainparent : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
      { assert(Hxx : forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx ->
        isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
        assert(Hgetva : isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\ 
        getTableAddrRoot ptsh2 sh2idx descParent va s).
        apply Hxx;trivial. clear Hxx.
        destruct Hgetva as (Hva & Hgetva).
        assert(Hisva : isVA' ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s) 
        by trivial.
        unfold getVirtualAddressSh2.
        unfold getTableAddrRoot in Hgetva.
        destruct Hgetva as (_ & Hgetva).
        assert(HcurSh2 : nextEntryIsPP descParent sh2idx sh2 s).
        rewrite  nextEntryIsPPgetSndShadow ;trivial.
        apply Hgetva in HcurSh2.
        destruct HcurSh2 as (nbL & HnbL & stop & Hstop & Hind).
        rewrite <- HnbL.
        subst.
        assert(Hgetind : getIndirection sh2 va nbL (nbLevel - 1) s = Some ptsh2).
        apply getIndirectionStopLevelGT2 with (nbL + 1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind.
        assert (Hptnotnull : (defaultPage =? ptsh2) = false) by trivial.
        rewrite Hptnotnull.
        unfold  isVA' in *. 
        unfold StateLib.readVirtual.
        destruct(lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ); 
        try now contradict Hisva.
        destruct v;try now contradict Hisva.
        subst. trivial. }
      rewrite Hvainparent in *.
      assert(Hgetparent : StateLib.getParent descParent (memory s) = Some ancestor).
      { apply nextEntryIsPPgetParent;trivial. }
      rewrite Hgetparent in *.
      assert(Hgetpdparent : StateLib.getPd ancestor (memory s) = Some pdAncestor).
      { apply nextEntryIsPPgetPd;trivial. }
      rewrite Hgetpdparent in *.
      case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor ); intros * Hi .
      rewrite Hi in *.
      unfold getAccessibleMappedPage in Hi.
      case_eq (StateLib.getNbLevel);intros * Hi2 ; rewrite Hi2 in *;
       try now contradict Hi.
      assert(Hancestor : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by 
      trivial.
      assert(Hget : isPE ptvaInAncestor ( StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\
            getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s).
      apply Hancestor; clear Hancestor;
      trivial.
      destruct Hget as (Hva & Hget).
      unfold getTableAddrRoot in Hget.
      destruct Hget as (_ & Hget).
      apply nextEntryIsPPgetPd in Hgetpdparent.
      apply Hget in Hgetpdparent.
      destruct Hgetpdparent as (nbL & HnbL & stop & Hstop & Hgettable).
      clear Hget.
      rewrite <- HnbL in *.
      inversion Hi2.
      subst.
      assert(Hind :getIndirection pdAncestor vaInAncestor l (nbLevel - 1) s = Some ptvaInAncestor).
      apply getIndirectionStopLevelGT2 with (l+1);trivial.
      omega.
      apply getNbLevelEq in HnbL.
      rewrite HnbL.
      unfold CLevel.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      simpl;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      rewrite Hind in *.
      assert (Hnotnull : (defaultPage =? ptvaInAncestor) = false) by trivial.
      rewrite Hnotnull in *.
      destruct (StateLib.readPresent ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b; try now contradict Hi.
      destruct(StateLib.readAccessible ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b.
      unfold StateLib.readPhyEntry in *.
      rewrite Hlookup in *.
      symmetry; assumption.
      now contradict Hi.
      rewrite Hi in *. 
      now contradict HaccessInParent.
            rewrite Hi in *. 
      now contradict HaccessInParent.
   (* accessibleChildPageIsAccessibleIntoParent *)
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (Hancestor & Hi).
      unfold s'.
      intuition. 
      subst.
      clear IHn.
      apply accessibleChildPageIsAccessibleIntoParentUpdateUserFlagFlase
      with level ancestor pdAncestor va ptsh2 descParent pt;trivial.
      assert(Hparentpart : parentInPartitionList s).
      unfold consistency in *; intuition.
      unfold parentInPartitionList in *.
      apply Hparentpart with descParent;trivial.
      (* noCycleInPartitionTree *)
      assert(Hdiff : noCycleInPartitionTree s) by trivial.
      unfold noCycleInPartitionTree in *.
      intros parent partition Hparts Hparentpart.
      simpl in *.
      assert (getPartitions multiplexer {|
              currentPartition := currentPartition s;
              memory := add ptvaInAncestor idxva
                          (PE
                             {|
                             read := read entry;
                             write := write entry;
                             exec := exec entry;
                             present := present entry;
                             user := false;
                             pa := pa entry |}) (memory s) beqPage beqIndex |}
               = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(HgetParent : getAncestors partition
                {|
                   currentPartition := currentPartition s;
                   memory := add ptvaInAncestor idxva
                               (PE
                                  {|
                                  read := read entry;
                                  write := write entry;
                                  exec := exec entry;
                                  present := present entry;
                                  user := false;
                                  pa := pa entry |}) (memory s) beqPage beqIndex |} = 
                      getAncestors partition  s).
      apply getAncestorsUpdateUserFlag;trivial.
      rewrite HgetParent in *; clear HgetParent.
      apply Hdiff;trivial.
      (* configTablesAreDifferent *)
      assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
      unfold configTablesAreDifferent in *.
      simpl in *.
      fold s'.
      intros partition1 partition2 Hpart1 Hpart2 Hdiff.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      apply Hconfigdiff;trivial.
      rename H into Hcond.
      (** isChild **)
      assert(Hchid : isChild s) by intuition.
      unfold isChild in *.
      simpl in *.
      intros partition parent Hparts Hgetparent.
      rewrite getPartitionsUpdateUserFlag in *;trivial.
      rewrite getParentUpdateUserFlag in *;trivial.
      rewrite getChildrenUpdateFlagUser;trivial.
      apply Hchid;trivial.
          (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    (** physicalPageNotDerived **)
    apply physicalPageNotDerivedUpdateUserFlag;trivial.
    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by trivial.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.  
    (** isParent  *)
    assert(Hisparent : isParent s) by trivial.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by trivial.
    unfold noDupPartitionTree in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by trivial.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va0 = Some vainparent).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by trivial.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh0 s va0 = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    apply getVirtualAddressSh2UpdateUserFlag;trivial.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by trivial.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by trivial.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.
  (** Propagated properties **)
      assert(Hi2 : StateLib.getIndexOfAddr va fstLevel = lastIndex) by intuition.
      {  intuition trivial. 
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
          unfold getTableAddrRoot.
          destruct H23 as (Hor & Htableroot).
          split;trivial.
          intros.         
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          left.
          clear IHn.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
(*             rewrite Hisancestor in *. *)
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages descParent s)).
            apply isConfigTable with descChild;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
            {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages (currentPartition s) s)).
            apply isConfigTable with descChild;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.

            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
(** partitions are diffrent then config pages are different *)
        + assert(Hi3 : forall idx : index,
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
           unfold getTableAddrRoot.
          destruct H7 as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi4 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.
        
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagSameValue;trivial.
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert (Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
                  assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages descParent s)).
            apply isConfigTable with shadow1;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages (currentPartition s) s)).
            apply isConfigTable with shadow1;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.       
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.

        assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
        unfold isAncestor in *.
        destruct Hisancestor as [Hisancestor | Hisancestor].
        - subst currentPart.
          clear IHn.
(*           rewrite Hisancestor in *. *)
          left.
          unfold consistency in *.
          assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *.
          assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages descParent s)).
          apply isConfigTable with shadow2;trivial.
          intuition. subst;trivial.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2.
        - unfold consistency in *.
          subst.
          clear IHn.
          assert(In (currentPartition s) (getPartitions multiplexer s)).
          unfold currentPartitionInPartitionsList in *.
          intuition.
          assert((currentPartition s) <> ancestor).
          { unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *. 
          assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages (currentPartition s) s)).
          apply isConfigTable with shadow2;trivial.
          intuition.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          left.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages descParent s)).
            apply isConfigTable with list;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages (currentPartition s) s)).
            apply isConfigTable with list;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi4 : nextEntryIsPP currentPart sh1idx tableroot s') by intuition.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.      
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
         
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.

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
      + assert (Hfalse' : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. 
        assert((getConfigPages partition s') = 
             (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        rewrite Hconfig in *.
        assert(Hii : forall partition : page,
            In partition (getPartitions multiplexer s) -> 
            In phyDescChild (getConfigPages partition s) -> False) by trivial.
        assert(Hfalse' : In phyDescChild (getConfigPages partition s)) by trivial.
        apply Hii in Hfalse';trivial. 
      + unfold isPartitionFalse. 
         unfold s'.
         cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
         
(** Internal properties to propagate **)      
      + unfold s'.
        apply isAncestorUpdateUserFlag;trivial. 
      + destruct H.  
        unfold propagatedProperties in *.
        { assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
          apply getPartitionsUpdateUserFlag; trivial.
          rewrite Hpartions; assumption. }
       
      + apply isPEUpdateUserFlag;trivial. 
          assert(Hpe : forall idx : index,
                StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ 
                getTableAddrRoot pt PDidx descParent va s) 
          by trivial.
           apply Hpe;trivial.
      +  assert(Hroot : isPE pt (StateLib.getIndexOfAddr va fstLevel ) s /\
          getTableAddrRoot pt PDidx descParent va s).
          assert(Hpe : forall idx : index,
           StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) 
            by trivial.
          apply Hpe;trivial.
          destruct Hroot as (Hve & Hroot). 
          unfold getTableAddrRoot in *.
          destruct Hroot as (Hor & Hroot).
          split;trivial.
          intros root Hpp.
          unfold s' in Hpp.
          apply nextEntryIsPPUpdateUserFlag' in Hpp.
          apply Hroot in Hpp.
          destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
          exists nbL ; split;trivial.
          exists stop;split;trivial.
          rewrite <- Hind.
          unfold s'.
          apply getIndirectionUpdateUserFlag;trivial. 
       +  apply entryPresentFlagUpdateUserFlag;trivial. 
       + apply entryUserFlagUpdateUserFlagSameValue;trivial.
       +  apply isEntryPageUpdateUserFlag;trivial. 
       +  subst. clear IHn.       
          assert(HisAccess : isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s' =
          isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow ancestor (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt : getVirtualAddressSh2 p
                             {| currentPartition := currentPartition s;
                              memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                              (PE
                                 {|
                                 read := read entry;
                                 write := write entry;
                                 exec := exec entry;
                                 present := present entry;
                                 user := false;
                                 pa := pa entry |}) (memory s) beqPage beqIndex |} vaInAncestor =
                            getVirtualAddressSh2 p s vaInAncestor).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some L = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p vaInAncestor L (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s vaInAncestor );
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent ancestor (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
                          {|
                          currentPartition := currentPartition s;
                          memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                                      (PE
                                         {|
                                         read := read entry;
                                         write := write entry;
                                         exec := exec entry;
                                         present := present entry;
                                         user := false;
                                         pa := pa entry |}) (memory s) beqPage beqIndex |} v = 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In ancestor (getPartitions multiplexer s)).
                apply Hparentpart with descParent;trivial.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions with ancestor p0;trivial.
                unfold consistency in *.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
                        isPE ptvaInAncestor idx s /\ 
                        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                as (Hpe & Hroot);
                trivial.
                apply Hparentpart with ancestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdiff1 : p0 <> ancestor).
                              assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                              apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              assert(Hparentinpart : parentInPartitionList s) by intuition.
              unfold parentInPartitionList in *.
              apply Hparentinpart with ancestor;trivial.
              rewrite nextEntryIsPPgetParent;trivial.
              unfold not;intros Hfalsei;subst.
              now contradict Hdiff1.
              }
              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold partitionDescriptorEntry in *.
              assert(exists entry : page, nextEntryIsPP descParent PDidx entry s /\
                      entry <> defaultPage) as (pdParent & Hpp & Hnotnull).
              apply Hpde;trivial.
              left;trivial.
              clear Hpde.
              apply nextEntryIsPPgetPd in Hpp.
              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
        + assert(Heq : StateLib.getPd descPart
                      (add ptvaInAncestor idxva
                         (PE
                            {|
                            read := read entry;
                            write := write entry;
                            exec := exec entry;
                            present := present entry;
                            user := false;
                            pa := pa entry |}) (memory s) beqPage beqIndex) = 
                     StateLib.getPd descPart
                      (memory s)). apply getPdUpdateUserFlag; trivial.
                      rewrite Heq in *;trivial. 
        + apply nextEntryIsPPUpdateUserFlag; assumption. 
        + apply isVAUpdateUserFlag; intuition.
          assert( Hisva :  forall idx : index,
                      StateLib.getIndexOfAddr va fstLevel = idx ->
                      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
                      apply Hisva; trivial. 
        + assert ( Hi : forall idx : index,
                  StateLib.getIndexOfAddr va fstLevel = idx ->
                  isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
          generalize (Hi lastIndex Hi2); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split; trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.      
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          unfold getTableAddrRoot.
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply isVA'UpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + assert(Hi :forall idx : index,
              StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
              isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) 
              by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption. 
        + assert(Hi : forall idx : index,
          StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
          isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split;trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.         
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
      (** WriteAccessible property **) 
      + unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. 
      + unfold isEntryPage.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  cbn. reflexivity.
      + unfold entryPresentFlag.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  
        cbn.
        unfold consistency in *.
        assert(Hpres : isPresentNotDefaultIff s ) by intuition.
        symmetry.
        apply phyPageIsPresent with ptvaInAncestor idxva s;trivial. }

(** setAccessible success **)
  simpl. subst. 
  (** recursion **)
  eapply weaken.
  eapply IHn.
  simpl. intros.
  assert(Hancestorpart : In ancestor (getPartitions MALInternal.multiplexer s)).
  { unfold propagatedProperties in *.
    unfold consistency in * .
    assert (Hparent : parentInPartitionList s) by intuition.
    unfold parentInPartitionList in *.
    apply Hparent with descParent; intuition. }
  assert (Hparentchild : In descParent (getChildren ancestor s)).
  unfold propagatedProperties in *.
  unfold consistency in *.
  assert(Hchildren : isChild s) by intuition.
  unfold isChild in *.
      apply Hchildren;trivial.
      intuition.
      apply nextEntryIsPPgetParent;intuition.
  assert(Hvs : verticalSharing s).
   { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. }
    unfold verticalSharing in *.
  assert(Hvsall : incl (getUsedPages descParent s) (getMappedPages ancestor s)).
  apply Hvs;trivial.
  clear Hvs.
  apply verticalSharing2 in Hvsall.
  unfold incl in *.
  generalize(Hvsall phypage);clear Hvsall; intros Hvs.
  assert(Hdescpage : In phypage (getMappedPages descParent s)).
  { intuition.
    subst.
    assert(Hpde : partitionDescriptorEntry s).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. } 
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP descParent PDidx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    left;trivial.
    destruct Hentrypd as (pdParent & Hpp & Hnotnul).
    apply inGetMappedPagesGetTableRoot with va pt pdParent ;trivial.

}

apply Hvs in Hdescpage.
clear Hvs.
unfold getMappedPages in *.
assert(HpdAncestor : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
rewrite nextEntryIsPPgetPd in *.
rewrite HpdAncestor in *.
unfold getMappedPagesAux in *.

apply filterOptionInIff in Hdescpage.
unfold getMappedPagesOption in *.
apply in_map_iff in Hdescpage.
destruct Hdescpage as (newVA & Hmapped & Hinvas).
unfold getMappedPage in Hmapped.
assert(Hlevel : Some L = StateLib.getNbLevel) by intuition.
rewrite <- Hlevel in *.
case_eq(getIndirection pdAncestor newVA L (nbLevel - 1) s);[intros ptAncestor HptAncestor |
intros HptAncestor];rewrite HptAncestor in *;try now contradict Hmapped.
case_eq(defaultPage =? ptAncestor);intros Hb;rewrite Hb in *;try now contradict Hmapped.
case_eq(StateLib.readPresent ptAncestor (StateLib.getIndexOfAddr newVA fstLevel) (memory s));
[intros present Hpresent |
intros Hpresent];rewrite Hpresent in *;try now contradict Hmapped.

destruct present;[| inversion Hmapped;subst;
 rewrite isNotDefaultPageFalse in Hnotdef;
 now contradict Hnotdef].
(* assert(vaInAncestor = newVA).
{ destruct H as (((((Ha & Hk )& Hi ) & Hj ) & Hl ) & Hm).
  intuition.
  clear IHn.
  subst.
  apply eqMappedPagesEqVaddrs with phypage pdAncestor s;trivial.
  apply getMappedPageGetTableRoot with ptvaInAncestor ancestor;trivial.
  rewrite nextEntryIsPPgetPd in *;trivial.
  apply AllVAddrAll.
  apply getMappedPageGetIndirection with ancestor ptAncestor L;trivial.
    rewrite nextEntryIsPPgetPd in *;trivial.
  assert (Hnodupmapped : noDupMappedPagesList s).
  unfold consistency in *;intuition.
  unfold noDupMappedPagesList in *.
  assert(Hnewnodup : NoDup (getMappedPages ancestor s)).
  apply Hnodupmapped;trivial.
  unfold getMappedPages in Hnewnodup.
  rewrite HpdAncestor in *.
  unfold getMappedPagesAux  in *.
  assumption. } *)
instantiate(1:= phypage).
instantiate (1:= StateLib.getIndexOfAddr vaInAncestor fstLevel).
instantiate (1:= ptvaInAncestor).

  split.
 intuition.
 split.
 assert(Hisancestor : isAncestor currentPart descParent s) by intuition.
 rewrite nextEntryIsPPgetParent in *.
unfold propagatedProperties in *. 
unfold consistency in *. 
apply isAncestorTrans with descParent;intuition.
             unfold consistency in *. intuition.
            unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition.    
intuition.
 intuition.
 subst;trivial.
   subst;trivial.
  subst;trivial. }
 

(** setAccessible failed **)
 intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition.
Qed.




Lemma noDupMappedPagesListWriteAccessibleRec n 

accessibleChild accessibleSh1 accessibleSh2 accessibleList 
descParent (va : vaddr) pt (phypage : page) idxvaparent pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild: 
{{  fun s : state =>
 propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
 pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s /\
 
isAncestor  currentPart descParent s /\
 ( In descParent (getPartitions MALInternal.multiplexer s)  /\
     (defaultPage =? phypage) = false /\
    (forall idx : index,
StateLib.getIndexOfAddr va fstLevel = idx ->
isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) /\
(defaultPage =? pt) = false /\
StateLib.getIndexOfAddr va fstLevel = idxvaparent /\
entryPresentFlag pt idxvaparent true s /\
entryUserFlag pt idxvaparent false s /\
    isEntryPage pt idxvaparent phypage s /\
    isAccessibleMappedPageInParent descParent va phypage s = true )
  /\ noDupMappedPagesList s
    }} 
  Internal.writeAccessibleRecAux n va descParent false {{
    fun _ s  => noDupMappedPagesList s
     }}.
Proof.
revert va descParent  pt phypage idxvaparent .
induction n.
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
                  destruct Hcurpart as ( Hancestors & (Hcurpart & Hnewprops) & Hnewpost).
                  clear Hancestors. 
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
  2:{
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
  } (** comparePageToNull **) 
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
  destruct H as 
  ((((((((Hprops & Hi ) & Hcurpart)& Hmult) & Hnotmult) & Hsh2root) & HnblL)
           & Hidxaddr) & H).
           
  destruct Hi as (  Hkk & Hnewprops).
 intuition.
  subst.
  apply beq_nat_false in H.
  now contradict H.
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
  intros pdAncestor. (* 
  unfold setAccessible.
  simpl.
  eapply bindRev.
(** setAccessible **)
  unfold setAccessible.
  { *) eapply bindRev.
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
    case_eq (isdefaultVA).
    -  intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition. 
    - intros isdefaultVAT.
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
      assert(Hcons : consistency s) by intuition.
      unfold consistency in *.
      destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent & _ & _).
      unfold parentInPartitionList in *. 
      instantiate (2:= ancestor).
      split.
      apply Hparent with descParent; intuition.
       
      instantiate (1:= PDidx).
      split. intuition.
      exists pdAncestor.
      split. intuition.
      split. 
      unfold consistency in *.
(*       destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent).  *)
      unfold partitionDescriptorEntry in Hpd.
      unfold parentInPartitionList in *.
      subst.
      assert(Hpartancestor : In ancestor (getPartitions MALInternal.multiplexer s)).
      {       apply Hparent with descParent; intuition. } 
      generalize (Hpd ancestor Hpartancestor); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/PDidx = sh3idx
              \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
            by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hancesnotnull).
      subst.
      assert (Hrootances : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup ancestor i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootances |
        now contradict Hrootances | 
       subst ; assumption| now contradict Hrootances| now contradict Hrootances ]  
       |now contradict Hrootances] | now contradict Hrootances].
      subst. left. split;intuition.
      intro ptvaInAncestor. simpl.
       (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2:{
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
      do  16 (* 6 *) rewrite <- and_assoc in H0.
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
  } (** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptvaInAncestorIsnull. simpl.
      case_eq ptvaInAncestorIsnull.
      2:{
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
      simpl.
      eapply bindRev; simpl;[|intros []].
      (** writeAccessible **)
      eapply WP.weaken.
      eapply WP.writeAccessible.
      intros. simpl.
      assert (exists entry0 : Pentry,
        lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry0)) as Hlookup.
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
      do 9 rewrite <- and_assoc in H.
      destruct H as (Hsplit & Hfalse & Hrest).
      assert(Heqphy : phypage = pa entry).
      {    destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (Hnew & Hll & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
         intuition. subst.
        unfold isAccessibleMappedPageInParent in *.
        assert (HgetVirt : getVirtualAddressSh2 sh2 s va  = Some vaInAncestor).
        apply isVaInParent with descParent ptsh2;trivial.
        apply nextEntryIsPPgetSndShadow in Hppsh2.
        rewrite Hppsh2 in *.
        rewrite HgetVirt in *.
        rewrite nextEntryIsPPgetParent in * .
        rewrite Hppparent in *. 
        apply nextEntryIsPPgetPd in Hpppd .
        rewrite Hpppd in *.
        case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor);
        intros * Hacce;
        rewrite Hacce in *;try now contradict Hfalse.
        unfold getAccessibleMappedPage in Hacce.
        assert( isPE ptvaInAncestor  (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) as (Hve & Hroot ).
        apply Hgetroot2;trivial.
        unfold getTableAddrRoot in *.
        destruct Hroot as (_ & Hroot).
        rewrite <- nextEntryIsPPgetPd in *.
        apply Hroot in  Hpppd.
        clear Hroot.
        destruct Hpppd as (nbL & HnbL & stop & Hstop & Hind).
        subst.
        rewrite <- HnbL in *.
        assert(Hgetind : getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s  
        = Some ptvaInAncestor).
        apply getIndirectionStopLevelGT2 with (nbL+1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind in *.
        rewrite H in *.
        destruct ( StateLib.readPresent ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s));try now contradict Hacce.
        destruct b;try now contradict Hacce.
        destruct ( StateLib.readAccessible ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s)); try now contradict Hacce.
        destruct b; try now contradict Hacce.
        unfold StateLib.readPhyEntry in *. 
        rewrite Hlookup in *.
        apply beq_nat_true in Hfalse.
        inversion Hacce.
        subst.
        destruct phypage; destruct (pa entry).
        simpl in *.
        subst.
        f_equal; apply proof_irrelevance. }
      assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true).
      { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        rewrite Heqphy.
        destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
        apply isAccessibleMappedPageInParentTrue with descParent va phypage ptvaInAncestor ptsh2 pdAncestor;
        subst;intuition.
        subst;assumption. }
      repeat rewrite and_assoc in Hsplit.
      destruct Hsplit as (Hprops & Hsplit).
(*       unfold propagatedProperties in *.
      do 73 rewrite <- and_assoc in Hprops.
      destruct Hprops as (Hprops & xx & Hprops2). 
            repeat rewrite and_assoc in Hprops. *)
      assert (Hnewprops := conj  Hprops  Hsplit).
      assert (H := conj (conj Hnewprops Htrue) Hrest).
      simpl.
      clear Hnewprops.
    (*   repeat rewrite and_assoc in H. *)
      pattern s in H.
      match type of H with 
      | ?HT s => instantiate (1 := fun tt s => HT s  /\ 
                  entryUserFlag ptvaInAncestor idxva false s /\
                  isEntryPage ptvaInAncestor idxva phypage s /\
                  entryPresentFlag ptvaInAncestor idxva true s  ) 
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
      simpl.
      unfold propagatedProperties in *. 
      do 7 rewrite and_assoc.
      clear Hrest  Hsplit  Hprops.
      split.
      
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
      split.
      (** partitionDescriptorEntry **)
      apply partitionDescriptorEntryUpdateUserFlag;trivial.
      intuition.
      (** dataStructurePdSh1Sh2asRoot **)
      destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
      Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      (** currentPartitionInPartitionsList **)
      split.
      unfold currentPartitionInPartitionsList in *.
      simpl in *. subst. 
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite Hpartions. assumption.
      (** noDupMappedPagesList **)  
      split.    
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
      split.
      (** noDupConfigPagesList **)
      apply getIndirectionsNoDupUpdateUserFlag; trivial.
      split.
      (** parentInPartitionList **)
      unfold parentInPartitionList in *.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart.
      intros partition HgetParts parent Hroot.
      generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
      apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
      apply Hparent; trivial.
      split.
      (** accessibleVAIsNotPartitionDescriptor **)
     unfold s'.
      subst.
      clear IHn.
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (_ & Hi).
      intuition.
      subst.
      apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag  with level ancestor   
        pdAncestor;trivial.
      assert(Hparentpart : parentInPartitionList s) by trivial.
      unfold parentInPartitionList in *.
      apply Hparent with descParent;trivial. 
       assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
      assert(  isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s ) as (_ & Hroot).
      apply Hget;split;trivial.
      assumption.
      apply nextEntryIsPPgetPd;trivial.
      subst.
      assert(HaccessInParent : isAccessibleMappedPageInParent descParent va (pa entry) s = true)
       by trivial.
       unfold isAccessibleMappedPageInParent in HaccessInParent.
       (** Here we use the property already present into the precondition : 
            *)
       assert(Hcursh2 : nextEntryIsPP descParent sh2idx sh2 s ) by trivial.
      apply nextEntryIsPPgetSndShadow in Hcursh2.
      rewrite Hcursh2 in HaccessInParent.
      assert(Hvainparent : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
      { assert(Hxx : forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx ->
        isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
        assert(Hgetva : isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\ 
        getTableAddrRoot ptsh2 sh2idx descParent va s).
        apply Hxx;trivial. clear Hxx.
        destruct Hgetva as (Hva & Hgetva).
        assert(Hisva : isVA' ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s) 
        by trivial.
        unfold getVirtualAddressSh2.
        unfold getTableAddrRoot in Hgetva.
        destruct Hgetva as (_ & Hgetva).
        assert(HcurSh2 : nextEntryIsPP descParent sh2idx sh2 s).
        rewrite  nextEntryIsPPgetSndShadow ;trivial.
        apply Hgetva in HcurSh2.
        destruct HcurSh2 as (nbL & HnbL & stop & Hstop & Hind).
        rewrite <- HnbL.
        subst.
        assert(Hgetind : getIndirection sh2 va nbL (nbLevel - 1) s = Some ptsh2).
        apply getIndirectionStopLevelGT2 with (nbL + 1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind.
        assert (Hptnotnull : (defaultPage =? ptsh2) = false) by trivial.
        rewrite Hptnotnull.
        unfold  isVA' in *. 
        unfold StateLib.readVirtual.
        destruct(lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ); 
        try now contradict Hisva.
        destruct v;try now contradict Hisva.
        subst. trivial. }
      rewrite Hvainparent in *.
      assert(Hgetparent : StateLib.getParent descParent (memory s) = Some ancestor).
      { apply nextEntryIsPPgetParent;trivial. }
      rewrite Hgetparent in *.
      assert(Hgetpdparent : StateLib.getPd ancestor (memory s) = Some pdAncestor).
      { apply nextEntryIsPPgetPd;trivial. }
      rewrite Hgetpdparent in *.
      case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor ); intros * Hi .
      rewrite Hi in *.
      unfold getAccessibleMappedPage in Hi.
      case_eq (StateLib.getNbLevel);intros * Hi2 ; rewrite Hi2 in *;
       try now contradict Hi.
      assert(Hancestor : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by 
      trivial.
      assert(Hget : isPE ptvaInAncestor ( StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\
            getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s).
      apply Hancestor; clear Hancestor;
      trivial.
      destruct Hget as (Hva & Hget).
      unfold getTableAddrRoot in Hget.
      destruct Hget as (_ & Hget).
      apply nextEntryIsPPgetPd in Hgetpdparent.
      apply Hget in Hgetpdparent.
      destruct Hgetpdparent as (nbL & HnbL & stop & Hstop & Hgettable).
      clear Hget.
      rewrite <- HnbL in *.
      inversion Hi2.
      subst.
      assert(Hind :getIndirection pdAncestor vaInAncestor l (nbLevel - 1) s = Some ptvaInAncestor).
      apply getIndirectionStopLevelGT2 with (l+1);trivial.
      omega.
      apply getNbLevelEq in HnbL.
      rewrite HnbL.
      unfold CLevel.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      simpl;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      rewrite Hind in *.
      assert (Hnotnull : (defaultPage =? ptvaInAncestor) = false) by trivial.
      rewrite Hnotnull in *.
      destruct (StateLib.readPresent ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b; try now contradict Hi.
      destruct(StateLib.readAccessible ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b.
      unfold StateLib.readPhyEntry in *.
      rewrite Hlookup in *.
      symmetry; assumption.
      now contradict Hi.
      rewrite Hi in *. 
      now contradict HaccessInParent.
            rewrite Hi in *. 
      now contradict HaccessInParent.
   (* accessibleChildPageIsAccessibleIntoParent *)
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (Hancestor & Hi).
      unfold s'.
      intuition. 
      subst.
      clear IHn.
      apply accessibleChildPageIsAccessibleIntoParentUpdateUserFlagFlase
      with level ancestor pdAncestor va ptsh2 descParent pt;trivial.
      assert(Hparentpart : parentInPartitionList s).
      unfold consistency in *; intuition.
      unfold parentInPartitionList in *.
      apply Hparentpart with descParent;trivial.
      (* noCycleInPartitionTree *)
      assert(Hdiff : noCycleInPartitionTree s) by trivial.
      unfold noCycleInPartitionTree in *.
      intros parent partition Hparts Hparentpart.
      simpl in *.
      assert (getPartitions multiplexer {|
              currentPartition := currentPartition s;
              memory := add ptvaInAncestor idxva
                          (PE
                             {|
                             read := read entry;
                             write := write entry;
                             exec := exec entry;
                             present := present entry;
                             user := false;
                             pa := pa entry |}) (memory s) beqPage beqIndex |}
               = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(HgetParent : getAncestors partition
                {|
                   currentPartition := currentPartition s;
                   memory := add ptvaInAncestor idxva
                               (PE
                                  {|
                                  read := read entry;
                                  write := write entry;
                                  exec := exec entry;
                                  present := present entry;
                                  user := false;
                                  pa := pa entry |}) (memory s) beqPage beqIndex |} = 
                      getAncestors partition  s).
      apply getAncestorsUpdateUserFlag;trivial.
      rewrite HgetParent in *; clear HgetParent.
      apply Hdiff;trivial.
      (* configTablesAreDifferent *)
      assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
      unfold configTablesAreDifferent in *.
      simpl in *.
      fold s'.
      intros partition1 partition2 Hpart1 Hpart2 Hdiff.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      apply Hconfigdiff;trivial.
      rename H into Hcond.
      (** isChild **)
      assert(Hchid : isChild s) by intuition.
      unfold isChild in *.
      simpl in *.
      intros partition parent Hparts Hgetparent.
      rewrite getPartitionsUpdateUserFlag in *;trivial.
      rewrite getParentUpdateUserFlag in *;trivial.
      rewrite getChildrenUpdateFlagUser;trivial.
      apply Hchid;trivial.
          (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    (** physicalPageNotDerived **)
    apply physicalPageNotDerivedUpdateUserFlag;trivial.
    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by trivial.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.  
    (** isParent  *)
    assert(Hisparent : isParent s) by trivial.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by trivial.
    unfold noDupPartitionTree in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by trivial.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va0 = Some vainparent).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by trivial.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh0 s va0 = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    apply getVirtualAddressSh2UpdateUserFlag;trivial.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by trivial.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by trivial.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.
  (** Propagated properties **)
      assert(Hi2 : StateLib.getIndexOfAddr va fstLevel = lastIndex) by intuition.
      {  intuition trivial. 
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
          unfold getTableAddrRoot.
          destruct H23 as (Hor & Htableroot).
          split;trivial.
          intros.         
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          left.
          clear IHn.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
(*             rewrite Hisancestor in *. *)
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages descParent s)).
            apply isConfigTable with descChild;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
            {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages (currentPartition s) s)).
            apply isConfigTable with descChild;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.

            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
(** partitions are diffrent then config pages are different *)
        + assert(Hi3 : forall idx : index,
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
           unfold getTableAddrRoot.
          destruct H7 as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi4 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.
        
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagSameValue;trivial.
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert (Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
                  assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages descParent s)).
            apply isConfigTable with shadow1;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages (currentPartition s) s)).
            apply isConfigTable with shadow1;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.       
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.

        assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
        unfold isAncestor in *.
        destruct Hisancestor as [Hisancestor | Hisancestor].
        - subst currentPart.
          clear IHn.
(*           rewrite Hisancestor in *.*)
          left.
          unfold consistency in *.
          assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *.
          assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages descParent s)).
          apply isConfigTable with shadow2;trivial.
          intuition. subst;trivial.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2.
        - unfold consistency in *.
          subst.
          clear IHn.
          assert(In (currentPartition s) (getPartitions multiplexer s)).
          unfold currentPartitionInPartitionsList in *.
          intuition.
          assert((currentPartition s) <> ancestor).
          { unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
           unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *. 
          assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages (currentPartition s) s)).
          apply isConfigTable with shadow2;trivial.
          intuition.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          left.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages descParent s)).
            apply isConfigTable with list;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages (currentPartition s) s)).
            apply isConfigTable with list;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi4 : nextEntryIsPP currentPart sh1idx tableroot s') by intuition.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.      
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
         
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.

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
      + assert (Hfalse' : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. 
        assert((getConfigPages partition s') = 
             (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        rewrite Hconfig in *.
        assert(Hii : forall partition : page,
            In partition (getPartitions multiplexer s) -> 
            In phyDescChild (getConfigPages partition s) -> False) by trivial.
        assert(Hfalse' : In phyDescChild (getConfigPages partition s)) by trivial.
        apply Hii in Hfalse';trivial. 
      + unfold isPartitionFalse. 
         unfold s'.
         cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
         
(** Internal properties to propagate **)      
      + unfold s'.
        apply isAncestorUpdateUserFlag;trivial. 
      + destruct H.  
        unfold propagatedProperties in *.
        { assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
          apply getPartitionsUpdateUserFlag; trivial.
          rewrite Hpartions; assumption. }
       
      + apply isPEUpdateUserFlag;trivial. 
          assert(Hpe : forall idx : index,
                StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ 
                getTableAddrRoot pt PDidx descParent va s) 
          by trivial.
           apply Hpe;trivial.
      +  assert(Hroot : isPE pt (StateLib.getIndexOfAddr va fstLevel ) s /\
          getTableAddrRoot pt PDidx descParent va s).
          assert(Hpe : forall idx : index,
           StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) 
            by trivial.
          apply Hpe;trivial.
          destruct Hroot as (Hve & Hroot). 
          unfold getTableAddrRoot in *.
          destruct Hroot as (Hor & Hroot).
          split;trivial.
          intros root Hpp.
          unfold s' in Hpp.
          apply nextEntryIsPPUpdateUserFlag' in Hpp.
          apply Hroot in Hpp.
          destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
          exists nbL ; split;trivial.
          exists stop;split;trivial.
          rewrite <- Hind.
          unfold s'.
          apply getIndirectionUpdateUserFlag;trivial. 
       +  apply entryPresentFlagUpdateUserFlag;trivial. 
       + apply entryUserFlagUpdateUserFlagSameValue;trivial.
       +  apply isEntryPageUpdateUserFlag;trivial. 
       +  subst. clear IHn.       
          assert(HisAccess : isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s' =
          isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow ancestor (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt : getVirtualAddressSh2 p
                             {| currentPartition := currentPartition s;
                              memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                              (PE
                                 {|
                                 read := read entry;
                                 write := write entry;
                                 exec := exec entry;
                                 present := present entry;
                                 user := false;
                                 pa := pa entry |}) (memory s) beqPage beqIndex |} vaInAncestor =
                            getVirtualAddressSh2 p s vaInAncestor).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some L = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p vaInAncestor L (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s vaInAncestor );
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent ancestor (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
                          {|
                          currentPartition := currentPartition s;
                          memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                                      (PE
                                         {|
                                         read := read entry;
                                         write := write entry;
                                         exec := exec entry;
                                         present := present entry;
                                         user := false;
                                         pa := pa entry |}) (memory s) beqPage beqIndex |} v = 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In ancestor (getPartitions multiplexer s)).
                apply Hparentpart with descParent;trivial.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions with ancestor p0;trivial.
                unfold consistency in *.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
                        isPE ptvaInAncestor idx s /\ 
                        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                as (Hpe & Hroot);
                trivial.
                apply Hparentpart with ancestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdiff1 : p0 <> ancestor).
                              assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                              apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              assert(Hparentinpart : parentInPartitionList s) by intuition.
              unfold parentInPartitionList in *.
              apply Hparentinpart with ancestor;trivial.
              rewrite nextEntryIsPPgetParent;trivial.
              unfold not;intros Hfalsei;subst.
              now contradict Hdiff1.
              }
              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold partitionDescriptorEntry in *.
              assert(exists entry : page, nextEntryIsPP descParent PDidx entry s /\
                      entry <> defaultPage) as (pdParent & Hpp & Hnotnull).
              apply Hpde;trivial.
              left;trivial.
              clear Hpde.
              apply nextEntryIsPPgetPd in Hpp.
              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
        + unfold noDupMappedPagesList in *.
          intros partition HgetPartnewstate.
          assert ( getMappedPages partition s' = getMappedPages partition s) as Hmaps.
          unfold getMappedPages.
          assert (StateLib.getPd partition (memory s') = StateLib.getPd partition (memory s) ) as HgetPd.
          apply getPdUpdateUserFlag;trivial.
          rewrite HgetPd.
          destruct (StateLib.getPd partition (memory s)) ;trivial.
          apply getMappedPagesAuxUpdateUserFlag;trivial.
          rewrite Hmaps. trivial. 
          assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
          apply getPartitionsUpdateUserFlag;trivial.
          rewrite HgetPart in HgetPartnewstate.
          assert(Hnodupmapped : noDupMappedPagesList s) by trivial.
          apply Hnodupmapped;assumption.  
        + apply nextEntryIsPPUpdateUserFlag; assumption. 
        + apply isVAUpdateUserFlag; intuition.
          assert( Hisva :  forall idx : index,
                      StateLib.getIndexOfAddr va fstLevel = idx ->
                      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
                      apply Hisva; trivial. 
        + assert ( Hi : forall idx : index,
                  StateLib.getIndexOfAddr va fstLevel = idx ->
                  isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
          generalize (Hi lastIndex Hi2); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split; trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.      
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          unfold getTableAddrRoot.
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply isVA'UpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + assert(Hi :forall idx : index,
              StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
              isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) 
              by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption. 
        + assert(Hi : forall idx : index,
          StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
          isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split;trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.         
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
      (** WriteAccessible property **) 
      + unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. 
      + unfold isEntryPage.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  cbn. reflexivity.
      + unfold entryPresentFlag.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  
        cbn.
        unfold consistency in *.
        assert(Hpres : isPresentNotDefaultIff s ) by intuition.
        symmetry.
        apply phyPageIsPresent with ptvaInAncestor idxva s;trivial. }

(** setAccessible success **)
  simpl. subst. 
  (** recursion **)
  eapply weaken.
  eapply IHn.
  simpl. intros.
  assert(Hancestorpart : In ancestor (getPartitions MALInternal.multiplexer s)).
  { unfold propagatedProperties in *.
    unfold consistency in * .
    assert (Hparent : parentInPartitionList s) by intuition.
    unfold parentInPartitionList in *.
    apply Hparent with descParent; intuition. }
  assert (Hparentchild : In descParent (getChildren ancestor s)).
  unfold propagatedProperties in *.
  unfold consistency in *.
  assert(Hchildren : isChild s) by intuition.
  unfold isChild in *.
      apply Hchildren;trivial.
      intuition.
      apply nextEntryIsPPgetParent;intuition.
  assert(Hvs : verticalSharing s).
   { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. }
    unfold verticalSharing in *.
  assert(Hvsall : incl (getUsedPages descParent s) (getMappedPages ancestor s)).
  apply Hvs;trivial.
  clear Hvs.
  apply verticalSharing2 in Hvsall.
  unfold incl in *.
  generalize(Hvsall phypage);clear Hvsall; intros Hvs.
  assert(Hdescpage : In phypage (getMappedPages descParent s)).
  { intuition.
    subst.
    assert(Hpde : partitionDescriptorEntry s).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. } 
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP descParent PDidx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    left;trivial.
    destruct Hentrypd as (pdParent & Hpp & Hnotnul).
    apply inGetMappedPagesGetTableRoot with va pt pdParent ;trivial.
    

}

apply Hvs in Hdescpage.
clear Hvs.
unfold getMappedPages in *.
assert(HpdAncestor : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
rewrite nextEntryIsPPgetPd in *.
rewrite HpdAncestor in *.
unfold getMappedPagesAux in *.

apply filterOptionInIff in Hdescpage.
unfold getMappedPagesOption in *.
apply in_map_iff in Hdescpage.
destruct Hdescpage as (newVA & Hmapped & Hinvas).
unfold getMappedPage in Hmapped.
assert(Hlevel : Some L = StateLib.getNbLevel) by intuition.
rewrite <- Hlevel in *.
case_eq(getIndirection pdAncestor newVA L (nbLevel - 1) s);[intros ptAncestor HptAncestor |
intros HptAncestor];rewrite HptAncestor in *;try now contradict Hmapped.
case_eq(defaultPage =? ptAncestor);intros Hb;rewrite Hb in *;try now contradict Hmapped.
case_eq(StateLib.readPresent ptAncestor (StateLib.getIndexOfAddr newVA fstLevel) (memory s));
[intros present Hpresent |
intros Hpresent];rewrite Hpresent in *;try now contradict Hmapped.

destruct present;[| inversion Hmapped;subst;
 rewrite isNotDefaultPageFalse in Hnotdef;
 now contradict Hnotdef].
(* assert(vaInAncestor = newVA).
{ destruct H as (((((Ha & Hk )& Hi ) & Hj ) & Hl ) & Hm).
  intuition.
  clear IHn.
  subst.
  apply eqMappedPagesEqVaddrs with phypage pdAncestor s;trivial.
  apply getMappedPageGetTableRoot with ptvaInAncestor ancestor;trivial.
  rewrite nextEntryIsPPgetPd in *;trivial.
  apply AllVAddrAll.
  apply getMappedPageGetIndirection with ancestor ptAncestor L;trivial.
    rewrite nextEntryIsPPgetPd in *;trivial.
  assert (Hnodupmapped : noDupMappedPagesList s).
  unfold consistency in *;intuition.
  unfold noDupMappedPagesList in *.
  assert(Hnewnodup : NoDup (getMappedPages ancestor s)).
  apply Hnodupmapped;trivial.
  unfold getMappedPages in Hnewnodup.
  rewrite HpdAncestor in *.
  unfold getMappedPagesAux  in *.
  assumption. } *)
instantiate(1:= phypage).
instantiate (1:= StateLib.getIndexOfAddr vaInAncestor fstLevel).
instantiate (1:= ptvaInAncestor).

  split.
 intuition.
 split.
 assert(Hisancestor : isAncestor currentPart descParent s) by intuition.
 rewrite nextEntryIsPPgetParent in *.
  unfold propagatedProperties in *.
 unfold consistency in *. intuition.
apply isAncestorTrans with descParent;intuition.
             unfold consistency in *. intuition.
            unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition.   
intuition.
 intuition.
 subst;trivial.
   subst;trivial.
  subst;trivial. }
 

(** setAccessible failed **)
 intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition.

Qed.

Lemma getPartitionsWriteAccessibleRec partitionX n 
accessibleChild accessibleSh1 accessibleSh2 accessibleList 
descParent (va : vaddr) pt (phypage : page) idxvaparent pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild: 
{{  fun s : state =>
 propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
 pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s /\
 
isAncestor  currentPart descParent s /\
 ( In descParent (getPartitions MALInternal.multiplexer s)  /\
     (defaultPage =? phypage) = false /\
    (forall idx : index,
StateLib.getIndexOfAddr va fstLevel = idx ->
isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) /\
(defaultPage =? pt) = false /\
StateLib.getIndexOfAddr va fstLevel = idxvaparent /\
entryPresentFlag pt idxvaparent true s /\
entryUserFlag pt idxvaparent false s /\
    isEntryPage pt idxvaparent phypage s /\
    isAccessibleMappedPageInParent descParent va phypage s = true )
  /\ In partitionX (getPartitions MALInternal.multiplexer s) 
    }} 
  Internal.writeAccessibleRecAux n va descParent false {{
    fun _ s  => In partitionX (getPartitions MALInternal.multiplexer s) 
     }}.
Proof.
revert va descParent  pt phypage idxvaparent .
induction n.
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
                  destruct Hcurpart as ( Hancestors & (Hcurpart & Hnewprops) & Hnewpost).
                  clear Hancestors. 
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
  2:{
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
  } (** comparePageToNull **) 
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
  destruct H as 
  ((((((((Hprops & Hi ) & Hcurpart)& Hmult) & Hnotmult) & Hsh2root) & HnblL)
           & Hidxaddr) & H).
           
  destruct Hi as (  Hkk & Hnewprops).
 intuition.
  subst.
  apply beq_nat_false in H.
  now contradict H.
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
  intros pdAncestor. (* 
  unfold setAccessible.
  simpl.
  eapply bindRev.
(** setAccessible **)
  unfold setAccessible.
  { *) eapply bindRev.
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
    case_eq (isdefaultVA).
    -  intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition. 
    - intros isdefaultVAT.
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
      assert(Hcons : consistency s) by intuition.
      unfold consistency in *.
      destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent & _ & _).
      unfold parentInPartitionList in *. 
      instantiate (2:= ancestor).
      split.
      apply Hparent with descParent; intuition.
       
      instantiate (1:= PDidx).
      split. intuition.
      exists pdAncestor.
      split. intuition.
      split. 
      unfold consistency in *.
(*       destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent).  *)
      unfold partitionDescriptorEntry in Hpd.
      unfold parentInPartitionList in *.
      subst.
      assert(Hpartancestor : In ancestor (getPartitions MALInternal.multiplexer s)).
      {       apply Hparent with descParent; intuition. } 
      generalize (Hpd ancestor Hpartancestor); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/PDidx = sh3idx
              \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
            by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hancesnotnull).
      subst.
      assert (Hrootances : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup ancestor i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootances |
        now contradict Hrootances | 
       subst ; assumption| now contradict Hrootances| now contradict Hrootances ]  
       |now contradict Hrootances] | now contradict Hrootances].
      subst. left. split;intuition.
      intro ptvaInAncestor. simpl.
       (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2:{
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
      do  16 (* 6 *) rewrite <- and_assoc in H0.
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
  } (** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptvaInAncestorIsnull. simpl.
      case_eq ptvaInAncestorIsnull.
      2:{
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
      simpl.
      eapply bindRev; simpl;[|intros []].
      (** writeAccessible **)
      eapply WP.weaken.
      eapply WP.writeAccessible.
      intros. simpl.
      assert (exists entry0 : Pentry,
        lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry0)) as Hlookup.
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
      do 9 rewrite <- and_assoc in H.
      destruct H as (Hsplit & Hfalse & Hrest).
      assert(Heqphy : phypage = pa entry).
      {    destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (Hnew & Hll & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
         intuition. subst.
        unfold isAccessibleMappedPageInParent in *.
        assert (HgetVirt : getVirtualAddressSh2 sh2 s va  = Some vaInAncestor).
        apply isVaInParent with descParent ptsh2;trivial.
        apply nextEntryIsPPgetSndShadow in Hppsh2.
        rewrite Hppsh2 in *.
        rewrite HgetVirt in *.
        rewrite nextEntryIsPPgetParent in * .
        rewrite Hppparent in *. 
        apply nextEntryIsPPgetPd in Hpppd .
        rewrite Hpppd in *.
        case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor);
        intros * Hacce;
        rewrite Hacce in *;try now contradict Hfalse.
        unfold getAccessibleMappedPage in Hacce.
        assert( isPE ptvaInAncestor  (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) as (Hve & Hroot ).
        apply Hgetroot2;trivial.
        unfold getTableAddrRoot in *.
        destruct Hroot as (_ & Hroot).
        rewrite <- nextEntryIsPPgetPd in *.
        apply Hroot in  Hpppd.
        clear Hroot.
        destruct Hpppd as (nbL & HnbL & stop & Hstop & Hind).
        subst.
        rewrite <- HnbL in *.
        assert(Hgetind : getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s  
        = Some ptvaInAncestor).
        apply getIndirectionStopLevelGT2 with (nbL+1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind in *.
        rewrite H in *.
        destruct ( StateLib.readPresent ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s));try now contradict Hacce.
        destruct b;try now contradict Hacce.
        destruct ( StateLib.readAccessible ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s)); try now contradict Hacce.
        destruct b; try now contradict Hacce.
        unfold StateLib.readPhyEntry in *. 
        rewrite Hlookup in *.
        apply beq_nat_true in Hfalse.
        inversion Hacce.
        subst.
        destruct phypage; destruct (pa entry).
        simpl in *.
        subst.
        f_equal; apply proof_irrelevance. }
      assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true).
      { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        rewrite Heqphy.
        destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
        apply isAccessibleMappedPageInParentTrue with descParent va phypage ptvaInAncestor ptsh2 pdAncestor;
        subst;intuition.
        subst;assumption. }
      repeat rewrite and_assoc in Hsplit.
      destruct Hsplit as (Hprops & Hsplit).
(*       unfold propagatedProperties in *.
      do 73 rewrite <- and_assoc in Hprops.
      destruct Hprops as (Hprops & xx & Hprops2). 
            repeat rewrite and_assoc in Hprops. *)
      assert (Hnewprops := conj  Hprops  Hsplit).
      assert (H := conj (conj Hnewprops Htrue) Hrest).
      simpl.
      clear Hnewprops.
    (*   repeat rewrite and_assoc in H. *)
      pattern s in H.
      match type of H with 
      | ?HT s => instantiate (1 := fun tt s => HT s  /\ 
                  entryUserFlag ptvaInAncestor idxva false s /\
                  isEntryPage ptvaInAncestor idxva phypage s /\
                  entryPresentFlag ptvaInAncestor idxva true s  ) 
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
      simpl.
      unfold propagatedProperties in *. 
      do 7 rewrite and_assoc.
      clear Hrest  Hsplit  Hprops.
      split.
      
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
      split.
      (** partitionDescriptorEntry **)
      apply partitionDescriptorEntryUpdateUserFlag;trivial.
      intuition.
      (** dataStructurePdSh1Sh2asRoot **)
      destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
      Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      (** currentPartitionInPartitionsList **)
      split.
      unfold currentPartitionInPartitionsList in *.
      simpl in *. subst. 
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite Hpartions. assumption.
      (** noDupMappedPagesList **)  
      split.    
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
      split.
      (** noDupConfigPagesList **)
      apply getIndirectionsNoDupUpdateUserFlag; trivial.
      split.
      (** parentInPartitionList **)
      unfold parentInPartitionList in *.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart.
      intros partition HgetParts parent Hroot.
      generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
      apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
      apply Hparent; trivial.
      split.
      (** accessibleVAIsNotPartitionDescriptor **)
     unfold s'.
      subst.
      clear IHn.
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (_ & Hi).
      intuition.
      subst.
      apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag  with level ancestor   
        pdAncestor;trivial.
      assert(Hparentpart : parentInPartitionList s) by trivial.
      unfold parentInPartitionList in *.
      apply Hparent with descParent;trivial. 
       assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
      assert(  isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s ) as (_ & Hroot).
      apply Hget;split;trivial.
      assumption.
      apply nextEntryIsPPgetPd;trivial.
      subst.
      assert(HaccessInParent : isAccessibleMappedPageInParent descParent va (pa entry) s = true)
       by trivial.
       unfold isAccessibleMappedPageInParent in HaccessInParent.
       (** Here we use the property already present into the precondition : 
            *)
       assert(Hcursh2 : nextEntryIsPP descParent sh2idx sh2 s ) by trivial.
      apply nextEntryIsPPgetSndShadow in Hcursh2.
      rewrite Hcursh2 in HaccessInParent.
      assert(Hvainparent : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
      { assert(Hxx : forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx ->
        isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
        assert(Hgetva : isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\ 
        getTableAddrRoot ptsh2 sh2idx descParent va s).
        apply Hxx;trivial. clear Hxx.
        destruct Hgetva as (Hva & Hgetva).
        assert(Hisva : isVA' ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s) 
        by trivial.
        unfold getVirtualAddressSh2.
        unfold getTableAddrRoot in Hgetva.
        destruct Hgetva as (_ & Hgetva).
        assert(HcurSh2 : nextEntryIsPP descParent sh2idx sh2 s).
        rewrite  nextEntryIsPPgetSndShadow ;trivial.
        apply Hgetva in HcurSh2.
        destruct HcurSh2 as (nbL & HnbL & stop & Hstop & Hind).
        rewrite <- HnbL.
        subst.
        assert(Hgetind : getIndirection sh2 va nbL (nbLevel - 1) s = Some ptsh2).
        apply getIndirectionStopLevelGT2 with (nbL + 1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind.
        assert (Hptnotnull : (defaultPage =? ptsh2) = false) by trivial.
        rewrite Hptnotnull.
        unfold  isVA' in *. 
        unfold StateLib.readVirtual.
        destruct(lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ); 
        try now contradict Hisva.
        destruct v;try now contradict Hisva.
        subst. trivial. }
      rewrite Hvainparent in *.
      assert(Hgetparent : StateLib.getParent descParent (memory s) = Some ancestor).
      { apply nextEntryIsPPgetParent;trivial. }
      rewrite Hgetparent in *.
      assert(Hgetpdparent : StateLib.getPd ancestor (memory s) = Some pdAncestor).
      { apply nextEntryIsPPgetPd;trivial. }
      rewrite Hgetpdparent in *.
      case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor ); intros * Hi .
      rewrite Hi in *.
      unfold getAccessibleMappedPage in Hi.
      case_eq (StateLib.getNbLevel);intros * Hi2 ; rewrite Hi2 in *;
       try now contradict Hi.
      assert(Hancestor : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by 
      trivial.
      assert(Hget : isPE ptvaInAncestor ( StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\
            getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s).
      apply Hancestor; clear Hancestor;
      trivial.
      destruct Hget as (Hva & Hget).
      unfold getTableAddrRoot in Hget.
      destruct Hget as (_ & Hget).
      apply nextEntryIsPPgetPd in Hgetpdparent.
      apply Hget in Hgetpdparent.
      destruct Hgetpdparent as (nbL & HnbL & stop & Hstop & Hgettable).
      clear Hget.
      rewrite <- HnbL in *.
      inversion Hi2.
      subst.
      assert(Hind :getIndirection pdAncestor vaInAncestor l (nbLevel - 1) s = Some ptvaInAncestor).
      apply getIndirectionStopLevelGT2 with (l+1);trivial.
      omega.
      apply getNbLevelEq in HnbL.
      rewrite HnbL.
      unfold CLevel.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      simpl;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      rewrite Hind in *.
      assert (Hnotnull : (defaultPage =? ptvaInAncestor) = false) by trivial.
      rewrite Hnotnull in *.
      destruct (StateLib.readPresent ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b; try now contradict Hi.
      destruct(StateLib.readAccessible ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b.
      unfold StateLib.readPhyEntry in *.
      rewrite Hlookup in *.
      symmetry; assumption.
      now contradict Hi.
      rewrite Hi in *. 
      now contradict HaccessInParent.      rewrite Hi in *. 
      now contradict HaccessInParent.
      
   (* accessibleChildPageIsAccessibleIntoParent *)
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (Hancestor & Hi).
      unfold s'.
      intuition. 
      subst.
      clear IHn.
      apply accessibleChildPageIsAccessibleIntoParentUpdateUserFlagFlase
      with level ancestor pdAncestor va ptsh2 descParent pt;trivial.
      assert(Hparentpart : parentInPartitionList s).
      unfold consistency in *; intuition.
      unfold parentInPartitionList in *.
      apply Hparentpart with descParent;trivial.
      (* noCycleInPartitionTree *)
      assert(Hdiff : noCycleInPartitionTree s) by trivial.
      unfold noCycleInPartitionTree in *.
      intros parent partition Hparts Hparentpart.
      simpl in *.
      assert (getPartitions multiplexer {|
              currentPartition := currentPartition s;
              memory := add ptvaInAncestor idxva
                          (PE
                             {|
                             read := read entry;
                             write := write entry;
                             exec := exec entry;
                             present := present entry;
                             user := false;
                             pa := pa entry |}) (memory s) beqPage beqIndex |}
               = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(HgetParent : getAncestors partition
                {|
                   currentPartition := currentPartition s;
                   memory := add ptvaInAncestor idxva
                               (PE
                                  {|
                                  read := read entry;
                                  write := write entry;
                                  exec := exec entry;
                                  present := present entry;
                                  user := false;
                                  pa := pa entry |}) (memory s) beqPage beqIndex |} = 
                      getAncestors partition  s).
      apply getAncestorsUpdateUserFlag;trivial.
      rewrite HgetParent in *; clear HgetParent.
      apply Hdiff;trivial.
      (* configTablesAreDifferent *)
      assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
      unfold configTablesAreDifferent in *.
      simpl in *.
      fold s'.
      intros partition1 partition2 Hpart1 Hpart2 Hdiff.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      apply Hconfigdiff;trivial.
      rename H into Hcond.
      (** isChild **)
      assert(Hchid : isChild s) by intuition.
      unfold isChild in *.
      simpl in *.
      intros partition parent Hparts Hgetparent.
      rewrite getPartitionsUpdateUserFlag in *;trivial.
      rewrite getParentUpdateUserFlag in *;trivial.
      rewrite getChildrenUpdateFlagUser;trivial.
      apply Hchid;trivial.
          (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    (** physicalPageNotDerived **)
    apply physicalPageNotDerivedUpdateUserFlag;trivial.

    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by trivial.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.  
    (** isParent  *)
    assert(Hisparent : isParent s) by trivial.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by trivial.
    unfold noDupPartitionTree in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by trivial.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va0 = Some vainparent).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by trivial.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh0 s va0 = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    apply getVirtualAddressSh2UpdateUserFlag;trivial.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by trivial.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by trivial.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.
  (** Propagated properties **)
      assert(Hi2 : StateLib.getIndexOfAddr va fstLevel = lastIndex) by intuition.
      {  intuition trivial. 
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
          unfold getTableAddrRoot.
          destruct H23 as (Hor & Htableroot).
          split;trivial.
          intros.         
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          left.
          clear IHn.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
(*             rewrite Hisancestor in *. *)
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages descParent s)).
            apply isConfigTable with descChild;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
            {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages (currentPartition s) s)).
            apply isConfigTable with descChild;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.

            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
(** partitions are diffrent then config pages are different *)
        + assert(Hi3 : forall idx : index,
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
           unfold getTableAddrRoot.
          destruct H7 as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi4 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.
        
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagSameValue;trivial.
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert (Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
                  assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages descParent s)).
            apply isConfigTable with shadow1;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages (currentPartition s) s)).
            apply isConfigTable with shadow1;trivial.
            intuition. 
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.       
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.

        assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
        unfold isAncestor in *.
        destruct Hisancestor as [Hisancestor | Hisancestor].
        - subst currentPart .
          clear IHn.
(*           rewrite Hisancestor in *. *)
          left.
          unfold consistency in *.
          assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *.
          assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages descParent s)).
          apply isConfigTable with shadow2;trivial.
          intuition. subst;trivial.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2.
        - unfold consistency in *.
          subst.
          clear IHn.
          assert(In (currentPartition s) (getPartitions multiplexer s)).
          unfold currentPartitionInPartitionsList in *.
          intuition.
          assert((currentPartition s) <> ancestor).
          { unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *. 
          assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages (currentPartition s) s)).
          apply isConfigTable with shadow2;trivial.
          intuition.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          left.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages descParent s)).
            apply isConfigTable with list;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.            
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages (currentPartition s) s)).
            apply isConfigTable with list;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi4 : nextEntryIsPP currentPart sh1idx tableroot s') by intuition.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.      
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
         
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.

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
      + assert (Hfalse' : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. 
        assert((getConfigPages partition s') = 
             (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        rewrite Hconfig in *.
        assert(Hii : forall partition : page,
            In partition (getPartitions multiplexer s) -> 
            In phyDescChild (getConfigPages partition s) -> False) by trivial.
        assert(Hfalse' : In phyDescChild (getConfigPages partition s)) by trivial.
        apply Hii in Hfalse';trivial. 
      + unfold isPartitionFalse. 
         unfold s'.
         cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
         
(** Internal properties to propagate **)      
      + unfold s'.
        apply isAncestorUpdateUserFlag;trivial. 
      + destruct H.  
        unfold propagatedProperties in *.
        { assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
          apply getPartitionsUpdateUserFlag; trivial.
          rewrite Hpartions; assumption. }
       
      + apply isPEUpdateUserFlag;trivial. 
          assert(Hpe : forall idx : index,
                StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ 
                getTableAddrRoot pt PDidx descParent va s) 
          by trivial.
           apply Hpe;trivial.
      +  assert(Hroot : isPE pt (StateLib.getIndexOfAddr va fstLevel ) s /\
          getTableAddrRoot pt PDidx descParent va s).
          assert(Hpe : forall idx : index,
           StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) 
            by trivial.
          apply Hpe;trivial.
          destruct Hroot as (Hve & Hroot). 
          unfold getTableAddrRoot in *.
          destruct Hroot as (Hor & Hroot).
          split;trivial.
          intros root Hpp.
          unfold s' in Hpp.
          apply nextEntryIsPPUpdateUserFlag' in Hpp.
          apply Hroot in Hpp.
          destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
          exists nbL ; split;trivial.
          exists stop;split;trivial.
          rewrite <- Hind.
          unfold s'.
          apply getIndirectionUpdateUserFlag;trivial. 
       +  apply entryPresentFlagUpdateUserFlag;trivial. 
       + apply entryUserFlagUpdateUserFlagSameValue;trivial.
       +  apply isEntryPageUpdateUserFlag;trivial. 
       +  subst. clear IHn.       
          assert(HisAccess : isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s' =
          isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow ancestor (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt : getVirtualAddressSh2 p
                             {| currentPartition := currentPartition s;
                              memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                              (PE
                                 {|
                                 read := read entry;
                                 write := write entry;
                                 exec := exec entry;
                                 present := present entry;
                                 user := false;
                                 pa := pa entry |}) (memory s) beqPage beqIndex |} vaInAncestor =
                            getVirtualAddressSh2 p s vaInAncestor).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some L = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p vaInAncestor L (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s vaInAncestor );
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent ancestor (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
                          {|
                          currentPartition := currentPartition s;
                          memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                                      (PE
                                         {|
                                         read := read entry;
                                         write := write entry;
                                         exec := exec entry;
                                         present := present entry;
                                         user := false;
                                         pa := pa entry |}) (memory s) beqPage beqIndex |} v = 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In ancestor (getPartitions multiplexer s)).
                apply Hparentpart with descParent;trivial.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions with ancestor p0;trivial.
                unfold consistency in *.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
                        isPE ptvaInAncestor idx s /\ 
                        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                as (Hpe & Hroot);
                trivial.
                apply Hparentpart with ancestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdiff1 : p0 <> ancestor).
                              assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                              apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              assert(Hparentinpart : parentInPartitionList s) by intuition.
              unfold parentInPartitionList in *.
              apply Hparentinpart with ancestor;trivial.
              rewrite nextEntryIsPPgetParent;trivial.
              unfold not;intros Hfalsei;subst.
              now contradict Hdiff1.
              }
              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold partitionDescriptorEntry in *.
              assert(exists entry : page, nextEntryIsPP descParent PDidx entry s /\
                      entry <> defaultPage) as (pdParent & Hpp & Hnotnull).
              apply Hpde;trivial.
              left;trivial.
              clear Hpde.
              apply nextEntryIsPPgetPd in Hpp.
              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
        +   
          assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
          apply getPartitionsUpdateUserFlag;trivial.
          rewrite HgetPart;trivial. 
        + apply nextEntryIsPPUpdateUserFlag; assumption. 
        + apply isVAUpdateUserFlag; intuition.
          assert( Hisva :  forall idx : index,
                      StateLib.getIndexOfAddr va fstLevel = idx ->
                      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
                      apply Hisva; trivial. 
        + assert ( Hi : forall idx : index,
                  StateLib.getIndexOfAddr va fstLevel = idx ->
                  isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
          generalize (Hi lastIndex Hi2); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split; trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.      
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          unfold getTableAddrRoot.
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply isVA'UpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + assert(Hi :forall idx : index,
              StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
              isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) 
              by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption. 
        + assert(Hi : forall idx : index,
          StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
          isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split;trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.         
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
      (** WriteAccessible property **) 
      + unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. 
      + unfold isEntryPage.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  cbn. reflexivity.
      + unfold entryPresentFlag.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  
        cbn.
        unfold consistency in *.
        assert(Hpres : isPresentNotDefaultIff s ) by intuition.
        symmetry.
        apply phyPageIsPresent with ptvaInAncestor idxva s;trivial. }

(** setAccessible success **)
  simpl. subst. 
  (** recursion **)
  eapply weaken.
  eapply IHn.
  simpl. intros.
  assert(Hancestorpart : In ancestor (getPartitions MALInternal.multiplexer s)).
  { unfold propagatedProperties in *.
    unfold consistency in * .
    assert (Hparent : parentInPartitionList s) by intuition.
    unfold parentInPartitionList in *.
    apply Hparent with descParent; intuition. }
  assert (Hparentchild : In descParent (getChildren ancestor s)).
  unfold propagatedProperties in *.
  unfold consistency in *.
  assert(Hchildren : isChild s) by intuition.
  unfold isChild in *.
      apply Hchildren;trivial.
      intuition.
      apply nextEntryIsPPgetParent;intuition.
  assert(Hvs : verticalSharing s).
   { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. }
    unfold verticalSharing in *.
  assert(Hvsall : incl (getUsedPages descParent s) (getMappedPages ancestor s)).
  apply Hvs;trivial.
  clear Hvs.
  apply verticalSharing2 in Hvsall.
  unfold incl in *.
  generalize(Hvsall phypage);clear Hvsall; intros Hvs.
  assert(Hdescpage : In phypage (getMappedPages descParent s)).
  { intuition.
    subst.
    assert(Hpde : partitionDescriptorEntry s).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. } 
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP descParent PDidx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    left;trivial.
    destruct Hentrypd as (pdParent & Hpp & Hnotnul).
    apply inGetMappedPagesGetTableRoot with va pt pdParent ;trivial.
    
    
}

apply Hvs in Hdescpage.
clear Hvs.
unfold getMappedPages in *.
assert(HpdAncestor : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
rewrite nextEntryIsPPgetPd in *.
rewrite HpdAncestor in *.
unfold getMappedPagesAux in *.

apply filterOptionInIff in Hdescpage.
unfold getMappedPagesOption in *.
apply in_map_iff in Hdescpage.
destruct Hdescpage as (newVA & Hmapped & Hinvas).
unfold getMappedPage in Hmapped.
assert(Hlevel : Some L = StateLib.getNbLevel) by intuition.
rewrite <- Hlevel in *.
case_eq(getIndirection pdAncestor newVA L (nbLevel - 1) s);[intros ptAncestor HptAncestor |
intros HptAncestor];rewrite HptAncestor in *;try now contradict Hmapped.
case_eq(defaultPage =? ptAncestor);intros Hb;rewrite Hb in *;try now contradict Hmapped.
case_eq(StateLib.readPresent ptAncestor (StateLib.getIndexOfAddr newVA fstLevel) (memory s));
[intros present Hpresent |
intros Hpresent];rewrite Hpresent in *;try now contradict Hmapped.

destruct present;[| inversion Hmapped;subst;
 rewrite isNotDefaultPageFalse in Hnotdef;
 now contradict Hnotdef].
(* assert(vaInAncestor = newVA).
{ destruct H as (((((Ha & Hk )& Hi ) & Hj ) & Hl ) & Hm).
  intuition.
  clear IHn.
  subst.
  apply eqMappedPagesEqVaddrs with phypage pdAncestor s;trivial.
  apply getMappedPageGetTableRoot with ptvaInAncestor ancestor;trivial.
  rewrite nextEntryIsPPgetPd in *;trivial.
  apply AllVAddrAll.
  apply getMappedPageGetIndirection with ancestor ptAncestor L;trivial.
    rewrite nextEntryIsPPgetPd in *;trivial.
  assert (Hnodupmapped : noDupMappedPagesList s).
  unfold consistency in *;intuition.
  unfold noDupMappedPagesList in *.
  assert(Hnewnodup : NoDup (getMappedPages ancestor s)).
  apply Hnodupmapped;trivial.
  unfold getMappedPages in Hnewnodup.
  rewrite HpdAncestor in *.
  unfold getMappedPagesAux  in *.
  assumption. } *)
instantiate(1:= phypage).
instantiate (1:= StateLib.getIndexOfAddr vaInAncestor fstLevel).
instantiate (1:= ptvaInAncestor).

  split.
 intuition.
 split.
 assert(Hisancestor : isAncestor currentPart descParent s) by intuition.
 rewrite nextEntryIsPPgetParent in *.

unfold propagatedProperties in *. unfold consistency in *.  apply isAncestorTrans with descParent;intuition.              unfold consistency in *. intuition.
            unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition.   

intuition.
 intuition.
 subst;trivial.
   subst;trivial.
  subst;trivial. }
 

(** setAccessible failed **)
 intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition.

Qed.
Lemma getAccessibleNoneWriteAccessibleRec n  pd va1 
accessibleChild accessibleSh1 accessibleSh2 accessibleList 
descParent (va : vaddr) pt (phypage : page) idxvaparent pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild: 
{{  fun s : state =>
 propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
 pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s /\
 
isAncestor  currentPart descParent s /\
 ( In descParent (getPartitions MALInternal.multiplexer s)  /\
     (defaultPage =? phypage) = false /\
    (forall idx : index,
StateLib.getIndexOfAddr va fstLevel = idx ->
isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) /\
(defaultPage =? pt) = false /\
StateLib.getIndexOfAddr va fstLevel = idxvaparent /\
entryPresentFlag pt idxvaparent true s /\
entryUserFlag pt idxvaparent false s /\
    isEntryPage pt idxvaparent phypage s /\
    isAccessibleMappedPageInParent descParent va phypage s = true )
  /\ getAccessibleMappedPage pd  s va1 = NonePage
    }} 
  Internal.writeAccessibleRecAux n va descParent false {{
    fun _ s  => getAccessibleMappedPage pd s va1 = NonePage
     }}.
Proof.
revert va descParent  pt phypage idxvaparent .
induction n.
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
                  destruct Hcurpart as ( Hancestors & (Hcurpart & Hnewprops) & Hnewpost).
                  clear Hancestors. 
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
  2:{
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
  } (** comparePageToNull **) 
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
  destruct H as 
  ((((((((Hprops & Hi ) & Hcurpart)& Hmult) & Hnotmult) & Hsh2root) & HnblL)
           & Hidxaddr) & H).
           
  destruct Hi as (  Hkk & Hnewprops).
 intuition.
  subst.
  apply beq_nat_false in H.
  now contradict H.
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
  intros pdAncestor. (* 
  unfold setAccessible.
  simpl.
  eapply bindRev.
(** setAccessible **)
  unfold setAccessible.
  { *) eapply bindRev.
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
    case_eq (isdefaultVA).
    -  intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition. 
    - intros isdefaultVAT.
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
      assert(Hcons : consistency s) by intuition.
      unfold consistency in *.
      destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent & _ & _).
      unfold parentInPartitionList in *. 
      instantiate (2:= ancestor).
      split.
      apply Hparent with descParent; intuition.
       
      instantiate (1:= PDidx).
      split. intuition.
      exists pdAncestor.
      split. intuition.
      split. 
      unfold consistency in *.
(*       destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent).  *)
      unfold partitionDescriptorEntry in Hpd.
      unfold parentInPartitionList in *.
      subst.
      assert(Hpartancestor : In ancestor (getPartitions MALInternal.multiplexer s)).
      {       apply Hparent with descParent; intuition. } 
      generalize (Hpd ancestor Hpartancestor); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/PDidx = sh3idx
              \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
            by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hancesnotnull).
      subst.
      assert (Hrootances : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup ancestor i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootances |
        now contradict Hrootances | 
       subst ; assumption| now contradict Hrootances| now contradict Hrootances ]  
       |now contradict Hrootances] | now contradict Hrootances].
      subst. left. split;intuition.
      intro ptvaInAncestor. simpl.
       (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2:{
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
      do  16 (* 6 *) rewrite <- and_assoc in H0.
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
  } (** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptvaInAncestorIsnull. simpl.
      case_eq ptvaInAncestorIsnull.
      2:{
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
      simpl.
      eapply bindRev; simpl;[|intros []].
      (** writeAccessible **)
      eapply WP.weaken.
      eapply WP.writeAccessible.
      intros. simpl.
      assert (exists entry0 : Pentry,
        lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry0)) as Hlookup.
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
      do 9 rewrite <- and_assoc in H.
      destruct H as (Hsplit & Hfalse & Hrest).
      assert(Heqphy : phypage = pa entry).
      {    destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (Hnew & Hll & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
         intuition. subst.
        unfold isAccessibleMappedPageInParent in *.
        assert (HgetVirt : getVirtualAddressSh2 sh2 s va  = Some vaInAncestor).
        apply isVaInParent with descParent ptsh2;trivial.
        apply nextEntryIsPPgetSndShadow in Hppsh2.
        rewrite Hppsh2 in *.
        rewrite HgetVirt in *.
        rewrite nextEntryIsPPgetParent in * .
        rewrite Hppparent in *. 
        apply nextEntryIsPPgetPd in Hpppd .
        rewrite Hpppd in *.
        case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor);
        intros * Hacce;
        rewrite Hacce in *;try now contradict Hfalse.
        unfold getAccessibleMappedPage in Hacce.
        assert( isPE ptvaInAncestor  (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) as (Hve & Hroot ).
        apply Hgetroot2;trivial.
        unfold getTableAddrRoot in *.
        destruct Hroot as (_ & Hroot).
        rewrite <- nextEntryIsPPgetPd in *.
        apply Hroot in  Hpppd.
        clear Hroot.
        destruct Hpppd as (nbL & HnbL & stop & Hstop & Hind).
        subst.
        rewrite <- HnbL in *.
        assert(Hgetind : getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s  
        = Some ptvaInAncestor).
        apply getIndirectionStopLevelGT2 with (nbL+1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind in *.
        rewrite H in *.
        destruct ( StateLib.readPresent ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s));try now contradict Hacce.
        destruct b;try now contradict Hacce.
        destruct ( StateLib.readAccessible ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s)); try now contradict Hacce.
        destruct b; try now contradict Hacce.
        unfold StateLib.readPhyEntry in *. 
        rewrite Hlookup in *.
        apply beq_nat_true in Hfalse.
        inversion Hacce.
        subst.
        destruct phypage; destruct (pa entry).
        simpl in *.
        subst.
        f_equal; apply proof_irrelevance. }
      assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true).
      { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        rewrite Heqphy.
        destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
        apply isAccessibleMappedPageInParentTrue with descParent va phypage ptvaInAncestor ptsh2 pdAncestor;
        subst;intuition.
        subst;assumption. }
      repeat rewrite and_assoc in Hsplit.
      destruct Hsplit as (Hprops & Hsplit).
(*       unfold propagatedProperties in *.
      do 73 rewrite <- and_assoc in Hprops.
      destruct Hprops as (Hprops & xx & Hprops2). 
            repeat rewrite and_assoc in Hprops. *)
      assert (Hnewprops := conj  Hprops  Hsplit).
      assert (H := conj (conj Hnewprops Htrue) Hrest).
      simpl.
      clear Hnewprops.
    (*   repeat rewrite and_assoc in H. *)
      pattern s in H.
      match type of H with 
      | ?HT s => instantiate (1 := fun tt s => HT s  /\ 
                  entryUserFlag ptvaInAncestor idxva false s /\
                  isEntryPage ptvaInAncestor idxva phypage s /\
                  entryPresentFlag ptvaInAncestor idxva true s  ) 
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
      simpl.
      unfold propagatedProperties in *. 
      do 7 rewrite and_assoc.
      clear Hrest  Hsplit  Hprops.
      split.
      
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
      split.
      (** partitionDescriptorEntry **)
      apply partitionDescriptorEntryUpdateUserFlag;trivial.
      intuition.
      (** dataStructurePdSh1Sh2asRoot **)
      destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
      Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      (** currentPartitionInPartitionsList **)
      split.
      unfold currentPartitionInPartitionsList in *.
      simpl in *. subst. 
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite Hpartions. assumption.
      (** noDupMappedPagesList **)  
      split.    
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
      split.
      (** noDupConfigPagesList **)
      apply getIndirectionsNoDupUpdateUserFlag; trivial.
      split.
      (** parentInPartitionList **)
      unfold parentInPartitionList in *.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart.
      intros partition HgetParts parent Hroot.
      generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
      apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
      apply Hparent; trivial.
      split.
      (** accessibleVAIsNotPartitionDescriptor **)
     unfold s'.
      subst.
      clear IHn.
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (_ & Hi).
      intuition.
      subst.
      apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag  with level ancestor   
        pdAncestor;trivial.
      assert(Hparentpart : parentInPartitionList s) by trivial.
      unfold parentInPartitionList in *.
      apply Hparent with descParent;trivial. 
       assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
      assert(  isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s ) as (_ & Hroot).
      apply Hget;split;trivial.
      assumption.
      apply nextEntryIsPPgetPd;trivial.
      subst.
      assert(HaccessInParent : isAccessibleMappedPageInParent descParent va (pa entry) s = true)
       by trivial.
       unfold isAccessibleMappedPageInParent in HaccessInParent.
       (** Here we use the property already present into the precondition : 
            *)
       assert(Hcursh2 : nextEntryIsPP descParent sh2idx sh2 s ) by trivial.
      apply nextEntryIsPPgetSndShadow in Hcursh2.
      rewrite Hcursh2 in HaccessInParent.
      assert(Hvainparent : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
      { assert(Hxx : forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx ->
        isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
        assert(Hgetva : isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\ 
        getTableAddrRoot ptsh2 sh2idx descParent va s).
        apply Hxx;trivial. clear Hxx.
        destruct Hgetva as (Hva & Hgetva).
        assert(Hisva : isVA' ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s) 
        by trivial.
        unfold getVirtualAddressSh2.
        unfold getTableAddrRoot in Hgetva.
        destruct Hgetva as (_ & Hgetva).
        assert(HcurSh2 : nextEntryIsPP descParent sh2idx sh2 s).
        rewrite  nextEntryIsPPgetSndShadow ;trivial.
        apply Hgetva in HcurSh2.
        destruct HcurSh2 as (nbL & HnbL & stop & Hstop & Hind).
        rewrite <- HnbL.
        subst.
        assert(Hgetind : getIndirection sh2 va nbL (nbLevel - 1) s = Some ptsh2).
        apply getIndirectionStopLevelGT2 with (nbL + 1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind.
        assert (Hptnotnull : (defaultPage =? ptsh2) = false) by trivial.
        rewrite Hptnotnull.
        unfold  isVA' in *. 
        unfold StateLib.readVirtual.
        destruct(lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ); 
        try now contradict Hisva.
        destruct v;try now contradict Hisva.
        subst. trivial. }
      rewrite Hvainparent in *.
      assert(Hgetparent : StateLib.getParent descParent (memory s) = Some ancestor).
      { apply nextEntryIsPPgetParent;trivial. }
      rewrite Hgetparent in *.
      assert(Hgetpdparent : StateLib.getPd ancestor (memory s) = Some pdAncestor).
      { apply nextEntryIsPPgetPd;trivial. }
      rewrite Hgetpdparent in *.
      case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor ); intros * Hi .
      rewrite Hi in *.
      unfold getAccessibleMappedPage in Hi.
      case_eq (StateLib.getNbLevel);intros * Hi2 ; rewrite Hi2 in *;
       try now contradict Hi.
      assert(Hancestor : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by 
      trivial.
      assert(Hget : isPE ptvaInAncestor ( StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\
            getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s).
      apply Hancestor; clear Hancestor;
      trivial.
      destruct Hget as (Hva & Hget).
      unfold getTableAddrRoot in Hget.
      destruct Hget as (_ & Hget).
      apply nextEntryIsPPgetPd in Hgetpdparent.
      apply Hget in Hgetpdparent.
      destruct Hgetpdparent as (nbL & HnbL & stop & Hstop & Hgettable).
      clear Hget.
      rewrite <- HnbL in *.
      inversion Hi2.
      subst.
      assert(Hind :getIndirection pdAncestor vaInAncestor l (nbLevel - 1) s = Some ptvaInAncestor).
      apply getIndirectionStopLevelGT2 with (l+1);trivial.
      omega.
      apply getNbLevelEq in HnbL.
      rewrite HnbL.
      unfold CLevel.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      simpl;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      rewrite Hind in *.
      assert (Hnotnull : (defaultPage =? ptvaInAncestor) = false) by trivial.
      rewrite Hnotnull in *.
      destruct (StateLib.readPresent ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b; try now contradict Hi.
      destruct(StateLib.readAccessible ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b.
      unfold StateLib.readPhyEntry in *.
      rewrite Hlookup in *.
      symmetry; assumption.
      now contradict Hi.
      rewrite Hi in *. 
      now contradict HaccessInParent.
            rewrite Hi in *. 
      now contradict HaccessInParent.
   (* accessibleChildPageIsAccessibleIntoParent *)
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (Hancestor & Hi).
      unfold s'.
      intuition. 
      subst.
      clear IHn.
      apply accessibleChildPageIsAccessibleIntoParentUpdateUserFlagFlase
      with level ancestor pdAncestor va ptsh2 descParent pt;trivial.
      assert(Hparentpart : parentInPartitionList s).
      unfold consistency in *; intuition.
      unfold parentInPartitionList in *.
      apply Hparentpart with descParent;trivial.
      (* noCycleInPartitionTree *)
      assert(Hdiff : noCycleInPartitionTree s) by trivial.
      unfold noCycleInPartitionTree in *.
      intros parent partition Hparts Hparentpart.
      simpl in *.
      assert (getPartitions multiplexer {|
              currentPartition := currentPartition s;
              memory := add ptvaInAncestor idxva
                          (PE
                             {|
                             read := read entry;
                             write := write entry;
                             exec := exec entry;
                             present := present entry;
                             user := false;
                             pa := pa entry |}) (memory s) beqPage beqIndex |}
               = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(HgetParent : getAncestors partition
                {|
                   currentPartition := currentPartition s;
                   memory := add ptvaInAncestor idxva
                               (PE
                                  {|
                                  read := read entry;
                                  write := write entry;
                                  exec := exec entry;
                                  present := present entry;
                                  user := false;
                                  pa := pa entry |}) (memory s) beqPage beqIndex |} = 
                      getAncestors partition  s).
      apply getAncestorsUpdateUserFlag;trivial.
      rewrite HgetParent in *; clear HgetParent.
      apply Hdiff;trivial.
      (* configTablesAreDifferent *)
      assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
      unfold configTablesAreDifferent in *.
      simpl in *.
      fold s'.
      intros partition1 partition2 Hpart1 Hpart2 Hdiff.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      apply Hconfigdiff;trivial.
      rename H into Hcond.
      (** isChild **)
      assert(Hchid : isChild s) by intuition.
      unfold isChild in *.
      simpl in *.
      intros partition parent Hparts Hgetparent.
      rewrite getPartitionsUpdateUserFlag in *;trivial.
      rewrite getParentUpdateUserFlag in *;trivial.
      rewrite getChildrenUpdateFlagUser;trivial.
      apply Hchid;trivial.
          (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    (** physicalPageNotDerived **)
    apply physicalPageNotDerivedUpdateUserFlag;trivial.
    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by trivial.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.  
    (** isParent  *)
    assert(Hisparent : isParent s) by trivial.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by trivial.
    unfold noDupPartitionTree in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by trivial.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va0 = Some vainparent).
    apply Hwell with partition pg pd0;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by trivial.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh0 s va0 = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg pd0;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    apply getVirtualAddressSh2UpdateUserFlag;trivial.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by trivial.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd0;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by trivial.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd0;trivial.
    (** Propagated properties **)
      assert(Hi2 : StateLib.getIndexOfAddr va fstLevel = lastIndex) by intuition.
      {  intuition trivial. 
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
          unfold getTableAddrRoot.
          destruct H23 as (Hor & Htableroot).
          split;trivial.
          intros.         
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          left.
          clear IHn.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
(*             rewrite Hisancestor in *. *)
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages descParent s)).
            { apply isConfigTable with descChild;trivial.
              intuition. subst;trivial. } 
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
            {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages (currentPartition s) s)).
            apply isConfigTable with descChild;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.

            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
(** partitions are diffrent then config pages are different *)
        + assert(Hi3 : forall idx : index,
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
           unfold getTableAddrRoot.
          destruct H7 as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi4 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.
        
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagSameValue;trivial.
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert (Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
                  assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages descParent s)).
            { apply isConfigTable with shadow1;trivial.
              intuition. subst;trivial. }
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages (currentPartition s) s)).
            apply isConfigTable with shadow1;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.       
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.

        assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
        unfold isAncestor in *.
        destruct Hisancestor as [Hisancestor | Hisancestor].
        - subst currentPart .
          clear IHn.
(*           rewrite Hisancestor in *. *)
          left.
          unfold consistency in *.
          assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *.
          assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages descParent s)).
          apply isConfigTable with shadow2;trivial.
          intuition.  subst;trivial. 
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2.
        - unfold consistency in *.
          subst.
          clear IHn.
          assert(In (currentPartition s) (getPartitions multiplexer s)).
          unfold currentPartitionInPartitionsList in *.
          intuition.
          assert((currentPartition s) <> ancestor).
          { unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *. 
          assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages (currentPartition s) s)).
          apply isConfigTable with shadow2;trivial.
          intuition.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          left.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart .
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages descParent s)).
            apply isConfigTable with list;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst currentPart.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                         unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages (currentPartition s) s)).
            apply isConfigTable with list;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi4 : nextEntryIsPP currentPart sh1idx tableroot s') by intuition.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.      
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
         
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.

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
      + assert (Hfalse' : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. 
        assert((getConfigPages partition s') = 
             (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        rewrite Hconfig in *.
        assert(Hii : forall partition : page,
            In partition (getPartitions multiplexer s) -> 
            In phyDescChild (getConfigPages partition s) -> False) by trivial.
        assert(Hfalse' : In phyDescChild (getConfigPages partition s)) by trivial.
        apply Hii in Hfalse';trivial. 
      + unfold isPartitionFalse. 
         unfold s'.
         cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
         
(** Internal properties to propagate **)      
      + unfold s'.
        apply isAncestorUpdateUserFlag;trivial. 
      + destruct H.  
        unfold propagatedProperties in *.
        { assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
          apply getPartitionsUpdateUserFlag; trivial.
          rewrite Hpartions; assumption. }
       
      + apply isPEUpdateUserFlag;trivial. 
          assert(Hpe : forall idx : index,
                StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ 
                getTableAddrRoot pt PDidx descParent va s) 
          by trivial.
           apply Hpe;trivial.
      +  assert(Hroot : isPE pt (StateLib.getIndexOfAddr va fstLevel ) s /\
          getTableAddrRoot pt PDidx descParent va s).
          assert(Hpe : forall idx : index,
           StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) 
            by trivial.
          apply Hpe;trivial.
          destruct Hroot as (Hve & Hroot). 
          unfold getTableAddrRoot in *.
          destruct Hroot as (Hor & Hroot).
          split;trivial.
          intros root Hpp.
          unfold s' in Hpp.
          apply nextEntryIsPPUpdateUserFlag' in Hpp.
          apply Hroot in Hpp.
          destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
          exists nbL ; split;trivial.
          exists stop;split;trivial.
          rewrite <- Hind.
          unfold s'.
          apply getIndirectionUpdateUserFlag;trivial. 
       +  apply entryPresentFlagUpdateUserFlag;trivial. 
       + apply entryUserFlagUpdateUserFlagSameValue;trivial.
       +  apply isEntryPageUpdateUserFlag;trivial. 
       +  subst. clear IHn.       
          assert(HisAccess : isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s' =
          isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow ancestor (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt : getVirtualAddressSh2 p
                             {| currentPartition := currentPartition s;
                              memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                              (PE
                                 {|
                                 read := read entry;
                                 write := write entry;
                                 exec := exec entry;
                                 present := present entry;
                                 user := false;
                                 pa := pa entry |}) (memory s) beqPage beqIndex |} vaInAncestor =
                            getVirtualAddressSh2 p s vaInAncestor).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some L = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p vaInAncestor L (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s vaInAncestor );
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent ancestor (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
                          {|
                          currentPartition := currentPartition s;
                          memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                                      (PE
                                         {|
                                         read := read entry;
                                         write := write entry;
                                         exec := exec entry;
                                         present := present entry;
                                         user := false;
                                         pa := pa entry |}) (memory s) beqPage beqIndex |} v = 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In ancestor (getPartitions multiplexer s)).
                apply Hparentpart with descParent;trivial.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions with ancestor p0;trivial.
                unfold consistency in *.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
                        isPE ptvaInAncestor idx s /\ 
                        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                as (Hpe & Hroot);
                trivial.
                apply Hparentpart with ancestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdiff1 : p0 <> ancestor).
                              assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                              apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              assert(Hparentinpart : parentInPartitionList s) by intuition.
              unfold parentInPartitionList in *.
              apply Hparentinpart with ancestor;trivial.
              rewrite nextEntryIsPPgetParent;trivial.
              unfold not;intros Hfalsei;subst.
              now contradict Hdiff1.
              }
              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold partitionDescriptorEntry in *.
              assert(exists entry : page, nextEntryIsPP descParent PDidx entry s /\
                      entry <> defaultPage) as (pdParent & Hpp & Hnotnull).
              apply Hpde;trivial.
              left;trivial.
              clear Hpde.
              apply nextEntryIsPPgetPd in Hpp.
              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
        + assert(Heq : getAccessibleMappedPage pd s va1 = NonePage) by trivial. 
          revert Heq Hlookup.
          clear.
          intros.
          unfold getAccessibleMappedPage in *.
          destruct (StateLib.getNbLevel); trivial.
          assert(Hind : getIndirection pd va1 l (nbLevel - 1) s' =
          getIndirection pd va1 l (nbLevel - 1) s) by ( 
          apply getIndirectionUpdateUserFlag; trivial).
          rewrite Hind in *.            
          destruct (getIndirection pd va1 l (nbLevel - 1) s);trivial.
          destruct ( defaultPage =? p);trivial.
          assert(Hread :  StateLib.readPresent p (StateLib.getIndexOfAddr va1 fstLevel) (memory s')=
          StateLib.readPresent p (StateLib.getIndexOfAddr va1 fstLevel) (memory s))
          by (apply readPresentUpdateUserFlag; trivial).
          rewrite Hread in *.
          destruct (StateLib.readPresent p (StateLib.getIndexOfAddr va1 fstLevel) (memory s));
          trivial. destruct b;trivial.
          unfold StateLib.readAccessible in *.
          simpl in *. 
          case_eq( beqPairs (ptvaInAncestor, idxva) (p, StateLib.getIndexOfAddr va1 fstLevel) beqPage beqIndex);
          intros Hpairs.  
          simpl in *;trivial. 
          assert(lookup p (StateLib.getIndexOfAddr va1 fstLevel)
          (removeDup ptvaInAncestor idxva (memory s) beqPage beqIndex) beqPage beqIndex =
          lookup p (StateLib.getIndexOfAddr va1 fstLevel) (memory s) beqPage beqIndex).
          apply removeDupIdentity.
          apply beqPairsFalse in Hpairs.
          intuition.
          rewrite H.
          case_eq( match lookup p (StateLib.getIndexOfAddr va1 fstLevel) (memory s) beqPage beqIndex with
          | Some (PE a) => Some (user a)
          | Some (VE _) => None
          | Some (PP _) => None
          | Some (VA _) => None
          | Some (I _) => None
          | None => None
          end);intros; trivial.
          rewrite H0 in *.
          destruct b;trivial.
          rewrite readPhyEntryUpdateUserFlag; trivial. 
          
        + apply nextEntryIsPPUpdateUserFlag; assumption. 
        + apply isVAUpdateUserFlag; intuition.
          assert( Hisva :  forall idx : index,
                      StateLib.getIndexOfAddr va fstLevel = idx ->
                      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
                      apply Hisva; trivial. 
        + assert ( Hi : forall idx : index,
                  StateLib.getIndexOfAddr va fstLevel = idx ->
                  isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
          generalize (Hi lastIndex Hi2); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split; trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.      
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          unfold getTableAddrRoot.
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply isVA'UpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + assert(Hi :forall idx : index,
              StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
              isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) 
              by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption. 
        + assert(Hi : forall idx : index,
          StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
          isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split;trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.         
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
      (** WriteAccessible property **) 
      + unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. 
      + unfold isEntryPage.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  cbn. reflexivity.
      + unfold entryPresentFlag.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  
        cbn.
        unfold consistency in *.
        assert(Hpres : isPresentNotDefaultIff s ) by intuition.
        symmetry.
        apply phyPageIsPresent with ptvaInAncestor idxva s;trivial. }

(** setAccessible success **)
  simpl. subst. 
  (** recursion **)
  eapply weaken.
  eapply IHn.
  simpl. intros.
  assert(Hancestorpart : In ancestor (getPartitions MALInternal.multiplexer s)).
  { unfold propagatedProperties in *.
    unfold consistency in * .
    assert (Hparent : parentInPartitionList s) by intuition.
    unfold parentInPartitionList in *.
    apply Hparent with descParent; intuition. }
  assert (Hparentchild : In descParent (getChildren ancestor s)).
  unfold propagatedProperties in *.
  unfold consistency in *.
  assert(Hchildren : isChild s) by intuition.
  unfold isChild in *.
      apply Hchildren;trivial.
      intuition.
      apply nextEntryIsPPgetParent;intuition.
  assert(Hvs : verticalSharing s).
   { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. }
    unfold verticalSharing in *.
  assert(Hvsall : incl (getUsedPages descParent s) (getMappedPages ancestor s)).
  apply Hvs;trivial.
  clear Hvs.
  apply verticalSharing2 in Hvsall.
  unfold incl in *.
  generalize(Hvsall phypage);clear Hvsall; intros Hvs.
  assert(Hdescpage : In phypage (getMappedPages descParent s)).
  { intuition.
    subst.
    assert(Hpde : partitionDescriptorEntry s).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. } 
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP descParent PDidx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    left;trivial.
    destruct Hentrypd as (pdParent & Hpp & Hnotnul).
    apply inGetMappedPagesGetTableRoot with va pt pdParent ;trivial.
}

apply Hvs in Hdescpage.
clear Hvs.
unfold getMappedPages in *.
assert(HpdAncestor : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
rewrite nextEntryIsPPgetPd in *.
rewrite HpdAncestor in *.
unfold getMappedPagesAux in *.
apply filterOptionInIff in Hdescpage.
unfold getMappedPagesOption in *.
apply in_map_iff in Hdescpage.
destruct Hdescpage as (newVA & Hmapped & Hinvas).
unfold getMappedPage in Hmapped.
assert(Hlevel : Some L = StateLib.getNbLevel) by intuition.
rewrite <- Hlevel in *.
case_eq(getIndirection pdAncestor newVA L (nbLevel - 1) s);[intros ptAncestor HptAncestor |
intros HptAncestor];rewrite HptAncestor in *;try now contradict Hmapped.
case_eq(defaultPage =? ptAncestor);intros Hb;rewrite Hb in *;try now contradict Hmapped.
case_eq(StateLib.readPresent ptAncestor (StateLib.getIndexOfAddr newVA fstLevel) (memory s));
[intros present Hpresent |
intros Hpresent];rewrite Hpresent in *;try now contradict Hmapped.

 destruct present;[| inversion Hmapped;subst;
 rewrite isNotDefaultPageFalse in Hnotdef;
 now contradict Hnotdef]. 
(* assert(vaInAncestor = newVA).
{ destruct H as (((((Ha & Hk )& Hi ) & Hj ) & Hl ) & Hm).
  intuition.
  clear IHn.
  subst.
  apply eqMappedPagesEqVaddrs with phypage pdAncestor s;trivial.
  apply getMappedPageGetTableRoot with ptvaInAncestor ancestor;trivial.
  rewrite nextEntryIsPPgetPd in *;trivial.
  apply AllVAddrAll.
  apply getMappedPageGetIndirection with ancestor ptAncestor L;trivial.
    rewrite nextEntryIsPPgetPd in *;trivial.
  assert (Hnodupmapped : noDupMappedPagesList s).
  unfold consistency in *;intuition.
  unfold noDupMappedPagesList in *.
  assert(Hnewnodup : NoDup (getMappedPages ancestor s)).
  apply Hnodupmapped;trivial.
  unfold getMappedPages in Hnewnodup.
  rewrite HpdAncestor in *.
  unfold getMappedPagesAux  in *.
  assumption. } *)
instantiate(1:= phypage).
instantiate (1:= StateLib.getIndexOfAddr vaInAncestor fstLevel).
instantiate (1:= ptvaInAncestor).

  split.
 intuition.
 split.
 assert(Hisancestor : isAncestor currentPart descParent s) by intuition.
 rewrite nextEntryIsPPgetParent in *.
unfold consistency in *. 
unfold  propagatedProperties in *.
  unfold consistency in *.
apply isAncestorTrans with descParent;intuition.
unfold propagatedProperties in *. 
             unfold consistency in *. intuition.
             unfold consistency in *. intuition.
            unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition.    
intuition.
 intuition.
 subst;trivial.
   subst;trivial.
  subst;trivial. }
 

(** setAccessible failed **)
 intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition.
Qed. 

Lemma WriteAccessibleRec accessibleChild accessibleSh1 accessibleSh2 accessibleList 
descParent va  pt (phypage : page) idxvaparent pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild: 
{{  fun s : state =>
 propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
 pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s /\
 
isAncestor  currentPart descParent s /\
 ( In descParent (getPartitions MALInternal.multiplexer s)  /\
     (defaultPage =? phypage) = false /\
    (forall idx : index,
StateLib.getIndexOfAddr va fstLevel = idx ->
isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) /\
(defaultPage =? pt) = false /\
StateLib.getIndexOfAddr va fstLevel = idxvaparent /\
entryPresentFlag pt idxvaparent true s /\
entryUserFlag pt idxvaparent false s /\
    isEntryPage pt idxvaparent phypage s /\
    isAccessibleMappedPageInParent descParent va phypage s = true )
    }} 
  Internal.writeAccessibleRecAux (nbPage+1) va descParent false {{
    fun _ s  =>
     propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
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
revert va descParent  pt phypage idxvaparent .
induction  (nbPage+1) .
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
                  destruct Hcurpart as ( Hancestors & Hcurpart & Hnewprops).
                  clear Hancestors. 
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
  2:{
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
  } (** comparePageToNull **) 
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
  destruct H as 
  ((((((((Hprops & Hi ) & Hcurpart)& Hmult) & Hnotmult) & Hsh2root) & HnblL)
           & Hidxaddr) & H).
           
  destruct Hi as (  _ & Hnewprops).
 intuition.
  subst.
  apply beq_nat_false in H.
  now contradict H.
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
  intros pdAncestor. (* 
  unfold setAccessible.
  simpl.
  eapply bindRev.
(** setAccessible **)
  unfold setAccessible.
  { *) eapply bindRev.
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
    case_eq (isdefaultVA).
    -  intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition. 
    - intros isdefaultVAT.
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
      assert(Hcons : consistency s) by intuition.
      unfold consistency in *.
      destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent & _ & _).
      unfold parentInPartitionList in *. 
      instantiate (2:= ancestor).
      split.
      apply Hparent with descParent; intuition.
       
      instantiate (1:= PDidx).
      split. intuition.
      exists pdAncestor.
      split. intuition.
      split. 
      unfold consistency in *.
(*       destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent).  *)
      unfold partitionDescriptorEntry in Hpd.
      unfold parentInPartitionList in *.
      subst.
      assert(Hpartancestor : In ancestor (getPartitions MALInternal.multiplexer s)).
      {       apply Hparent with descParent; intuition. } 
      generalize (Hpd ancestor Hpartancestor); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/PDidx = sh3idx
              \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
            by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hancesnotnull).
      subst.
      assert (Hrootances : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup ancestor i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootances |
        now contradict Hrootances | 
       subst ; assumption| now contradict Hrootances| now contradict Hrootances ]  
       |now contradict Hrootances] | now contradict Hrootances].
      subst. left. split;intuition.
      intro ptvaInAncestor. simpl.
       (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2:{
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
      do  15 (* 6 *) rewrite <- and_assoc in H0.
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
  } (** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptvaInAncestorIsnull. simpl.
      case_eq ptvaInAncestorIsnull.
      2:{
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
      simpl.
      eapply bindRev; simpl;[|intros []].
      (** writeAccessible **)
      eapply WP.weaken.
      eapply WP.writeAccessible.
      intros. simpl.
      assert (exists entry0 : Pentry,
        lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry0)) as Hlookup.
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
      do 9 rewrite <- and_assoc in H.
      destruct H as (Hsplit & Hfalse & Hrest).
      assert(Heqphy : phypage = pa entry).
      {    destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
         intuition. subst.
        unfold isAccessibleMappedPageInParent in *.
        assert (HgetVirt : getVirtualAddressSh2 sh2 s va  = Some vaInAncestor).
        apply isVaInParent with descParent ptsh2;trivial.
        apply nextEntryIsPPgetSndShadow in Hppsh2.
        rewrite Hppsh2 in *.
        rewrite HgetVirt in *.
        rewrite nextEntryIsPPgetParent in * .
        rewrite Hppparent in *. 
        apply nextEntryIsPPgetPd in Hpppd .
        rewrite Hpppd in *.
        case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor);
        intros * Hacce;
        rewrite Hacce in *;try now contradict Hfalse.
        unfold getAccessibleMappedPage in Hacce.
        assert( isPE ptvaInAncestor  (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) as (Hve & Hroot ).
        apply Hgetroot2;trivial.
        unfold getTableAddrRoot in *.
        destruct Hroot as (_ & Hroot).
        rewrite <- nextEntryIsPPgetPd in *.
        apply Hroot in  Hpppd.
        clear Hroot.
        destruct Hpppd as (nbL & HnbL & stop & Hstop & Hind).
        subst.
        rewrite <- HnbL in *.
        assert(Hgetind : getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s  
        = Some ptvaInAncestor).
        apply getIndirectionStopLevelGT2 with (nbL+1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind in *.
        rewrite H in *.
        destruct ( StateLib.readPresent ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s));try now contradict Hacce.
        destruct b;try now contradict Hacce.
        destruct ( StateLib.readAccessible ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s)); try now contradict Hacce.
        destruct b; try now contradict Hacce.
        unfold StateLib.readPhyEntry in *. 
        rewrite Hlookup in *.
        apply beq_nat_true in Hfalse.
        inversion Hacce.
        subst.
        destruct phypage; destruct (pa entry).
        simpl in *.
        subst.
        f_equal; apply proof_irrelevance. }
      assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true).
      { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        rewrite Heqphy.
        destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
        apply isAccessibleMappedPageInParentTrue with descParent va phypage ptvaInAncestor ptsh2 pdAncestor;
        subst;intuition.
        subst;assumption. }
      repeat rewrite and_assoc in Hsplit.
      destruct Hsplit as (Hprops & Hsplit).
(*       unfold propagatedProperties in *.
      do 73 rewrite <- and_assoc in Hprops.
      destruct Hprops as (Hprops & xx & Hprops2). 
            repeat rewrite and_assoc in Hprops. *)
      assert (Hnewprops := conj  Hprops  Hsplit).
      assert (H := conj (conj Hnewprops Htrue) Hrest).
      simpl.
      clear Hnewprops.
    (*   repeat rewrite and_assoc in H. *)
      pattern s in H.
      match type of H with 
      | ?HT s => instantiate (1 := fun tt s => HT s  /\ 
                  entryUserFlag ptvaInAncestor idxva false s /\
                  isEntryPage ptvaInAncestor idxva phypage s /\
                  entryPresentFlag ptvaInAncestor idxva true s  ) 
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
      simpl.
      unfold propagatedProperties in *. 
      do 7 rewrite and_assoc.
      clear Hrest  Hsplit  Hprops.
      split.
      
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
      split.
      (** partitionDescriptorEntry **)
      apply partitionDescriptorEntryUpdateUserFlag;trivial.
      intuition.
      (** dataStructurePdSh1Sh2asRoot **)
      destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
      Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      (** currentPartitionInPartitionsList **)
      split.
      unfold currentPartitionInPartitionsList in *.
      simpl in *. subst. 
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite Hpartions. assumption.
      (** noDupMappedPagesList **)  
      split.    
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
      split.
      (** noDupConfigPagesList **)
      apply getIndirectionsNoDupUpdateUserFlag; trivial.
      split.
      (** parentInPartitionList **)
      unfold parentInPartitionList in *.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart.
      intros partition HgetParts parent Hroot.
      generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
      apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
      apply Hparent; trivial.
      split.
      (** accessibleVAIsNotPartitionDescriptor **)
     unfold s'.
      subst.
      clear IHn.
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (_ & Hi).
      intuition.
      subst.
      apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag  with level ancestor   
        pdAncestor;trivial.
      assert(Hparentpart : parentInPartitionList s) by trivial.
      unfold parentInPartitionList in *.
      apply Hparent with descParent;trivial. 
       assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
      assert(  isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s ) as (_ & Hroot).
      apply Hget;split;trivial.
      assumption.
      apply nextEntryIsPPgetPd;trivial.
      subst.
      assert(HaccessInParent : isAccessibleMappedPageInParent descParent va (pa entry) s = true)
       by trivial.
       unfold isAccessibleMappedPageInParent in HaccessInParent.
       (** Here we use the property already present into the precondition : 
            *)
       assert(Hcursh2 : nextEntryIsPP descParent sh2idx sh2 s ) by trivial.
      apply nextEntryIsPPgetSndShadow in Hcursh2.
      rewrite Hcursh2 in HaccessInParent.
      assert(Hvainparent : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
      { assert(Hxx : forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx ->
        isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
        assert(Hgetva : isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\ 
        getTableAddrRoot ptsh2 sh2idx descParent va s).
        apply Hxx;trivial. clear Hxx.
        destruct Hgetva as (Hva & Hgetva).
        assert(Hisva : isVA' ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s) 
        by trivial.
        unfold getVirtualAddressSh2.
        unfold getTableAddrRoot in Hgetva.
        destruct Hgetva as (_ & Hgetva).
        assert(HcurSh2 : nextEntryIsPP descParent sh2idx sh2 s).
        rewrite  nextEntryIsPPgetSndShadow ;trivial.
        apply Hgetva in HcurSh2.
        destruct HcurSh2 as (nbL & HnbL & stop & Hstop & Hind).
        rewrite <- HnbL.
        subst.
        assert(Hgetind : getIndirection sh2 va nbL (nbLevel - 1) s = Some ptsh2).
        apply getIndirectionStopLevelGT2 with (nbL + 1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind.
        assert (Hptnotnull : (defaultPage =? ptsh2) = false) by trivial.
        rewrite Hptnotnull.
        unfold  isVA' in *. 
        unfold StateLib.readVirtual. 
        destruct(lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ); 
        try now contradict Hisva.
        destruct v;try now contradict Hisva.
        subst. trivial. }
      rewrite Hvainparent in *.
      assert(Hgetparent : StateLib.getParent descParent (memory s) = Some ancestor).
      { apply nextEntryIsPPgetParent;trivial. }
      rewrite Hgetparent in *.
      assert(Hgetpdparent : StateLib.getPd ancestor (memory s) = Some pdAncestor).
      { apply nextEntryIsPPgetPd;trivial. }
      rewrite Hgetpdparent in *.
      case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor ); intros * Hi .
      rewrite Hi in *.
      unfold getAccessibleMappedPage in Hi.
      case_eq (StateLib.getNbLevel);intros * Hi2 ; rewrite Hi2 in *;
       try now contradict Hi.
      assert(Hancestor : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by 
      trivial.
      assert(Hget : isPE ptvaInAncestor ( StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\
            getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s).
      apply Hancestor; clear Hancestor;
      trivial.
      destruct Hget as (Hva & Hget).
      unfold getTableAddrRoot in Hget.
      destruct Hget as (_ & Hget).
      apply nextEntryIsPPgetPd in Hgetpdparent.
      apply Hget in Hgetpdparent.
      destruct Hgetpdparent as (nbL & HnbL & stop & Hstop & Hgettable).
      clear Hget.
      rewrite <- HnbL in *.
      inversion Hi2.
      subst.
      assert(Hind :getIndirection pdAncestor vaInAncestor l (nbLevel - 1) s = Some ptvaInAncestor).
      apply getIndirectionStopLevelGT2 with (l+1);trivial.
      omega.
      apply getNbLevelEq in HnbL.
      rewrite HnbL.
      unfold CLevel.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      simpl;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      rewrite Hind in *.
      assert (Hnotnull : (defaultPage =? ptvaInAncestor) = false) by trivial.
      rewrite Hnotnull in *.
      destruct (StateLib.readPresent ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b; try now contradict Hi.
      destruct(StateLib.readAccessible ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b.
      unfold StateLib.readPhyEntry in *.
      rewrite Hlookup in *.
      symmetry; assumption.
      now contradict Hi.
      rewrite Hi in *. 
      now contradict HaccessInParent.      rewrite Hi in *. 
      now contradict HaccessInParent.
      
   (* accessibleChildPageIsAccessibleIntoParent *)
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (Hancestor & Hi).
      unfold s'.
      intuition. 
      subst.
      clear IHn.
      apply accessibleChildPageIsAccessibleIntoParentUpdateUserFlagFlase
      with level ancestor pdAncestor va ptsh2 descParent pt;trivial.
      assert(Hparentpart : parentInPartitionList s).
      unfold consistency in *; intuition.
      unfold parentInPartitionList in *.
      apply Hparentpart with descParent;trivial.
      (* noCycleInPartitionTree *)
      assert(Hdiff : noCycleInPartitionTree s) by trivial.
      unfold noCycleInPartitionTree in *.
      intros parent partition Hparts Hparentpart.
      simpl in *.
      assert (getPartitions multiplexer {|
              currentPartition := currentPartition s;
              memory := add ptvaInAncestor idxva
                          (PE
                             {|
                             read := read entry;
                             write := write entry;
                             exec := exec entry;
                             present := present entry;
                             user := false;
                             pa := pa entry |}) (memory s) beqPage beqIndex |}
               = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(HgetParent : getAncestors partition
                {|
                   currentPartition := currentPartition s;
                   memory := add ptvaInAncestor idxva
                               (PE
                                  {|
                                  read := read entry;
                                  write := write entry;
                                  exec := exec entry;
                                  present := present entry;
                                  user := false;
                                  pa := pa entry |}) (memory s) beqPage beqIndex |} = 
                      getAncestors partition  s).
      apply getAncestorsUpdateUserFlag;trivial.
      rewrite HgetParent in *; clear HgetParent.
      apply Hdiff;trivial.
      (* configTablesAreDifferent *)
      assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
      unfold configTablesAreDifferent in *.
      simpl in *.
      fold s'.
      intros partition1 partition2 Hpart1 Hpart2 Hdiff.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      apply Hconfigdiff;trivial.
      rename H into Hcond.
      (** isChild **)
      assert(Hchid : isChild s) by intuition.
      unfold isChild in *.
      simpl in *.
      intros partition parent Hparts Hgetparent.
      rewrite getPartitionsUpdateUserFlag in *;trivial.
      rewrite getParentUpdateUserFlag in *;trivial.
      rewrite getChildrenUpdateFlagUser;trivial.
      apply Hchid;trivial.
          (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    (** physicalPageNotDerived **)
    apply physicalPageNotDerivedUpdateUserFlag;trivial.
    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by trivial.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.  
    (** isParent  *)
    assert(Hisparent : isParent s) by trivial.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by trivial.
    unfold noDupPartitionTree in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by trivial.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va0 = Some vainparent).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by trivial.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh0 s va0 = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    apply getVirtualAddressSh2UpdateUserFlag;trivial.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by trivial.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by trivial.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.
  (** Propagated properties **)
      assert(Hi2 : StateLib.getIndexOfAddr va fstLevel = lastIndex) by intuition.
      {  intuition trivial. 
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
          unfold getTableAddrRoot.
          destruct H23 as (Hor & Htableroot).
          split;trivial.
          intros.         
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          left.
          clear IHn.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
(*             rewrite Hisancestor in *. *)
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages descParent s)).
            apply isConfigTable with descChild;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
            {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                                     unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages (currentPartition s) s)).
            apply isConfigTable with descChild;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
(** partitions are diffrent then config pages are different *)
        + assert(Hi3 : forall idx : index,
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
           unfold getTableAddrRoot.
          destruct H7 as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi4 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.
        
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagSameValue;trivial.
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert (Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
                  assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages descParent s)).
            apply isConfigTable with shadow1;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition. 
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                                     unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages (currentPartition s) s)).
            apply isConfigTable with shadow1;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.       
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.

        assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
        unfold isAncestor in *.
        destruct Hisancestor as [Hisancestor | Hisancestor].
        - subst currentPart.
          clear IHn.
(*           rewrite Hisancestor in *. *)
          left.
          unfold consistency in *.
          assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *.
          assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages descParent s)).
          apply isConfigTable with shadow2;trivial.
          intuition. subst;trivial.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2.
        - unfold consistency in *.
          subst.
          clear IHn.
          assert(In (currentPartition s) (getPartitions multiplexer s)).
          unfold currentPartitionInPartitionsList in *.
          intuition.
          assert((currentPartition s) <> ancestor).
          { unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                                     unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *. 
          assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages (currentPartition s) s)).
          apply isConfigTable with shadow2;trivial.
          intuition.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          left.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages descParent s)).
            apply isConfigTable with list;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                                     unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages (currentPartition s) s)).
            apply isConfigTable with list;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi4 : nextEntryIsPP currentPart sh1idx tableroot s') by intuition.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.      
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
         
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.

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
      + assert (Hfalse' : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. 
        assert((getConfigPages partition s') = 
             (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        rewrite Hconfig in *.
        assert(Hii : forall partition : page,
            In partition (getPartitions multiplexer s) -> 
            In phyDescChild (getConfigPages partition s) -> False) by trivial.
        assert(Hfalse' : In phyDescChild (getConfigPages partition s)) by trivial.
        apply Hii in Hfalse';trivial. 
      + unfold isPartitionFalse. 
         unfold s'.
         cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
         
(** Internal properties to propagate **)      
      + unfold s'.
        apply isAncestorUpdateUserFlag;trivial. 
      + destruct H.  
        unfold propagatedProperties in *.
        { assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
          apply getPartitionsUpdateUserFlag; trivial.
          rewrite Hpartions; assumption. }
       
      + apply isPEUpdateUserFlag;trivial. 
          assert(Hpe : forall idx : index,
                StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ 
                getTableAddrRoot pt PDidx descParent va s) 
          by trivial.
           apply Hpe;trivial.
      +  assert(Hroot : isPE pt (StateLib.getIndexOfAddr va fstLevel ) s /\
          getTableAddrRoot pt PDidx descParent va s).
          assert(Hpe : forall idx : index,
           StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) 
            by trivial.
          apply Hpe;trivial.
          destruct Hroot as (Hve & Hroot). 
          unfold getTableAddrRoot in *.
          destruct Hroot as (Hor & Hroot).
          split;trivial.
          intros root Hpp.
          unfold s' in Hpp.
          apply nextEntryIsPPUpdateUserFlag' in Hpp.
          apply Hroot in Hpp.
          destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
          exists nbL ; split;trivial.
          exists stop;split;trivial.
          rewrite <- Hind.
          unfold s'.
          apply getIndirectionUpdateUserFlag;trivial. 
       +  apply entryPresentFlagUpdateUserFlag;trivial. 
       + apply entryUserFlagUpdateUserFlagSameValue;trivial.
       +  apply isEntryPageUpdateUserFlag;trivial. 
       +  subst. clear IHn.       
          assert(HisAccess : isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s' =
          isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow ancestor (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt : getVirtualAddressSh2 p
                             {| currentPartition := currentPartition s;
                              memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                              (PE
                                 {|
                                 read := read entry;
                                 write := write entry;
                                 exec := exec entry;
                                 present := present entry;
                                 user := false;
                                 pa := pa entry |}) (memory s) beqPage beqIndex |} vaInAncestor =
                            getVirtualAddressSh2 p s vaInAncestor).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some L = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p vaInAncestor L (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s vaInAncestor );
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent ancestor (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
                          {|
                          currentPartition := currentPartition s;
                          memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                                      (PE
                                         {|
                                         read := read entry;
                                         write := write entry;
                                         exec := exec entry;
                                         present := present entry;
                                         user := false;
                                         pa := pa entry |}) (memory s) beqPage beqIndex |} v = 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In ancestor (getPartitions multiplexer s)).
                apply Hparentpart with descParent;trivial.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions with ancestor p0;trivial.
                unfold consistency in *.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
                        isPE ptvaInAncestor idx s /\ 
                        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                as (Hpe & Hroot);
                trivial.
                apply Hparentpart with ancestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdiff1 : p0 <> ancestor).
                              assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                              apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              assert(Hparentinpart : parentInPartitionList s) by intuition.
              unfold parentInPartitionList in *.
              apply Hparentinpart with ancestor;trivial.
              rewrite nextEntryIsPPgetParent;trivial.
              unfold not;intros Hfalsei;subst.
              now contradict Hdiff1.
              }
              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold partitionDescriptorEntry in *.
              assert(exists entry : page, nextEntryIsPP descParent PDidx entry s /\
                      entry <> defaultPage) as (pdParent & Hpp & Hnotnull).
              apply Hpde;trivial.
              left;trivial.
              clear Hpde.
              apply nextEntryIsPPgetPd in Hpp.
              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
        + apply nextEntryIsPPUpdateUserFlag; assumption. 
        + apply isVAUpdateUserFlag; intuition.
          assert( Hisva :  forall idx : index,
                      StateLib.getIndexOfAddr va fstLevel = idx ->
                      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
                      apply Hisva; trivial. 
        + assert ( Hi : forall idx : index,
                  StateLib.getIndexOfAddr va fstLevel = idx ->
                  isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
          generalize (Hi lastIndex Hi2); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split; trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.      
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          unfold getTableAddrRoot.
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply isVA'UpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + assert(Hi :forall idx : index,
              StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
              isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) 
              by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption. 
        + assert(Hi : forall idx : index,
          StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
          isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split;trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.         
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
      (** WriteAccessible property **) 
      + unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. 
      + unfold isEntryPage.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  cbn. reflexivity.
      + unfold entryPresentFlag.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  
        cbn.
        unfold consistency in *.
        assert(Hpres : isPresentNotDefaultIff s ) by intuition.
        symmetry.
        apply phyPageIsPresent with ptvaInAncestor idxva s;trivial. }

(** setAccessible success **)
  simpl. subst. 
  (** recursion **)
  eapply weaken.
  eapply IHn.
  simpl. intros.
  assert(Hancestorpart : In ancestor (getPartitions MALInternal.multiplexer s)).
  { unfold propagatedProperties in *.
    unfold consistency in * .
    assert (Hparent : parentInPartitionList s) by intuition.
    unfold parentInPartitionList in *.
    apply Hparent with descParent; intuition. }
  assert (Hparentchild : In descParent (getChildren ancestor s)).
  unfold propagatedProperties in *.
  unfold consistency in *.
  assert(Hchildren : isChild s) by intuition.
  unfold isChild in *.
      apply Hchildren;trivial.
      intuition.
      apply nextEntryIsPPgetParent;intuition.
  assert(Hvs : verticalSharing s).
   { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. }
    unfold verticalSharing in *.
  assert(Hvsall : incl (getUsedPages descParent s) (getMappedPages ancestor s)).
  apply Hvs;trivial.
  clear Hvs.
  apply verticalSharing2 in Hvsall.
  unfold incl in *.
  generalize(Hvsall phypage);clear Hvsall; intros Hvs.
  assert(Hdescpage : In phypage (getMappedPages descParent s)).
  { intuition.
    subst.
    assert(Hpde : partitionDescriptorEntry s).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. } 
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP descParent PDidx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    left;trivial.
    destruct Hentrypd as (pdParent & Hpp & Hnotnul).
    apply inGetMappedPagesGetTableRoot with va pt pdParent ;trivial.
  
}

apply Hvs in Hdescpage.
clear Hvs.
unfold getMappedPages in *.
assert(HpdAncestor : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
rewrite nextEntryIsPPgetPd in *.
rewrite HpdAncestor in *.
unfold getMappedPagesAux in *.

apply filterOptionInIff in Hdescpage.
unfold getMappedPagesOption in *.
apply in_map_iff in Hdescpage.
destruct Hdescpage as (newVA & Hmapped & Hinvas).
unfold getMappedPage in Hmapped.
assert(Hlevel : Some L = StateLib.getNbLevel) by intuition.
rewrite <- Hlevel in *.
case_eq(getIndirection pdAncestor newVA L (nbLevel - 1) s);[intros ptAncestor HptAncestor |
intros HptAncestor];rewrite HptAncestor in *;try now contradict Hmapped.
case_eq(defaultPage =? ptAncestor);intros Hb;rewrite Hb in *;try now contradict Hmapped.
case_eq(StateLib.readPresent ptAncestor (StateLib.getIndexOfAddr newVA fstLevel) (memory s));
[intros present Hpresent |
intros Hpresent];rewrite Hpresent in *;try now contradict Hmapped.

destruct present;[| inversion Hmapped;subst;
 rewrite isNotDefaultPageFalse in Hnotdef;
 now contradict Hnotdef].
(* assert(vaInAncestor = newVA).
{ destruct H as (((((Ha & Hk )& Hi ) & Hj ) & Hl ) & Hm).
  intuition.
  clear IHn.
  subst.
  apply eqMappedPagesEqVaddrs with phypage pdAncestor s;trivial.
  apply getMappedPageGetTableRoot with ptvaInAncestor ancestor;trivial.
  rewrite nextEntryIsPPgetPd in *;trivial.
  apply AllVAddrAll.
  apply getMappedPageGetIndirection with ancestor ptAncestor L;trivial.
    rewrite nextEntryIsPPgetPd in *;trivial.
  assert (Hnodupmapped : noDupMappedPagesList s).
  unfold consistency in *;intuition.
  unfold noDupMappedPagesList in *.
  assert(Hnewnodup : NoDup (getMappedPages ancestor s)).
  apply Hnodupmapped;trivial.
  unfold getMappedPages in Hnewnodup.
  rewrite HpdAncestor in *.
  unfold getMappedPagesAux  in *.
  assumption. } *)
instantiate(1:= phypage).
instantiate (1:= StateLib.getIndexOfAddr vaInAncestor fstLevel).
instantiate (1:= ptvaInAncestor).

  split.
 intuition.
 split.
 assert(Hisancestor : isAncestor currentPart descParent s) by intuition.
 rewrite nextEntryIsPPgetParent in *.

unfold propagatedProperties in *. unfold consistency in *.  apply isAncestorTrans with descParent;intuition. 
     unfold consistency in *. intuition.
            unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition.   
intuition.
 intuition.
 subst;trivial.
   subst;trivial.
  subst;trivial. }
 

(** setAccessible failed **)
 intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition.
Qed.



 Lemma pdPartNotNull' phyDescChild pdChildphy s:
In phyDescChild (getPartitions multiplexer s) -> 
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
partitionDescriptorEntry s -> 
(defaultPage =? pdChildphy) = false.
Proof.
intros. 
 unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP phyDescChild PDidx entry s /\ entry <> defaultPage)).
        apply H1;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pdChildphy).
apply getPdNextEntryIsPPEq  with phyDescChild s;trivial.
apply nextEntryIsPPgetPd;trivial.
subst;trivial.
apply Nat.eqb_neq.
symmetrynot.
unfold not;intros.
apply Hnotnull.
destruct pdChildphy;simpl in *.
destruct defaultPage;simpl in *.
subst.

f_equal.
trivial.
apply proof_irrelevance.
Qed.

Lemma WriteAccessibleRecPostCondition accessibleChild accessibleSh1 accessibleSh2 accessibleList 
descParent va  pt (phypage : page) idxvaparent pdChild currentPart currentPD level 
ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild: 
{{  fun s : state =>
 propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
 pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s /\
 
isAncestor  currentPart descParent s /\
 ( In descParent (getPartitions MALInternal.multiplexer s)  /\
     (defaultPage =? phypage) = false /\
    (forall idx : index,
StateLib.getIndexOfAddr va fstLevel = idx ->
isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) /\
(defaultPage =? pt) = false /\
StateLib.getIndexOfAddr va fstLevel = idxvaparent /\
entryPresentFlag pt idxvaparent true s /\
entryUserFlag pt idxvaparent false s /\
    isEntryPage pt idxvaparent phypage s /\
    isAccessibleMappedPageInParent descParent va phypage s = true ) (* /\
    nextEntryIsPP currentPart PPRidx descParent s *)
    }} 
  Internal.writeAccessibleRecAux (nbPage +1) va descParent false {{
    fun res  s  =>forall partition,
    In partition (getAncestors descParent s)-> 
    ~In phypage (getAccessibleMappedPages partition s) }}.
Proof.
 revert va descParent  pt phypage idxvaparent .
 unfold getAncestors.
induction (nbPage + 1).
intros;simpl.
eapply weaken.
eapply WP.ret. simpl.
intuition.  
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
  unfold not; intros Hfalse.
  intuition subst.
  assert(Hmult :  StateLib.getParent descParent (memory s) = None). 
  { unfold StateLib.Page.eqb in *.
    assert(Hismult : true = (descParent =? multiplexer)) by trivial.
  symmetry in Hismult.
  apply  beq_nat_true in Hismult.
  unfold propagatedProperties in *.
   
  unfold consistency in *.
  
  assert(Hmultcons : multiplexerWithoutParent s) by intuition.
  revert Hismult Hmultcons.
  clear.
  intros.
  unfold multiplexerWithoutParent in *.
  rewrite <- Hmultcons.
  f_equal.
  destruct  descParent; destruct multiplexer.
  simpl in *.
  subst.
  f_equal.
  apply proof_irrelevance.  }
  rewrite Hmult in *.
  now contradict H0.
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
  eapply GetTableAddr.getTableAddr with (currentPart:= descParent) (idxroot:= sh2idx).
  simpl. 
  intros.
  split.
  pattern s in H.
  eapply H.
  split.
  unfold propagatedProperties in *.
  intuition.
  split.
  intuition.
  split. 
  intuition.
  exists sh2.
  split.
  intuition.
  split.
  apply sh2PartNotNull with descParent s;intuition.
  unfold propagatedProperties in *; unfold consistency in *;intuition.  
  left; split; intuition.
  intros ptsh2. simpl.  
   (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2:{
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
        apply idxSh2idxSh1notEq.
      - assumption.
      - contradict Hfalse.
        symmetrynot.
        apply idxPDidxSh2notEq.
      - assumption.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP.
  } (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptsh2Isnull. simpl.
  case_eq ptsh2Isnull.
  intros.
  eapply WP.weaken.
  eapply WP.ret .
  simpl. intros.
  assert(Hptsh2NotNulltrue : (defaultPage =? ptsh2) = false ).
 { assert(Hwellformed :wellFormedShadows sh2idx s).
    unfold propagatedProperties in *.
    unfold consistency in *.
    intuition.
    unfold wellFormedShadows in Hwellformed.
  assert(Hpde : partitionDescriptorEntry s). 
            { unfold propagatedProperties in *.
              unfold consistency in *.
              intuition. }
      assert(Hpdedesc : (exists entry : page,
            nextEntryIsPP descParent PDidx entry s /\ entry <> defaultPage)).
      { 
      apply Hpde;trivial.
      intuition.
      left;trivial. }
      destruct Hpdedesc as (pdparent & Hentry1 & Hentry2).
  assert(Hmult : multiplexer = MALInternal.multiplexer ) by intuition.
      subst.
  assert(Htrue : getIndirection sh2 va level (nbLevel -1) s = Some ptsh2 /\
              (defaultPage =? ptsh2) = false).
  assert(Hexist : exists indirection2 : page,
                getIndirection sh2 va level (nbLevel - 1) s = Some indirection2 /\
                (defaultPage =? indirection2) = false). 
  apply Hwellformed with descParent pdparent pt;trivial. 
  + intuition.      
  + assert( false = StateLib.Page.eqb descParent multiplexer) as Hnotmul by 
               intuition.
      unfold StateLib.Page.eqb in *.
      unfold not;intros ; subst.
      symmetry in Hnotmul.
      apply beq_nat_false in Hnotmul.
      apply nextEntryIsPPgetPd;trivial.
  + intuition.
  + unfold propagatedProperties in *.
    intuition.
  + 
    apply getIndirectionGetTableRoot1 with descParent; trivial.
     
      apply nextEntryIsPPgetPd;intuition.
      unfold propagatedProperties in *.
    intuition.
    intuition.
  + intuition.
  + destruct Hexist as (indirection2 & Hin1 & Hin2).
  assert(getIndirection sh2 va level (nbLevel - 1) s = Some ptsh2).
  { 
   (* 
    assert( ptsh2 = indirection2). *)
    assert((getTableAddrRoot' ptsh2 sh2idx descParent va s /\ ptsh2 = defaultPage \/
       (forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx ->
        isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s))
         /\  (defaultPage =? ptsh2) = true
        /\ nextEntryIsPP descParent sh2idx sh2 s) by intuition.
   assert(Hlevel  : Some level = StateLib.getNbLevel ). { unfold propagatedProperties in *.
   intuition. }
  clear H0.
  
  intuition.
  ++
  subst. 

  unfold getTableAddrRoot' in *.
  assert(exists nbL : ADT.level,
        Some nbL = StateLib.getNbLevel /\
        (exists stop : nat,
           stop > 0 /\ stop <= nbL /\ getIndirection sh2 va nbL stop s = Some defaultPage)).
           apply H0. 
     intuition.
     destruct H2 as (l & Hl & stop & Hstop1 & Hstop2 & Hind).
     rewrite <- Hl in Hlevel.
     inversion Hlevel.
     subst l.
       apply getIndirectionNbLevelEq with stop;trivial.
       apply getNbLevelEq in Hl.
       subst. apply nbLevelEq.
   ++ (* destruct H2 with (StateLib.getIndexOfAddr va fstLevel  ) as (_ & Hi); *)
   trivial. 




   apply getIndirectionGetTableRoot2 with descParent;trivial.
   apply nextEntryIsPPgetSndShadow;trivial.
   intuition.  }
  split;trivial.
  rewrite  H in Hin1.
  inversion Hin1;subst indirection2;trivial.
  + intuition. }
  
  
  
  unfold propagatedProperties in *. 
  (** New consistency property sh2 data structure is well-formed : there is a table into the sh2 structure *)
  intuition subst.
  apply beq_nat_false in Hptsh2NotNulltrue.
  now contradict Hptsh2NotNulltrue. 
  rewrite Hptsh2NotNulltrue in *.
  intuition.
  intros Hptsh2NotNull.
  (** readVirtual **)
  eapply bindRev. 
  eapply weaken.
  2: {  
  intros.
  destruct H as ((H & Hstrong) & Htrue).
  assert(Heqv:  (isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\ getTableAddrRoot ptsh2 sh2idx descParent va s)).
  { destruct Hstrong as [Hor|Hor].   
    assert(Hfalse: (defaultPage =? defaultPage) = false) by (intuition;subst;trivial).
    apply beq_nat_false in Hfalse.
    now contradict Hfalse.
    destruct Hor with (StateLib.getIndexOfAddr va fstLevel);trivial.
    intuition; subst;trivial.
 }
  clear Hstrong.
  assert (Hnew:= conj (conj H Heqv) Htrue).
  eapply Hnew. }
  eapply weaken.
  eapply Invariants.readVirtual.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
  subst.
  intuition;
  subst;trivial.
  intros vaInAncestor.
  simpl.
  subst.
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
  assert (Hparent:  parentInPartitionList s) by (unfold consistency in *;  intuition).
  unfold parentInPartitionList in *.
  apply Hparent with descParent; intuition.
  intros pdAncestor. 
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
    case_eq (isdefaultVA).
    - intros.
      eapply weaken.
      eapply WP.ret.
      simpl. intros.
      subst.
      assert(Hptsh2NotNulltrue : (defaultPage =? ptsh2) = false ) by intuition.
      
      assert(Hfalse : true = StateLib.VAddr.eqbList defaultV vaInAncestor) by intuition.
      assert(Htrue :  false = StateLib.VAddr.eqbList defaultV vaInAncestor).
      { assert(Hwellformed1 : wellFormedSndShadow s ).
        unfold propagatedProperties in *.
        unfold consistency in *.
        intuition.
        unfold wellFormedSndShadow in *.
       assert(Hpde : partitionDescriptorEntry s). 
            { unfold propagatedProperties in *.
              unfold consistency in *.
              intuition. }
      assert(Hpdedesc : (exists entry : page,
            nextEntryIsPP descParent PDidx entry s /\ entry <> defaultPage)).
      { 
      apply Hpde;trivial.
      intuition.
      left;trivial. }
      destruct Hpdedesc as (pdparent & Hentry1 & Hentry2).
      assert( getMappedPage pdparent s va = SomePage phypage  ) as Hmap.
      apply getMappedPageGetTableRoot with pt descParent;intuition; subst;trivial.
     (*  assert(Hnotdef : phypage <> defaultPage). 
      { assert( entryPresentFlag pt idxvaparent true s /\ 
      isEntryPage pt idxvaparent phypage s ) as(Hpresent & Hmapphy) by intuition.
      (* unfold entryPresentFlag in Hpresent.
      unfold isEntryPage in Hmapphy. *)
      assert(Hconsprent : isPresentNotDefaultIff s).
      { unfold propagatedProperties in *.
              unfold consistency in *.
              intuition. }
      unfold isPresentNotDefaultIff in *.
      assert(Hread : StateLib.readPhyEntry pt idxvaparent (memory s) <> Some defaultPage).
      unfold not;intros.
      apply Hconsprent in H.
      rewrite entryPresentFlagReadPresent with s pt idxvaparent true in H ;
      trivial.
      now contradict H.
      unfold isEntryPage in Hmapphy.
     unfold StateLib.readPhyEntry in Hread. 
     destruct ( lookup pt idxvaparent (memory s) beqPage beqIndex);simpl in *;
     try now contradict Hmapphy.
     destruct v;try now contradict Hmapphy.
     subst.
     contradict Hread.
     f_equal.
     trivial. } *)
 
      assert(Hmult : multiplexer = MALInternal.multiplexer ) by intuition.
      subst. 
      assert(exists vainparent : vaddr, getVirtualAddressSh2 sh2 s va = Some vainparent  
      /\  beqVAddr defaultVAddr vainparent = false ) . 
      apply Hwellformed1 with  descParent phypage pdparent .
      intuition.      
      assert( false = StateLib.Page.eqb descParent multiplexer) as Hnotmul by 
               intuition.
      unfold StateLib.Page.eqb in *.
      unfold not;intros ; subst.
      symmetry in Hnotmul.
      apply beq_nat_false in Hnotmul.
      now contradict Hnotmul.
      apply nextEntryIsPPgetPd;trivial.
      apply nextEntryIsPPgetSndShadow;intuition.
      apply getMappedPageGetTableRoot with pt descParent;intuition;subst;trivial.
      destruct H as (vainparent & Hgetva & Hvanotdef).
      assert (Heqva : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
      {
      apply getVirtualAddressSh2GetTableRoot with ptsh2 descParent 
      level;trivial.
      + intuition; subst; trivial.
      + intuition;subst;trivial.
      + apply nextEntryIsPPgetSndShadow;intuition.
      + unfold propagatedProperties in *; intuition. }
      rewrite Heqva in Hgetva.
      inversion Hgetva.
      subst.      
      unfold StateLib.VAddr.eqbList .
      assert(defaultV = defaultVAddr) by intuition.
      subst.  
      rewrite Hvanotdef;trivial. } 
       (** New consistency property sh2 data structure is well-formed : 
          the vaddr into the sh2 structure is not equal to defaultVAddr *)
      rewrite <- Htrue in Hfalse.
      now contradict Hfalse.  
    - intros isdefaultVAT.
      eapply bindRev.
      (** getTableAddr **)
      eapply WP.weaken. 
      apply getTableAddr with (currentPart:= ancestor) (idxroot:= PDidx).
      simpl.
      intros s H.
      split.
      try repeat rewrite and_assoc in H.
      pattern s in H. 
      eapply H.
      assert(Hancestor: In ancestor (getPartitions MALInternal.multiplexer s)).
      { assert(Hparent : parentInPartitionList s) by (unfold propagatedProperties in *;unfold consistency in *;intuition).
        apply Hparent with descParent; intuition. }
      split;[unfold propagatedProperties in *;intuition|].
      split;[intuition|].      
      split;[intuition|].
      exists pdAncestor.
      split. intuition.
      split.
      apply pdPartNotNull with ancestor s;trivial. 
      intuition.
      unfold propagatedProperties in *.
      unfold consistency in *.
      intuition.
      subst. left. split;intuition.
      intro ptvaInAncestor. simpl.
       (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2:{
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
            apply idxPDidxSh1notEq.
          - contradict Hfalse.
            apply idxPDidxSh2notEq.
          - assumption.
          - subst;intuition;trivial.  }
      assert (HP :=conj H0 H).
      pattern s in HP.
      eapply HP.
  } (** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptvaInAncestorIsnull. simpl.
      case_eq ptvaInAncestorIsnull.
      { intros HptvaInAncestorIsnulll.
        eapply weaken.
        eapply WP.ret.
        simpl;intros.
        subst.
        
            assert(Ha3:Some L = StateLib.getNbLevel ) by intuition.
        (** verticalSharing : (defaultPage =? ptvaInAncestor) = false *)
        assert(Htrue : (defaultPage =? ptvaInAncestor) = false). 
        {(*  destruct H as (((((((Hprops & Ha1) & Ha2) & Ha3) & Ha4) & Ha5)
                    & Ha6 ) & Ha7).
(*           destruct Ha1 as (Ha1 & Ha8 & Ha9 & Ha10 & Ha11 & Ha12 & Ha13 & Ha14).
          destruct Ha14 as ( Ha15 & Ha16 & Ha17 & Ha18 & Ha19 & Ha20 & Ha21 & Ha22).
          clear H0.
 *)       *)   
 assert(Ha17:isAccessibleMappedPageInParent descParent va phypage s = true) by intuition.
           unfold isAccessibleMappedPageInParent in Ha17.
          assert (  Hsh2 : nextEntryIsPP descParent sh2idx sh2 s) by intuition.
          rewrite nextEntryIsPPgetSndShadow in *.
          rewrite Hsh2 in *.
          assert(Hgetvainparent : getVirtualAddressSh2 sh2 s va = Some  vaInAncestor).
          { subst.
            apply  getVirtualAddressSh2GetTableRoot with ptsh2 descParent L; intuition.
            intuition;subst;trivial.
            intuition.
            intuition.
            subst. intuition.
            
            subst. intuition.
            
            subst. intuition.
              }
          rewrite Hgetvainparent in *.
          assert(Hparent : nextEntryIsPP descParent PPRidx ancestor s) by intuition.
          rewrite nextEntryIsPPgetParent in *.
          rewrite Hparent in *.
          assert(Hpd :  nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
          rewrite nextEntryIsPPgetPd in Hpd.
          rewrite Hpd in *.          
          case_eq (getAccessibleMappedPage pdAncestor s vaInAncestor) ;
          [intros p Hp |intros Hp|intros Hp]; rewrite Hp in *;
          try now contradict Ha17.
          apply beq_nat_true in Ha17.
          subst.
          assert(Ha6:(getTableAddrRoot' ptvaInAncestor PDidx ancestor vaInAncestor s /\ ptvaInAncestor = defaultPage \/
          (forall idx : index,
           StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
           isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s))) by intuition.
          unfold getTableAddrRoot' in Ha6. 
          unfold getTableAddrRoot in Ha6.
          destruct Ha6 as [Ha6 | Ha6].
          + destruct Ha6 as (Ha6 & _).
            destruct Ha6 as (_ & Ha6).
            rewrite <- nextEntryIsPPgetPd in Hpd.
            apply Ha6 in Hpd. clear Ha6.
            destruct Hpd as (nbL & HnbL & Hpd).
            destruct Hpd as (stop & Hstop1 & Hstop2 & Hind).
            rewrite <- HnbL in *.
            inversion Ha3;subst.
            clear IHn.
            unfold getAccessibleMappedPage in *.
            rewrite <- HnbL in *.
            case_eq(getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s);
            [intros pt1 Hpt1 | intros Hpt1]; 
            rewrite Hpt1 in *; try now contradict Hp.
            case_eq(defaultPage =? pt1);intros Hisnull;
            rewrite Hisnull in *;try now contradict Hp.
            clear Hp.
            apply getNbLevelEq in HnbL.
            subst.
            apply getIndirectionRetNotDefaultLtNbLevel with (nbLevel - 1)  
            stop (CLevel (nbLevel - 1)) pdAncestor pt1 vaInAncestor s;trivial;[|rewrite nbLevelEq;trivial].
            assert(Hpde : partitionDescriptorEntry s). 
            { unfold propagatedProperties in *.
              unfold consistency in *.
              intuition. }
            unfold partitionDescriptorEntry in *.
            assert(Hpdedesc : (exists entry : page,
                  nextEntryIsPP descParent PPRidx entry s /\ entry <> defaultPage)).
            { apply Hpde;trivial.
            intuition. intuition. }
            destruct Hpdedesc as (entry & Hentry1 & Hentry2).
            assert(entry = ancestor)by(apply getParentNextEntryIsPPEq with descParent s;trivial).
            subst.
            apply pdPartNotNull' with ancestor s;trivial.
            assert(Hparentpart : parentInPartitionList s) by 
              (unfold propagatedProperties in *; unfold consistency in *; intuition).
            unfold parentInPartitionList in *.
            apply Hparentpart with descParent;trivial.
            intuition. intuition.
          + destruct Ha6 with (StateLib.getIndexOfAddr vaInAncestor fstLevel) as (_ & Ha5);trivial.
            clear Ha6.
            destruct Ha5 as (_ & Ha5).
            rewrite <- nextEntryIsPPgetPd in Hpd.
            apply Ha5 in Hpd. clear Ha5.
            destruct Hpd as (nbL & HnbL & Hpd).
            destruct Hpd as (stop & Hstop1 &  Hind).
            rewrite <- HnbL in *.
            inversion Ha3;subst.
            unfold getAccessibleMappedPage in *.
            rewrite <- HnbL in *.
            case_eq(getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s);
            [intros pt1 Hpt1 | intros Hpt1]; 
            rewrite Hpt1 in *; try now contradict Hp.
            case_eq(defaultPage =? pt1);intros Hisnull;
            rewrite Hisnull in *;try now contradict Hp.
            clear Hp.
            apply getNbLevelEq in HnbL.
            subst.
            assert(Hindeq : getIndirection pdAncestor vaInAncestor 
            (CLevel (nbLevel - 1)) (nbLevel - 1)s = Some ptvaInAncestor).
            apply getIndirectionStopLevelGT2 with (CLevel (nbLevel - 1) + 1); 
            try omega;trivial.
            apply nbLevelEq.
            rewrite Hindeq in *.
            inversion Hpt1.
            subst.
            trivial.   }
        intuition subst.
        apply beq_nat_false in Htrue;
        now contradict Htrue.
        rewrite Htrue in *.
        intuition. } 
      intros HptvaInAncestorIsnulll.
  (** StateLib.getIndexOfAddr **)                
  eapply WP.bindRev.
      eapply WP.weaken.
      2:{ intros.
          destruct H as ((H & [(Hptchild& Hnull) | Hptchild] ) & Hptchildnotnull) .
        + subst.  apply beq_nat_false in Hptchildnotnull. intuition.
        + assert (HP := conj (conj H Hptchild) Hptchildnotnull).
          try repeat rewrite and_assoc in HP.
          pattern s in HP.
          eapply HP.  }
      eapply weaken.
      apply Invariants.getIndexOfAddr.
      simpl;intros.
      eapply H.
      intros idxva.
      simpl.
      intros.
      eapply bindRev; simpl;[|intros []].
      (** writeAccessible **)
      eapply WP.weaken.
      eapply WP.writeAccessible.
      intros. simpl.
      assert (exists entry0 : Pentry,
        lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry0)) as Hlookup.
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
      do 9 rewrite <- and_assoc in H.
      destruct H as (Hsplit & Hfalse & Hrest).
      assert(Heqphy : phypage = pa entry).
      {    destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hx & Hnotnul3 & Hva' & Hppparent & Hpppd & Hi & Hi2 &  Hgetroot2 & Hdef & Hidxancestor).
         intuition. subst.
        unfold isAccessibleMappedPageInParent in *.
        assert (HgetVirt : getVirtualAddressSh2 sh2 s va  = Some vaInAncestor).
        apply isVaInParent with descParent ptsh2;intuition;subst;trivial.
        apply nextEntryIsPPgetSndShadow in Hppsh2.
        rewrite Hppsh2 in *.
        rewrite HgetVirt in *.
        rewrite nextEntryIsPPgetParent in * .
        rewrite Hppparent in *. 
        apply nextEntryIsPPgetPd in Hpppd .
        rewrite Hpppd in *.
        case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor);
        intros * Hacce;
        rewrite Hacce in *;try now contradict Hfalse.
        unfold getAccessibleMappedPage in Hacce.
        assert( isPE ptvaInAncestor  (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) as (Hve & Hroot ).
        apply Hgetroot2;trivial.
        unfold getTableAddrRoot in *.
        destruct Hroot as (_ & Hroot).
        rewrite <- nextEntryIsPPgetPd in *.
        apply Hroot in  Hpppd.
        clear Hroot.
        destruct Hpppd as (nbL & HnbL & stop & Hstop & Hind).
        subst.
        rewrite <- HnbL in *.
        assert(Hgetind : getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s  
        = Some ptvaInAncestor).
        apply getIndirectionStopLevelGT2 with (nbL+1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind in *.
        rewrite Hdef in *.
        destruct ( StateLib.readPresent ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s));try now contradict Hacce.
        destruct b;try now contradict Hacce.
        destruct ( StateLib.readAccessible ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s)); try now contradict Hacce.
        destruct b; try now contradict Hacce.
        unfold StateLib.readPhyEntry in *. 
        rewrite Hlookup in *.
        apply beq_nat_true in Hfalse.
        inversion Hacce.
        subst.
        destruct phypage; destruct (pa entry).
        simpl in *.
        subst.
        f_equal; apply proof_irrelevance. }
      assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true).
      { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        rewrite Heqphy.
        destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
        apply isAccessibleMappedPageInParentTrue with descParent va phypage ptvaInAncestor ptsh2 pdAncestor;
        subst;intuition.
        subst;assumption. subst;trivial. }
      repeat rewrite and_assoc in Hsplit.
      destruct Hsplit as (Hprops & Hsplit).
(*       unfold propagatedProperties in *.
      do 73 rewrite <- and_assoc in Hprops.
      destruct Hprops as (Hprops & xx & Hprops2). 
            repeat rewrite and_assoc in Hprops. *)
      assert (Hnewprops := conj  Hprops  Hsplit).
      assert (H := conj (conj Hnewprops Htrue) Hrest).
      simpl.
      clear Hnewprops.
    (*   repeat rewrite and_assoc in H. *)
      pattern s in H.
      match type of H with 
      | ?HT s => instantiate (1 := fun tt s => HT s  /\ 
                  entryUserFlag ptvaInAncestor idxva false s /\
                  isEntryPage ptvaInAncestor idxva phypage s /\
                  entryPresentFlag ptvaInAncestor idxva true s  ) 
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
      simpl.
      unfold propagatedProperties in *. 
      do 7 rewrite and_assoc.
      clear Hrest  Hsplit  Hprops.
      split.
      
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
      split.
      (** partitionDescriptorEntry **)
      apply partitionDescriptorEntryUpdateUserFlag;trivial.
      intuition.
      (** dataStructurePdSh1Sh2asRoot **)
      destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
      Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      (** currentPartitionInPartitionsList **)
      split.
      unfold currentPartitionInPartitionsList in *.
      simpl in *. subst. 
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite Hpartions. assumption.
      (** noDupMappedPagesList **)  
      split.    
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
      split.
      (** noDupConfigPagesList **)
      apply getIndirectionsNoDupUpdateUserFlag; trivial.
      split.
      (** parentInPartitionList **)
      unfold parentInPartitionList in *.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart.
      intros partition HgetParts parent Hroot.
      generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
      apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
      apply Hparent; trivial.
      split.
      (** accessibleVAIsNotPartitionDescriptor **)
     unfold s'.
      subst.
      clear IHn.
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (_ & Hi).
      intuition.
      subst.
      apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag  with level ancestor   
        pdAncestor;trivial.
      assert(Hparentpart : parentInPartitionList s) by trivial.
      unfold parentInPartitionList in *.
      apply Hparent with descParent;trivial. 
       assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
      assert(  isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s ) as (_ & Hroot).
      apply Hget;split;trivial.
      assumption.
      apply nextEntryIsPPgetPd;trivial.
      subst.
      assert(HaccessInParent : isAccessibleMappedPageInParent descParent va (pa entry) s = true)
       by trivial.
       unfold isAccessibleMappedPageInParent in HaccessInParent.
       (** Here we use the property already present into the precondition : 
            *)
       assert(Hcursh2 : nextEntryIsPP descParent sh2idx sh2 s ) by trivial.
      apply nextEntryIsPPgetSndShadow in Hcursh2.
      rewrite Hcursh2 in HaccessInParent.
      assert(Hvainparent : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
      { assert(Hxx : 
        isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by intuition.
        assert(Hgetva : isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\ 
        getTableAddrRoot ptsh2 sh2idx descParent va s).
        apply Hxx;trivial. clear Hxx.
        destruct Hgetva as (Hva & Hgetva).
        assert(Hisva : isVA' ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s) 
        by trivial.
        unfold getVirtualAddressSh2.
        unfold getTableAddrRoot in Hgetva.
        destruct Hgetva as (_ & Hgetva).
        assert(HcurSh2 : nextEntryIsPP descParent sh2idx sh2 s).
        rewrite  nextEntryIsPPgetSndShadow ;trivial.
        apply Hgetva in HcurSh2.
        destruct HcurSh2 as (nbL & HnbL & stop & Hstop & Hind).
        rewrite <- HnbL.
        subst.
        assert(Hgetind : getIndirection sh2 va nbL (nbLevel - 1) s = Some ptsh2).
        apply getIndirectionStopLevelGT2 with (nbL + 1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind.
        assert (Hptnotnull : (defaultPage =? ptsh2) = false) by trivial.
        rewrite Hptnotnull.
        unfold  isVA' in *. 
        unfold StateLib.readVirtual.
        destruct(lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ); 
        try now contradict Hisva.
        destruct v;try now contradict Hisva.
        subst. trivial. }
      rewrite Hvainparent in *.
      assert(Hgetparent : StateLib.getParent descParent (memory s) = Some ancestor).
      { apply nextEntryIsPPgetParent;trivial. }
      rewrite Hgetparent in *.
      assert(Hgetpdparent : StateLib.getPd ancestor (memory s) = Some pdAncestor).
      { apply nextEntryIsPPgetPd;trivial. }
      rewrite Hgetpdparent in *.
      case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor ); intros * Hi .
      rewrite Hi in *.
      unfold getAccessibleMappedPage in Hi.
      case_eq (StateLib.getNbLevel);intros * Hi2 ; rewrite Hi2 in *;
       try now contradict Hi.
      assert(Hancestor : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by 
      trivial.
      assert(Hget : isPE ptvaInAncestor ( StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\
            getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s).
      apply Hancestor; clear Hancestor;
      trivial.
      destruct Hget as (Hva & Hget).
      unfold getTableAddrRoot in Hget.
      destruct Hget as (_ & Hget).
      apply nextEntryIsPPgetPd in Hgetpdparent.
      apply Hget in Hgetpdparent.
      destruct Hgetpdparent as (nbL & HnbL & stop & Hstop & Hgettable).
      clear Hget.
      rewrite <- HnbL in *.
      inversion Hi2.
      subst.
      assert(Hind :getIndirection pdAncestor vaInAncestor l (nbLevel - 1) s = Some ptvaInAncestor).
      apply getIndirectionStopLevelGT2 with (l+1);trivial.
      omega.
      apply getNbLevelEq in HnbL.
      rewrite HnbL.
      unfold CLevel.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      simpl;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      rewrite Hind in *.
      assert (Hnotnull : (defaultPage =? ptvaInAncestor) = false) by trivial.
      rewrite Hnotnull in *.
      destruct (StateLib.readPresent ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b; try now contradict Hi.
      destruct(StateLib.readAccessible ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b.
      unfold StateLib.readPhyEntry in *.
      rewrite Hlookup in *.
      symmetry; assumption.
      now contradict Hi.
      rewrite Hi in *. 
      now contradict HaccessInParent.
            rewrite Hi in *. 
      now contradict HaccessInParent.
   (* accessibleChildPageIsAccessibleIntoParent *)
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (Hancestor & Hi).
      unfold s'.
      intuition. 
      subst.
      clear IHn.
      apply accessibleChildPageIsAccessibleIntoParentUpdateUserFlagFlase
      with level ancestor pdAncestor va ptsh2 descParent pt;trivial.
      intros;subst;intuition.
      assert(Hparentpart : parentInPartitionList s).
      unfold consistency in *; intuition.
      unfold parentInPartitionList in *.
      apply Hparentpart with descParent;trivial.
      (* noCycleInPartitionTree *)
      assert(Hdiff : noCycleInPartitionTree s) by trivial.
      unfold noCycleInPartitionTree in *.
      intros parent partition Hparts Hparentpart.
      simpl in *.
      assert (getPartitions multiplexer {|
              currentPartition := currentPartition s;
              memory := add ptvaInAncestor idxva
                          (PE
                             {|
                             read := read entry;
                             write := write entry;
                             exec := exec entry;
                             present := present entry;
                             user := false;
                             pa := pa entry |}) (memory s) beqPage beqIndex |}
               = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(HgetParent : getAncestors partition
                {|
                   currentPartition := currentPartition s;
                   memory := add ptvaInAncestor idxva
                               (PE
                                  {|
                                  read := read entry;
                                  write := write entry;
                                  exec := exec entry;
                                  present := present entry;
                                  user := false;
                                  pa := pa entry |}) (memory s) beqPage beqIndex |} = 
                      getAncestors partition  s).
      apply getAncestorsUpdateUserFlag;trivial.
      rewrite HgetParent in *; clear HgetParent.
      apply Hdiff;trivial.
      (* configTablesAreDifferent *)
      assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
      unfold configTablesAreDifferent in *.
      simpl in *.
      fold s'.
      intros partition1 partition2 Hpart1 Hpart2 Hdiff.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      apply Hconfigdiff;trivial.
      rename H into Hcond.
      (** isChild **)
      assert(Hchid : isChild s) by intuition.
      unfold isChild in *.
      simpl in *.
      intros partition parent Hparts Hgetparent.
      rewrite getPartitionsUpdateUserFlag in *;trivial.
      rewrite getParentUpdateUserFlag in *;trivial.
      rewrite getChildrenUpdateFlagUser;trivial.
      apply Hchid;trivial.
          (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    (** physicalPageNotDerived **)
    apply physicalPageNotDerivedUpdateUserFlag;trivial.
    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by trivial.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.  
    (** isParent  *)
    assert(Hisparent : isParent s) by trivial.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by trivial.
    unfold noDupPartitionTree in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by trivial.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va0 = Some vainparent).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by trivial.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh0 s va0 = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg pd;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    apply getVirtualAddressSh2UpdateUserFlag;trivial.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by trivial.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by trivial.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.

  (** Propagated properties **)
      assert(Hi2 : StateLib.getIndexOfAddr va fstLevel = lastIndex) by intuition.
      {  intuition trivial. 
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
          unfold getTableAddrRoot.
          destruct H23 as (Hor & Htableroot).
          split;trivial.
          intros.         
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          left.
          clear IHn.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.

(*             rewrite Hisancestor in *. *)
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages descParent s)).
            apply isConfigTable with descChild;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
            {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                                     unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages (currentPartition s) s)).
            apply isConfigTable with descChild;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.

            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
(** partitions are diffrent then config pages are different *)
        + assert(Hi3 : forall idx : index,
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
           unfold getTableAddrRoot.
          destruct H7 as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi4 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.
        
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagSameValue;trivial.
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert (Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
                  assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages descParent s)).
            apply isConfigTable with shadow1;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                                     unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages (currentPartition s) s)).
            apply isConfigTable with shadow1;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.       
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.

        assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
        unfold isAncestor in *.
        destruct Hisancestor as [Hisancestor | Hisancestor].
        - subst currentPart.
          clear IHn.
(*           rewrite Hisancestor in *. *)
          left.
          unfold consistency in *.
          assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *.
          assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages descParent s)).
          apply isConfigTable with shadow2;trivial.
          intuition. subst;trivial.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2.
        - unfold consistency in *.
          subst.
          clear IHn.
          assert(In (currentPartition s) (getPartitions multiplexer s)).
          unfold currentPartitionInPartitionsList in *.
          intuition.
          assert((currentPartition s) <> ancestor).
          { unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                                     unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *. 
          assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages (currentPartition s) s)).
          apply isConfigTable with shadow2;trivial.
          intuition.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          left.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages descParent s)).
            apply isConfigTable with list;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                                     unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages (currentPartition s) s)).
            apply isConfigTable with list;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi4 : nextEntryIsPP currentPart sh1idx tableroot s') by intuition.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.      
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
         
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.

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
      + assert (Hfalse' : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. 
        assert((getConfigPages partition s') = 
             (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        rewrite Hconfig in *.
        assert(Hii : forall partition : page,
            In partition (getPartitions multiplexer s) -> 
            In phyDescChild (getConfigPages partition s) -> False) by trivial.
        assert(Hfalse' : In phyDescChild (getConfigPages partition s)) by trivial.
        apply Hii in Hfalse';trivial. 
      + unfold isPartitionFalse. 
         unfold s'.
         cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
         
(** Internal properties to propagate **)      
      + unfold s'.
        apply isAncestorUpdateUserFlag;trivial. 
      + destruct H.  
        unfold propagatedProperties in *.
        { assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
          apply getPartitionsUpdateUserFlag; trivial.
          rewrite Hpartions; assumption. }
       
      + apply isPEUpdateUserFlag;trivial. 
          assert(Hpe : forall idx : index,
                StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ 
                getTableAddrRoot pt PDidx descParent va s) 
          by trivial.
           apply Hpe;trivial.
      +  assert(Hroot : isPE pt (StateLib.getIndexOfAddr va fstLevel ) s /\
          getTableAddrRoot pt PDidx descParent va s).
          assert(Hpe : forall idx : index,
           StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) 
            by trivial.
          apply Hpe;trivial.
          destruct Hroot as (Hve & Hroot). 
          unfold getTableAddrRoot in *.
          destruct Hroot as (Hor & Hroot).
          split;trivial.
          intros root Hpp.
          unfold s' in Hpp.
          apply nextEntryIsPPUpdateUserFlag' in Hpp.
          apply Hroot in Hpp.
          destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
          exists nbL ; split;trivial.
          exists stop;split;trivial.
          rewrite <- Hind.
          unfold s'.
          apply getIndirectionUpdateUserFlag;trivial. 
       +  apply entryPresentFlagUpdateUserFlag;trivial. 
       + apply entryUserFlagUpdateUserFlagSameValue;trivial.
       +  apply isEntryPageUpdateUserFlag;trivial. 
       +  subst. clear IHn.       
          assert(HisAccess : isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s' =
          isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow ancestor (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt : getVirtualAddressSh2 p
                             {| currentPartition := currentPartition s;
                              memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                              (PE
                                 {|
                                 read := read entry;
                                 write := write entry;
                                 exec := exec entry;
                                 present := present entry;
                                 user := false;
                                 pa := pa entry |}) (memory s) beqPage beqIndex |} vaInAncestor =
                            getVirtualAddressSh2 p s vaInAncestor).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some L = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p vaInAncestor L (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s vaInAncestor );
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent ancestor (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
                          {|
                          currentPartition := currentPartition s;
                          memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                                      (PE
                                         {|
                                         read := read entry;
                                         write := write entry;
                                         exec := exec entry;
                                         present := present entry;
                                         user := false;
                                         pa := pa entry |}) (memory s) beqPage beqIndex |} v = 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In ancestor (getPartitions multiplexer s)).
                apply Hparentpart with descParent;trivial.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions with ancestor p0;trivial.
                unfold consistency in *.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
                        isPE ptvaInAncestor idx s /\ 
                        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                as (Hpe & Hroot);
                trivial.
                apply Hparentpart with ancestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdiff1 : p0 <> ancestor).
                              assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                              apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              assert(Hparentinpart : parentInPartitionList s) by intuition.
              unfold parentInPartitionList in *.
              apply Hparentinpart with ancestor;trivial.
              rewrite nextEntryIsPPgetParent;trivial.
              unfold not;intros Hfalsei;subst.
              now contradict Hdiff1.
              }
              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold partitionDescriptorEntry in *.
              assert(exists entry : page, nextEntryIsPP descParent PDidx entry s /\
                      entry <> defaultPage) as (pdParent & Hpp & Hnotnull).
              apply Hpde;trivial.
              left;trivial.
              clear Hpde.
              apply nextEntryIsPPgetPd in Hpp.
              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
        + apply nextEntryIsPPUpdateUserFlag; assumption. 
        + apply isVAUpdateUserFlag; intuition.
        +  assert ( Hi : 
                  getTableAddrRoot ptsh2 sh2idx descParent va s) by intuition.
          unfold getTableAddrRoot in *.
          destruct Hi as (Hii & Htableroot).
          split; trivial.
          intro. intros  Hxx.
          apply nextEntryIsPPUpdateUserFlag' in Hxx.      
          generalize(Htableroot tableroot Hxx );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          unfold getTableAddrRoot.
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply isVA'UpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + assert(Hi :forall idx : index,
              StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
              isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) 
              by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption. 
        + assert(Hi : forall idx : index,
          StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
          isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split;trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.         
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
      (** WriteAccessible property **) 
      + unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. 
      + unfold isEntryPage.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  cbn. reflexivity.
      + unfold entryPresentFlag.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  
        cbn.
        unfold consistency in *.
        assert(Hpres : isPresentNotDefaultIff s ) by intuition.
        symmetry.
        apply phyPageIsPresent with ptvaInAncestor idxva s;trivial. }

(** setAccessible success **)
  simpl. subst.
  unfold hoareTriple in *.
  intros.  
  case_eq (writeAccessibleRecAux n vaInAncestor ancestor false s );
   [intros p Hi | intros undefnum s0 Hundef ].
  * destruct p;simpl ; intros.
   assert(match writeAccessibleRecAux n vaInAncestor ancestor false s with
      | val (_, s') =>
          forall partition : page,
          In partition (getAncestorsAux ancestor (memory s') n) ->
          ~ In phypage (getAccessibleMappedPages partition s')
      | undef _ _ => False
      end).
  {
  apply IHn with ptvaInAncestor idxva;trivial.
  intuition.
  + unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) 
    by apply pageDecOrNot.
    destruct Hor as [Hor | Hor].
    left;trivial.
    right.
    assert(Hpp : nextEntryIsPP descParent PPRidx ancestor s ) by trivial.
    assert (HisAnces : isAncestor currentPart descParent s) by trivial.
    assert (His : isAncestor currentPart ancestor s).
    unfold propagatedProperties in *. unfold consistency in *.  apply isAncestorTrans with descParent;intuition. 
                             unfold consistency in *. intuition.
            unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition.   
    apply nextEntryIsPPgetParent;trivial.
    unfold isAncestor in His.
    destruct His as [His | Hsi];
    intuition.
  +    unfold propagatedProperties in *.
      unfold consistency in *.
      apply ancestorInPartitionTree with descParent;trivial.
 intuition. intuition.
 assert(Hpp :nextEntryIsPP descParent PPRidx ancestor s); trivial.
 rewrite nextEntryIsPPgetParent in Hpp.
  unfold getAncestors.
  destruct nbPage;simpl; rewrite Hpp;
  simpl;left;trivial.
 }
  rewrite Hi in *.

   assert(Hnextpp: StateLib.getParent descParent (memory s) = Some ancestor).
   apply nextEntryIsPPgetParent;intuition.
   assert( HparentEq : StateLib.getParent descParent (memory s0) =
   StateLib.getParent descParent (memory s)).
   {
   assert(Ha : 
   {{ fun s : state => propagatedProperties accessibleChild accessibleSh1 accessibleSh2 accessibleList pdChild currentPart
  currentPD level ptRefChild descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild
  ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList
  idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
  derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
  derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
isAncestor currentPart ancestor s /\
(In ancestor (getPartitions MALInternal.multiplexer s) /\
(defaultPage =? phypage) = false /\
(forall idx : index,
 StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
 isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) /\
(defaultPage =? ptvaInAncestor) = false /\
StateLib.getIndexOfAddr vaInAncestor fstLevel = idxva /\
entryPresentFlag ptvaInAncestor idxva true s /\
entryUserFlag ptvaInAncestor idxva false s /\
isEntryPage ptvaInAncestor idxva phypage s /\
isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true)
  /\ StateLib.getParent descParent (memory s) = Some ancestor }}
writeAccessibleRecAux n vaInAncestor ancestor false
{{  fun _ s => StateLib.getParent descParent (memory s) = Some ancestor}}).

   apply  getParentWriteAccessibleRec ;trivial.
   unfold hoareTriple in Ha.
   generalize (Ha s ) ; clear Ha; intros Ha. (* 

   apply Ha in Hnextpp. *)
      rewrite Hi in *.
      rewrite Ha.    assert(Hnext: StateLib.getParent descParent (memory s) = Some ancestor).
   apply nextEntryIsPPgetParent;intuition.   
   
   rewrite Hnextpp in *.
   symmetry ;trivial. clear Ha.
   intuition.
   { unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) 
    by apply pageDecOrNot.
    destruct Hor as [Hor | Hor].
    left;trivial.
    right.
    assert(Hpp : nextEntryIsPP descParent PPRidx ancestor s ) by trivial.
    assert (HisAnces : isAncestor currentPart descParent s) by trivial.
    assert (His : isAncestor currentPart ancestor s).
    unfold propagatedProperties in *. unfold consistency in *.  apply isAncestorTrans with descParent;intuition. 
     unfold consistency in *. intuition.
     unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition.   
    unfold isAncestor in His.
    destruct His as [His | Hsi];
    intuition. }
  {    unfold propagatedProperties in *.
      unfold consistency in *.
      apply ancestorInPartitionTree with descParent;trivial.
 intuition. intuition.
 assert(Hpp :nextEntryIsPP descParent PPRidx ancestor s); trivial.
 rewrite nextEntryIsPPgetParent in Hpp.
  unfold getAncestors.
  destruct nbPage;simpl; rewrite Hpp;
  simpl;left;trivial. } }
   simpl in *.
   rewrite HparentEq in *.
   rewrite  Hnextpp in *.
   simpl in *.
   destruct H0.
   **
   subst partition.
   assert(Hnone: getAccessibleMappedPage pdAncestor s vaInAncestor = NonePage). 
  { apply getMappedPageNotAccessible with ptvaInAncestor ancestor phypage;
  intuition;subst;trivial. }
  assert( getMappedPage pdAncestor s vaInAncestor = SomePage phypage).
  { apply getMappedPageGetTableRoot with ptvaInAncestor ancestor;
  intuition;subst;trivial.  }
  unfold getAccessibleMappedPages.
   assert(Hpdanc : StateLib.getPd ancestor (memory s) = Some pdAncestor).
   { apply nextEntryIsPPgetPd;intuition. }
 assert( HpdEq : StateLib.getPd ancestor (memory s0) =
   StateLib.getPd ancestor (memory s)).
 {  assert(Ha : 
   {{ fun s : state => propagatedProperties accessibleChild accessibleSh1 accessibleSh2 accessibleList pdChild currentPart
  currentPD level ptRefChild descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild
  ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList
  idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
  derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
  derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
isAncestor currentPart ancestor s /\
(In ancestor (getPartitions MALInternal.multiplexer s) /\
(defaultPage =? phypage) = false /\
(forall idx : index,
 StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
 isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) /\
(defaultPage =? ptvaInAncestor) = false /\
StateLib.getIndexOfAddr vaInAncestor fstLevel = idxva /\
entryPresentFlag ptvaInAncestor idxva true s /\
entryUserFlag ptvaInAncestor idxva false s /\
isEntryPage ptvaInAncestor idxva phypage s /\
isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true)
  /\ StateLib.getPd ancestor (memory s) = Some pdAncestor }}
writeAccessibleRecAux n vaInAncestor ancestor false
{{  fun _ s => StateLib.getPd ancestor (memory s) = Some pdAncestor}}).

   apply  getPdWriteAccessibleRec;trivial.
    unfold hoareTriple in Ha.
   generalize (Ha s ) ; clear Ha; intros Ha. (* 

   apply Ha in Hnextpp. *)
      rewrite Hi in *.
      rewrite Ha.
          assert(Hnext: StateLib.getPd ancestor (memory s) = Some pdAncestor ).
   apply nextEntryIsPPgetPd;intuition.   
  rewrite Hnext. trivial.
   intuition.
   { unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) 
    by apply pageDecOrNot.
    destruct Hor as [Hor | Hor].
    left;trivial.
    right.
    assert(Hpp : nextEntryIsPP descParent PPRidx ancestor s ) by trivial.
    assert (HisAnces : isAncestor currentPart descParent s) by trivial.
    assert (His : isAncestor currentPart ancestor s).
    unfold propagatedProperties in *. unfold consistency in *.  apply isAncestorTrans with descParent;intuition. 
     unfold consistency in *. intuition.
     unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition.   
    unfold isAncestor in His.
    destruct His as [His | Hsi];
    intuition. }
  {    unfold propagatedProperties in *.
      unfold consistency in *.
      apply ancestorInPartitionTree with descParent;trivial.
 intuition. intuition.
 assert(Hpp :nextEntryIsPP descParent PPRidx ancestor s); trivial.
 rewrite nextEntryIsPPgetParent in Hpp.
  unfold getAncestors.
  destruct nbPage;simpl; rewrite Hpp;
  simpl;left;trivial. } } 
   rewrite HpdEq.
   rewrite Hpdanc.
   unfold getAccessibleMappedPagesAux.
   rewrite filterOptionInIff.
   unfold getAccessibleMappedPagesOption.
   rewrite in_map_iff.
   unfold not;intros Hfalse.
   destruct Hfalse as (x & Hx1 & Hx2).
  
   assert(getMappedPage pdAncestor s0 x = SomePage phypage).
   { apply accessiblePAgeIsMapped; trivial. }
    contradict Hx1.

(*   assert(HaccessEqx : getAccessibleMappedPage pdAncestor s0 vaInAncestor =
  getAccessibleMappedPage pdAncestor s vaInAncestor).
   apply getAccessibleMappedPageWriteAccessibleRec  with n ancestor b; trivial.
      
 *)
  assert(HaccessEq :  getMappedPage pdAncestor s0 vaInAncestor=
  getMappedPage pdAncestor s vaInAncestor).
  {  assert(Ha : 
   {{ fun s : state => propagatedProperties accessibleChild accessibleSh1 accessibleSh2 accessibleList pdChild currentPart
  currentPD level ptRefChild descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild
  ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList
  idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
  derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
  derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
isAncestor currentPart ancestor s /\
(In ancestor (getPartitions MALInternal.multiplexer s) /\
(defaultPage =? phypage) = false /\
(forall idx : index,
 StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
 isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) /\
(defaultPage =? ptvaInAncestor) = false /\
StateLib.getIndexOfAddr vaInAncestor fstLevel = idxva /\
entryPresentFlag ptvaInAncestor idxva true s /\
entryUserFlag ptvaInAncestor idxva false s /\
isEntryPage ptvaInAncestor idxva phypage s /\
isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true)
  /\ getMappedPage pdAncestor s vaInAncestor = SomePage phypage}}
writeAccessibleRecAux n vaInAncestor ancestor false
{{  fun _ s =>getMappedPage pdAncestor s vaInAncestor = SomePage phypage}}).

     apply getMappedPageWriteAccessibleRec;trivial.
    unfold hoareTriple in Ha.
   generalize (Ha s ) ; clear Ha; intros Ha. (* 

   apply Ha in Hnextpp. *)
      rewrite Hi in *.
      rewrite Ha.
      intuition.

   intuition.
   { unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) 
    by apply pageDecOrNot.
    destruct Hor as [Hor | Hor].
    left;trivial.
    right.
    assert(Hpp : nextEntryIsPP descParent PPRidx ancestor s ) by trivial.
    assert (HisAnces : isAncestor currentPart descParent s) by trivial.
    assert (His : isAncestor currentPart ancestor s).
    unfold propagatedProperties in *. unfold consistency in *.  apply isAncestorTrans with descParent;intuition. 
     unfold consistency in *. intuition.
     unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition. 
    unfold isAncestor in His.
    destruct His as [His | Hsi];
    intuition. }
  {    unfold propagatedProperties in *.
      unfold consistency in *.
      apply ancestorInPartitionTree with descParent;trivial.
 intuition. intuition.
 assert(Hpp :nextEntryIsPP descParent PPRidx ancestor s); trivial.
 rewrite nextEntryIsPPgetParent in Hpp.
  unfold getAncestors.
  destruct nbPage;simpl; rewrite Hpp;
  simpl;left;trivial. } }  
 (*  rewrite  HaccessEq in *. *)
 assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaInAncestor va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).

  assert (va1 = x). 
    { apply eqMappedPagesEqVaddrs with phypage pdAncestor s0;trivial.
      rewrite <- H0.
      symmetry.
      rewrite  <-HaccessEq .
      apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
      apply getNbLevelEqOption.

      assert(HnodupS0 : noDupMappedPagesList s0).
      { assert(Ha :  {{ fun s : state => propagatedProperties accessibleChild accessibleSh1 accessibleSh2 accessibleList pdChild currentPart
  currentPD level ptRefChild descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild
  ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList
  idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
  derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
  derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
isAncestor currentPart ancestor s /\
(In ancestor (getPartitions MALInternal.multiplexer s) /\
(defaultPage =? phypage) = false /\
(forall idx : index,
 StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
 isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) /\
(defaultPage =? ptvaInAncestor) = false /\
StateLib.getIndexOfAddr vaInAncestor fstLevel = idxva /\
entryPresentFlag ptvaInAncestor idxva true s /\
entryUserFlag ptvaInAncestor idxva false s /\
isEntryPage ptvaInAncestor idxva phypage s /\
isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true)
  /\ noDupMappedPagesList s }}
writeAccessibleRecAux n vaInAncestor ancestor false
{{  fun _ s =>noDupMappedPagesList s }}).

     apply noDupMappedPagesListWriteAccessibleRec;trivial.
    unfold hoareTriple in Ha.
   generalize (Ha s ) ; clear Ha; intros Ha. (* 

   apply Ha in Hnextpp. *)
      rewrite Hi in *.
      
      apply Ha.
      intuition.
   { unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) 
    by apply pageDecOrNot.
    destruct Hor as [Hor | Hor].
    left;trivial.
    right.
    assert(Hpp : nextEntryIsPP descParent PPRidx ancestor s ) by trivial.
    assert (HisAnces : isAncestor currentPart descParent s) by trivial.
    assert (His : isAncestor currentPart ancestor s).
    unfold propagatedProperties in *. unfold consistency in *.  apply isAncestorTrans with descParent;intuition. 
     unfold consistency in *. intuition.
     unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition. 
    unfold isAncestor in His.
    destruct His as [His | Hsi];
    intuition. }
  {    unfold propagatedProperties in *.
      unfold consistency in *.
      apply ancestorInPartitionTree with descParent;trivial.
 intuition. intuition.
 assert(Hpp :nextEntryIsPP descParent PPRidx ancestor s); trivial.
 rewrite nextEntryIsPPgetParent in Hpp.
  unfold getAncestors.
  destruct nbPage;simpl; rewrite Hpp;
  simpl;left;trivial. } unfold propagatedProperties in *.
  unfold consistency in *. intuition.  }
      unfold noDupMappedPagesList in *. 

   assert(Hparentpart : parentInPartitionList s).
     { unfold propagatedProperties in *.
      unfold consistency in *. intuition. }
   assert(In ancestor (getPartitions MALInternal.multiplexer s)).
   { unfold parentInPartitionList in *.
     apply  Hparentpart with descParent; trivial.
     intuition.
     apply nextEntryIsPPgetParent;intuition. }      
    assert(HnodupS : In ancestor (getPartitions MALInternal.multiplexer s0)).
    { assert(Ha : 
   {{ fun s : state => propagatedProperties accessibleChild accessibleSh1 accessibleSh2 accessibleList pdChild currentPart
  currentPD level ptRefChild descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild
  ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList
  idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
  derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
  derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
isAncestor currentPart ancestor s /\
(In ancestor (getPartitions MALInternal.multiplexer s) /\
(defaultPage =? phypage) = false /\
(forall idx : index,
 StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
 isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) /\
(defaultPage =? ptvaInAncestor) = false /\
StateLib.getIndexOfAddr vaInAncestor fstLevel = idxva /\
entryPresentFlag ptvaInAncestor idxva true s /\
entryUserFlag ptvaInAncestor idxva false s /\
isEntryPage ptvaInAncestor idxva phypage s /\
isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true)
  /\ In ancestor (getPartitions MALInternal.multiplexer s) }}
writeAccessibleRecAux n vaInAncestor ancestor false
{{  fun _ s =>In ancestor (getPartitions MALInternal.multiplexer s) }}).

     apply getPartitionsWriteAccessibleRec;trivial.
    unfold hoareTriple in Ha.
   generalize (Ha s ) ; clear Ha; intros Ha. (* 

   apply Ha in Hnextpp. *)
      rewrite Hi in *.
      apply Ha.
      intuition.
   { unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) 
    by apply pageDecOrNot.
    destruct Hor as [Hor | Hor].
    left;trivial.
    right.
    assert(Hpp : nextEntryIsPP descParent PPRidx ancestor s ) by trivial.
    assert (HisAnces : isAncestor currentPart descParent s) by trivial.
    assert (His : isAncestor currentPart ancestor s).
    unfold propagatedProperties in *. unfold consistency in *.  apply isAncestorTrans with descParent;intuition. 
     unfold consistency in *. intuition.
     unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition. 
    unfold isAncestor in His.
    destruct His as [His | Hsi];
    intuition. }
    }

    apply HnodupS0 in HnodupS.
    unfold getMappedPages in HnodupS.
    rewrite HpdEq in *.
    rewrite Hpdanc in *.
    unfold getMappedPagesAux in *. 
    unfold getMappedPagesOption in *;trivial.      
   }
          subst x.
   assert(Htrue : getAccessibleMappedPage pdAncestor s0 vaInAncestor= NonePage) .
   { assert(Ha : 
   {{ fun s : state => propagatedProperties accessibleChild accessibleSh1 accessibleSh2 accessibleList pdChild currentPart
        currentPD level ptRefChild descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild
        ptSh1Child shadow1 idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList
        idxConfigPagesList presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
        derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
        derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
      isAncestor currentPart ancestor s /\
      (In ancestor (getPartitions MALInternal.multiplexer s) /\
      (defaultPage =? phypage) = false /\
      (forall idx : index,
       StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
       isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) /\
      (defaultPage =? ptvaInAncestor) = false /\
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idxva /\
      entryPresentFlag ptvaInAncestor idxva true s /\
      entryUserFlag ptvaInAncestor idxva false s /\
      isEntryPage ptvaInAncestor idxva phypage s /\
      isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true)
        /\  getAccessibleMappedPage pdAncestor s vaInAncestor = NonePage }}
      writeAccessibleRecAux n vaInAncestor ancestor false
      {{  fun _ s => getAccessibleMappedPage pdAncestor s vaInAncestor = NonePage}}).

   apply  getAccessibleNoneWriteAccessibleRec ;trivial.
    unfold hoareTriple in Ha.
   generalize (Ha s ) ; clear Ha; intros Ha. (* 

   apply Ha in Hnextpp. *)
      rewrite Hi in *.
      rewrite Ha;trivial.
      intuition.
      
   { unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) 
    by apply pageDecOrNot.
    destruct Hor as [Hor | Hor].
    left;trivial.
    right.
    assert(Hpp : nextEntryIsPP descParent PPRidx ancestor s ) by trivial.
    assert (HisAnces : isAncestor currentPart descParent s) by trivial.
    assert (His : isAncestor currentPart ancestor s).
    unfold propagatedProperties in *. unfold consistency in *.  apply isAncestorTrans with descParent;intuition. 
     unfold consistency in *. intuition.
     unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition. 
    unfold isAncestor in His.
    destruct His as [His | Hsi];
    intuition. }
  {    unfold propagatedProperties in *.
      unfold consistency in *.
      apply ancestorInPartitionTree with descParent;trivial.
 intuition. intuition.
 assert(Hpp :nextEntryIsPP descParent PPRidx ancestor s); trivial.
 rewrite nextEntryIsPPgetParent in Hpp.
  unfold getAncestors.
  destruct nbPage;simpl; rewrite Hpp;
  simpl;left;trivial. 
     } }
     assert(Hnewhyp : getAccessibleMappedPage pdAncestor s0 vaInAncestor = 
     getAccessibleMappedPage pdAncestor s0 va1).
     apply getAccessibleMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.
rewrite <- Hnewhyp.
  
   rewrite Htrue.
    unfold not; intros Hfalse; now contradict Hfalse. (* 
   intuition.        
    move Hx1 at bottom.
    rewrite HaccessEqx in *.
    rewrite Hx1 in *.
    now contradict Hnone. *)
    ** apply H1;trivial.  
    

    
 * 
  assert(match writeAccessibleRecAux n vaInAncestor ancestor false s with
      | val (_, s') =>
          forall partition : page,
          In partition (getAncestorsAux ancestor (memory s') n) ->
          ~ In phypage (getAccessibleMappedPages partition s')
      | undef _ _ => False
      end).

  {
  apply IHn with ptvaInAncestor idxva;trivial.
  intuition.
  + unfold isAncestor.
  assert(Hor : currentPart = ancestor \/ currentPart <>  ancestor) 
    by apply pageDecOrNot.
    destruct Hor as [Hor | Hor].
    left;trivial.
    right.
    assert(Hpp : nextEntryIsPP descParent PPRidx ancestor s ) by trivial.
    assert (HisAnces : isAncestor currentPart descParent s) by trivial.
    assert (His : isAncestor currentPart ancestor s).
     
    unfold propagatedProperties in *. unfold consistency in *.  apply isAncestorTrans with descParent;intuition. 
     unfold consistency in *. intuition.
     unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition. 
    apply nextEntryIsPPgetParent;trivial.
    unfold isAncestor in His.
    destruct His as [His | Hsi];
    intuition.
  +    unfold propagatedProperties in *.
      unfold consistency in *.
      apply ancestorInPartitionTree with descParent;trivial.
 intuition. intuition.
 assert(Hpp :nextEntryIsPP descParent PPRidx ancestor s); trivial.
 rewrite nextEntryIsPPgetParent in Hpp.
  unfold getAncestors.
  destruct nbPage;simpl; rewrite Hpp;
  simpl;left;trivial.
 }
  rewrite Hundef in *. trivial.    }
Qed.
 
Lemma WriteAccessibleRecPropagateNewProp pg accessibleChild accessibleSh1 accessibleSh2 accessibleList 
descParent va  pt (phypage : page) idxvaparent pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild: 
{{  fun s : state =>
 propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
 pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
  ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
 presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
 idxConfigPagesList presentConfigPagesList 
 currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
 ptSh1ChildFromSh1 derivedSh1Child childSh2
 derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s /\
 
isAncestor  currentPart descParent s /\
(In descParent (getPartitions MALInternal.multiplexer s)  /\
     (defaultPage =? phypage) = false /\
    (forall idx : index,
StateLib.getIndexOfAddr va fstLevel = idx ->
isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) /\
(defaultPage =? pt) = false /\
StateLib.getIndexOfAddr va fstLevel = idxvaparent /\
entryPresentFlag pt idxvaparent true s /\
entryUserFlag pt idxvaparent false s /\
    isEntryPage pt idxvaparent phypage s /\
    isAccessibleMappedPageInParent descParent va phypage s = true ) /\ 
    (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In pg (getAccessibleMappedPages partition s))
    }} 
  Internal.writeAccessibleRecAux (nbPage+1) va descParent false {{
    fun _ s  =>
    (forall partition : page,
    In partition (getAncestors currentPart s) ->
    ~ In pg (getAccessibleMappedPages partition s)) 
     }}.
Proof.
revert va descParent  pt phypage idxvaparent .
induction  (nbPage+1) .
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
  assert(Htrue : forall partition : page,
       In partition (getAncestors currentPart s) ->
       ~ In pg (getAccessibleMappedPages partition s)) by intuition.
  apply Htrue;trivial.
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
                  destruct Hcurpart as ( Hancestors & (Hcurpart & Hnewprops) & Hnewprops1).
                  clear Hancestors. 
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
  2:{
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
  } (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptsh2Isnull. simpl.
  case_eq ptsh2Isnull.
  intros. eapply WP.weaken.  eapply WP.ret . simpl. intros.
  
  assert(Htrue : forall partition : page,
       In partition (getAncestors currentPart s) ->
       ~ In pg (getAccessibleMappedPages partition s)) by intuition.
  apply Htrue;trivial.
  intros Hptsh2NotNull.
  (** readVirtual **)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.readVirtual.
  simpl; intros.
  split.
  pattern s in H.
  eapply H.
  destruct H as 
  ((((((((Hprops & Hi ) & Hcurpart)& Hmult) & Hnotmult) & Hsh2root) & HnblL)
           & Hidxaddr) & H).
           
  destruct Hi as (  _ & Hnewprops).
 intuition.
  subst.
  apply beq_nat_false in H.
  now contradict H.
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
  intros pdAncestor. (* 
  unfold setAccessible.
  simpl.
  eapply bindRev.
(** setAccessible **)
  unfold setAccessible.
  { *) eapply bindRev.
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
    case_eq (isdefaultVA).
    -  intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition. 
    - intros isdefaultVAT.
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
      assert(Hcons : consistency s) by intuition.
      unfold consistency in *.
      destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent & _ & _).
      unfold parentInPartitionList in *. 
      instantiate (2:= ancestor).
      split.
      apply Hparent with descParent; intuition.
       
      instantiate (1:= PDidx).
      split. intuition.
      exists pdAncestor.
      split. intuition.
      split. 
      unfold consistency in *.
(*       destruct Hcons as (Hpd & _& _& _ & _ & _ & _ & Hparent).  *)
      unfold partitionDescriptorEntry in Hpd.
      unfold parentInPartitionList in *.
      subst.
      assert(Hpartancestor : In ancestor (getPartitions MALInternal.multiplexer s)).
      {       apply Hparent with descParent; intuition. } 
      generalize (Hpd ancestor Hpartancestor); clear Hpd; intros Hpd.     
      assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/PDidx = sh3idx
              \/ PDidx = PPRidx  \/ PDidx = PRidx ) as Htmp 
            by auto.
      generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
      destruct Hpd as (Hidxpd & _& Hentry).
      destruct Hentry as (page1 & Hpd & Hancesnotnull).
      subst.
      assert (Hrootances : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
      unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
       [destruct (lookup ancestor i (memory s) beqPage beqIndex)
       as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict Hrootances |
        now contradict Hrootances | 
       subst ; assumption| now contradict Hrootances| now contradict Hrootances ]  
       |now contradict Hrootances] | now contradict Hrootances].
      subst. left. split;intuition.
      intro ptvaInAncestor. simpl.
       (** simplify the new precondition **)     
      eapply WP.weaken.
      intros.
      2:{
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
      do  16 (* 6 *) rewrite <- and_assoc in H0.
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
  } (** comparePageToNull **) 
      eapply WP.bindRev.
      eapply Invariants.comparePageToNull.
      intro ptvaInAncestorIsnull. simpl.
      case_eq ptvaInAncestorIsnull.
      2:{
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
      simpl.
      eapply bindRev; simpl;[|intros []].
      (** writeAccessible **)
      eapply WP.weaken.
      eapply WP.writeAccessible.
      intros. simpl.
      assert (exists entry0 : Pentry,
        lookup ptvaInAncestor idxva (memory s) beqPage beqIndex = Some (PE entry0)) as Hlookup.
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
      do 9 rewrite <- and_assoc in H.
      destruct H as (Hsplit & Hfalse & Hrest).
      assert(Heqphy : phypage = pa entry).
      {    destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & _& Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
         intuition. subst.
        unfold isAccessibleMappedPageInParent in *.
        assert (HgetVirt : getVirtualAddressSh2 sh2 s va  = Some vaInAncestor).
        apply isVaInParent with descParent ptsh2;trivial.
        apply nextEntryIsPPgetSndShadow in Hppsh2.
        rewrite Hppsh2 in *.
        rewrite HgetVirt in *.
        rewrite nextEntryIsPPgetParent in * .
        rewrite Hppparent in *. 
        apply nextEntryIsPPgetPd in Hpppd .
        rewrite Hpppd in *.
        case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor);
        intros * Hacce;
        rewrite Hacce in *;try now contradict Hfalse.
        unfold getAccessibleMappedPage in Hacce.
        assert( isPE ptvaInAncestor  (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) as (Hve & Hroot ).
        apply Hgetroot2;trivial.
        unfold getTableAddrRoot in *.
        destruct Hroot as (_ & Hroot).
        rewrite <- nextEntryIsPPgetPd in *.
        apply Hroot in  Hpppd.
        clear Hroot.
        destruct Hpppd as (nbL & HnbL & stop & Hstop & Hind).
        subst.
        rewrite <- HnbL in *.
        assert(Hgetind : getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s  
        = Some ptvaInAncestor).
        apply getIndirectionStopLevelGT2 with (nbL+1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind in *.
        rewrite H in *.
        destruct ( StateLib.readPresent ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s));try now contradict Hacce.
        destruct b;try now contradict Hacce.
        destruct ( StateLib.readAccessible ptvaInAncestor
        (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
        (memory s)); try now contradict Hacce.
        destruct b; try now contradict Hacce.
        unfold StateLib.readPhyEntry in *. 
        rewrite Hlookup in *.
        apply beq_nat_true in Hfalse.
        inversion Hacce.
        subst.
        destruct phypage; destruct (pa entry).
        simpl in *.
        subst.
        f_equal; apply proof_irrelevance. }
      assert (Htrue : isAccessibleMappedPageInParent ancestor vaInAncestor phypage s = true).
      { assert(Hcons : consistency s).
        { unfold propagatedProperties in *.
          intuition. }
        unfold consistency in Hcons.
        rewrite Heqphy.
        destruct Hsplit as 
(((((((((Hprops  & _ )  & Hmult)& Hnotnul1)  
 & Hgetroot ) & Hnotnull2 ) & Hidx )
           & Hpresent ) & Huser ) &Hep).
           destruct Hrest as (_ & Hnotmult & Hppsh2 & HL & Hlstidx & Hva & 
           Hnotnul3 & Hva' & Hppparent & Hpppd & Hgetroot2 & Hdef & Hidxancestor).
        apply isAccessibleMappedPageInParentTrue with descParent va phypage ptvaInAncestor ptsh2 pdAncestor;
        subst;intuition.
        subst;assumption. }
      repeat rewrite and_assoc in Hsplit.
      destruct Hsplit as (Hprops & Hsplit).
(*       unfold propagatedProperties in *.
      do 73 rewrite <- and_assoc in Hprops.
      destruct Hprops as (Hprops & xx & Hprops2). 
            repeat rewrite and_assoc in Hprops. *)
      assert (Hnewprops := conj  Hprops  Hsplit).
      assert (H := conj (conj Hnewprops Htrue) Hrest).
      simpl.
      clear Hnewprops.
    (*   repeat rewrite and_assoc in H. *)
      pattern s in H.
      match type of H with 
      | ?HT s => instantiate (1 := fun tt s => HT s  /\ 
                  entryUserFlag ptvaInAncestor idxva false s /\
                  isEntryPage ptvaInAncestor idxva phypage s /\
                  entryPresentFlag ptvaInAncestor idxva true s  ) 
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
      simpl.
      unfold propagatedProperties in *. 
      do 7 rewrite and_assoc.
      
      clear Hrest  Hsplit  Hprops.
      split.
      
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
      split.
      (** partitionDescriptorEntry **)
      apply partitionDescriptorEntryUpdateUserFlag;trivial.
      intuition.
      (** dataStructurePdSh1Sh2asRoot **)
      destruct Hcons as (Hpe & Hpd & Hsh1 & Hsh2 & Hcurpartlist & 
      Hnodupmapped & Hnodupconfig & Hparent & Hsh1struct).
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      split.
      apply dataStructurePdSh1Sh2asRootUpdateUserFlag;intuition.
      (** currentPartitionInPartitionsList **)
      split.
      unfold currentPartitionInPartitionsList in *.
      simpl in *. subst. 
      assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite Hpartions. assumption.
      (** noDupMappedPagesList **)  
      split.    
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
      split.
      (** noDupConfigPagesList **)
      apply getIndirectionsNoDupUpdateUserFlag; trivial.
      split.
      (** parentInPartitionList **)
      unfold parentInPartitionList in *.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart.
      intros partition HgetParts parent Hroot.
      generalize (Hparent partition HgetParts); clear Hparent; intros Hparent; trivial.
      apply  nextEntryIsPPUpdateUserFlag' in  Hroot.
      apply Hparent; trivial.
      split.
      (** accessibleVAIsNotPartitionDescriptor **)
     unfold s'.
      subst.
      clear IHn.
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (_ & Hi).
      intuition.
      subst.
      apply accessibleVAIsNotPartitionDescriptorUpdateUserFlag  with level ancestor   
        pdAncestor;trivial.
      assert(Hparentpart : parentInPartitionList s) by trivial.
      unfold parentInPartitionList in *.
      apply Hparent with descParent;trivial. 
       assert(Hget : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
      assert(  isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s ) as (_ & Hroot).
      apply Hget;split;trivial.
      assumption.
      apply nextEntryIsPPgetPd;trivial.
      subst.
      assert(HaccessInParent : isAccessibleMappedPageInParent descParent va (pa entry) s = true)
       by trivial.
       unfold isAccessibleMappedPageInParent in HaccessInParent.
       (** Here we use the property already present into the precondition : 
            *)
       assert(Hcursh2 : nextEntryIsPP descParent sh2idx sh2 s ) by trivial.
      apply nextEntryIsPPgetSndShadow in Hcursh2.
      rewrite Hcursh2 in HaccessInParent.
      assert(Hvainparent : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
      { assert(Hxx : forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx ->
        isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
        assert(Hgetva : isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\ 
        getTableAddrRoot ptsh2 sh2idx descParent va s).
        apply Hxx;trivial. clear Hxx.
        destruct Hgetva as (Hva & Hgetva).
        assert(Hisva : isVA' ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s) 
        by trivial.
        unfold getVirtualAddressSh2.
        unfold getTableAddrRoot in Hgetva.
        destruct Hgetva as (_ & Hgetva).
        assert(HcurSh2 : nextEntryIsPP descParent sh2idx sh2 s).
        rewrite  nextEntryIsPPgetSndShadow ;trivial.
        apply Hgetva in HcurSh2.
        destruct HcurSh2 as (nbL & HnbL & stop & Hstop & Hind).
        rewrite <- HnbL.
        subst.
        assert(Hgetind : getIndirection sh2 va nbL (nbLevel - 1) s = Some ptsh2).
        apply getIndirectionStopLevelGT2 with (nbL + 1);trivial.
        omega.
        apply getNbLevelEq in HnbL.
        rewrite HnbL.
        unfold CLevel.
        case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
        simpl;trivial.
        assert(0<nbLevel) by apply nbLevelNotZero.
        omega.
        rewrite Hgetind.
        assert (Hptnotnull : (defaultPage =? ptsh2) = false) by trivial.
        rewrite Hptnotnull.
        unfold  isVA' in *. 
        unfold StateLib.readVirtual. 
        destruct(lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ); 
        try now contradict Hisva.
        destruct v;try now contradict Hisva.
        subst. trivial. }
      rewrite Hvainparent in *.
      assert(Hgetparent : StateLib.getParent descParent (memory s) = Some ancestor).
      { apply nextEntryIsPPgetParent;trivial. }
      rewrite Hgetparent in *.
      assert(Hgetpdparent : StateLib.getPd ancestor (memory s) = Some pdAncestor).
      { apply nextEntryIsPPgetPd;trivial. }
      rewrite Hgetpdparent in *.
      case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor ); intros * Hi .
      rewrite Hi in *.
      unfold getAccessibleMappedPage in Hi.
      case_eq (StateLib.getNbLevel);intros * Hi2 ; rewrite Hi2 in *;
       try now contradict Hi.
      assert(Hancestor : forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by 
      trivial.
      assert(Hget : isPE ptvaInAncestor ( StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\
            getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s).
      apply Hancestor; clear Hancestor;
      trivial.
      destruct Hget as (Hva & Hget).
      unfold getTableAddrRoot in Hget.
      destruct Hget as (_ & Hget).
      apply nextEntryIsPPgetPd in Hgetpdparent.
      apply Hget in Hgetpdparent.
      destruct Hgetpdparent as (nbL & HnbL & stop & Hstop & Hgettable).
      clear Hget.
      rewrite <- HnbL in *.
      inversion Hi2.
      subst.
      assert(Hind :getIndirection pdAncestor vaInAncestor l (nbLevel - 1) s = Some ptvaInAncestor).
      apply getIndirectionStopLevelGT2 with (l+1);trivial.
      omega.
      apply getNbLevelEq in HnbL.
      rewrite HnbL.
      unfold CLevel.
      case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
      simpl;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      rewrite Hind in *.
      assert (Hnotnull : (defaultPage =? ptvaInAncestor) = false) by trivial.
      rewrite Hnotnull in *.
      destruct (StateLib.readPresent ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b; try now contradict Hi.
      destruct(StateLib.readAccessible ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
      (memory s)); try now contradict Hi.
      destruct b.
      unfold StateLib.readPhyEntry in *.
      rewrite Hlookup in *.
      symmetry; assumption.
      now contradict Hi.
      rewrite Hi in *. 
      now contradict HaccessInParent.
            rewrite Hi in *. 
      now contradict HaccessInParent.
   (* accessibleChildPageIsAccessibleIntoParent *)
      destruct Hsh1struct as (Hsh1struct & HaccessRec & Hcons1 & Hcons2).
      destruct H as ((( H & Hi ) & H1 ) & H2). 
      destruct Hi as (Hancestor & Hi).
      unfold s'.
      intuition. 
      subst.
      clear IHn.
      apply accessibleChildPageIsAccessibleIntoParentUpdateUserFlagFlase
      with level ancestor pdAncestor va ptsh2 descParent pt;trivial.
      assert(Hparentpart : parentInPartitionList s).
      unfold consistency in *; intuition.
      unfold parentInPartitionList in *.
      apply Hparentpart with descParent;trivial.
      (* noCycleInPartitionTree *)
      assert(Hdiff : noCycleInPartitionTree s) by trivial.
      unfold noCycleInPartitionTree in *.
      intros parent partition Hparts Hparentpart.
      simpl in *.
      assert (getPartitions multiplexer {|
              currentPartition := currentPartition s;
              memory := add ptvaInAncestor idxva
                          (PE
                             {|
                             read := read entry;
                             write := write entry;
                             exec := exec entry;
                             present := present entry;
                             user := false;
                             pa := pa entry |}) (memory s) beqPage beqIndex |}
               = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(HgetParent : getAncestors partition
                {|
                   currentPartition := currentPartition s;
                   memory := add ptvaInAncestor idxva
                               (PE
                                  {|
                                  read := read entry;
                                  write := write entry;
                                  exec := exec entry;
                                  present := present entry;
                                  user := false;
                                  pa := pa entry |}) (memory s) beqPage beqIndex |} = 
                      getAncestors partition  s).
      apply getAncestorsUpdateUserFlag;trivial.
      rewrite HgetParent in *; clear HgetParent.
      apply Hdiff;trivial.
      (* configTablesAreDifferent *)
      assert(Hconfigdiff : configTablesAreDifferent s) by trivial.
      unfold configTablesAreDifferent in *.
      simpl in *.
      fold s'.
      intros partition1 partition2 Hpart1 Hpart2 Hdiff.
      assert (getPartitions multiplexer s' = getPartitions multiplexer s) as HgetPart.
      apply getPartitionsUpdateUserFlag; trivial.
      rewrite HgetPart in *. clear HgetPart.
      assert(Hconfig : getConfigPages partition1 s' = getConfigPages partition1 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      assert(Hconfig : getConfigPages partition2 s' = getConfigPages partition2 s).
      apply getConfigPagesUpdateUserFlag;trivial.
      rewrite Hconfig;clear Hconfig.
      apply Hconfigdiff;trivial.
      rename H into Hcond.
      (** isChild **)
      assert(Hchid : isChild s) by intuition.
      unfold isChild in *.
      simpl in *.
      intros partition parent Hparts Hgetparent.
      rewrite getPartitionsUpdateUserFlag in *;trivial.
      rewrite getParentUpdateUserFlag in *;trivial.
      rewrite getChildrenUpdateFlagUser;trivial.
      apply Hchid;trivial.
          (** isPresentNotDefaultIff **)
    assert (Hpres : isPresentNotDefaultIff s) by intuition.
    unfold isPresentNotDefaultIff in *.
    unfold s'.
    simpl.
    intros table idx.
    rewrite readPhyEntryUpdateUserFlag;trivial.
    rewrite readPresentUpdateUserFlag;trivial.
    (** physicalPageNotDerived **)
    apply physicalPageNotDerivedUpdateUserFlag;trivial.
    (** multiplexerWithoutParent  *)
    assert(Hmult : multiplexerWithoutParent s) by trivial.
    unfold multiplexerWithoutParent in *.
    rewrite <- Hmult.
    apply getParentUpdateUserFlag;trivial.  
    (** isParent  *)
    assert(Hisparent : isParent s) by trivial.
    unfold isParent in *.
    intros parent partition Hin1 Hin2.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    simpl.
    rewrite getParentUpdateUserFlag in *;trivial.
    rewrite getChildrenUpdateFlagUser in *;trivial.
    apply Hisparent;trivial.
    (** noDupPartitionTree *)
    assert(Hnoduptree : noDupPartitionTree s) by trivial.
    unfold noDupPartitionTree in *.
    rewrite getPartitionsUpdateUserFlag in *;trivial. 
    (** wellFormedFstShadow *)
    assert(Hwell : wellFormedFstShadow s) by trivial.
    unfold wellFormedFstShadow in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr, getVirtualAddressSh1 sh1 s va0 = Some vainparent).
    apply Hwell with partition pg0 pd;trivial.
    destruct Hexist as (vainparent & Hexist).
    exists vainparent.
    rewrite <- Hexist.
    symmetry.
    apply getVirtualAddressSh1UpdateUserFlag;trivial.
    (** wellFormedSndShadow  *)
    assert(Hwell : wellFormedSndShadow s) by trivial.
    unfold wellFormedSndShadow in *.
    intros.
    simpl in *.
    rewrite getSndShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    fold s'.
    assert(Hexist : exists vainparent : vaddr,
          getVirtualAddressSh2 sh0 s va0 = Some vainparent /\ 
          beqVAddr defaultVAddr vainparent = false).
    apply Hwell with partition pg0 pd;trivial.
    destruct Hexist as (vainparent & Hexist & Hnotnul).
    exists vainparent.
    rewrite <- Hexist.
    split;trivial.
    symmetry.
    unfold s'.
    subst.
    apply getVirtualAddressSh2UpdateUserFlag;trivial.
    (** wellFormedShadows : sh1*)
    assert(Hwell : wellFormedShadows sh1idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh1idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedShadows : sh2*)
    assert(Hwell : wellFormedShadows sh2idx s ) by trivial.
    unfold wellFormedShadows in *.
    intros.
    rewrite getIndirectionUpdateUserFlag in *;trivial.
    simpl in *.
    rewrite getPdUpdateUserFlag in *;trivial.
    assert(Hpp :   nextEntryIsPP partition sh2idx structroot s') by trivial. 
    apply nextEntryIsPPUpdateUserFlag' in Hpp.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    apply Hwell with partition pdroot indirection1;trivial.
    (** wellFormedFstShadowIfNone *)
    assert(Hwell : wellFormedFstShadowIfNone s) by trivial.
    unfold wellFormedFstShadowIfNone in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.
        (** wellFormedFstShadowIfDefaultValues *)
    assert(Hwell : wellFormedFstShadowIfDefaultValues s) by trivial.
    unfold wellFormedFstShadowIfDefaultValues in *.
    intros.
    simpl in *.
    rewrite getFstShadowUpdateUserFlag in *;trivial.
    rewrite getPdUpdateUserFlag in *;trivial.
    rewrite getPartitionsUpdateUserFlag in *;trivial.
    rewrite getMappedPageUpdateUserFlag in *;trivial.
    rewrite <- getPDFlagUpdateUserFlag ;trivial.
    rewrite <- getVirtualAddressSh1UpdateUserFlag ;trivial. 
    apply Hwell with partition pd;trivial.
  (** Propagated properties **)
      assert(Hi2 : StateLib.getIndexOfAddr va fstLevel = lastIndex) by intuition.
      {  intuition trivial. 
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
          unfold getTableAddrRoot.
          destruct H23 as (Hor & Htableroot).
          split;trivial.
          intros.         
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          left.
          clear IHn.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
(*             rewrite Hisancestor in *. *)
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages descParent s)).
            apply isConfigTable with descChild;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
            {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
             unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptRefChild (getConfigPages (currentPartition s) s)).
            apply isConfigTable with descChild;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.

            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
(** partitions are diffrent then config pages are different *)
        + assert(Hi3 : forall idx : index,
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
           unfold getTableAddrRoot.
          destruct H7 as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi4 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.
        
          generalize(Htableroot tableroot Hi4 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagSameValue;trivial.
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert (Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
                  assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages descParent s)).
            apply isConfigTable with shadow1;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
            unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptSh1Child (getConfigPages (currentPartition s) s)).
            apply isConfigTable with shadow1;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.       
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split;trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.

        assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
        unfold isAncestor in *.
        destruct Hisancestor as [Hisancestor | Hisancestor].
        - subst currentPart.
          clear IHn.
(*           rewrite Hisancestor in *. *)
          left.
          unfold consistency in *.
          assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *.
          assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages descParent s)).
          apply isConfigTable with shadow2;trivial.
          intuition. subst;trivial.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2.
        - unfold consistency in *.
          subst.
          clear IHn.
          assert(In (currentPartition s) (getPartitions multiplexer s)).
          unfold currentPartitionInPartitionsList in *.
          intuition.
          assert((currentPartition s) <> ancestor).
          { unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                        unfold consistency in *. intuition.
            apply nextEntryIsPPgetParent;trivial. }
          assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
          unfold configTablesAreDifferent in *. 
          assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
          apply Hconfigdiff;trivial.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          assert(Hin1 : In ptSh2Child (getConfigPages (currentPartition s) s)).
          apply isConfigTable with shadow2;trivial.
          intuition.
          assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
          apply isConfigTable with vaInAncestor;trivial.
          intuition.
          assert(Hparet : parentInPartitionList s) by intuition.
          unfold parentInPartitionList in *.
          apply Hparet with descParent;trivial.
          unfold disjoint in *.
          left.
          apply Hdisjoint in Hin1.
          unfold not;intros; subst.
          now contradict Hin2. 
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
           unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.       
          assert(Hi3 : nextEntryIsPP currentPart PDidx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.     
          generalize(Htableroot tableroot Hi3 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl & Hind).
          exists nbL. split;trivial.
          destruct Hind as (stop  & Hstop & Hind). 
          rewrite <- Hind.
          exists stop; split; trivial.
          apply getIndirectionUpdateUserFlag;trivial.
        + apply entryPresentFlagUpdateUserFlag;assumption.
        + apply entryUserFlagUpdateUserFlagRandomValue;trivial.
          assert(Hisancestor : isAncestor  currentPart descParent s) by trivial.
          unfold isAncestor in *.
          destruct Hisancestor as [Hisancestor | Hisancestor].
          - subst currentPart.
            clear IHn.
(*             rewrite Hisancestor in *. *)
            left.
            unfold consistency in *.
            assert(descParent <> ancestor).
            { assert(Hdiff : noCycleInPartitionTree s) by
              intuition.
              unfold noCycleInPartitionTree in *.
              unfold not;intros Hii;symmetry in Hii;contradict Hii.
              apply Hdiff;trivial.
              apply parentIsAncestor;trivial. }    
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *.
            assert(Hdisjoint : disjoint (getConfigPages descParent s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages descParent s)).
            apply isConfigTable with list;trivial.
            intuition. subst;trivial.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2.
          - unfold consistency in *.
            subst.
            clear IHn.
            assert(In (currentPartition s) (getPartitions multiplexer s)).
            unfold currentPartitionInPartitionsList in *.
            intuition.
            assert((currentPartition s) <> ancestor).
                        {  unfold not;intros Hii;symmetry in Hii;contradict Hii.
            assert (Hnocycle : noCycleInPartitionTree s) by intuition.
            unfold noCycleInPartitionTree in *.
            apply Hnocycle;trivial.
            unfold consistency in *. apply isAncestorTrans2 with descParent;trivial.  intuition. intuition.
                        unfold consistency in *. intuition.
            
            apply nextEntryIsPPgetParent;trivial. }
            assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
            unfold configTablesAreDifferent in *. 
            assert(Hdisjoint : disjoint (getConfigPages (currentPartition s) s) (getConfigPages ancestor s)).
            apply Hconfigdiff;trivial.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            assert(Hin1 : In ptConfigPagesList (getConfigPages (currentPartition s) s)).
            apply isConfigTable with list;trivial.
            intuition.
            assert(Hin2: In ptvaInAncestor (getConfigPages ancestor s)).
            apply isConfigTable with vaInAncestor;trivial.
            intuition.
            assert(Hparet : parentInPartitionList s) by intuition.
            unfold parentInPartitionList in *.
            apply Hparet with descParent;trivial.
            unfold disjoint in *.
            left.
            apply Hdisjoint in Hin1.
            unfold not;intros; subst.
            now contradict Hin2. 
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi4 : nextEntryIsPP currentPart sh1idx tableroot s') by intuition.
          apply nextEntryIsPPUpdateUserFlag' in Hi4.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.    
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.      
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.
         
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
                     unfold getTableAddrRoot.
          destruct H7' as (Hor & Htableroot).
          split;trivial.
          intros.   
          assert(Hi3 : nextEntryIsPP currentPart sh1idx tableroot s') by trivial.
          apply nextEntryIsPPUpdateUserFlag' in Hi3.

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
      + assert (Hfalse' : In phyPDChild (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh1Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phySh2Child (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert (Hfalse' : In phyConfigPagesList (getConfigPagesAux partition s')); trivial.
        contradict Hfalse'.
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
      + assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
        apply getPartitionsUpdateUserFlag; trivial.
        rewrite Hpartions in *. 
        assert((getConfigPages partition s') = 
             (getConfigPages partition s)) as Hconfig.
        apply getConfigPagesUpdateUserFlag; trivial.
        rewrite Hconfig in *.
        assert(Hii : forall partition : page,
            In partition (getPartitions multiplexer s) -> 
            In phyDescChild (getConfigPages partition s) -> False) by trivial.
        assert(Hfalse' : In phyDescChild (getConfigPages partition s)) by trivial.
        apply Hii in Hfalse';trivial. 
      + unfold isPartitionFalse. 
         unfold s'.
         cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial.
      + unfold isPartitionFalse; unfold s';cbn.
         rewrite readPDflagUpdateUserFlag;trivial. 
         
(** Internal properties to propagate **)      
      + unfold s'.
        apply isAncestorUpdateUserFlag;trivial. 
      + destruct H.  
        unfold propagatedProperties in *.
        { assert(getPartitions multiplexer s' = getPartitions multiplexer s) as Hpartions.
          apply getPartitionsUpdateUserFlag; trivial.
          rewrite Hpartions; assumption. }
       
      + apply isPEUpdateUserFlag;trivial. 
          assert(Hpe : forall idx : index,
                StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ 
                getTableAddrRoot pt PDidx descParent va s) 
          by trivial.
           apply Hpe;trivial.
      +  assert(Hroot : isPE pt (StateLib.getIndexOfAddr va fstLevel ) s /\
          getTableAddrRoot pt PDidx descParent va s).
          assert(Hpe : forall idx : index,
           StateLib.getIndexOfAddr va fstLevel = idx -> isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) 
            by trivial.
          apply Hpe;trivial.
          destruct Hroot as (Hve & Hroot). 
          unfold getTableAddrRoot in *.
          destruct Hroot as (Hor & Hroot).
          split;trivial.
          intros root Hpp.
          unfold s' in Hpp.
          apply nextEntryIsPPUpdateUserFlag' in Hpp.
          apply Hroot in Hpp.
          destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
          exists nbL ; split;trivial.
          exists stop;split;trivial.
          rewrite <- Hind.
          unfold s'.
          apply getIndirectionUpdateUserFlag;trivial. 
       +  apply entryPresentFlagUpdateUserFlag;trivial. 
       + apply entryUserFlagUpdateUserFlagSameValue;trivial.
       +  apply isEntryPageUpdateUserFlag;trivial. 
       +  subst. clear IHn.       
          assert(HisAccess : isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s' =
          isAccessibleMappedPageInParent ancestor vaInAncestor (pa entry) s).
          { unfold isAccessibleMappedPageInParent.
            unfold s'.
            simpl.
            rewrite getSndShadowUpdateUserFlag;trivial.
            case_eq( StateLib.getSndShadow ancestor (memory s));
            intros * Hsh2 ;trivial.
            assert( Hvirt : getVirtualAddressSh2 p
                             {| currentPartition := currentPartition s;
                              memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                              (PE
                                 {|
                                 read := read entry;
                                 write := write entry;
                                 exec := exec entry;
                                 present := present entry;
                                 user := false;
                                 pa := pa entry |}) (memory s) beqPage beqIndex |} vaInAncestor =
                            getVirtualAddressSh2 p s vaInAncestor).
            { unfold getVirtualAddressSh2.
              assert(HnbL: Some L = StateLib.getNbLevel) by trivial.
              rewrite <- HnbL;trivial.
              rewrite getIndirectionUpdateUserFlag;trivial.
              destruct(getIndirection p vaInAncestor L (nbLevel - 1) s );trivial.
              simpl.
              rewrite readVirtualUpdateUserFlag;trivial. }
              rewrite Hvirt;trivial.
              case_eq (getVirtualAddressSh2 p s vaInAncestor );
              intros * Hvainances;trivial.
              rewrite getParentUpdateUserFlag;trivial.
              case_eq( StateLib.getParent ancestor (memory s)); 
              intros * HparentAcestor;trivial.
              rewrite getPdUpdateUserFlag.
              case_eq(StateLib.getPd p0 (memory s) );
              intros * Hpdparentances;trivial.
              assert( Haccessible : 
                        getAccessibleMappedPage p1
                          {|
                          currentPartition := currentPartition s;
                          memory := add ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                                      (PE
                                         {|
                                         read := read entry;
                                         write := write entry;
                                         exec := exec entry;
                                         present := present entry;
                                         user := false;
                                         pa := pa entry |}) (memory s) beqPage beqIndex |} v = 
                        getAccessibleMappedPage p1 s v).
              { symmetry.
                
                unfold consistency in *.
                assert (Hparentpart : parentInPartitionList s ) by  intuition.
                unfold parentInPartitionList in *.
                assert(Hancestor : In ancestor (getPartitions multiplexer s)).
                apply Hparentpart with descParent;trivial.
                apply getAccessibleMappedPageUpdateUserFlagDiffrentPartitions with ancestor p0;trivial.
                unfold consistency in *.
                intuition.
                assert(Hget : forall idx : index,
                        StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
                        isPE ptvaInAncestor idx s /\ 
                        getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
                destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
                as (Hpe & Hroot);
                trivial.
                apply Hparentpart with ancestor;trivial.
                apply nextEntryIsPPgetParent;trivial.
                assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdiff1 : p0 <> ancestor).
                              assert(Hdiff : noCycleInPartitionTree s)
                by intuition.
                unfold noCycleInPartitionTree in *.
                apply Hdiff;trivial.
                              apply parentIsAncestor.
                apply nextEntryIsPPgetParent;trivial.
              assert(Hdisjoint : configTablesAreDifferent s) by intuition.
              unfold configTablesAreDifferent in *.
              apply Hdisjoint;trivial.
              assert(Hparentinpart : parentInPartitionList s) by intuition.
              unfold parentInPartitionList in *.
              apply Hparentinpart with ancestor;trivial.
              rewrite nextEntryIsPPgetParent;trivial.
              unfold not;intros Hfalsei;subst.
              now contradict Hdiff1.
              }
              assert(Haccess : accessibleChildPageIsAccessibleIntoParent s).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold accessibleChildPageIsAccessibleIntoParent in *.
              assert(Hpde : partitionDescriptorEntry s ).
              { unfold propagatedProperties in *.
                unfold consistency in *.
                intuition. }
              unfold partitionDescriptorEntry in *.
              assert(exists entry : page, nextEntryIsPP descParent PDidx entry s /\
                      entry <> defaultPage) as (pdParent & Hpp & Hnotnull).
              apply Hpde;trivial.
              left;trivial.
              clear Hpde.
              apply nextEntryIsPPgetPd in Hpp.
              rewrite Haccessible;trivial.
              assumption. }
          rewrite HisAccess.
          assumption.
        + clear Hfalse.
          assert(Hpred :  forall partition : page,
           In partition (getAncestors currentPart s) ->
           In pg (getAccessibleMappedPages partition s) -> False ) by trivial.
          assert(Hanc: getAncestors currentPart s' = getAncestors currentPart s) by
          (apply getAncestorsUpdateUserFlag; trivial).
          rewrite Hanc in *.
          assert(Hfalse : In pg (getAccessibleMappedPages partition s')) by trivial.
          contradict Hfalse.
          assert(~ In pg (getAccessibleMappedPages partition s)).
          { unfold not; intros. apply Hpred with partition; trivial. }
          assert(Hincl : incl
          (getAccessibleMappedPages partition
           s')
          (getAccessibleMappedPages partition s)).
          apply getAccessibleMappedPagesUpdateUserFlagFalse; trivial.
          unfold incl in *.
          unfold not;intros Hfalse.
          assert(Htrue1 : ~ In pg (getAccessibleMappedPages partition s)) by 
          trivial.
          apply Htrue1.
          apply Hincl;trivial.
        + apply nextEntryIsPPUpdateUserFlag; assumption. 
        + apply isVAUpdateUserFlag; intuition.
          assert( Hisva :  forall idx : index,
                      StateLib.getIndexOfAddr va fstLevel = idx ->
                      isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
                      apply Hisva; trivial. 
        + assert ( Hi : forall idx : index,
                  StateLib.getIndexOfAddr va fstLevel = idx ->
                  isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) by trivial.
          generalize (Hi lastIndex Hi2); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split; trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.      
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          unfold getTableAddrRoot.
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
        + apply isVA'UpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + apply  nextEntryIsPPUpdateUserFlag; trivial. 
        + assert(Hi :forall idx : index,
              StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
              isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) 
              by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3);clear H7;intros (H7 & _).
          apply isPEUpdateUserFlag;assumption. 
        + assert(Hi : forall idx : index,
          StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
          isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) by trivial.
          assert(Hi3 : StateLib.getIndexOfAddr vaInAncestor fstLevel = idx) by trivial.
          generalize (Hi idx Hi3); clear H7; intros (_ & H7). 
          unfold getTableAddrRoot in *.
          destruct H7 as (Hii & Htableroot).
          split;trivial.
          intros.
          apply nextEntryIsPPUpdateUserFlag' in H7.         
          generalize(Htableroot tableroot H7 );clear Htableroot; intros Htableroot.
          destruct Htableroot as (nbL & Hnbl  & stop & Hstop & Hind).
          exists nbL. split;trivial.
          exists stop. split; trivial.
          rewrite <- Hind.
          apply getIndirectionUpdateUserFlag;trivial. 
      (** WriteAccessible property **) 
      + unfold entryUserFlag. unfold s'.
        cbn.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        rewrite Hpairs.  cbn. reflexivity. 
      + unfold isEntryPage.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  cbn. reflexivity.
      + unfold entryPresentFlag.
        unfold s'.
        assert( beqPairs (ptvaInAncestor, idxva) (ptvaInAncestor, idxva)
        beqPage beqIndex = true) as Hpairs.
        apply beqPairsTrue.  split;trivial.
        cbn.
        rewrite Hpairs.  
        cbn.
        unfold consistency in *.
        assert(Hpres : isPresentNotDefaultIff s ) by intuition.
        symmetry.
        apply phyPageIsPresent with ptvaInAncestor idxva s;trivial. }

(** setAccessible success **)
  simpl. subst. 
  (** recursion **)
  eapply weaken.
  eapply IHn.
  simpl. intros.
  assert(Hancestorpart : In ancestor (getPartitions MALInternal.multiplexer s)).
  { unfold propagatedProperties in *.
    unfold consistency in * .
    assert (Hparent : parentInPartitionList s) by intuition.
    unfold parentInPartitionList in *.
    apply Hparent with descParent; intuition. }
  assert (Hparentchild : In descParent (getChildren ancestor s)).
  unfold propagatedProperties in *.
  unfold consistency in *.
  assert(Hchildren : isChild s) by intuition.
  unfold isChild in *.
      apply Hchildren;trivial.
      intuition.
      apply nextEntryIsPPgetParent;intuition.
  assert(Hvs : verticalSharing s).
   { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. }
    unfold verticalSharing in *.
  assert(Hvsall : incl (getUsedPages descParent s) (getMappedPages ancestor s)).
  apply Hvs;trivial.
  clear Hvs.
  apply verticalSharing2 in Hvsall.
  unfold incl in *.
  generalize(Hvsall phypage);clear Hvsall; intros Hvs.
  assert(Hdescpage : In phypage (getMappedPages descParent s)).
  { intuition.
    subst.
    assert(Hpde : partitionDescriptorEntry s).
    { unfold propagatedProperties in *.
      unfold consistency in *.
      intuition. } 
    unfold partitionDescriptorEntry in *.
    assert(Hentrypd: exists entry , nextEntryIsPP descParent PDidx entry s /\ entry <> defaultPage).
    apply Hpde;trivial.
    left;trivial.
    destruct Hentrypd as (pdParent & Hpp & Hnotnul).
    apply inGetMappedPagesGetTableRoot with va pt pdParent ;trivial.
}

apply Hvs in Hdescpage.
clear Hvs.
unfold getMappedPages in *.
assert(HpdAncestor : nextEntryIsPP ancestor PDidx pdAncestor s) by intuition.
rewrite nextEntryIsPPgetPd in *.
rewrite HpdAncestor in *.
unfold getMappedPagesAux in *.

apply filterOptionInIff in Hdescpage.
unfold getMappedPagesOption in *.
apply in_map_iff in Hdescpage.
destruct Hdescpage as (newVA & Hmapped & Hinvas).
unfold getMappedPage in Hmapped.
assert(Hlevel : Some L = StateLib.getNbLevel) by intuition.
rewrite <- Hlevel in *.
case_eq(getIndirection pdAncestor newVA L (nbLevel - 1) s);[intros ptAncestor HptAncestor |
intros HptAncestor];rewrite HptAncestor in *;try now contradict Hmapped.
case_eq(defaultPage =? ptAncestor);intros Hb;rewrite Hb in *;try now contradict Hmapped.
case_eq(StateLib.readPresent ptAncestor (StateLib.getIndexOfAddr newVA fstLevel) (memory s));
[intros present Hpresent |
intros Hpresent];rewrite Hpresent in *;try now contradict Hmapped.

destruct present;[| inversion Hmapped;subst;
 rewrite isNotDefaultPageFalse in Hnotdef;
 now contradict Hnotdef].
(* assert(vaInAncestor = newVA).
{ destruct H as (((((Ha & Hk )& Hi ) & Hj ) & Hl ) & Hm).
  intuition.
  clear IHn.
  subst.
  apply eqMappedPagesEqVaddrs with phypage pdAncestor s;trivial.
  apply getMappedPageGetTableRoot with ptvaInAncestor ancestor;trivial.
  rewrite nextEntryIsPPgetPd in *;trivial.
  apply AllVAddrAll.
  apply getMappedPageGetIndirection with ancestor ptAncestor L;trivial.
    rewrite nextEntryIsPPgetPd in *;trivial.
  assert (Hnodupmapped : noDupMappedPagesList s).
  unfold consistency in *;intuition.
  unfold noDupMappedPagesList in *.
  assert(Hnewnodup : NoDup (getMappedPages ancestor s)).
  apply Hnodupmapped;trivial.
  unfold getMappedPages in Hnewnodup.
  rewrite HpdAncestor in *.
  unfold getMappedPagesAux  in *.
  assumption. } *)
instantiate(1:= phypage).
instantiate (1:= StateLib.getIndexOfAddr vaInAncestor fstLevel).
instantiate (1:= ptvaInAncestor).

  split.
 intuition.
 split.
 assert(Hisancestor : isAncestor currentPart descParent s) by intuition.
 rewrite nextEntryIsPPgetParent in *.

unfold propagatedProperties in *. unfold consistency in *.  apply isAncestorTrans with descParent;intuition. 
            unfold consistency in *. intuition.
            
     unfold propagatedProperties in *.
            intuition.
            subst. trivial.
            unfold consistency in *.
            intuition. 
intuition.
 intuition.
 subst;trivial.
   subst;trivial.
  subst;trivial. }
 

(** setAccessible failed **)
 intros.
  eapply weaken.
  eapply WP.ret.
  intros.
  simpl. intuition.
Qed. 
