(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2018)                 *)
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
    This file contains the invariant of [prepare]. 
    We prove that this PIP service preserves the isolation property *)

Require Import Model.ADT Model.Hardware Core.Services Core.Internal Isolation Consistency  
WeakestPreconditions Invariants StateLib Model.Lib Model.MAL GetTableAddr 
InternalLemmas DependentTypeLemmas LinkedListConfig PropagatedProperties 
WriteAccessibleFalse WriteAccessibleRecPrepare InitPEntryTable UpdateMappedPageContent
InitFstShadow InitSndShadow UpdateShadow1StructurePrepare InsertEntryIntoLL.

Require Import Omega Bool List Coq.Logic.ProofIrrelevance.
(************************** TO MOVE ******************************)
(*%%%%%%%%%%%%Consistency%%%%%%%%%%%*)

(*******************************************************************)


(* We need  descChild as a virtual address to set up a correct sharing configuration into the parent partition*)
Lemma prepareRec (descChild : vaddr) (descChildphy phyPDChild phySh1Child phySh2Child LLChildphy fstLL: page)  (vaToPrepare : vaddr) 
(fstVA : vaddr) (l:level) :
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s 
/\ In descChildphy (getPartitions multiplexer s) /\
indirectionDescription s descChildphy phyPDChild PDidx vaToPrepare l /\
indirectionDescription s descChildphy phySh1Child sh1idx vaToPrepare l /\
indirectionDescription s descChildphy phySh2Child sh2idx vaToPrepare l /\
getConfigTablesLinkedList descChildphy (memory s) = Some fstLL /\
In LLChildphy (getLLPages fstLL s (nbPage + 1))
     }} 
prepareRec (nbLevel+1) descChild descChildphy phyPDChild phySh1Child phySh2Child LLChildphy vaToPrepare fstVA l
{{fun _ s  => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
assert(Hsize : nbLevel   <= nbLevel) by omega.
assert (Hlevelind : l < nbLevel).
destruct l. simpl;omega.
revert Hsize Hlevelind.
revert phyPDChild phySh1Child phySh2Child LLChildphy l.
generalize nbLevel at 1 3 4.
induction n; simpl.
+ intros. destruct l.
  simpl in *.
  now contradict Hlevelind.
+ intros.
  (** Level.eqb **)
  eapply WP.bindRev.
  eapply WP.weaken. 
  eapply Invariants.Level.eqb.
  simpl;intros. 
  pattern s in H. 
  eexact H.
  intro islevel0.
  simpl.
  case_eq (islevel0);intros;subst.
  (** prepareType true defaultVAddr **)
  (* 1 *)
  unfold prepareType.
  eapply weaken.
  eapply WP.ret.
  simpl.
  intros.
  intuition.
  (* 2 *)
  (** compareVAddrToNull **) 
  eapply WP.bindRev.
  eapply Invariants.compareVAddrToNull.
  intro fstVAIsnull. simpl.
  case_eq fstVAIsnull.
  (* 1 : prepareType false defaultVAddr *)
  intros.
  eapply WP.weaken.
  eapply WP.ret .
  simpl. intros.
  intuition.
  (* 2 *)
  intros fstVAnotnull. 
  subst.
  (** getCurPartition **)
  eapply WP.bindRev.
  eapply WP.weaken. 
  eapply Invariants.getCurPartition .
  cbn. 
  intros. 
  pattern s in H. 
  eexact H.
  intro currentPart.
  (** getPd **)
  eapply bindRev.
  eapply WP.weaken. 
  eapply Invariants.getPd.
  cbn.
  intros s H.
  split.
  pattern s in H.
  eexact H.
  split.
  unfold consistency in *.
  unfold partitionDescriptorEntry in *.
  intuition.
  simpl.
  unfold consistency in *.
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  intros currentPD.
 (** getFstShadow **)
  eapply bindRev.
  eapply WP.weaken. 
  eapply Invariants.getFstShadow. cbn.
  intros s H.
  split.
  pattern s in H.
  eexact H.
  unfold consistency in *.
  unfold partitionDescriptorEntry in *.
  intuition.
  simpl.
  intros currentShadow1.
  (** getSndShadow **)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.getSndShadow.
  simpl;intros.
  split.
  pattern s in H. 
  exact H.
  split. trivial.
  unfold consistency in *.
  unfold partitionDescriptorEntry in *.
  intuition.
  simpl.
  unfold consistency in *.
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  intros currentShadow2.
  simpl.
  (** StateLib.getIndexOfAddr **)                
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getIndexOfAddr.
  { simpl. intros.
    pattern s in H.
    eexact H.  }
  intro idxToPrepare. simpl.
  (** readPhyEntry **)
  eapply bindRev.
  eapply WP.weaken.
  eapply Invariants.readPhyEntry. 
  simpl. intros.
  split.
  pattern s in H. eapply H.
  clear IHn.
  repeat rewrite and_assoc in H.
  assert (Hindirection: indirectionDescription s descChildphy phyPDChild PDidx vaToPrepare l  ) by intuition.
  destruct Hindirection as (childpd & Hcurpd & Hpdnotnull  &   [Hindirection | Hindirection]);    
  subst.
  intuition;subst;trivial. 
  eapply fstIndirectionContainsPENbLevelGT1  with (idxroot:= PDidx) (l:=l) 
   (currentPart:= descChildphy);intuition.
  unfold consistency in *;intuition.
  eapply middleIndirectionsContainsPE  with (idxroot:= PDidx) (l0:=l) 
    (currentPart:= descChildphy) (rootind:=childpd) (va:=vaToPrepare);intuition.
  unfold consistency in *;intuition.    
  intros indMMUToPrepare.
  eapply WP.bindRev. 
  (** comparePageToNull **)
  eapply WP.weaken.
  eapply Invariants.comparePageToNull.
  simpl. intros.
  pattern s in H.
  eapply H.
  intros isNull.
  case_eq (negb isNull).
  - (* This MMU level is already configued *)
    intros Hnextindisnotnull.
    apply negb_true_iff in Hnextindisnotnull.
    subst.
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply Invariants.Level.pred.
    intros.
    simpl.
    split.
    pattern s in H.
    eapply H.
    assert ( false = StateLib.Level.eqb l fstLevel) as Hnotfstlevel by intuition.
    apply levelEqBEqNatFalse0;trivial.
    symmetry;trivial.
    intros levelpred.
    (** readPhyEntry : sh1**)
    eapply bindRev.
    eapply WP.weaken.
    eapply Invariants.readPhyEntry. 
    simpl. intros.
    split.
    pattern s in H. eapply H.
    clear IHn.
    repeat rewrite and_assoc in H.
    assert (Hindirection: indirectionDescription s descChildphy  phySh1Child sh1idx vaToPrepare l  ) by intuition.
    destruct Hindirection as (childpd & Hcurpd & Hpdnotnull  &   [Hindirection | Hindirection]);    
    subst.
    intuition;subst;trivial. 
    eapply fstIndirectionContainsPENbLevelGT1  with (idxroot:= sh1idx) (l:=l) 
     (currentPart:= descChildphy);intuition.
    unfold consistency in *;intuition.
    eapply middleIndirectionsContainsPE  with (idxroot:= sh1idx) (l0:=l) 
      (currentPart:= descChildphy) (rootind:=childpd) (va:=vaToPrepare);intuition.
    unfold consistency in *;intuition.    
    intros indSh1ToPrepare.
    eapply WP.bindRev.     
    (** readPhyEntry : sh2**)
    eapply WP.weaken.
    eapply Invariants.readPhyEntry. 
    simpl. intros.
    split.
    pattern s in H. eapply H.
    clear IHn.
    repeat rewrite and_assoc in H.
    assert (Hindirection: indirectionDescription s descChildphy  phySh2Child sh2idx vaToPrepare l  ) by intuition.
    destruct Hindirection as (childpd & Hcurpd & Hpdnotnull  &   [Hindirection | Hindirection]);    
    subst.
    intuition;subst;trivial. 
    eapply fstIndirectionContainsPENbLevelGT1  with (idxroot:= sh2idx) (l:=l) 
     (currentPart:= descChildphy);intuition.
    unfold consistency in *;intuition.
    eapply middleIndirectionsContainsPE  with (idxroot:= sh2idx) (l0:=l) 
      (currentPart:= descChildphy) (rootind:=childpd) (va:=vaToPrepare);intuition.
    unfold consistency in *;intuition.    
    intros indSh2ToPrepare.
    simpl.
    unfold hoareTriple.
    intros.
    assert(Hkey: levelpred < n).

assert(Hlevelpred:  StateLib.Level.pred l = Some levelpred) by intuition.
  assert(Hkey : levelpred < l).
  apply levelPredLt;trivial.
  intuition.
  omega.
    generalize (IHn indMMUToPrepare indSh1ToPrepare indSh2ToPrepare  LLChildphy levelpred  );clear IHn;intro IHn.
    unfold hoareTriple in IHn.
    intros.
    eapply IHn;trivial.
    omega.
    
    intuition.
    (* MMU data structure *)
    * assert(Hdesc :  indirectionDescription s descChildphy phyPDChild PDidx vaToPrepare l) by trivial.
    unfold indirectionDescription.
    unfold indirectionDescription in Hdesc.
    destruct Hdesc as ( pd & idxpd & ( Hnotnull & 
                            [(Hpd & Hlvl) | (nbL & stop & Hnbl &Hstople &Hind & Hindnotnull & Hstop)])).
    { (* root *) 
      exists pd. subst. 
      split;trivial.
      split;trivial.
      right.
      exists l, 1.
      split;trivial.
      subst.
      split.
      assert(Hnotfstlevel :false = StateLib.Level.eqb l fstLevel) by trivial. 
      symmetry in Hnotfstlevel. 
      apply levelEqBEqNatFalse0 in Hnotfstlevel.
      destruct l. omega.
      split.
      assert(Hentrypage : isEntryPage phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s) by trivial.
      unfold isEntryPage in Hentrypage.
      case_eq (lookup phyPDChild (StateLib.getIndexOfAddr vaToPrepare l)  (memory s) beqPage beqIndex);
      [intros v Hcase | intros Hcase];rewrite Hcase in Hentrypage;
      [ destruct v as [ p |v|p|v|i]; [ trivial | now contradict Hentrypage | 
                      now contradict Hentrypage| now contradict Hentrypage| now contradict Hentrypage ] | now contradict Hentrypage] .
      subst.   
      apply getIndirectionStop1   with (StateLib.getIndexOfAddr vaToPrepare l) ; try assumption.
      symmetry; assumption.
      trivial.
      split.
      unfold not.
      intros Hfalse1.
      assert(Hfalse : (defaultPage =? indMMUToPrepare) = false) by trivial.
      apply beq_nat_false in Hfalse.
      rewrite Hfalse1 in Hfalse. 
      now contradict Hfalse.
      apply levelPredMinus1. symmetry;trivial. trivial. }
    { (* middle *)
      exists pd. subst. 
      split;trivial. split;trivial.
      right.
      exists nbL, (stop +1).
      split;trivial.
      split.
      assert(Hnotfstlevel : false = StateLib.Level.eqb (CLevel (nbL - stop)) fstLevel) by trivial.
      symmetry in Hnotfstlevel.
      apply levelEqBEqNatFalse0 in Hnotfstlevel.
      assert(nbL - stop < nbLevel).
      destruct nbL.
      simpl in *.
      omega.
      apply level_gt in Hnotfstlevel.
      omega. assumption.
      split.  
      subst.
      assert(Hentrypage : isEntryPage phyPDChild (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indMMUToPrepare s) by trivial.
      unfold isEntryPage in Hentrypage.
      case_eq (lookup phyPDChild (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop)))  
      (memory s) beqPage beqIndex); [intros v Hcase | intros Hcase]; rewrite Hcase in Hentrypage; 
      [ destruct v as [ p |v|p|v|i]; [ trivial | now contradict Hentrypage | 
                now contradict Hentrypage| now contradict Hentrypage| now contradict Hentrypage] | now contradict Hentrypage] .
      subst.
      apply getIndirectionProp with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) phyPDChild;trivial.
      assert(Hnotfstlevel : false = StateLib.Level.eqb (CLevel (nbL - stop)) fstLevel) by trivial.
      symmetry in Hnotfstlevel.
      apply levelEqBEqNatFalse0 in Hnotfstlevel.
      unfold CLevel in Hnotfstlevel.
      case_eq (lt_dec (nbL - stop) nbLevel).
      intros l Hstop.
      rewrite Hstop in Hnotfstlevel.
      simpl in *. omega.
      intros n0 Hfalse.
      rewrite Hfalse  in Hnotfstlevel.
      unfold StateLib.getNbLevel in Hnbl.
      case_eq ( gt_dec nbLevel 0);
      [intros v Hnblnot0 | intro Hnblnot0] .
      rewrite Hnblnot0 in Hnbl.
      inversion Hnbl. clear Hnbl. subst.
      simpl in *.
      contradict Hfalse.
      omega.
      intros Hright.
      rewrite Hright in Hnbl.
      simpl in *.
      inversion Hnbl.
      symmetry. assumption.
      split.
      unfold not.
      intros Hfalse1.
      assert(Hfalse : (defaultPage =? indMMUToPrepare) = false) by trivial.
      apply beq_nat_false in Hfalse.
      rewrite Hfalse1 in Hfalse. 
      now contradict Hfalse.
      rewrite NPeano.Nat.sub_add_distr.
      set (aux := nbL - stop) in *.
      assert (Haux : aux = CLevel aux ).
      { unfold CLevel.
      case_eq ( lt_dec aux nbLevel ).
      intros.
      simpl. intuition.
      intros. contradict H.
      unfold aux in *. cbn.
      destruct nbL.
      simpl in *. omega. }      
      rewrite Haux.
      apply levelPredMinus1 ;trivial.
      symmetry; assumption. }
    (* sh1 data structure *)
    * assert(Hdesc :  indirectionDescription s descChildphy phySh1Child sh1idx vaToPrepare l) by trivial.
      unfold indirectionDescription.
      unfold indirectionDescription in Hdesc.   
      destruct Hdesc as ( root  & idxroot & ( Hnotnull & 
                            [(Hroot & Hlvl) | (nbL & stop & Hnbl &Hstople &Hind & Hindnotnull & Hstop)])).
      { (* root *) 
        exists root. subst. 
        split;trivial.
        split;trivial.
        right.
        exists l, 1.
        split;trivial.
        subst.
        split.
        assert(Hnotfstlevel :false = StateLib.Level.eqb l fstLevel) by trivial. 
        symmetry in Hnotfstlevel. 
        apply levelEqBEqNatFalse0 in Hnotfstlevel.
        destruct l. omega.
        split.
        assert(Hentrypage : isEntryPage phySh1Child (StateLib.getIndexOfAddr vaToPrepare l) indSh1ToPrepare s) by trivial.
        unfold isEntryPage in Hentrypage.
        case_eq (lookup phySh1Child (StateLib.getIndexOfAddr vaToPrepare l)  (memory s) beqPage beqIndex);
        [intros v Hcase | intros Hcase];rewrite Hcase in Hentrypage;
        [ destruct v as [ p |v|p|v|i]; [ trivial | now contradict Hentrypage | 
                        now contradict Hentrypage| now contradict Hentrypage| now contradict Hentrypage ] | now contradict Hentrypage] .
        subst.   
        apply getIndirectionStop1   with (StateLib.getIndexOfAddr vaToPrepare l) ; try assumption.
        symmetry; assumption.
        trivial.
        split.
        unfold not.
        intros Hfalse1.
        assert(Hfalse : (defaultPage =? indSh1ToPrepare) = false).
        apply InternalLemmas.structIndirectionIsnotnull with indMMUToPrepare phySh1Child descChildphy phyPDChild vaToPrepare l levelpred sh1idx s;trivial.
        left;trivial.
        apply beq_nat_false in Hfalse.
        rewrite Hfalse1 in Hfalse. 
        now contradict Hfalse.
        apply levelPredMinus1. symmetry;trivial. trivial. }
      { (* middle *)
        exists root. subst. 
        split;trivial. split;trivial.
        right.
        exists nbL, (stop +1).
        split;trivial.
        split.
        assert(Hnotfstlevel : false = StateLib.Level.eqb (CLevel (nbL - stop)) fstLevel) by trivial.
        symmetry in Hnotfstlevel.
        apply levelEqBEqNatFalse0 in Hnotfstlevel.
        assert(nbL - stop < nbLevel).
        destruct nbL.
        simpl in *.
        omega.
        apply level_gt in Hnotfstlevel.
        omega. assumption.
        split.  
        subst.
        assert(Hentrypage : isEntryPage phySh1Child (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indSh1ToPrepare s) by trivial.
        unfold isEntryPage in Hentrypage.
        case_eq (lookup phySh1Child (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop)))  
        (memory s) beqPage beqIndex); [intros v Hcase | intros Hcase]; rewrite Hcase in Hentrypage; 
        [ destruct v as [ p |v|p|v|i]; [ trivial | now contradict Hentrypage | 
                  now contradict Hentrypage| now contradict Hentrypage| now contradict Hentrypage] | now contradict Hentrypage] .
        subst.
        apply getIndirectionProp with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) phySh1Child;trivial.
        assert(Hnotfstlevel : false = StateLib.Level.eqb (CLevel (nbL - stop)) fstLevel) by trivial.
        symmetry in Hnotfstlevel.
        apply levelEqBEqNatFalse0 in Hnotfstlevel.
        unfold CLevel in Hnotfstlevel.
        case_eq (lt_dec (nbL - stop) nbLevel).
        intros l Hstop.
        rewrite Hstop in Hnotfstlevel.
        simpl in *. omega.
        intros n0 Hfalse.
        rewrite Hfalse  in Hnotfstlevel.
        unfold StateLib.getNbLevel in Hnbl.
        case_eq ( gt_dec nbLevel 0);
        [intros v Hnblnot0 | intro Hnblnot0] .
        rewrite Hnblnot0 in Hnbl.
        inversion Hnbl. clear Hnbl. subst.
        simpl in *.
        contradict Hfalse.
        omega.
        intros Hright.
        rewrite Hright in Hnbl.
        simpl in *.
        inversion Hnbl.
        symmetry. assumption.
        split.
        unfold not.
        intros Hfalse1.
        assert(Hfalse : (defaultPage =? indSh1ToPrepare) = false).
        { apply structIndirectionIsnotnullMiddle  with
         indMMUToPrepare phySh1Child descChildphy phyPDChild vaToPrepare nbL levelpred stop  sh1idx s;trivial.
         left;trivial.
}
        apply beq_nat_false in Hfalse.
        rewrite Hfalse1 in Hfalse. 
        now contradict Hfalse.
        rewrite NPeano.Nat.sub_add_distr.
        set (aux := nbL - stop) in *.
        assert (Haux : aux = CLevel aux ).
        { unfold CLevel.
        case_eq ( lt_dec aux nbLevel ).
        intros.
        simpl. intuition.
        intros. contradict H.
        unfold aux in *. cbn.
        destruct nbL.
        simpl in *. omega. }
        rewrite Haux.
        apply levelPredMinus1 ;trivial.
        symmetry; assumption. }
    (* sh2 data structure *)
    * assert(Hdesc :  indirectionDescription s descChildphy phySh2Child sh2idx vaToPrepare l) by trivial.
      unfold indirectionDescription.
      unfold indirectionDescription in Hdesc.   
      destruct Hdesc as ( root  & idxroot & ( Hnotnull & 
                            [(Hroot & Hlvl) | (nbL & stop & Hnbl &Hstople &Hind & Hindnotnull & Hstop)])).
      { (* root *) 
        exists root. subst. 
        split;trivial.
        split;trivial.
        right.
        exists l, 1.
        split;trivial.
        subst.
        split.
        assert(Hnotfstlevel :false = StateLib.Level.eqb l fstLevel) by trivial. 
        symmetry in Hnotfstlevel. 
        apply levelEqBEqNatFalse0 in Hnotfstlevel.
        destruct l. omega.
        split.
        assert(Hentrypage : isEntryPage phySh2Child (StateLib.getIndexOfAddr vaToPrepare l) indSh2ToPrepare s) by trivial.
        unfold isEntryPage in Hentrypage.
        case_eq (lookup phySh2Child (StateLib.getIndexOfAddr vaToPrepare l)  (memory s) beqPage beqIndex);
        [intros v Hcase | intros Hcase];rewrite Hcase in Hentrypage;
        [ destruct v as [ p |v|p|v|i]; [ trivial | now contradict Hentrypage | 
                        now contradict Hentrypage| now contradict Hentrypage| now contradict Hentrypage ] | now contradict Hentrypage] .
        subst.   
        apply getIndirectionStop1   with (StateLib.getIndexOfAddr vaToPrepare l) ; try assumption.
        symmetry; assumption.
        trivial.
        split.
        (** Here we use the consistency property wellFormedShadows to prove that the second 
        shadow data structure follows the same configuration as the MMU *)
        assert(Hfalse : (defaultPage =? indSh2ToPrepare) = false).
        apply structIndirectionIsnotnull with indMMUToPrepare phySh2Child descChildphy phyPDChild vaToPrepare l levelpred sh2idx s;trivial.
        right;trivial.
        unfold not;intros.
        subst.
        rewrite <- beq_nat_refl in Hfalse.
        intuition. 
        apply levelPredMinus1. symmetry;trivial. trivial. }
      { (* middle *)
        exists root. subst. 
        split;trivial. split;trivial.
        right.
        exists nbL, (stop +1).
        split;trivial.
        split.
        assert(Hnotfstlevel : false = StateLib.Level.eqb (CLevel (nbL - stop)) fstLevel) by trivial.
        symmetry in Hnotfstlevel.
        apply levelEqBEqNatFalse0 in Hnotfstlevel.
        assert(nbL - stop < nbLevel).
        destruct nbL.
        simpl in *.
        omega.
        apply level_gt in Hnotfstlevel.
        omega. assumption.
        split.  
        subst.
        assert(Hentrypage : isEntryPage phySh2Child (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indSh2ToPrepare s) by trivial.
        unfold isEntryPage in Hentrypage.
        case_eq (lookup phySh2Child (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop)))  
        (memory s) beqPage beqIndex); [intros v Hcase | intros Hcase]; rewrite Hcase in Hentrypage; 
        [ destruct v as [ p |v|p|v|i]; [ trivial | now contradict Hentrypage | 
                  now contradict Hentrypage| now contradict Hentrypage| now contradict Hentrypage] | now contradict Hentrypage] .
        subst.
        apply getIndirectionProp with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) phySh2Child;trivial.
        assert(Hnotfstlevel : false = StateLib.Level.eqb (CLevel (nbL - stop)) fstLevel) by trivial.
        symmetry in Hnotfstlevel.
        apply levelEqBEqNatFalse0 in Hnotfstlevel.
        unfold CLevel in Hnotfstlevel.
        case_eq (lt_dec (nbL - stop) nbLevel).
        intros l Hstop.
        rewrite Hstop in Hnotfstlevel.
        simpl in *. omega.
        intros n0 Hfalse.
        rewrite Hfalse  in Hnotfstlevel.
        unfold StateLib.getNbLevel in Hnbl.
        case_eq ( gt_dec nbLevel 0);
        [intros v Hnblnot0 | intro Hnblnot0] .
        rewrite Hnblnot0 in Hnbl.
        inversion Hnbl. clear Hnbl. subst.
        simpl in *.
        contradict Hfalse.
        omega.
        intros Hright.
        rewrite Hright in Hnbl.
        simpl in *.
        inversion Hnbl.
        symmetry. assumption.
        split.
        unfold not.
        intros Hfalse1.
        assert(Hfalse : (defaultPage =? indSh2ToPrepare) = false).
        { apply structIndirectionIsnotnullMiddle  with
         indMMUToPrepare phySh2Child descChildphy phyPDChild vaToPrepare nbL levelpred stop  sh2idx s;trivial.
         right;trivial.
}
        apply beq_nat_false in Hfalse.
        rewrite Hfalse1 in Hfalse. 
        now contradict Hfalse.
        rewrite NPeano.Nat.sub_add_distr.
        set (aux := nbL - stop) in *.
        assert (Haux : aux = CLevel aux ).
        { unfold CLevel.
        case_eq ( lt_dec aux nbLevel ).
        intros.
        simpl. intuition.
        intros. contradict H.
        unfold aux in *. cbn.
        destruct nbL.
        simpl in *. omega. }
        rewrite Haux.
        apply levelPredMinus1 ;trivial.
        symmetry; assumption. } 
  - (* This MMU level is not configued *)
    intros Hnull.
    apply negb_false_iff in Hnull.
    subst.
  (** getNbLevel **)
    eapply WP.bindRev.
    eapply weaken.
    eapply Invariants.getNbLevel.
    simpl. intros.
    pattern s in H.
    eexact H.
    intros nbLgen.
  (** getStoreFetchIndex **)
    simpl.
    eapply bindRev.
    unfold getStoreFetchIndex.
    eapply WP.weaken.
    eapply Invariants.ret .
    intros.
    simpl.
    eapply H. 
    intros idxstorefetch.
  (** StateLib.getIndexOfAddr **)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getIndexOfAddr.
  { simpl. intros.
    pattern s in H.
    eexact H.  }
  intro idxFstVA.
  simpl.  
  (** getTableAddr **)
  eapply WP.bindRev.
  eapply WP.weaken. 
  apply getTableAddr.
  simpl.
  intros s H.  
  split. 
  pattern s in H. 
  eexact H. subst.
  split. 
  intuition.
  split. 
  instantiate (1:= currentPart).
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  instantiate (1:= PDidx).
  split. intuition.
  assert(Hcons : consistency s) by intuition.
  assert(Hlevel : Some nbLgen = StateLib.getNbLevel) by intuition. 
  assert(Hcp : currentPart = currentPartition s) by intuition.
  assert (H0 : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
  exists currentPD.
  split. intuition.
  unfold consistency in *.
  destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
  unfold partitionDescriptorEntry in Hpd.
  assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/  PDidx  = sh3idx
  \/  PDidx  = PPRidx \/  PDidx = PRidx) as Htmp 
  by auto.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
  generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
  destruct Hpd as (Hidxpd & _& Hentry). 
  destruct Hentry as (page1 & Hpd & Hnotnull).
  subst.
  split. 
   unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
   [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
   as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict H0 | 
   now contradict H0 | 
   subst;assumption | now contradict H0| now contradict H0 ]  
   |now contradict H0] | now contradict H0].
  subst. left. split;intuition.
  intro ptMMUFstVA. simpl.
  (** simplify the new precondition **)
  eapply WP.weaken.
  intros.
  2: {
  intros.
  destruct H as (H0 & H1).
  assert ( (getTableAddrRoot' ptMMUFstVA PDidx currentPart fstVA s /\ ptMMUFstVA = defaultPage) \/
  (forall idx : index,
  StateLib.getIndexOfAddr fstVA fstLevel = idx ->
  isPE ptMMUFstVA idx s /\ getTableAddrRoot ptMMUFstVA PDidx currentPart fstVA s  )).
  { destruct H1 as [H1 |(Hi & Hi1 & H1)].
    + left. trivial. 
    + right. intros idx Hidx.
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
      - (*  split; assumption.
      - *) contradict Htrue.
        apply idxPDidxSh1notEq.
      - contradict Hfalse.
        apply idxPDidxSh2notEq.
      - split;trivial. }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP. }
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptVaInCurPartpdIsnull. simpl.
  case_eq ptVaInCurPartpdIsnull.
  { intros. eapply WP.weaken.
    eapply WP.ret . simpl.
    intros. intuition. }
  intros HptVaInCurPartpdNotNull.
  subst.  
  (** readAccessible **)
  eapply WP.bindRev.
  { eapply WP.weaken.
    eapply Invariants.readAccessible. simpl.
    intros.
    destruct H as ((Ha1 & Ha3) & Ha4).
    assert (Hnewget : isPE ptMMUFstVA (
    StateLib.getIndexOfAddr fstVA fstLevel) s /\
         getTableAddrRoot ptMMUFstVA PDidx currentPart fstVA s /\ 
         (defaultPage =? ptMMUFstVA) = false).
    { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
      + subst.
        apply beq_nat_false in Ha4.
        now contradict Ha4.
      + destruct Ha3 with (StateLib.getIndexOfAddr fstVA fstLevel);trivial.
        intuition. }
     subst.
   split.
    assert (HP := conj Ha1 Hnewget).
    pattern s in HP.
    eexact HP. clear Ha3. 
    intuition. subst;trivial. }
  intros fstVAisAccessible. simpl.
  case_eq(negb fstVAisAccessible);intros Haccess.
  intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition.
(** readPresent **)
  eapply WP.bindRev.
  { eapply WP.weaken.
    eapply Invariants.readPresent. simpl.
    intros.
    split.
    pattern s in H.
    eexact H. 
    intuition. subst;trivial. }
  intros fstVAisPresent. simpl.
  apply negb_false_iff in Haccess;subst.
  case_eq(negb fstVAisPresent);intros Hpres.
  intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition.
  apply negb_false_iff in Hpres;subst.
(** readPhyEntry **)
  eapply WP.bindRev.
  { eapply WP.weaken.
    eapply Invariants.readPhyEntry. simpl.
    intros.
    split.
    pattern s in H.
    eapply H. 
    subst.
    intuition;subst;trivial. }
  intros phyMMUaddr. simpl.
(** readVirtualUser **)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.readVirtualUser.
  simpl.
  intros.
  apply H.
  simpl.
  intros sndVA.
(** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.compareVAddrToNull.
  intro sndvaisnull. simpl.
  case_eq sndvaisnull.
  { intros. eapply WP.weaken.
    eapply WP.ret . simpl.
    intros. intuition. }
  intros.
  subst.
  (** StateLib.getIndexOfAddr **)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getIndexOfAddr.
  { simpl. intros.
    pattern s in H.
    eexact H.  }
  intro idxSndVA.
  simpl.    
  (** getTableAddr **)
  eapply WP.bindRev.
  eapply WP.weaken. 
  apply getTableAddr.
  simpl.
  intros s H.  
  split. 
  pattern s in H. 
  eexact H. subst.
  split. 
  intuition.
  split. 
  instantiate (1:= currentPart).
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  instantiate (1:= PDidx).
  split. intuition.
  assert(Hcons : consistency s) by intuition.
  assert(Hlevel : Some nbLgen = StateLib.getNbLevel) by intuition. 
  assert(Hcp : currentPart = currentPartition s) by intuition.
  assert (H0 : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
  exists currentPD.
  split. intuition.
  unfold consistency in *.
  destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
  unfold partitionDescriptorEntry in Hpd.
  assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/  PDidx  = sh3idx
  \/  PDidx  = PPRidx \/  PDidx = PRidx) as Htmp 
  by auto.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
  generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
  destruct Hpd as (Hidxpd & _& Hentry). 
  destruct Hentry as (page1 & Hpd & Hnotnull).
  subst.
  split. 
   unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
   [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
   as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict H0 | 
   now contradict H0 | 
   subst;assumption | now contradict H0| now contradict H0 ]  
   |now contradict H0] | now contradict H0].
  subst. left. split;intuition.
  intro ptMMUSndVA. simpl.
  (** simplify the new precondition **)
  eapply WP.weaken.
  intros.
  2: {
  intros.
  destruct H as (H0 & H1).
  assert ( (getTableAddrRoot' ptMMUSndVA PDidx currentPart sndVA s /\ ptMMUSndVA = defaultPage) \/
  (forall idx : index,
  StateLib.getIndexOfAddr sndVA fstLevel = idx ->
  isPE ptMMUSndVA idx s /\ getTableAddrRoot ptMMUSndVA PDidx currentPart sndVA s  )).
  { destruct H1 as [H1 |(Hi & Hi1 & H1)].
    + left. trivial. 
    + right. intros idx Hidx.
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
      - (*  split; assumption.
      - *) contradict Htrue.
        apply idxPDidxSh1notEq.
      - contradict Hfalse.
        apply idxPDidxSh2notEq.
      - split;trivial. }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP. }
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptVaInCurPartpdIsnull. simpl.
  case_eq ptVaInCurPartpdIsnull.
  { intros. eapply WP.weaken.
    eapply WP.ret . simpl.
    intros. intuition. }
  intros HptVaInCurPartpdNotNull.
  subst.  
  (** readAccessible **)
  eapply WP.bindRev.
  { eapply WP.weaken.
    eapply Invariants.readAccessible. simpl.
    intros.
    destruct H as ((Ha1 & Ha3) & Ha4).
    assert (Hnewget : isPE ptMMUSndVA (
    StateLib.getIndexOfAddr sndVA fstLevel) s /\
         getTableAddrRoot ptMMUSndVA PDidx currentPart sndVA s /\ 
         (defaultPage =? ptMMUSndVA) = false).
    { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
      + subst.
        apply beq_nat_false in Ha4.
        now contradict Ha4.
      + destruct Ha3 with (StateLib.getIndexOfAddr sndVA fstLevel);trivial.
        intuition. }
     subst.
   split.
    assert (HP := conj Ha1 Hnewget).
    pattern s in HP.
    eexact HP. clear Ha3. 
    intuition. subst;trivial. }
  intros sndVAisAccessible. simpl.
  case_eq(negb sndVAisAccessible);intros Haccess.
  intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition.
(** readPresent **)
  eapply WP.bindRev.
  { eapply WP.weaken.
    eapply Invariants.readPresent. simpl.
    intros.
    split.
    pattern s in H.
    eexact H. 
    intuition. subst;trivial. }
  intros sndVAisPresent. simpl.
  apply negb_false_iff in Haccess;subst.
  case_eq(negb sndVAisPresent);intros Hpres.
  intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition.
  apply negb_false_iff in Hpres;subst.
(** readPhyEntry **)
  eapply WP.bindRev.
  { eapply WP.weaken.
    eapply Invariants.readPhyEntry. simpl.
    intros.
    split.
    pattern s in H.
    eapply H. 
    subst.
    intuition;subst;trivial. }
  intros phySh1addr. simpl.
(** readVirtualUser **)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.readVirtualUser.
  simpl.
  intros.
  apply H.
  simpl.
  intros trdVA.
(** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.compareVAddrToNull.
  intro sndvaisnull. simpl.
  case_eq sndvaisnull.
  { intros. eapply WP.weaken.
    eapply WP.ret . simpl.
    intros. intuition. }
  intros.
  subst.   
(** Index.zero *) 
  eapply bindRev.
  eapply weaken.
  eapply Invariants.Index.zero.
  intros.
  simpl.
  eapply H.
  intros zeroI.
  simpl.
(** checkVAddrsEqualityWOOffset *)
  repeat (eapply WP.bindRev; [ eapply WP.weaken ; 
                [ apply Invariants.checkVAddrsEqualityWOOffset | intros ; simpl; pattern s in H; eapply H ] 
                                  | simpl; intros  ]).
  case_eq (a || a0 || a1 ); intros Hvaddrs.
  eapply WP.weaken.
  eapply WP.ret.
  intros.
  simpl. intuition.
  try repeat rewrite orb_false_iff in Hvaddrs.
  try repeat rewrite and_assoc in Hvaddrs.
  intuition.
  subst.
(** getTableAddr **)
  eapply WP.bindRev.
  eapply WP.weaken. 
  apply getTableAddr.
  simpl.
  intros s H.
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
  instantiate (1:= sh1idx).
  split. intuition.
  assert(Hcons : consistency s) by intuition.
  assert(Hlevel : Some nbLgen = StateLib.getNbLevel) by intuition. 
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
  intro ptSh1FstVA.
  simpl.
(** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2: {
  intros.
  destruct H as (H0 & H1).
  assert ( (getTableAddrRoot' ptSh1FstVA sh1idx currentPart fstVA s /\ ptSh1FstVA = defaultPage) \/
 (forall idx : index,
  StateLib.getIndexOfAddr fstVA fstLevel = idx ->
  isVE ptSh1FstVA idx s /\  getTableAddrRoot ptSh1FstVA sh1idx currentPart fstVA s)).
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
  intro fstVAsh1notnull. simpl.
  case_eq fstVAsh1notnull.
  { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
  intros HfstVAsh1notnull. subst.  
(** derived **)
  eapply WP.bindRev.
  { eapply WP.weaken.
    eapply Invariants.checkDerivation. simpl.
    simpl. intros. 
    destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
    + destruct Hptchild. subst. contradict Hptchildnotnull.
      intro Hnull.  apply beq_nat_false in Hnull. intuition.
    + subst.
      destruct Hptchild with (StateLib.getIndexOfAddr fstVA fstLevel) as (Hve & Htbl);
      trivial.
      assert (HP := conj (conj (conj H Hve) Htbl) Hptchildnotnull).
      split.
      eapply HP. 
      subst.
      assert ( StateLib.getIndexOfAddr fstVA fstLevel = idxFstVA) as Hidxchild.
      intuition.
      apply Hptchild in Hidxchild. destruct Hidxchild; assumption. }
  simpl. intros fstvanotshared.
(** getTableAddr **)
  eapply WP.bindRev.
  eapply WP.weaken. 
  apply getTableAddr.
  simpl.
  intros s H.
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
  instantiate (1:= sh1idx).
  split. intuition.
  assert(Hcons : consistency s) by intuition.
  assert(Hlevel : Some nbLgen = StateLib.getNbLevel) by intuition. 
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
  intro ptSh1SndVA.
  simpl.
(** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2: {
  intros.
  destruct H as (H0 & H1).
  assert ( (getTableAddrRoot' ptSh1SndVA sh1idx currentPart sndVA s /\ ptSh1SndVA = defaultPage) \/
 (forall idx : index,
  StateLib.getIndexOfAddr sndVA fstLevel = idx ->
  isVE ptSh1SndVA idx s /\  getTableAddrRoot ptSh1SndVA sh1idx currentPart sndVA s)).
  { destruct H1 as [H1 |(Hi & Hi1 & H1 )].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
    - split;intuition;subst.
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
  intro sndVAsh1notnull. simpl.
  case_eq sndVAsh1notnull.
  { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
  intros HsndVAsh1notnull. subst.  
(** derived **)
  eapply WP.bindRev.
  { eapply WP.weaken.
    eapply Invariants.checkDerivation. simpl.
    simpl. intros. 
    destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
    + destruct Hptchild. subst. contradict Hptchildnotnull.
      intro Hnull.  apply beq_nat_false in Hnull. intuition.
    + subst.
      destruct Hptchild with (StateLib.getIndexOfAddr sndVA fstLevel) as (Hve & Htbl);
      trivial.
      assert (HP := conj (conj (conj H Hve) Htbl) Hptchildnotnull).
      split.
      eapply HP. 
      subst.
      assert ( StateLib.getIndexOfAddr sndVA fstLevel = idxSndVA) as Hidxchild.
      intuition.
      apply Hptchild in Hidxchild. destruct Hidxchild; assumption. }
  simpl. intros sndvanotshared.
  (** StateLib.getIndexOfAddr **)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getIndexOfAddr.
  { simpl. intros.
    pattern s in H.
    eexact H.  }
  intro idxTrdVA.
  simpl.  
  (** getTableAddr **)
  eapply WP.bindRev.
  eapply WP.weaken. 
  apply getTableAddr.
  simpl.
  intros s H.  
  split. 
  pattern s in H. 
  eexact H. subst.
  split. 
  intuition.
  split. 
  instantiate (1:= currentPart).
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  instantiate (1:= PDidx).
  split. intuition.
  assert(Hcons : consistency s) by intuition.
  assert(Hlevel : Some nbLgen = StateLib.getNbLevel) by intuition. 
  assert(Hcp : currentPart = currentPartition s) by intuition.
  assert (H0 : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
  exists currentPD.
  split. intuition.
  unfold consistency in *.
  destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
  unfold partitionDescriptorEntry in Hpd.
  assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/  PDidx  = sh3idx
  \/  PDidx  = PPRidx \/  PDidx = PRidx) as Htmp 
  by auto.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
  generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
  destruct Hpd as (Hidxpd & _& Hentry). 
  destruct Hentry as (page1 & Hpd & Hnotnull).
  subst.
  split. 
   unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
   [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
   as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict H0 | 
   now contradict H0 | 
   subst;assumption | now contradict H0| now contradict H0 ]  
   |now contradict H0] | now contradict H0].
  subst. left. split;intuition.
  intro ptMMUTrdVA. simpl.
  (** simplify the new precondition **)
  eapply WP.weaken.
  intros.
  2: {
  intros.
  destruct H as (H0 & H1).
  assert ( (getTableAddrRoot' ptMMUTrdVA PDidx currentPart trdVA s /\ ptMMUTrdVA = defaultPage) \/
  (forall idx : index,
  StateLib.getIndexOfAddr trdVA fstLevel = idx ->
  isPE ptMMUTrdVA idx s /\ getTableAddrRoot ptMMUTrdVA PDidx currentPart trdVA s  )).
  { destruct H1 as [H1 |(Hi & Hi1 & H1)].
    + left. trivial. 
    + right. intros idx Hidx.
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
      - (*  split; assumption.
      - *) contradict Htrue.
        apply idxPDidxSh1notEq.
      - contradict Hfalse.
        apply idxPDidxSh2notEq.
      - split;trivial. }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP. }
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptVaInCurPartpdIsnull. simpl.
  case_eq ptVaInCurPartpdIsnull.
  { intros. eapply WP.weaken.
    eapply WP.ret . simpl.
    intros. intuition. }
  intros HptVaInCurPartpdNotNull.
  subst.  
  (** readAccessible **)
  eapply WP.bindRev.
  { eapply WP.weaken.
    eapply Invariants.readAccessible. simpl.
    intros.
    destruct H as ((Ha1 & Ha3) & Ha4).
    assert (Hnewget : isPE ptMMUTrdVA (
    StateLib.getIndexOfAddr trdVA fstLevel) s /\
         getTableAddrRoot ptMMUTrdVA PDidx currentPart trdVA s /\ 
         (defaultPage =? ptMMUTrdVA) = false).
    { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
      + subst.
        apply beq_nat_false in Ha4.
        now contradict Ha4.
      + destruct Ha3 with (StateLib.getIndexOfAddr trdVA fstLevel);trivial.
        intuition. }
     subst.
   split.
    assert (HP := conj Ha1 Hnewget).
    pattern s in HP.
    eexact HP. clear Ha3. 
    intuition. subst;trivial. }
  intros trdVAisAccessible. simpl.
  case_eq(negb trdVAisAccessible);intros Haccess.
  intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition.
(** readPresent **)
  eapply WP.bindRev.
  { eapply WP.weaken.
    eapply Invariants.readPresent. simpl.
    intros.
    split.
    pattern s in H.
    eexact H. 
    intuition. subst;trivial. }
  intros trdVAisPresent. simpl.
  apply negb_false_iff in Haccess;subst.
  case_eq(negb trdVAisPresent);intros Hpres.
  intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition.
  apply negb_false_iff in Hpres;subst.
(** readPhyEntry **)
  eapply WP.bindRev.
  { eapply WP.weaken.
    eapply Invariants.readPhyEntry. simpl.
    intros.
    split.
    pattern s in H.
    eapply H. 
    subst.
    intuition;subst;trivial. }
  intros phySh2addr. simpl.
(** getTableAddr **)
  eapply WP.bindRev.
  eapply WP.weaken. 
  apply getTableAddr.
  simpl.
  intros s H.
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
  instantiate (1:= sh1idx).
  split. intuition.
  assert(Hcons : consistency s) by intuition.
  assert(Hlevel : Some nbLgen = StateLib.getNbLevel) by intuition. 
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
  intro ptSh1TrdVA.
  simpl.
(** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2: {
  intros.
  destruct H as (H0 & H1).
  assert ( (getTableAddrRoot' ptSh1TrdVA sh1idx currentPart trdVA s /\ ptSh1TrdVA = defaultPage) \/
 (forall idx : index,
  StateLib.getIndexOfAddr trdVA fstLevel = idx ->
  isVE ptSh1TrdVA idx s /\  getTableAddrRoot ptSh1TrdVA sh1idx currentPart trdVA s)).
  { destruct H1 as [H1 |(Hi & Hi1 & H1 )].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
    - split;intuition;subst.
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
  intro trdVAsh1notnull. simpl.
  case_eq trdVAsh1notnull.
  { intros. eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition. }
  intros HtrdVAsh1notnull. subst.  
(** derived **)
  eapply WP.bindRev.
  { eapply WP.weaken.
    eapply Invariants.checkDerivation. simpl.
    simpl. intros. 
    destruct H as ((H & [Hptchild | Hptchild]) & Hptchildnotnull).
    + destruct Hptchild. subst. contradict Hptchildnotnull.
      intro Hnull.  apply beq_nat_false in Hnull. intuition.
    + subst.
      destruct Hptchild with (StateLib.getIndexOfAddr trdVA fstLevel) as (Hve & Htbl);
      trivial.
      assert (HP := conj (conj (conj H Hve) Htbl) Hptchildnotnull).
      split.
      eapply HP. 
      subst.
      assert ( StateLib.getIndexOfAddr trdVA fstLevel = idxTrdVA) as Hidxchild.
      intuition.
      apply Hptchild in Hidxchild. destruct Hidxchild; assumption. }
  simpl. intros trdvanotshared.  
(** Check sharing *)
  case_eq(fstvanotshared && sndvanotshared && trdvanotshared);intros Hlegit.
  repeat rewrite andb_true_iff in Hlegit.
  intuition. subst.
  eapply bindRev.
  eapply weaken.
  eapply LinkedListConfig.checkEnoughEntriesLinkedList.
  simpl.
  intros.
  eapply H.
  intros lastLLTable;simpl.  
(** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro trdVAsh1notnull. simpl.
  case_eq (negb trdVAsh1notnull).
(** We don't need to link a new LL table *) 
  * intros HtrdVAsh1notnull. 
    apply negb_true_iff in HtrdVAsh1notnull.
    subst.    
    (** readVirtualUser **)
    eapply bindRev.
    eapply weaken.
    eapply Invariants.readVirtualUser.
    simpl.
    intros.
    assert(Hconfig1: initPEntryTablePreconditionToPropagatePrepareProperties s phyMMUaddr). 
    apply proveInitPEntryTablePreconditionToPropagatePrepareProperties
     with ptMMUFstVA fstVA  (currentPartition s) nbLgen currentPD;intuition; subst;trivial.
     unfold consistency in *;intuition.
    assert(Hconfig2: initPEntryTablePreconditionToPropagatePrepareProperties s phySh1addr).
    apply proveInitPEntryTablePreconditionToPropagatePrepareProperties
     with ptMMUSndVA sndVA  (currentPartition s) nbLgen currentPD;intuition; subst;trivial.
     unfold consistency in *;intuition.
    assert(Hconfig3: initPEntryTablePreconditionToPropagatePrepareProperties s phySh2addr). 
    apply proveInitPEntryTablePreconditionToPropagatePrepareProperties
     with ptMMUTrdVA trdVA  (currentPartition s) nbLgen currentPD;intuition; subst;trivial.
     unfold consistency in *;intuition.
    assert(Hispart :isPartitionFalseAll s  ptSh1FstVA  ptSh1TrdVA ptSh1SndVA idxFstVA   idxSndVA   idxTrdVA).
    { unfold isPartitionFalseAll.
      intuition;subst.
      eapply isPartitionFalseProof with (currentPart:=currentPartition s);trivial;try eassumption.
      unfold consistency in *;intuition.
      rewrite Nat.eqb_sym;trivial.
      unfold isPartitionFalseAll.
      intuition;subst.
      eapply isPartitionFalseProof with (currentPart:=currentPartition s)
      (descChild:= sndVA) (ptRefChild:=ptMMUSndVA) ;trivial;try eassumption.
      unfold consistency in *;intuition.
      rewrite Nat.eqb_sym;trivial.
      eapply isPartitionFalseProof with (currentPart:=currentPartition s)
      (descChild:= trdVA) (ptRefChild:=ptMMUTrdVA) ;trivial;try eassumption.
      unfold consistency in *;intuition.
      rewrite Nat.eqb_sym;trivial. }
    pattern s in H. 
    assert(Hnew:= conj (conj (conj (conj H Hconfig1) Hconfig2) Hconfig3) Hispart).
    apply Hnew.
    simpl.
    intros nextVA.
    (** writeAccessible *)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply writeAccessiblePropagatePropertiesPrepareFstVA with (ptMMUTrdVA:=ptMMUTrdVA) 
    (phySh2addr:=phySh2addr) (phySh1addr:=phySh1addr) (indMMUToPrepare:=indMMUToPrepare) 
    (ptMMUFstVA:=ptMMUFstVA) (phyMMUaddr:=phyMMUaddr) (lastLLTable:=lastLLTable) 
    (phyPDChild:=phyPDChild) (currentShadow2:=currentShadow2) (phySh2Child:=phySh2Child) 
    (currentPD:=currentPD) (ptSh1TrdVA:=ptSh1TrdVA) (ptMMUSndVA:=ptMMUSndVA) (ptSh1SndVA:=ptSh1SndVA)
    (ptSh1FstVA:=ptSh1FstVA) (currentShadow1:=currentShadow1) (descChildphy:=descChildphy)
    (phySh1Child:=phySh1Child) (trdVA:=trdVA) (nextVA:=nextVA) (vaToPrepare:=vaToPrepare) 
    (sndVA:=sndVA) (fstVA:=fstVA) (nbLgen:=nbLgen) (l:=l)  
    (userMMUSndVA:=true) (userMMUTrdVA:=true) (idxFstVA:= idxFstVA) (idxSndVA:= idxSndVA) 
    (idxTrdVA:=idxTrdVA) (currentPart:= currentPart)(zeroI:= zeroI)(LLroot:= fstLL)(LLChildphy:=LLChildphy)  (newLastLLable:=lastLLTable) (minFI:=3).
    simpl.
    intros.
    simpl.
    intuition;subst;trivial.
    unfold propagatedPropertiesPrepare, indirectionDescriptionAll, initPEntryTablePreconditionToPropagatePreparePropertiesAll, checkEnoughEntriesLinkedListPC in *.  
    intuition;subst;trivial.
    apply inGetLLPages with LLChildphy;trivial.
    admit. (** Consistency not found : LLconfiguration5 *)
    intros [].
    (** writeAccessibleRec **)
    eapply bindRev.
    eapply weaken.
    eapply postAnd.
    eapply WriteAccessibleRecPropagatePrepareProperties
      with(va:=fstVA) (descParent:= currentPart) (phypage:= phyMMUaddr) (pt:= ptMMUFstVA). 
    eapply weaken.
    eapply WriteAccessibleRecPrepareNewProperty with (phypage:= phyMMUaddr).
    intros;simpl.
    destruct H as (_ & Hi).
    eapply Hi.
    intros;simpl.
    split.
    split;[eapply H|].
    intuition.
    apply writeAccessibleRecPreconditionProofFstVA in H;trivial.
    simpl.
    intros[].
    (** writeAccessible *)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply postAnd.
    3:{ intros. eapply H. }
    eapply weaken.
    eapply writeAccessiblePropagatePropertiesPrepareSndVA with (ptMMUTrdVA:=ptMMUTrdVA) 
    (phySh2addr:=phySh2addr) (phySh1addr:=phySh1addr) (indMMUToPrepare:=indMMUToPrepare) 
    (ptMMUFstVA:=ptMMUFstVA) (phyMMUaddr:=phyMMUaddr) (lastLLTable:=lastLLTable) 
    (phyPDChild:=phyPDChild) (currentShadow2:=currentShadow2) (phySh2Child:=phySh2Child) 
    (currentPD:=currentPD) (ptSh1TrdVA:=ptSh1TrdVA) (ptMMUSndVA:=ptMMUSndVA) (ptSh1SndVA:=ptSh1SndVA)
    (ptSh1FstVA:=ptSh1FstVA) (currentShadow1:=currentShadow1) (descChildphy:=descChildphy)
    (phySh1Child:=phySh1Child) (trdVA:=trdVA) (nextVA:=nextVA) (vaToPrepare:=vaToPrepare) 
    (sndVA:=sndVA) (fstVA:=fstVA) (nbLgen:=nbLgen) (l:=l)  
     (userMMUTrdVA:=true) (idxFstVA:= idxFstVA) (idxSndVA:= idxSndVA) 
    (idxTrdVA:=idxTrdVA) (currentPart:= currentPart) (zeroI:= zeroI) (LLroot:= fstLL)(LLChildphy:=LLChildphy)  (newLastLLable:=lastLLTable) (minFI:=3).
    simpl.
    intros.
    simpl.
    intuition;subst;trivial.
    eapply weaken.
    eapply writeAccessiblePropagateWriteAccessibleRecProperty with (pg:= phyMMUaddr) (vaToUpdate:= sndVA)
    (currentPart:= currentPart).
    simpl;intros;intuition.
    unfold preconditionToPropagateWriteAccessibleRecProperty, propagatedPropertiesPrepare in *;
    intuition.    
    intros [].
    (** writeAccessibleRec **)
    eapply bindRev.
    eapply weaken.
    eapply postAnd.
    eapply postAnd.
    4:{  intros; eapply H. }
    eapply weaken.
    eapply WriteAccessibleRecPropagatePrepareProperties
      with(va:=sndVA) (descParent:= currentPart) (phypage:= phySh1addr) (pt:= ptMMUSndVA). 
    simpl;intros.
    split.
    intuition; try eassumption.
    destruct H as (H & Hi).
    

    apply writeAccessibleRecPreconditionProofSndVA in H;trivial.
    simpl.
    eapply weaken.  
    eapply WriteAccessibleRecPreparePropagateNewProperty with (pg:= phyMMUaddr). 
    intros;simpl. 
    destruct H as ( H & Hii).
    apply writeAccessibleRecPreconditionProofSndVA in H;trivial.
    split;eassumption.
    simpl.    
    eapply weaken.    
    eapply WriteAccessibleRecPrepareNewProperty with (va:=sndVA) (descParent:= currentPart) (phypage:= phySh1addr) (pt:= ptMMUSndVA). 
    simpl;intros.
    destruct H as (Hi & Hii ).
    apply writeAccessibleRecPreconditionProofSndVA in Hi;trivial.
    eapply Hi.
    simpl.    
    intros[].
    (** writeAccessible *)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply postAnd.
    eapply postAnd.
    4:{ intros. eapply H. }
    eapply weaken.
    eapply writeAccessiblePropagatePropertiesPrepareTrdVA with (ptMMUTrdVA:=ptMMUTrdVA) 
    (phySh2addr:=phySh2addr) (phySh1addr:=phySh1addr) (indMMUToPrepare:=indMMUToPrepare) 
    (ptMMUFstVA:=ptMMUFstVA) (phyMMUaddr:=phyMMUaddr) (lastLLTable:=lastLLTable) 
    (phyPDChild:=phyPDChild) (currentShadow2:=currentShadow2) (phySh2Child:=phySh2Child) 
    (currentPD:=currentPD) (ptSh1TrdVA:=ptSh1TrdVA) (ptMMUSndVA:=ptMMUSndVA) (ptSh1SndVA:=ptSh1SndVA)
    (ptSh1FstVA:=ptSh1FstVA) (currentShadow1:=currentShadow1) (descChildphy:=descChildphy)
    (phySh1Child:=phySh1Child) (trdVA:=trdVA) (nextVA:=nextVA) (vaToPrepare:=vaToPrepare) 
    (sndVA:=sndVA) (fstVA:=fstVA) (nbLgen:=nbLgen) (l:=l)  
     (idxFstVA:= idxFstVA) (idxSndVA:= idxSndVA) 
    (idxTrdVA:=idxTrdVA) (currentPart:= currentPart) (zeroI:= zeroI) (LLroot:= fstLL)(LLChildphy:=LLChildphy)  (newLastLLable:=lastLLTable)(minFI:=3) .
    simpl.
    intros.
    simpl.
    intuition;subst;trivial.
    eapply weaken.
    eapply writeAccessiblePropagateWriteAccessibleRecProperty with (pg:= phyMMUaddr) (vaToUpdate:= trdVA)
    (currentPart:= currentPart).
    simpl;intros;intuition.
    unfold preconditionToPropagateWriteAccessibleRecProperty, propagatedPropertiesPrepare in *;
    intuition.
    eapply weaken.
    eapply writeAccessiblePropagateWriteAccessibleRecProperty with (pg:= phySh1addr) (vaToUpdate:= trdVA)
    (currentPart:= currentPart).
    simpl;intros;intuition.
    unfold preconditionToPropagateWriteAccessibleRecProperty, propagatedPropertiesPrepare in *;
    intuition.
    simpl.        
    intros [].
    (** writeAccessibleRec **)
    eapply bindRev.
    eapply weaken.
    eapply postAnd.
    eapply postAnd.
    eapply postAnd.
    5:{  intros; eapply H. }
    eapply weaken.
    eapply WriteAccessibleRecPropagatePrepareProperties
      with(va:=trdVA) (descParent:= currentPart) (phypage:= phySh2addr) (pt:= ptMMUTrdVA). 
    simpl;intros.
    split.
    intuition;try eassumption.
    eapply writeAccessibleRecPreconditionProofTrdVA.
    intuition;try eassumption. (*   with phySh1addr indMMUToPrepare
        ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD
        ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy
        phySh1Child  nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA zeroI
        fstLL LLChildphy lastLLTable;
    intuition. *)
    eapply weaken.  
    eapply WriteAccessibleRecPreparePropagateNewProperty with (pg:= phyMMUaddr). 
    intros;simpl. 
    split;intuition;try eassumption.
    eapply writeAccessibleRecPreconditionProofTrdVA;
    (* with phySh1addr indMMUToPrepare
        ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD
        ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy
        phySh1Child  nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA zeroI
        fstLL LLChildphy lastLLTable;*)
    intuition;try eassumption.
    eapply weaken.  
    eapply WriteAccessibleRecPreparePropagateNewProperty with (pg:= phySh1addr). 
    intros;simpl.
    split;intuition;try eassumption.
    eapply writeAccessibleRecPreconditionProofTrdVA; (* with phySh1addr indMMUToPrepare
        ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD
        ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy
        phySh1Child  nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA zeroI
        fstLL LLChildphy lastLLTable;*)
    intuition;try eassumption.
    eapply weaken.
    eapply WriteAccessibleRecPrepareNewProperty with (descParent:= currentPart) 
    (phypage:= phySh2addr) (pt:= ptMMUTrdVA). 
    simpl;intros.
    eapply writeAccessibleRecPreconditionProofTrdVA; (* with phySh1addr indMMUToPrepare
        ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD
        ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy
        phySh1Child  nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA zeroI
        fstLL LLChildphy lastLLTable;*)
    intuition;try eassumption.
    intros[].
   (**  Level.pred *)
    simpl.
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply Invariants.Level.pred.
    intros.
    simpl.
    split.
    repeat rewrite and_assoc in H.
    pattern s in H.
    eapply H.
    unfold propagatedPropertiesPrepare in *.
    apply levelEqBEqNatFalse0;intuition.
    intro lpred. 
    simpl in *. 
(** initPEntryTable **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply conjPrePost.
    eapply initPEntryTablePropagateProperties.  
    eapply initPEntryTableNewPropertyL;simpl.
    intros;simpl.
    repeat rewrite and_assoc in H.
    destruct H.
    split. split.
    eapply H.
    intuition.
    eassumption. 
    unfold propagatedPropertiesPrepare, indirectionDescriptionAll, initPEntryTablePreconditionToPropagatePreparePropertiesAll in *;
    intuition.
    unfold propagatedPropertiesPrepare, indirectionDescriptionAll, initPEntryTablePreconditionToPropagatePreparePropertiesAll in *;
    intuition.
    unfold initPEntryTablePreconditionToProveNewProperty.
    intros.
     assert (zeroI = CIndex 0) as Hzero by (unfold propagatedPropertiesPrepare, indirectionDescriptionAll, initPEntryTablePreconditionToPropagatePreparePropertiesAll in *;intuition).    
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
    omega.
    intros [].
    simpl.
(** initFstShadow *)
    eapply WP.bindRev.
    eapply initFstShadowPrepareHT.
    intros [].
(** initSndShadow *)
    eapply bindRev.   
    apply initSndShadowPrepareHT.
    intros [].
(** writeVirEntry **)
    eapply bindRev.
    eapply weaken.
    eapply writeVirEntryFstVA.
    simpl.
    intros.
    unfold writeAccessibleRecPreparePostconditionAll, isWellFormedTables.
    intuition try eassumption.
    intros [].
(** writeVirEntry **)
    eapply bindRev.
    eapply weaken.
    eapply writeVirEntrySndVA.
    simpl;intros.
    intuition; try eassumption.
(** writeVirEntry **)
    intros [].
    eapply bindRev.
    eapply writeVirEntryTrdVA.
    intros [].
(** insertEntryIntoLL**)
    eapply bindRev.
    eapply insertEntryIntoLLHT.
    intros [].
(** insertEntryIntoLL**)
    eapply bindRev.
    eapply insertEntryIntoLLHT.
    intros [].        
(** insertEntryIntoLL**)
    eapply bindRev.
    eapply insertEntryIntoLLHT.
    intros [].        



(** TODO : To be proved *)
Admitted.

Lemma prepare (descChild : vaddr)  (va : vaddr) (fstVA : vaddr) :
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }} 
prepare descChild va fstVA
{{fun _ s  => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold prepare.
(** getCurPartition **)
eapply WP.bindRev.
eapply WP.weaken. 
eapply Invariants.getCurPartition .
cbn. 
intros. 
pattern s in H. 
eexact H.
intro currentPart.
(** getPd **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getPd.
cbn.
intros s H.
split.
pattern s in H.
eexact H.
split.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
unfold consistency in *.
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
intuition.
intros currentPD.
(** getNbLevel **)
eapply WP.bindRev.
eapply weaken.
eapply Invariants.getNbLevel.
simpl. intros.
pattern s in H.
eexact H.
intros level.
simpl.
(** checkChild **)
  unfold Internal.checkChild.
  rewrite assoc.
  eapply bindRev.
  (** getFstShadow **)
  eapply WP.weaken. 
  eapply Invariants.getFstShadow. cbn.
  intros s H.
  split.
  pattern s in H.
  eexact H.
  unfold consistency in *.
  unfold partitionDescriptorEntry in *.
  intuition.
  simpl.
  intros currentShadow1.
  rewrite assoc.
  (** StateLib.getIndexOfAddr **)                
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getIndexOfAddr.
  { simpl. intros.
    pattern s in H.
    eexact H.  }
  intro idxDescChild. simpl.
  rewrite assoc.
  (** getTableAddr **)
  eapply WP.bindRev.
  eapply WP.weaken. 
  apply getTableAddr.
  simpl.
  intros s H.
  split.
  pattern s in H. 
  eexact H. subst.
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
  assert(Hcp : currentPart = currentPartition s) by intuition.
  assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
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
   as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict H0 | 
   now contradict H0 | 
   subst;assumption | now contradict H0| now contradict H0 ]  
   |now contradict H0] | now contradict H0].
  subst. left. split;intuition.
  intro ptDescChild. simpl.
  (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2: {
  intros.
  destruct H as (H0 & H1).
  assert ( (getTableAddrRoot' ptDescChild sh1idx currentPart descChild s /\ ptDescChild = defaultPage) \/
  (forall idx : index,
  StateLib.getIndexOfAddr descChild fstLevel = idx ->
  isVE ptDescChild idx s /\ getTableAddrRoot ptDescChild sh1idx currentPart descChild s  )).
  { destruct H1 as [H1 |(Hi & Hi1 & H1)].
    + left. trivial. 
    + right. intros idx Hidx.
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
      - split; assumption.
      - contradict Hfalse. 
        symmetrynot. 
        apply idxSh2idxSh1notEq.
      - contradict Hfalse. 
        symmetrynot. apply idxPDidxSh1notEq.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP. }
  rewrite assoc.
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptDescChildIsnull. simpl.
  case_eq ptDescChildIsnull.
  { intros.
    eapply WP.weaken.
    eapply WP.ret .
    simpl. intros.
    intuition. }
  intros HptDescChildIsnull. 
  subst.
  (* readPDflag *)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.readPDflag.
  simpl;intros.
  split.
  destruct H as (((Ha1 & Ha2) & Ha3) & Ha4).
  assert (Hnewget : isVE ptDescChild (StateLib.getIndexOfAddr descChild fstLevel) s /\
       getTableAddrRoot ptDescChild sh1idx currentPart descChild s /\ 
       (defaultPage =? ptDescChild) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr descChild fstLevel);trivial.
      intuition. }
  assert (HP := conj (conj Ha1 Ha2) Hnewget).
  pattern s in HP.
  eexact HP.
  destruct H as (H & Htrue).
  destruct H as (H & Hor).
  destruct Hor as [(Hor & Hfalse) | Hor].
  subst.
  apply beq_nat_false in Htrue.
  now contradict Htrue.
  destruct H as (H & Hidx).
  subst.
  destruct Hor with (StateLib.getIndexOfAddr descChild fstLevel);
  trivial.
  intros ischild;simpl in *.
  intros.
  case_eq ischild; intros Hischild;[|intros;eapply weaken;[ eapply WP.ret;trivial|
  intros;simpl;intuition]].
  subst.
(** end checkChild *)
(** getTableAddr : to return the physical page of the descChild   **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
split. 
instantiate (1:= currentPart).
unfold consistency in *. 
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
intuition.
instantiate (1:= PDidx).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
exists currentPD.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/  PDidx  = sh3idx
\/  PDidx  = PPRidx \/  PDidx = PRidx) as Htmp 
by auto.
    generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split. 
 unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx);
 [destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex)
 as [v |]; [ destruct v as [ p |v|p|v|ii] ; [ now contradict H0 | 
 now contradict H0 | 
 subst;assumption | now contradict H0| now contradict H0 ]  
 |now contradict H0] | now contradict H0].
subst. left. split;intuition.
intro ptDescChildpd. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptDescChildpd PDidx currentPart descChild s /\ ptDescChildpd = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptDescChildpd idx s /\ getTableAddrRoot ptDescChildpd PDidx currentPart descChild s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
    - (*  split; assumption.
    - *) contradict Htrue.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - split;trivial. }
assert (HP := conj H0 H).
pattern s in HP.
exact HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro ptDescChildpdIsnull. simpl.
case_eq ptDescChildpdIsnull.
{ intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition. }
intros HptDescChildpdNotNull. subst.
(** StateLib.getIndexOfAddr **)                
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getIndexOfAddr.
{ simpl. intros.
  destruct H as ((Ha1 & Ha3) & Ha4).
  assert (Hnewget : isPE ptDescChildpd 
  (StateLib.getIndexOfAddr descChild fstLevel) s /\
       getTableAddrRoot ptDescChildpd PDidx currentPart descChild s /\ 
       (defaultPage =? ptDescChildpd) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr descChild fstLevel);trivial.
      intuition. }
   subst.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  eexact HP. }
intro idxDescChild1.
simpl. 
(** readPresent **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPresent. simpl.
  intros.
  split.
  pattern s in H.
  eexact H. 
  intuition. subst;trivial. }
intros presentdescChild. simpl.
case_eq ( negb presentdescChild);intros Hlegit1;subst;[intros;eapply weaken;[ eapply WP.ret;trivial|
  intros;simpl;intuition]|].  
(** readPhyEntry **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPhyEntry. simpl.
  intros.
  split.
  pattern s in H.
  eapply H. 
  subst.
  intuition;subst;trivial. }
intros phyDescChild. simpl.
(** getPd **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getPd.
cbn.
intros s H.
(** descChild is a child *)
assert(Hchildren : In phyDescChild (getChildren (currentPartition s) s)).
{ unfold getChildren.
  assert(Hlevel : Some level = StateLib.getNbLevel) by intuition.
  rewrite <- Hlevel.
  assert(Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
  { apply nextEntryIsPPgetPd.
    intuition. }
  assert (Heq : currentPartition s = currentPart) by intuition.
  subst.
  rewrite Hcurpd.
  unfold getMappedPagesAux.
  rewrite filterOptionInIff.
  unfold getMappedPagesOption.
  rewrite in_map_iff.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel descChild va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1.  split;trivial. 
assert(Hnewgoal : getMappedPage currentPD s descChild = SomePage phyDescChild). 
{  apply getMappedPageGetTableRoot with ptDescChildpd (currentPartition s); intuition;
  subst;trivial.
  apply negb_false_iff in Hlegit1.
  subst;trivial. }
  rewrite <- Hnewgoal.
  symmetry.
  apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
  apply getNbLevelEqOption.
  unfold getPdsVAddr.
  apply filter_In.
  split;trivial. 
  assert(Hnewgoal : checkChild (currentPartition s) level s descChild = true).
  { unfold checkChild. 
  assert(Hcursh1 : getFstShadow (currentPartition s) (memory s) = Some currentShadow1).
  { apply nextEntryIsPPgetFstShadow. intuition; subst;trivial. }
  rewrite Hcursh1.
  assert(Hpt :getIndirection currentShadow1 descChild level (nbLevel - 1) s  = Some ptDescChild). 
  { apply getIndirectionGetTableRoot with (currentPartition s);intuition.
    subst;trivial. }
  rewrite Hpt.
  assert(Htrue : (ptDescChild =? defaultPage) = false ). 
  { rewrite Nat.eqb_neq in *. intuition. }
  rewrite Htrue.
  assert(Hpdchild :  entryPDFlag ptDescChild idxDescChild true s) by intuition.
  assert(Hpdtrue : StateLib.readPDflag ptDescChild
    (StateLib.getIndexOfAddr descChild fstLevel) (memory s) = Some true).
  { unfold StateLib.readPDflag, entryPDFlag in *.
    intuition. subst.
    destruct (lookup ptDescChild (StateLib.getIndexOfAddr descChild fstLevel) (memory s) beqPage beqIndex );
    try now contradict Hpdchild.
    destruct v;try now contradict Hpdchild.
    f_equal. subst. intuition. }
    rewrite Hpdtrue;trivial. }
  rewrite <- Hnewgoal.
  apply checkChildEq.
  intuition.
  rewrite checkVAddrsEqualityWOOffsetPermut.
  rewrite <- Hva11.
  f_equal.
  assert(Hlvl : StateLib.getNbLevel = Some (CLevel (nbLevel - 1))) by apply getNbLevelEqOption. 
  rewrite  Hlvl in *.
  inversion Hlevel;trivial. }
split. 
assert(Hnew := conj H Hchildren).  
pattern s in Hnew.
eexact Hnew.
split.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
unfold consistency in *.
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
apply childrenPartitionInPartitionList with (currentPartition s); intuition.
intros pdChildphy.
simpl.
(** getFstShadow **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getFstShadow1. cbn.
intros s H.
split.
pattern s in H.
eexact H.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
apply childrenPartitionInPartitionList with (currentPartition s); intuition.
intros phySh1Child.
simpl.
(** getSndShadow **)
eapply bindRev.
eapply weaken.
eapply Invariants.getSndShadow.
simpl;intros.
split.
pattern s in H. 
exact H.
split. trivial.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
unfold consistency in *.
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
apply childrenPartitionInPartitionList with (currentPartition s); intuition.
intros phySh2Child.
simpl.
(** getConfigTablesLinkedList **)
eapply bindRev.
eapply weaken.
eapply Invariants.getConfigTablesLinkedList.
simpl;intros.
split.
pattern s in H. 
exact H.
split. trivial.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
unfold consistency in *.
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
apply childrenPartitionInPartitionList with (currentPartition s); intuition.
(** prepareAux **)
intros LLChildphy.
simpl.
unfold prepareAux.
eapply weaken.
apply prepareRec with (fstLL := LLChildphy);trivial.
simpl. intros.
intuition.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
unfold consistency in *.
intuition.
unfold consistency in *.
intuition.
unfold indirectionDescription.
exists pdChildphy.
split;trivial.
split;trivial.
apply pdPartNotNull with phyDescChild s;trivial.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
unfold consistency in *.
intuition.
unfold consistency in *.
intuition.
unfold consistency in *.
intuition.
left.
split;trivial.
unfold indirectionDescription.
exists phySh1Child.
split;trivial.
split;trivial.
apply sh1PartNotNull with phyDescChild s;trivial.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
unfold consistency in *.
intuition.
unfold consistency in *.
intuition.
unfold consistency in *.
intuition.
left.
split;trivial.
unfold indirectionDescription.
exists phySh2Child.
split;trivial.
split;trivial.
apply sh2PartNotNull with phyDescChild s;trivial.
apply childrenPartitionInPartitionList with (currentPartition s);trivial.
unfold consistency in *.
intuition.
unfold consistency in *.
intuition.
unfold consistency in *.
intuition.
left.
split;trivial.
apply nextEntryIsPPgetConfigList;trivial.
destruct nbPage;simpl.
case_eq(StateLib.getMaxIndex );[intros x Hx|intros Hx].
destruct(StateLib.readPhysical LLChildphy x (memory s));simpl;[|left;trivial].
destruct(p =? defaultPage);simpl;left;trivial.
contradict Hx.
apply getMaxIndexNotNone.

case_eq(StateLib.getMaxIndex );[intros x Hx|intros Hx].
destruct(StateLib.readPhysical LLChildphy x (memory s));simpl;[|left;trivial].
destruct(p =? defaultPage);simpl;left;trivial.
contradict Hx.
apply getMaxIndexNotNone.
Qed.


