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
    This file contains the invariant of [initConfigPagesList] some associated lemmas *)
Require Import Core.Internal Isolation Consistency WeakestPreconditions Invariants.
Require Import StateLib Model.Hardware Model.ADT DependentTypeLemmas
PropagatedProperties  UpdateMappedPageContent InternalLemmas.
Require Import Coq.Logic.ProofIrrelevance Omega Model.MAL List Bool.

Lemma initConfigPagesListNewProperty phyConfigPagesList (curidx : index):
{{ fun s : state => (curidx = (CIndex 0) \/ Nat.Odd curidx) /\ 
                  (forall idx : index, idx <> (CIndex (tableSize - 1)) -> Nat.Odd idx -> idx < curidx ->
                  StateLib.readVirtual phyConfigPagesList idx s.(memory) = Some defaultVAddr)  /\ 
                 (forall idx : index,  Nat.Even idx -> idx < curidx -> 
                 exists idxValue, StateLib.readIndex phyConfigPagesList idx s.(memory) = Some idxValue)}}
  Internal.initConfigPagesList phyConfigPagesList curidx 
{{ fun _ s  => StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) s.(memory)
                 = Some defaultPage /\ 
                 (forall idx : index, idx <> (CIndex (tableSize - 1)) -> Nat.Odd idx -> 
                  StateLib.readVirtual phyConfigPagesList idx s.(memory) = Some defaultVAddr)  /\ 
                 (forall idx : index,  Nat.Even idx -> 
                 exists idxValue, StateLib.readIndex phyConfigPagesList idx s.(memory) = Some idxValue)  }}.
Proof.
unfold initConfigPagesList.
assert(Hsize : tableSize + curidx >= tableSize) by omega.
revert Hsize.
revert phyConfigPagesList curidx.
generalize tableSize at 1 4. 
induction n.  simpl. 
+ intros. eapply weaken.
  eapply WP.ret. simpl. intros.
  destruct curidx.
  simpl in *.
  clear H.
  contradict Hi.
  omega.
+ intros. simpl.
(** Index.zero **)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.Index.zero.
  intros; simpl.
  pattern s in H;eassumption. 
  intros zero; simpl.
(** getMaxIndex *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getMaxIndex.
  intros; simpl.
  pattern s in H;eassumption. 
  intros maxidx; simpl.
(** MALInternal.Index.eqb *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.Index.eqb.
  intros. simpl.
  pattern s in H.
  eapply H.
  intros eqbMax.     
  simpl.
(** MALInternal.Index.eqb *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.Index.eqb.
  intros. simpl.
  pattern s in H.
  eapply H.
  intros eqbZero.     
  simpl.  
(** the last entry *) 
  case_eq eqbMax;intros HlastEntry.
  { eapply WP.bindRev.
(** getDefaultPage **)
    eapply WP.weaken.
    eapply Invariants.getDefaultPage.
    intros. simpl.
    pattern s in H.
    eassumption.
    simpl.
    subst.
    intros nullP. simpl. 
(** writePhysical **) 
    eapply weaken.
    eapply WP.writePhysical.
    simpl.
    intros.
    repeat rewrite and_assoc in H.
    destruct H as ( Hor & Hodd & Heven & Hzero & Hmax & Heqmax & Heqbzero & Hnull ).
    split.
   (** propagate readPhysical **)
    unfold StateLib.readPhysical.
    cbn; simpl in *.
    subst.
    assert(Htrue : Lib.beqPairs (phyConfigPagesList, curidx)
     (phyConfigPagesList,  CIndex (tableSize - 1)) beqPage beqIndex= true).
    { apply beqPairsTrue.
      split; trivial.
      apply indexEqbTrue.
      assumption. }
    rewrite Htrue; trivial.
    split.
  (** propagate odd (readVirtual) through write physical **)
  intros.
  unfold StateLib.readVirtual in *.
  cbn in *. 
  clear IHn Heven.
  subst.
  assert (Hcuridx : idx <> curidx).
  { apply indexEqbTrue in Heqmax.
    subst.
    unfold not; intros Hfalse.
    subst.
    now contradict H. }
  assert(Hfalse : Lib.beqPairs (phyConfigPagesList, curidx) (phyConfigPagesList, idx) beqPage beqIndex = false).
  { apply beqPairsFalse.
    right.
    unfold not; intros Hfalse.
    subst.
    now contradict Hcuridx. }
    rewrite Hfalse.
    assert(Hmemory : Lib.lookup phyConfigPagesList idx
          (Lib.removeDup phyConfigPagesList curidx (memory s) beqPage beqIndex) beqPage beqIndex = 
           Lib.lookup phyConfigPagesList idx (memory s) beqPage beqIndex  ).
    { apply removeDupIdentity. right.
      assumption. }
    rewrite Hmemory.
    apply Hodd; try assumption.
    apply indexMaxEqFalseLt in H.
    apply indexEqbTrue in Heqmax.
    subst.
    apply indexMaxEqFalseLt1; trivial.
  (** propagate even (readIndex) through writePhysical **)
  intros.
  unfold StateLib.readIndex.
  cbn.
  subst.
  assert (Nat.Odd curidx).
  apply indexEqbTrue in Heqmax.
  subst.
  assert (Nat.Even tableSize) by apply tableSizeIsEven.
  unfold CIndex.
  case_eq (lt_dec (tableSize - 1) tableSize); intros.
  simpl.
  replace tableSize with (S (tableSize -1)) in H0 by omega.
  apply NPeano.Nat.Even_succ; trivial.
  assert(tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
  omega.
  assert (idx <> curidx).
  { unfold not.
    intros Hoddeven.
    subst.
     apply Nat.Even_Odd_False in H ; trivial. }
  assert(Hfalse : Lib.beqPairs (phyConfigPagesList, curidx) (phyConfigPagesList, idx) beqPage beqIndex = false).
  { apply beqPairsFalse.
    right.
    unfold not; intros Hfalse.
    subst.
    now contradict H1. }
    rewrite Hfalse.
    assert(Hmemory : Lib.lookup phyConfigPagesList idx
          (Lib.removeDup phyConfigPagesList curidx (memory s) beqPage beqIndex) beqPage beqIndex = 
           Lib.lookup phyConfigPagesList idx (memory s) beqPage beqIndex  ).
    { apply removeDupIdentity. right.
      assumption. }
    rewrite Hmemory.
    unfold StateLib.readIndex in Heven.
    apply Heven; trivial.
    apply indexEqbTrue in Heqmax.
    subst.
    apply indexMaxEqFalseLt1; trivial.

   }
(** the first entry *) 
case_eq eqbZero;intros HfstEntry.
  { (** MALInternal.Index.succ **) 
   eapply bindRev.
   eapply WP.weaken. 
   eapply Invariants.Index.succ.
   intros.
   clear IHn.
   simpl.
   split.
   try repeat rewrite and_assoc in H.  
   pattern s in H.
   eassumption.
   repeat rewrite and_assoc in H.
   destruct H as (  Hor & Hodd & Heven & Hzero & Hmax & Hnoteqmax & Heqbzero ).
   unfold StateLib.Index.eqb in Hnoteqmax.
   symmetry in Hnoteqmax.
   apply beq_nat_false in Hnoteqmax.
   rewrite Hmax in Hnoteqmax.
   apply indexMaxEqFalseLt.
   unfold not; intros.
   subst.
   now contradict Hnoteqmax.
   intros idxsucc.
   simpl.
   eapply bindRev.
(** writeIndex **)
   eapply weaken.
   eapply WP.writeIndex.
   simpl;intros.
   try repeat rewrite and_assoc in H.
   pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                 StateLib.readIndex phyConfigPagesList curidx s.(memory) = Some (idxsucc) )
    end.
   simpl in *.
   destruct H.
   split. split. 
   assumption.
   destruct H0 as (  Hodd & Heven & Hzero & Hmax & Hnoteqmax & Heqbzero & Hidxsucc ).
   apply and_assoc.
   split. 
   { split; intros; 
     assert False.
     subst.
     apply indexEqbTrue in Heqbzero.
     subst.
     apply indexLtZero with idx.
     assumption.
     now contradict H3.
     apply indexEqbTrue in Heqbzero.
     subst.
     apply indexLtZero with idx.
     assumption.
     now contradict H2. }
   intuition.
   unfold StateLib.readIndex.
   cbn.
   assert (Htrue :Lib.beqPairs (phyConfigPagesList, curidx) (phyConfigPagesList, curidx) beqPage beqIndex
   = true).
   apply beqPairsTrue;split;trivial.
   rewrite Htrue; trivial.
   intros [].
(** recursion **)
   simpl.
   unfold hoareTriple in *.
   intros.
   apply IHn.
   simpl.
   assert (StateLib.Index.succ curidx = Some idxsucc) by intuition.
   clear H IHn.
   unfold StateLib.Index.succ in *.
   case_eq (lt_dec (curidx + 1) tableSize) ;intros; rewrite H in *.
   inversion H0.
   destruct idxsucc, curidx.
   simpl in *.
   omega.
   now contradict H0.
   destruct H as ((Hor & Hodd & Heven & Hzero & Hmax & Hnoteqmax 
                    & Heqbzero & Hidxsucc) & Hreadi).
   split.
   (** Nat.Odd idxsucc**)
   { right.
     subst.
     apply indexSEqbZeroOdd with curidx; trivial. }
     split; intros.
     subst.
     apply Hodd; trivial.
     apply indexEqbTrue in Heqbzero.
     subst.
     assert (~ Nat.Odd idx).
     apply indexZeroNotOdd with idxsucc; trivial.
     now contradict H2.
     exists idxsucc.
     apply indexEqbTrue in Heqbzero.
     assert ( idx = (CIndex 0)).
     subst.
     apply indexSEqbZeroLt  with idxsucc; assumption.
     subst; trivial. }

(** not the last entry **)
  eapply bindRev.
(** getDefaultPage **)
    eapply WP.weaken.
    eapply Invariants.getDefaultVAddr.
    intros. simpl.
    pattern s in H.
    eassumption.
    simpl.
    subst.
    simpl;intros nullV.
    eapply bindRev.
(** writeVirtual **)
   eapply weaken.
   eapply WP.writeVirtual.
   simpl;intros.
    try repeat rewrite and_assoc in H.
   pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                 StateLib.readVirtual phyConfigPagesList curidx s.(memory) = Some nullV )
    end.
   simpl in *.
   split.
      destruct H as (Hor & Hodd & Heven & Hzero & Hmax & Hnoteqmax 
                    & Heqbzero & Hnullv).
    subst.
    split ; trivial.
    split.
(**  Odd **)
    { intros.
    clear Hor.
    unfold StateLib.readVirtual in *.
    
    cbn.
    assert (idx <> curidx).
    apply indexDiffLtb; left; assumption.
    assert(Hfalse : Lib.beqPairs (phyConfigPagesList, curidx) (phyConfigPagesList, idx) beqPage beqIndex=
    false).
    { apply beqPairsFalse.
      right; unfold not; intros.
        subst. now contradict H2. }
    rewrite Hfalse.
    assert (Hmemory :   Lib.lookup phyConfigPagesList idx (Lib.removeDup phyConfigPagesList curidx (memory s) beqPage beqIndex) beqPage
    beqIndex =  Lib.lookup phyConfigPagesList idx (memory s) beqPage beqIndex).
    { apply removeDupIdentity; right; trivial. }
    rewrite Hmemory.
    apply Hodd; trivial. }
(** even **)
    split.
    { intros.
      unfold StateLib.readIndex  in *.
        cbn.
      assert (idx <> curidx).
    apply indexDiffLtb; left; assumption.
    assert(Hfalse : Lib.beqPairs (phyConfigPagesList, curidx) (phyConfigPagesList, idx) beqPage beqIndex=
    false).
    { apply beqPairsFalse.
      right; unfold not; intros.
        subst. now contradict H1. }
    rewrite Hfalse.
    assert (Hmemory :   Lib.lookup phyConfigPagesList idx (Lib.removeDup phyConfigPagesList curidx (memory s) beqPage beqIndex) beqPage
    beqIndex =  Lib.lookup phyConfigPagesList idx (memory s) beqPage beqIndex).
    { apply removeDupIdentity; right; trivial. }
    rewrite Hmemory.
    apply Heven; trivial. }
(** writeVirtual postcondition **)
    intuition.
   unfold StateLib.readVirtual.
   cbn.
   assert (Htrue :Lib.beqPairs (phyConfigPagesList, curidx) (phyConfigPagesList, curidx) beqPage beqIndex
   = true).
   apply beqPairsTrue;split;trivial.
   rewrite Htrue; trivial.   
   intros [].
 (** MALInternal.Index.succ **) 
   eapply bindRev.
   eapply WP.weaken. 
   eapply Invariants.Index.succ.
   intros.
   clear IHn.
   simpl.
   split.
   try repeat rewrite and_assoc in H.  
   pattern s in H.
   eassumption.
   repeat rewrite and_assoc in H.
         destruct H as (Hor & Hodd & Heven & Hzero & Hmax & Hnoteqmax 
                    & Heqbzero & Hidxsucc & HreadV).
   unfold StateLib.Index.eqb in Hnoteqmax.
   symmetry in Hnoteqmax.
   apply beq_nat_false in Hnoteqmax.
   rewrite Hmax in Hnoteqmax.
   apply indexMaxEqFalseLt.
   unfold not; intros.
   subst.
   now contradict Hnoteqmax.
   intros iIndex.
   simpl.
   eapply bindRev.
 (** MALInternal.Index.succ **) 
   eapply WP.weaken. 
   eapply Invariants.Index.succ.
   intros.
   clear IHn.
   simpl.
   split.
   try repeat rewrite and_assoc in H.  
   pattern s in H.
   eassumption.
   repeat rewrite and_assoc in H.
   
   destruct H as ( Hor & Hodd & Heven & Hzero & Hmax & Hnoteqmax & 
                   Heqbzero & Hnullv & Hreadv & Hidxsucc).
   assert(Hoddcuridx : Nat.Odd curidx).
   {  destruct Hor.
      unfold StateLib.Index.eqb in *.
      symmetry in Heqbzero.
      apply beq_nat_false in Heqbzero.
      subst.
      now contradict Heqbzero.
      assumption. }
   clear Hor.
   unfold StateLib.Index.eqb in Hnoteqmax.
   symmetry in Hnoteqmax.
   apply beq_nat_false in Hnoteqmax.
   assert (curidx < tableSize -1).
   rewrite Hmax in Hnoteqmax.
   apply indexMaxEqFalseLt.
   unfold StateLib.Index.succ in *.
   unfold not; intros.
   subst.
   now contradict Hnoteqmax.
   assert (Nat.Even tableSize) by apply tableSizeIsEven.
   unfold  StateLib.Index.succ in *.
   case_eq (lt_dec (curidx + 1) tableSize); intros; rewrite H1 in *; try now contradict Hidxsucc.
  inversion Hidxsucc.
  destruct curidx.
  simpl in *. subst.
  clear Hidxsucc.  
  clear Hnoteqmax.
  clear Heqbzero Hreadv.
  unfold Nat.Even in *.
  destruct H0.
  unfold Nat.Odd in *.
  destruct Hoddcuridx.
  subst.
  omega.
  simpl.
  intros nextidx.
   simpl.
   eapply bindRev.
(** writeIndex **)
   eapply weaken.
   eapply WP.writeIndex.
   simpl;intros.
   try repeat rewrite and_assoc in H.
   pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s /\ 
                 StateLib.readIndex phyConfigPagesList iIndex s.(memory) = Some nextidx )
    end.
   simpl in *.
   split. split.
   destruct H.
   assumption.
   assert (Hoddcuridx : Nat.Odd curidx).
   { assert (curidx = CIndex 0 \/ Nat.Odd curidx) by intuition.
    
      assert (false = StateLib.Index.eqb curidx zero) by intuition.
      assert(zero = CIndex 0) by intuition.
      clear H IHn.
      destruct H0.
      
      unfold StateLib.Index.eqb in *.
      symmetry in H1.
      apply beq_nat_false in H1.
      subst.
      now contradict H1.
      assumption. }
   destruct H.
   clear H.
      destruct H0 as (Hodd & Heven & Hzero & Hmax & Hnoteqmax & 
                   Heqbzero & Hnullv & Hreadv & HiIndex & Hnextidx).
   split.
   intros.
   subst.

(** odd : StateLib.readVirtual**)
   assert (idx <> iIndex).
   apply indexSuccGt with curidx; trivial.
   unfold StateLib.readVirtual in *.
   cbn.
   
   assert (Hfalse :Lib.beqPairs(phyConfigPagesList, iIndex) (phyConfigPagesList, idx) beqPage beqIndex
   = false).
   { 
   apply beqPairsFalse; right.
   unfold not; intros; subst; now contradict H2. }
   
   
   rewrite Hfalse in *; trivial.
   assert( Hmemory : Lib.lookup phyConfigPagesList idx (Lib.removeDup phyConfigPagesList iIndex (memory s) beqPage beqIndex)
    beqPage beqIndex = Lib.lookup phyConfigPagesList idx (memory s) beqPage beqIndex).
        { apply removeDupIdentity.
      right. assumption. }
      rewrite Hmemory.
      apply Hodd; trivial.
   split.
 (** even : StateLib.readIndex  **)
 intros.
 unfold  StateLib.readIndex.
 cbn.
   assert (idx <> iIndex).
   apply indexSuccGt with curidx; trivial.
   unfold StateLib.readVirtual in *.
   cbn.
   
   assert (Hfalse :Lib.beqPairs(phyConfigPagesList, iIndex) (phyConfigPagesList, idx) beqPage beqIndex
   = false).
   { 
   apply beqPairsFalse; right.
   unfold not; intros; subst; now contradict H1. }
   
   
   rewrite Hfalse in *; trivial.
   assert( Hmemory : Lib.lookup phyConfigPagesList idx (Lib.removeDup phyConfigPagesList iIndex (memory s) beqPage beqIndex)
    beqPage beqIndex = Lib.lookup phyConfigPagesList idx (memory s) beqPage beqIndex).
        { apply removeDupIdentity.
      right. assumption. }
      rewrite Hmemory.
      apply Heven; trivial.

  intuition.
  (** result :  StateLib.readVirtual **)
   unfold StateLib.readVirtual in *.
   cbn.
   
   assert (Hfalse :Lib.beqPairs(phyConfigPagesList, iIndex) (phyConfigPagesList, curidx) beqPage beqIndex
   = false).
   { 
   apply beqPairsFalse; right.
   unfold not. intros.
   symmetry in H.
   contradict H.
    apply indexSuccEqFalse; trivial. }
   
   rewrite Hfalse in *; trivial.
   assert( Hmemory : Lib.lookup phyConfigPagesList curidx (Lib.removeDup phyConfigPagesList iIndex (memory s) beqPage beqIndex)
    beqPage beqIndex = Lib.lookup phyConfigPagesList curidx (memory s) beqPage beqIndex).
        { apply removeDupIdentity.
      right.
      apply indexSuccEqFalse; trivial. }

  rewrite Hmemory.
  trivial.
  unfold StateLib.readIndex.
   cbn.
   assert (Htrue :Lib.beqPairs (phyConfigPagesList, iIndex) (phyConfigPagesList, iIndex) beqPage beqIndex
   = true).
   apply beqPairsTrue;split;trivial.
   rewrite Htrue; trivial.
   intros [].
(** Recursion **)
   simpl.
   unfold hoareTriple in *.
   intros.
   apply IHn.
   simpl.
   assert (StateLib.Index.succ curidx = Some iIndex /\ StateLib.Index.succ iIndex = Some nextidx) as 
   (Hidxsucc1 & Hidxsucc2) by intuition.
   clear H IHn.
   unfold StateLib.Index.succ in *.
   case_eq (lt_dec (curidx + 1) tableSize) ;intros; rewrite H in *; try now contradict Hidxsucc1.
   case_eq (lt_dec (iIndex + 1) tableSize) ;intros; rewrite H0 in *; try now contradict Hidxsucc2.
   inversion Hidxsucc1; clear Hidxsucc1.
   inversion Hidxsucc2; clear Hidxsucc2.
   simpl in *.
   destruct nextidx.
   inversion H3.
   clear H3.
   destruct iIndex.
   simpl in *; subst.
   inversion H2.
   clear H2.
   destruct curidx.
   simpl in *; subst.
   omega.
   assert (Nat.Odd curidx).
   { assert (curidx = CIndex 0 \/ Nat.Odd curidx) by intuition.
    
      assert (false = StateLib.Index.eqb curidx zero) by intuition.
      assert(zero = CIndex 0) by intuition.
      clear H IHn.
      destruct H0.
      
      unfold StateLib.Index.eqb in *.
      symmetry in H1.
      apply beq_nat_false in H1.
      subst.
      now contradict H1.
      assumption. }
   split.
   right.
   assert (StateLib.Index.succ curidx = Some iIndex /\ StateLib.Index.succ iIndex = Some nextidx) as 
   (Hidxsucc1 & Hidxsucc2) by intuition.
   clear H IHn.
   unfold StateLib.Index.succ in *.
   case_eq (lt_dec (curidx + 1) tableSize) ;intros; rewrite H in *; try now contradict Hidxsucc1.
   case_eq (lt_dec (iIndex + 1) tableSize) ;intros; rewrite H1 in *; try now contradict Hidxsucc2.
   inversion Hidxsucc1; clear Hidxsucc1.
   inversion Hidxsucc2; clear Hidxsucc2.
   simpl in *.
   destruct nextidx.
   inversion H4.
   clear H4.
   destruct iIndex.
   simpl in *; subst.
   inversion H3.
   clear H3.
   destruct curidx.
   simpl in *.
   unfold Nat.Odd  in *.
   destruct H0.
   rewrite H4.
   f_equal.
   subst.
   exists (x+1).
   omega.
    destruct H as ((Hor & Hodd & Heven & Hzero & Hmax & Hnoteqmax & 
             Heqbzero & Hnullv & Hreadv & HiIndex & Hnextidx) & Hreadi).
   split.
   intros.
  
  assert (Horcuridx : idx = curidx \/ idx < curidx).
  apply indexSuccSuccOddOr with iIndex nextidx; trivial.

    destruct Horcuridx.
    subst.
    assumption.
    intuition.
    clear Hor. 
    intros.
       assert (HoriIndex : idx = iIndex \/ idx < iIndex).
{ destruct iIndex.
      simpl in *. 
      unfold StateLib.Index.succ in Hnextidx.
      simpl in *.
      destruct (lt_dec (i + 1) tableSize).
      destruct nextidx.
      simpl in *.
      inversion Hnextidx.
      simpl in *.
      subst.
      simpl in *. 
      rewrite NPeano.Nat.add_1_r in H1.
      apply lt_n_Sm_le in H1.
      apply le_lt_or_eq in H1.
      destruct H1.
      right. assumption.
      left. subst.
      destruct idx. simpl in *.
      subst. 
      assert (Hi = Hi1).
      apply proof_irrelevance.
      subst. reflexivity. inversion Hnextidx. }
    destruct HoriIndex.
    subst.
    exists nextidx.
    assumption.
    apply Heven; trivial.
    apply indexSuccSuccEvenOddLt with iIndex nextidx; trivial.
Qed.

Lemma initConfigPagesListPropagateProperties 
curidx pdChild currentPart currentPD level ptRefChild descChild idxRefChild
      presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1
      ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list pzero phyPDChild phySh1Child phySh2Child phyConfigPagesList 
      phyDescChild:
presentRefChild = true  /\ presentPDChild = true  /\
              presentConfigPagesList = true /\ presentSh1 = true /\ presentSh2 = true
               -> 
{{ fun s : state =>
  (((propagatedProperties false false false false pdChild currentPart currentPD level ptRefChild
        descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1
        idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
        presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
        derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
        derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
        phyDescChild s /\((((forall partition : page,
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
        ~ In phyDescChild (getAccessibleMappedPages partition s))) /\ pzero = CIndex 0) /\ isWellFormedSndShadow level phySh2Child s) /\
    isWellFormedFstShadow level phySh1Child s) /\
   (forall idx : index,
    StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
    StateLib.readPresent phyPDChild idx (memory s) = Some false)  /\ 
   (curidx = (CIndex 0) \/ Nat.Odd curidx)
    }} 

  Internal.initConfigPagesList phyConfigPagesList curidx 
  
  {{ fun _ s  =>
  (((propagatedProperties false false false false pdChild currentPart currentPD level ptRefChild
        descChild idxRefChild presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1
        idxSh1 presentSh1 ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
        presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
        derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
        derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList
        phyDescChild s /\ ((((forall partition : page,
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
        ~ In phyDescChild (getAccessibleMappedPages partition s))) /\pzero = CIndex 0) /\ isWellFormedSndShadow level phySh2Child s) /\
    isWellFormedFstShadow level phySh1Child s) /\
   (forall idx : index,
    StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
    StateLib.readPresent phyPDChild idx (memory s) = Some false)  
   }}.
Proof.
unfold initConfigPagesList.
intros Hlegit.
assert(Hsize : tableSize + curidx >= tableSize) by omega.
revert Hsize.
revert phyConfigPagesList curidx.
generalize tableSize at 1 3. 
induction n.  simpl. 
+ intros. eapply weaken.
  eapply WP.ret. simpl. intros.
  destruct curidx.
  simpl in *.
  clear H.
  contradict Hi.
  omega.
+ intros. simpl.
(** Index.zero **)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.Index.zero.
  intros; simpl.
  pattern s in H;eassumption. 
  intros zero; simpl.
(** getMaxIndex *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getMaxIndex.
  intros; simpl.
  pattern s in H;eassumption. 
  intros maxidx; simpl.
(** MALInternal.Index.eqb *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.Index.eqb.
  intros. simpl.
  pattern s in H.
  eapply H.
  intros eqbMax.     
  simpl.
(** MALInternal.Index.eqb *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.Index.eqb.
  intros. simpl.
  pattern s in H.
  eapply H.
  intros eqbZero.     
  simpl.  
(** the last entry *) 
  case_eq eqbMax;intros HlastEntry.
  { eapply WP.bindRev.
(** getDefaultPage **)
    eapply WP.weaken.
    eapply Invariants.getDefaultPage.
    intros. simpl.
    pattern s in H.
    eassumption.
    simpl.
    subst.
    intros nullP. simpl. 
(** writePhysical **) 
    eapply weaken.
    eapply WP.writePhysical.
    simpl.
    intros.
    repeat rewrite and_assoc in H.
    repeat rewrite and_assoc.
    split.
    destruct H.
    apply propagatedPropertiesUpdateMappedPageData; trivial.
    unfold propagatedProperties in *. 
    intuition.
    unfold propagatedProperties in *.
    intuition.
   unfold propagatedProperties in *.  
   assert(Hcurpart : In currentPart (getPartitions multiplexer s)).
   {unfold consistency in *. 
   intuition; 
   subst;
   unfold currentPartitionInPartitionsList in *;   
   subst;intuition. }
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition.  (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*)  
   
    split. intuition.
(*     split.
    intros. *)
         assert(Hprop : phyConfigPagesList <> phySh2Child). 
    { destruct H.
    clear H0.
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptSh2Child ptConfigPagesList  idxSh2  
    idxConfigPagesList   shadow2 list level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption. }
    assert(Hprop2 : phyConfigPagesList <> phySh1Child). 
    { destruct H.
    clear H0.
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptSh1Child ptConfigPagesList  idxSh1  
    idxConfigPagesList   shadow1 list level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption. }
    assert(Hprop3 : phyConfigPagesList <> phyPDChild).
    { destruct H.
    clear H0.   
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    clear IHn.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptPDChild ptConfigPagesList  idxPDChild  
    idxConfigPagesList   pdChild list level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption. }
    split.
    apply isWellFormedSndShadowUpdateMappedPageData;trivial.
    intuition.
    split.
    apply isWellFormedFstShadowUpdateMappedPageData;trivial.
    intuition.
    assert (Htable : (forall idx : index,
    StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
    StateLib.readPresent phyPDChild idx (memory s) = Some false))
    by intuition.
    intros.
    generalize (Htable idx); clear Htable; intros Htable.
    destruct Htable as (Htable1 & Htable2).
    rewrite <- Htable1.
    rewrite <- Htable2.
    split. 
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial.
    symmetry.
    apply readPresentUpdateMappedPageData;trivial. }
    
    (** the first entry *) 
case_eq eqbZero;intros HfstEntry.
  { (** MALInternal.Index.succ **) 
   eapply bindRev.
   eapply WP.weaken. 
   eapply Invariants.Index.succ.
   intros.
   clear IHn.
   simpl.
   split.
   try repeat rewrite and_assoc in H.  
   pattern s in H.
   eassumption.
   repeat rewrite and_assoc in H.
   destruct H as (Hpp & _  & _ & _ &_ & _ &  _  & _ & _ &_ & _ &  Hzero & Hmax & 
                  Hnoteqmax & Heqbzero).  
   unfold StateLib.Index.eqb in Hnoteqmax.
   symmetry in Hnoteqmax.
   apply beq_nat_false in Hnoteqmax.
   rewrite Hmax in Hnoteqmax.
   apply indexMaxEqFalseLt.
   unfold not; intros.
   subst.
   now contradict Hnoteqmax.
   intros idxsucc.
   simpl.
   eapply bindRev.
(** writeIndex **)
   eapply weaken.
   eapply WP.writeIndex.
   simpl;intros.
   try repeat rewrite and_assoc in H.
   pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s  )
    end.
   simpl in *.
       split.
    destruct H.
    apply propagatedPropertiesUpdateMappedPageData; trivial.
    unfold propagatedProperties in *. 
    intuition.
    unfold propagatedProperties in *.
    intuition.
   unfold propagatedProperties in *.  
   assert(Hcurpart : In currentPart (getPartitions multiplexer s)).
   {unfold consistency in *. 
   intuition; 
   subst;
   unfold currentPartitionInPartitionsList in *;   
   subst;intuition. }
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition.  (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*)  

    split.
 intuition.
          assert(Hprop : phyConfigPagesList <> phySh2Child). 
    { destruct H.
    clear H0.
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptSh2Child ptConfigPagesList  idxSh2  
    idxConfigPagesList   shadow2 list level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption.
    }
    assert(Hprop2 : phyConfigPagesList <> phySh1Child). 
    { destruct H.
    clear H0.
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptSh1Child ptConfigPagesList  idxSh1  
    idxConfigPagesList   shadow1 list level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption.
     }
    
    split.
    apply isWellFormedSndShadowUpdateMappedPageData;trivial.
    intuition.
    split.
    apply isWellFormedFstShadowUpdateMappedPageData;trivial.
    intuition.
    split.
        assert (Htable : (forall idx : index,
     StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
     StateLib.readPresent phyPDChild idx (memory s) = Some false))
    by intuition.
        assert(Hprop3 : phyConfigPagesList <> phyPDChild).
    { destruct H.
    clear H0.   
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    clear IHn.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptPDChild ptConfigPagesList  idxPDChild  
    idxConfigPagesList   pdChild list level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption.
    }
    intros.
    generalize (Htable idx); clear Htable; intros Htable.
    destruct Htable as (Htable1 & Htable2).
    rewrite <- Htable1.
    rewrite <- Htable2.
    split. 
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial.
    symmetry.
    apply readPresentUpdateMappedPageData;trivial.    
    intros.
    intuition.
   intros [].
(** recursion **)
   simpl.
   unfold hoareTriple in *.
   intros.
   apply IHn.
   simpl.
   assert (StateLib.Index.succ curidx = Some idxsucc) by intuition.
   clear H IHn.
   unfold StateLib.Index.succ in *.
   case_eq (lt_dec (curidx + 1) tableSize) ;intros; rewrite H in *.
   inversion H0.
   destruct idxsucc, curidx.
   simpl in *.
   omega.
   now contradict H0.
   split.
   
   intuition.
   split. intuition.
   
   destruct H as (Hpp & _  & _ & _ &_ &  _ &_  & _ & _ &_ &  _ & Hzero & Hmax & 
                  Hnoteqmax & Heqbzero & Hidxsucc).
   (** Nat.Odd idxsucc**)
   { right.
     subst.
     apply indexSEqbZeroOdd with curidx; trivial. } }

(** not the last entry **)
  eapply bindRev.
(** getDefaultPage **)
    eapply WP.weaken.
    eapply Invariants.getDefaultVAddr.
    intros. simpl.
    pattern s in H.
    eassumption.
    simpl.
    subst.
    simpl;intros nullV.
    eapply bindRev.
(** writeVirtual **)
   eapply weaken.
   eapply WP.writeVirtual.
   simpl;intros.
    try repeat rewrite and_assoc in H.
   pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s )
    end.
   simpl in *.
   split.
    destruct H.
        apply propagatedPropertiesUpdateMappedPageData; trivial.
    unfold propagatedProperties in *. 
    intuition.
    unfold propagatedProperties in *.
    intuition.
   unfold propagatedProperties in *.  
   assert(Hcurpart : In currentPart (getPartitions multiplexer s)).
   {unfold consistency in *. 
   intuition; 
   subst;
   unfold currentPartitionInPartitionsList in *;   
   subst;intuition. }
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition.  (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*)  
    split.
   intuition.
            assert(Hprop : phyConfigPagesList <> phySh2Child). 
    { destruct H.
    clear H0.
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptSh2Child ptConfigPagesList  idxSh2  
    idxConfigPagesList   shadow2 list level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption.
    }
    assert(Hprop2 : phyConfigPagesList <> phySh1Child). 
    { destruct H.
    clear H0.
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptSh1Child ptConfigPagesList  idxSh1  
    idxConfigPagesList   shadow1 list level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption.
    }
    assert(Hprop3 : phyConfigPagesList <> phyPDChild).
    { destruct H.
    clear H0.   
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    clear IHn.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptPDChild ptConfigPagesList  idxPDChild  
    idxConfigPagesList   pdChild list level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption.
     }
    split.
    apply isWellFormedSndShadowUpdateMappedPageData;trivial.
    intuition.
    split.
    apply isWellFormedFstShadowUpdateMappedPageData;trivial.
    intuition.
    split. 
    assert (Htable : (forall idx : index,
    StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
    StateLib.readPresent phyPDChild idx (memory s) = Some false))
    by intuition.
    intros.
    generalize (Htable idx); clear Htable; intros Htable.
    destruct Htable as (Htable1 & Htable2).
    rewrite <- Htable1.
    rewrite <- Htable2.
    split. 
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial.
    symmetry.
    apply readPresentUpdateMappedPageData;trivial.
    intuition.
   intros [].
 (** MALInternal.Index.succ **) 
   eapply bindRev.
   eapply WP.weaken. 
   eapply Invariants.Index.succ.
   intros.
   clear IHn.
   simpl.
   split.
   try repeat rewrite and_assoc in H.  
   pattern s in H.
   eassumption.
   repeat rewrite and_assoc in H.
   destruct H as (Hpp & _  & _ & _  & _ & _ & _  & _ & _  & _ & _ & Hzero & Hmax & 
                  Hnoteqmax & Heqbzero & Hnullv).  
   unfold StateLib.Index.eqb in Hnoteqmax.
   symmetry in Hnoteqmax.
   apply beq_nat_false in Hnoteqmax.
   rewrite Hmax in Hnoteqmax.
   apply indexMaxEqFalseLt.
   unfold not; intros.
   subst.
   now contradict Hnoteqmax.
   intros iIndex.
   simpl.
   eapply bindRev.
 (** MALInternal.Index.succ **) 
   eapply WP.weaken. 
   eapply Invariants.Index.succ.
   intros.
   clear IHn.
   simpl.
   split.
   try repeat rewrite and_assoc in H.  
   pattern s in H.
   eassumption.   
   repeat rewrite and_assoc in H.
      destruct H as (Hpp & _  & _ & _ &_ & _  & _ & _ &_ & _ & Hor & Hzero & Hmax & 
                  Hnoteqmax & Heqbzero & Hnullv & Hidxsucc). 

   assert(Hoddcuridx : Nat.Odd curidx).
   {  destruct Hor.
      unfold StateLib.Index.eqb in *.
      symmetry in Heqbzero.
      apply beq_nat_false in Heqbzero.
      subst.
      now contradict Heqbzero.
      assumption. }
   clear Hor.
   unfold StateLib.Index.eqb in Hnoteqmax.
   symmetry in Hnoteqmax.
   apply beq_nat_false in Hnoteqmax.
   assert (curidx < tableSize -1).
   rewrite Hmax in Hnoteqmax.
   apply indexMaxEqFalseLt.
   unfold StateLib.Index.succ in *.
   unfold not; intros.
   subst.
   now contradict Hnoteqmax.
   assert (Nat.Even tableSize) by apply tableSizeIsEven.
   unfold  StateLib.Index.succ in *.
   case_eq (lt_dec (curidx + 1) tableSize); intros; rewrite H1 in *; try now contradict Hidxsucc.
  inversion Hidxsucc.
  destruct curidx.
  simpl in *. subst.
  clear Hidxsucc.  
  clear Hnoteqmax.
  clear Heqbzero .
  unfold Nat.Even in *.
  destruct H0.
  unfold Nat.Odd in *.
  destruct Hoddcuridx.
  subst.
  omega.
  simpl.
  intros nextidx.
   simpl.
   eapply bindRev.
(** writeIndex **)
   eapply weaken.
   eapply WP.writeIndex.
   simpl;intros.
   try repeat rewrite and_assoc in H.
   pattern s in H.
    match type of H with 
    | ?HT s => instantiate (1 := fun tt s => HT s )
    end.
   simpl in *.
   split.
    destruct H.
        apply propagatedPropertiesUpdateMappedPageData; trivial.
    unfold propagatedProperties in *. 
    intuition.
    unfold propagatedProperties in *.
    
    intuition.
   unfold propagatedProperties in *.  
   assert(Hcurpart : In currentPart (getPartitions multiplexer s)).
   {unfold consistency in *. 
   intuition; 
   subst;
   unfold currentPartitionInPartitionsList in *;   
   subst;intuition. }
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition.  (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*) 
   split. apply writeAccessibleRecPostCondUpdateMappedPageData ;subst;intuition. (** New Prop*)  
    
    split.
    intuition.
             assert(Hprop : phyConfigPagesList <> phySh2Child). 
    { destruct H.
    clear H0.
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptSh2Child ptConfigPagesList  idxSh2  
    idxConfigPagesList   shadow2 list level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption.
     }
    assert(Hprop2 : phyConfigPagesList <> phySh1Child). 
    { destruct H.
    clear H0.
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptSh1Child ptConfigPagesList  idxSh1  
    idxConfigPagesList   shadow1 list level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption.
     }
    assert(Hprop3 : phyConfigPagesList <> phyPDChild).
    { destruct H.
    clear H0.   
    unfold propagatedProperties in *.
    unfold consistency in *.
    unfold not.
    intros Hfalse.
    clear IHn.
    intuition.
    symmetry in Hfalse.
    contradict Hfalse.
    apply readMappedPageDataUpdateMappedPageData 
    with currentPart  ptPDChild ptConfigPagesList  idxPDChild  
    idxConfigPagesList   pdChild list level s; trivial.
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    subst.
    intuition.
    repeat rewrite andb_true_iff in Hlegit.
    intuition.
    subst.
    assumption.
    
    }
    split.
    apply isWellFormedSndShadowUpdateMappedPageData;trivial.
    intuition.
    split.
    apply isWellFormedFstShadowUpdateMappedPageData;trivial.
    intuition.
    split. 
    assert (Htable : (forall idx : index,
    StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
    StateLib.readPresent phyPDChild idx (memory s) = Some false))
    by intuition.
    intros.
    generalize (Htable idx); clear Htable; intros Htable.
    destruct Htable as (Htable1 & Htable2).
    rewrite <- Htable1.
    rewrite <- Htable2.
    split. 
    symmetry.
    apply readPhyEntryUpdateMappedPageData; trivial.
    symmetry.
    apply readPresentUpdateMappedPageData;trivial.
    intuition.
   intros [].
(** Recursion **)
   simpl.
   unfold hoareTriple in *.
   intros.
   apply IHn.
   simpl.
   assert (StateLib.Index.succ curidx = Some iIndex /\ StateLib.Index.succ iIndex = Some nextidx) as 
   (Hidxsucc1 & Hidxsucc2) by intuition.
   clear H IHn.
   unfold StateLib.Index.succ in *.
   case_eq (lt_dec (curidx + 1) tableSize) ;intros; rewrite H in *; try now contradict Hidxsucc1.
   case_eq (lt_dec (iIndex + 1) tableSize) ;intros; rewrite H0 in *; try now contradict Hidxsucc2.
   inversion Hidxsucc1; clear Hidxsucc1.
   inversion Hidxsucc2; clear Hidxsucc2.
   simpl in *.
   destruct nextidx.
   inversion H3.
   clear H3.
   destruct iIndex.
   simpl in *; subst.
   inversion H2.
   clear H2.
   destruct curidx.
   simpl in *; subst.
   omega.
   assert (Nat.Odd curidx).
   { assert (curidx = CIndex 0 \/ Nat.Odd curidx) by intuition.
    
      assert (false = StateLib.Index.eqb curidx zero) by intuition.
      assert(zero = CIndex 0) by intuition.
      clear H IHn.
      destruct H0.
      
      unfold StateLib.Index.eqb in *.
      symmetry in H1.
      apply beq_nat_false in H1.
      subst.
      now contradict H1.
      assumption. }
   split.
   intuition.
   split. intuition.
   right.
   assert (StateLib.Index.succ curidx = Some iIndex /\ StateLib.Index.succ iIndex = Some nextidx) as 
   (Hidxsucc1 & Hidxsucc2) by intuition.
   clear H IHn.
   unfold StateLib.Index.succ in *.
   case_eq (lt_dec (curidx + 1) tableSize) ;intros; rewrite H in *; try now contradict Hidxsucc1.
   case_eq (lt_dec (iIndex + 1) tableSize) ;intros; rewrite H1 in *; try now contradict Hidxsucc2.
   inversion Hidxsucc1; clear Hidxsucc1.
   inversion Hidxsucc2; clear Hidxsucc2.
   simpl in *.
   destruct nextidx.
   inversion H4.
   clear H4.
   destruct iIndex.
   simpl in *; subst.
   inversion H3.
   clear H3.
   destruct curidx.
   simpl in *.
   unfold Nat.Odd  in *.
   destruct H0.
   rewrite H4.
   f_equal.
   subst.
   exists (x+1).
   omega.
Qed.