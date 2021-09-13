(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2021)                *)
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
    This file contains required lemmas to help in proving some properties
    on our dependent types defined into [Model.ADT] *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.MAL Pip.Model.Lib.

Require Import Pip.Proof.StateLib.

Require Import Coq.Logic.ProofIrrelevance Arith Lia Bool.

(** ADT : level **)
Lemma levelEqBEqNatTrue :
forall l l' : level, StateLib.Level.eqb l l' = true -> l = l' .
 Proof.
 intros l l' H.  
 unfold StateLib.Level.eqb in H. 
 apply beq_nat_true in H.
 destruct l.
 destruct l'. simpl in *.
 subst.
 assert (Hl = Hl0).
 apply proof_irrelevance. subst. intuition.
Qed.

Lemma levelEqBEqNatFalse : 
forall l ,
StateLib.Level.eqb l fstLevel = false -> l > fstLevel.
Proof.
intros.
unfold StateLib.Level.eqb in H.
apply beq_nat_false in H.
unfold fstLevel in *.
unfold CLevel in *.
case_eq (lt_dec 0 nbLevel).
intros.
rewrite H0 in *.
simpl in *. lia.
intros.
assert (0 < nbLevel). 
apply nbLevelNotZero.
contradict H1.
intuition. 
Qed. 

Lemma levelEqBEqNatFalse0 : 
forall l ,
StateLib.Level.eqb l fstLevel = false -> l > 0.
Proof.
intros.
unfold StateLib.Level.eqb in H.
apply beq_nat_false in H.
unfold fstLevel in H.
unfold CLevel in H.
case_eq (lt_dec 0 nbLevel).
intros.
rewrite H0 in H.
simpl in *. lia.
intros.
assert (0 < nbLevel). 
apply nbLevelNotZero.
contradict H1.
intuition. 
Qed. 

Lemma levelEqBEqNatTrue0 : 
forall l ,
StateLib.Level.eqb l fstLevel = true -> l <= 0.
Proof.
intros.
unfold StateLib.Level.eqb in H.
apply beq_nat_true in H.
unfold fstLevel in H.
unfold CLevel in H.
case_eq (lt_dec 0 nbLevel).
intros.
rewrite H0 in H.
simpl in *. lia.
intros.
assert (0 < nbLevel). 
apply nbLevelNotZero.
contradict H1.
intuition. 
Qed.
 
Lemma levelPredNone nbL:
StateLib.Level.eqb nbL fstLevel = false ->
StateLib.Level.pred nbL <> None.
Proof.
intros.
unfold Level.pred.
case_eq(gt_dec nbL 0); intros.
unfold not; intros.
inversion H1.
apply levelEqBEqNatFalse0 in H.
lia.
Qed.

Lemma levelPredLt nbL l :
StateLib.Level.eqb nbL fstLevel = false ->
StateLib.Level.pred nbL = Some l -> 
l < nbL. 
Proof.
intros.
unfold Level.pred in *.
case_eq(gt_dec nbL 0); intros.
rewrite H1 in *.
inversion H0.
simpl in *.
lia.
apply levelEqBEqNatFalse0 in H.
lia.
Qed.    

Lemma CLevel0_r :  forall l : level,l - CLevel 0 = l. 
Proof. 
unfold CLevel.
case_eq (lt_dec 0 nbLevel).
intros.
simpl. lia.
intros.
assert (0 < nbLevel).
apply nbLevelNotZero. lia.
Qed.

Lemma CLevelIdentity : forall l : level, CLevel (l - CLevel 0) = l.
Proof.
intros l.
rewrite CLevel0_r. destruct l.
simpl.
unfold CLevel. 
case_eq(lt_dec l nbLevel).
intros. simpl.
assert ( Hl = ADT.CLevel_obligation_1 l l0).
apply proof_irrelevance.
subst. reflexivity.
intros.
contradict H. 
lia.
Qed.

Lemma CLevelIdentity1 : forall l : level, CLevel l  = l.
Proof.
intros l.
unfold CLevel. 
case_eq(lt_dec l nbLevel).
intros. simpl.
destruct l.
simpl.
f_equal.
apply proof_irrelevance.
subst.
intros.
destruct l.
simpl in *. 
lia.
Qed.

Lemma CLevelIdentityLe :
forall a , a < nbLevel ->  a <= CLevel a.
Proof.
intros.
unfold CLevel.
case_eq (lt_dec a nbLevel); intros.
simpl; lia.
now contradict H.
Qed.

Lemma levelPredMinus1: forall l l' , StateLib.Level.eqb l fstLevel = false -> StateLib.Level.pred l = Some l' -> l' = CLevel (l - 1).
Proof.
intros. 
unfold StateLib.Level.pred  in *.
assert (l > 0).
{ apply levelEqBEqNatFalse0.
  assumption. }
case_eq (gt_dec l 0).
* intros.
  rewrite H2 in H0.
  inversion H0.
  unfold CLevel.
  case_eq (lt_dec (l - 1) nbLevel).
  intros. subst.   
  assert (ADT.CLevel_obligation_1 (l - 1) l0  = StateLib.Level.pred_obligation_1 l g ).
  apply proof_irrelevance. 
  rewrite H4. reflexivity.
  intros.
  destruct l.
  subst. 
  simpl in *.
  contradict H3.
  lia.
* intros.
  contradict H1.
  assumption.
Qed.

Lemma levelEqNat : 
forall a b , a < nbLevel -> b < nbLevel -> CLevel a = CLevel b -> a = b.
Proof.
intros a b Ha Hb Hab.
 unfold CLevel in *.
 case_eq (lt_dec a nbLevel );intros g Ha'.
 + rewrite Ha' in Hab.
   case_eq (lt_dec b nbLevel);intros p Hb'.
   - rewrite Hb' in Hab.
     inversion Hab. intuition.
   - lia.
 + lia.
Qed.

Lemma level_gt : 
forall x x0, x - x0 < nbLevel ->  CLevel (x - x0) > 0 -> x > x0.
Proof.
intros.
unfold CLevel in *.
case_eq (lt_dec (x - x0) nbLevel ).
intros. rewrite H1 in H0.
simpl in *. lia.
intros. contradict H1. lia.
Qed.

Lemma getNbLevelLe : 
forall nbL, 
Some nbL = StateLib.getNbLevel -> 
nbL <= CLevel (nbLevel - 1).
Proof.
intros.
unfold getNbLevel in *.
destruct (gt_dec nbLevel 0).
inversion H. 
unfold CLevel.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros.
simpl.
lia.
lia.
assert (0 < nbLevel) by apply nbLevelNotZero.
lia.
Qed.

Lemma getNbLevelEq : 
forall nbL, 
Some nbL = StateLib.getNbLevel -> 
nbL = CLevel (nbLevel - 1).
Proof.
intros.
unfold getNbLevel in *.
destruct (gt_dec nbLevel 0).
inversion H.
destruct nbL.
simpl in *.
 
unfold CLevel.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros.
inversion H.
subst.
f_equal.
apply proof_irrelevance.
assert (0 < nbLevel) by apply nbLevelNotZero.
lia.
now contradict H.
Qed.

Lemma getNbLevelEqOption : 
 StateLib.getNbLevel= Some (CLevel (nbLevel - 1)).
Proof.
unfold getNbLevel in *.
destruct (gt_dec nbLevel 0);simpl.
f_equal.
unfold CLevel.
case_eq (lt_dec (nbLevel - 1) nbLevel); simpl in *;intros.
f_equal.
apply proof_irrelevance.
lia.
assert (0 < nbLevel) by apply nbLevelNotZero.
lia.
Qed.

Lemma nbLevelEq :
nbLevel - 1 = CLevel (nbLevel - 1).
Proof.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel); intros.
simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
Qed.

Lemma fstLevelLe :
forall l: level ,
fstLevel <= l.
Proof.
unfold fstLevel.
unfold CLevel.
intros.
case_eq( lt_dec 0 nbLevel);intros.
simpl;lia.
assert(0 <nbLevel) by apply nbLevelNotZero.
lia.
Qed.
 
Lemma getNbLevelLt nbL:
StateLib.getNbLevel = Some nbL -> nbL < nbLevel.
Proof.
intros.
unfold  StateLib.getNbLevel in *.
destruct (gt_dec nbLevel 0).
inversion H.
simpl;trivial.
lia.
now contradict H.
Qed.

Lemma notFstLevel (level1 : level) : 
 0 < level1 -> 
StateLib.Level.eqb level1 fstLevel = false.
Proof. 
unfold Level.eqb.
intros.
apply NPeano.Nat.eqb_neq.
unfold fstLevel. 
unfold CLevel.
case_eq (lt_dec 0 nbLevel);intros. 
simpl.
lia.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
Qed.

Lemma ClevelMinus0Eq (nbL: level) stop :
stop <= nbL -> 
nbL = CLevel (nbL - stop) -> 
stop = 0.
Proof.
intros.
destruct nbL;simpl.
unfold CLevel in *.
simpl in *.
case_eq(lt_dec (l - stop) nbLevel );intros;rewrite H1 in *.
inversion H0.
subst.
clear H0 H1.
lia.
lia.
Qed.

Lemma ClevelMinus0Le (nbL: level) stop :
stop <= nbL -> 
nbL <= CLevel (nbL - stop) -> 
stop = 0.
Proof.
intros.
destruct nbL;simpl.
unfold CLevel in *.
simpl in *.
case_eq(lt_dec (l - stop) nbLevel );intros;rewrite H1 in *.
simpl in *.
lia.
inversion H0.
subst.
clear H0 H1.
lia.
lia.
Qed.

(**** ADT : page **)
Lemma isDefaultPageFalse : forall p,   (defaultPage =? pa p) = false -> pa p <> defaultPage .
Proof.
intros. 
apply beq_nat_false in H.
unfold not. intros.
contradict H. symmetry.
unfold defaultPage in *.
unfold CPage in *.
case_eq (lt_dec 0 nbPage).
intros.
rewrite H in H0.
rewrite H0. trivial.
intros.
rewrite H in H0. rewrite H0. intuition.
Qed.

Lemma isDefaultPageTrue : forall p,   (defaultPage =? pa p) = true -> pa p = defaultPage .
Proof.
intros. 
apply beq_nat_true in H. symmetry.
unfold defaultPage in *.
unfold CPage in *.
case_eq (lt_dec 0 nbPage).
intros.
rewrite H0 in H.
symmetry.
simpl in *.
destruct p.
simpl in *. 
subst.
destruct pa.
simpl in *.
subst.
assert (Hp = ADT.CPage_obligation_1 0 l ).
apply proof_irrelevance.
subst.
intuition.
intros.
rewrite H0 in H.
subst.
simpl in *.
destruct p.
simpl in *. 
subst.
destruct pa.
simpl in *.
subst.
destruct page_d.
simpl in *.
assert (Hp = Hp0).
apply proof_irrelevance.
subst.
intuition.
Qed.

Lemma pageDecOrNot :
forall p1 p2 : page, p1 = p2 \/ p1<>p2.
Proof.
destruct p1;simpl in *;subst;destruct p2;simpl in *;subst.
assert (Heq :p=p0 \/ p<> p0) by lia.
destruct Heq as [Heq|Heq].
subst.
left;f_equal;apply proof_irrelevance.
right. unfold not;intros.
inversion H.
subst.
now contradict Heq.
Qed.

Lemma listPageDecOrNot :
forall x (l: list page), List.In x l \/ 
              ~List.In x l.
Proof.              
induction l;trivial.
right;intuition.
simpl.
assert(a=x \/ a<> x) by apply pageDecOrNot.
destruct H.
left;left;trivial.
destruct IHl.
left;right;trivial.
right.
apply Logic.Classical_Prop.and_not_or. intuition.
Qed. 
             
             
(** ADT : index **)
Lemma indexEqFalse : 
forall a b : nat , a < tableSize -> b < tableSize -> a <> b -> CIndex a <> CIndex b.
Proof.
intros.
unfold CIndex.
case_eq (lt_dec a tableSize).
+ intros.
  case_eq (lt_dec b tableSize).
  - intros.
    unfold not in *.
    intros.
    apply H1.
    inversion H4.
    intuition.
  - intros. contradict H0. assumption.
+ intros. contradict H. intuition.
Qed. 

Lemma indexltbTrue : 
forall i1 i2 : index , 
StateLib.Index.ltb i1 i2 = true -> i1 < i2.
Proof. intros. unfold MALInternal.Index.ltb in H. 
apply NPeano.Nat.ltb_lt in H.
assumption.
Qed. 

Lemma indexltbFalse : 
forall i1 i2 : index , 
StateLib.Index.ltb i1 i2 = false -> i1 >= i2.
Proof.
intros.
unfold MALInternal.Index.ltb in *. 
apply not_lt.
apply NPeano.Nat.ltb_nlt in H.
lia.
Qed. 

Lemma indexBoundEq : 
forall i : index , i>= CIndex (tableSize - 1) -> i =  CIndex (tableSize - 1). 
Proof.
intros.
unfold CIndex in *.
destruct (lt_dec (tableSize - 1) tableSize).
simpl in *.
destruct i.
simpl in *. 
subst.
assert(i = tableSize - 1). lia.
subst. 
assert (Hi = ADT.CIndex_obligation_1 (tableSize - 1) l ).
apply proof_irrelevance.
subst. trivial.
contradict n.
assert (0 < tableSize).
assert (tableSize > tableSizeLowerBound). 
apply tableSizeBigEnough.
unfold  tableSizeLowerBound in * . lia. lia.
Qed.

Lemma indexDiffLtb :
forall i1 i2 : index, i2 < i1 \/ i1 < i2 <-> i2 <> i1.
Proof.
intros.
split;destruct i1, i2;
simpl in *.
 unfold not;
intros;
inversion H0; lia.
intros.
apply nat_total_order.
unfold not in *; intros; subst.
apply H; f_equal.
apply proof_irrelevance.
Qed.

Lemma indexEqId : 
forall i : index, CIndex i = i. 
Proof.
intros.
unfold CIndex.
destruct i.
simpl.
case_eq(lt_dec i tableSize); intros.
assert(ADT.CIndex_obligation_1 i l = Hi) by apply proof_irrelevance.
subst. reflexivity.
now contradict Hi.
Qed.

Lemma indexMaxEqFalseLt : 
forall idx : index, idx <> CIndex (tableSize - 1) -> idx < tableSize - 1.
Proof.
intros.
unfold CIndex in *.
case_eq (lt_dec (tableSize - 1) tableSize).
intros .
rewrite H0 in *.
destruct idx.
simpl in *.
apply not_ge.
unfold not.
intros.
contradict H.
assert (i = tableSize - 1).
lia.
subst.
f_equal.
apply proof_irrelevance.
intros.
assert(tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
lia.
Qed.

Lemma SuccOddEven :
forall oneI twoI : index, 
oneI < tableSize -1 -> 
StateLib.Index.succ oneI = Some twoI -> 
Nat.Odd oneI -> 
Nat.Even twoI.
Proof.
intros.
unfold StateLib.Index.succ in *.
case_eq (lt_dec (oneI + 1) tableSize);intros; rewrite H2 in *;simpl in *.
inversion H0.
simpl in *.
revert H1.
clear.
intros.
destruct oneI.
simpl in *.
rewrite <- Nat.Even_succ in H1.
unfold Nat.Even in *.
destruct H1 as (m & Hm).
exists m.
lia.
now contradict H0.   
Qed.

Lemma SuccEvenOdd :
forall oneI twoI : index, 
oneI < tableSize -1 -> 
StateLib.Index.succ oneI = Some twoI -> 
Nat.Even oneI -> 
Nat.Odd twoI.
Proof.
intros.
unfold StateLib.Index.succ in *.
case_eq (lt_dec (oneI + 1) tableSize);intros; rewrite H2 in *;simpl in *.
inversion H0.
simpl in *.
revert H1.
clear.
intros.
destruct oneI.
simpl in *.
rewrite <- Nat.Odd_succ in H1.
unfold Nat.Odd in *.
destruct H1 as (m & Hm).
exists m.
lia.
now contradict H0.   
Qed.

Lemma indexMaxEqFalseLt1 : 
forall idx : index, idx <> CIndex (tableSize - 1) -> idx < CIndex (tableSize - 1).
Proof.
intros.
unfold CIndex in *.
case_eq (lt_dec (tableSize - 1) tableSize).
intros .
rewrite H0 in *.
destruct idx.
simpl in *.
apply not_ge.
unfold not.
intros.
contradict H.
assert (i = tableSize - 1).
lia.
subst.
f_equal.
apply proof_irrelevance.
intros.
assert(tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
lia.
Qed.

Lemma noteqIndex a b:
a < tableSizeLowerBound -> b < tableSizeLowerBound -> a<>b ->  
CIndex a <> CIndex b.
Proof.
intros. 
apply indexEqFalse;
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
lia.  apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
lia. apply tableSizeBigEnough. lia.
Qed.

Lemma CIndex0lt :
CIndex 0 < tableSize - 1.
Proof.
unfold CIndex.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
case_eq(lt_dec 0 tableSize);intros;simpl;try lia.
Qed.

Lemma CIndex1lt oneI:
StateLib.Index.succ (CIndex 0) = Some oneI-> 
oneI < tableSize - 1.
Proof.
unfold StateLib.Index.succ.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
case_eq(lt_dec (CIndex 0 + 1) tableSize);intros;simpl in *;try lia.
inversion H1.
simpl.
unfold CIndex.
case_eq(lt_dec 0 tableSize);intros;simpl;try lia.
now contradict H1.
Qed.

Lemma indexEqbTrue : 
forall idx1 idx2 : index, true = StateLib.Index.eqb idx1 idx2 -> 
idx1 = idx2.
Proof.
unfold StateLib.Index.eqb in *.
intros.
symmetry in H.
apply beq_nat_true in H.
destruct idx1; destruct idx2.
simpl in *.
subst.
f_equal.
apply proof_irrelevance.
Qed.


Lemma indexLtZero : 
forall idx : index, idx < CIndex 0 -> False.
Proof.
intros.
unfold CIndex in *.
case_eq (lt_dec 0 tableSize); intros; rewrite H0 in *.
destruct idx. simpl in *.
lia.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
lia.
Qed.

Lemma indexSEqbZeroOdd : 
forall curidx idxsucc, 
true = StateLib.Index.eqb curidx (CIndex 0) -> 
StateLib.Index.succ curidx = Some idxsucc -> 
Nat.Odd idxsucc.
Proof.
intros.
apply indexEqbTrue in H.
subst.
unfold Index.succ in *.
case_eq (lt_dec (CIndex 0 + 1) tableSize); intros; rewrite H in *.
inversion H0.
destruct idxsucc.
inversion H2.
subst.
unfold Nat.Odd.
eexists 0.
simpl.
unfold CIndex.
case_eq (lt_dec 0 tableSize); intros.
simpl. trivial.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
lia.
now contradict H0.
Qed.

Lemma indexSuccNot0:
forall FFI nextFFI,
StateLib.Index.succ FFI = Some nextFFI -> 
(CIndex 0) <> nextFFI .
Proof.
intros. 
unfold Index.succ in *.
case_eq(lt_dec (FFI + 1) tableSize);intros; rewrite H0 in *.
inversion H.
simpl in *.
unfold CIndex.
case_eq( lt_dec 0 tableSize);intros.
contradict H2.
inversion H2.
unfold not;intros.
subst.
lia.
pose proof tableSizeBigEnough.
lia.
now contradict H.
Qed.

Lemma indexZeroNotOdd : 
forall idx idxsucc : index,
idx < idxsucc -> 
StateLib.Index.succ (CIndex 0) = Some idxsucc ->
~ Nat.Odd idx.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec (CIndex 0 + 1) tableSize); intros; rewrite H1 in *.
inversion H0.
destruct idxsucc.
inversion H3.
subst.
clear H0 H3.
simpl in *.
unfold CIndex in H.
case_eq (lt_dec 0 tableSize); intros.
simpl. rewrite H0 in *.
simpl in *.
unfold not.
intros.
unfold Nat.Odd in *.
destruct H2.
rewrite H2 in *.
lia.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
lia.
now contradict H0.
Qed.
 
 Lemma indexSEqbZeroLt : 
forall  idxsucc idx : index, 
StateLib.Index.succ (CIndex 0)  = Some idxsucc -> 
idx < idxsucc -> 
idx = CIndex 0.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec (CIndex 0 + 1) tableSize); intros; rewrite H1 in *.
inversion H.
destruct idxsucc.
inversion H3.
subst.
clear H H3 H1  l.
simpl in *.
unfold CIndex in *.
case_eq (lt_dec 0 tableSize); intros; rewrite H in *.
simpl in *.
destruct idx.
simpl in *.
destruct i.
f_equal.
apply proof_irrelevance.
lia.
assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
lia.
now contradict H0.
Qed.

Lemma indexSuccGt : 
forall idx curidx iIndex : index,
StateLib.Index.succ curidx = Some iIndex -> 
idx < curidx -> 
idx <> iIndex.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec(curidx + 1) tableSize); intros; rewrite H1 in *.
simpl in *.
destruct idx.
simpl in *.
destruct iIndex.
inversion H.
unfold not; intros.
inversion H2.
subst.
lia.
now contradict H.
Qed.
Lemma Succ0is1 oneI:
StateLib.Index.succ (CIndex 0) = Some oneI -> 
oneI = CIndex 1.
Proof.
intros.
unfold StateLib.Index.succ in *.

assert(CIndex 0 + 1 = 1).
{
unfold CIndex.
case_eq (lt_dec 0 tableSize );intros. 
simpl;trivial.  
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
lia. }
 unfold Ops.idxSuccM_obligation_1 in *.
rewrite H0 in *.
case_eq(lt_dec 1 tableSize);intros;simpl in *;
rewrite H1 in *;try lia.
inversion H.
subst.
unfold CIndex.
rewrite H1.
f_equal.
now contradict H1.
Qed.

Lemma indexSuccEqFalse: 
forall  curidx iIndex : index,
StateLib.Index.succ curidx = Some iIndex -> 
 curidx <> iIndex.
Proof.
intros.
unfold Index.succ in *.
case_eq (lt_dec(curidx + 1) tableSize); intros; rewrite H0 in *.
simpl in *.
destruct iIndex.
inversion H.
subst.
clear H.
unfold not; intros.
destruct curidx.
simpl in *.
inversion H.
lia.
now contradict H.
Qed.

Lemma indexSuccSuccOddOr (curidx iIndex nextidx idx : index): 
StateLib.Index.succ curidx = Some iIndex ->
StateLib.Index.succ iIndex = Some nextidx -> 
Nat.Odd curidx -> 
Nat.Odd idx -> 
idx < nextidx -> 
idx = curidx \/ idx < curidx.
Proof.
intros.
unfold StateLib.Index.succ in *.
      destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
      inversion H; clear H.
      destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
      inversion H0; clear H0.
      destruct nextidx.
      inversion H4; clear H4.
      destruct iIndex.
      simpl in *.
      subst.
      inversion H5; clear H5.
      destruct curidx.
      simpl in *.
      destruct idx.
      simpl in *.
      rewrite <- H0 in H3.
      clear H0 Hi l0 l Hi0 .
      assert (i1 = i \/ i1 < i).
      unfold Nat.Odd in *.
      destruct H1 ; destruct H2.
      
      lia.
      destruct H.
      left.
      subst.
      f_equal.
      apply proof_irrelevance.
      right; trivial.
Qed.
      
Lemma indexSuccSuccEvenOr (curidx iIndex nextidx idx : index): 
StateLib.Index.succ curidx = Some iIndex ->
StateLib.Index.succ iIndex = Some nextidx -> 
Nat.Even curidx -> 
Nat.Even idx -> 
idx < nextidx -> 
idx = curidx \/ idx < curidx.
Proof.
intros.
unfold StateLib.Index.succ in *.
      destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
      inversion H; clear H.
      destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
      inversion H0; clear H0.
      destruct nextidx.
      inversion H4; clear H4.
      destruct iIndex.
      simpl in *.
      subst.
      inversion H5; clear H5.
      destruct curidx.
      simpl in *.
      destruct idx.
      simpl in *.
      rewrite <- H0 in H3.
      clear H0 Hi l0 l Hi0 .
      assert (i1 = i \/ i1 < i).
      destruct H1 ; destruct H2.
      lia.
      destruct H.
      left.
      subst.
      f_equal.
      apply proof_irrelevance.
      right; trivial.
Qed.

Lemma indexSuccSuccEvenOddLt (curidx iIndex nextidx idx : index): 
StateLib.Index.succ curidx = Some iIndex ->
StateLib.Index.succ iIndex = Some nextidx -> 
Nat.Even idx -> 
Nat.Odd curidx -> 
idx < nextidx -> 
idx < iIndex -> 
idx < curidx.
Proof.
intros.
unfold StateLib.Index.succ in *.
      destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
      inversion H; clear H.
      destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
      inversion H0; clear H0.
      destruct nextidx.
      inversion H5; clear H5.
      destruct iIndex.
      simpl in *.
      subst.
      inversion H6; clear H6.
      destruct curidx.
      simpl in *.
      destruct idx.
      simpl in *.
      destruct H1; destruct H2.
      subst.
      
      lia.
Qed.
Lemma indexSuccSuccOddEvenLt (curidx iIndex nextidx idx : index): 
StateLib.Index.succ curidx = Some iIndex ->
StateLib.Index.succ iIndex = Some nextidx -> 
Nat.Odd idx -> 
Nat.Even curidx -> 
idx < nextidx -> 
idx < iIndex -> 
idx < curidx.
Proof.
intros.
unfold StateLib.Index.succ in *.
destruct (lt_dec (curidx + 1) tableSize); try now contradict H.
inversion H; clear H.
destruct (lt_dec (iIndex + 1) tableSize); try now contradict H0.
inversion H0; clear H0.
destruct nextidx.
inversion H5; clear H5.
destruct iIndex.
simpl in *.
subst.
inversion H6; clear H6.
destruct curidx.
simpl in *.
destruct idx.
simpl in *.
destruct H1; destruct H2.
subst.
lia.
Qed.

Lemma succLet (Scuridx SScuridx idx:index):

StateLib.Index.succ Scuridx = Some SScuridx -> 
idx < SScuridx -> 
idx = Scuridx \/ idx < Scuridx.
Proof.
intros.
unfold Index.succ in *.
case_eq(lt_dec (Scuridx + 1) tableSize);intros;rewrite H1 in *.
inversion H.
destruct SScuridx;simpl in *.
clear H.
inversion H3.
subst.
replace (Scuridx + 1) with (S Scuridx) in *by lia.
apply lt_n_Sm_le in H0.
apply or_comm.
clear H1 H3.
intros.
destruct Scuridx;simpl in *;destruct idx;simpl in *.
rewrite Nat.le_lteq in H0.
destruct H0.
left;trivial.
right.
subst.
f_equal.
apply proof_irrelevance.
now contradict H0.
Qed.
  
  
  
Lemma indexNotEqSuccNotEq (idx1 idx2 : index): 
idx1 < tableSize -1 -> 
idx2 < tableSize -1 -> 
idx1 <> idx2 -> 
StateLib.Index.succ idx2 <> StateLib.Index.succ idx1.
Proof.
intros.
unfold Index.succ.
case_eq (lt_dec (idx2 + 1) tableSize); intros; try lia.
case_eq (lt_dec (idx1 + 1) tableSize); intros; try lia.
destruct idx1; destruct idx2; simpl in *.
unfold not; intros Hfalse.
inversion Hfalse.
assert (i0 = i) by lia.
subst.
contradict H1.
f_equal.
apply proof_irrelevance.
Qed.

Lemma tableSizeMinus0: 
forall idx: index,  idx = CIndex (tableSize - 1) -> idx>0.
Proof.
intros.
unfold CIndex in *.
assert(tableSize > tableSizeLowerBound) by apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
case_eq(lt_dec (tableSize - 1) tableSize);intros Hcase Hcasedec;rewrite Hcasedec in *;
simpl in *.
destruct idx;simpl in *.
inversion H;subst.
lia.
lia.
Qed. 

Lemma tableSizeMinus2: 
CIndex (tableSize - 1) - 1 = tableSize - 2. 
Proof.
unfold CIndex.
case_eq(lt_dec (tableSize - 1) tableSize);intros;simpl in *;try lia.
assert(tableSize> tableSizeLowerBound).
apply tableSizeBigEnough.
lia.
Qed.

Lemma TableSizeMinus2: 
forall idx, idx < CIndex (tableSize - 2) -> idx < CIndex (tableSize - 1).
Proof.
intros.
unfold CIndex in *.
assert(tableSize > tableSizeLowerBound) by apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
case_eq( lt_dec (tableSize - 2) tableSize);intros Hi Hii ; rewrite Hii in *;simpl in *; try lia. 
case_eq (lt_dec (tableSize - 1) tableSize);intros;simpl; lia.
Qed.
 
Lemma predMaxIndex :
forall i,  StateLib.Index.pred (CIndex (tableSize - 1)) = Some i -> 
i = CIndex (tableSize - 2).
Proof.
intros.
unfold StateLib.Index.pred in *.
case_eq( gt_dec (CIndex (tableSize - 1)) 0);intros;rewrite H0 in *;try now contradict H.
inversion H.
clear H H2.
assert(tableSize> tableSizeLowerBound).
apply tableSizeBigEnough.
rewrite <- tableSizeMinus2.
unfold CIndex at 3.
case_eq(lt_dec (CIndex (tableSize - 1) - 1) tableSize);simpl;intros;try lia.
f_equal.
apply proof_irrelevance.
clear H0 H1.
contradict n.
unfold CIndex in *.
case_eq(lt_dec (tableSize - 1) tableSize);intros;simpl in *;
rewrite H0 in *.
simpl in *.
lia.
lia.
Qed.
(** ADT : vaddr **)
Lemma lengthVAddrNotZero (va : vaddr) : fstLevel < (length va -1).
Proof. 
 unfold fstLevel.  destruct va.
 simpl. rewrite Hva. unfold CLevel. case_eq (lt_dec 0 nbLevel).
 simpl. intros. lia.
 intros. destruct level_d. simpl. lia. 
 Qed.

Lemma CLevelMinusEq0 : 
forall (a : level) b , CLevel (a -  b) = CLevel 0 ->   a = CLevel b \/ a < b. 
Proof.
intros.
unfold CLevel in *.  
case_eq (lt_dec (a - b) nbLevel );
intros lab Hab; rewrite Hab in *.
case_eq(lt_dec 0 nbLevel);
intros l0 H0;
rewrite H0 in*.
inversion H.
case_eq (lt_dec b nbLevel);
intros lb Hb.
simpl in *.
apply NPeano.Nat.sub_0_le in H2.
apply le_lt_or_eq in H2.
destruct H2. 
right; assumption.
left.
destruct a.
simpl in *.
subst.
assert (Hl =  ADT.CLevel_obligation_1 b lb ) by 
apply proof_irrelevance.
subst. reflexivity.
right; destruct a; simpl in *; lia.
assert (0 < nbLevel) by apply nbLevelNotZero.
now contradict H1.
destruct a. simpl in *.
lia.
Qed.


(** beqPairs **)
Lemma beqPairsTrue : 
forall table1 idx1 table2 idx2 , table1 = table2 /\ idx1 = idx2 <->   
beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex = true.
Proof.
intros.
unfold beqPairs.
cbn.  
unfold beqPage , beqIndex .
split.
* case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
  apply beq_nat_false in H.  
  destruct idx1 , idx2. simpl in *. inversion H3. lia.  
  apply beq_nat_false in H0.
  destruct table1, table2. simpl in *.
  inversion H2. lia.
  destruct ((false && false)%bool). trivial.
  apply beq_nat_false in H0.
  destruct table1, table2. simpl in *.
  inversion H2. lia.
* intros. 
  case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
  apply beq_nat_true in H1; trivial.
  destruct table1, table2; simpl in *; subst; f_equal; apply proof_irrelevance. 
  destruct idx1 , idx2; simpl in *.
  apply beq_nat_true in H0; subst; f_equal; apply proof_irrelevance.
  apply beq_nat_true in H1; trivial.
  destruct table1, table2; simpl in *; subst; f_equal; apply proof_irrelevance.
  rewrite H0 in H.
  rewrite H1 in H. 
  case_eq ((true && false)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.
  rewrite H2 in H; now contradict H.
  rewrite H0 in H.
  rewrite H1 in H. 
  case_eq ((false && true)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.
  rewrite H2 in H; now contradict H.
  apply beq_nat_true in H0.
  destruct idx1 , idx2; simpl in *;subst; f_equal; apply proof_irrelevance. 
  rewrite H0 in H.
  rewrite H1 in H. 
  case_eq ((false && false)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.  
  rewrite H2 in H; now contradict H.
  rewrite H0 in H.
  rewrite H1 in H. 
  case_eq ((false && false)%bool); intros.
  apply Bool.andb_true_iff in H2.
  now contradict H2.  
  rewrite H2 in H; now contradict H.
Qed.

Lemma beqPairsFalse : 
forall table1 idx1 table2 idx2 , 
table1 <> table2 \/ idx1 <> idx2 <-> 
beqPairs (table1, idx1) (table2, idx2) beqPage beqIndex = false.
Proof.
intros.
unfold beqPairs.
cbn.  
unfold beqPage , beqIndex .
intuition.
case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
contradict H0.
apply beq_nat_true in H1.
destruct table1, table2. simpl in *. subst.
assert (Hp = Hp0).
apply proof_irrelevance. subst. trivial. 
assert((idx1 =? idx2) = false).
apply Nat.eqb_neq. unfold not.
intros.
destruct idx1; destruct idx2.
simpl in *.
subst.
apply H0.
f_equal.
apply proof_irrelevance.
rewrite H.
case_eq ((table1 =? table2) && false).
intros.
apply andb_true_iff in H1.
intuition.
trivial.
case_eq (table1 =? table2) ; case_eq(idx1 =? idx2);intuition.
+ rewrite H1 in H.
  rewrite H0 in H.
  intuition.
+ apply beq_nat_false in H0.
  right.
  intros. 
  destruct idx1; destruct idx2.
  simpl in *.
  inversion H2.
  subst.
  now contradict H0.
+ apply beq_nat_false in H1.
  left.
  intros. 
  destruct table1; destruct table2.
  simpl in *.
  inversion H2.
  subst.
  now contradict H1.
+ apply beq_nat_false in H1.
  left.
  intros. 
  destruct table1; destruct table2.
  simpl in *.
  inversion H2.
  subst.
  now contradict H1.
Qed.
Require Import List Classical_Prop.
Lemma listIndexDecOrNot :
forall p1 p2 : list index, p1 = p2 \/ p1<>p2.
Proof.
induction p1;intros.
induction p2;intros.
left;trivial.
simpl.
right;intuition.
now contradict H.
now contradict H.
induction p2;simpl;intros.
right;intuition.
now contradict H.
destruct IHp2.
rewrite H.
right.
clear.
induction p2;simpl.
intuition.
now contradict H.
unfold not;intros. contradict IHp2.
inversion H.
subst.
trivial.
apply NNPP.
unfold not at  1.
intros.
apply not_or_and in H0.
destruct H0.
now contradict H1.
Qed.

Lemma vaddrDecOrNot :
forall p1 p2 : vaddr, p1 = p2 \/ p1<>p2.
Proof.
destruct p1;destruct p2;simpl in *.
assert(Hor : va = va0 \/ va<>va0).
apply listIndexDecOrNot.
destruct Hor as [Hor | Hor].
subst.
left;simpl.
f_equal.
apply proof_irrelevance.
right.
simpl.
unfold not;intros Hirr.
inversion Hirr.
subst;now contradict Hor.
Qed.
    
Lemma idxPRsucNotEqidxPPR : PRidx < tableSize - 1 -> 
exists succidx1 : index, Index.succ PRidx = Some succidx1 /\ (succidx1 = PPRidx -> False).
Proof. 
unfold Index.succ.
case_eq (lt_dec (PRidx + 1) tableSize); intros.
eexists.
split.
instantiate (1:= CIndex (PRidx + 1)).
f_equal.
unfold CIndex .
case_eq (lt_dec(PRidx + 1) tableSize); intros.
f_equal.
apply proof_irrelevance.
abstract lia.
unfold CIndex.
case_eq(lt_dec (PRidx + 1) tableSize ); intros.

assert(Hi : {| i := PRidx + 1; Hi := ADT.CIndex_obligation_1 (PRidx + 1) l0 |} = PPRidx)
by trivial.
contradict Hi.
subst.
unfold PRidx. unfold PPRidx.
unfold CIndex at 3.
case_eq (lt_dec 10 tableSize); intros.
unfold not; intros Hii.
inversion Hii as (Hi2).
unfold CIndex in Hi2.
case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
simpl in *. 
inversion Hii.
abstract lia.
abstract lia.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
abstract lia.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
abstract lia.
abstract lia.
Qed. 
     Lemma idxPPRsuccNotEqidxPR : PPRidx < tableSize - 1 -> 
    exists succidx2 : index, Index.succ PPRidx = Some succidx2 /\ (succidx2 = PRidx -> False).
    Proof.  
    unfold Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.    
    assert(Hi : {| i := PPRidx + 1; Hi := ADT.CIndex_obligation_1 (PPRidx + 1) l0 |} = PRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed. 
Lemma idxPRidxPPRNotEq : PRidx <> PPRidx.
    Proof.  
      unfold PRidx. unfold PPRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.
      apply tableSizeBigEnough.
      abstract lia. Qed. 

    Lemma idxPPRsuccNotEqidxPD : PPRidx < tableSize - 1 -> 
    exists succidx2 : index, StateLib.Index.succ PPRidx = Some succidx2 /\ (succidx2 = PDidx -> False).
    Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.
    
    assert(Hi : {| i := PPRidx + 1; Hi := ADT.CIndex_obligation_1 (PPRidx + 1) l0 |} = PDidx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    abstract lia.
    Qed.

Lemma idxPPRidxPDNotEq : PPRidx <> PDidx.
    Proof. 
      unfold PPRidx. unfold PDidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia. apply tableSizeBigEnough. abstract lia. Qed. 
    Lemma idxPDsucNotEqidxPPR :  PDidx < tableSize - 1 -> 
    exists succidx1 : index, StateLib.Index.succ PDidx = Some succidx1 /\ (succidx1 = PPRidx -> False).
    Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    
    assert(Hi : {| i := PDidx + 1; Hi := ADT.CIndex_obligation_1 (PDidx + 1) l0 |} = PPRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold PDidx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 2 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed.

 Lemma idxPDidxPPRNotEq : PDidx <> PPRidx.
    Proof. 
      unfold PRidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.
      apply tableSizeBigEnough.
      abstract lia. Qed.

 Lemma idxPPRidxSh1NotEq : PPRidx <> sh1idx.
    Proof. 
      unfold PPRidx. unfold sh1idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia. apply tableSizeBigEnough. abstract lia. Qed.
   
    Lemma idxPPRsuccNotEqidxSh1 : PPRidx < tableSize - 1 -> 
    exists succidx2 : index, StateLib.Index.succ PPRidx = Some succidx2 /\ (succidx2 = sh1idx -> False).
    Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.
    
    assert(Hi : {| i := PPRidx + 1; Hi := ADT.CIndex_obligation_1 (PPRidx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold sh1idx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    abstract lia.
    Qed. 

    Lemma idxSh1succNotEqidxPPR : sh1idx < tableSize - 1 ->
    exists succidx1 : index, StateLib.Index.succ sh1idx = Some succidx1 /\ (succidx1 = PPRidx -> False).
    Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    
    assert(Hi : {| i := sh1idx + 1; Hi := ADT.CIndex_obligation_1 (sh1idx + 1) l0 |} = PPRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 4 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed.

Lemma idxSh1idxPPRnotEq : sh1idx <> PPRidx.
    Proof.  
      unfold sh1idx. unfold PPRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.
      apply tableSizeBigEnough.
      abstract lia. Qed.

    Lemma idxPPRsuccNotEqidxSh2 : PPRidx < tableSize - 1 -> 
    exists succidx2 : index, StateLib.Index.succ PPRidx = Some succidx2 /\ (succidx2 = sh2idx -> False).
    Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.    
    assert(Hi : {| i := PPRidx + 1; Hi := ADT.CIndex_obligation_1 (PPRidx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    abstract lia.
    Qed. 

Lemma idxPPRidxSh2NotEq : PPRidx <> sh2idx. Proof. 
      unfold PPRidx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.
      apply tableSizeBigEnough.
      abstract lia. Qed.
    Lemma idxSh2succNotEqidxPPR : sh2idx < tableSize - 1 -> 
    exists succidx1 : index, StateLib.Index.succ sh2idx = Some succidx1 /\ (succidx1 = PPRidx -> False).
    Proof.  
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.    
    assert(Hi : {| i := sh2idx + 1; Hi := ADT.CIndex_obligation_1 (sh2idx + 1) l0 |} = PPRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed. 

Lemma idxSh2idxPPRnotEq : sh2idx <> PPRidx.
    Proof.  
      unfold sh1idx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.
      apply tableSizeBigEnough.
      abstract lia. Qed.

    Lemma idxPPRsuccNotEqidxSh3 : PPRidx < tableSize - 1 -> 
    exists succidx2 : index, StateLib.Index.succ PPRidx = Some succidx2 /\ (succidx2 = sh3idx -> False).
    Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PPRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PPRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PPRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PPRidx + 1) tableSize ); intros.
    
     assert(Hi : {| i := PPRidx + 1; Hi := ADT.CIndex_obligation_1 (PPRidx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold PPRidx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 10 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    abstract lia.
    Qed. 

    Lemma idxSh3succNotEqPPRidx : sh3idx < tableSize - 1 -> 
    exists succidx1 : index, StateLib.Index.succ sh3idx = Some succidx1 /\ (succidx1 = PPRidx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
     assert(Hi : {| i := sh3idx + 1; Hi := ADT.CIndex_obligation_1 (sh3idx + 1) l0 |} = PPRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold PPRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 10 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed. 

 Lemma idxPPRidxSh3NotEq : PPRidx <> sh3idx.
    Proof.  
      unfold PPRidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.
       apply tableSizeBigEnough. abstract lia. Qed.

    Lemma idxSh3succNotEqPRidx : sh3idx < tableSize - 1 -> 
    exists succidx2 : index, StateLib.Index.succ sh3idx = Some succidx2 /\ (succidx2 = PRidx -> False).
    Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
    
     assert(Hi : {| i := sh3idx + 1; Hi := ADT.CIndex_obligation_1 (sh3idx + 1) l0 |} = PRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed.

    Lemma idxPRsuccNotEqidxSh3 : PRidx < tableSize - 1 -> exists succidx1 : index, StateLib.Index.succ PRidx = Some succidx1 /\ (succidx1 = sh3idx -> False).
    Proof.  
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.
    assert(Hi : {| i := PRidx + 1; Hi := ADT.CIndex_obligation_1 (PRidx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed.

    Lemma  idxPRidxSh3NotEq : PRidx <> sh3idx.
    Proof.  
    (* *)
      unfold PRidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia. apply tableSizeBigEnough. abstract lia. Qed.  

    Lemma idxSh3succNotEqidxPDidx : sh3idx < tableSize - 1 -> 
    exists succidx2 : index, StateLib.Index.succ sh3idx = Some succidx2 /\ (succidx2 = PDidx -> False).
    Proof.  
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
     assert(Hi : {| i := sh3idx + 1; Hi := ADT.CIndex_obligation_1 (sh3idx + 1) l0 |} = PDidx)
    by trivial.
    contradict Hi.
    subst.
    unfold PDidx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    abstract lia.
    Qed.


    Lemma idxPDsucNotEqidxSh3 : PDidx < tableSize - 1 -> 
    exists succidx1 : index, StateLib.Index.succ PDidx = Some succidx1 /\ (succidx1 = sh3idx -> False).
    Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    abstract lia.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    
     assert(Hi : {| i := PDidx + 1; Hi := ADT.CIndex_obligation_1 (PDidx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 2 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    abstract lia.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    abstract lia.
    abstract lia.
    Qed.

    Lemma idxPDidxSh3notEq : PDidx <> sh3idx.
    Proof. 
(*    
 *)      unfold PDidx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      abstract lia. apply tableSizeBigEnough. abstract lia.
      Qed. 

    Lemma idxSh3succNotEqidxSh1 : 
    sh3idx < tableSize - 1 -> 
     exists succidx2 : index, StateLib.Index.succ sh3idx = Some succidx2 /\ (succidx2 = sh1idx -> False).
     Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
    
     assert(Hi : {| i := sh3idx + 1; Hi := ADT.CIndex_obligation_1 (sh3idx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold sh1idx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    lia.
    Qed.
    Lemma sh1idxSh3idxNotEq : sh1idx < tableSize - 1 ->
    exists succidx1 : index, StateLib.Index.succ sh1idx = Some succidx1 /\ (succidx1 = sh3idx -> False).
    Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    
     assert(Hi : {| i := sh1idx + 1; Hi := ADT.CIndex_obligation_1 (sh1idx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold sh3idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 4 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.
    Lemma idxSh1idxSh3notEq :  sh1idx <> sh3idx.
     Proof. 
      unfold sh1idx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia. apply tableSizeBigEnough. lia.
      Qed. 

    Lemma idxSh3succNotEqidxSh2 : sh3idx < tableSize - 1 ->
    exists succidx2 : index, StateLib.Index.succ sh3idx = Some succidx2 /\ (succidx2 = sh2idx -> False).
    Proof.  
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh3idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh3idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh3idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh3idx + 1) tableSize ); intros.
    assert(Hi : {| i := sh3idx + 1; Hi := ADT.CIndex_obligation_1 (sh3idx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 8 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    lia.
    Qed.

    Lemma idxSh2succNotEqidxSh3 : sh2idx < tableSize - 1 ->
    exists succidx1 : index, StateLib.Index.succ sh2idx = Some succidx1 /\ (succidx1 = sh3idx -> False).
    Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
     assert(Hi : {| i := sh2idx + 1; Hi := ADT.CIndex_obligation_1 (sh2idx + 1) l0 |} = sh3idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh3idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 8 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.
 
    Lemma idxSh2idxSh3notEq : sh2idx <> sh3idx .
    Proof.  
      unfold sh2idx. unfold sh3idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia. apply tableSizeBigEnough. lia. 
     Qed.
     
   Lemma  idxSh2succNotEqidxPR : sh2idx < tableSize - 1 -> 
   exists succidx2 : index, StateLib.Index.succ sh2idx = Some succidx2 /\ (succidx2 = PRidx -> False).
   Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
    
     assert(Hi : {| i := sh2idx + 1; Hi := ADT.CIndex_obligation_1 (sh2idx + 1) l0 |} = PRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.   
    
        Lemma idxPRsuccNotEqidxSh2 : PRidx < tableSize - 1 -> 
    exists succidx1 : index, StateLib.Index.succ PRidx = Some succidx1 /\ (succidx1 = sh2idx -> False). 
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.
    
     assert(Hi : {| i := PRidx + 1; Hi := ADT.CIndex_obligation_1 (PRidx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.
        Lemma idxPRidxSh2NotEq : PRidx <> sh2idx.
    Proof.
      unfold PRidx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia. apply tableSizeBigEnough. lia.
      Qed.   

          Lemma idxSh2succNotEqidxPD : sh2idx < tableSize - 1 -> 
     exists succidx2 : index, StateLib.Index.succ sh2idx = Some succidx2 /\ (succidx2 = PDidx -> False).
     Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
    assert(Hi : {| i := sh2idx + 1; Hi := ADT.CIndex_obligation_1 (sh2idx + 1) l0 |} = PDidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.

    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    
    lia.
    Qed.

        Lemma idxPDsucNotEqidxSh2 : 
    PDidx < tableSize - 1 -> 
    exists succidx1 : index, StateLib.Index.succ PDidx = Some succidx1 /\ (succidx1 = sh2idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
   
   
    assert(Hi : {| i := PDidx + 1; Hi := ADT.CIndex_obligation_1 (PDidx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh2idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 2 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed. 

 
    Lemma idxPDidxSh2notEq : PDidx <> sh2idx .
    Proof.  
      unfold PDidx. unfold sh2idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia. apply tableSizeBigEnough. lia. Qed.

          Lemma idxSh2succNotEqidxSh1 : 
    sh2idx < tableSize - 1 -> 
    exists succidx2 : index, StateLib.Index.succ sh2idx = Some succidx2 /\ (succidx2 = sh1idx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh2idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh2idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh2idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh2idx + 1) tableSize ); intros.
      assert(Hi : {| i := sh2idx + 1; Hi := ADT.CIndex_obligation_1 (sh2idx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 6 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    lia.
    Qed.

  
      Lemma idxSh1succNotEqidxSh2 : 
    sh1idx < tableSize - 1 -> 
    exists succidx1 : index, StateLib.Index.succ sh1idx = Some succidx1 /\ (succidx1 = sh2idx -> False).
    Proof.  
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    
     assert(Hi : {| i := sh1idx + 1; Hi := ADT.CIndex_obligation_1 (sh1idx + 1) l0 |} = sh2idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold sh2idx.
    unfold CIndex at 3.
    case_eq (lt_dec 6 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 4 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.	


      
    Lemma idxSh1succNotEqidxPR : 
    sh1idx < tableSize - 1 -> 
    exists succidx2 : index, StateLib.Index.succ sh1idx = Some succidx2 /\ (succidx2 = PRidx -> False).
    Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    assert(Hi : {| i := sh1idx + 1; Hi := ADT.CIndex_obligation_1 (sh1idx + 1) l0 |} = PRidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.
    lia.
    
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.
        Lemma idxPRsuccNotEqidxSh1 :
    PRidx + 1 < tableSize -> 
(*     PRidx + 1< tableSize - 1 ->  *)
    exists succidx1 : index, StateLib.Index.succ PRidx = Some succidx1 /\ (succidx1 = sh1idx -> False).
    Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros.
    assert(Hi : {| i := PRidx + 1; Hi := ADT.CIndex_obligation_1 (PRidx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.
    lia.

    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    lia.
    Qed.
Lemma idxPRidxSh1NotEq : PRidx <> sh1idx.
    Proof. 
      unfold PRidx. unfold sh1idx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia. apply tableSizeBigEnough. lia.
      Qed.
      
          Lemma idxSh1succNotEqidxPD : 
    sh1idx + 1 < tableSize -> 
    exists succidx2 : index, StateLib.Index.succ sh1idx = Some succidx2 /\ (succidx2 = PDidx -> False).
    Proof.  
    unfold StateLib.Index.succ.
    case_eq (lt_dec (sh1idx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (sh1idx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(sh1idx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (sh1idx + 1) tableSize ); intros.
    assert(Hi : {| i := sh1idx + 1; Hi := ADT.CIndex_obligation_1 (sh1idx + 1) l0 |} = PDidx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 4 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.
(*     lia.
    
    
    contradict H13.
    subst.
    unfold PDidx. unfold sh1idx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros.
    unfold not; intros.
    inversion H14.
    unfold CIndex in H16.
    case_eq(lt_dec 4 tableSize); intros; rewrite H15 in *.
    inversion H16. *)
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    lia.
    Qed. 
    
        Lemma  idxPDsucNotEqidxSh1 : 
    PDidx + 1 < tableSize -> 
    exists succidx1 : index, StateLib.Index.succ PDidx = Some succidx1 /\ (succidx1 = sh1idx -> False).
    Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    assert(Hi : {| i := PDidx + 1; Hi := ADT.CIndex_obligation_1 (PDidx + 1) l0 |} = sh1idx)
    by trivial.
    contradict Hi.
    subst.
    unfold sh1idx. unfold PDidx.
    unfold CIndex at 3.
    case_eq (lt_dec 4 tableSize); intros.
    unfold not; intros Hii.
    inversion Hii as (Hi2).
    unfold CIndex in Hi2.
    case_eq(lt_dec 2 tableSize); intros Hi1 Hi3; rewrite Hi3 in *.
    simpl in *. 
    inversion Hii.
    lia.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    Qed.


      
          Lemma idxPDsucNotEqidxPR : 
    PDidx + 1 < tableSize -> 
     exists succidx2 : index, StateLib.Index.succ PDidx = Some succidx2 /\ (succidx2 = PRidx -> False).
     Proof.
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PDidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PDidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PDidx + 1) tableSize); intros.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (PDidx + 1) tableSize ); intros.
    
    assert(Hii : {| i := PDidx + 1; Hi := ADT.CIndex_obligation_1 (PDidx + 1) l0 |} = PRidx)

by trivial.
    contradict Hii.
    subst.
    unfold PDidx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 0 tableSize); intros.
    unfold not; intros Hi.
    inversion Hi.
    assert(Hii : CIndex 2 + 1 = 0) by trivial.
    unfold CIndex in Hii.
    case_eq(lt_dec 0 tableSize); intros Hi1 Hi2;  rewrite Hi2 in *.
    inversion Hi.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    lia.
    lia.
    Qed.
    
        Lemma idxPRsucNotEqidxPD : 
    PRidx + 1 < tableSize -> 
    exists succidx1 : index, Index.succ PRidx = Some succidx1 /\ (succidx1 = PDidx -> False).
    Proof. 
    unfold StateLib.Index.succ.
    case_eq (lt_dec (PRidx + 1) tableSize); intros.
    eexists.
    split.
    instantiate (1:= CIndex (PRidx + 1)).
    f_equal.
    unfold CIndex .
    case_eq (lt_dec(PRidx + 1) tableSize); intros * Hc2.
    f_equal.
    apply proof_irrelevance.
    lia.
    unfold CIndex.
    case_eq(lt_dec (PRidx + 1) tableSize ); intros * Hc3 Hc4.
    contradict Hc4.
    subst.
    unfold PDidx. unfold PRidx.
    unfold CIndex at 3.
    case_eq (lt_dec 2 tableSize); intros * Hc5.
    unfold not; intros Hc6.
    inversion Hc6 as [Hc7].
    unfold CIndex in Hc7.
    case_eq(lt_dec 0 tableSize); intros * Hc8; rewrite Hc8 in *.
    inversion Hc6.
    simpl in *.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    subst.
    lia.
    assert (tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    lia.
    lia.
    
    lia.
    Qed.

        Lemma idxPRidxPDNotEq : PRidx <> PDidx.
    Proof.  
      unfold PDidx. unfold PRidx.
      apply indexEqFalse ;
      assert (tableSize > tableSizeLowerBound).
      apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia.  apply tableSizeBigEnough.
      unfold tableSizeLowerBound in *.
      lia. apply tableSizeBigEnough. lia.
      Qed.

Lemma pageEqNatEqEquiv : forall (a b : page), eq (p a) (p b) <-> (eq a b).
Proof.
split.
intro.
destruct a; destruct b.
simpl in *.
subst.
f_equal. apply proof_irrelevance.

intro.
rewrite H.
reflexivity.
Qed.

Lemma pageNeqNatNeqEquiv : forall (a b : page), (p a) <> (p b) <-> a <> b.
Proof.
intro; split; intro.
destruct a; destruct b.
cbn in *.
injection.
intro.
contradict H1.
assumption.

contradict H.
apply pageEqNatEqEquiv; assumption.
Qed.

Lemma index0Ltfalse (idx:index):
idx < CIndex 0 -> False.
Proof.
intros.
unfold CIndex in H.
case_eq (lt_dec 0 tableSize).
intros.
rewrite H0 in H.
simpl in *. lia.
intros.
contradict H0.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
lia.
Qed.


Lemma indexDecOrNot :
forall p1 p2 : index, p1 = p2 \/ p1<>p2.
Proof.
destruct p1;simpl in *;subst;destruct p2;simpl in *;subst.
assert (Heq :i=i0 \/ i<> i0) by lia.
destruct Heq as [Heq|Heq].
subst.
left;f_equal;apply proof_irrelevance.
right. unfold not;intros.
inversion H.
subst.
now contradict Heq.
Qed.
Lemma getNbLevelEqNat : 
forall nbL, 
Some nbL = StateLib.getNbLevel -> 
nbLevel - 1 = nbL.
Proof.
intros.
unfold StateLib.getNbLevel in *.
destruct (gt_dec nbLevel 0).
inversion H.
destruct nbL.
simpl in *;trivial.
assert (0 < nbLevel) by apply nbLevelNotZero.
lia.
Qed.


Lemma level_eq_l:
forall x1 x2: level, l x1 = l x2 -> x1 = x2.
Proof.
intros. 
destruct x1;destruct x2;simpl in *.
subst.
f_equal.
apply proof_irrelevance.
Qed.

Lemma page_eq_p:
forall x1 x2: page, p x1 =p x2 -> x1 = x2.
Proof.
intros. 
destruct x1;destruct x2;simpl in *.
subst.
f_equal.
apply proof_irrelevance.
Qed.
