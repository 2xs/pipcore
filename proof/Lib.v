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
      This file contains some generic lemmas used by invariants **)
Require Import List Coq.Logic.Classical_Prop Model.Lib.
Import List.ListNotations Lia.

Lemma NoDupSplit (A: Type) :
forall l l': list A , 
NoDup (l++l') -> NoDup l /\ NoDup l'.
Proof. 
intros.
split. 
 + induction l'. 
   rewrite app_nil_r in H.
   assumption.
   apply IHl'.
   apply NoDup_remove_1 in H.
   assumption.
 + induction l'. 
   apply NoDup_nil.
   assert (NoDup (l ++ a :: l')). assumption.
   apply NoDup_remove_2 in H.
   constructor 2.
   unfold not in *. intro. apply H.
   apply in_or_app.
   right. assumption.
   apply IHl'.
   apply NoDup_remove_1 in H0.
   assumption.
Qed.

Definition disjoint {A : Type} (l1 l2 : list A) : Prop := 
forall x : A,  In x l1  -> ~ In x l2 . 

Lemma NoDupSplitInclIff (A: Type) :
forall l l': list A , 
NoDup (l++l') <-> (NoDup l /\ NoDup l') /\ disjoint l l'.
Proof. 
intros.
split.   
 + intros. split.
   -  apply NoDupSplit; trivial.
   - unfold disjoint. intros.
     revert x l H H0. 
     induction l'; intros.
     unfold not. intros. now contradict H1.
     simpl.
     apply and_not_or. 
     split.
     unfold not. intros. subst.
     unfold not in *.
     apply NoDup_remove in H.
     destruct H.
     contradict H1.
     apply in_or_app.
     left; trivial.
     apply NoDup_remove in H.
     destruct H.
     apply IHl' with l; trivial.
 + intros.
   revert l' H.
   induction l.
   - intros; simpl in *.
     intuition.
   - simpl.
     intros.
     constructor.
     intuition.
     apply in_app_iff in H0.
     destruct H0.
     apply NoDup_cons_iff in H.
     destruct H.
     now contradict H0.
     unfold disjoint in *.
     apply NoDup_cons_iff in H.
     
     destruct H.
     contradict H0.
     apply H2.
     simpl;left;trivial.
     apply IHl.
     intuition.
     apply NoDup_cons_iff in H; destruct H; trivial.
     unfold disjoint in *.
     intros.
     apply H1.
     simpl; right; trivial.          
Qed.
Lemma inclDisjoint (A : Type) (l l' l1 l2 : list A): 
disjoint l l'  -> incl l1 l -> incl l2 l' -> disjoint l1 l2.
Proof. 
intros.
unfold disjoint in *.
intros.
unfold incl in *.
unfold not.
intros.
apply H1 in H3.
contradict H3.
apply H.
apply H0; trivial.
Qed.

Lemma removeNotIn (A :Type) (eq_dec : forall x y : A, {x = y} + {x <> y}):
forall l a, ~ In a l -> remove eq_dec a l =l.
Proof.
induction l; intros; simpl;trivial.
apply Classical_Prop.not_or_and in H.
destruct H.
case_eq (eq_dec a0 a);intros.
subst.
now contradict H.
f_equal.
apply IHl;trivial.  
Qed.

Lemma removeIncl (A :Type) (eq_dec : forall x y : A, {x = y} + {x <> y}):
forall l a, incl (remove eq_dec a l) l.
Proof.
induction l;simpl;intros;trivial.
unfold incl.
intros.
trivial.
case_eq (eq_dec a0 a);intros.
subst.
assert(~ In a ((remove eq_dec a l) )).
apply remove_In.
unfold incl.
intros.
simpl .
right.
unfold incl in IHl.
apply IHl with a;trivial.
unfold incl.
intros.
simpl.
unfold incl in *.
assert(a = a1 \/ a <> a1).
{ destruct eq_dec with a a1.
  left;trivial.
  right;trivial. } 
destruct H1.
left;trivial.
right.
apply IHl with a0.
simpl in H0.
destruct H0.
subst.
assert(a1 = a1).
auto.
contradiction.
trivial.
Qed.

Lemma removeNoDup 
(A :Type) (eq_dec : forall x y : A, {x = y} + {x <> y}):
forall l a,NoDup l ->  NoDup (remove eq_dec a l).
Proof.
induction l;simpl;intros.
+ constructor.
+ apply NoDup_cons_iff  in H.
  destruct H. 
  case_eq (eq_dec a0 a);intros.
  subst.
  apply IHl;trivial.
  constructor.
  assert(incl (remove eq_dec a0 l) l).
  { apply removeIncl. }
  unfold incl in H2.
  unfold not;intros.
  contradict H.
  apply H2;trivial.
  apply IHl;trivial.
Qed.

Lemma removeLength (A :Type) (eq_dec : forall x y : A, {x = y} + {x <> y}):
forall l a, NoDup l -> In a l -> S (length (remove eq_dec a l)) = length l.
Proof.
induction l;simpl;intros.
+ contradiction.
+ f_equal.
  destruct H0.
  subst. 
  destruct (eq_dec a0 a0);intros.
  assert(~ In a0 l).
   apply NoDup_cons_iff  in H.
  destruct H;trivial.
  f_equal.
  apply removeNotIn;trivial.
  auto.
  assert(a0 = a0).
  auto.
  contradiction.
  case_eq (eq_dec a0 a);intros.
  subst.
  apply NoDup_cons_iff  in H.
  destruct H;trivial.
  contradiction.
  simpl.
  apply NoDup_cons_iff  in H.
  destruct H;trivial.
  apply IHl;trivial.
Qed.

Lemma removeCons (A :Type) (eq_dec : forall x y : A, {x = y} + {x <> y}):
forall l a b, a <> b -> remove eq_dec a (b ::l) = b :: (remove eq_dec a l) .
Proof.
induction l;simpl;intros.
+ case_eq (eq_dec a b);intros.
  contradiction.
  trivial.
+ case_eq (eq_dec  a0 b);intros.
  contradiction.
  f_equal.
Qed.

Lemma removeConsEq (A :Type) (eq_dec : forall x y : A, {x = y} + {x <> y}):
forall l a , remove eq_dec a (a ::l) =remove eq_dec a l .
Proof.
induction l;simpl;intros.
+ case_eq (eq_dec a a);intros;trivial.
assert(a=a) by auto.
  contradiction.
+ case_eq (eq_dec  a0 a0);intros;trivial.
  assert(a0=a0) by auto.
  contradiction.
Qed.

Lemma removeStillIn (A :Type) (eq_dec : forall x y : A, {x = y} + {x <> y}):
forall a b : A, forall l' l: list A ,
a <> b -> remove eq_dec a l' = l  -> In b l' -> In b l.
Proof.
induction l';simpl;trivial.
intros.
now contradict H1.
intros.
destruct H1.
subst.
case_eq(eq_dec a b);intros.
contradiction.
simpl;left;trivial.
case_eq(eq_dec a a0 );intros.
subst.
rewrite H2.
apply IHl';trivial.
rewrite H2 in H0.
subst.
simpl.
right.
apply IHl';trivial.
Qed.

Lemma  removeStillInIncl (A :Type) (eq_dec : forall x y : A, {x = y} + {x <> y}):
forall v a : A , forall l l1 l' : list A, v <> a -> remove eq_dec a l' = l -> 
incl l1 l' -> In v l1 -> In v l.
Proof.
intros.
apply removeStillIn with eq_dec a l';trivial.
intuition.
unfold incl in H1.
apply H1;trivial.
Qed.

Lemma addLengthIn (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) :
forall l' l, forall x b : A,
length l' = S (length l)  -> 
incl l l' -> 
x <> b -> 
In x l' -> 
~ In x l -> 
In b l' ->
NoDup l -> 
NoDup l' -> 
In b l.
Proof.
induction l';simpl;intros.
+ lia.
+ destruct H2;subst;destruct H4;subst.
  - now contradict H1.
  - destruct l. simpl in *.
    * assert(length l' = 0).
      lia.
      apply length_zero_iff_nil in H4.
      subst.
      now contradict H2.
    * assert( incl (a :: l) l').
      { apply incl_cons.
        unfold incl in H0.
        simpl in *.
        apply Classical_Prop.not_or_and in H3.
        destruct H3.
        assert(x = a \/ In a l').
        apply H0;clear H0.
        left;trivial. 
        destruct H7.
        subst.
        now contradict H3.
        trivial.
        simpl in H3.
        apply Classical_Prop.not_or_and in H3.
        destruct H3.
        unfold incl in H0.
        simpl in *.
        unfold incl.
        intros.
        assert(a0 <> x).
        unfold not;intros.
        subst.
        now contradict H4.  
        assert(x = a0 \/ In a0 l').
        apply H0;trivial.
        right;trivial.
        destruct H9;subst.
        now contradict H7.
        trivial. }
      subst.  
      simpl.
      assert(a=b \/ a <> b).
      { destruct eq_dec with a b.
        left;trivial.
        right;trivial. } 
      destruct H7.
      left;trivial. 
      right.
      simpl in *.
      inversion H. 
      apply Classical_Prop.not_or_and in H3.
      destruct H3.
      assert (incl l l').
      { unfold incl in H4.
        unfold incl.
        intros.
        apply H4.
        simpl.
        right;trivial. }
      apply IHl' with a;trivial.
      unfold incl in H4.
      apply H4;simpl;left;trivial.
      apply NoDup_cons_iff  in H5.
      destruct H5;trivial.
      apply NoDup_cons_iff  in H5.
      destruct H5;trivial.
      apply NoDup_cons_iff  in H6.
      destruct H6;trivial.
  - inversion H.
    assert(In b l \/ ~ In b l).
    { clear H5 H3 H7 H H0.
      induction l.
      right.
      auto.
      simpl.
      assert(a=b \/ a <> b).
      { destruct eq_dec with a b.
        left;trivial.
        right;trivial. }
      destruct H.
      subst.
      do 2 left;trivial.
      destruct IHl.
      left;right;trivial.
      right.
      intuition. }
    destruct H4 ;trivial.
    contradict H3.
    assert(incl l l').  
    unfold incl in H0.
    unfold incl.
    intros.
    simpl in *.
    assert( b = a \/ In a l').
    { apply H0; trivial. }
    destruct H8.
    subst.
    now contradict H4.
    trivial.
    apply Classical_Prop.NNPP.
    unfold not at 1.
    intros.
    contradict H4.
    clear H0.
    destruct l.
    { simpl in *.
      assert(length l' = 0).
      lia.
      apply length_zero_iff_nil in H0.
      subst.
      now contradict H2. }
    assert( incl ( a :: l) l').
    { apply incl_cons.
      unfold incl in H3.
      simpl in *.
      apply Classical_Prop.not_or_and in H8.
      destruct H8.
      apply H3.
      left;trivial.
      unfold incl.
      intros.
      unfold incl in H3.
      apply H3.
      simpl;right;trivial. }
    subst.  
    simpl.
    assert(a=b \/ a <> b).
    { destruct eq_dec with a b.
      left;trivial.
      right;trivial. }
    destruct H4.
    left;trivial. 
    right.
    simpl in *.
    inversion H.
    apply Classical_Prop.not_or_and in H8.
    destruct H8.
    assert (incl l l').
    { unfold incl in H0.
      unfold incl.
      intros.
      apply H0.
      simpl.
      right;trivial. }
    assert(  ~ In x l) by trivial.
    apply Classical_Prop.NNPP.
    unfold not at 1;intros.
    contradict H9.
    apply IHl' with a;trivial.
    unfold incl in H0.
    apply H0;simpl;left;trivial.
    apply NoDup_cons_iff  in H5.
    destruct H5;trivial.  
    apply NoDup_cons_iff  in H5.
    destruct H5;trivial. 
    apply NoDup_cons_iff  in H6.
    destruct H6;trivial.
  - inversion H.
    simpl in *.
    subst.
    assert(In a l \/ ~ In a l).
    { clear H5 H3 H0 H H8.
      induction l.
      right.
      auto.
      simpl.
      assert(a0=a \/ a0 <> a).
      { destruct eq_dec with a0 a.
        left;trivial.
        right;trivial. }
      destruct H.
      subst.
      do 2 left;trivial.
      destruct IHl.
      left;right;trivial.
      right.
      intuition. }
    destruct H7.
    * assert(exists li, li = remove eq_dec a l).
      eexists.
      reflexivity.
      destruct H9 as (newL &HnewL).
      assert (a <> b).
      apply NoDup_cons_iff  in H6.
      destruct H6;trivial.
      unfold not;intros.
      subst.
      now contradict H6.
      assert(In b  newL).
      apply IHl' with x;trivial.
      subst.
      inversion H.
      rewrite H11.
      symmetry.
      apply removeLength;trivial.
      subst.
      assert (~ In a (remove eq_dec a l) ).
      apply remove_In.
      assert(incl (remove eq_dec a l) l).
      { apply removeIncl. }
      unfold incl.
      intros.
      unfold incl in *.
      simpl in *. 
      assert( a = a0 \/ In a0 l').
      apply H0.
      apply H11;trivial.
      destruct H13.
      subst.
      contradict H12.
      apply remove_In.
      trivial.
      subst.      
      assert(incl (remove eq_dec a l) l).
      { apply removeIncl. }
      unfold incl in H10.
      unfold not; intros.
      apply H10 in H11.
      contradiction.
      assert(incl (remove eq_dec a l) l).
      { apply removeIncl. }
      subst.
      apply removeNoDup;trivial.
      apply NoDup_cons_iff  in H6.
      destruct H6;trivial.
      assert(incl (remove eq_dec a l) l).
      { apply removeIncl. }
      subst.
      unfold incl in H11.
      apply H11;trivial.  
    * destruct l.
      simpl in *. 
      assert(length l' = 0).
      lia.
      apply length_zero_iff_nil in H9.
      subst.
      now contradict H2.
      simpl in *.
      apply Classical_Prop.not_or_and in H3.
      destruct H3.
      apply Classical_Prop.not_or_and in H7.
      destruct H7.
      right.
      assert(incl l l').
      unfold incl.
      intros.
      unfold incl in H0.
      simpl in *.
      assert(a = a1 \/ In a1 l').
      apply H0.
      right.
      trivial.
      destruct H12.
      subst.
      now contradict H10.
      trivial.
      apply IHl' with x;trivial.
      apply NoDup_cons_iff  in H5.
      destruct H5;trivial.
      apply NoDup_cons_iff  in H6.
      destruct H6;trivial.
Qed.

Lemma flat_map_app_cons (A : Type) (f : A ->  list A ):
forall l1 p l2 ,
flat_map f (l1 ++ p :: l2) =
flat_map f l1 ++
flat_map f [p] ++
flat_map f l2.
Proof.
intros.
do 4 rewrite flat_map_concat_map.
rewrite <- concat_app.
rewrite <- concat_app.
f_equal.
rewrite map_app.
f_equal.
Qed.

Lemma flat_map_app (A : Type) (f : A ->  list A ):
forall l1 l2 ,
flat_map f (l1 ++ l2) =
flat_map f l1 ++
flat_map f l2.
Proof.
intros.
do 3 rewrite flat_map_concat_map.
rewrite map_app.
rewrite concat_app.
f_equal.
Qed.

Lemma disjointPermut(A : Type) :
forall l1 l2 : list A, 
disjoint l1 l2 -> disjoint l2 l1.
Proof.
unfold disjoint.
induction l1.
simpl.
intros.
auto.
intros.
simpl.
simpl in  H.
apply Classical_Prop.and_not_or.
split.
assert(~ In  a l2).
apply H.
left;trivial.
unfold not;intros.
subst.
now contradict H1.
apply IHl1 with l2;trivial.
intros.
apply H.
right;trivial.
Qed.

 Lemma length_diff (A : Type): 
 forall (l1 l2 :list A), length l1 <> length l2 -> l1 <> l2.
 Proof.
 induction l1; simpl.
 intros.
 contradict H.
 symmetry.
 apply length_zero_iff_nil.
 rewrite H. trivial.
 intros.
 unfold not;intros.
 rewrite <- H0 in H.
 simpl in *.
 lia.
 Qed.
 
Lemma app_cons_not (A : Type) :
forall (l1 : list A) l2 a, l1 ++ a :: l2 <> l1 ++ l2.
Proof.
 intros. unfold not;intros.
 assert(l1 ++ [a] ++ l2 = l1 ++ l2).
 simpl. trivial.
 clear H. 
 assert(length ( l1 ++ [a] ++ l2) =1+ length (l1 ++ l2)).
 do 3 rewrite app_length.
 simpl.
 lia.
 contradict H0.
 apply length_diff.
 lia.
Qed. 
