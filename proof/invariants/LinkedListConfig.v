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

(**  * Summary 
    In this file we formalize and prove all invariants about the linked list configuration *)
Require Import Model.ADT Model.Hardware Core.Services Model.MAL Core.Internal 
Isolation Consistency Model.Lib StateLib  WeakestPreconditions
DependentTypeLemmas List Bool Invariants InternalLemmas.
Require Import Coq.Logic.ProofIrrelevance Omega  Setoid.
(**********************************TO MOVE*********************************)
(** Consistency : Linked list properties **)
Definition LLconfiguration1 s:=
forall part fstLL LLtable,
In part (getPartitions multiplexer s) -> 
nextEntryIsPP part sh3idx fstLL s ->  
In LLtable (getLLPages part s nbPage) -> 
isI LLtable (CIndex 1) s.

Definition LLconfiguration2 s:=
forall part fstLL LLtable maxidx,
In part (getPartitions multiplexer s) -> 
nextEntryIsPP part sh3idx fstLL s ->  
In LLtable (getLLPages part s nbPage) -> 
StateLib.getMaxIndex = Some maxidx -> 
isPP LLtable maxidx s.

(*%%%%%%%%%%%%%%%%%%InternalLemmas%%%%%%%%%%%%%%%%%%%%%%%%%*)

(**************************************************************************)
Lemma getnbFreeEntriesLLInv LLtable P : 
{{ fun s : state => P s /\ isI LLtable (CIndex 1) s}} getnbFreeEntriesLL LLtable 
{{ fun nbfree s =>P s /\ StateLib.readIndex LLtable (CIndex 1) (memory s) = Some nbfree   }}.
Proof.
unfold getnbFreeEntriesLL.
eapply bindRev.
eapply Invariants.Index.zero.
simpl.
intros;trivial.
eapply bindRev.
(** succ **)
eapply weaken.
eapply Invariants.Index.succ.
simpl;intros.
split.
eapply H.
intuition.
subst.
apply CIndex0lt.
intros oneI.
simpl.
(** readIndex **)
eapply strengthen.
eapply weaken.
eapply Invariants.readIndex.
intros.
simpl.
split.
apply H.
intuition.
subst.
assert(oneI=(CIndex 1)).
apply Succ0is1;trivial.
subst;trivial.
simpl.
intros.
split;intuition.
subst.
assert(oneI=(CIndex 1)).
apply Succ0is1;trivial.
subst;trivial.
unfold isIndexValue in *;unfold StateLib.readIndex.
destruct (lookup LLtable (CIndex 1) (memory s) beqPage beqIndex); try now contradict H1.
destruct v ;try now contradict H1.
subst;trivial.
Qed.



Lemma checkEnoughEntriesLinkedListeqstate LLtable  (si:state) n:
{{ fun s => s=si }} checkEnoughEntriesLLAux n LLtable {{ fun lasttable s =>s=si }}.
Proof.
revert LLtable.
induction n;simpl;intros.
eapply weaken.
eapply WP.ret.
simpl.
intros;trivial.
intuition.
eapply bindRev.
(** Index.const3 **)
unfold Index.const3.
eapply weaken.
eapply Invariants.ret.
simpl;intros.
apply H.
simpl.
intros threeI.
(** getnbFreeEntriesLL *)
eapply bindRev.
eapply weaken.
eapply getnbFreeEntriesLLInv.
intros.
simpl.
split. 
eapply H.
admit. (** Consistency not found : LLconfiguration1 *) 
intros nbfree;simpl.
eapply bindRev.
eapply weaken.
eapply Invariants.Index.geb;simpl.
intros.
simpl.
eapply H.
intros gebnbfree.
simpl.
case_eq(gebnbfree);intros;subst.
eapply weaken.
eapply WP.ret.
simpl.
intros;trivial.
intuition.
(** getMaxIndex *)
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getMaxIndex.
intros; simpl.
pattern s in H;eassumption. 
intros maxidx; simpl.
eapply bindRev.
(** readPhysical *)
eapply weaken.
eapply Invariants.readPhysical.
intros.
simpl.
split;trivial.
eapply H.
admit. (** Consistency not found : LLconfiguration2 *) 
simpl.
intros nextLLtable.
eapply bindRev.
(** comparePageToNull **)
eapply weaken.
eapply Invariants.comparePageToNull.
intros.
simpl.
eapply H.
simpl.
intros.
case_eq a;intros;subst.
eapply WP.weaken.  eapply WP.ret . simpl. intros. intuition.
eapply weaken.
eapply strengthen.
eapply IHn.
intros.
simpl in *.
intuition.
intros.
simpl.
intuition.
Admitted.
Lemma checkEnoughEntriesLLAuxStateEq n nextLLtable s s0 p:
checkEnoughEntriesLLAux n nextLLtable s = val (p, s0) -> s=s0.
Proof.
intros.
pose proof checkEnoughEntriesLinkedListeqstate.
unfold hoareTriple in *.
assert(s=s) by trivial.
generalize(H0 nextLLtable s n s H1);intros.
rewrite H in H2.
subst;trivial.
Qed.


Lemma checkEnoughEntriesLinkedList LLtable (P: state -> Prop) :
{{ fun s => P s }} checkEnoughEntriesLinkedList LLtable {{ fun lasttable s => P s /\ ((defaultPage =? lasttable) = false -> In lasttable (getLLPages LLtable s (nbPage + 1))) }}.
Proof.
unfold checkEnoughEntriesLinkedList.
revert LLtable.
assert(Htrue: nbPage <= nbPage) by omega.
revert Htrue.
generalize nbPage  at 1 3 4 .
induction n;simpl;intros.
eapply weaken.
eapply WP.ret.
simpl.
intros;trivial.
split;trivial.
intros  Hfalse.
rewrite Nat.eqb_refl in Hfalse.
intuition.
eapply bindRev.
(** Index.const3 **)
unfold Index.const3.
eapply weaken.
eapply Invariants.ret.
simpl;intros.
apply H.
simpl.
intros threeI.
(** getnbFreeEntriesLL *)
eapply bindRev.
eapply weaken.
eapply getnbFreeEntriesLLInv.
intros.
simpl.
split. 
eapply H.
admit. (** Consistency not found : LLconfiguration1 *) 
intros nbfree;simpl.
eapply bindRev.
eapply weaken.
eapply Invariants.Index.geb;simpl.
intros.
simpl.
eapply H.
intros gebnbfree.
simpl.
case_eq(gebnbfree);intros;subst.
eapply weaken.
eapply WP.ret.
simpl.
intros;trivial.
intuition.
assert(Hmaxidx: exists maxindex, StateLib.getMaxIndex = Some maxindex).
{
unfold StateLib.getMaxIndex.
case_eq(gt_dec tableSize 0);intros;simpl.
eexists.
f_equal.
pose proof tableSizeBigEnough.
omega. }
destruct Hmaxidx as (maxidx & Hmaxidx).
destruct nbPage;simpl;
rewrite Hmaxidx;
destruct ( StateLib.readPhysical LLtable maxidx (memory s));simpl;trivial;try left;trivial;
destruct (p =? defaultPage);simpl;left;trivial.
(** getMaxIndex *)
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getMaxIndex.
intros; simpl.
pattern s in H;eassumption. 
intros maxidx; simpl.
eapply bindRev.
(** readPhysical *)
eapply weaken.
eapply Invariants.readPhysical.
intros.
simpl.
split;trivial.
eapply H.
admit. (** Consistency not found : LLconfiguration2 *) 
simpl.
intros nextLLtable.
eapply bindRev.
(** comparePageToNull **)
eapply weaken.
eapply Invariants.comparePageToNull.
intros.
simpl.
eapply H.
simpl.
intros.
case_eq a;intros;subst.
eapply WP.weaken.
eapply WP.ret ;simpl; intuition.
intuition.
rewrite <-beq_nat_refl in *.
intuition.
unfold hoareTriple in *;intros.
intuition.
assert(Hi:  n <= nbPage) by omega.
generalize(IHn Hi nextLLtable s H);clear IHn; intros IHn.
case_eq(checkEnoughEntriesLLAux n nextLLtable s); [intros x Hx|intros x Hn Hx] ;
rewrite Hx in *;trivial.
destruct x;simpl;intuition.


assert(Hmaxidx: StateLib.getMaxIndex = Some maxidx).
{ 
unfold StateLib.getMaxIndex.
pose proof tableSizeBigEnough.
case_eq(gt_dec tableSize 0);intros;simpl.
f_equal.
subst.
unfold CIndex.
case_eq(lt_dec (tableSize - 1) tableSize);intros;simpl;f_equal.
apply proof_irrelevance.
omega.
omega. }
rewrite Hmaxidx.
subst.
assert(Hread:StateLib.readPhysical LLtable (CIndex (tableSize - 1)) (memory s0)  = Some nextLLtable).
apply readPhysicalIsPP';trivial.
assert(s=s0).
apply checkEnoughEntriesLLAuxStateEq with n nextLLtable p;trivial.
subst;trivial.
rewrite Hread.
rewrite Nat.eqb_sym.
assert(Hnotdef:(defaultPage =? nextLLtable) = false) by trivial.
rewrite Hnotdef.
simpl.
right;trivial.
Admitted.
