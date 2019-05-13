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
DependentTypeLemmas List Bool Invariants.
Require Import Coq.Logic.ProofIrrelevance Omega  Setoid.

(** Consistency : Linked list properties **)
Definition LLconfiguration1 s:=
forall part fstLL LLtable,
In part (getPartitions multiplexer s) -> 
nextEntryIsPP part sh3idx fstLL s ->  
In LLtable (getTrdShadows part s nbPage) -> 
isI LLtable (CIndex 1) s.

Definition LLconfiguration2 s:=
forall part fstLL LLtable maxidx,
In part (getPartitions multiplexer s) -> 
nextEntryIsPP part sh3idx fstLL s ->  
In LLtable (getTrdShadows part s nbPage) -> 
StateLib.getMaxIndex = Some maxidx -> 
isPP LLtable maxidx s.


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

Lemma checkEnoughEntriesLinkedList LLtable (P: state -> Prop) :
{{ fun s => P s }} checkEnoughEntriesLinkedList LLtable {{ fun lasttable s => P s  }}.
Proof.
unfold checkEnoughEntriesLinkedList.
revert LLtable.
assert(Htrue: nbPage <= nbPage) by omega.
revert Htrue.
generalize nbPage  at 1 3.
induction n;simpl;intros.
eapply weaken.
eapply WP.ret.
simpl.
intros;trivial.
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
eapply IHn.
intros.
omega.
intros.
simpl.
intuition.
Admitted.