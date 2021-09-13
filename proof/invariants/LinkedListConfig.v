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

(**  * Summary 
    In this file we formalize and prove all invariants about the linked list configuration *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Services Pip.Core.Internal.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.InternalLemmas
               Pip.Proof.Isolation Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Invariants.
Require Import Bool List Coq.Logic.ProofIrrelevance Lia Setoid Compare_dec EqNat.
(**********************************TO MOVE*********************************)

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

Definition checkEnoughEntriesLinkedListPC s (lasttable LLtable: page):=
((Nat.eqb defaultPage lasttable) = false -> (In lasttable (getLLPages LLtable s (nbPage + 1)) /\ (exists NbFI, isIndexValue lasttable (CIndex 1) NbFI s /\ NbFI >= (CIndex 3)))).
Lemma checkEnoughEntriesLinkedList LLtable (P: state -> Prop) :
{{ fun s => P s }} checkEnoughEntriesLinkedList LLtable {{ fun lasttable s => P s /\ checkEnoughEntriesLinkedListPC s lasttable LLtable  }}.
Proof.
unfold checkEnoughEntriesLinkedList, checkEnoughEntriesLinkedListPC.
revert LLtable.
assert(Htrue: nbPage <= nbPage) by lia.
revert Htrue.
generalize nbPage  at 1 3 4 .
induction n;simpl;intros.
eapply weaken.
eapply WP.ret.
simpl.
intros;trivial.
split;trivial.
intros  Hfalse.
rewrite PeanoNat.Nat.eqb_refl in Hfalse.
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
lia. }
destruct Hmaxidx as (maxidx & Hmaxidx).
destruct nbPage;simpl;
rewrite Hmaxidx;
destruct ( StateLib.readPhysical LLtable maxidx (memory s));simpl;trivial;try left;trivial;
destruct (Nat.eqb p defaultPage);simpl;left;trivial.
subst.
assert(Hcons: isI LLtable (CIndex 1) s) by admit. (** Consistency not found : LLconfiguration1 *) 
unfold isI, isIndexValue in *.
case_eq(lookup LLtable (CIndex 1) (memory s) beqPage beqIndex );[intros v Hv| intros Hv];rewrite Hv in *;try now contradict Hcons.
destruct v;try now contradict Hcons.
exists i.
split;trivial.
assert(Hidx: StateLib.readIndex LLtable (CIndex 1) (memory s) = Some nbfree) by trivial.
unfold StateLib.readIndex in Hidx.
rewrite Hv in *.
inversion Hidx.
subst.
unfold StateLib.Index.geb in *.
apply  Coq.Logic.Classical_Prop.NNPP.
unfold not at 1.
intros.
contradict H1.
symmetrynot.
apply not_true_iff_false.
apply NPeano.Nat.leb_nle.
unfold Constants.idx3.
lia.
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
rewrite <-beq_nat_refl in *.
intuition.
unfold hoareTriple in *;intros.
intuition.
assert(Hi:  n <= nbPage) by lia.
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
lia.
lia. }
rewrite Hmaxidx.
subst.
assert(Hread:StateLib.readPhysical LLtable (CIndex (tableSize - 1)) (memory s0)  = Some nextLLtable).
apply readPhysicalIsPP';trivial.
assert(s=s0).
apply checkEnoughEntriesLLAuxStateEq with n nextLLtable p;trivial.
subst;trivial.
rewrite Hread.
rewrite PeanoNat.Nat.eqb_sym.
assert(Hnotdef:(Nat.eqb defaultPage nextLLtable) = false) by trivial.
rewrite Hnotdef.
simpl.
right;trivial.
Admitted.
