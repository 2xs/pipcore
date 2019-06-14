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
Require Import StateLib Model.Hardware Model.ADT DependentTypeLemmas Model.Lib
PropagatedProperties  UpdateMappedPageContent  InternalLemmas WriteIndex InsertEntryIntoLL.
Require Import Coq.Logic.ProofIrrelevance Omega Model.MAL List Bool.
Definition writeIndexInitLLPC phyConfigPagesList (curidx : index) zero maxidx maxidxminus1 eqbZero nullP nullV maxentries oneI twoI s:=

   ((((Nat.Even curidx /\
       (forall idx : index,
        idx > CIndex 1 ->
        idx < CIndex (tableSize - 2) ->
        Nat.Odd idx ->
        idx < curidx ->
        exists idxValue : index,
          StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) /\
       (forall idx : index,
        idx > CIndex 1 ->
        idx < CIndex (tableSize - 2) ->
        Nat.Even idx ->
        idx < curidx ->
        StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) /\
       zero = CIndex 0 /\
       maxidx = CIndex (tableSize - 1) /\
       StateLib.Index.pred maxidx = Some maxidxminus1 /\
       true = StateLib.Index.geb curidx maxidxminus1 /\
       eqbZero = StateLib.Index.eqb curidx zero /\
       nullP = defaultPage /\
       nullV = defaultVAddr /\
       StateLib.readVirtual phyConfigPagesList maxidxminus1 (memory s) = Some nullV) /\
      StateLib.readPhysical phyConfigPagesList maxidx (memory s) = Some nullP) /\
     maxentries = {| i := Init.Nat.div2 tableSize - 2; Hi := MAL.maxFreeLL_obligation_1 |}) /\
    StateLib.Index.succ zero = Some oneI) /\ StateLib.Index.succ oneI = Some twoI . 

Lemma readIndexUpdateLLIndex idx ptVaInCurPart table idxvaInCurPart  s x:
ptVaInCurPart <> table \/ idxvaInCurPart <> idx ->
StateLib.readIndex ptVaInCurPart idxvaInCurPart (memory s) = 
StateLib.readIndex ptVaInCurPart idxvaInCurPart
(memory  {|
currentPartition := currentPartition s;
memory := add table idx (I x)
            (memory s) beqPage beqIndex |}).
Proof.
intros Hentry.
unfold StateLib.readIndex.
cbn.
case_eq (beqPairs (table, idx) (ptVaInCurPart, idxvaInCurPart) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   intuition.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  ptVaInCurPart idxvaInCurPart (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  ptVaInCurPart idxvaInCurPart  (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed. 


Lemma writeIndexNbFI phyConfigPagesList (curidx : index) zero maxidx maxidxminus1 eqbZero nullP nullV maxentries oneI twoI :
{{fun s: state => writeIndexInitLLPC phyConfigPagesList (curidx : index) zero maxidx maxidxminus1 eqbZero nullP nullV maxentries oneI twoI s }} 
writeIndex phyConfigPagesList oneI maxentries {{ fun (_ : unit) (s : state) =>
                                                 initConfigPagesListPostCondition
                                                     phyConfigPagesList s }}.
Proof.
eapply weaken.
eapply WP.writeIndex.
simpl.
intros.
unfold initConfigPagesListPostCondition.
simpl.
assert(Hcons : isI phyConfigPagesList (CIndex 1) s) by admit. (**Consistency not found LLconfiguration1*)
assert(exists entry, 
 lookup phyConfigPagesList (CIndex 1) (memory s) beqPage beqIndex = Some (I entry)) as (entry & Hlookup).
{ intuition.
subst.
 assert(Hi :  isI phyConfigPagesList (CIndex 1) s) ;trivial.
 unfold isI in Hi.
 case_eq(lookup phyConfigPagesList  (CIndex 1) (memory s) beqPage beqIndex);
  [intros v Hv |intros Hv];rewrite Hv in *;try now contradict Hi.
  destruct v;try now contradict Hv.
  subst.
 exists i;trivial. }

unfold writeIndexInitLLPC in *.
  assert(oneI = CIndex 1).
  apply Succ0is1;trivial.
  subst;intuition.
  subst;
  trivial.
  subst.
intuition;subst.
+  assert(StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) =
     Some defaultPage) as Hi by trivial.
  rewrite <- Hi.
  apply readPhysicalUpdateLLIndex with entry;trivial.
+ assert( StateLib.Index.pred (CIndex (tableSize - 1)) = Some maxidxminus1) as Hi by trivial.
apply predMaxIndex in Hi.
subst.
assert(Hi : StateLib.readVirtual phyConfigPagesList (CIndex (tableSize - 2)) (memory s) =
      Some defaultVAddr) by trivial.
      rewrite <- Hi.
      apply readVirtualUpdateLLIndex with entry; trivial.
+ assert(Hi: forall idx : index,
    idx > CIndex 1 ->
    idx < CIndex (tableSize - 2) ->
    Nat.Odd idx ->
    idx < curidx ->
    exists idxValue : index,
      StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) by trivial.
 assert(Hix: exists idxValue : index,
      StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue).
      apply Hi;trivial.
 assert( StateLib.Index.pred (CIndex (tableSize - 1)) = Some maxidxminus1) as Hx by trivial.
apply predMaxIndex in Hx.
subst.
assert(Hii:  StateLib.Index.geb curidx (CIndex (tableSize - 2)) = true) by intuition.
unfold StateLib.Index.geb in Hii.
apply leb_complete in Hii.
omega.
destruct Hix as (idxvalue & Hidxv).
exists idxvalue.
rewrite <- Hidxv.
symmetry.
apply readIndexUpdateLLIndex.
right.
unfold not;intros;subst.
omega.
+ assert(forall idx : index,
     idx > CIndex 1 ->
     idx < CIndex (tableSize - 2) ->
     Nat.Even idx ->
     idx < curidx ->
     StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) as Hi by trivial.
   rewrite <- Hi with idx;trivial.
   apply readVirtualUpdateLLIndex with entry;trivial.
 assert( StateLib.Index.pred (CIndex (tableSize - 1)) = Some maxidxminus1) as Hx by trivial.
apply predMaxIndex in Hx.
subst.
   
assert(Hii:  StateLib.Index.geb curidx (CIndex (tableSize - 2)) = true) by intuition.
unfold StateLib.Index.geb in Hii.
apply leb_complete in Hii.
omega.
Admitted.

Lemma writeIndexFFI  phyConfigPagesList (curidx : index) zero maxidx maxidxminus1 eqbZero nullP nullV maxentries oneI twoI:
{{ fun s : state =>writeIndexInitLLPC phyConfigPagesList (curidx : index) zero maxidx maxidxminus1 eqbZero nullP nullV maxentries oneI twoI s }} 
  writeIndex phyConfigPagesList zero twoI {{ fun _ s => 
  writeIndexInitLLPC phyConfigPagesList (curidx : index) zero maxidx maxidxminus1 eqbZero nullP nullV maxentries oneI twoI s }}.
Proof.
eapply weaken.
eapply WP.writeIndex.
simpl.
intros.
unfold initConfigPagesListPostCondition.
simpl.
assert(Hcons : isI phyConfigPagesList (CIndex 0) s) by admit. (** consistency not found : LLconfiguration3*)
assert(exists entry, 
 lookup phyConfigPagesList (CIndex 0) (memory s) beqPage beqIndex = Some (I entry)) as (entry & Hlookup).
{ intuition.
subst.
 assert(Hi :  isI phyConfigPagesList (CIndex 0) s) ;trivial.
 unfold isI in Hi.
 case_eq(lookup phyConfigPagesList  (CIndex 0) (memory s) beqPage beqIndex);
  [intros v Hv |intros Hv];rewrite Hv in *;try now contradict Hi.
  destruct v;try now contradict Hv.
  subst.
 exists i;trivial. }

unfold writeIndexInitLLPC in *.
  
intuition;subst;simpl in *.
+ assert(Hi: forall idx : index,
    idx > CIndex 1 ->
    idx < CIndex (tableSize - 2) ->
    Nat.Odd idx ->
    idx < curidx ->
    exists idxValue : index,
      StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) by trivial.
 assert(Hix: exists idxValue : index,
      StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue).
      apply Hi;trivial.
 assert( StateLib.Index.pred (CIndex (tableSize - 1)) = Some maxidxminus1) as Hx by trivial.
apply predMaxIndex in Hx.
subst.
assert(Hii:  StateLib.Index.geb curidx (CIndex (tableSize - 2)) = true) by intuition.
unfold StateLib.Index.geb in Hii.
apply leb_complete in Hii.
destruct Hix as (idxvalue & Hidxv).
exists idxvalue.
rewrite <- Hidxv.
symmetry.
apply readIndexUpdateLLIndex.
right.
unfold not;intros;subst.
apply DependentTypeLemmas.index0Ltfalse with (CIndex 1).
omega.
+ assert(forall idx : index,
     idx > CIndex 1 ->
     idx < CIndex (tableSize - 2) ->
     Nat.Even idx ->
     idx < curidx ->
     StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) as Hi by trivial.
   rewrite <- Hi with idx;trivial.
   apply readVirtualUpdateLLIndex with entry;trivial.
+ assert( StateLib.Index.pred (CIndex (tableSize - 1)) = Some maxidxminus1) as Hi by trivial.
apply predMaxIndex in Hi.
subst.
assert(Hi : StateLib.readVirtual phyConfigPagesList (CIndex (tableSize - 2)) (memory s) =
      Some defaultVAddr) by trivial.
      rewrite <- Hi.
      apply readVirtualUpdateLLIndex with entry; trivial.
+  assert(StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) =
     Some defaultPage) as Hi by trivial.
  rewrite <- Hi.
  apply readPhysicalUpdateLLIndex with entry;trivial.
 
Admitted.

Lemma initConfigPagesListNewProperty phyConfigPagesList (curidx : index):
{{ fun s : state => ((* curidx = (CIndex 0) \/ *) (* curidx = (CIndex 1) \/ *) Nat.Even curidx) /\ 
                  (forall idx : index, idx > (CIndex 1) -> idx < CIndex (tableSize -2) -> Nat.Odd idx -> idx < curidx ->
                  exists idxValue, StateLib.readIndex phyConfigPagesList idx s.(memory) = Some idxValue)  /\ 
                 (forall idx : index,  idx > (CIndex 1) -> idx < CIndex (tableSize -2) -> Nat.Even idx -> idx < curidx -> 
                 StateLib.readVirtual phyConfigPagesList idx s.(memory) = Some defaultVAddr)}}
  Internal.initConfigPagesList phyConfigPagesList curidx 
{{ fun _ s  => initConfigPagesListPostCondition phyConfigPagesList s }}.
Proof.
unfold initConfigPagesList.
assert(Hsize : tableSize + curidx >= tableSize) by omega.
revert Hsize.
revert phyConfigPagesList curidx.
generalize tableSize at 1 5. 
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
(** Index.pred *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.Index.pred.
  intros. simpl.
  pattern s in H.
  split.
  eapply H.
  destruct H as (H & Hmax).
  apply tableSizeMinus0;trivial.
  intros maxidxminus1.     
  simpl.
(** MALInternal.Index.geb *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.Index.geb.
  intros. simpl.
  pattern s in H.
  eapply H.
  intros gebmaxidxminus1.     
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
(** the last couple of entries *) 
  case_eq gebmaxidxminus1;intros HlastEntry.
  eapply WP.bindRev.
(** getDefaultPage **)
  eapply WP.weaken.
  eapply Invariants.getDefaultPage.
  intros. simpl.
  pattern s in H.
  eassumption.
  simpl.
  subst.
  intros nullP. simpl. 
  (** getDefaultVaddr **)
  eapply bindRev.
  eapply WP.weaken.
  eapply Invariants.getDefaultVAddr.
  intros. simpl.
  pattern s in H.
  eassumption.
  simpl.
  subst.
  intros nullV. simpl.
  (** writeVirtual **)
  eapply bindRev.
  eapply weaken.
  eapply WP.writeVirtual.
  simpl;intros.
  try repeat rewrite and_assoc in H.
  pattern s in H.
  match type of H with 
  | ?HT s => instantiate (1 := fun tt s => HT s /\ 
             StateLib.readVirtual phyConfigPagesList maxidxminus1 s.(memory) = Some nullV )
  end.
  simpl in *.
  split.
  destruct H as (Hor & Hodd & Heven & Hzero & Hmax & Hnoteqmax 
                & Heqbzero & Hnullv).
  subst.
  split ; trivial.
  split.
  (** Odd: (tableSize - 2) **)
  intros.
  unfold StateLib.readIndex  in *.
  cbn.
  assert(maxidxminus1 = CIndex (tableSize - 2)).
  apply predMaxIndex;trivial.
  subst.
  assert (idx <> CIndex (tableSize - 2)).
  apply indexDiffLtb; left; assumption.
  assert(Hfalse : Lib.beqPairs (phyConfigPagesList, CIndex (tableSize - 2)) (phyConfigPagesList, idx) beqPage beqIndex=
  false).
  { apply beqPairsFalse.
    right; unfold not; intros.
    subst. now contradict H1. }
  rewrite Hfalse.
  assert (Hmemory :   Lib.lookup phyConfigPagesList idx (Lib.removeDup phyConfigPagesList (CIndex (tableSize - 2)) (memory s) beqPage beqIndex) beqPage
  beqIndex =  Lib.lookup phyConfigPagesList idx (memory s) beqPage beqIndex).
  { apply removeDupIdentity; right; trivial. }
  rewrite Hmemory.
  apply Hodd; trivial.
  (** Even: (tableSize-2) **)
  intros.
  split;[|intuition].
  intros.
  cbn.
  assert(maxidxminus1 = CIndex (tableSize - 2)).
  apply predMaxIndex;trivial.
  subst.
  assert(CIndex (tableSize - 2) <> idx). 
  apply indexDiffLtb; right. assumption. 
  assert(Hfalse : Lib.beqPairs (phyConfigPagesList,  (CIndex (tableSize - 2))) (phyConfigPagesList, idx) beqPage beqIndex=
  false).
  { apply beqPairsFalse.
  right;trivial. }
  unfold StateLib.readVirtual in *.
  cbn in *.
  rewrite Hfalse.
  assert (Hmemory :   Lib.lookup phyConfigPagesList idx (Lib.removeDup phyConfigPagesList (CIndex (tableSize - 2)) (memory s) beqPage beqIndex) beqPage
  beqIndex =  Lib.lookup phyConfigPagesList idx (memory s) beqPage beqIndex).
  { apply removeDupIdentity; right; trivial. intuition. }
  rewrite Hmemory.
  apply Heven; trivial. 
  (** writeVirtual postcondition **)
  unfold StateLib.readVirtual .
  cbn.
  assert(Htrue : Lib.beqPairs (phyConfigPagesList, maxidxminus1) (phyConfigPagesList, maxidxminus1) 
       beqPage beqIndex = true).
  apply beqPairsTrue;split;trivial.
  rewrite Htrue;trivial.
  intros [].
  (** writePhysical **) 
  eapply bindRev.
  eapply weaken.
  eapply WP.writePhysical.
  simpl.
  intros.
  repeat rewrite and_assoc in H.
  pattern s in H.
  match type of H with 
  | ?HT s => instantiate (1 := fun tt s => HT s /\ 
             StateLib.readPhysical phyConfigPagesList maxidx s.(memory) = Some nullP )
  end.
  simpl in *.
  split.
  destruct H as (Hor & Hodd & Heven & Hzero & Hmax & Hmaxpred 
                & Hcuridx & Heqbzero & Hi & Hii & Hnullv);subst.
  split ; trivial.
  split.
  (** Odd: (tableSize - 1) **)
  intros.
  assert(idx < CIndex (tableSize - 1)).
  apply TableSizeMinus2;trivial.
  unfold StateLib.readIndex  in *.
  cbn.
  assert (idx <> CIndex (tableSize - 1)).
  apply indexDiffLtb; left; assumption.
  assert(Hfalse : Lib.beqPairs (phyConfigPagesList, CIndex (tableSize - 1)) (phyConfigPagesList, idx) beqPage beqIndex=
  false).
  { apply beqPairsFalse.
  right; unfold not; intros.
  subst. now contradict H1. }
  rewrite Hfalse.
  assert (Hmemory :   Lib.lookup phyConfigPagesList idx (Lib.removeDup phyConfigPagesList (CIndex (tableSize - 1)) (memory s) beqPage beqIndex) beqPage
  beqIndex =  Lib.lookup phyConfigPagesList idx (memory s) beqPage beqIndex).
  { apply removeDupIdentity; right; trivial. }
  rewrite Hmemory.
  apply Hodd; trivial.
  (** Even: (tableSize-1) **)
  intros.
  split;[|intuition].
  intros.
  cbn.
  intros.
  assert(idx < CIndex (tableSize - 1)).
  apply TableSizeMinus2;trivial.
  unfold StateLib.readIndex  in *.
  cbn.
  assert (idx <> CIndex (tableSize - 1)).
  apply indexDiffLtb; left; assumption. 
  assert(Hfalse : Lib.beqPairs (phyConfigPagesList,  (CIndex (tableSize - 1))) (phyConfigPagesList, idx) beqPage beqIndex=
  false).
  { apply beqPairsFalse.
  right;trivial. intuition. }
  unfold StateLib.readVirtual in *.
  cbn in *.
  rewrite Hfalse.
  assert (Hmemory :   Lib.lookup phyConfigPagesList idx (Lib.removeDup phyConfigPagesList (CIndex (tableSize - 1)) (memory s) beqPage beqIndex) beqPage
  beqIndex =  Lib.lookup phyConfigPagesList idx (memory s) beqPage beqIndex).
  { apply removeDupIdentity; right; trivial. }
  rewrite Hmemory.
  apply Heven; trivial.
  (** Propagate readVirtual *)
  assert(maxidxminus1 = CIndex (tableSize - 2)).
  apply predMaxIndex;trivial.
  subst.
  assert (tableSize > tableSizeLowerBound).
  apply tableSizeBigEnough.
  unfold tableSizeLowerBound in *.
  assert(CIndex (tableSize - 1) <> (CIndex (tableSize - 2)) ). 
  apply indexEqFalse;try omega. 
  assert(Hfalse : Lib.beqPairs (phyConfigPagesList,  (CIndex (tableSize - 1))) (phyConfigPagesList, (CIndex (tableSize - 2))) beqPage beqIndex=
  false).
  { apply beqPairsFalse.
  right;trivial. }
  unfold StateLib.readVirtual in *.
  cbn in *.
  rewrite Hfalse.
  assert (Hmemory :   Lib.lookup phyConfigPagesList (CIndex (tableSize - 2))
    (Lib.removeDup phyConfigPagesList (CIndex (tableSize - 1)) (memory s) beqPage beqIndex) beqPage
    beqIndex =  Lib.lookup phyConfigPagesList  (CIndex (tableSize - 2))(memory s) beqPage beqIndex).
  { apply removeDupIdentity; right; trivial. intuition. }
  rewrite Hmemory;trivial.
  (** propagate readPhysical **)
  unfold StateLib.readPhysical.
  cbn; simpl in *.
  subst.
  assert(Htrue : Lib.beqPairs (phyConfigPagesList, maxidx)
   (phyConfigPagesList,  maxidx) beqPage beqIndex= true).
  { apply beqPairsTrue.
    split; trivial. }
  rewrite Htrue; trivial.
  intros [].
  (** maxFreeLL *)
  eapply bindRev.
  eapply weaken.
  unfold maxFreeLL.
  eapply Invariants.ret.
  simpl;intros.
  eapply H.
  intros maxentries.
  (** succ *)
  eapply bindRev.
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
  (** succ *)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.Index.succ.
  simpl;intros.
  split.
  eapply H.
  intuition.
  subst.
  apply CIndex1lt;trivial.
  intros twoI.
  simpl.
  (** writeIndex : First free index **)
  eapply bindRev.
  eapply writeIndexFFI.
  intros [].
  (** writeIndex : Nb free indexes **)
  eapply writeIndexNbFI.
  case_eq eqbZero;intros;subst.
  (** succ *)
  eapply bindRev.
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
  (** succ *)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.Index.succ.
  simpl;intros.
  split.
  eapply H.
  intuition.
  subst.
  apply CIndex1lt;trivial.
  intros twoI.
  simpl.
(** recursion **)
  simpl.
  unfold hoareTriple in *.
  intros.
  apply IHn.
  simpl.
  clear IHn.
  assert(Hcur0: true = StateLib.Index.eqb curidx zero) by intuition.
  assert(Hone: StateLib.Index.succ zero = Some oneI) by  intuition.
  assert(Htwo:StateLib.Index.succ oneI = Some twoI) by intuition.
  assert( zero = CIndex 0) by intuition.
  clear H.
  apply indexEqbTrue in Hcur0;subst.
  assert(n +oneI >= tableSize).
  unfold StateLib.Index.succ in Hone.
  case_eq(lt_dec (CIndex 0 + 1) tableSize);intros;try omega;
  rewrite H in *.
  inversion Hone.
  simpl.
  simpl in *.
  omega.
  now contradict Hone.
  unfold StateLib.Index.succ in Htwo.
  case_eq(lt_dec (oneI + 1) tableSize);intros;try omega;
  rewrite H0 in *;simpl in *.
  inversion Htwo.
  simpl in *.
  omega.
  now contradict Htwo.
  split.
  (** Nat.even two **)
  assert(Hodd: Nat.Odd oneI).
  { intuition;subst.
   apply indexSEqbZeroOdd with (CIndex 0); trivial.
   unfold StateLib.Index.eqb.
   apply beq_nat_refl. }
   apply SuccOddEven with oneI;trivial.
   apply CIndex1lt;intuition.
   subst;trivial.
   intuition.
   split; intros.
   subst.
   admit. (* contradiction *)
   admit. (* contradiction *)

(** Initialize the table between position 2 and (maxindex -2) **)
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
  intros.
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
  apply Hodd; trivial.
  split.
  intros.
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
  apply Heven; trivial.
  intuition.
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
  assert(curidx < tableSize - 1). 
  { repeat rewrite and_assoc in H.
    destruct H as (Hor & Hodd & Heven & Hzero & Hmax & Hmaxpred 
                  & Hgeb & Heqbzero & Hidxsucc & HreadV).
    unfold StateLib.Index.geb in Hgeb.
    symmetry in Hgeb.
    apply leb_complete_conv in Hgeb.
    subst.
    apply predMaxIndex in Hmaxpred.
    subst.
    unfold CIndex in Hgeb.
    case_eq(lt_dec (tableSize - 2) tableSize);intros; rewrite H in *;simpl in *.
    omega.
    assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
    omega. }
  trivial.
  intros Scuridx.
  simpl.
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
  destruct H as (Hor & Hodd & Heven & Hzero & Hmax & Hmaxpred 
          & Hgeb & Heqbzero & Hidxsucc & HreadV & Hscuridx).
  { 
  unfold StateLib.Index.geb in Hgeb.
  symmetry in Hgeb.
  apply leb_complete_conv in Hgeb.
  subst.
  apply predMaxIndex in Hmaxpred.
  subst.
  unfold CIndex in Hgeb.
  case_eq(lt_dec (tableSize - 2) tableSize);intros; rewrite H in *;simpl in *.
  unfold StateLib.Index.succ in *.
  case_eq(lt_dec (curidx + 1) tableSize);intros Hi Hii;rewrite Hii in *;simpl in *;try now contradict Hscuridx.
  inversion Hscuridx;clear Hscuridx.
  simpl in *.
  omega.
  assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
  omega. }
  repeat rewrite and_assoc in H.
  intros SScuridx.
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
                 StateLib.readIndex phyConfigPagesList Scuridx s.(memory) = Some SScuridx )
    end.
   simpl in *.
   split. split.
   destruct H.
   assumption.
      split.
   intros.
   subst.
(*    intuition.
   subst.
   
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
      assumption. } *)
   destruct H as (H & H4).
(*    clear H. *)
      destruct H4 as (Hodd & Heven & Hzero & Hmax & Hmaxminus1 & Hnoteqmax & 
                   Heqbzero & Hnullv & Hreadv & HiIndex & Hnextidx).
subst.
(** odd : StateLib.readIndex**)
   assert (idx <> Scuridx).
   apply indexSuccGt with curidx; trivial.
   unfold StateLib.readIndex in *.
   cbn.
   
   assert (Hfalse :Lib.beqPairs(phyConfigPagesList, Scuridx) (phyConfigPagesList, idx) beqPage beqIndex
   = false).
   { 
   apply beqPairsFalse; right.
   unfold not; intros; subst; now contradict H2. }
   
   
   rewrite Hfalse in *; trivial.
   assert( Hmemory : Lib.lookup phyConfigPagesList idx (Lib.removeDup phyConfigPagesList Scuridx (memory s) beqPage beqIndex)
    beqPage beqIndex = Lib.lookup phyConfigPagesList idx (memory s) beqPage beqIndex).
        { apply removeDupIdentity.
      right. assumption. }
      rewrite Hmemory.
      apply Hodd; trivial.
   split.
 (** even : StateLib.readIndex  **)
 intros.
 unfold  StateLib.readVirtual.
 cbn.
   assert (idx <> Scuridx).
   apply indexSuccGt with curidx; trivial.
   unfold StateLib.readVirtual in *.
   cbn.
   intuition.
   
   assert (Hfalse :Lib.beqPairs(phyConfigPagesList, Scuridx) (phyConfigPagesList, idx) beqPage beqIndex
   = false).
   { 
   apply beqPairsFalse; right.
   unfold not; intros; subst; now contradict H1. }
   
   
   rewrite Hfalse in *; trivial.
   assert( Hmemory : Lib.lookup phyConfigPagesList idx (Lib.removeDup phyConfigPagesList Scuridx (memory s) beqPage beqIndex)
    beqPage beqIndex = Lib.lookup phyConfigPagesList idx (memory s) beqPage beqIndex).
        { apply removeDupIdentity.
      right. assumption. }
      rewrite Hmemory.
 destruct H as (H & (Hodd & Heven & Hzero & Hmax & Hmaxminus1 & Hnoteqmax & 
                   Heqbzero & Hnullv & Hreadv & HiIndex & Hnextidx)).     
      apply Heven; trivial.

  intuition.
  (** result :  StateLib.readVirtual **)
   unfold StateLib.readVirtual in *.
   cbn.
   
   assert (Hfalse :Lib.beqPairs(phyConfigPagesList, Scuridx) (phyConfigPagesList, curidx) beqPage beqIndex
   = false).
   { 
   apply beqPairsFalse; right.

   assert(Hsucc: StateLib.Index.succ curidx = Some Scuridx) by trivial.
   symmetry in Hsucc.
   symmetrynot.
    apply indexSuccEqFalse; trivial.  }
   
   rewrite Hfalse in *; trivial.
   assert( Hmemory : Lib.lookup phyConfigPagesList curidx (Lib.removeDup phyConfigPagesList Scuridx (memory s) beqPage beqIndex)
    beqPage beqIndex = Lib.lookup phyConfigPagesList curidx (memory s) beqPage beqIndex).
        { apply removeDupIdentity.
      right.
      apply indexSuccEqFalse; trivial. }

  rewrite Hmemory.
  trivial.
  unfold StateLib.readIndex.
   cbn.
   assert (Htrue :Lib.beqPairs (phyConfigPagesList, Scuridx) (phyConfigPagesList, Scuridx) beqPage beqIndex
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
   assert (StateLib.Index.succ curidx = Some Scuridx /\ StateLib.Index.succ Scuridx = Some SScuridx) as 
   (Hidxsucc1 & Hidxsucc2) by intuition.
   clear H IHn.
   unfold StateLib.Index.succ in *.
   case_eq (lt_dec (curidx + 1) tableSize) ;intros; rewrite H in *; try now contradict Hidxsucc1.
   case_eq (lt_dec (Scuridx + 1) tableSize) ;intros; rewrite H0 in *; try now contradict Hidxsucc2.
   inversion Hidxsucc1; clear Hidxsucc1.
   inversion Hidxsucc2; clear Hidxsucc2.
   simpl in *.
   destruct SScuridx.
   inversion H3.
   clear H3.
   destruct Scuridx.
   simpl in *; subst.
   inversion H2.
   clear H2.
   destruct curidx.
   simpl in *; subst.
   omega.
   destruct H as ((Hor & Hodd & Heven & Hzero & Hmax & Hnoteqmax & Hgeb & 
             Heqbzero & Hnullv & Hreadv & HiIndex & Hnextidx) & Hreadi).
   subst.
   clear IHn.
   split.
   subst.
  { apply SuccOddEven with Scuridx;trivial.
    * unfold StateLib.Index.geb in Hgeb.
      symmetry in Hgeb.
      apply leb_complete_conv in Hgeb.
      subst.
      apply predMaxIndex in Hnoteqmax.
      subst.
      unfold CIndex in Hgeb.
      case_eq(lt_dec (tableSize - 2) tableSize);intros; rewrite H in *;simpl in *.
      unfold StateLib.Index.succ in *.
      case_eq(lt_dec (curidx + 1) tableSize);intros Hi Hii;rewrite Hii in *;simpl in *;try now contradict Hscuridx.
      inversion HiIndex;clear HiIndex.
      simpl in *.
      omega.
      assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
      omega.
      assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
      omega;trivial.
    * apply SuccEvenOdd with curidx;trivial.
      unfold StateLib.Index.succ in *.
      case_eq (lt_dec (curidx + 1) tableSize) ;intros; rewrite H in *; try now contradict Hidxsucc1.
      inversion HiIndex; clear HiIndex.
      simpl in *.
      omega.
      now contradict HiIndex. }
    split;
    intros.
    subst.
    assert (Horcuridx : idx = Scuridx \/ idx < Scuridx) by admit.
    destruct Horcuridx as [Horc| Horc].
    subst. 
    exists SScuridx;trivial.
    apply Hodd;trivial.
    apply indexSuccSuccOddEvenLt with Scuridx SScuridx;trivial.
    intros.
    
    assert (Horcuridx : idx = curidx \/ idx < curidx) by admit.
    destruct Horcuridx as [Horc| Horc].
    subst;trivial.
    apply Heven;trivial.
Admitted.

Lemma initConfigPagesListPropagateProperties 
(curidx:index) pdChild currentPart currentPD level ptRefChild descChild idxRefChild
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
   (Nat.Even curidx)
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
(** Index.pred *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.Index.pred.
  intros. simpl.
  pattern s in H.
  split.
  eapply H.
  destruct H as (H & Hmax).
  apply tableSizeMinus0;trivial.
  intros maxidxminus1.     
  simpl.
(** MALInternal.Index.geb *)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.Index.geb.
  intros. simpl.
  pattern s in H.
  eapply H.
  intros gebmaxidxminus1.     
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
(** the last couple of entries *) 
  case_eq gebmaxidxminus1;intros HlastEntry.
  eapply WP.bindRev.
(** getDefaultPage **)
  eapply WP.weaken.
  eapply Invariants.getDefaultPage.
  intros. simpl.
  pattern s in H.
  eassumption.
  simpl.
  subst.
  intros nullP. simpl. 
  (** getDefaultVaddr **)
  eapply bindRev.
  eapply WP.weaken.
  eapply Invariants.getDefaultVAddr.
  intros. simpl.
  pattern s in H.
  eassumption.
  simpl.
  subst.
  intros nullV. simpl.
(** writeVirtual **)
  eapply bindRev.
  eapply weaken.
 eapply WP.writeVirtual.
  simpl;intros.
  try repeat rewrite and_assoc in H.
  pattern s in H.
  match type of H with 
  | ?HT s => instantiate (1 := fun tt s => HT s  )
  end.
  simpl in *.
  destruct H.
  split.
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
    split.
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
    intuition.
    subst.
(** writePhysical **)
  eapply bindRev.
  eapply weaken.
 eapply WP.writePhysical.
  simpl;intros.
  try repeat rewrite and_assoc in H.
  pattern s in H.
  match type of H with 
  | ?HT s => instantiate (1 := fun tt s => HT s  )
  end.
  simpl in *.
  destruct H.
  split.
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
    idxConfigPagesList   pdChild list level s; trivial. }
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
    split.
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
    intuition.
    subst.
   (** maxFreeLL *)
  eapply bindRev.
  eapply weaken.
  unfold maxFreeLL.
  eapply Invariants.ret.
  simpl;intros.
  eapply H.
  intros maxentries.
  (** succ *)
  eapply bindRev.
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
  (** succ *)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.Index.succ.
  simpl;intros.
  split.
  eapply H.
  intuition.
  subst.
  apply CIndex1lt;trivial.
  intros twoI.
  simpl.
(** writeIndex **)
  eapply bindRev.
  eapply weaken.
  eapply WP.writeIndex.
  simpl;intros.
  try repeat rewrite and_assoc in H.
  pattern s in H.
  match type of H with 
  | ?HT s => instantiate (1 := fun tt s => HT s  )
  end.
  simpl in *.
  destruct H.
  split.
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
    idxConfigPagesList   shadow2 list level s; trivial. }
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
    idxConfigPagesList   shadow1 list level s; trivial. }
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
    idxConfigPagesList   pdChild list level s; trivial. }
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
    split.
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
    intuition.
    subst.
(** writeIndex **)
  eapply weaken.
  eapply WP.writeIndex.
  simpl;intros.
  try repeat rewrite and_assoc in H.
 repeat rewrite and_assoc.
  
  simpl in *.
  destruct H.
  split.
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
    idxConfigPagesList   shadow2 list level s; trivial. }
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
    idxConfigPagesList   shadow1 list level s; trivial. }
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
    idxConfigPagesList   pdChild list level s; trivial. }
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
    apply readPresentUpdateMappedPageData;trivial.
    subst.
    
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
                  Hnoteqmax & Heqbzero &  Hnoteqmaxx).
   subst.
   apply CIndex0lt.
   intros oneI.
   simpl.
   eapply bindRev.
    (** succ *)
  eapply weaken.
  eapply Invariants.Index.succ.
  simpl;intros.
  split.
  eapply H.
  intuition.
  subst.
  apply CIndex1lt;trivial.
  intros twoI.
  simpl. 
  (** recursion **)
   simpl.
  unfold hoareTriple in *.
  intros.
  apply IHn.
  simpl.
  clear IHn.
  assert(Hcur0: true = StateLib.Index.eqb curidx zero) by intuition.
  assert(Hone: StateLib.Index.succ zero = Some oneI) by  intuition.
  assert(Htwo:StateLib.Index.succ oneI = Some twoI) by intuition.
  assert( zero = CIndex 0) by intuition.
  clear H.
  apply indexEqbTrue in Hcur0;subst.
  assert(n +oneI >= tableSize).
  unfold StateLib.Index.succ in Hone.
  case_eq(lt_dec (CIndex 0 + 1) tableSize);intros;try omega;
  rewrite H in *.
  inversion Hone.
  simpl.
  simpl in *.
  omega.
  now contradict Hone.
  unfold StateLib.Index.succ in Htwo.
  case_eq(lt_dec (oneI + 1) tableSize);intros;try omega;
  rewrite H0 in *;simpl in *.
  inversion Htwo.
  simpl in *.
  omega.
  now contradict Htwo.
  intuition.
assert(Hodd: Nat.Odd oneI).
  { intuition;subst.
   apply indexSEqbZeroOdd with (CIndex 0); trivial.
   unfold StateLib.Index.eqb.
   apply beq_nat_refl. }
   apply SuccOddEven with oneI;trivial.
   apply CIndex1lt;intuition.
   subst;trivial.
}
(** Initialize the table between position 2 and (maxindex -2) **)
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
  | ?HT s => instantiate (1 := fun tt s => HT s  )
  end.
  simpl in *.
  destruct H.
  split.
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
    split.
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
    intuition.
    subst.
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
  assert(curidx < tableSize - 1). 
  { repeat rewrite and_assoc in H.
    destruct H as (_ & _ & _ & _ & _ &_ & _ & _  & _ &Hodd & Heven & Hzero & Hmax & Hmaxpred 
                  & Hgeb & Heqbzero & Hidxsucc ).
    unfold StateLib.Index.geb in Hgeb.
    symmetry in Hgeb.
    apply leb_complete_conv in Hgeb.
    subst.
    apply predMaxIndex in Hmaxpred.
    subst.
    unfold CIndex in Hgeb.
    case_eq(lt_dec (tableSize - 2) tableSize);intros; rewrite H in *;simpl in *.
    omega.
    assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
    omega. }
  trivial.
  intros Scuridx.
  simpl.
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
  destruct H as (_ & _ & _ & _ & _ &_ & _ & _  & _ &Hodd & Heven & Hzero & Hmax & Hmaxpred 
                  & Hgeb & Heqbzero & Hidxsucc & Hxx).
   { 
  unfold StateLib.Index.geb in Hgeb.
  symmetry in Hgeb.
  apply leb_complete_conv in Hgeb.
  subst.
  apply predMaxIndex in Hmaxpred.
  subst.
  unfold CIndex in Hgeb.
  case_eq(lt_dec (tableSize - 2) tableSize);intros; rewrite H in *;simpl in *.
  unfold StateLib.Index.succ in *.
  case_eq(lt_dec (curidx + 1) tableSize);intros Hi Hii;rewrite Hii in *;simpl in *;try now contradict Hscuridx.
  inversion Hxx;clear Hxx.
  simpl in *.
  omega.
  assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
  omega.
  
  assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
  omega. }
  repeat rewrite and_assoc in H.
  intros SScuridx.
   simpl.
(** writeIndex **)
eapply bindRev.
  eapply weaken.
  eapply WP.writeIndex.
  simpl;intros.
  try repeat rewrite and_assoc in H.
  pattern s in H.
  match type of H with 
  | ?HT s => instantiate (1 := fun tt s => HT s  )
  end.
  simpl in *.
  destruct H.
  split.
  simpl in *.
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
    idxConfigPagesList   shadow2 list level s; trivial. }
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
    idxConfigPagesList   shadow1 list level s; trivial. }
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
    idxConfigPagesList   pdChild list level s; trivial. }
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
    subst.
    intuition.
    intros [].
(** Recursion **)
   simpl.
   unfold hoareTriple in *.
   intros.
   apply IHn.
   simpl.
   assert (StateLib.Index.succ curidx = Some Scuridx /\ StateLib.Index.succ Scuridx = Some SScuridx) as 
   (Hidxsucc1 & Hidxsucc2) by intuition.
   clear H IHn.
   unfold StateLib.Index.succ in *.
   case_eq (lt_dec (curidx + 1) tableSize) ;intros; rewrite H in *; try now contradict Hidxsucc1.
   case_eq (lt_dec (Scuridx + 1) tableSize) ;intros; rewrite H0 in *; try now contradict Hidxsucc2.
   inversion Hidxsucc1; clear Hidxsucc1.
   inversion Hidxsucc2; clear Hidxsucc2.
   simpl in *.
   destruct SScuridx.
   inversion H3.
   clear H3.
   destruct Scuridx.
   simpl in *; subst.
   inversion H2.
   clear H2.
   destruct curidx.
   simpl in *; subst.
   omega.
   split.
   intuition.
   destruct H as (_ & _ & _ & _ & _ &  _ & _ & _ & _ & Hodd & Heven & Hzero & Hmax & Hnoteqmax & Hgeb & 
             Heqbzero & Hnullv & Hreadv & HiIndex ).
   split.
   intuition.
   subst.
   clear IHn.
   subst.
   apply SuccOddEven with Scuridx;trivial.
    * unfold StateLib.Index.geb in Hgeb.
      symmetry in Hgeb.
      apply leb_complete_conv in Hgeb.
      subst.
      apply predMaxIndex in Hnoteqmax.
      subst.
      unfold CIndex in Hgeb.
      case_eq(lt_dec (tableSize - 2) tableSize);intros; rewrite H in *;simpl in *.
      unfold StateLib.Index.succ in *.
      case_eq(lt_dec (curidx + 1) tableSize);intros Hi Hii;rewrite Hii in *;simpl in *;try now contradict Hscuridx.
      inversion HiIndex;clear HiIndex.
      case_eq(lt_dec (Scuridx + 1) tableSize);intros;rewrite H0 in *.
      inversion H1.
      subst.
      omega.
      
      simpl in *.
      now contradict H1.
      now contradict Hreadv.
      assert (tableSizeLowerBound < tableSize) by apply tableSizeBigEnough.
      omega.
    * apply SuccEvenOdd with curidx;trivial.
      unfold StateLib.Index.succ in *.
      case_eq (lt_dec (curidx + 1) tableSize) ;intros; rewrite H in *; try now contradict Hidxsucc1.
      inversion HiIndex; clear HiIndex.
      simpl in *.
      omega.
      now contradict HiIndex.
Qed.
