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
    This file contains the invariant of [writePhyEntry]. 
    We prove that this instruction preserves the isolation property  *)
Require Import  Model.ADT Model.Hardware Core.Services Isolation
Consistency Invariants WeakestPreconditions Model.Lib StateLib
Model.MAL Lib InternalLemmas DependentTypeLemmas GetTableAddr PropagatedProperties WriteAccessible MapMMUPage.
 Require Import Omega Bool  Coq.Logic.ProofIrrelevance List.
Lemma getMappedPageAddIndirection s indirection nextIndirection idxToPrepare entry nbLgen vavalue pd partition:
lookup indirection idxToPrepare (memory s) beqPage beqIndex = Some (PE entry) -> 
Some nbLgen = StateLib.getNbLevel ->
nextEntryIsPP partition PDidx pd s -> 
getMappedPage pd s vavalue = getMappedPage pd  {|
  currentPartition := currentPartition s;
  memory := add indirection idxToPrepare
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |} vavalue.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hlookup Hl Hpd.
unfold getMappedPage.
rewrite  <-Hl.
case_eq(getIndirection pd vavalue nbLgen (nbLevel - 1) s );[intros tbl Htbl |intros Htbl]. 
- case_eq( getIndirection pd vavalue nbLgen (nbLevel - 1) s'); [intros tbl' Htbl' |intros Htbl'].
  +  admit.
  + admit. (* contradiction *)
- assert(Hnone: getIndirection pd vavalue nbLgen (nbLevel - 1) s' = None) by admit.
  rewrite Hnone;trivial.
Admitted.

Lemma getMappedPagesAuxAddIndirection s indirection nextIndirection  entry nbLgen valist pd pg indMMUToPrepare vaToPrepare partition l:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) -> 
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
In pg (getMappedPagesAux pd valist s)  -> In pg  (getMappedPagesAux pd valist {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}).
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hlookup Hl Hroot Hdef Hdef' Hinit Hlevel. 
unfold getMappedPagesAux.
intros Hgoal.
rewrite filterOptionInIff in *.
unfold getMappedPagesOption in *.
rewrite in_map_iff in *.
destruct Hgoal as (vapg & Hvapg & Hinvalist).
exists vapg;split;trivial.
unfold indirectionDescription,  initPEntryTablePreconditionToPropagatePrepareProperties in *.
destruct Hroot as (tableroot & Hpp & Hrootnotdef & Hor).
assert(Hpdor: tableroot = pd \/ tableroot <> pd) by apply pageDecOrNot.
destruct Hpdor as [Hpdor| Hpdor];subst.
+ (** same partition **)
destruct Hor as [(Heq & HnbL) | Hor].
- (** root **) subst.
  assert(Hnoneind:getIndirection indirection vaToPrepare l (nbLevel - 1) s = Some defaultPage).
  { apply getIndirectionNbLevelEq with 1;try omega.
    rewrite  getNbLevelEq with l;trivial.
    apply nbLevelEq.
    symmetry in Hlevel.
    apply levelEqBEqNatFalse0 in Hlevel.
    omega.
    simpl.
    rewrite <- Hlevel.
    assert(Hread: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some indMMUToPrepare).
    apply isEntryPageReadPhyEntry1;trivial.
    rewrite Hread.
    rewrite Hdef';trivial. }
  assert(Hnone: getMappedPage indirection s vaToPrepare = NonePage).
  { unfold getMappedPage.
    rewrite <- HnbL.
    rewrite Hnoneind.
    assert(Heq: true=(defaultPage =? defaultPage)).
    apply beq_nat_refl.
    rewrite <- Heq.
    trivial. }
    (* assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaInCurrentPartition va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1.
split;trivial.
rewrite <- H.*)
  assert(Hor :checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = true \/ 
         checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = false).
  { destruct (checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l);intuition. }
  destruct Hor as [Hor | Hor].
  * (** Same virtual address : contradiction **)
    assert(Hfalse: getMappedPage indirection s vapg = NonePage).
    rewrite <- Hnone.
    symmetry.
    apply getMappedPageEq with l;trivial.
    symmetry;trivial.
    rewrite Hfalse in Hvapg.
    now contradict Hvapg. 
  * (* rewrite <- Hvapg.
    symmetry. *)
    unfold getMappedPage.
    unfold getMappedPage in Hvapg.
rewrite <- HnbL in *.
    case_eq(getIndirection indirection vapg l (nbLevel - 1) s)
    ;[intros ind Hind | intros Hind];rewrite Hind in *;try now contradict Hvapg.
    case_eq(defaultPage =? ind) ;intros Hi;rewrite Hi in *;try now contradict Hvapg.
    case_eq(getIndirection indirection vapg l (nbLevel - 1) s');[intros ind' Hind'|intros Hind'].

  
(*   Lemma twoMappedPagesAreDifferent phy1 phy2 v1 v2 p nbL s: 
getMappedPage p s v1 = SomePage phy1 ->
getMappedPage p s v2 = SomePage phy2-> 
NoDup (filterOption (map (getMappedPage p s) getAllVAddrWithOffset0)) -> 
StateLib.getNbLevel = Some nbL -> 
StateLib.checkVAddrsEqualityWOOffset nbLevel v1 v2 nbL = false -> 
phy1 <> phy2.
Proof.
intros.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel v1 va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).
assert(Hmap1: getMappedPage p s va1 = SomePage phy1). 
rewrite <- H.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.
clear H.

assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel v2 va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va2 & Hva2 & Hva22).
assert(Hmap2: getMappedPage p s va2 = SomePage phy2). 
rewrite <- H0.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.
clear H0.
assert(Hx :StateLib.checkVAddrsEqualityWOOffset nbLevel  va2 v1 nbL = false).
apply checkVAddrsEqualityWOOffsetTrans with v2;trivial.
rewrite <- Hva22.
assert(StateLib.getNbLevel = Some (CLevel (nbLevel - 1))). 
apply getNbLevelEqOption.
rewrite  H in *.
inversion H2;trivial.
apply checkVAddrsEqualityWOOffsetPermut.
assert(Hvax :StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 nbL = false). 
apply checkVAddrsEqualityWOOffsetTrans with v1;trivial.
rewrite <- Hva11.
assert(StateLib.getNbLevel = Some (CLevel (nbLevel - 1))). 
apply getNbLevelEqOption.
rewrite  H in *.
inversion H2;trivial.
apply checkVAddrsEqualityWOOffsetPermut.
clear H3 Hva11 Hva22 Hx.
revert dependent va1.
revert dependent va2.
revert H1 H2.
revert phy1 phy2 p nbL.
clear v1 v2.

induction getAllVAddrWithOffset0.
intuition.
intros.
destruct Hva2; destruct Hva1.
subst.
(* rewrite H2 in H4. *)
contradict Hvax. 
rewrite  Bool.not_false_iff_true.
apply checkVAddrsEqualityWOOffsetEqTrue.
subst.
simpl in *. 
rewrite Hmap2 in H1.
apply NoDup_cons_iff in H1.
destruct H1.
assert(In phy1 (filterOption (map (getMappedPage p s) l))).
apply filterOptionInIff.
apply in_map_iff.
exists va1; split; trivial.
unfold not; intros.
subst.
now contradict H3.
subst.
simpl in *.
rewrite Hmap1 in H1.
apply NoDup_cons_iff in H1.
destruct H1.
assert(In phy2 (filterOption (map (getMappedPage p s) l))).
apply filterOptionInIff.
apply in_map_iff.
exists va2; split; trivial.
unfold not; intros.
subst.
now contradict H0.
subst.
apply IHl with  p nbL va2 va1; trivial.
simpl in H1.
destruct(getMappedPage p s a ).
apply NoDup_cons_iff in H1.
intuition.
assumption.
trivial.
Qed. *)
  admit.
  admit.
  - admit.
  + admit.
  

(* (* induction valist;simpl;intros pd Hmap;trivial.
case_eq( getMappedPage pd s a); [intros x Hx | intros Hx | intros Hx] ;rewrite Hx in *.
+ case_eq (getMappedPage pd s' a );intros.
  - 
simpl in *.
  destruct Hmap;subst.
  *
  assert(Hor: p = pg \/ p <> pg ) by apply pageDecOrNot.
  destruct Hor as [Hor | Hor];[left;trivial|].
  right. 

admit. (*contradiction *)
* right.
  apply IHvalist;trivial.
  - simpl in *.
  destruct Hmap;subst.
  admit.  (**contradiction**)
  apply IHvalist;trivial.
  - simpl in *.
  destruct Hmap;subst.
  admit.  (**contradiction**)
  apply IHvalist;trivial. *)
 
+ case_eq( getMappedPage pd s' vapg );intros.
simpl. trivial. right.
apply IHvalist;trivial.
apply IHvalist;trivial.
apply IHvalist;trivial.
+ case_eq(getMappedPage pd s' a );intros.
 simpl. right.
 apply IHvalist;trivial.
  apply IHvalist;trivial.
   apply IHvalist;trivial. *)
Admitted.



Lemma getChildrenAddIndirection s indirection nextIndirection idxToPrepare partition entry nbLgen:
lookup indirection idxToPrepare (memory s) beqPage beqIndex = Some (PE entry) -> 
Some nbLgen = StateLib.getNbLevel ->
getChildren partition s = getChildren partition {|
  currentPartition := currentPartition s;
  memory := add indirection idxToPrepare
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':={|currentPartition:= _ |}) in *.
unfold getChildren.
intros Hlookup HnbL.
assert(Hgetpd : forall partition, StateLib.getPd partition
  (add indirection idxToPrepare(PE
                     {|
                     read := true;
                     write := true;
                     exec := true;
                     present := true;
                     user := true;
                     pa := nextIndirection |}) 
     (memory s) beqPage beqIndex ) = StateLib.getPd partition (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
intros. 
rewrite Hgetpd in *. clear Hgetpd.
case_eq(StateLib.getPd partition (memory s) );[intros pd Hpd |intros Hpd];
trivial.
assert(Hpds : getPdsVAddr partition nbLgen getAllVAddrWithOffset0 s =
getPdsVAddr partition nbLgen getAllVAddrWithOffset0 s') by admit. 
rewrite <- HnbL.
rewrite <-Hpds.
assert(Hmap: forall valist, getMappedPagesAux pd valist s = 
getMappedPagesAux pd valist s') by admit.
apply Hmap.
Admitted.
Lemma getPartitionsAddIndirection s indirection nextIndirection idxToPrepare:
getPartitions multiplexer s = getPartitions multiplexer {|
  currentPartition := currentPartition s;
  memory := add indirection idxToPrepare
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':={|currentPartition:= _ |}) in *.
unfold getPartitions.
generalize multiplexer at 1 2.
induction (nbPage + 1);simpl;trivial;intros.
f_equal;trivial.
assert(Hchild: forall partition, getChildren partition s = getChildren partition s') by admit.
rewrite <- Hchild.
clear Hchild.
induction (getChildren p s);simpl;trivial.
f_equal.
apply IHn;trivial.
trivial.
Admitted.                 

Lemma kernelDataIsolationAddIndirection s indirection nextIndirection idxToPrepare:
kernelDataIsolation s ->
kernelDataIsolation
  {|
  currentPartition := currentPartition s;
  memory := add indirection idxToPrepare
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}. 
Proof.
intros HKDI.
set(s':={|currentPartition:= _ |}) in *.
unfold kernelDataIsolation in *.
simpl in *;intros partition1 partition2 Hpart1 Hpart2.
assert(Hparts: getPartitions multiplexer s = getPartitions multiplexer s').

Admitted.
 
 
Lemma insertEntryIntoLLPCAddIndirection  ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
 phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable idxToPrepare:
forall s : state,
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) true ->
insertEntryIntoLLPC
  {|
  currentPartition := currentPartition s;
  memory := add phyPDChild idxToPrepare
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := phyMMUaddr |}) (memory s) beqPage beqIndex |} ptMMUTrdVA phySh2addr
  phySh1addr phyMMUaddr ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2
  phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
  descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l
  idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy lastLLTable
  (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) false.
Proof.
intros.
unfold insertEntryIntoLLPC in *;intuition.
unfold propagatedPropertiesPrepare in *.
intuition;subst;trivial.
+ 

Admitted.    
Lemma writePhyEntryAddIndirection ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
     phyMMUaddr phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA
     ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart
     trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred
     fstLL LLChildphy lastLLTable idxToPrepare :
 {{ fun s : state =>
   insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
     phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA
     ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart
     trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred
     fstLL LLChildphy lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1))  true}} 
  writePhyEntry phyPDChild idxToPrepare phyMMUaddr true true true true true
 {{ fun _ s =>  insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr phyMMUaddr ptMMUFstVA
     phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA
     ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart
     trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred
     fstLL LLChildphy lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) false}}.
Proof.
eapply weaken.
eapply WP.writePhyEntry.
simpl.
unfold insertEntryIntoLLPC, propagatedPropertiesPrepare in *.
intuition.

Admitted.
     