 (*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2024)                *)
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
    This file contains required lemmas to prove that updating the first shadow 
    structure preserves isolation and consistency properties (prepare) *)

Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Internal.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.InternalLemmas
Pip.Proof.Isolation Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Invariants PropagatedProperties UpdateMappedPageContent UpdateShadow1Structure.
Import Bool Coq.Logic.ProofIrrelevance List.

(************************************To MOVE******************************************)


(*******************************************************************************)
Lemma newIndirectionsAreNotMappedAddDerivation s pt idx vaValue v0 part newIndirection: 
let s':= {|
  currentPartition := currentPartition s;
  memory := add pt idx (VE {| pd := false; va := vaValue |}) (memory s) pageEq idxEq |} in 
  lookup pt idx (memory s) pageEq idxEq = Some (VE v0) -> 
isPartitionFalse pt idx s -> 
 newIndirectionsAreNotMappedInChildren s part newIndirection -> 
 newIndirectionsAreNotMappedInChildren s' part newIndirection.
Proof.
intros s' Hlookup Hpart Hgoal.
unfold newIndirectionsAreNotMappedInChildren in *.
intros.
assert(Haccess: getMappedPages child s' =getMappedPages child s).
apply getMappedPagesAddDerivation with v0;trivial.
rewrite Haccess.
apply Hgoal;trivial.
assert(Hparts: getChildren part s' = getChildren part s).
apply getChildrenAddDerivation with v0;trivial.
rewrite <- Hparts;trivial.
Qed.


Lemma propagatedPropertiesPrepareUpdateShadow1Structure b1 b2 b3 b4 b5 b6  (vaValue:vaddr) (ptMMU ptSh1  pg:page) (idx:index) s 
       ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare
       ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD
       ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
       currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI LLroot LLChildphy newLastLLable minFI indMMUToPreparebool:
PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure b1 b2 b3 b4 b5 b6  
vaValue fstVA sndVA trdVA ptMMU ptSh1 pg ptSh1FstVA ptSh1SndVA ptSh1TrdVA phyMMUaddr phySh1addr phySh2addr
 ptMMUFstVA ptMMUSndVA ptMMUTrdVA idxFstVA idxSndVA idxTrdVA idx-> 
isPartitionFalse ptSh1 idx s ->
propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare
       ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD
       ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
       currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false b1 b2 b3
        idxFstVA idxSndVA idxTrdVA zeroI minFI -> 
propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable {|  currentPartition := currentPartition s;
                                 memory := add ptSh1 idx (VE {| pd := false; va := vaValue |}) (memory s) pageEq idxEq |}
       ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare
       ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD
       ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
       currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false b4 b5 b6
       idxFstVA idxSndVA idxTrdVA zeroI minFI.
Proof.
set (s':= {|currentPartition:= _ |}) in *.
intros Hor Hispart Hprops.
unfold propagatedPropertiesPrepare, indirectionDescriptionAll, 
initPEntryTablePreconditionToPropagatePreparePropertiesAll, isPartitionFalseAll in *.  
assert((Nat.eqb pageDefault ptMMU) = false 
        /\ entryPresentFlag ptMMU (StateLib.getIndexOfAddr vaValue levelMin) true s
        (* /\ entryUserFlag ptMMU (StateLib.getIndexOfAddr vaValue fstLevel) true s *)
        /\ isEntryPage ptMMU (StateLib.getIndexOfAddr vaValue levelMin) pg s
        /\ isPE ptMMU idx s
        /\ getTableAddrRoot ptMMU idxPageDir (currentPartition s) vaValue s
        /\ (Nat.eqb pageDefault ptSh1) = false
        /\ isVE ptSh1 idx s
        /\ StateLib.getIndexOfAddr vaValue levelMin = idx
        /\ vaddrEq vaddrDefault vaValue = false
        /\ (Nat.eqb pageDefault ptSh1) = false
        /\ getTableAddrRoot ptSh1 idxShadow1 (currentPartition s) vaValue s 
        /\ isPartitionFalse ptSh1 idx s 
        
) as (Hnotdef &Hpres (* &Huser *) & Hentryp & Hpe & Htblmmu & Hsh1notdef
& Hve & Hidx  & Hvanotnull & Hptsh1notnull & Htblsh1 &Hreadflag).
{ unfold PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure in *;intuition;subst;trivial. }
assert(Hlookup :exists entry, 
 lookup ptSh1 idx (memory s) pageEq idxEq = Some (VE entry)).
{ assert(Hva : isVE ptSh1 idx s) by trivial.  
  unfold isVE in *.
 subst. 
 destruct(lookup ptSh1
          (StateLib.getIndexOfAddr vaValue levelMin) (memory s)
          );intros; try now contradict Hva.
 destruct v; try now contradict Hva.
 do 2 f_equal.
 exists v;trivial. }
 destruct Hlookup as(v0 & Hlookup).
assert(Hpartitions: getPartitions pageRootPartition s' = getPartitions pageRootPartition s) by 
(apply getPartitionsAddDerivation with v0;trivial).
assert(Hchildren: getChildren (currentPartition s) s' = getChildren (currentPartition s) s) by 
(apply getChildrenAddDerivation with v0;trivial).
intuition;subst;trivial;simpl.
+ apply kernelDataIsolationUpdtateSh1Structure with (entry:= v0);trivial.
+ apply partitionsIsolationUpdtateSh1Structure with (entry:= v0);trivial.
+ apply verticalSharingUpdtateSh1Structure  with (entry:= v0);trivial.
+ eapply consistencyUpdtateSh1Structure with (level:= nbLgen) (entry:=v0)
  (currentPD:=currentPD) (ptVaInCurPartpd:=ptMMU) (phyVaChild:=pg);intuition;unfold consistency in *;
  intuition.
+ apply getTableRootAddDerivation with  (StateLib.getIndexOfAddr trdVA levelMin) v0 isPE;trivial;intros;split;
  subst;trivial.
+ apply isPEAddDerivation with v0;trivial.
+ unfold PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure in *.
   assert (Hi : exists va : vaddr,
         isEntryVA ptSh1TrdVA (StateLib.getIndexOfAddr trdVA levelMin) va s/\ 
         vaddrEq vaddrDefault va = b3 ) by trivial.
  destruct Hi as (va & Hva & Hderiv).
  destruct Hor as [Hor|[Hor|Hor]];
  intuition;subst.
  - exists va;split;trivial.
    apply isEntryVAAddDerivation; trivial.
    eapply toApplyPageTablesOrIndicesAreDifferent with 
      trdVA  fstVA (currentPartition s)
      currentShadow1 idxShadow1 nbLgen isVE s ;trivial.
    right;left; trivial.
    rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
    intros;split;subst;trivial.
    intros;split;subst;trivial.
  - exists va;split;trivial.
   apply isEntryVAAddDerivation; trivial.
   eapply toApplyPageTablesOrIndicesAreDifferent with 
    trdVA  sndVA (currentPartition s)
    currentShadow1 idxShadow1 nbLgen isVE s ;trivial.
   right;left; trivial.
   rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
   intros;split;subst;trivial.
   intros;split;subst;trivial.
  - exists trdVA;split;trivial.
    unfold isEntryVA. cbn.
    assert(Hpairs :  beqPairs (ptSh1TrdVA,  StateLib.getIndexOfAddr trdVA levelMin)
      (ptSh1TrdVA,  StateLib.getIndexOfAddr trdVA levelMin)
    pageEq idxEq = true). 
    apply beqPairsTrue;split;trivial.
    rewrite Hpairs.
    simpl;trivial.
+ apply getTableRootAddDerivation with  (StateLib.getIndexOfAddr trdVA levelMin) v0 isVE;trivial;intros;split;
  subst;trivial.
+ apply isVEAddDerivation with v0; trivial.
+ apply isEntryPageAddDerivation with v0; trivial.
+ apply entryPresentFlagAddDerivation with v0; trivial.
+ apply entryUserFlagAddDerivation  with v0; trivial.
+ apply getTableRootAddDerivation with  (StateLib.getIndexOfAddr sndVA levelMin) v0 isPE;trivial; intros;split;
  subst;trivial.
+ apply isPEAddDerivation  with v0; trivial.
+ unfold PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure in *.
   assert (Hi : exists va : vaddr,
         isEntryVA ptSh1SndVA (StateLib.getIndexOfAddr sndVA levelMin) va s/\ 
         vaddrEq vaddrDefault va = b2 ) by trivial.
  destruct Hi as (va & Hva & Hderiv).
  destruct Hor as [Hor|[Hor|Hor]];
  intuition;subst.
  - exists va;split;trivial.
    apply isEntryVAAddDerivation; trivial.
    eapply toApplyPageTablesOrIndicesAreDifferent with 
      sndVA  fstVA (currentPartition s)
      currentShadow1 idxShadow1 nbLgen isVE s ;trivial.
    right;left; trivial.
    rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
    intros;split;subst;trivial.
    intros;split;subst;trivial.
  - exists sndVA;split;trivial.
    unfold isEntryVA. cbn.
    assert(Hpairs :  beqPairs (ptSh1SndVA,  StateLib.getIndexOfAddr sndVA levelMin)
      (ptSh1SndVA,  StateLib.getIndexOfAddr sndVA levelMin)
    pageEq idxEq = true). 
    apply beqPairsTrue;split;trivial.
    rewrite Hpairs.
    simpl;trivial.
  - exists va;split;trivial.
    apply isEntryVAAddDerivation; trivial.
    eapply toApplyPageTablesOrIndicesAreDifferent with 
    sndVA trdVA (currentPartition s)
    currentShadow1 idxShadow1 nbLgen isVE s ;trivial.
    right;left; trivial.
    intros;split;subst;trivial.
    intros;split;subst;trivial.
+ apply getTableRootAddDerivation with  (StateLib.getIndexOfAddr sndVA levelMin) v0 isVE;trivial;intros;split;
  subst;trivial.
+ apply isVEAddDerivation with v0; trivial.
+ unfold PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure in *.
   assert (Hi : exists va : vaddr,
         isEntryVA ptSh1FstVA (StateLib.getIndexOfAddr fstVA levelMin) va s/\ 
         vaddrEq vaddrDefault va = b1 ) by trivial.
  destruct Hi as (va & Hva & Hderiv).
  destruct Hor as [Hor|[Hor|Hor]];
  intuition;subst.
  - exists fstVA;split;trivial.
    unfold isEntryVA. cbn.
    assert(Hpairs :  beqPairs (ptSh1FstVA,  StateLib.getIndexOfAddr fstVA levelMin)
      (ptSh1FstVA,  StateLib.getIndexOfAddr fstVA levelMin)
    pageEq idxEq = true). 
    apply beqPairsTrue;split;trivial.
    rewrite Hpairs.
    simpl;trivial.  
  - exists va;split;trivial.
    apply isEntryVAAddDerivation; trivial.
    eapply toApplyPageTablesOrIndicesAreDifferent with 
      fstVA sndVA (currentPartition s)
      currentShadow1 idxShadow1 nbLgen isVE s ;trivial.
    right;left; trivial.
    intros;split;subst;trivial.
    intros;split;subst;trivial.    
  - exists va;split;trivial.
    apply isEntryVAAddDerivation; trivial.
    eapply toApplyPageTablesOrIndicesAreDifferent with 
    fstVA trdVA (currentPartition s)
    currentShadow1 idxShadow1 nbLgen isVE s ;trivial.
    right;left; trivial.
    intros;split;subst;trivial.
    intros;split;subst;trivial.
+ apply getTableRootAddDerivation with  (StateLib.getIndexOfAddr fstVA levelMin) v0 isVE;trivial;intros;split;
  subst;trivial.
+ apply isVEAddDerivation with v0; trivial.
+ apply isEntryPageAddDerivation with v0; trivial.
+ apply entryPresentFlagAddDerivation with v0; trivial.
+ apply entryUserFlagAddDerivation  with v0; trivial.
+ apply getTableRootAddDerivation with  (StateLib.getIndexOfAddr fstVA levelMin) v0 isPE;trivial;intros;split;
  subst;trivial.
+ apply isPEAddDerivation with v0; trivial.
+ apply entryUserFlagAddDerivation  with v0; trivial.
+ apply entryPresentFlagAddDerivation with v0; trivial.
+ apply isEntryPageAddDerivation with v0; trivial.
+ apply isEntryPageAddDerivation with v0; trivial.
+ apply nextEntryIsPPAddDerivation with v0; trivial.
+ apply nextEntryIsPPAddDerivation with v0; trivial.
+ apply nextEntryIsPPAddDerivation with v0; trivial.
+ rewrite Hpartitions;trivial.
+ rewrite Hchildren;trivial.
+ apply indirectionDescriptionAddDerivation with v0;trivial. 
+ apply indirectionDescriptionAddDerivation with v0;trivial.
+ apply indirectionDescriptionAddDerivation with v0;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesAddDerivation with v0;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesAddDerivation with v0;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesAddDerivation with v0;trivial.
+ assert(Hi: StateLib.getConfigTablesLinkedList descChildphy (memory s) = Some LLroot) by trivial.
  rewrite <- Hi.
  apply getConfigTablesLinkedListAddDerivation with v0;trivial.
+ admit.
+ admit.
+ admit.
Admitted.



Lemma writeVirEntryFstVA ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable minFI indMMUToPreparebool:
{{ fun s : state =>
   propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false true true true idxFstVA idxSndVA idxTrdVA zeroI minFI
   /\ isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA 
   /\ writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s 
   /\ StateLib.Level.pred l = Some lpred 
   /\ isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s
   /\ newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr
   /\ newIndirectionsAreNotMappedInChildrenAll s currentPart phyMMUaddr phySh1addr phySh2addr }} 

  MAL.writeVirEntry ptSh1FstVA idxFstVA fstVA

  {{fun _ s  => 
   propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false false true true idxFstVA idxSndVA idxTrdVA zeroI minFI
   /\ isPartitionFalse ptSh1SndVA idxSndVA s 
   /\ isPartitionFalse ptSh1TrdVA idxTrdVA s
   /\ writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s 
   /\ StateLib.Level.pred l = Some lpred 
   /\ isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s
   /\ newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr
   /\ newIndirectionsAreNotMappedInChildrenAll s currentPart phyMMUaddr phySh1addr phySh2addr
   /\ isEntryVA  ptSh1FstVA idxFstVA fstVA s
   }}.
Proof.
eapply weaken. 
eapply WP.writeVirEntry.
simpl;intros.
assert(Hlookup :exists entry, 
 lookup ptSh1FstVA idxFstVA (memory s) pageEq idxEq = Some (VE entry)).
{ assert(Hva : isVE ptSh1FstVA idxFstVA s) by 
(unfold propagatedPropertiesPrepare in *;intuition;subst;trivial).  
  unfold isVE in *.
 subst. 
 destruct( lookup ptSh1FstVA idxFstVA (memory s) pageEq idxEq
          );intros; try now contradict Hva.
 destruct v; try now contradict Hva.
 do 2 f_equal.
 exists v;trivial. }
 destruct Hlookup as(v0 & Hlookup).
assert(initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr)
as (Hinit1 & Hinit2 & Hinit3) by (unfold propagatedPropertiesPrepare in *;intuition ).
unfold writeAccessibleRecPreparePostconditionAll, isWellFormedTables,  isPartitionFalseAll in *. 
intuition.
+ apply propagatedPropertiesPrepareUpdateShadow1Structure with true true true ptMMUFstVA phyMMUaddr; trivial.
  unfold PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure.
  left;intuition.
+ unfold propagatedPropertiesPrepare in *;intuition.
  apply isPartitionFalseAddDerivationNotEq with sndVA fstVA currentShadow1 nbLgen;trivial.
+ unfold propagatedPropertiesPrepare in *;intuition.
  apply isPartitionFalseAddDerivationNotEq with trdVA fstVA currentShadow1 nbLgen;trivial.
+ apply writeAccessibleRecPreparePostconditionAddDerivation with v0;trivial.
+ apply writeAccessibleRecPreparePostconditionAddDerivation with v0;trivial.
+ apply writeAccessibleRecPreparePostconditionAddDerivation with v0;trivial.
+ apply isWellFormedMMUTablesAddDerivation with v0;trivial.
+ assert(Hconfig: In ptSh1FstVA (getConfigPages currentPart s)).
  apply isConfigTableSh1WithVE with fstVA; unfold propagatedPropertiesPrepare in *; unfold consistency in *;intuition; subst;trivial.
  apply isWellFormedFstShadowTablesAddDerivation with v0 (currentPartition s) ; 
    unfold propagatedPropertiesPrepare in *; unfold consistency in *;intuition; subst;trivial.
+ apply isWellFormedSndShadowTablesAddDerivation with v0;trivial.
+ apply newIndirectionsAreNotAccessibleAddDerivation with v0;trivial.
+ unfold newIndirectionsAreNotMappedInChildrenAll in *.
  intuition ;apply newIndirectionsAreNotMappedAddDerivation with v0;trivial.  
+ unfold isEntryVA;cbn.
  assert(Htrue : beqPairs (ptSh1FstVA, idxFstVA) (ptSh1FstVA, idxFstVA) pageEq idxEq
    = true).
  { apply beqPairsTrue.
    split; trivial. }
  rewrite Htrue.
  cbn;trivial.
Qed.

Lemma writeVirEntrySndVA ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable minFI indMMUToPreparebool:
{{ fun s : state =>
   propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
     phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA
     ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart
     trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false false true true idxFstVA
     idxSndVA idxTrdVA zeroI minFI
 /\ isPartitionFalse ptSh1SndVA idxSndVA s 
 /\ isPartitionFalse ptSh1TrdVA idxTrdVA s
 /\ writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s
 /\ StateLib.Level.pred l = Some lpred
 /\   isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s
 /\ newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr
 /\ newIndirectionsAreNotMappedInChildrenAll s currentPart phyMMUaddr phySh1addr phySh2addr    
 /\  isEntryVA ptSh1FstVA idxFstVA fstVA s }}
  MAL.writeVirEntry ptSh1SndVA idxSndVA sndVA
  {{fun _ s  => 
   propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false false false true idxFstVA idxSndVA idxTrdVA zeroI minFI
   /\ isPartitionFalse ptSh1TrdVA idxTrdVA s
   /\ writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s 
   /\ StateLib.Level.pred l = Some lpred 
   /\ isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s
   /\ newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr
   /\ newIndirectionsAreNotMappedInChildrenAll s currentPart phyMMUaddr phySh1addr phySh2addr
   /\ isEntryVA  ptSh1FstVA idxFstVA fstVA s
   /\ isEntryVA  ptSh1SndVA idxSndVA sndVA s}}.
Proof.
unfold writeAccessibleRecPreparePostconditionAll, isWellFormedTables.
eapply weaken. 
eapply WP.writeVirEntry.
simpl;intros.
assert(Hlookup :exists entry, 
 lookup ptSh1SndVA idxSndVA  (memory s) pageEq idxEq = Some (VE entry)).
{ assert(Hva : isVE ptSh1SndVA idxSndVA  s) by 
(unfold propagatedPropertiesPrepare in *;intuition;subst;trivial).  
  unfold isVE in *.
 subst. 
 destruct( lookup  ptSh1SndVA idxSndVA (memory s) pageEq idxEq
          );intros; try now contradict Hva.
 destruct v; try now contradict Hva.
 do 2 f_equal.
 exists v;trivial. }
 destruct Hlookup as(v0 & Hlookup).
assert(initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr)
as (Hinit1 & Hinit2 & Hinit3)  by (unfold propagatedPropertiesPrepare in *;intuition ).
unfold writeAccessibleRecPreparePostconditionAll, isWellFormedTables in *. 
intuition.
+ eapply propagatedPropertiesPrepareUpdateShadow1Structure with false true true ptMMUSndVA phySh1addr; trivial.
  unfold PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure.
  right;left; intuition.
+ unfold propagatedPropertiesPrepare in *;intuition.
  apply isPartitionFalseAddDerivationNotEq with trdVA sndVA currentShadow1 nbLgen;trivial.
+ apply writeAccessibleRecPreparePostconditionAddDerivation with v0;trivial.
+ apply writeAccessibleRecPreparePostconditionAddDerivation with v0;trivial.
+ apply writeAccessibleRecPreparePostconditionAddDerivation with v0;trivial.
+ apply isWellFormedMMUTablesAddDerivation with v0;trivial.
+ assert(Hconfig: In ptSh1SndVA (getConfigPages currentPart s)).
  apply isConfigTableSh1WithVE with sndVA; unfold propagatedPropertiesPrepare in *; unfold consistency in *;intuition; subst;trivial.
  apply isWellFormedFstShadowTablesAddDerivation with v0 (currentPartition s) ; 
    unfold propagatedPropertiesPrepare in *; unfold consistency in *;intuition; subst;trivial.
+ apply isWellFormedSndShadowTablesAddDerivation with v0;trivial.
+ apply newIndirectionsAreNotAccessibleAddDerivation with v0;trivial.
+ unfold newIndirectionsAreNotMappedInChildrenAll in *.
  intuition ;apply newIndirectionsAreNotMappedAddDerivation with v0;trivial.  
+ unfold propagatedPropertiesPrepare in *.
  intuition;subst.
  apply isEntryVAAddDerivation;trivial.  
  apply toApplyPageTablesOrIndicesAreDifferent with fstVA
      sndVA (currentPartition s)
      currentShadow1 idxShadow1 nbLgen isVE s ;trivial.
      right;left; trivial.
  intros;subst;split;trivial.      
  intros;subst;split;trivial.
+ unfold isEntryVA.
  cbn.
  assert(Htrue : beqPairs (ptSh1SndVA, idxSndVA) (ptSh1SndVA, idxSndVA) pageEq idxEq
    = true).
  { apply beqPairsTrue.
    split; trivial. }
  rewrite Htrue.
  cbn;trivial.
Qed.
 
Lemma writeVirEntryTrdVA ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable minFI indMMUToPreparebool:
{{ fun s : state =>
   propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
     phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA
     ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart
     trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false false false true idxFstVA
     idxSndVA idxTrdVA zeroI minFI
   /\ isPartitionFalse ptSh1TrdVA idxTrdVA s  
   /\ writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s 
   /\ StateLib.Level.pred l = Some lpred 
   /\ isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s
   /\ newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr
   /\ newIndirectionsAreNotMappedInChildrenAll s currentPart phyMMUaddr phySh1addr phySh2addr
   /\ isEntryVA  ptSh1FstVA idxFstVA fstVA s
   /\ isEntryVA  ptSh1SndVA idxSndVA sndVA s}}
  MAL.writeVirEntry ptSh1TrdVA idxTrdVA trdVA

  {{fun _ s  => 
   propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false false false false idxFstVA idxSndVA idxTrdVA zeroI minFI
   /\ writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s 
   /\ StateLib.Level.pred l = Some lpred 
   /\ isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s
   /\ newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr
   /\ newIndirectionsAreNotMappedInChildrenAll s currentPart phyMMUaddr phySh1addr phySh2addr  
   /\ isEntryVA  ptSh1FstVA idxFstVA fstVA s
   /\ isEntryVA  ptSh1SndVA idxSndVA sndVA s
   /\ isEntryVA  ptSh1TrdVA idxTrdVA trdVA s}}.
Proof.
eapply weaken. 
eapply WP.writeVirEntry.
simpl;intros.
assert(Hlookup :exists entry, 
 lookup ptSh1TrdVA idxTrdVA  (memory s) pageEq idxEq = Some (VE entry)).
{ assert(Hva : isVE ptSh1TrdVA idxTrdVA  s) by 
(unfold propagatedPropertiesPrepare in *;intuition;subst;trivial).  
  unfold isVE in *.
 subst. 
 destruct( lookup  ptSh1TrdVA idxTrdVA (memory s) pageEq idxEq
          );intros; try now contradict Hva.
 destruct v; try now contradict Hva.
 do 2 f_equal.
 exists v;trivial. }
 destruct Hlookup as(v0 & Hlookup).
assert(initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr)
as (Hinit1 & Hinit2 & Hinit3) by (unfold propagatedPropertiesPrepare in *;intuition ).
unfold writeAccessibleRecPreparePostconditionAll, isWellFormedTables in *. 
intuition.
+ eapply propagatedPropertiesPrepareUpdateShadow1Structure with false false true ptMMUTrdVA phySh2addr; trivial.
  unfold PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure.
  right;right; intuition.
+ apply writeAccessibleRecPreparePostconditionAddDerivation with v0;trivial.
+ apply writeAccessibleRecPreparePostconditionAddDerivation with v0;trivial.
+ apply writeAccessibleRecPreparePostconditionAddDerivation with v0;trivial.
+ apply isWellFormedMMUTablesAddDerivation with v0;trivial.
+ assert(Hconfig: In ptSh1TrdVA (getConfigPages currentPart s)).
  apply isConfigTableSh1WithVE with trdVA; unfold propagatedPropertiesPrepare in *; unfold consistency in *;intuition; subst;trivial.
  apply isWellFormedFstShadowTablesAddDerivation with v0 (currentPartition s) ; 
    unfold propagatedPropertiesPrepare in *; unfold consistency in *;intuition; subst;trivial.
+ apply isWellFormedSndShadowTablesAddDerivation with v0;trivial.
+ apply newIndirectionsAreNotAccessibleAddDerivation with v0;trivial.
+ unfold newIndirectionsAreNotMappedInChildrenAll in *.
  intuition ;apply newIndirectionsAreNotMappedAddDerivation with v0;trivial. 
+ unfold propagatedPropertiesPrepare in *.
  intuition;subst.
  apply isEntryVAAddDerivation;trivial.  
  apply toApplyPageTablesOrIndicesAreDifferent with fstVA
      trdVA (currentPartition s)
      currentShadow1 idxShadow1 nbLgen isVE s ;trivial.
      right;left; trivial.
  intros;subst;split;trivial.      
  intros;subst;split;trivial.
+ unfold propagatedPropertiesPrepare in *.
  intuition;subst.
  apply isEntryVAAddDerivation;trivial.  
  apply toApplyPageTablesOrIndicesAreDifferent with sndVA
      trdVA (currentPartition s)
      currentShadow1 idxShadow1 nbLgen isVE s ;trivial.
      right;left; trivial.
  intros;subst;split;trivial.      
  intros;subst;split;trivial.
+ unfold isEntryVA.
  cbn.
  assert(Htrue : beqPairs (ptSh1TrdVA, idxTrdVA) (ptSh1TrdVA, idxTrdVA) pageEq idxEq
    = true).
  { apply beqPairsTrue.
    split; trivial. }
  rewrite Htrue.
  cbn;trivial.
Qed.
