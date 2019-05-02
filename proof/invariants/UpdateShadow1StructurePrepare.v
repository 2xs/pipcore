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
    This file contains required lemmas to prove that updating the first shadow 
    structure preserves isolation and consistency properties (prepare) *)

Require Import Model.ADT Core.Internal Isolation Consistency WeakestPreconditions 
Invariants StateLib Model.Hardware  Model.MAL 
DependentTypeLemmas Model.Lib InternalLemmas PropagatedProperties UpdateMappedPageContent
UpdateShadow1Structure.
Require Import Coq.Logic.ProofIrrelevance Omega List Bool. 
(*match pt, idx, vaValue with 
|ptSh1FstVA, idxFstVA, fstVA  =>
|ptSh1SndVA, idxSndVA, sndVA =>
|ptSh1TrdVA, idxTrdVA, trdVA => 
| _, _, _ => True ->*)
Definition PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure  b1 b2 b3 b4 b5 b6  
(vaValue fstVA sndVA trdVA:vaddr) (ptMMU ptSh1 pg ptSh1FstVA ptSh1SndVA ptSh1TrdVA phyMMUaddr 
phySh1addr phySh2addr ptMMUFstVA ptMMUSndVA ptMMUTrdVA :page) 
(idxFstVA idxSndVA idxTrdVA idx:index):=
(ptSh1 =ptSh1FstVA /\ idx= idxFstVA /\ vaValue = fstVA /\ pg=phyMMUaddr /\ ptMMU= ptMMUFstVA  /\ b1 = true /\ b4=false /\ b3 = b6 /\ b2 = b5) 
\/ (ptSh1 =ptSh1SndVA /\ idx= idxSndVA /\ vaValue = sndVA /\ pg=phySh1addr /\ ptMMU= ptMMUSndVA /\ b2 = true /\ b5=false /\ b1= b4 /\ b3 = b6) 
\/ (ptSh1 = ptSh1TrdVA/\ idx= idxTrdVA /\ vaValue = trdVA /\ pg=phySh2addr /\ ptMMU= ptMMUTrdVA /\ b3 = true /\ b6=false /\ b1=b4 /\ b2=b5).

Lemma propagatedPropertiesPrepareUpdateShadow1Structure b1 b2 b3 b4 b5 b6  (vaValue:vaddr) (ptMMU ptSh1  pg:page) (idx:index) s 
       ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare
       ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD
       ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
       currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI:
       
PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure b1 b2 b3 b4 b5 b6  
vaValue fstVA sndVA trdVA ptMMU ptSh1 pg ptSh1FstVA ptSh1SndVA ptSh1TrdVA phyMMUaddr phySh1addr phySh2addr
 ptMMUFstVA ptMMUSndVA ptMMUTrdVA idxFstVA idxSndVA idxTrdVA idx-> 
propagatedPropertiesPrepare s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare
       ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD
       ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
       currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false b1 b2 b3
        idxFstVA idxSndVA idxTrdVA zeroI -> 
propagatedPropertiesPrepare  {|  currentPartition := currentPartition s;
                                 memory := add ptSh1 idx (VE {| pd := false; va := vaValue |}) (memory s) beqPage beqIndex |}
       ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare
       ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD
       ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
       currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false b4 b5 b6
       idxFstVA idxSndVA idxTrdVA zeroI.
Proof.
set (s':= {|currentPartition:= _ |}) in *.
intros Hor Hprops.
unfold propagatedPropertiesPrepare in *.
assert((defaultPage =? ptMMU) = false 
        /\ entryPresentFlag ptMMU (StateLib.getIndexOfAddr vaValue fstLevel) true s
        (* /\ entryUserFlag ptMMU (StateLib.getIndexOfAddr vaValue fstLevel) true s *)
        /\ isEntryPage ptMMU (StateLib.getIndexOfAddr vaValue fstLevel) pg s
        /\ isPE ptMMU idx s
        /\ getTableAddrRoot ptMMU PDidx (currentPartition s) vaValue s
        /\ (defaultPage =? ptSh1 ) = false
        /\ isVE ptSh1 idx s
        /\ StateLib.getIndexOfAddr vaValue fstLevel = idx
        /\ beqVAddr defaultVAddr vaValue = false
        /\ (defaultPage =? ptSh1) = false
        /\ getTableAddrRoot ptSh1 sh1idx (currentPartition s) vaValue s
) as (Hnotdef &Hpres (* &Huser *) & Hentryp & Hpe & Htblmmu & Hsh1notdef
& Hve & Hidx  & Hvanotnull & Hptsh1notnull & Htblsh1).
{ unfold PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure in *;intuition;subst;trivial. }
assert(Hlookup :exists entry, 
 lookup ptSh1 idx (memory s) beqPage beqIndex = Some (VE entry)).
{ assert(Hva : isVE ptSh1 idx s) by trivial.  
  unfold isVE in *.
 subst. 
 destruct(lookup ptSh1
          (StateLib.getIndexOfAddr vaValue fstLevel) (memory s)
          );intros; try now contradict Hva.
 destruct v; try now contradict Hva.
 do 2 f_equal.
 exists v;trivial. }
 destruct Hlookup as(v0 & Hlookup).
 
assert (Hreadflag : isPartitionFalse ptSh1 idx s ).
{ admit.  (* unfold isPartitionFalse.
unfold consistency in *. 
assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
unfold accessibleVAIsNotPartitionDescriptor in *.
assert (Hflag : getPDFlag currentShadow1 vaValue s = false).
{ eapply Haccessva with (partition:= (currentPartition s)) (pd:= currentPD) (page0:=pg).
  unfold consistency in *.
  unfold currentPartitionInPartitionsList in *.
  intuition.
  apply nextEntryIsPPgetPd; intuition.
  apply nextEntryIsPPgetFstShadow;intuition.
  intuition;subst.  
  eapply isAccessibleMappedPage2  with (currentPartition s) ptMMU;trivial.
  intros;subst;split;trivial. }
apply getPDFlagReadPDflag with currentShadow1 vaValue currentPart;trivial.
intuition;subst;trivial.
intros;intuition;subst;trivial. *) }
assert(Hpartitions: getPartitions multiplexer s' = getPartitions multiplexer s) by 
(apply getPartitionsAddDerivation with v0;trivial).
intuition;subst;trivial;simpl.
+ apply kernelDataIsolationUpdtateSh1Structure with (entry:= v0);trivial.
+ apply partitionsIsolationUpdtateSh1Structure with (entry:= v0);trivial.
+ apply verticalSharingUpdtateSh1Structure  with (entry:= v0);trivial.
+ eapply consistencyUpdtateSh1Structure with (level0:= nbLgen) (entry:=v0)
  (currentPD:=currentPD) (ptVaInCurPartpd:=ptMMU) (phyVaChild:=pg);intuition;unfold consistency in *;
  intuition.
+ apply getTableRootAddDerivation with  (StateLib.getIndexOfAddr trdVA fstLevel) v0 isPE;trivial;intros;split;
  subst;trivial.
+ apply isPEAddDerivation with v0;trivial.
+ unfold PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure in *.
   assert (Hi : exists va : vaddr,
         isEntryVA ptSh1TrdVA (StateLib.getIndexOfAddr trdVA fstLevel) va s/\ 
         beqVAddr defaultVAddr va = b3 ) by trivial.
  destruct Hi as (va & Hva & Hderiv).
  destruct Hor as [Hor|[Hor|Hor]];
  intuition;subst.
  - exists va;split;trivial.
    apply isEntryVAAddDerivation; trivial.
    eapply toApplyPageTablesOrIndicesAreDifferent with 
      trdVA  fstVA (currentPartition s)
      currentShadow1 sh1idx nbLgen isVE s ;trivial.
    right;left; trivial.
    rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
    intros;split;subst;trivial.
    intros;split;subst;trivial.
  - exists va;split;trivial.
   apply isEntryVAAddDerivation; trivial.
   eapply toApplyPageTablesOrIndicesAreDifferent with 
    trdVA  sndVA (currentPartition s)
    currentShadow1 sh1idx nbLgen isVE s ;trivial.
   right;left; trivial.
   rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
   intros;split;subst;trivial.
   intros;split;subst;trivial.
  - exists trdVA;split;trivial.
    unfold isEntryVA. cbn.
    assert(Hpairs :  beqPairs (ptSh1TrdVA,  StateLib.getIndexOfAddr trdVA fstLevel)
      (ptSh1TrdVA,  StateLib.getIndexOfAddr trdVA fstLevel)
    beqPage beqIndex = true). 
    apply beqPairsTrue;split;trivial.
    rewrite Hpairs.
    simpl;trivial.
+ apply getTableRootAddDerivation with  (StateLib.getIndexOfAddr trdVA fstLevel) v0 isVE;trivial;intros;split;
  subst;trivial.
+ apply isVEAddDerivation with v0; trivial.
+ apply isEntryPageAddDerivation with v0; trivial.
+ apply entryPresentFlagAddDerivation with v0; trivial.
+ apply entryUserFlagAddDerivation  with v0; trivial.
+ apply getTableRootAddDerivation with  (StateLib.getIndexOfAddr sndVA fstLevel) v0 isPE;trivial; intros;split;
  subst;trivial.
+ apply isPEAddDerivation  with v0; trivial.
+ unfold PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure in *.
   assert (Hi : exists va : vaddr,
         isEntryVA ptSh1SndVA (StateLib.getIndexOfAddr sndVA fstLevel) va s/\ 
         beqVAddr defaultVAddr va = b2 ) by trivial.
  destruct Hi as (va & Hva & Hderiv).
  destruct Hor as [Hor|[Hor|Hor]];
  intuition;subst.
  - exists va;split;trivial.
    apply isEntryVAAddDerivation; trivial.
    eapply toApplyPageTablesOrIndicesAreDifferent with 
      sndVA  fstVA (currentPartition s)
      currentShadow1 sh1idx nbLgen isVE s ;trivial.
    right;left; trivial.
    rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
    intros;split;subst;trivial.
    intros;split;subst;trivial.
  - exists sndVA;split;trivial.
    unfold isEntryVA. cbn.
    assert(Hpairs :  beqPairs (ptSh1SndVA,  StateLib.getIndexOfAddr sndVA fstLevel)
      (ptSh1SndVA,  StateLib.getIndexOfAddr sndVA fstLevel)
    beqPage beqIndex = true). 
    apply beqPairsTrue;split;trivial.
    rewrite Hpairs.
    simpl;trivial.
  - exists va;split;trivial.
    apply isEntryVAAddDerivation; trivial.
    eapply toApplyPageTablesOrIndicesAreDifferent with 
    sndVA trdVA (currentPartition s)
    currentShadow1 sh1idx nbLgen isVE s ;trivial.
    right;left; trivial.
    intros;split;subst;trivial.
    intros;split;subst;trivial.
+ apply getTableRootAddDerivation with  (StateLib.getIndexOfAddr sndVA fstLevel) v0 isVE;trivial;intros;split;
  subst;trivial.
+ apply isVEAddDerivation with v0; trivial.
+ unfold PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure in *.
   assert (Hi : exists va : vaddr,
         isEntryVA ptSh1FstVA (StateLib.getIndexOfAddr fstVA fstLevel) va s/\ 
         beqVAddr defaultVAddr va = b1 ) by trivial.
  destruct Hi as (va & Hva & Hderiv).
  destruct Hor as [Hor|[Hor|Hor]];
  intuition;subst.
  - exists fstVA;split;trivial.
    unfold isEntryVA. cbn.
    assert(Hpairs :  beqPairs (ptSh1FstVA,  StateLib.getIndexOfAddr fstVA fstLevel)
      (ptSh1FstVA,  StateLib.getIndexOfAddr fstVA fstLevel)
    beqPage beqIndex = true). 
    apply beqPairsTrue;split;trivial.
    rewrite Hpairs.
    simpl;trivial.  
  - exists va;split;trivial.
    apply isEntryVAAddDerivation; trivial.
    eapply toApplyPageTablesOrIndicesAreDifferent with 
      fstVA sndVA (currentPartition s)
      currentShadow1 sh1idx nbLgen isVE s ;trivial.
    right;left; trivial.
    intros;split;subst;trivial.
    intros;split;subst;trivial.    
  - exists va;split;trivial.
    apply isEntryVAAddDerivation; trivial.
    eapply toApplyPageTablesOrIndicesAreDifferent with 
    fstVA trdVA (currentPartition s)
    currentShadow1 sh1idx nbLgen isVE s ;trivial.
    right;left; trivial.
    intros;split;subst;trivial.
    intros;split;subst;trivial.
+ apply getTableRootAddDerivation with  (StateLib.getIndexOfAddr fstVA fstLevel) v0 isVE;trivial;intros;split;
  subst;trivial.
+ apply isVEAddDerivation with v0; trivial.
+ apply isEntryPageAddDerivation with v0; trivial.
+ apply entryPresentFlagAddDerivation with v0; trivial.
+ apply entryUserFlagAddDerivation  with v0; trivial.
+ apply getTableRootAddDerivation with  (StateLib.getIndexOfAddr fstVA fstLevel) v0 isPE;trivial;intros;split;
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
Admitted.
 
Lemma writeVirEntryFstVA ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred:
{{ fun s : state =>
   propagatedPropertiesPrepare s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false true true true idxFstVA idxSndVA idxTrdVA zeroI 
   /\ writeAccessibleRecPreparePostcondition currentPart phyMMUaddr s 
   /\ writeAccessibleRecPreparePostcondition currentPart phySh1addr s 
   /\ writeAccessibleRecPreparePostcondition currentPart phySh2addr s 
   /\ StateLib.Level.pred l = Some lpred 
   /\ isWellFormedMMUTables phyMMUaddr s 
   /\ isWellFormedFstShadow lpred phySh1addr s 
   /\ isWellFormedSndShadow lpred phySh2addr s }} 
  
  writeVirEntry ptSh1FstVA idxFstVA fstVA 
  
  {{fun _ s  => 
   propagatedPropertiesPrepare s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false false true true idxFstVA idxSndVA idxTrdVA zeroI 
   /\ writeAccessibleRecPreparePostcondition currentPart phyMMUaddr s 
   /\ writeAccessibleRecPreparePostcondition currentPart phySh1addr s 
   /\ writeAccessibleRecPreparePostcondition currentPart phySh2addr s 
   /\ StateLib.Level.pred l = Some lpred 
   /\ isWellFormedMMUTables phyMMUaddr s 
   /\ isWellFormedFstShadow lpred phySh1addr s 
   /\ isWellFormedSndShadow lpred phySh2addr s}}.
Proof.
eapply weaken. 
eapply WP.writeVirEntry.
simpl;intros.
intuition.
apply propagatedPropertiesPrepareUpdateShadow1Structure with true true true ptMMUFstVA phyMMUaddr; trivial.
unfold PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure.
left;intuition.
Admitted.