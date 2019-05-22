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

(************************************To MOVE******************************************)
Lemma isPartitionFalseAddDerivationNotEq childSh2 idxSh2 ( ptSh1ChildFromSh1:page) idxSh1 descChild (shadow2 shadow1: vaddr) ( currentShadow1:page) (l:level) s: 
isPartitionFalse childSh2 idxSh2 s ->
(defaultPage =? childSh2) = false ->
(defaultPage =? ptSh1ChildFromSh1) = false ->
consistency s ->
StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2 ->
StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1 ->
false = checkVAddrsEqualityWOOffset nbLevel shadow1 shadow2 l ->
isVE childSh2 (StateLib.getIndexOfAddr shadow2 fstLevel) s->
getTableAddrRoot childSh2 sh1idx (currentPartition s) shadow2 s ->
isVE ptSh1ChildFromSh1 (StateLib.getIndexOfAddr shadow1 fstLevel) s ->
getTableAddrRoot ptSh1ChildFromSh1 sh1idx (currentPartition s) shadow1 s ->
nextEntryIsPP (currentPartition s) sh1idx currentShadow1 s ->
Some l = StateLib.getNbLevel ->
isPartitionFalse childSh2 idxSh2
  {|
  currentPartition := currentPartition s;
  memory := add ptSh1ChildFromSh1 idxSh1
              (VE {| pd := false;
                     va := descChild |}) (memory s) beqPage beqIndex |}.
Proof.
intros ispart.
intros.
unfold isPartitionFalse in *.
simpl in *.
assert(Hreadflag : StateLib.readPDflag childSh2 idxSh2
  (add ptSh1ChildFromSh1 idxSh1 (VE {| pd := false; va := descChild |})        
  (memory s) beqPage beqIndex) = StateLib.readPDflag childSh2 idxSh2
  (memory s)).
apply  readPDflagAddDerivation.
eapply toApplyPageTablesOrIndicesAreDifferent with shadow2 shadow1 (currentPartition s) 
currentShadow1 sh1idx l isVE  s;trivial.
right;left;trivial.
subst.
rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
intros;split;subst;trivial.
intros;split;subst;trivial.
rewrite Hreadflag;trivial.
Qed.
Lemma indirectionDescriptionAddDerivation ptSh1 vaValue flag l descChildphy 
phyPDChild vaToPrepare v0 idxroot s:
let s':= {|
      currentPartition := currentPartition s;
      memory := add ptSh1 (StateLib.getIndexOfAddr vaValue fstLevel) 
              (VE {| pd := flag; va := vaValue |}) (memory s) beqPage beqIndex |} in 
 lookup ptSh1 (StateLib.getIndexOfAddr vaValue fstLevel)
            (memory s) beqPage beqIndex = Some (VE v0) -> 
indirectionDescription s descChildphy phyPDChild idxroot vaToPrepare l -> 
indirectionDescription s' descChildphy phyPDChild idxroot vaToPrepare l.
Proof.
intros s' Hlookup Hind.
unfold indirectionDescription in *.
destruct Hind as (tableroot & Hpp & Hnotdef & Hor).
exists tableroot.
split;trivial.
unfold s'.
rewrite <- nextEntryIsPPAddDerivation;trivial. eassumption.
split;trivial.
destruct Hor as  [(Hroot & Hl) |(nbL & stop& HnbL & Hstop & Hind & Hnotdefind & Hl)].
left;split;trivial.
right.
exists nbL, stop.
intuition.
rewrite <- Hind.
apply getIndirectionAddDerivation with v0;trivial. 
Qed.

Lemma initPEntryTablePreconditionToPropagatePreparePropertiesAddDerivation pg
ptSh1 vaValue  v0  s:
let s':= {|
      currentPartition := currentPartition s;
      memory := add ptSh1 (StateLib.getIndexOfAddr vaValue fstLevel) 
              (VE {| pd := false; va := vaValue |}) (memory s) beqPage beqIndex |} in 
 lookup ptSh1 (StateLib.getIndexOfAddr vaValue fstLevel)
            (memory s) beqPage beqIndex = Some (VE v0) -> 
initPEntryTablePreconditionToPropagatePrepareProperties s pg ->
isPartitionFalse ptSh1 (StateLib.getIndexOfAddr vaValue fstLevel)  s -> 
initPEntryTablePreconditionToPropagatePrepareProperties s' pg.
Proof.
intros s' Hlookup (Hgoal & Hnotdef) Hnotpart.
unfold initPEntryTablePreconditionToPropagatePrepareProperties.
split;trivial.
intros part Hpart.
assert(Hpartitions: getPartitions multiplexer s' = getPartitions multiplexer s). (* *)
 apply getPartitionsAddDerivation with v0;trivial.
assert(Hconf: getConfigPages part s'= getConfigPages part s).
apply getConfigPagesAddDerivation with v0;trivial.
rewrite Hconf.
apply Hgoal.
rewrite <- Hpartitions;trivial.
Qed.

Lemma writeAccessibleRecPreparePostconditionAddDerivation desc pg idx
ptSh1 vaValue  v0  s:
let s':= {|
      currentPartition := currentPartition s;
      memory := add ptSh1 idx
              (VE {| pd := false; va := vaValue |}) (memory s) beqPage beqIndex |} in 
 lookup ptSh1 idx
            (memory s) beqPage beqIndex = Some (VE v0) -> 
(* isPartitionFalse ptSh1 (StateLib.getIndexOfAddr vaValue fstLevel)  s -> *)            
writeAccessibleRecPreparePostcondition desc pg s ->
writeAccessibleRecPreparePostcondition desc pg s'.
Proof.
intros s' Hlookup Hgoal (*Hnotpart*).
unfold writeAccessibleRecPreparePostcondition in *.
intros part Hpart.
assert(Haccess: getAccessibleMappedPages part s' = getAccessibleMappedPages part s). (* *)
 apply getAccessibleMappedPagesAddDerivation with v0;trivial.
rewrite Haccess.
apply Hgoal.
assert(Hances: getAncestors desc s' = getAncestors desc s).
apply getAncestorsAddDerivation with v0;trivial.
rewrite <- Hances;trivial.
Qed.

Lemma isWellFormedMMUTablesAddDerivation s pg pt idx vaValue v0:
let s':= {|
  currentPartition := currentPartition s;
  memory := add pt idx (VE {| pd := false; va := vaValue |}) (memory s) beqPage beqIndex |} in 
  lookup pt idx (memory s) beqPage beqIndex = Some (VE v0) -> 
isWellFormedMMUTables pg s -> isWellFormedMMUTables pg s'.
Proof.
intros s' Hlookup Hgoal.
unfold isWellFormedMMUTables in *.
intros.
generalize (Hgoal idx0);clear Hgoal; intros (Hphy & Hpres).
split.
rewrite <- Hphy.
apply readPhyEntryAddDerivation with v0;trivial.
rewrite <- Hpres.
apply readPresentAddDerivation with v0;trivial.
Qed.

Lemma isWellFormedFstShadowTablesAddDerivation s phySh1addr pt idx vaValue v0 nbL partition:
let s':= {|
  currentPartition := currentPartition s;
  memory := add pt idx (VE {| pd := false; va := vaValue |}) (memory s) beqPage beqIndex |} in 
  lookup pt idx (memory s) beqPage beqIndex = Some (VE v0) -> 
initPEntryTablePreconditionToPropagatePrepareProperties s phySh1addr -> 
In partition (getPartitions multiplexer s) -> 
In pt (getConfigPages partition s) ->  
isWellFormedFstShadow nbL phySh1addr s-> isWellFormedFstShadow nbL phySh1addr s'.
Proof.
intros s' Hlookup (Hnotconfig&Hnotnull) Hpart Hconfig Hgoal.
unfold isWellFormedFstShadow in *.
destruct Hgoal as [(Hl & Hgoal) |(Hl & Hgoal)];[left|right];split;trivial;intros idx0;
generalize (Hgoal idx0);clear Hgoal; intros (Hphy & Hpres);
rewrite <- Hpres;rewrite<-  Hphy;split.
apply readPhyEntryAddDerivation with v0;trivial.
apply readPresentAddDerivation with v0;trivial.
apply readVirEntryAddDerivation.
unfold initPEntryTablePreconditionToPropagatePrepareProperties in *.
left.
apply Hnotconfig in Hpart.
unfold not;intros;subst.
now contradict Hconfig.
apply readPDflagAddDerivation.
unfold initPEntryTablePreconditionToPropagatePrepareProperties in *.
left.
apply Hnotconfig in Hpart.
unfold not;intros;subst.
now contradict Hconfig.
Qed.
Lemma isWellFormedSndShadowTablesAddDerivation s pg pt idx vaValue v0 l:
let s':= {|
  currentPartition := currentPartition s;
  memory := add pt idx (VE {| pd := false; va := vaValue |}) (memory s) beqPage beqIndex |} in 
  lookup pt idx (memory s) beqPage beqIndex = Some (VE v0) -> 
isWellFormedSndShadow l pg s -> isWellFormedSndShadow l pg s'.
Proof.
intros s' Hlookup Hgoal.
unfold isWellFormedSndShadow in *.
intros.
destruct Hgoal as [(Hl & Hgoal) |(Hl & Hgoal)];[left|right];split;trivial;intros idx0;
generalize (Hgoal idx0);clear Hgoal;[ intros (Hphy & Hpres)| intros Hphy];
rewrite <- Hphy;[rewrite<-  Hpres;split|].
apply readPhyEntryAddDerivation with v0;trivial.
apply readPresentAddDerivation with v0;trivial.
apply readVirtualAddDerivation with v0;trivial.
Qed.

(*******************************************************************************)
Lemma propagatedPropertiesPrepareUpdateShadow1Structure b1 b2 b3 b4 b5 b6  (vaValue:vaddr) (ptMMU ptSh1  pg:page) (idx:index) s 
       ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare
       ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD
       ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
       currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI LLroot LLChildphy newLastLLable:
PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure b1 b2 b3 b4 b5 b6  
vaValue fstVA sndVA trdVA ptMMU ptSh1 pg ptSh1FstVA ptSh1SndVA ptSh1TrdVA phyMMUaddr phySh1addr phySh2addr
 ptMMUFstVA ptMMUSndVA ptMMUTrdVA idxFstVA idxSndVA idxTrdVA idx-> 
isPartitionFalse ptSh1 idx s ->
propagatedPropertiesPrepare LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare
       ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD
       ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
       currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false b1 b2 b3
        idxFstVA idxSndVA idxTrdVA zeroI -> 
propagatedPropertiesPrepare LLroot LLChildphy newLastLLable {|  currentPartition := currentPartition s;
                                 memory := add ptSh1 idx (VE {| pd := false; va := vaValue |}) (memory s) beqPage beqIndex |}
       ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare
       ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD
       ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
       currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false b4 b5 b6
       idxFstVA idxSndVA idxTrdVA zeroI.
Proof.
set (s':= {|currentPartition:= _ |}) in *.
intros Hor Hispart Hprops.
unfold propagatedPropertiesPrepare, indirectionDescriptionAll, 
initPEntryTablePreconditionToPropagatePreparePropertiesAll, isPartitionFalseAll in *.  
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
        /\ isPartitionFalse ptSh1 idx s 
        
) as (Hnotdef &Hpres (* &Huser *) & Hentryp & Hpe & Htblmmu & Hsh1notdef
& Hve & Hidx  & Hvanotnull & Hptsh1notnull & Htblsh1 &Hreadflag).
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
+ apply indirectionDescriptionAddDerivation with v0;trivial. 
+ apply indirectionDescriptionAddDerivation with v0;trivial.
+ apply indirectionDescriptionAddDerivation with v0;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesAddDerivation with v0;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesAddDerivation with v0;trivial.
+ apply initPEntryTablePreconditionToPropagatePreparePropertiesAddDerivation with v0;trivial.
Admitted.



Lemma writeVirEntryFstVA ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable:
{{ fun s : state =>
   propagatedPropertiesPrepare LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false true true true idxFstVA idxSndVA idxTrdVA zeroI 
   /\ isPartitionFalseAll s ptSh1FstVA ptSh1TrdVA ptSh1SndVA idxFstVA idxSndVA idxTrdVA 
   /\ writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s 
   /\ StateLib.Level.pred l = Some lpred 
   /\ isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s }} 
  
  writeVirEntry ptSh1FstVA idxFstVA fstVA 
  
  {{fun _ s  => 
   propagatedPropertiesPrepare LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false false true true idxFstVA idxSndVA idxTrdVA zeroI 
   /\ isPartitionFalse ptSh1SndVA idxSndVA s 
   /\ isPartitionFalse ptSh1TrdVA idxTrdVA s
   /\ writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s 
   /\ StateLib.Level.pred l = Some lpred 
   /\ isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s
   /\ isEntryVA  ptSh1FstVA idxFstVA fstVA s}}.
Proof.
eapply weaken. 
eapply WP.writeVirEntry.
simpl;intros.
assert(Hlookup :exists entry, 
 lookup ptSh1FstVA idxFstVA (memory s) beqPage beqIndex = Some (VE entry)).
{ assert(Hva : isVE ptSh1FstVA idxFstVA s) by 
(unfold propagatedPropertiesPrepare in *;intuition;subst;trivial).  
  unfold isVE in *.
 subst. 
 destruct( lookup ptSh1FstVA idxFstVA (memory s) beqPage beqIndex
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
+ unfold isEntryVA;cbn.
  assert(Htrue : beqPairs (ptSh1FstVA, idxFstVA) (ptSh1FstVA, idxFstVA) beqPage beqIndex
    = true).
  { apply beqPairsTrue.
    split; trivial. }
  rewrite Htrue.
  cbn;trivial.
Qed.

Lemma writeVirEntrySndVA ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable:
{{ fun s : state =>
   propagatedPropertiesPrepare LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
     phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA
     ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart
     trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false false true true idxFstVA
     idxSndVA idxTrdVA zeroI 
 /\ isPartitionFalse ptSh1SndVA idxSndVA s 
 /\ isPartitionFalse ptSh1TrdVA idxTrdVA s
 /\ writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s /\
   StateLib.Level.pred l = Some lpred /\
   isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s /\ isEntryVA ptSh1FstVA idxFstVA fstVA s }} 
  writeVirEntry ptSh1SndVA idxSndVA sndVA 
    
  {{fun _ s  => 
   propagatedPropertiesPrepare LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false false false true idxFstVA idxSndVA idxTrdVA zeroI 
   /\ isPartitionFalse ptSh1TrdVA idxTrdVA s
   /\ writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s 
   /\ StateLib.Level.pred l = Some lpred 
   /\ isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s
   /\ isEntryVA  ptSh1FstVA idxFstVA fstVA s
   /\ isEntryVA  ptSh1SndVA idxSndVA sndVA s}}.
Proof.
unfold writeAccessibleRecPreparePostconditionAll, isWellFormedTables.
eapply weaken. 
eapply WP.writeVirEntry.
simpl;intros.
assert(Hlookup :exists entry, 
 lookup ptSh1SndVA idxSndVA  (memory s) beqPage beqIndex = Some (VE entry)).
{ assert(Hva : isVE ptSh1SndVA idxSndVA  s) by 
(unfold propagatedPropertiesPrepare in *;intuition;subst;trivial).  
  unfold isVE in *.
 subst. 
 destruct( lookup  ptSh1SndVA idxSndVA (memory s) beqPage beqIndex
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
+ unfold propagatedPropertiesPrepare in *.
  intuition;subst.
  apply isEntryVAAddDerivation;trivial.  
  apply toApplyPageTablesOrIndicesAreDifferent with fstVA
      sndVA (currentPartition s)
      currentShadow1 sh1idx nbLgen isVE s ;trivial.
      right;left; trivial.
  intros;subst;split;trivial.      
  intros;subst;split;trivial.
+ unfold isEntryVA.
  cbn.
  assert(Htrue : beqPairs (ptSh1SndVA, idxSndVA) (ptSh1SndVA, idxSndVA) beqPage beqIndex
    = true).
  { apply beqPairsTrue.
    split; trivial. }
  rewrite Htrue.
  cbn;trivial.
Qed.
 
Lemma writeVirEntryTrdVA ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable:
{{ fun s : state =>
   propagatedPropertiesPrepare LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
     phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA
     ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart
     trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false false false true idxFstVA
     idxSndVA idxTrdVA zeroI 
   /\ isPartitionFalse ptSh1TrdVA idxTrdVA s  
   /\ writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s 
   /\ StateLib.Level.pred l = Some lpred 
   /\ isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s
   /\ isEntryVA  ptSh1FstVA idxFstVA fstVA s
   /\ isEntryVA  ptSh1SndVA idxSndVA sndVA s}} 
  writeVirEntry ptSh1TrdVA idxTrdVA trdVA 
    
  {{fun _ s  => 
   propagatedPropertiesPrepare LLroot LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
      currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false false false false idxFstVA idxSndVA idxTrdVA zeroI 
   /\ writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s 
   /\ StateLib.Level.pred l = Some lpred 
   /\ isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s
   /\ isEntryVA  ptSh1FstVA idxFstVA fstVA s
   /\ isEntryVA  ptSh1SndVA idxSndVA sndVA s
   /\ isEntryVA  ptSh1TrdVA idxTrdVA trdVA s}}.
Proof.
eapply weaken. 
eapply WP.writeVirEntry.
simpl;intros.
assert(Hlookup :exists entry, 
 lookup ptSh1TrdVA idxTrdVA  (memory s) beqPage beqIndex = Some (VE entry)).
{ assert(Hva : isVE ptSh1TrdVA idxTrdVA  s) by 
(unfold propagatedPropertiesPrepare in *;intuition;subst;trivial).  
  unfold isVE in *.
 subst. 
 destruct( lookup  ptSh1TrdVA idxTrdVA (memory s) beqPage beqIndex
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
+ unfold propagatedPropertiesPrepare in *.
  intuition;subst.
  apply isEntryVAAddDerivation;trivial.  
  apply toApplyPageTablesOrIndicesAreDifferent with fstVA
      trdVA (currentPartition s)
      currentShadow1 sh1idx nbLgen isVE s ;trivial.
      right;left; trivial.
  intros;subst;split;trivial.      
  intros;subst;split;trivial.
+ unfold propagatedPropertiesPrepare in *.
  intuition;subst.
  apply isEntryVAAddDerivation;trivial.  
  apply toApplyPageTablesOrIndicesAreDifferent with sndVA
      trdVA (currentPartition s)
      currentShadow1 sh1idx nbLgen isVE s ;trivial.
      right;left; trivial.
  intros;subst;split;trivial.      
  intros;subst;split;trivial.
+ unfold isEntryVA.
  cbn.
  assert(Htrue : beqPairs (ptSh1TrdVA, idxTrdVA) (ptSh1TrdVA, idxTrdVA) beqPage beqIndex
    = true).
  { apply beqPairsTrue.
    split; trivial. }
  rewrite Htrue.
  cbn;trivial.
Qed.