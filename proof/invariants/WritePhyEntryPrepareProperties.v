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
    Require Import Arith Lia Classical_Prop.


Require Import  Model.ADT Model.Hardware Core.Services Isolation
Consistency Invariants WeakestPreconditions Model.Lib StateLib
Model.MAL Lib InternalLemmas DependentTypeLemmas GetTableAddr PropagatedProperties 
WriteAccessible MapMMUPage InternalLemmas2 WritePhyEntryPrepare.
 Require Import Omega Bool  Coq.Logic.ProofIrrelevance List.
 
 
Lemma kernelDataIsolationAddIndirection
s indirection nextIndirection  entry nbLgen  pd idxroot  
(vaToPrepare vaNextInd : vaddr) partition l  
(currentPart currentPD ptMMUvaNextInd ptSh1VaNextInd: page) root r w e phyPDChild phyMMUaddr phySh1Child 
  phySh1addr phySh2Child phySh2addr lpred:
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child 
  phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
(forall parts, In parts (getPartitions multiplexer s) ->
   ~ In nextIndirection (getAccessibleMappedPages parts s)) -> 
kernelDataIsolation s ->   
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
verticalSharing s ->
partitionsIsolation s ->
consistency s ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s -> *)
(* (defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some defaultPage->
  
   
isWellFormedMMUTables phyMMUaddr s ->
false = StateLib.Level.eqb l fstLevel ->
nextEntryIsPP partition PDidx pd s ->
writeAccessibleRecPreparePostcondition currentPart nextIndirection s ->
In currentPart (getPartitions multiplexer s) ->
getTableAddrRoot ptMMUvaNextInd PDidx currentPart vaNextInd s->
isPE ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) s->
entryUserFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) false s ->
entryPresentFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) true s ->
nextEntryIsPP currentPart PDidx currentPD s ->
(defaultPage =? ptMMUvaNextInd) = false ->
isEntryPage ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) nextIndirection s ->
(* (exists va : vaddr,
  isEntryVA ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) va s /\ beqVAddr defaultVAddr va = true)-> *)
(defaultPage =? ptSh1VaNextInd) = false ->
getTableAddrRoot ptSh1VaNextInd sh1idx currentPart vaNextInd s ->
isVE ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) s ->

noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP partition idxroot root s ->
In indirection (getIndirections root s)->
isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s  ->
kernelDataIsolation
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
Proof.
intros * Hindor3 Hwell1 Hlpred Hor3 Hnotacces Hkdi.
intros.
 
set(s':={|currentPartition:= _ |}) in *.
unfold kernelDataIsolation in *.
simpl in *;intros partition1 partition2 Hpart1 Hpart2.

assert(Hpart : forall part, In part (getPartitions multiplexer s) <-> In part (getPartitions multiplexer s')).
intros.
unfold s'.
eapply  getPartitionsAddIndirection;trivial;try eassumption;trivial.
rewrite <- Hpart in Hpart1.
rewrite <- Hpart in Hpart2.
clear Hpart. 
unfold disjoint in *.
intros x Hx.
assert(Hgoal: In x (getAccessibleMappedPages partition1 s)).
unfold s' in *.
rewrite  getAccessibleMappedPagesAddIndirection; trivial;try eassumption.
assert(Horpage: x=nextIndirection \/ x <> nextIndirection) by apply pageDecOrNot.
destruct Horpage as [Horpage|Horpage].
- (** same page : nextIndirection *)
  subst.
  generalize (Hnotacces partition1 Hpart1);clear Hnotacces;intros Hnotacces.
  now contradict Hnotacces.
- assert(Horparts1: partition1 = partition \/ partition1 <> partition) by apply pageDecOrNot.
  destruct Horparts1 as [Horparts1|Horparts1].
  + subst.
    assert(Hin: ~ In x (getConfigPages partition2 s)).
    apply Hkdi with partition;trivial.
    contradict Hin.
    assert(Horparts2: partition2 = partition \/ partition2 <> partition) by apply pageDecOrNot.
    destruct Horparts2 as [Horparts2|Horparts2].
    * subst.
    apply getConfigPagesAddIndirectionNotSamePage with nextIndirection root vaToPrepare l lpred indirection entry r w
e idxroot phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;
    trivial.
    intuition.
    (* Ok1 : In x (getConfigPages partition s') -> In x (getConfigPages partition s)*)
    * assert(Hconfig: getConfigPages partition2 s' = getConfigPages partition2 s).
     symmetry. apply getConfigPagesMapMMUPage with partition entry;trivial. (* Ok config Eq : getConfigPagesMapMMUPage*)
     { unfold getConfigPages;simpl.
        right.
        destruct Hor3 as [Hor3 | [Hor3 | Hor3]];subst.
        + apply inGetIndirectionsAuxInConfigPagesPD with root;trivial.
        apply nextEntryIsPPgetPd;trivial.
        + apply inGetIndirectionsAuxInConfigPagesSh1 with root;trivial.
          apply nextEntryIsPPgetFstShadow;trivial.
        + apply inGetIndirectionsAuxInConfigPagesSh2 with root;trivial.
          apply nextEntryIsPPgetSndShadow;trivial.  } 
     assert(Hconfdiff: configTablesAreDifferent s ) by intuition.
     unfold configTablesAreDifferent in *.
     apply Hconfdiff;trivial.
     intuition.
     intuition.
      rewrite <- Hconfig;trivial.
  + assert(Horparts2: partition2 = partition \/ partition2 <> partition) by apply pageDecOrNot.
    destruct Horparts2 as [Horparts2|Horparts2].
    * subst.
      assert(Hin: ~ In x (getConfigPages partition s)).
      apply Hkdi with partition1;trivial.
      contradict Hin.
       apply getConfigPagesAddIndirectionNotSamePage with nextIndirection root vaToPrepare l lpred indirection entry r w
e idxroot phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;
    trivial. intuition. (* Ok1 *)
    * assert(Hconfig: getConfigPages partition2 s' = getConfigPages partition2 s).
     { symmetry. apply getConfigPagesMapMMUPage with partition entry;trivial. (* Ok config Eq : getConfigPagesMapMMUPage*)
     assert(Hconfdiff: configTablesAreDifferent s ) by intuition.
     unfold configTablesAreDifferent in *.
     { unfold getConfigPages;simpl.
        right.
        destruct Hor3 as [Hor3 | [Hor3 | Hor3]];subst.
        + apply inGetIndirectionsAuxInConfigPagesPD with root;trivial.
        apply nextEntryIsPPgetPd;trivial.
        + apply inGetIndirectionsAuxInConfigPagesSh1 with root;trivial.
          apply nextEntryIsPPgetFstShadow;trivial.
        + apply inGetIndirectionsAuxInConfigPagesSh2 with root;trivial.
          apply nextEntryIsPPgetSndShadow;trivial.  }
          intuition.
     intuition.
     }
      rewrite  Hconfig;trivial.
      apply Hkdi with partition1;trivial.
Qed.



    
Lemma insertEntryIntoLLPCAddIndirection  indirection nextIndirection ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
 phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (* idxToPrepare *) e w r idxroot:
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot->  
or3 idxroot ->
forall s : state,
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) true  ->
insertEntryIntoLLPC
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |} ptMMUTrdVA phySh2addr
  phySh1addr phyMMUaddr ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2
  phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
  descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l
  idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy lastLLTable
  (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) false.
Proof.
intros Hor Hor3.
intros.
unfold insertEntryIntoLLPC in *.
unfold propagatedPropertiesPrepare in *.
assert(Hep: isPE indirection (StateLib.getIndexOfAddr vaToPrepare l)  s ).
{ assert(Hnotacces: newIndirectionsAreNotAccessible s  phyMMUaddr phySh1addr phySh2addr) by intuition.
  unfold consistency in *;intuition.
  destruct Hor as[Hor |[Hor | Hor]];intuition;subst.  
  + assert(Hi: indirectionDescription s descChildphy phyPDChild PDidx vaToPrepare l) 
    by (  unfold indirectionDescriptionAll in *; intuition).
    unfold indirectionDescription in *.
    destruct Hi as (root &Hroot & Hrootdef & Horx).
    destruct Horx as [(Heq & Horx)|Horx];subst.
    - apply fstIndirectionContainsPENbLevelGT1  with  PDidx l  vaToPrepare descChildphy ;trivial.
      symmetry;trivial.
    - apply middleIndirectionsContainsPE  with  PDidx l root vaToPrepare descChildphy ;trivial.
      symmetry;trivial.
  + assert(Hi: indirectionDescription s descChildphy phySh1Child sh1idx vaToPrepare l) 
    by (  unfold indirectionDescriptionAll in *; intuition).
    unfold indirectionDescription in *.
    destruct Hi as (root &Hroot & Hrootdef & Horx).
    destruct Horx as [(Heq & Horx)|Horx];subst.
    - apply fstIndirectionContainsPENbLevelGT1  with  sh1idx l  vaToPrepare descChildphy ;trivial.
      symmetry;trivial.
    - apply middleIndirectionsContainsPE  with  sh1idx l root vaToPrepare descChildphy ;trivial.
      symmetry;trivial.
   + assert(Hi: indirectionDescription s descChildphy phySh2Child sh2idx vaToPrepare l) 
    by (  unfold indirectionDescriptionAll in *; intuition).
    unfold indirectionDescription in *.
    destruct Hi as (root &Hroot & Hrootdef & Horx).
    destruct Horx as [(Heq & Horx)|Horx];subst.
    - apply fstIndirectionContainsPENbLevelGT1  with  sh2idx l  vaToPrepare descChildphy ;trivial.
          symmetry;trivial.
    - apply middleIndirectionsContainsPE  with  sh2idx l root vaToPrepare descChildphy ;trivial.
          symmetry;trivial. }   
assert(Hlookup: exists entry, lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry)). 
{ unfold isPE  in Hep.
  case_eq(lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex);intros * Hlookup;
  rewrite Hlookup in *;try now contradict Hep.
  destruct v;try now contradict Hep.
  exists p;trivial. }
destruct Hlookup as (entry & Hlookup).
assert( exists pdchild, nextEntryIsPP descChildphy PDidx pdchild s) as(pdchild & Hpdchild).
{ assert(Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
  unfold partitionDescriptorEntry in *.
  assert(Hchildpart: In descChildphy (getPartitions multiplexer s) ) by intuition.
  generalize (Hpde descChildphy Hchildpart PDidx);clear Hpde;intros Hpde.
  destruct Hpde as (_ & _ & pdchild & Hppchild & Hnptdef). left;trivial.
  exists pdchild;trivial. }
(*  assert(Hindin: In indirection (getIndirections pdchild s)).
 { unfold consistency, indirectionDescriptionAll, isWellFormedTables, writeAccessibleRecPreparePostconditionAll in *.
   assert(Hroot: indirectionDescription s descChildphy indirection PDidx vaToPrepare l).
   { intuition subst;trivial.
   apply indirectionDescriptionInGetIndirections  with descChildphy vaToPrepare l;subst;trivial.
     } } *)
 assert(Hconfig: In indirection (getConfigPages descChildphy s)). 
  { 
 unfold consistency, indirectionDescriptionAll, isWellFormedTables, writeAccessibleRecPreparePostconditionAll in *.
(*     assert(Hroot: indirectionDescription s descChildphy phyPDChild PDidx vaToPrepare l) by trivial. *)
     unfold getConfigPages. 
     simpl. right.
     unfold getConfigPagesAux.
     apply nextEntryIsPPgetPd in Hpdchild.
     rewrite Hpdchild.
     pose proof pdSh1Sh2ListExistsNotNull as Hkey.
     destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
     intuition.
     intuition.     
     rewrite Hsh1.
     rewrite Hsh2.
     rewrite Hll.
     destruct Hor as[Hor |[Hor | Hor]].
     + intuition;subst.
     apply in_app_iff.
     left.
     trivial.
     apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l PDidx;subst;trivial.
     apply nextEntryIsPPgetPd;trivial. 
    + intuition;subst.
     apply in_app_iff.
     right.
     apply in_app_iff.
     left.
     apply indirectionDescriptionInGetIndirections  with descChildphy vaToPrepare l sh1idx;subst;trivial.
     apply nextEntryIsPPgetFstShadow;trivial.
     + intuition;subst.
     apply in_app_iff.
     right.
     apply in_app_iff.
     right.
     apply in_app_iff.
     left.
     apply indirectionDescriptionInGetIndirections  with descChildphy vaToPrepare l sh2idx;subst;trivial.
     apply nextEntryIsPPgetSndShadow;trivial.
       }     
  assert(Haccessnotconfig: forall part, In part (getPartitions multiplexer s) ->
   ~In nextIndirection (getConfigPages part s)). 
   { destruct Hor as[(Hi1&Hi2&Hi3) |[(Hi1&Hi2&Hi3) | (Hi1&Hi2&Hi3)]];subst;
     assert(Hcons: initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr ) by intuition;
     unfold initPEntryTablePreconditionToPropagatePreparePropertiesAll in *;
     unfold initPEntryTablePreconditionToPropagatePrepareProperties in *; 
   intuition. }
   assert(Hchildpart:  In descChildphy (getPartitions multiplexer s)) by intuition.
  apply Haccessnotconfig in Hchildpart.
  assert(forall parts : page,
In parts (getPartitions multiplexer s) -> ~ In nextIndirection (getAccessibleMappedPages parts s)).
{   unfold newIndirectionsAreNotAccessible in *.
  assert(Hnotacces: newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr) by intuition.
unfold newIndirectionsAreNotAccessible in *.
  intros.
  apply Hnotacces;trivial.
  unfold nextIndirectionsOR in *.
  move Hor at bottom.
  intuition.
}
  
  unfold consistency, indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll in *;intuition;subst;trivial.
+ (** kernelDataIsolation **) 
  unfold nextIndirectionsOR in *;intuition;subst;trivial.
  - apply kernelDataIsolationAddIndirection with entry nbLgen pdchild PDidx fstVA descChildphy (currentPartition s)
      currentPD ptMMUFstVA ptSh1FstVA pdchild phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.
    * assert((defaultPage =? indMMUToPrepare) = true /\ isEntryPage phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s) as (Hi1 & Hi2).
      split;trivial.
      apply beq_nat_true in Hi1.
      unfold isEntryPage, StateLib.readPhyEntry in *. rewrite Hlookup in *.
      f_equal. destruct defaultPage;destruct indMMUToPrepare;simpl in *;subst. rewrite Hi2;f_equal;apply proof_irrelevance.
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault;try eassumption.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l PDidx;subst;trivial.
  - pose proof pdSh1Sh2ListExistsNotNull as Hkey.
    destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
    apply kernelDataIsolationAddIndirection with entry nbLgen pdchild sh1idx sndVA descChildphy (currentPartition s)
      currentPD ptMMUSndVA ptSh1SndVA sh1 phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.
    * assert(Hwellx: wellFormedShadows sh1idx s) by trivial.
      unfold wellFormedShadows in Hwellx.
       admit. 
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault with (table := ptMMUSndVA);trivial; try eassumption.
    * apply nextEntryIsPPgetFstShadow;trivial.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l sh1idx;subst;trivial.
      apply nextEntryIsPPgetFstShadow;trivial.
  - pose proof pdSh1Sh2ListExistsNotNull as Hkey.
    destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
    apply kernelDataIsolationAddIndirection with entry nbLgen pdchild sh2idx trdVA descChildphy (currentPartition s)
      currentPD ptMMUTrdVA ptSh1TrdVA sh2 phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.
    * admit. 
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault with (table := ptMMUTrdVA);trivial; try eassumption.
    * apply nextEntryIsPPgetSndShadow;trivial.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l sh2idx;subst;trivial.
      apply nextEntryIsPPgetSndShadow;trivial. 
+ (** partitionsIsolation *)
    
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

