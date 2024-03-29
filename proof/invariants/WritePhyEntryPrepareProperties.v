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
    This file contains the invariant of [writePhyEntry].
    We prove that this instruction preserves the isolation property  *)

Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Services.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.InternalLemmas
Pip.Proof.InternalLemmas2 Pip.Proof.Isolation Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Invariants GetTableAddr Lib MapMMUPage PropagatedProperties WriteAccessible WritePhyEntryPrepare.
Import Arith Bool Classical_Prop Coq.Logic.ProofIrrelevance Lia List ListNotations.
(******************************************* propagatedProperties ***************************)


(************************************************************************)   
 (******************************************* InternalLemmas2 ***************************)

(********************************** dependentTypeLemma **********************************)


(************************************************************************)   
 
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
(forall parts, In parts (getPartitions pageRootPartition s) ->
   ~ In nextIndirection (getAccessibleMappedPages parts s)) -> 
kernelDataIsolation s ->   
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
verticalSharing s ->
partitionsIsolation s ->
consistency s ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s -> *)
(* (defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault->
  
   
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
nextEntryIsPP partition idxPageDir pd s ->
writeAccessibleRecPreparePostcondition currentPart nextIndirection s ->
In currentPart (getPartitions pageRootPartition s) ->
getTableAddrRoot ptMMUvaNextInd idxPageDir currentPart vaNextInd s->
isPE ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) s->
entryUserFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) false s ->
entryPresentFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) true s ->
nextEntryIsPP currentPart idxPageDir currentPD s ->
(pageDefault =? ptMMUvaNextInd) = false ->
isEntryPage ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) nextIndirection s ->
(* (exists va : vaddr,
  isEntryVA ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) va s /\ beqVAddr defaultVAddr va = true)-> *)
(pageDefault =? ptSh1VaNextInd) = false ->
getTableAddrRoot ptSh1VaNextInd idxShadow1 currentPart vaNextInd s ->
isVE ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) s ->

noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
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
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}.
Proof.
intros * Hindor3 Hwell1 Hlpred Hor3 Hnotacces Hkdi.
intros.
 
set(s':={|currentPartition:= _ |}) in *.
unfold kernelDataIsolation in *.
simpl in *;intros partition1 partition2 Hpart1 Hpart2.

assert(Hpart : forall part, In part (getPartitions pageRootPartition s) <-> In part (getPartitions pageRootPartition s')).
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

 Lemma toApplykernelDataIsolationAddIndirection indirection nextIndirection ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
 phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (* idxToPrepare *) e w r idxroot entry pdchild s:
(forall part : page, In part (getPartitions pageRootPartition s) -> ~In nextIndirection (getConfigPages part s)) ->
~ In nextIndirection (getConfigPages descChildphy s) ->
In indirection (getConfigPages descChildphy s) ->
StateLib.readPhyEntry phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot->  
or3 idxroot ->
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) true ->
 lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq =
          Some (PE entry) ->
nextEntryIsPP descChildphy idxPageDir pdchild s ->          
(forall parts : page,
     In parts (getPartitions pageRootPartition s) -> ~In nextIndirection (getAccessibleMappedPages parts s)) ->

kernelDataIsolation
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
              (memory s) pageEq idxEq |}.
Proof.              
intros Haccessnotconfig Hchildpart Hconfig Hread.
  unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, consistency, indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll.
intuition.
  unfold nextIndirectionsOR in *;intuition;subst;trivial.
  - 
    apply kernelDataIsolationAddIndirection with entry nbLgen pdchild idxPageDir fstVA descChildphy (currentPartition s)
      currentPD ptMMUFstVA ptSh1FstVA pdchild phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.       
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault;try eassumption.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l idxPageDir;subst;trivial.
  - pose proof pdSh1Sh2ListExistsNotNull as Hkey.
    destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
    apply kernelDataIsolationAddIndirection with entry nbLgen pdchild idxShadow1 sndVA descChildphy (currentPartition s)
      currentPD ptMMUSndVA ptSh1SndVA sh1 phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.
    * assert(Hl: false = levelEq l levelMin) by trivial.
      assert(Hwellx: wellFormedShadows idxShadow1 s) by trivial.
      unfold wellFormedShadows in Hwellx.
      assert(Hi:  indirectionDescription s descChildphy phySh1Child idxShadow1 vaToPrepare l) by trivial.
      assert(Hii:  indirectionDescription s descChildphy phyPDChild idxPageDir vaToPrepare l) by trivial.
      unfold indirectionDescription in *.
      destruct Hi as (root &Hroot & Hrootdef & Horx).
      destruct Hii as (rootpd &Hrootpd & Hrootdefpd & Horxpd).
      destruct Horx as [(Heq & Horx)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)];subst.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)].
         ** subst.
            assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare l 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
            { apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
            apply nextEntryIsPPgetPd;trivial.
            simpl.
            rewrite <- Hl.
            rewrite Hread.
            rewrite <- beq_nat_refl.
            trivial.
            rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           rewrite <- Hl in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare l) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.
           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred l = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
        ** assert(stop =0 ).
          {  rewrite <- Horx in HnbL.
            inversion HnbL as (Hxxx);subst. 
            assert(Hnat: (nbL - stop) < nbLevel).
            destruct nbL. 
            simpl in *. lia.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst.
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    lia. }
           subst;simpl in *.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare nbL 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = levelEq nbL levelMin) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred nbL = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL1 & stop1 & HnbL1 & Hstop1 & Hind1 & Hdef1 & Hlll1)].
         ** subst.
           assert(stop =0 ).
          {  rewrite <- Horxpd in HnbL.
            inversion HnbL as (Hxxx);subst. 
            assert(Hnat: (nbL - stop) < nbLevel).
            destruct nbL. 
            simpl in *. lia.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst. 
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    lia. }
            subst;simpl in *.
            inversion Hind;subst root.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare nbL 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = levelEq nbL levelMin) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred nbL = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
        ** rewrite <- HnbL in HnbL1.
           inversion HnbL1;subst nbL1.
           assert(stop1 = stop) .
           { assert(Hx: nbL - stop < nbLevel).
           destruct nbL;simpl in *.
           lia.
           apply CLevelIdentity2 in Hx.
           symmetry in Hx.
           rewrite  Hlll1 in Hx.
           assert(Hxx: nbL - stop1 < nbLevel).
           destruct nbL;simpl in *.
           lia.
           apply CLevelIdentity2 in Hxx.
           rewrite Hx in Hxx.
           lia.
 }

           subst stop1.
           
           pose proof nbLevelNotZero.
           assert(Hor: stop = nbL \/ stop < nbL) by lia.
           destruct Hor as [Hor | Hor].
           subst.
           unfold levelEq in Hl.
            contradict Hl.
            unfold CLevel.
            case_eq(lt_dec (nbL - nbL) nbLevel);intros.
            simpl.
            unfold levelMin.
            unfold CLevel.
            case_eq(lt_dec 0 nbLevel);intros * Hvv.
            simpl.
            replace (nbL - nbL) with 0 by lia.
            rewrite <- beq_nat_refl.
            auto.
            lia.
            lia.
           assert ( exists indirection2 : page,
            getIndirection root vaToPrepare nbL (stop+1) s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy rootpd pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              apply getIndirectionStopS1 with phyPDChild;trivial.
              lia.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
            
            apply getIndirectionStopSRead with root;trivial.
            lia.
            apply beq_nat_true in Htrue.
            destruct ind2; destruct pageDefault;simpl in *; inversion Htrue;subst;trivial.
            rewrite Hind2.
            f_equal.
            f_equal.
            apply proof_irrelevance.
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault with (table := ptMMUSndVA);trivial; try eassumption.
    * apply nextEntryIsPPgetFstShadow;trivial.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l idxShadow1;subst;trivial.
      apply nextEntryIsPPgetFstShadow;trivial.
  - pose proof pdSh1Sh2ListExistsNotNull as Hkey.
    destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
    apply kernelDataIsolationAddIndirection with entry nbLgen pdchild idxShadow2 trdVA descChildphy (currentPartition s)
      currentPD ptMMUTrdVA ptSh1TrdVA sh2 phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.
    * assert(Hl: false = levelEq l levelMin) by trivial.
      assert(Hwellx: wellFormedShadows idxShadow2 s) by trivial.
      unfold wellFormedShadows in Hwellx.
      assert(Hi:  indirectionDescription s descChildphy phySh2Child idxShadow2 vaToPrepare l) by trivial.
      assert(Hii:  indirectionDescription s descChildphy phyPDChild idxPageDir vaToPrepare l) by trivial.
      unfold indirectionDescription in *.
      destruct Hi as (root &Hroot & Hrootdef & Horx).
      destruct Hii as (rootpd &Hrootpd & Hrootdefpd & Horxpd).
      destruct Horx as [(Heq & Horx)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)];subst.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)].
         ** subst.
            assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare l 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
            { apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
            apply nextEntryIsPPgetPd;trivial.
            simpl.
            rewrite <- Hl.
            rewrite Hread.
            rewrite <- beq_nat_refl.
            trivial.
            rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           rewrite <- Hl in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare l) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.
           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred l = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
        ** assert(stop =0 ).
          {  rewrite <- Horx in HnbL.
            inversion HnbL as (Hxxx);subst. 
            assert(Hnat: (nbL - stop) < nbLevel).
            destruct nbL. 
            simpl in *. lia.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst.
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    lia. }
           subst;simpl in *.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare nbL 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = levelEq nbL levelMin) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred nbL = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL1 & stop1 & HnbL1 & Hstop1 & Hind1 & Hdef1 & Hlll1)].
         ** subst.
           assert(stop =0 ).
          {  rewrite <- Horxpd in HnbL.
            inversion HnbL as (Hxxx);subst. 
            assert(Hnat: (nbL - stop) < nbLevel).
            destruct nbL. 
            simpl in *. lia.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst. 
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    lia. }
            subst;simpl in *.
            inversion Hind;subst root.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare nbL 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = levelEq nbL levelMin) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred nbL = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
        ** rewrite <- HnbL in HnbL1.
           inversion HnbL1;subst nbL1.
           assert(stop1 = stop) .
           { assert(Hx: nbL - stop < nbLevel).
           destruct nbL ;simpl in *.
           lia.
           apply CLevelIdentity2 in Hx.
           symmetry in Hx.
           rewrite  Hlll1 in Hx.
           assert(Hxx: nbL - stop1 < nbLevel).
           destruct nbL;simpl in *.
           lia.
           apply CLevelIdentity2 in Hxx.
           rewrite Hx in Hxx.
           lia.
 }

           subst stop1.
           
           pose proof nbLevelNotZero.
           assert(Hor: stop = nbL \/ stop < nbL) by lia.
           destruct Hor as [Hor | Hor].
           subst.
           unfold levelEq in Hl.
            contradict Hl.
            unfold CLevel.
            case_eq(lt_dec (nbL - nbL) nbLevel);intros.
            simpl.
            unfold levelMin.
            unfold CLevel.
            case_eq(lt_dec 0 nbLevel);intros * Hvv.
            simpl.
            replace (nbL - nbL) with 0 by lia.
            rewrite <- beq_nat_refl.
            auto.
            lia.
            lia.
           assert ( exists indirection2 : page,
            getIndirection root vaToPrepare nbL (stop+1) s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy rootpd pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              apply getIndirectionStopS1 with phyPDChild;trivial.
              lia.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
            
            apply getIndirectionStopSRead with root;trivial.
            lia.
            apply beq_nat_true in Htrue.
            destruct ind2; destruct pageDefault;simpl in *; inversion Htrue;subst;trivial.
            rewrite Hind2.
            f_equal.
            f_equal.
            apply proof_irrelevance. 
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault with (table := ptMMUTrdVA);trivial; try eassumption.
    * apply nextEntryIsPPgetSndShadow;trivial.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l idxShadow2;subst;trivial.
      apply nextEntryIsPPgetSndShadow;trivial. 
Qed.

Lemma partitionsIsolationAddIndirection
s indirection nextIndirection  entry nbLgen  pd idxroot  
(vaToPrepare vaNextInd : vaddr) phyDescChild l  
(currentPart currentPD ptMMUvaNextInd ptSh1VaNextInd: page) root r w e phyPDChild phyMMUaddr phySh1Child 
  phySh1addr phySh2Child phySh2addr lpred:
newIndirectionsAreNotMappedInChildrenAll s currentPart phyMMUaddr phySh1addr phySh2addr -> 
  partitionsIsolation s ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child 
  phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
(forall parts, In parts (getPartitions pageRootPartition s) ->
   ~ In nextIndirection (getAccessibleMappedPages parts s)) -> 
kernelDataIsolation s ->   
initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
verticalSharing s ->
In phyDescChild (getChildren currentPart s) ->
consistency s ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s phyDescChild indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s -> *)
(* (defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault->
  
   
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
nextEntryIsPP phyDescChild idxPageDir pd s ->
writeAccessibleRecPreparePostcondition currentPart nextIndirection s ->
In currentPart (getPartitions pageRootPartition s) ->
getTableAddrRoot ptMMUvaNextInd idxPageDir currentPart vaNextInd s->
isPE ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) s->
entryUserFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) false s ->
entryPresentFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) true s ->
nextEntryIsPP currentPart idxPageDir currentPD s ->
(pageDefault =? ptMMUvaNextInd) = false ->
isEntryPage ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) nextIndirection s ->
(* (exists va : vaddr,
  isEntryVA ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) va s /\ beqVAddr defaultVAddr va = true)-> *)
(pageDefault =? ptSh1VaNextInd) = false ->
getTableAddrRoot ptSh1VaNextInd idxShadow1 currentPart vaNextInd s ->
isVE ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) s ->

noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In phyDescChild (getPartitions pageRootPartition s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP phyDescChild idxroot root s ->
In indirection (getIndirections root s)-> 
In indirection (getConfigPages phyDescChild s) ->
isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s  ->

(* isPartitionFalseAll s  ptSh1FstVA  ptSh1TrdVA ptSh1SndVA idxFstVA   idxSndVA   idxTrdVA -> *)
partitionsIsolation
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
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}.
Proof.
intros * Hnotshared Hiso Hindor3 Hwell1 Hlpred Hor3 Hnotacces Hkdi (Hnotconf1 & Hnotconf2 & Hnotconf3).
intros.
 
set(s':={|currentPartition:= _ |}) in *.
unfold partitionsIsolation in *.
simpl in *;intros * Hparent Hchild1 Hchild2 Hdist.
assert(Hpart : forall part, In part (getPartitions pageRootPartition s) <-> In part (getPartitions pageRootPartition s')).
intros.
unfold s'.
eapply  getPartitionsAddIndirection;trivial;try eassumption;trivial.
rewrite <- Hpart in *.
clear Hpart.
assert(Hpart : forall part, In part (getChildren parent s) <-> In part (getChildren parent s')).
intros.
eapply getChildrenAddIndirection;try eassumption;trivial.
symmetry;trivial.
rewrite <- Hpart in *.
assert(Hchild : In phyDescChild (getPartitions pageRootPartition s)) by trivial.
assert(Hnotsamepart : forall part, phyDescChild <> part -> 
In part (getPartitions pageRootPartition s) -> 
getUsedPages part s = getUsedPages part s').
{ intros. apply getUsedPagesAddIndirectionNotSamePart with entry nbLgen root
     phyDescChild idxroot  
    phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr ;trivial.
    intuition. }
assert(Horx:  ( phyDescChild <> child1 /\ phyDescChild <> child2) \/
            (phyDescChild = child1 \/ phyDescChild = child2)).
{ clear. destruct phyDescChild;destruct child1 ; destruct child2.
  simpl in *.
  assert(  (p <> p0 /\ p <> p1) \/
  (p = p0 \/ p = p1)) by lia.
  destruct
   H. left. 
   destruct H.
   split. 
   unfold not;intros.
   inversion H1.
   subst.
   lia.
   unfold not;intros.
   inversion H1.
   subst.
   lia.
   right. 
   destruct H. 
   left. 
   subst.
   f_equal.
   apply proof_irrelevance.
   right. 
   subst;f_equal.
   apply proof_irrelevance. }
destruct Horx as [Horx| Horx].
+ (*phyDescChild <> child1 /\ phyDescChild <> child2 *)
 destruct Horx as (Hor1 & Hor2).
 assert(Hnodup :  noDupPartitionTree s).
 unfold consistency in *.
 intuition.
  rewrite <- Hnotsamepart;trivial.
  rewrite <- Hnotsamepart;trivial.
  apply Hiso with parent;trivial.
  apply childrenPartitionInPartitionList with parent;trivial.
  apply childrenPartitionInPartitionList with parent;trivial.
+ destruct Horx as [Horx | Horx].  
  - (** phyDescChild = child1 **)
    subst child1.
    assert(Heq: getUsedPages child2 s = getUsedPages child2 s'). 
    { apply Hnotsamepart;trivial.
      apply childrenPartitionInPartitionList with parent;trivial. }
    rewrite <- Heq.
    unfold getUsedPages.
    unfold disjoint.
    intros * Hgoal.
    rewrite in_app_iff in *.
    destruct Hgoal as [Hgoal | Hgoal].
    * apply and_not_or.
      split.
      ++ assert(Hor1: x=nextIndirection \/ x<> nextIndirection) by apply pageDecOrNot.
         destruct Hor1 as [Hor1 | Hor1].
         -- subst x.
            destruct Hindor3 as [(Hi1 & Hi2 & Hii3) | [(Hi1 & Hi2 & Hii3) | (Hi1 & Hi2 & Hii3)] ].
            ** subst. apply Hnotconf1;trivial.
               apply childrenPartitionInPartitionList with parent;trivial.         
            ** subst. apply Hnotconf2;trivial.
               apply childrenPartitionInPartitionList with parent;trivial.         
            ** subst. apply Hnotconf3;trivial.
               apply childrenPartitionInPartitionList with parent;trivial.         
         -- assert(In x (getConfigPages phyDescChild s)).
            apply getConfigPagesAddIndirectionNotSamePage with nextIndirection root vaToPrepare l lpred indirection entry r w
            e idxroot phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;
            trivial. intuition.
            assert(Hconf: configTablesAreDifferent s) by  trivial.
            unfold configTablesAreDifferent in *.
            unfold disjoint in *.
            apply Hconf with phyDescChild;trivial.
            apply childrenPartitionInPartitionList with parent;trivial.
      ++ assert(Hor1: x=nextIndirection \/ x<> nextIndirection) by apply pageDecOrNot.
         destruct Hor1 as [Hor1 | Hor1].
         -- subst x.
         assert(Hparentcons : isParent s).
        unfold consistency in *.
        intuition.
        assert(parent = currentPart). 
        { apply getParentNextEntryIsPPEq with phyDescChild s;
          trivial.
          apply nextEntryIsPPgetParent;trivial.
          apply Hparentcons;trivial.
          unfold consistency in *.
          unfold currentPartitionInPartitionsList in *.
        apply Hparentcons;trivial. }
        subst parent.
        move Hnotshared at bottom.
        unfold newIndirectionsAreNotMappedInChildrenAll in *.        
        destruct Hnotshared as (Hshared1 & Hshared2 & Hshared3).
        unfold newIndirectionsAreNotMappedInChildren in *.
        destruct Hindor3 as [(Hi1 & Hi2 & Hii3) | [(Hi1 & Hi2 & Hii3) | (Hi1 & Hi2 & Hii3)] ];subst.
        apply Hshared1;trivial.
        apply Hshared2;trivial.        
        apply Hshared3;trivial.
        (** propagate new internal property: ~ In child  (getMappedPages phyDescChild s) *)
        -- assert(In x (getConfigPages phyDescChild s)).
           apply getConfigPagesAddIndirectionNotSamePage with nextIndirection root vaToPrepare l lpred indirection entry r w
            e idxroot phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;
           trivial. intuition.
           move Hiso at bottom.
           assert(Hkey: disjoint (getUsedPages phyDescChild s) (getUsedPages child2 s)).
           apply Hiso with parent;trivial.
           unfold disjoint in Hkey.
           unfold getUsedPages in *.
           generalize(Hkey x);clear Hkey;intros Hkey.
           rewrite in_app_iff in Hkey. 
           unfold not;intros.
           destruct Hkey. 
           left;trivial.
           apply in_app_iff.
           right;trivial.
   * apply and_not_or.
     assert (Hssi: forall x, In x (getMappedPages phyDescChild s) <-> 
          In x (getMappedPages phyDescChild s')).
     intros. 
     eapply getMappedPagesAddIndirectionSamePart;try eassumption.
     split.
     ++ assert(Hor1: x=nextIndirection \/ x<> nextIndirection) by apply pageDecOrNot.
        destruct Hor1 as [Hor1 | Hor1].
        -- subst x.
           rewrite <- Hssi in Hgoal.
           clear Hssi.
           contradict Hgoal.
           move Hnotshared at bottom.
            unfold newIndirectionsAreNotMappedInChildrenAll in *.        
            destruct Hnotshared as (Hshared1 & Hshared2 & Hshared3).
            unfold newIndirectionsAreNotMappedInChildren in *.
            destruct Hindor3 as [(Hi1 & Hi2 & Hii3) | [(Hi1 & Hi2 & Hii3) | (Hi1 & Hi2 & Hii3)] ];subst.
            apply Hshared1;trivial.
            apply Hshared2;trivial.        
            apply Hshared3;trivial.
   (** propagate new internal property: ~In nextIndirection  (getMappedPages phyDescChild s) *)
        -- rewrite <- Hssi in Hgoal.
           unfold disjoint in *.
           generalize (Hiso parent phyDescChild child2 Hparent Hchild1 Hchild2 Hdist x);
           clear Hiso;intros Hiso.
           unfold getUsedPages in Hiso.
           rewrite in_app_iff in Hiso.
           rewrite in_app_iff in Hiso.
           assert(Hx: ~ (In x (getConfigPages child2 s) \/ In x (getMappedPages child2 s))).
           apply Hiso;trivial.
           right;trivial.
           apply not_or_and in Hx.
           intuition.
     ++ rewrite <- Hssi in Hgoal.    
        unfold disjoint in *.
        generalize (Hiso parent phyDescChild child2 Hparent Hchild1 Hchild2 Hdist x);
        clear Hiso;intros Hiso.
        unfold getUsedPages in Hiso.
        rewrite in_app_iff in Hiso.
        rewrite in_app_iff in Hiso.
        assert(Hx: ~ (In x (getConfigPages child2 s) \/ In x (getMappedPages child2 s))).
        apply Hiso;trivial.
        right;trivial.
        apply not_or_and in Hx.
        intuition.
  - subst child2.
    rename child1 into child2.
    assert(Heq: getUsedPages child2 s = getUsedPages child2 s'). 
    { apply Hnotsamepart;trivial.
      intuition.
      apply childrenPartitionInPartitionList with parent;trivial. }
    rewrite <- Heq.
    unfold getUsedPages.
    unfold disjoint.
    intros * Hgoal.
    rewrite in_app_iff in *.
    destruct Hgoal as [Hgoal | Hgoal].
    * apply and_not_or.
      split.
      ++ assert(Hor1: x=nextIndirection \/ x<> nextIndirection) by apply pageDecOrNot.
         destruct Hor1 as [Hor1 | Hor1].
         -- subst x.
            destruct Hindor3 as [(Hi1 & Hi2 & Hii3) | [(Hi1 & Hi2 & Hii3) | (Hi1 & Hi2 & Hii3)] ]; contradict Hgoal.
            ** subst. apply Hnotconf1;trivial.
               apply childrenPartitionInPartitionList with parent;trivial.         
            ** subst. apply Hnotconf2;trivial.
               apply childrenPartitionInPartitionList with parent;trivial.         
            ** subst. apply Hnotconf3;trivial.
               apply childrenPartitionInPartitionList with parent;trivial.         
         -- contradict Hgoal.
            assert(In x (getConfigPages phyDescChild s)).
            apply getConfigPagesAddIndirectionNotSamePage with nextIndirection root vaToPrepare l lpred indirection entry r w
            e idxroot phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;
            trivial. intuition.
            assert(Hconf: configTablesAreDifferent s) by  trivial.
            unfold configTablesAreDifferent in *.
            unfold disjoint in *.
            apply Hconf with phyDescChild;trivial.
            apply childrenPartitionInPartitionList with parent;trivial.
            intuition.
      ++ assert(Hor1: x=nextIndirection \/ x<> nextIndirection) by apply pageDecOrNot.
         destruct Hor1 as [Hor1 | Hor1].
         -- subst x.
         contradict Hgoal.
         assert(Hparentcons : isParent s).
        unfold consistency in *.
        intuition.
        assert(parent = currentPart). 
        { apply getParentNextEntryIsPPEq with phyDescChild s;
          trivial.
          apply nextEntryIsPPgetParent;trivial.
          apply Hparentcons;trivial.
          unfold consistency in *.
          unfold currentPartitionInPartitionsList in *.
        apply Hparentcons;trivial. }
        subst parent.
        assert (Hssi: forall x, In x (getMappedPages phyDescChild s) <-> 
        In x (getMappedPages phyDescChild s')).
        intros. 
        eapply getMappedPagesAddIndirectionSamePart;try eassumption.
        rewrite <- Hssi in Hgoal.
        contradict Hgoal.
        move Hnotshared at bottom.
        unfold newIndirectionsAreNotMappedInChildrenAll in *.        
        destruct Hnotshared as (Hshared1 & Hshared2 & Hshared3).
        unfold newIndirectionsAreNotMappedInChildren in *.
        destruct Hindor3 as [(Hi1 & Hi2 & Hii3) | [(Hi1 & Hi2 & Hii3) | (Hi1 & Hi2 & Hii3)] ];subst.
        apply Hshared1;trivial.
        apply Hshared2;trivial.        
        apply Hshared3;trivial.
        (** propagate new internal property: ~ In child  (getMappedPages phyDescChild s) *)
        -- contradict Hgoal.
           assert (Hssi: forall x, In x (getMappedPages phyDescChild s) <-> 
             In x (getMappedPages phyDescChild s')).
           intros. 
           eapply getMappedPagesAddIndirectionSamePart;try eassumption.
            rewrite <- Hssi in Hgoal.
           unfold disjoint in *.
           assert(Hdis': phyDescChild<>child2) by intuition.
           generalize (Hiso parent phyDescChild child2 Hparent Hchild2 Hchild1 Hdis' x);
           clear Hiso;intros Hiso.
           unfold getUsedPages in Hiso.
           rewrite in_app_iff in Hiso.
           rewrite in_app_iff in Hiso.
           assert(Hx: ~ (In x (getConfigPages child2 s) \/ In x (getMappedPages child2 s))).
           apply Hiso;trivial.
           right;trivial.
           apply not_or_and in Hx.
           intuition.
           (*  *)
    * apply and_not_or.
     assert (Hssi: forall x, In x (getMappedPages phyDescChild s) <-> 
          In x (getMappedPages phyDescChild s')).
     intros. 
     eapply getMappedPagesAddIndirectionSamePart;try eassumption.
     split.
     ++ assert(Hor1: x=nextIndirection \/ x<> nextIndirection) by apply pageDecOrNot.
        destruct Hor1 as [Hor1 | Hor1].
        -- subst x.
           contradict Hgoal.
          assert(Hparentcons : isParent s).
          unfold consistency in *.
          intuition.
          assert(parent = currentPart). 
          { apply getParentNextEntryIsPPEq with phyDescChild s;
            trivial.
            apply nextEntryIsPPgetParent;trivial.
            apply Hparentcons;trivial.
            unfold consistency in *.
            unfold currentPartitionInPartitionsList in *.
            apply Hparentcons;trivial. }
          subst parent.
          move Hnotshared at bottom.
          unfold newIndirectionsAreNotMappedInChildrenAll in *.        
          destruct Hnotshared as (Hshared1 & Hshared2 & Hshared3).
          unfold newIndirectionsAreNotMappedInChildren in *.
          destruct Hindor3 as [(Hi1 & Hi2 & Hii3) | [(Hi1 & Hi2 & Hii3) | (Hi1 & Hi2 & Hii3)] ];subst.
          apply Hshared1;trivial.
          apply Hshared2;trivial.        
          apply Hshared3;trivial. 
         (** propagate new internal property: ~In nextIndirection  (getMappedPages phyDescChild s) *)
        -- contradict Hgoal.
           assert(In x (getConfigPages phyDescChild s)).
           { apply getConfigPagesAddIndirectionNotSamePage with nextIndirection root vaToPrepare l lpred indirection entry r w
            e idxroot phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;
           trivial. intuition. }
           move Hiso at bottom.
           assert(Hkey: disjoint (getUsedPages child2 s) (getUsedPages phyDescChild s)).
           apply Hiso with parent;trivial.
           unfold disjoint in Hkey.
           unfold getUsedPages in *.
           generalize(Hkey x);clear Hkey;intros Hkey.
           rewrite in_app_iff in Hkey. 
           unfold not;intros.
           destruct Hkey. 
           right;trivial.
           apply in_app_iff.
           left;trivial.
     ++ rewrite <- Hssi.    
        unfold disjoint in *.
        assert(Hdis': phyDescChild<>child2) by intuition.
        generalize (Hiso parent child2 phyDescChild  Hparent Hchild1 Hchild2 Hdist x);
        clear Hiso;intros Hiso.
        unfold getUsedPages in Hiso.
        rewrite in_app_iff in Hiso.
        rewrite in_app_iff in Hiso.
        assert(Hx: ~ (In x (getConfigPages phyDescChild s) \/ In x (getMappedPages phyDescChild s))).
        apply Hiso;trivial.
        right;trivial.
        apply not_or_and in Hx.
        intuition.
Qed.

 Lemma toApplyPartitionsIsolationAddIndirection indirection nextIndirection ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
 phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (* idxToPrepare *) e w r idxroot entry pdchild s:
(forall part : page, In part (getPartitions pageRootPartition s) -> ~In nextIndirection (getConfigPages part s)) ->
~ In nextIndirection (getConfigPages descChildphy s) ->
In indirection (getConfigPages descChildphy s) ->
StateLib.readPhyEntry phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot->  
or3 idxroot ->
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) true ->
 lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq =
          Some (PE entry) ->
nextEntryIsPP descChildphy idxPageDir pdchild s ->
(forall parts : page,
     In parts (getPartitions pageRootPartition s) -> ~In nextIndirection (getAccessibleMappedPages parts s)) ->
In descChildphy (getChildren (currentPartition s) s) ->
partitionsIsolation
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
              (memory s) pageEq idxEq |}.
Proof.              
intros Haccessnotconfig Hchildpart Hconfig Hread.
  unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, consistency, indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll.
intuition.
  unfold nextIndirectionsOR in *;intuition;subst;trivial.
  -   apply partitionsIsolationAddIndirection  with entry nbLgen pdchild idxPageDir fstVA descChildphy (currentPartition s) 
currentPD ptMMUFstVA ptSh1FstVA pdchild phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.       
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault;try eassumption.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l idxPageDir;subst;trivial.
  - pose proof pdSh1Sh2ListExistsNotNull as Hkey.
    destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
    apply partitionsIsolationAddIndirection with entry nbLgen pdchild idxShadow1 sndVA descChildphy (currentPartition s)
      currentPD ptMMUSndVA ptSh1SndVA sh1 phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.
    * assert(Hl: false = levelEq l levelMin) by trivial.
      assert(Hwellx: wellFormedShadows idxShadow1 s) by trivial.
      unfold wellFormedShadows in Hwellx.
      assert(Hi:  indirectionDescription s descChildphy phySh1Child idxShadow1 vaToPrepare l) by trivial.
      assert(Hii:  indirectionDescription s descChildphy phyPDChild idxPageDir vaToPrepare l) by trivial.
      unfold indirectionDescription in *.
      destruct Hi as (root &Hroot & Hrootdef & Horx).
      destruct Hii as (rootpd &Hrootpd & Hrootdefpd & Horxpd).
      destruct Horx as [(Heq & Horx)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)];subst.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)].
         ** subst.
            assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare l 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
            { apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
            apply nextEntryIsPPgetPd;trivial.
            simpl.
            rewrite <- Hl.
            rewrite Hread.
            rewrite <- beq_nat_refl.
            trivial.
            rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           rewrite <- Hl in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare l) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.
           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred l = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
        ** assert(stop =0 ).
          {  rewrite <- Horx in HnbL.
            inversion HnbL as (Hxxx);subst. 
            assert(Hnat: (nbL - stop) < nbLevel).
            destruct nbL. 
            simpl in *. lia.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst.
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    lia. }
           subst;simpl in *.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare nbL 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = levelEq nbL levelMin) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred nbL = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL1 & stop1 & HnbL1 & Hstop1 & Hind1 & Hdef1 & Hlll1)].
         ** subst.
           assert(stop =0 ).
          {  rewrite <- Horxpd in HnbL.
            inversion HnbL as (Hxxx);subst. 
            assert(Hnat: (nbL - stop) < nbLevel).
            destruct nbL. 
            simpl in *. lia.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst. 
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    lia. }
            subst;simpl in *.
            inversion Hind;subst root.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare nbL 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = levelEq nbL levelMin) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred nbL = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
        ** rewrite <- HnbL in HnbL1.
           inversion HnbL1;subst nbL1.
           assert(stop1 = stop) .
           { assert(Hx: nbL - stop < nbLevel).
           destruct nbL;simpl in *.
           lia.
           apply CLevelIdentity2 in Hx.
           symmetry in Hx.
           rewrite  Hlll1 in Hx.
           assert(Hxx: nbL - stop1 < nbLevel).
           destruct nbL;simpl in *.
           lia.
           apply CLevelIdentity2 in Hxx.
           rewrite Hx in Hxx.
           lia. }
           subst stop1.
           pose proof nbLevelNotZero.
           assert(Hor: stop = nbL \/ stop < nbL) by lia.
           destruct Hor as [Hor | Hor].
           subst.
           unfold levelEq in Hl.
            contradict Hl.
            unfold CLevel.
            case_eq(lt_dec (nbL - nbL) nbLevel);intros.
            simpl.
            unfold levelMin.
            unfold CLevel.
            case_eq(lt_dec 0 nbLevel);intros * Hvv.
            simpl.
            replace (nbL - nbL) with 0 by lia.
            rewrite <- beq_nat_refl.
            auto.
            lia.
            lia.
           assert ( exists indirection2 : page,
            getIndirection root vaToPrepare nbL (stop+1) s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy rootpd pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              apply getIndirectionStopS1 with phyPDChild;trivial.
              lia.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
            apply getIndirectionStopSRead with root;trivial.
            lia.
            apply beq_nat_true in Htrue.
            destruct ind2; destruct pageDefault;simpl in *; inversion Htrue;subst;trivial.
            rewrite Hind2.
            f_equal.
            f_equal.
            apply proof_irrelevance.
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault with (table := ptMMUSndVA);trivial; try eassumption.
    * apply nextEntryIsPPgetFstShadow;trivial.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l idxShadow1;subst;trivial.
      apply nextEntryIsPPgetFstShadow;trivial.
  - pose proof pdSh1Sh2ListExistsNotNull as Hkey.
    destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
    apply partitionsIsolationAddIndirection with entry nbLgen pdchild idxShadow2 trdVA descChildphy (currentPartition s)
      currentPD ptMMUTrdVA ptSh1TrdVA sh2 phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.
    * assert(Hl: false = levelEq l levelMin) by trivial.
      assert(Hwellx: wellFormedShadows idxShadow2 s) by trivial.
      unfold wellFormedShadows in Hwellx.
      assert(Hi:  indirectionDescription s descChildphy phySh2Child idxShadow2 vaToPrepare l) by trivial.
      assert(Hii:  indirectionDescription s descChildphy phyPDChild idxPageDir vaToPrepare l) by trivial.
      unfold indirectionDescription in *.
      destruct Hi as (root &Hroot & Hrootdef & Horx).
      destruct Hii as (rootpd &Hrootpd & Hrootdefpd & Horxpd).
      destruct Horx as [(Heq & Horx)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)];subst.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)].
         ** subst.
            assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare l 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
            { apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
            apply nextEntryIsPPgetPd;trivial.
            simpl.
            rewrite <- Hl.
            rewrite Hread.
            rewrite <- beq_nat_refl.
            trivial.
            rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           rewrite <- Hl in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare l) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.
           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred l = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
        ** assert(stop =0 ).
          {  rewrite <- Horx in HnbL.
            inversion HnbL as (Hxxx);subst. 
            assert(Hnat: (nbL - stop) < nbLevel).
            destruct nbL. 
            simpl in *. lia.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst.
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    lia. }
           subst;simpl in *.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare nbL 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = levelEq nbL levelMin) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred nbL = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL1 & stop1 & HnbL1 & Hstop1 & Hind1 & Hdef1 & Hlll1)].
         ** subst.
           assert(stop =0 ).
          {  rewrite <- Horxpd in HnbL.
            inversion HnbL as (Hxxx);subst. 
            assert(Hnat: (nbL - stop) < nbLevel).
            destruct nbL. 
            simpl in *. lia.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst. 
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    lia. }
            subst;simpl in *.
            inversion Hind;subst root.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare nbL 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = levelEq nbL levelMin) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred nbL = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
        ** rewrite <- HnbL in HnbL1.
           inversion HnbL1;subst nbL1.
           assert(stop1 = stop) .
           { assert(Hx: nbL - stop < nbLevel).
           destruct nbL ;simpl in *.
           lia.
           apply CLevelIdentity2 in Hx.
           symmetry in Hx.
           rewrite  Hlll1 in Hx.
           assert(Hxx: nbL - stop1 < nbLevel).
           destruct nbL;simpl in *.
           lia.
           apply CLevelIdentity2 in Hxx.
           rewrite Hx in Hxx.
           lia.
 }

           subst stop1.
           pose proof nbLevelNotZero.
           assert(Hor: stop = nbL \/ stop < nbL) by lia.
           destruct Hor as [Hor | Hor].
           subst.
           unfold levelEq in Hl.
            contradict Hl.
            unfold CLevel.
            case_eq(lt_dec (nbL - nbL) nbLevel);intros.
            simpl.
            unfold levelMin.
            unfold CLevel.
            case_eq(lt_dec 0 nbLevel);intros * Hvv.
            simpl.
            replace (nbL - nbL) with 0 by lia.
            rewrite <- beq_nat_refl.
            auto.
            lia.
            lia.
           assert ( exists indirection2 : page,
            getIndirection root vaToPrepare nbL (stop+1) s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy rootpd pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              apply getIndirectionStopS1 with phyPDChild;trivial.
              lia.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
            apply getIndirectionStopSRead with root;trivial.
            lia.
            apply beq_nat_true in Htrue.
            destruct ind2; destruct pageDefault;simpl in *; inversion Htrue;subst;trivial.
            rewrite Hind2.
            f_equal.
            f_equal.
            apply proof_irrelevance. 
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault with (table := ptMMUTrdVA);trivial; try eassumption.
    * apply nextEntryIsPPgetSndShadow;trivial.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l idxShadow2;subst;trivial.
      apply nextEntryIsPPgetSndShadow;trivial. 
Qed.
Lemma verticalSharingAddIndirection
s indirection nextIndirection  entry nbLgen  pd idxroot  
(vaToPrepare vaNextInd : vaddr) phyDescChild l  
(currentPart currentPD ptMMUvaNextInd ptSh1VaNextInd: page) root r w e phyPDChild phyMMUaddr phySh1Child 
  phySh1addr phySh2Child phySh2addr lpred:
newIndirectionsAreNotMappedInChildrenAll s currentPart phyMMUaddr phySh1addr phySh2addr -> 
  verticalSharing s ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child 
  phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
(forall parts, In parts (getPartitions pageRootPartition s) ->
   ~ In nextIndirection (getAccessibleMappedPages parts s)) -> 
kernelDataIsolation s ->   
initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
verticalSharing s ->
In phyDescChild (getChildren currentPart s) ->
consistency s ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s phyDescChild indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s -> *)
(* (defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault->
  
   
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
nextEntryIsPP phyDescChild idxPageDir pd s ->
writeAccessibleRecPreparePostcondition currentPart nextIndirection s ->
In currentPart (getPartitions pageRootPartition s) ->
getTableAddrRoot ptMMUvaNextInd idxPageDir currentPart vaNextInd s->
isPE ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) s->
entryUserFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) false s ->
entryPresentFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) true s ->
nextEntryIsPP currentPart idxPageDir currentPD s ->
(pageDefault =? ptMMUvaNextInd) = false ->
isEntryPage ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) nextIndirection s ->
(* (exists va : vaddr,
  isEntryVA ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) va s /\ beqVAddr defaultVAddr va = true)-> *)
(pageDefault =? ptSh1VaNextInd) = false ->
getTableAddrRoot ptSh1VaNextInd idxShadow1 currentPart vaNextInd s ->
isVE ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) s ->

noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In phyDescChild (getPartitions pageRootPartition s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP phyDescChild idxroot root s ->
In indirection (getIndirections root s)-> 
In indirection (getConfigPages phyDescChild s) ->
isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s  ->

(* isPartitionFalseAll s  ptSh1FstVA  ptSh1TrdVA ptSh1SndVA idxFstVA   idxSndVA   idxTrdVA -> *)
verticalSharing
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
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}.
Proof.
intros * Hnotshared Hiso Hindor3 Hwell1 Hlpred Hor3 Hnotacces Hkdi (Hnotconf1 & Hnotconf2 & Hnotconf3).
intros. 
set(s':={|currentPartition:= _ |}) in *.
unfold verticalSharing in *.
simpl in *;intros * Hparent Hchild1.
assert(Hpart : forall part, In part (getPartitions pageRootPartition s) <-> In part (getPartitions pageRootPartition s')).
intros.
unfold s'.
eapply  getPartitionsAddIndirection;trivial;try eassumption;trivial.
rewrite <- Hpart in *.
clear Hpart.
assert(Hpart : forall part, In part (getChildren parent s) <-> In part (getChildren parent s')).
intros.
eapply getChildrenAddIndirection;try eassumption;trivial.
symmetry;trivial.
rewrite <- Hpart in *.
assert(Hchild : In phyDescChild (getPartitions pageRootPartition s)) by trivial.
assert(Hnotsamepart : forall part, phyDescChild <> part -> 
In part (getPartitions pageRootPartition s) -> 
getUsedPages part s = getUsedPages part s').
{ intros. apply getUsedPagesAddIndirectionNotSamePart with entry nbLgen root
     phyDescChild idxroot  
    phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr ;trivial.
    intuition. }
assert (Hssi: forall x, In x (getMappedPages phyDescChild s) <-> 
          In x (getMappedPages phyDescChild s')).
intros. 
eapply getMappedPagesAddIndirectionSamePart;try eassumption.    
assert(Hor:  child= phyDescChild \/ child<> phyDescChild) by apply pageDecOrNot.   
destruct Hor as  [Hor|Hor].
+ subst child.    
  assert(Hparentcons : isParent s).
  unfold consistency in *.
  intuition.
  assert(parent = currentPart). 
  { apply getParentNextEntryIsPPEq with phyDescChild s;
  trivial.
  apply nextEntryIsPPgetParent;trivial.
  apply Hparentcons;trivial.
  unfold consistency in *.
  unfold currentPartitionInPartitionsList in *.
  apply Hparentcons;trivial. }
  subst parent.
  unfold incl.
  intros * Hgoal.
  assert(Heq:getMappedPages currentPart s = getMappedPages currentPart s'). 
  { apply getMappedPagesAddIndirectionNotSamePart with  entry nbLgen root phyDescChild idxroot phyPDChild phyMMUaddr phySh1Child phySh1addr
    phySh2Child phySh2addr;trivial.
    apply childIsNotParent with s;trivial. 
    unfold consistency in *;intuition. }
  rewrite <- Heq.
  unfold getUsedPages in Hgoal.
  apply in_app_iff in Hgoal.
  destruct Hgoal as [Hgoal| Hgoal].
  - assert(Hor1: a=nextIndirection \/ a<> nextIndirection) by apply pageDecOrNot.
    destruct Hor1 as [Hor1 | Hor1].
    * subst a.
      destruct Hindor3 as [(Hi1 & Hi2 & Hii3) | [(Hi1 & Hi2 & Hii3) | (Hi1 & Hi2 & Hii3)] ];subst;
      eapply inGetMappedPagesGetTableRoot with (pt:=ptMMUvaNextInd) (va:=vaNextInd);intros;subst;try eassumption;
         split;trivial.
    * assert(In a (getConfigPages phyDescChild s)).
      { apply getConfigPagesAddIndirectionNotSamePage with nextIndirection root vaToPrepare l lpred indirection entry r w
        e idxroot phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;
        trivial. intuition. }
      unfold incl in *.
      apply Hiso with phyDescChild;trivial.
      unfold getUsedPages.
      apply in_app_iff.
      left;trivial.
   - unfold incl in *.
     apply Hiso with phyDescChild;trivial.
     unfold getUsedPages.
     apply in_app_iff.
     right;trivial.
     apply Hssi;trivial.
+ unfold incl; intros * Hgoal.
  assert(Heq: getUsedPages child s = getUsedPages child s').
  apply Hnotsamepart;trivial.
  intuition.
  apply childrenPartitionInPartitionList with parent;trivial.
  rewrite <-Heq in *.
  assert(Hor1: parent = phyDescChild \/ parent <> phyDescChild) by apply pageDecOrNot.
  destruct Hor1 as [Hor1| Hor1].
  - subst. 
    apply Hssi.
    unfold incl in *.
    apply Hiso with child;trivial.
  - assert(Heqp:getMappedPages parent s = getMappedPages parent s'). 
    { apply getMappedPagesAddIndirectionNotSamePart with  entry nbLgen root phyDescChild idxroot phyPDChild phyMMUaddr phySh1Child phySh1addr
      phySh2Child phySh2addr;trivial. }
    rewrite <- Heqp.
    unfold incl in *.
    apply Hiso with child;trivial.
Qed.

Lemma toApplyVerticalSharingAddIndirection indirection nextIndirection ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
 phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (* idxToPrepare *) e w r idxroot entry pdchild s:
(forall part : page, In part (getPartitions pageRootPartition s) -> ~In nextIndirection (getConfigPages part s)) ->
~ In nextIndirection (getConfigPages descChildphy s) ->
In indirection (getConfigPages descChildphy s) ->
StateLib.readPhyEntry phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot->  
or3 idxroot ->
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) true ->
 lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq =
          Some (PE entry) ->
nextEntryIsPP descChildphy idxPageDir pdchild s ->          
(forall parts : page,
     In parts (getPartitions pageRootPartition s) -> ~In nextIndirection (getAccessibleMappedPages parts s)) ->
In descChildphy (getChildren (currentPartition s) s) ->
verticalSharing
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
              (memory s) pageEq idxEq |}.
Proof.              
intros Haccessnotconfig Hchildpart Hconfig Hread.
  unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, consistency, indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll.
intuition.
  unfold nextIndirectionsOR in *;intuition;subst;trivial.
  -   apply verticalSharingAddIndirection  with entry nbLgen pdchild idxPageDir fstVA descChildphy (currentPartition s) 
currentPD ptMMUFstVA ptSh1FstVA pdchild phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.       
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault;try eassumption.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l idxPageDir;subst;trivial.
  - pose proof pdSh1Sh2ListExistsNotNull as Hkey.
    destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
    apply verticalSharingAddIndirection with entry nbLgen pdchild idxShadow1 sndVA descChildphy (currentPartition s)
      currentPD ptMMUSndVA ptSh1SndVA sh1 phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.
    * assert(Hl: false = levelEq l levelMin) by trivial.
      assert(Hwellx: wellFormedShadows idxShadow1 s) by trivial.
      unfold wellFormedShadows in Hwellx.
      assert(Hi:  indirectionDescription s descChildphy phySh1Child idxShadow1 vaToPrepare l) by trivial.
      assert(Hii:  indirectionDescription s descChildphy phyPDChild idxPageDir vaToPrepare l) by trivial.
      unfold indirectionDescription in *.
      destruct Hi as (root &Hroot & Hrootdef & Horx).
      destruct Hii as (rootpd &Hrootpd & Hrootdefpd & Horxpd).
      destruct Horx as [(Heq & Horx)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)];subst.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)].
         ** subst.
            assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare l 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
            { apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
            apply nextEntryIsPPgetPd;trivial.
            simpl.
            rewrite <- Hl.
            rewrite Hread.
            rewrite <- beq_nat_refl.
            trivial.
            rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           rewrite <- Hl in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare l) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.
           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred l = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
        ** assert(stop =0 ).
          {  rewrite <- Horx in HnbL.
            inversion HnbL as (Hxxx);subst. 
            assert(Hnat: (nbL - stop) < nbLevel).
            destruct nbL. 
            simpl in *. lia.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst.
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    lia. }
           subst;simpl in *.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare nbL 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = levelEq nbL levelMin) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred nbL = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL1 & stop1 & HnbL1 & Hstop1 & Hind1 & Hdef1 & Hlll1)].
         ** subst.
           assert(stop =0 ).
          {  rewrite <- Horxpd in HnbL.
            inversion HnbL as (Hxxx);subst. 
            assert(Hnat: (nbL - stop) < nbLevel).
            destruct nbL. 
            simpl in *. lia.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst. 
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    lia. }
            subst;simpl in *.
            inversion Hind;subst root.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare nbL 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = levelEq nbL levelMin) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred nbL = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
        ** rewrite <- HnbL in HnbL1.
           inversion HnbL1;subst nbL1.
           assert(stop1 = stop) .
           { assert(Hx: nbL - stop < nbLevel).
           destruct nbL;simpl in *.
           lia.
           apply CLevelIdentity2 in Hx.
           symmetry in Hx.
           rewrite  Hlll1 in Hx.
           assert(Hxx: nbL - stop1 < nbLevel).
           destruct nbL;simpl in *.
           lia.
           apply CLevelIdentity2 in Hxx.
           rewrite Hx in Hxx.
           lia.
 }

           subst stop1.
           
           pose proof nbLevelNotZero.
           assert(Hor: stop = nbL \/ stop < nbL) by lia.
           destruct Hor as [Hor | Hor].
           subst.
           unfold levelEq in Hl.
            contradict Hl.
            unfold CLevel.
            case_eq(lt_dec (nbL - nbL) nbLevel);intros.
            simpl.
            unfold levelMin.
            unfold CLevel.
            case_eq(lt_dec 0 nbLevel);intros * Hvv.
            simpl.
            replace (nbL - nbL) with 0 by lia.
            rewrite <- beq_nat_refl.
            auto.
            lia.
            lia.
           assert ( exists indirection2 : page,
            getIndirection root vaToPrepare nbL (stop+1) s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy rootpd pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              apply getIndirectionStopS1 with phyPDChild;trivial.
              lia.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
            
            apply getIndirectionStopSRead with root;trivial.
            lia.
            apply beq_nat_true in Htrue.
            destruct ind2; destruct pageDefault;simpl in *; inversion Htrue;subst;trivial.
            rewrite Hind2.
            f_equal.
            f_equal.
            apply proof_irrelevance.
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault with (table := ptMMUSndVA);trivial; try eassumption.
    * apply nextEntryIsPPgetFstShadow;trivial.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l idxShadow1;subst;trivial.
      apply nextEntryIsPPgetFstShadow;trivial.
  - pose proof pdSh1Sh2ListExistsNotNull as Hkey.
    destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
    apply verticalSharingAddIndirection with entry nbLgen pdchild idxShadow2 trdVA descChildphy (currentPartition s)
      currentPD ptMMUTrdVA ptSh1TrdVA sh2 phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.
    * assert(Hl: false = levelEq l levelMin) by trivial.
      assert(Hwellx: wellFormedShadows idxShadow2 s) by trivial.
      unfold wellFormedShadows in Hwellx.
      assert(Hi:  indirectionDescription s descChildphy phySh2Child idxShadow2 vaToPrepare l) by trivial.
      assert(Hii:  indirectionDescription s descChildphy phyPDChild idxPageDir vaToPrepare l) by trivial.
      unfold indirectionDescription in *.
      destruct Hi as (root &Hroot & Hrootdef & Horx).
      destruct Hii as (rootpd &Hrootpd & Hrootdefpd & Horxpd).
      destruct Horx as [(Heq & Horx)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)];subst.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)].
         ** subst.
            assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare l 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
            { apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
            apply nextEntryIsPPgetPd;trivial.
            simpl.
            rewrite <- Hl.
            rewrite Hread.
            rewrite <- beq_nat_refl.
            trivial.
            rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           rewrite <- Hl in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare l) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.
           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred l = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
        ** assert(stop =0 ).
          {  rewrite <- Horx in HnbL.
            inversion HnbL as (Hxxx);subst. 
            assert(Hnat: (nbL - stop) < nbLevel).
            destruct nbL. 
            simpl in *. lia.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst.
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    lia. }
           subst;simpl in *.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare nbL 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = levelEq nbL levelMin) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred nbL = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL1 & stop1 & HnbL1 & Hstop1 & Hind1 & Hdef1 & Hlll1)].
         ** subst.
           assert(stop =0 ).
          {  rewrite <- Horxpd in HnbL.
            inversion HnbL as (Hxxx);subst. 
            assert(Hnat: (nbL - stop) < nbLevel).
            destruct nbL. 
            simpl in *. lia.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst. 
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    lia. }
            subst;simpl in *.
            inversion Hind;subst root.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare nbL 1 s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = levelEq nbL levelMin) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(pageDefault =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct pageDefault;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
           assert(Hlpred: StateLib.Level.pred nbL = Some lpred) by trivial.
           rewrite Hlpred in Hind2.
           inversion Hind2;subst.
           rewrite Heq in Htrue.
           now contradict Htrue.
        ** rewrite <- HnbL in HnbL1.
           inversion HnbL1;subst nbL1.
           assert(stop1 = stop) .
           { assert(Hx: nbL - stop < nbLevel).
           destruct nbL ;simpl in *.
           lia.
           apply CLevelIdentity2 in Hx.
           symmetry in Hx.
           rewrite  Hlll1 in Hx.
           assert(Hxx: nbL - stop1 < nbLevel).
           destruct nbL;simpl in *.
           lia.
           apply CLevelIdentity2 in Hxx.
           rewrite Hx in Hxx.
           lia.
 }

           subst stop1.
           
           pose proof nbLevelNotZero.
           assert(Hor: stop = nbL \/ stop < nbL) by lia.
           destruct Hor as [Hor | Hor].
           subst.
           unfold levelEq in Hl.
            contradict Hl.
            unfold CLevel.
            case_eq(lt_dec (nbL - nbL) nbLevel);intros.
            simpl.
            unfold levelMin.
            unfold CLevel.
            case_eq(lt_dec 0 nbLevel);intros * Hvv.
            simpl.
            replace (nbL - nbL) with 0 by lia.
            rewrite <- beq_nat_refl.
            auto.
            lia.
            lia.
           assert ( exists indirection2 : page,
            getIndirection root vaToPrepare nbL (stop+1) s = Some indirection2 /\
            (pageDefault =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy rootpd pageDefault;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              apply getIndirectionStopS1 with phyPDChild;trivial.
              lia.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
            
            apply getIndirectionStopSRead with root;trivial.
            lia.
            apply beq_nat_true in Htrue.
            destruct ind2; destruct pageDefault;simpl in *; inversion Htrue;subst;trivial.
            rewrite Hind2.
            f_equal.
            f_equal.
            apply proof_irrelevance. 
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault with (table := ptMMUTrdVA);trivial; try eassumption.
    * apply nextEntryIsPPgetSndShadow;trivial.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l idxShadow2;subst;trivial.
      apply nextEntryIsPPgetSndShadow;trivial. 
Qed.

Lemma partitionDescriptorEntryAddIndirection
s indirection nextIndirection idxroot  entry nbLgen  pd   vaToPrepare partition l lpred r w e
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr :
partitionDescriptorEntry s->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
nextEntryIsPP partition idxroot pd s ->
In indirection (getIndirections pd s) ->

StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 

noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->

(* isPartitionFalseAll s  ptSh1FstVA  ptSh1TrdVA ptSh1SndVA idxFstVA   idxSndVA   idxTrdVA -> *)
partitionDescriptorEntry
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
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}.
Proof.
set(s':={|currentPartition:= _ |}) in *.
(* intros * Hgoal Hnotshared Hiso Hindor3 Hwell1 Hlpred Hor3 Hnotacces Hkdi (Hnotconf1 & Hnotconf2 & Hnotconf3). *)
intros Hgoal.
intros.
move Hgoal at bottom.
unfold partitionDescriptorEntry in *. 
intros.
assert( idxroot0 < tableSize - 1 /\
     isVA partition0 idxroot0 s /\
     (exists entry : page,
        nextEntryIsPP partition0 idxroot0 entry s /\ entry <> pageDefault)) 
        as (Hi1 & Hi2 & Hi3) .
apply Hgoal;trivial.
assert(Hpart : forall part, In part (getPartitions pageRootPartition s) <-> In part (getPartitions pageRootPartition s')).
intros.
unfold s'.
eapply  getPartitionsAddIndirection;trivial;try eassumption;trivial.
rewrite <- Hpart in *.
trivial.
split;trivial.
split.
apply isVAMapMMUPage with entry;trivial.
destruct Hi3 as (pp & Hpp & Hnotdef).
exists pp;split;trivial.
apply nextEntryIsPPMapMMUPage with entry;trivial.
Qed.

Lemma wellFormedRootDataStructAddIndirection  indirection idx s  phyMMUaddr x   e r w level partition (va:vaddr) pd entry idxroot stop indirection0: 
  let s':=  {|
      currentPartition := currentPartition s;
      memory := add indirection x
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyMMUaddr |}) (memory s) pageEq idxEq |} in
  lookup indirection x (memory s) pageEq idxEq =
          Some (PE entry) -> 
  Some level = StateLib.getNbLevel ->
   
  In partition (getPartitions pageRootPartition s) ->
  nextEntryIsPP partition idxroot pd s -> 
  dataStructurePdSh1Sh2asRoot idxroot s -> 
getIndirection pd va level stop s = Some indirection0 ->
indirection <> pageDefault -> 
PCWellFormedRootDataStruct stop level indirection0 idx s' idxroot.
Proof.
intros * Hlook Hnblgen Hpart0 Hpp Hgoal Hind1 (* Hmid *) Hindnotdef.
unfold PCWellFormedRootDataStruct. 
assert (Hdef: indirection0 = pageDefault \/ indirection0 <> pageDefault ) by apply pageDecOrNot.
destruct Hdef.
left;trivial.
right.
(* 
assert(Hind: getIndirection pd va level  stop s = Some indirection0 ).
apply getIndirectionMiddle2 with  n indirection;trivial.
lia.
rewrite <- Hmid.
f_equal.
lia . *)

assert(Ht: True) by trivial.
  generalize(Hgoal partition Hpart0  pd Hpp va Ht level stop Hnblgen indirection0 idx Hind1 );
  clear Hgoal;intros Hgoal.
  simpl in *.
  destruct Hgoal as [Hgoal|Hgoal].
  now contradict Hgoal.
        destruct Hgoal as (Hgoal & Hx).
        split;trivial.
        destruct Hgoal as [Hgoal|Hgoal].
        left;intuition.
        apply isPEMapMMUPage with entry;trivial.
        right.
        destruct Hgoal as (Hx1 &Hgoal).
        split;trivial.
         destruct Hgoal as [Hgoal|Hgoal].
        left;intuition.
        apply isVEMapMMUPage with entry;trivial.
        right.
         destruct Hgoal as [Hgoal|Hgoal].
        left;intuition.
        apply isVAMapMMUPage with entry;trivial.
        right;intuition.
        apply isPEMapMMUPage with entry;trivial.
        (*
  assert(Hind:  Some indirection = Some indirection ) by trivial.
  apply Hgoal in Hind;clear Hgoal.
  destruct Hind as [Hind|Hind].
  left;trivial.
  right.
  destruct Hind as (Hind & Hii).
  split;trivial.
  destruct Hind as [Hind|Hind].
  left. 
  intuition.
  apply isPEMapMMUPage with entry;trivial.
  right.
  intuition;trivial.
  left;split;trivial.
  apply isVEMapMMUPage with entry;trivial.
  right;left;split;trivial.
  apply isVAMapMMUPage with entry;trivial.
  right;right;split;trivial.
  apply isPEMapMMUPage with entry;trivial. *)
 Qed. 

(* Lemma wellFormedRootDataStructAddIndirection  indirection idx s  phyMMUaddr x m  e r w level partition (va:vaddr) pd entry idxroot n indirection0: 
  let s':=  {|
      currentPartition := currentPartition s;
      memory := add indirection x
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyMMUaddr |}) (memory s) beqPage beqIndex |} in
  lookup indirection x (memory s) beqPage beqIndex =
          Some (PE entry) -> 
  Some level = StateLib.getNbLevel ->
   
  In partition (getPartitions multiplexer s) ->
  nextEntryIsPP partition idxroot pd s -> 
  dataStructurePdSh1Sh2asRoot idxroot s -> 
getIndirection pd va level n s = Some indirection ->
getIndirection indirection va (CLevel (level -n))  m s = Some indirection0 ->
indirection <> defaultPage -> 
PCWellFormedRootDataStruct (n+m) level indirection0 idx s' idxroot.
Proof.
intros * Hlook Hnblgen Hpart0 Hpp Hgoal Hind1 Hmid Hindnotdef.
unfold PCWellFormedRootDataStruct. 
assert (Hdef: indirection0 = defaultPage \/ indirection0 <> defaultPage ) by apply pageDecOrNot.
destruct Hdef.
left;trivial.
right.

assert(Hind: getIndirection pd va level  (n+m) s = Some indirection0 ).
apply getIndirectionMiddle2 with  n indirection;trivial.
lia.
rewrite <- Hmid.
f_equal.
lia .

assert(Ht: True) by trivial.
  generalize(Hgoal partition Hpart0  pd Hpp va Ht level (n+m) Hnblgen indirection0 idx Hind );
  clear Hgoal;intros Hgoal.
  simpl in *.
  destruct Hgoal as [Hgoal|Hgoal].
  now contradict Hgoal.
        destruct Hgoal as (Hgoal & Hx).
        split;trivial.
        destruct Hgoal as [Hgoal|Hgoal].
        left;intuition.
        apply isPEMapMMUPage with entry;trivial.
        right.
        destruct Hgoal as (Hx1 &Hgoal).
        split;trivial.
         destruct Hgoal as [Hgoal|Hgoal].
        left;intuition.
        apply isVEMapMMUPage with entry;trivial.
        right.
         destruct Hgoal as [Hgoal|Hgoal].
        left;intuition.
        apply isVAMapMMUPage with entry;trivial.
        right;intuition.
        apply isPEMapMMUPage with entry;trivial.
        (*
  assert(Hind:  Some indirection = Some indirection ) by trivial.
  apply Hgoal in Hind;clear Hgoal.
  destruct Hind as [Hind|Hind].
  left;trivial.
  right.
  destruct Hind as (Hind & Hii).
  split;trivial.
  destruct Hind as [Hind|Hind].
  left. 
  intuition.
  apply isPEMapMMUPage with entry;trivial.
  right.
  intuition;trivial.
  left;split;trivial.
  apply isVEMapMMUPage with entry;trivial.
  right;left;split;trivial.
  apply isVAMapMMUPage with entry;trivial.
  right;right;split;trivial.
  apply isPEMapMMUPage with entry;trivial. *)
 Qed. *)
Lemma wellFormedMMUAddIndirection n indirection idx s  phyMMUaddr m  e r w level  entry : 
  let s':=  {|
      currentPartition := currentPartition s;
      memory := add indirection m
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyMMUaddr |}) (memory s) pageEq idxEq |} in
isWellFormedMMUTables phyMMUaddr s ->
   lookup indirection m (memory s) pageEq idxEq =
          Some (PE entry) -> 
(pageDefault =? phyMMUaddr) = false ->  
PCWellFormedRootDataStruct n level phyMMUaddr idx s' idxPageDir.
Proof.
intros * Hwellmmu Hlook Hnotdef.
intros.
right.
split. 
--- assert(Horl:n < level \/ n >= level) by lia.
destruct Horl.
left;split;trivial.
 apply isPEMapMMUPage with entry ;trivial.
 move Hwellmmu at bottom.
 unfold isWellFormedMMUTables in *.
 destruct Hwellmmu with idx as (Hi & _).
 unfold  StateLib.readPhyEntry, isPE in *.
 destruct (lookup phyMMUaddr idx (memory s) pageEq idxEq);try now contradict Hi.
 destruct v;try now contradict Hi.
 trivial.
right;split;trivial.
 right;right;split;trivial.
 apply isPEMapMMUPage with entry ;trivial.
 move Hwellmmu at bottom.
 unfold isWellFormedMMUTables in *.
 destruct Hwellmmu with idx as (Hi & _).
 unfold  StateLib.readPhyEntry, isPE in *.
 destruct (lookup phyMMUaddr idx (memory s) pageEq idxEq);try now contradict Hi.
 destruct v;try now contradict Hi.
 trivial.
--- apply beq_nat_false in Hnotdef. intuition.
   subst.
   apply Hnotdef;trivial.
Qed.

Lemma getIndirectionEqAddIndirectionIndirectionIsRoot p va l0 stop s phyMMUaddr e r w vaToPrepare l indirection entry partition :
let s' := {|
currentPartition := currentPartition s;
memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
      (PE
         {|
         read := r;
         write := w;
         exec := e;
         present := true;
         user := true;
         pa := phyMMUaddr |}) (memory s) pageEq idxEq |} in 
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq =
Some (PE entry) ->
false = levelEq l levelMin ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l) (memory s) = Some p ->
(pageDefault =? p) = false -> 
StateLib.Level.pred l = Some l0 ->
nextEntryIsPP partition idxPageDir indirection s -> 
Some l = StateLib.getNbLevel ->
indirection <> pageDefault->
NoDup (getIndirectionsAux indirection s nbLevel) -> 
getIndirection p va l0 stop s' = getIndirection p va l0 stop s.
Proof.
intros * Hlook Hnotfst Hnextind Hdef Hl Hpp Hnbl Hrootnotdef Hdup .
intros.
symmetry. 
apply getIndirectionMapMMUPage11 with entry;trivial.
(*********)
intros * Hi1 Hi2.
assert(Horstop : S(stop0+1) <= nbLevel \/ S(stop0+1) > nbLevel) by lia.
destruct Horstop as [Horstop|Horstop].
- assert(Hin:  In indirection (getIndirectionsAux indirection s (stop0+1) )).
  { replace (stop0+1) with (S stop0) by lia.
  simpl. left;trivial. }
  assert(~ In tbl (getIndirectionsAux indirection s (stop0+1) )).
{ apply getIndirectionInGetIndirections2' with va l;trivial. lia.
replace (stop0+1) with (S stop0) by lia.
simpl.
rewrite <- Hnotfst.
rewrite Hnextind.
rewrite Hdef.
rewrite Hl;trivial.
apply noDupPreviousMMULevels with nbLevel;trivial.
lia.

apply beq_nat_falseNot;trivial.
assert(Hlvlx: nbLevel - 1  = l).

{
apply getNbLevelEq in Hnbl.
subst.
rewrite <- nbLevelEq;trivial. }
lia.
lia. }

unfold not;intros;subst; now contradict Hin.

- assert( getIndirection p va l0 (nbLevel -1 -1) s = Some tbl).
assert(Hlvlx: nbLevel - 1  = l).

{
apply getNbLevelEq in Hnbl.
subst.
rewrite <- nbLevelEq;trivial. }
pose proof Hl as Hpred'.
apply levelPredMinus1 in Hl.
apply getIndirectionStopLevelGT2 with (stop0);trivial.
unfold CLevel in Hl.
case_eq(lt_dec (l - 1) nbLevel);intros * Hll;rewrite Hll in *.
subst.
simpl in *.
pose proof nbLevelNotZero as Hx.
subst.
rewrite <- Hlvlx.
assert(Hlnot0: l > 0).
apply levelEqBEqNatFalse0;trivial.
symmetry;trivial.
lia.
assert(Hlnot0: l > 0).
apply levelEqBEqNatFalse0;trivial.
symmetry;trivial.

lia.

unfold CLevel in Hl.
case_eq(lt_dec (l - 1) nbLevel);intros * Hll;rewrite Hll in *.
subst.
simpl in *.
assert(Hlnot0: l > 0).
apply levelEqBEqNatFalse0;trivial.
symmetry;trivial.
lia.
assert(Hlnot0: l > 0).
apply levelEqBEqNatFalse0;trivial.
symmetry;trivial.
lia.
symmetry;trivial.

assert(Hll: l = CLevel (nbLevel - 1)).
apply getNbLevelEq;trivial.
pose proof nbLevelEq as Heq.
rewrite <- Hll in Heq.
assert(Ll: l> 0).
apply levelEqBEqNatFalse0;trivial.
symmetry;trivial.
assert(Hin:  In indirection (getIndirectionsAux indirection s (nbLevel-1) )).
{ destruct (nbLevel-1);simpl.
subst;lia. left;trivial.  }

assert(~ In tbl (getIndirectionsAux indirection s (nbLevel-1) )).

{ pose proof nbLevelNotZero.
apply getIndirectionInGetIndirections2' with va l;trivial.
lia.


destruct (nbLevel-1);simpl.
subst;lia.
rewrite <- Hnotfst.
rewrite Hnextind.
rewrite Hdef.
rewrite Hl.

replace (S n- 1) with n in * by lia.
trivial.

unfold getIndirections in *.
replace  (nbLevel - 1 + 1) with nbLevel by lia.
trivial.
assert(Htruex:  (pageDefault =? tbl) = false) by trivial.
apply beq_nat_false in Htruex.
unfold not;intros;subst;try now contradict Htruex.
apply beq_nat_false in Hi2.
unfold not;intros;subst.

lia. lia. }
unfold not;intros ;subst;now contradict Hin.
- apply beq_nat_false in Hdef.
unfold not;intros;subst;try now contradict Hdef.
Qed.

Lemma getIndirectionEqAddIndirectionIndirectionIsRoot' p va l0 stop s phyMMUaddr e r w (* vaToPrepare *) 
l indirection entry partition m idxroot:
let s' := {|
currentPartition := currentPartition s;
memory := add indirection m
      (PE
         {|
         read := r;
         write := w;
         exec := e;
         present := true;
         user := true;
         pa := phyMMUaddr |}) (memory s) pageEq idxEq |} in 
lookup indirection m (memory s) pageEq idxEq =
Some (PE entry) ->
false = levelEq l levelMin ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l) (memory s) = Some p ->
(pageDefault =? p) = false -> 
StateLib.Level.pred l = Some l0 ->
nextEntryIsPP partition idxroot indirection s -> 
Some l = StateLib.getNbLevel ->
indirection <> pageDefault->
NoDup (getIndirectionsAux indirection s nbLevel) -> 
getIndirection p va l0 stop s' = getIndirection p va l0 stop s.
Proof.
intros * Hlook Hnotfst Hnextind Hdef Hl Hpp Hnbl Hrootnotdef Hdup.
symmetry. 
apply getIndirectionMapMMUPage11 with entry;trivial.
(*********)
intros * Hi1 Hi2.
assert(Horstop : S(stop0+1) <= nbLevel \/ S(stop0+1) > nbLevel) by lia.
destruct Horstop as [Horstop|Horstop].
- assert(Hin:  In indirection (getIndirectionsAux indirection s (stop0+1) )).
  { replace (stop0+1) with (S stop0) by lia.
  simpl. left;trivial. }
  assert(~ In tbl (getIndirectionsAux indirection s (stop0+1) )).
{ apply getIndirectionInGetIndirections2' with va l;trivial. lia.
replace (stop0+1) with (S stop0) by lia.
simpl.
rewrite <- Hnotfst.
rewrite Hnextind.
rewrite Hdef.
rewrite Hl;trivial.
apply noDupPreviousMMULevels with nbLevel;trivial.


lia.

apply beq_nat_falseNot;trivial.
assert(Hlvlx: nbLevel - 1  = l).

{
apply getNbLevelEq in Hnbl.
subst.
rewrite <- nbLevelEq;trivial. }
lia.
lia. }

unfold not;intros;subst; now contradict Hin.

- assert( getIndirection p va l0 (nbLevel -1 -1) s = Some tbl).
assert(Hlvlx: nbLevel - 1  = l).

{
apply getNbLevelEq in Hnbl.
subst.
rewrite <- nbLevelEq;trivial. }
pose proof Hl as Hpred'.
apply levelPredMinus1 in Hl.
apply getIndirectionStopLevelGT2 with (stop0);trivial.
unfold CLevel in Hl.
case_eq(lt_dec (l - 1) nbLevel);intros * Hll;rewrite Hll in *.
subst.
simpl in *.
pose proof nbLevelNotZero as Hx.
subst.
rewrite <- Hlvlx.
assert(Hlnot0: l > 0).
apply levelEqBEqNatFalse0;trivial.
symmetry;trivial.
lia.
assert(Hlnot0: l > 0).
apply levelEqBEqNatFalse0;trivial.
symmetry;trivial.

lia.

unfold CLevel in Hl.
case_eq(lt_dec (l - 1) nbLevel);intros * Hll;rewrite Hll in *.
subst.
simpl in *.
assert(Hlnot0: l > 0).
apply levelEqBEqNatFalse0;trivial.
symmetry;trivial.
lia.
assert(Hlnot0: l > 0).
apply levelEqBEqNatFalse0;trivial.
symmetry;trivial.
lia.
symmetry;trivial.

assert(Hll: l = CLevel (nbLevel - 1)).
apply getNbLevelEq;trivial.
pose proof nbLevelEq as Heq.
rewrite <- Hll in Heq.
assert(Ll: l> 0).
apply levelEqBEqNatFalse0;trivial.
symmetry;trivial.
assert(Hin:  In indirection (getIndirectionsAux indirection s (nbLevel-1) )).
{ destruct (nbLevel-1);simpl.
subst;lia. left;trivial.  }

assert(~ In tbl (getIndirectionsAux indirection s (nbLevel-1) )).

{ pose proof nbLevelNotZero.
apply getIndirectionInGetIndirections2' with va l;trivial.
lia.


destruct (nbLevel-1);simpl.
subst;lia.
rewrite <- Hnotfst.
rewrite Hnextind.
rewrite Hdef.
rewrite Hl.

replace (S n- 1) with n in * by lia.
trivial.

unfold getIndirections in *.
replace  (nbLevel - 1 + 1) with nbLevel by lia.
trivial.
assert(Htruex:  (pageDefault =? tbl) = false) by trivial.
apply beq_nat_false in Htruex.
unfold not;intros;subst;try now contradict Htruex.
apply beq_nat_false in Hi2.
unfold not;intros;subst.

lia. lia. }
unfold not;intros ;subst;now contradict Hin.
- apply beq_nat_false in Hdef.
unfold not;intros;subst;try now contradict Hdef.
Qed.


Lemma PCWellFormedDataStructAddIndirection stop  indirection0 idx s phyMMUaddr e r w  m
(* vaToPrepare *) l  va indirection entry partition lpred: 
let s' := {|
currentPartition := currentPartition s;
memory := add indirection m
            (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |}) 
            (memory s) pageEq idxEq |} in 
getIndirection indirection va l stop s' = Some indirection0 -> 
lookup indirection m (memory s) pageEq idxEq =
    Some (PE entry) ->
In partition (getPartitions pageRootPartition s) ->
nextEntryIsPP partition idxPageDir indirection s ->
Some l = StateLib.getNbLevel ->
false = levelEq l levelMin ->
StateLib.Level.pred l = Some lpred -> 
(pageDefault =? phyMMUaddr) = false ->
dataStructurePdSh1Sh2asRoot idxPageDir s ->
isWellFormedMMUTables phyMMUaddr s ->
phyMMUaddr <> indirection ->
indirection <> pageDefault ->
NoDup (getIndirectionsAux indirection s nbLevel) -> 
PCWellFormedRootDataStruct stop l indirection0 idx s' idxPageDir.
Proof.
intros * Hind Hlook Hpart0 Hpp Hnbl Hnotfst Hlpred Hdup.
intros.
(* 
assert(Hvaddr: StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare va l = true \/
  StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare va l = false)
  by (destruct (StateLib.checkVAddrsEqualityWOOffset);[left|right];trivial).
 destruct Hvaddr as [Hvaddr|Hvaddr].
 --  *) destruct stop.
    ** simpl in *.
       inversion Hind.
       subst indirection0.
        eapply wellFormedRootDataStructAddIndirection with partition va indirection entry  ;trivial.
    ** simpl in *.
       rewrite <- Hnotfst in Hind.
        assert(Hor : m = (StateLib.getIndexOfAddr va l) \/ m <> (StateLib.getIndexOfAddr va l)) by apply indexDecOrNot.  
       destruct Hor as [Hor | Hor].
       ++ subst. 

       assert(Hnewind:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
             (add indirection (StateLib.getIndexOfAddr va l)
                (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |}) (memory s) pageEq idxEq) =
                Some phyMMUaddr). 
       { apply readPhyEntryAddIndirectionSameTable. }  
       rewrite Hnewind in Hind.
       assert(Hnotdef: (pageDefault =? phyMMUaddr) = false) by trivial.
       rewrite Hnotdef in Hind.
       rewrite Hlpred in Hind.
       destruct stop; simpl in *.
       +++ inversion Hind;subst indirection0.
           apply wellFormedMMUAddIndirection with entry;trivial.
       +++ case_eq(levelEq lpred levelMin);intros * Hlpred0;rewrite Hlpred0 in *. 
         --- inversion Hind;subst indirection0.
             apply wellFormedMMUAddIndirection with entry;trivial.      
         --- assert(Hreadnext: StateLib.readPhyEntry phyMMUaddr (StateLib.getIndexOfAddr va lpred)
             (add indirection (StateLib.getIndexOfAddr va l)
                (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |}) 
                (memory s) pageEq idxEq) = Some pageDefault).
              { assert(Hwell':  isWellFormedMMUTables phyMMUaddr s').
                apply isWellFormedMMUTablesAddIndirection with entry;trivial.
                unfold isWellFormedMMUTables in Hwell'.
                generalize (Hwell' (StateLib.getIndexOfAddr va lpred))  ; clear Hwell'; intros .
                intuition.  }
              rewrite Hreadnext in *.
              rewrite <- beq_nat_refl in Hind.
              inversion Hind;subst.
              left;trivial.
      ++ assert(Hreadeq: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
           (add indirection m
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |}) 
              (memory s) pageEq idxEq) =
              StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
          (memory s)). {
          symmetry. apply readPhyEntryMapMMUPage with entry;trivial.
          right;trivial.
          intuition. }
          rewrite Hreadeq in Hind.
     (*      apply wellFormedRootDataStructAddIndirection with partition va indirection entry;trivial.
          simpl.
          rewrite <- Hnotfst. *)
          case_eq(StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l) (memory s));intros * Hnextind;
          rewrite Hnextind in *;try now contradict Hind.
          case_eq(pageDefault =? p);intros * Hdef; rewrite Hdef in *;try now contradict Hind.
          -- inversion Hind;subst.
             unfold PCWellFormedRootDataStruct.
             left;trivial.
          --
          trivial.
          case_eq(StateLib.Level.pred l );intros * Hl; rewrite Hl in *;try now contradict Hind.
          assert(Hindeq: getIndirection p va l0 stop s' = getIndirection p va l0 stop s).
          { apply getIndirectionEqAddIndirectionIndirectionIsRoot' with l entry
          partition idxPageDir;trivial. }
          rewrite Hindeq in Hind.
          assert(Hi: getIndirection indirection va l (S stop) s = Some indirection0). 
          simpl. 
          rewrite <- Hnotfst.
          rewrite Hnextind.
          rewrite Hdef.
          rewrite Hl.
          trivial.
          trivial. 
       eapply wellFormedRootDataStructAddIndirection with partition va indirection entry  ;trivial.
Qed.

 Set Nested Proofs Allowed.      
       Lemma wellFormedSh1AddIndirection  l indirection0 vaToPrepare  m va stop indirection idx s  phySh1addr   e r w level  entry lpred : 
  let s':=  {|
      currentPartition := currentPartition s;
      memory := add indirection (StateLib.getIndexOfAddr vaToPrepare m)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phySh1addr |}) (memory s) pageEq idxEq |} in
phySh1addr <> indirection -> 
isWellFormedFstShadow lpred phySh1addr s ->
   lookup indirection (StateLib.getIndexOfAddr vaToPrepare m) (memory s) pageEq idxEq =
          Some (PE entry) -> 
(pageDefault =? phySh1addr) = false ->  
false = levelEq level levelMin ->
StateLib.Level.pred level = Some lpred ->
 StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
            (add indirection (StateLib.getIndexOfAddr va l)
               (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |}) (memory s) pageEq idxEq) =
          Some phySh1addr -> 
getIndirection phySh1addr va lpred stop s' = Some indirection0->
PCWellFormedRootDataStruct (S stop) level indirection0 idx s' idxShadow1.
Proof.
intros * Hdiffnew Hwellmmu Hlook Hnotdef Hfst Hlpred Hread Hind.
intros.
assert(Hind0def: indirection0= pageDefault \/ indirection0<>pageDefault) by apply pageDecOrNot.
destruct Hind0def as[Hind0def|Hind0def]. 
left;trivial.
right.
split;trivial.
assert(Hwell': isWellFormedFstShadow lpred phySh1addr s').
{  apply isWellFormedFstShadowTablesAddIndirection with entry;trivial. }
unfold isWellFormedFstShadow in Hwellmmu.
destruct stop;simpl in *.
- inversion Hind;subst indirection0.
  assert ( 1 < level \/ 1 >= level) by lia.
  destruct H.
  + left.
    split. trivial.
    destruct Hwellmmu as [(Hip &Hwellmmu) |(Hip &Hwellmmu)].
    apply isPEMapMMUPage with entry ;trivial.
    move Hwellmmu at bottom.
    destruct Hwellmmu with idx as (Hi & _).
    unfold  StateLib.readPhyEntry, isPE in *.
    destruct (lookup phySh1addr idx (memory s) pageEq idxEq);try now contradict Hi.
    destruct v;try now contradict Hi.
    trivial.
    subst.
    symmetry in Hfst.
    apply levelPredMinus1Nat in Hlpred;trivial.
    unfold levelMin in Hlpred.
    rewrite <- CLevelIdentity2 in Hlpred.
    subst.
    lia.
    apply nbLevelNotZero.
  + right.
    split;trivial.
    left.
    split;trivial.
    assert( lpred = levelMin).
    { symmetry in Hfst.
    apply levelPredMinus1Nat in Hlpred;trivial.
    unfold levelMin .
    symmetry.
    assert (0 = lpred).
    lia.
    rewrite H0.
    apply CLevelIdentity1. }
    destruct Hwellmmu as [(Hip &Hwellmmu) |(Hip &Hwellmmu)].
    now contradict Hip.
    apply isVEMapMMUPage with entry ;trivial.
    move Hwellmmu at bottom.
    destruct Hwellmmu with idx as (Hi & _).
    unfold  StateLib.readVirEntry, isVE in *.
    destruct (lookup phySh1addr idx (memory s) pageEq idxEq);try now contradict Hi.
    destruct v;try now contradict Hi.
    trivial.
- assert ( S (S stop)  < level \/ S (S stop) >= level) by lia.
  destruct H.
  + destruct Hwellmmu as [(Hip &Hwellmmu) |(Hip &Hwellmmu)].
    * left.
      split. trivial.
      assert(Hf: levelEq lpred levelMin = false) .
      { rewrite <- not_true_iff_false.
        contradict Hip.
        apply levelEqBEqNatTrue in Hip;trivial. }
      rewrite Hf in *. 
      assert(Hreadnext:  StateLib.readPhyEntry phySh1addr (StateLib.getIndexOfAddr va lpred)
               (add indirection (StateLib.getIndexOfAddr vaToPrepare m) (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |}) 
                  (memory s) pageEq idxEq) = Some pageDefault).
      { unfold isWellFormedFstShadow in *.
        destruct Hwell' as [Hwell'|Hwell'].
        destruct Hwell' as (_ & Hwell').
        destruct Hwell' with (StateLib.getIndexOfAddr va lpred) as ( Hi & _ ).
        trivial.
        destruct Hwell' as (hFALSE & _).
        subst. now contradict Hip.
        }
      rewrite Hreadnext in Hind.
      rewrite <- beq_nat_refl in Hind.              
      apply isPEMapMMUPage with entry ;trivial.
      inversion Hind. subst.
      now contradict Hind0def.
    * subst.
      clear Hind.
      contradict Hlpred.
      unfold not;intros Hfalse.
      symmetry in Hfst.
      eapply levelPredMinus1Nat with (l':= levelMin) in Hfst.
      unfold levelMin in Hfst.
      rewrite <- CLevelIdentity2 in Hfst.
      lia.
      apply nbLevelNotZero;trivial.
      trivial.
  + destruct Hwellmmu as [(Hip &Hwellmmu) |(Hip &Hwellmmu)].
    * right. 
      split. trivial.
      left. 
      split;trivial.
      assert(Hf: levelEq lpred levelMin = false) . 
      { move Hip at bottom.
      unfold levelEq.
      apply Nat.eqb_neq.
      destruct levelMin; destruct lpred;simpl in *.
      simpl in *.
      contradict Hip.
      subst.
      f_equal.
      apply proof_irrelevance. }      
      
      rewrite Hf in *.
           assert(Hreadnext:  StateLib.readPhyEntry phySh1addr (StateLib.getIndexOfAddr va lpred)
               (add indirection (StateLib.getIndexOfAddr vaToPrepare m) (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |}) 
                  (memory s) pageEq idxEq) = Some pageDefault).
      { unfold isWellFormedFstShadow in *.
        destruct Hwell' as [Hwell'|Hwell'].
        destruct Hwell' as (_ & Hwell').
        destruct Hwell' with (StateLib.getIndexOfAddr va lpred) as ( Hi & _ ).
        trivial.
        destruct Hwell' as (hFALSE & _).
        subst. now contradict Hip.
        }
      rewrite Hreadnext in Hind.
      rewrite <- beq_nat_refl in Hind.
      inversion Hind. subst.
      now contradict Hind0def.
    * right.
      split;trivial.
      left;split;trivial.
      assert(Hf: levelEq lpred levelMin = true).
      subst.
      unfold  levelEq.
      rewrite <- beq_nat_refl;trivial.
      rewrite Hf in *.
      inversion Hind;subst indirection0.
      apply isVEMapMMUPage with entry ;trivial.
      move Hwellmmu at bottom.
      destruct Hwellmmu with idx as (Hi & _).
      unfold  StateLib.readVirEntry, isVE in *.
      destruct (lookup phySh1addr idx (memory s) pageEq idxEq);try now contradict Hi.
      destruct v;try now contradict Hi.
      trivial.
 
Qed. 

Lemma wellFormedSh2AddIndirection  l indirection0 vaToPrepare  m va stop indirection idx s  phySh2addr   e r w level  entry lpred : 
  let s':=  {|
      currentPartition := currentPartition s;
      memory := add indirection (StateLib.getIndexOfAddr vaToPrepare m)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phySh2addr |}) (memory s) pageEq idxEq |} in
phySh2addr <> indirection -> 
isWellFormedSndShadow lpred phySh2addr s ->
   lookup indirection (StateLib.getIndexOfAddr vaToPrepare m) (memory s) pageEq idxEq =
          Some (PE entry) -> 
(pageDefault =? phySh2addr) = false ->  
false = levelEq level levelMin ->
StateLib.Level.pred level = Some lpred ->
 StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
            (add indirection (StateLib.getIndexOfAddr va l)
               (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh2addr |}) (memory s) pageEq idxEq) =
          Some phySh2addr -> 
getIndirection phySh2addr va lpred stop s' = Some indirection0->
PCWellFormedRootDataStruct (S stop) level indirection0 idx s' idxShadow2.
Proof.
intros * Hdiffnew Hwellmmu Hlook Hnotdef Hfst Hlpred Hread Hind.
intros.
assert(Hind0def: indirection0= pageDefault \/ indirection0<>pageDefault) by apply pageDecOrNot.
destruct Hind0def as[Hind0def|Hind0def]. 
left;trivial.
right.
split;trivial.
assert(Hwell': isWellFormedSndShadow lpred phySh2addr s').
{  apply isWellFormedSndShadowTablesAddIndirection with entry;trivial. }
unfold isWellFormedFstShadow in Hwellmmu.
destruct stop;simpl in *.
- inversion Hind;subst indirection0.
  assert ( 1 < level \/ 1 >= level) by lia.
  destruct H.
  + left.
    split. trivial.
    destruct Hwellmmu as [(Hip &Hwellmmu) |(Hip &Hwellmmu)].
    apply isPEMapMMUPage with entry ;trivial.
    move Hwellmmu at bottom.
    destruct Hwellmmu with idx as (Hi & _).
    unfold  StateLib.readPhyEntry, isPE in *.
    destruct (lookup phySh2addr idx (memory s) pageEq idxEq);try now contradict Hi.
    destruct v;try now contradict Hi.
    trivial.
    subst.
    symmetry in Hfst.
    apply levelPredMinus1Nat in Hlpred;trivial.
    unfold levelMin in Hlpred.
    rewrite <- CLevelIdentity2 in Hlpred.
    subst.
    lia.
    apply nbLevelNotZero.
  + right.
    split;trivial.
    right;left.
    split;trivial.
    assert( lpred = levelMin).
    { symmetry in Hfst.
    apply levelPredMinus1Nat in Hlpred;trivial.
    unfold levelMin .
    symmetry.
    assert (0 = lpred).
    lia.
    rewrite H0.
    apply CLevelIdentity1. }
    destruct Hwellmmu as [(Hip &Hwellmmu) |(Hip &Hwellmmu)].
    now contradict Hip.
    apply isVAMapMMUPage with entry ;trivial.
    move Hwellmmu at bottom.
    generalize (Hwellmmu idx);intros Hi.
    unfold  StateLib.readVirtual, isVA in *.
    destruct (lookup phySh2addr idx (memory s) pageEq idxEq);try now contradict Hi.
    destruct v;try now contradict Hi.
    trivial.
- assert ( S (S stop)  < level \/ S (S stop) >= level) by lia.
  destruct H.
  + destruct Hwellmmu as [(Hip &Hwellmmu) |(Hip &Hwellmmu)].
    * left.
      split. trivial.
      assert(Hf: levelEq lpred levelMin = false) .
      { rewrite <- not_true_iff_false.
        contradict Hip.
        apply levelEqBEqNatTrue in Hip;trivial. }
      rewrite Hf in *. 
      assert(Hreadnext:  StateLib.readPhyEntry phySh2addr (StateLib.getIndexOfAddr va lpred)
               (add indirection (StateLib.getIndexOfAddr vaToPrepare m) (PE {| read := r; 
               write := w; exec := e; present := true; user := true; pa := phySh2addr |}) 
                  (memory s) pageEq idxEq) = Some pageDefault).
      { unfold isWellFormedSndShadow in *.
        destruct Hwell' as [Hwell'|Hwell'].
        destruct Hwell' as (_ & Hwell').
        destruct Hwell' with (StateLib.getIndexOfAddr va lpred) as ( Hi & _ ).
        trivial.
        destruct Hwell' as (hFALSE & _).
        subst. now contradict Hip.
        }
      rewrite Hreadnext in Hind.
      rewrite <- beq_nat_refl in Hind.              
      apply isPEMapMMUPage with entry ;trivial.
      inversion Hind. subst.
      now contradict Hind0def.
    * subst.
      clear Hind.
      contradict Hlpred.
      unfold not;intros Hfalse.
      symmetry in Hfst.
      eapply levelPredMinus1Nat with (l':= levelMin) in Hfst.
      unfold levelMin in Hfst.
      rewrite <- CLevelIdentity2 in Hfst.
      lia.
      apply nbLevelNotZero;trivial.
      trivial.
  + destruct Hwellmmu as [(Hip &Hwellmmu) |(Hip &Hwellmmu)].
    * right. 
      split. trivial.
      right;left. 
      split;trivial.
      assert(Hf: levelEq lpred levelMin = false) . 
      { move Hip at bottom.
      unfold levelEq.
      apply Nat.eqb_neq.
      destruct levelMin; destruct lpred;simpl in *.
      simpl in *.
      contradict Hip.
      subst.
      f_equal.
      apply proof_irrelevance. }      
      
      rewrite Hf in *.
           assert(Hreadnext:  StateLib.readPhyEntry phySh2addr (StateLib.getIndexOfAddr va lpred)
               (add indirection (StateLib.getIndexOfAddr vaToPrepare m) (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh2addr |}) 
                  (memory s) pageEq idxEq) = Some pageDefault).
      { unfold isWellFormedSndShadow in *.
        destruct Hwell' as [Hwell'|Hwell'].
        destruct Hwell' as (_ & Hwell').
        destruct Hwell' with (StateLib.getIndexOfAddr va lpred) as ( Hi & _ ).
        trivial.
        destruct Hwell' as (hFALSE & _).
        subst. now contradict Hip.
        }
      rewrite Hreadnext in Hind.
      rewrite <- beq_nat_refl in Hind.
      inversion Hind. subst.
      now contradict Hind0def.
    * right.
      split;trivial.
      right;left;split;trivial.
      assert(Hf: levelEq lpred levelMin = true).
      subst.
      unfold  levelEq.
      rewrite <- beq_nat_refl;trivial.
      rewrite Hf in *.
      inversion Hind;subst indirection0.
      apply isVAMapMMUPage with entry ;trivial.
      move Hwellmmu at bottom.
      generalize(Hwellmmu idx);intros Hi. 
      unfold  StateLib.readVirtual, isVA in *.
      destruct (lookup phySh2addr idx (memory s) pageEq idxEq);try now contradict Hi.
      destruct v;try now contradict Hi.
      trivial.
Qed. 



Lemma PCWellFormedDataStructAddIndirectionsh1 stop  indirection0 idx s phySh1addr e r w  m
(* vaToPrepare *) l  va indirection entry partition lpred: 
let s' := {|
currentPartition := currentPartition s;
memory := add indirection m
            (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |}) 
            (memory s) pageEq idxEq |} in 
getIndirection indirection va l stop s' = Some indirection0 -> 
lookup indirection m (memory s) pageEq idxEq =
    Some (PE entry) ->
In partition (getPartitions pageRootPartition s) ->
nextEntryIsPP partition idxShadow1 indirection s ->
Some l = StateLib.getNbLevel ->
false = levelEq l levelMin ->
StateLib.Level.pred l = Some lpred -> 
(pageDefault =? phySh1addr) = false ->
dataStructurePdSh1Sh2asRoot idxShadow1 s ->
isWellFormedFstShadow lpred phySh1addr s -> 
phySh1addr <> indirection ->
indirection <> pageDefault ->
NoDup (getIndirectionsAux indirection s nbLevel) -> 
PCWellFormedRootDataStruct stop l indirection0 idx s' idxShadow1.
Proof.
intros * Hind Hlook Hpart0 Hpp Hnbl Hnotfst Hlpred Hdup.
intros.
destruct stop.
** simpl in *.
   inversion Hind.
   subst indirection0.
    eapply wellFormedRootDataStructAddIndirection with partition va indirection entry  ;trivial.
** simpl in *.
   rewrite <- Hnotfst in Hind.
    assert(Hor : m = (StateLib.getIndexOfAddr va l) \/ m <> (StateLib.getIndexOfAddr va l)) by apply indexDecOrNot.  
   destruct Hor as [Hor | Hor].
   ++ subst.
   assert(Hnewind:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
         (add indirection (StateLib.getIndexOfAddr va l)
            (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |}) (memory s) pageEq idxEq) =
            Some phySh1addr). 
   { apply readPhyEntryAddIndirectionSameTable. }  
   rewrite Hnewind in Hind.
   assert(Hnotdef: (pageDefault =? phySh1addr) = false) by trivial.
   rewrite Hnotdef in Hind.
   rewrite Hlpred in Hind.
   unfold PCWellFormedRootDataStruct.
   unfold dataStructurePdSh1Sh2asRoot in *.
   clear H.
   apply wellFormedSh1AddIndirection with l va entry lpred;trivial.
   ++ assert(Hreadeq: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
       (add indirection m
          (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |}) 
          (memory s) pageEq idxEq) =
          StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
      (memory s)). {
      symmetry. apply readPhyEntryMapMMUPage with entry;trivial.
      right;trivial.
      intuition. }
      rewrite Hreadeq in Hind.
      case_eq(StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l) (memory s));intros * Hnextind;
      rewrite Hnextind in *;try now contradict Hind.
      case_eq(pageDefault =? p);intros * Hdef; rewrite Hdef in *;try now contradict Hind.
      -- inversion Hind;subst.
         unfold PCWellFormedRootDataStruct.
         left;trivial.
      --
      trivial.
      case_eq(StateLib.Level.pred l );intros * Hl; rewrite Hl in *;try now contradict Hind.
      assert(Hindeq: getIndirection p va l0 stop s' = getIndirection p va l0 stop s).
      { apply getIndirectionEqAddIndirectionIndirectionIsRoot' with l entry
      partition idxShadow1;trivial. }
      rewrite Hindeq in Hind.
      assert(Hi: getIndirection indirection va l (S stop) s = Some indirection0). 
      simpl. 
      rewrite <- Hnotfst.
      rewrite Hnextind.
      rewrite Hdef.
      rewrite Hl.
      trivial.
      trivial. 
   eapply wellFormedRootDataStructAddIndirection with partition va indirection entry  ;trivial.
Qed.

Lemma PCWellFormedDataStructAddIndirectionsh2 stop  indirection0 idx s phySh2addr e r w  m
(* vaToPrepare *) l  va indirection entry partition lpred: 
let s' := {|
currentPartition := currentPartition s;
memory := add indirection m
            (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh2addr |}) 
            (memory s) pageEq idxEq |} in 
getIndirection indirection va l stop s' = Some indirection0 -> 
lookup indirection m (memory s) pageEq idxEq =
    Some (PE entry) ->
In partition (getPartitions pageRootPartition s) ->
nextEntryIsPP partition idxShadow2 indirection s ->
Some l = StateLib.getNbLevel ->
false = levelEq l levelMin ->
StateLib.Level.pred l = Some lpred -> 
(pageDefault =? phySh2addr) = false ->
dataStructurePdSh1Sh2asRoot idxShadow2 s ->
isWellFormedSndShadow lpred phySh2addr s -> 
phySh2addr <> indirection ->
indirection <> pageDefault ->
NoDup (getIndirectionsAux indirection s nbLevel) -> 
PCWellFormedRootDataStruct stop l indirection0 idx s' idxShadow2.
Proof.
intros * Hind Hlook Hpart0 Hpp Hnbl Hnotfst Hlpred Hdup.
intros.
destruct stop.
** simpl in *.
   inversion Hind.
   subst indirection0.
    eapply wellFormedRootDataStructAddIndirection with partition va indirection entry  ;trivial.
** simpl in *.
   rewrite <- Hnotfst in Hind.
    assert(Hor : m = (StateLib.getIndexOfAddr va l) \/ m <> (StateLib.getIndexOfAddr va l)) by apply indexDecOrNot.  
   destruct Hor as [Hor | Hor].
   ++ subst.
   assert(Hnewind:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
         (add indirection (StateLib.getIndexOfAddr va l)
            (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh2addr |}) (memory s) pageEq idxEq) =
            Some phySh2addr). 
   { apply readPhyEntryAddIndirectionSameTable. }  
   rewrite Hnewind in Hind.
   assert(Hnotdef: (pageDefault =? phySh2addr) = false) by trivial.
   rewrite Hnotdef in Hind.
   rewrite Hlpred in Hind.
   unfold PCWellFormedRootDataStruct.
   unfold dataStructurePdSh1Sh2asRoot in *.
   clear H.
   apply wellFormedSh2AddIndirection with l va entry lpred;trivial.
   ++ assert(Hreadeq: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
       (add indirection m
          (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh2addr |}) 
          (memory s) pageEq idxEq) =
          StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
      (memory s)). {
      symmetry. apply readPhyEntryMapMMUPage with entry;trivial.
      right;trivial.
      intuition. }
      rewrite Hreadeq in Hind.
      case_eq(StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l) (memory s));intros * Hnextind;
      rewrite Hnextind in *;try now contradict Hind.
      case_eq(pageDefault =? p);intros * Hdef; rewrite Hdef in *;try now contradict Hind.
      -- inversion Hind;subst.
         unfold PCWellFormedRootDataStruct.
         left;trivial.
      --
      trivial.
      case_eq(StateLib.Level.pred l );intros * Hl; rewrite Hl in *;try now contradict Hind.
      assert(Hindeq: getIndirection p va l0 stop s' = getIndirection p va l0 stop s).
      { apply getIndirectionEqAddIndirectionIndirectionIsRoot' with l entry
      partition idxShadow2;trivial. }
      rewrite Hindeq in Hind.
      assert(Hi: getIndirection indirection va l (S stop) s = Some indirection0). 
      simpl. 
      rewrite <- Hnotfst.
      rewrite Hnextind.
      rewrite Hdef.
      rewrite Hl.
      trivial.
      trivial. 
   eapply wellFormedRootDataStructAddIndirection with partition va indirection entry  ;trivial.
Qed.

Lemma getIndirectionEqAddIndirectionIndirectionIsMiddle indirection s phyMMUaddr e r w vaToPrepare l pd level
               va stop   entry (* partition *)sstop indirection0 :
let s' := {|
currentPartition := currentPartition s;
memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
      (PE
         {|
         read := r;
         write := w;
         exec := e;
         present := true;
         user := true;
         pa := phyMMUaddr |}) (memory s) pageEq idxEq |} in 
NoDup (getIndirectionsAux pd s nbLevel) -> 
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq =
Some (PE entry) ->
indirection <> pageDefault-> 
Some level = StateLib.getNbLevel ->
sstop <= level ->
pd <> pageDefault ->
getIndirection pd vaToPrepare level sstop s = Some indirection ->
sstop > 0 ->
StateLib.checkVAddrsEqualityWOOffset sstop vaToPrepare va level = false ->
stop >= sstop ->
indirection0 <> pageDefault ->
getIndirection pd va level stop s' = Some indirection0 ->
getIndirection pd va level stop s' = getIndirection pd va level stop s.
Proof.
intros * Hdup Hlook Hnotdef Hnblgen Hsstop Hrootnotdef Hind1 Hsstop0 Hstopor Hor Hdefind0 Hind. 
symmetry.
apply getIndirectionMapMMUPage11 with entry;trivial.
intros * Hi1 Hi2.
assert(Hor0 : stop0 < sstop \/ stop0=sstop \/ stop0 > sstop) by lia.
{ destruct Hor0 as [Hor0 | [Hor0 | Hor0]].
  - assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
    { apply getIndirectionInGetIndirections1 with va level;trivial.
      destruct level;simpl in *.
      lia.
      apply beq_nat_false in Hi2.
      unfold not;intros;subst;now contradict Hi2. }
    assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop0+1))).
    apply getIndirectionInGetIndirections2n with sstop vaToPrepare level;trivial.
    destruct level;simpl in *.
    lia.
    apply noDupPreviousMMULevels with nbLevel ;trivial.
    destruct level;simpl in *.
    lia.
    lia.
    unfold not;intros;subst;now contradict Hnotinind.
  - subst stop0.                  
    assert(HsstopS: (S (sstop - 1)) = sstop) by lia.
    eapply pageTablesAreDifferentMiddle with (root1:=pd) (root2:=pd) (s:=s) 
    (va1:= va) (va2:= vaToPrepare) (stop0:= sstop-1) (level1:=level) ;trivial;try rewrite HsstopS;trivial.
    rewrite <- checkVAddrsEqualityWOOffsetPermut';trivial.
    left;split;trivial.
    apply getNbLevelEq;trivial.
    apply beq_nat_false in Hi2.
    unfold not;intros;subst;now contradict Hi2.
  -  pose proof getIndirectionMiddle as Hmid. 
     generalize (Hmid stop pd va level s' indirection0 sstop Hind Hdefind0 Hor);clear Hmid;
     intros Hmid.
     destruct Hmid as (middle & Hmid1 & Hmid2).
    assert(Hx: nbLevel - 1 = level).
    { apply getNbLevelEq in Hnblgen.
      subst.
      rewrite <- nbLevelEq;trivial. }
    assert(Horss: sstop>= nbLevel-1 \/ sstop < nbLevel-1 ) by lia.
    destruct Horss as [Horss|Horss].
    + assert(Hkey: ~In indirection (getIndirectionsAux pd s sstop)).
      {  assert(Hex: sstop + 1 <= nbLevel).
      destruct level;simpl in *.
      lia.
      apply getIndirectionInGetIndirections2' with vaToPrepare level;trivial.
      unfold getIndirections in *.
      apply noDupPreviousMMULevels with nbLevel ;trivial. }
      assert(Heqindx: getIndirection pd va level sstop s' =getIndirection pd va level sstop s). 
      {  apply getIndirectionAddIndirectionEq with entry;trivial. }     
      assert(Hix: getIndirection pd va level (nbLevel - 1)  s = Some middle). 
      { apply getIndirectionStopLevelGe with sstop;trivial.
        lia. rewrite <- Heqindx;trivial. }
      assert(Hkey1: getIndirection pd va level (nbLevel-1) s = Some tbl).
      { apply getIndirectionStopLevelGe with stop0;trivial.
        lia. } 
      rewrite Hkey1 in Hix.
      inversion Hix;subst.
      assert(Hkey2: getIndirection pd vaToPrepare level (nbLevel-1) s = Some indirection). 
      { apply getIndirectionStopLevelGe with sstop;trivial.
        lia. }
      assert(Hid: middle<> indirection).
      { assert(HsstopS: (S (sstop - 1)) = sstop) by lia.
        eapply pageTablesAreDifferentMiddle with (root1:=pd) (root2:=pd) (s:=s) 
        (va1:= va) (va2:= vaToPrepare) (stop0:= sstop-1) (level1:=level) ;trivial;try rewrite HsstopS;trivial.
        rewrite <- checkVAddrsEqualityWOOffsetPermut';trivial.
        left;split;trivial.
        apply getNbLevelEq;trivial.
        apply beq_nat_false in Hi2.
        unfold not;intros;subst;now contradict Hi2.
        rewrite <- Heqindx;trivial. }
      trivial.
    + assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
      destruct Hornbl as [Hornbl | Hornbl].
      * assert(Hinind: In indirection (getIndirectionsAux pd  s (sstop+1))).
        { apply getIndirectionInGetIndirections1 with vaToPrepare level;trivial.
          lia. }
        assert(Hex: sstop + 1 <= nbLevel) by lia.
        assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (sstop+1))).
        { eapply getIndirectionInGetIndirections2n  with (nbLevel -1) va level;trivial;try lia.
          apply getIndirectionStopLevelGe with stop0;trivial.
          lia.
          unfold getIndirections in *.
          apply noDupPreviousMMULevels with nbLevel ;trivial.
          lia.
          apply beq_nat_false in Hi2.
          unfold not;intros;subst;now contradict Hi2. }
        unfold not;intros;subst;now contradict Hnotinind.
      * assert(Hinind: In indirection (getIndirectionsAux pd  s (sstop+1))).
        { apply getIndirectionInGetIndirections1 with vaToPrepare level;trivial.
          lia. }
      assert(Hex: sstop + 1 <= nbLevel) by lia.
      assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (sstop+1))).
      { apply getIndirectionInGetIndirections2n with stop0 va level;trivial;try lia.
        unfold getIndirections in *.
        apply noDupPreviousMMULevels with nbLevel ;trivial.
        lia.
        apply beq_nat_false in Hi2.
        unfold not;intros;subst;now contradict Hi2. }
      unfold not;intros;subst;now contradict Hnotinind. }
Qed. 

Lemma PCWellFormedRootDataStructAddIndirection pd vaToPrepare (level lpred:level) sstop s indirection idx 
va  indirection0 stop phyMMUaddr r w e entry partition:
let s' := {|
currentPartition := currentPartition s;
memory := add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
    (PE
       {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |})
    (memory s) pageEq idxEq |} in 
NoDup (getIndirectionsAux pd s nbLevel) -> 
lookup indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop))) 
  (memory s) pageEq idxEq = Some (PE entry) -> 
isWellFormedMMUTables phyMMUaddr s -> 
dataStructurePdSh1Sh2asRoot idxPageDir s -> 
Some level = StateLib.getNbLevel -> 
In partition (getPartitions pageRootPartition s) ->
getIndirection pd vaToPrepare level sstop s = Some indirection -> 

getIndirection pd va level stop s' = Some indirection0 -> 
stop <= nbLevel - 1 ->
sstop <= level ->
stop >= sstop -> 
sstop > 0 ->
isPE indirection idx s -> 
indirection <> pageDefault -> 
false = levelEq (CLevel (level - sstop)) levelMin -> 
(pageDefault =? phyMMUaddr) = false -> 
StateLib.Level.pred (CLevel (level - sstop)) = Some lpred -> 
nextEntryIsPP partition idxPageDir pd s -> 
indirection0 <> pageDefault ->
pd <> pageDefault -> 
phyMMUaddr <> indirection -> 
PCWellFormedRootDataStruct stop level indirection0 idx s' idxPageDir.
Proof.
intros * Hdup Hlookup Hwellmmu Hgoal Hnblgen Hpart0 Hind1 (* Hmid1 Hmid2 *) Hind Hi Hsstop
  Hor Hsstop0 Hispe Hdefind0 Hnotfst Hnotdefp Hlpred Hpp Hdefind00 Hrootnotdef.
intros.
pose proof getIndirectionMiddle as Hmid. 
generalize (Hmid stop pd va level s' indirection0 sstop Hind Hdefind00 Hor);clear Hmid;
intros Hmid.
destruct Hmid as (middle & Hmid1 & Hmid2).
   assert(Hkey: ~In indirection (getIndirectionsAux pd s sstop)).
{ assert(Hex: sstop + 1 <= nbLevel).
  destruct level;simpl in *.
  lia.
  apply getIndirectionInGetIndirections2' with vaToPrepare level;trivial.
  unfold getIndirections in *.
  apply noDupPreviousMMULevels with nbLevel ;trivial. }
assert(Heqindx: getIndirection pd va level sstop s' =getIndirection pd va level sstop s). 
  {  apply getIndirectionAddIndirectionEq with entry;trivial. }
rewrite Heqindx in Hmid1.
assert(Heqmid: middle = indirection \/  middle <> indirection) by apply pageDecOrNot.
destruct Heqmid as [Heqmid|Heqmid].
- subst.
  assert( Horx: (StateLib.getIndexOfAddr va (CLevel (level - sstop))) =  
  (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))\/ 
  (StateLib.getIndexOfAddr va (CLevel (level - sstop))) <>  
  (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop))) ) by apply indexDecOrNot.
  destruct Horx as [Horx | Horx].
  destruct (stop - sstop) ;simpl in *.
  + inversion Hmid2.
    subst indirection0.
    right.
    split;trivial.
    assert(Horl: stop < level \/ stop >= level) by  lia.                  
    destruct Horl as [Horl | Horl]. 
    left;split;trivial.
    apply isPEMapMMUPage with entry;trivial.
    right.
    split;trivial.
    right;right;split;trivial.
    apply isPEMapMMUPage with entry;trivial.
  + rewrite <- Hnotfst in *.
    assert(Hnewind:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va  (CLevel (level - sstop)))
    (add indirection (StateLib.getIndexOfAddr va  (CLevel (level - sstop)))
    (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |}) (memory s) pageEq idxEq) =
    Some phyMMUaddr). 
    { apply readPhyEntryAddIndirectionSameTable. }
    rewrite Horx in *. 
    rewrite Hnewind in Hmid2.
    rewrite Hnotdefp in Hmid2.
    rewrite Hlpred in Hmid2.
    destruct n; simpl in *.
    * inversion Hmid2;subst indirection0.
      apply wellFormedMMUAddIndirection with entry;trivial.
    * case_eq(levelEq lpred levelMin);intros * Hlpred0;rewrite Hlpred0 in *. 
      inversion Hmid2;subst indirection0.
      apply wellFormedMMUAddIndirection with entry;trivial.
      assert(Hreadnext: StateLib.readPhyEntry phyMMUaddr (StateLib.getIndexOfAddr va lpred)
      (add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
        (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |}) 
        (memory s) pageEq idxEq) = Some pageDefault).
      { assert(Hwell':  isWellFormedMMUTables phyMMUaddr s').
        apply isWellFormedMMUTablesAddIndirection with entry;trivial.
        unfold isWellFormedMMUTables in Hwell'.
        generalize (Hwell' (StateLib.getIndexOfAddr va lpred))  ; clear Hwell'; intros .
        intuition.  }
      rewrite Hreadnext in *.
      clear Hreadnext.
      rewrite <- beq_nat_refl in Hmid2.
      inversion Hmid2;subst.
      left;trivial.
  + apply wellFormedRootDataStructAddIndirection  with partition va pd entry;trivial. 
    apply getIndirectionMiddle2  with sstop indirection;trivial.
    rewrite <- Hmid2.
    clear    Hind1 .
    assert(Hnodup: NoDup (getIndirectionsAux indirection s (stop - sstop))).
    eapply nodupLevelMinusN with sstop pd va level ;trivial.
    replace (sstop + (stop - sstop)) with stop by lia.
    apply noDupPreviousMMULevels with nbLevel;trivial.
    lia.
    lia.
    case_eq (stop - sstop);simpl;intros * Hc;rewrite Hc in *;trivial.
    case_eq(levelEq (CLevel (level - sstop)) levelMin);intros * Hl;trivial.
    assert(Hreadeq: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va (CLevel (level - sstop)))
    (add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
     (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |})
     (memory s) pageEq idxEq) =
     StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va (CLevel (level - sstop)))
     (memory s) ).
     symmetry.
     apply readPhyEntryMapMMUPage with entry;trivial.
     right;trivial.
     rewrite Hreadeq;clear Hreadeq.
    case_eq(StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va (CLevel (level - sstop))) (memory s));intros 
    *  Hre;trivial.
    case_eq (      pageDefault =? p);intros * Hp;trivial.
    case_eq( StateLib.Level.pred (CLevel (level - sstop)) );intros;trivial.
    apply beq_nat_false in Hp.
    assert(p <> pageDefault).
    { unfold not;intros;subst;now contradict Hp. }

    apply getIndirectionMapMMUPage11Stoplt with entry;trivial.
    intros.
    simpl in Hnodup.
    apply NoDup_cons_iff in Hnodup.
    destruct Hnodup as (Hnodup & _).
    rewrite in_flat_map in Hnodup.
    contradict Hnodup.
    exists p.
    split.
    * apply readPhyEntryInGetTablePages with (StateLib.getIndexOfAddr va (CLevel (level - sstop)));
      trivial.
      destruct (StateLib.getIndexOfAddr va (CLevel (level - sstop)));simpl;trivial.
      rewrite <- Hre.
      f_equal.
      apply indexEqId.
    * rewrite <- Hnodup.
      assert(In tbl (getIndirectionsAux p s (stop0+1))).
      apply getIndirectionInGetIndirections1 with va l;trivial.
      lia.
      assert(Hdef: (pageDefault =? tbl) = false) by trivial.
      apply beq_nat_false in Hdef.
      unfold not;intros;subst;now contradict Hdef.
      pose proof inclGetIndirectionsAuxLe as Hproof.
      unfold incl in *.
      apply Hproof with (stop0 + 1);trivial.
      lia.
- apply wellFormedRootDataStructAddIndirection  with partition va pd entry;trivial.
  rewrite <- Hind.
  symmetry.
  apply getIndirectionEqAddIndirectionIndirectionIsMiddle with entry
  sstop indirection0;trivial.
  assert(Hori: StateLib.checkVAddrsEqualityWOOffset sstop vaToPrepare va level = true \/
               StateLib.checkVAddrsEqualityWOOffset sstop vaToPrepare va level = false).
  { destruct ( StateLib.checkVAddrsEqualityWOOffset sstop vaToPrepare va level);simpl.
    left;trivial.
    right;trivial. }
  destruct Hori;trivial.
  assert(Hkey1: getIndirection pd vaToPrepare level sstop s = getIndirection pd va level sstop s).

  apply getIndirectionEqStop;trivial.
  rewrite checkVAddrsEqualityWOOffsetPermut';trivial.
  rewrite Hind1 in Hkey1.
  rewrite Hmid1 in Hkey1.
  inversion Hkey1.
  now contradict Heqmid.
Qed.
 
Lemma dataStructurePdSh1Sh2asRootMMUAddIndirection
s indirection nextIndirection idxroot  entry nbLgen  pd   vaToPrepare partition l lpred r w e
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr :
dataStructurePdSh1Sh2asRoot idxPageDir s->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
nextEntryIsPP partition idxroot pd s ->
In indirection (getIndirections pd s) ->
In partition (getPartitions pageRootPartition s) ->
(pageDefault =? nextIndirection) = false ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 

noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
consistency s -> 

(* isPartitionFalseAll s  ptSh1FstVA  ptSh1TrdVA ptSh1SndVA idxFstVA   idxSndVA   idxTrdVA -> *)
dataStructurePdSh1Sh2asRoot idxPageDir
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
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros * Hgoal Hindor3  Hwell1 Hlpred Hor3 Hlookup Hnblgen Hindesc Hwellmmu Hnotfst Hppx Hinmmu Hpartin Hnewnotdef.
intros.
move Hgoal at bottom.
 unfold dataStructurePdSh1Sh2asRoot in *.
intros * Hpart0 * Hpp0 * Ht * Hllv * Hind .
assert(Hdup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition idxroot;trivial. 
  assert(Hconsdup: noDupConfigPagesList s) by trivial.
  apply Hconsdup;trivial. }
assert(Hpart : forall part, In part (getPartitions pageRootPartition s) <-> In part (getPartitions pageRootPartition s')).
intros.
unfold s'.
eapply  getPartitionsAddIndirection;trivial;try eassumption;trivial.
rewrite <- Hpart in *.
assert(Hpp': nextEntryIsPP partition0 idxPageDir entry0 s).
apply nextEntryIsPPMapMMUPage' with indirection (StateLib.getIndexOfAddr vaToPrepare l) 
  nextIndirection r w  e;trivial.

assert(Horx: partition = partition0 \/ partition <> partition0) by apply pageDecOrNot.
destruct Horx as[Horx | Horx].
+ subst partition0.
  move Hindesc at bottom.
  destruct Hindor3 as [(Hi1 & Hi2 & Hii3) | [(Hi1 & Hi2 & Hii3) | (Hi1 & Hi2 & Hii3)] ].
  - assert(HingetInd : In indirection (getIndirections  entry0 s)).
    apply indirectionDescriptionInGetIndirections with partition vaToPrepare l idxPageDir;trivial.
    left;trivial.
    subst;trivial.
    unfold indirectionDescription,  initPEntryTablePreconditionToPropagatePrepareProperties in *.
    destruct Hindesc as (tableroot & Hpp & Hrootnotdef & Hor). 
    subst phyPDChild.
    subst.
    assert (pd = entry0).
    apply getPdNextEntryIsPPEq with partition s;trivial.
    apply nextEntryIsPPgetPd;trivial.
    subst entry0 .
     assert (pd = tableroot).
    apply getPdNextEntryIsPPEq with partition s;trivial.
    apply nextEntryIsPPgetPd;trivial.
    subst tableroot.
    rewrite <- Hnblgen in Hllv.
    inversion Hllv;subst nbLgen.
    clear Hpp0.
    assert(Hispe:isPE indirection idx s) by (
    apply MMUindirectionIsPE with partition pd vaToPrepare l;trivial).
    destruct Hor as [(Hroot & Hnbl) | (nbl & sstop & Hnbl & Hsstop & Hind1 & Hnotdef & Hl)].
    * subst.
      rewrite <- Hnblgen in Hnbl.
      inversion Hnbl;subst.
      apply PCWellFormedDataStructAddIndirection with va entry partition lpred;trivial.
    * rewrite <- Hnblgen in Hnbl.
      inversion Hnbl;subst.
      clear Hllv Hpp' Hpart Hnbl.
      assert(sstop=0 \/ sstop>0) as [Horsstop0|Hsstop0] by lia.
      -- subst;simpl in *.
         inversion Hind1;subst.
         rewrite CLevelIdentity' in *.
         apply PCWellFormedDataStructAddIndirection with va entry partition lpred;trivial.
         unfold s' in *;trivial.
         rewrite CLevelIdentity' in *.
         trivial.
      -- assert(stop < sstop \/ stop = sstop \/ stop>sstop) as [Hor |[Hor|Hor]] by lia.
         ** assert(Heq : getIndirection pd va level stop s' =getIndirection pd va level stop s). 
            { symmetry.
              apply getIndirectionMapMMUPage11Stoplt with entry;trivial.        
              intros.
            assert(Hin: In tbl (getIndirectionsAux pd s (stop0+1))).
            { apply getIndirectionInGetIndirections1 with va level ;trivial.
              destruct level;simpl in *.  lia.
              assert(Hx: (pageDefault =? tbl) = false) by trivial.
              apply beq_nat_false in Hx;unfold not;intros;subst;now contradict Hx. }
           assert(~In indirection (getIndirectionsAux pd s (stop0+1))).
           { apply getIndirectionInGetIndirections2n with sstop vaToPrepare level;trivial.
             destruct level;simpl in *.
             lia.
             apply noDupPreviousMMULevels with nbLevel ;trivial.
             destruct level;simpl in *.
             lia.
             lia. }
            unfold not;intros ;subst; now contradict Hin. }
            rewrite Heq in Hind.
            apply wellFormedRootDataStructAddIndirection with partition va pd entry;trivial.
         ** subst.
            assert(Hkey: ~In indirection (getIndirectionsAux pd s sstop)).
            { assert(Hex: sstop + 1 <= nbLevel).
              destruct level;simpl in *.
              lia.
              apply getIndirectionInGetIndirections2' with vaToPrepare level;trivial.
              unfold getIndirections in *.
              apply noDupPreviousMMULevels with nbLevel ;trivial. }
            assert(Heqind: getIndirection pd va level sstop s' =getIndirection pd va level sstop s). 
            {  apply getIndirectionAddIndirectionEq with entry;trivial. }
            rewrite Heqind in Hind.
            apply wellFormedRootDataStructAddIndirection with partition va pd entry;trivial.
        ** assert(Hdefind0: indirection0 = pageDefault  \/ indirection0 <> pageDefault ) by apply pageDecOrNot. 
           destruct Hdefind0 as [Hdefind0|Hdefind0].
           left;trivial.
(*            right.  *)
           assert(Hkey: ~In indirection (getIndirectionsAux pd s sstop)).
           { assert(Hex: sstop + 1 <= nbLevel).
            destruct level;simpl in *.
            lia.
            apply getIndirectionInGetIndirections2' with vaToPrepare level;trivial.
            unfold getIndirections in *.
            apply noDupPreviousMMULevels with nbLevel ;trivial.
           }
          assert(Heqind: getIndirection pd vaToPrepare level sstop s' =getIndirection pd vaToPrepare level sstop s). 
               {  apply getIndirectionAddIndirectionEq with entry;trivial. }
          assert(Heqindx: getIndirection pd va level sstop s' =getIndirection pd va level sstop s). 
                {  apply getIndirectionAddIndirectionEq with entry;trivial. }
          assert(Hi: stop <= nbLevel-1 \/ stop > nbLevel -1) by lia.
          destruct Hi as [Hi | Hi].
          +++ apply PCWellFormedRootDataStructAddIndirection with pd lpred va  entry partition;trivial.
              lia.
          +++ pose proof nbLevelNotZero.  
               assert(Hx:  (nbLevel -1) = level).
              {  rewrite  CLevelIdentity2 with (nbLevel-1).
                 symmetry.
                 rewrite getNbLevelEq with level;trivial. 
                 lia. }
              assert(Hxp: PCWellFormedRootDataStruct (nbLevel - 1) level indirection0 idx s' idxPageDir).
              apply PCWellFormedRootDataStructAddIndirection with pd lpred va  entry partition;trivial.
              apply getIndirectionStopLevelGT2 with stop;trivial.
              lia.
              lia.
              unfold PCWellFormedRootDataStruct in Hxp.
              rewrite Hx in Hxp.
              destruct Hxp as [HdefaultPage|Hxp] ; [left ; trivial|right].
              destruct Hxp as [Hxp _] ; split; trivial.
              destruct Hxp as [HContradiction|Hxp].
              { inversion HContradiction as [Hlevel _].
                contradict Hlevel.
                lia.
              }
              destruct Hxp as [_ Hxp].
              right.
              split; trivial.
              rewrite Hx in Hi.
              lia.
    - subst.
      clear Hpart.
      move Hinmmu at bottom.
      move Hppx at bottom.
      assert(Hindeq: getIndirection entry0 va level stop s' = getIndirection entry0 va level stop s).
      { symmetry.
        apply getIndirectionMapMMUPage11 with entry;trivial.
        intros * Hi Hi1.
        assert(Hin: In tbl (getIndirections entry0 s)).
        { apply  getIndirectionInGetIndirections with va level stop0;trivial.
          apply nbLevelNotZero.
          apply beq_nat_false in Hi1;unfold not;intros ;subst;now contradict Hi1.
          rewrite getNbLevelEq with level;trivial.
          apply pdPartNotNull with partition s;trivial. }
          apply disjointPartitionDataStructure with entry0 pd idxPageDir idxShadow1 partition s;trivial.        
          unfold or3;left;trivial.
          apply idxPDidxSh1notEq.
          assert(Hconsdup: noDupConfigPagesList s) by trivial.
          unfold noDupConfigPagesList in *.
          apply Hconsdup in Hpart0.
          unfold getConfigPages in Hpart0.
          apply NoDup_cons_iff in Hpart0.
          intuition.
          apply pdPartNotNull with partition s;trivial.  }
        apply wellFormedRootDataStructAddIndirection with partition va entry0 entry;trivial.
        rewrite <- Hindeq;trivial.
        apply  indirectionDescriptionNotDefault in Hindesc;trivial.
      - subst.
        clear Hpart.
        move Hinmmu at bottom.
        move Hppx at bottom.
        assert(Hindeq: getIndirection entry0 va level stop s' = getIndirection entry0 va level stop s).
        { symmetry.
          apply getIndirectionMapMMUPage11 with entry;trivial.
          intros * Hi Hi1.
          assert(Hin: In tbl (getIndirections entry0 s)).
          { apply  getIndirectionInGetIndirections with va level stop0;trivial.
            apply nbLevelNotZero.
            apply beq_nat_false in Hi1;unfold not;intros ;subst;now contradict Hi1.
            rewrite getNbLevelEq with level;trivial.
            apply pdPartNotNull with partition s;trivial. }
            apply disjointPartitionDataStructure with entry0 pd idxPageDir idxShadow2 partition s;trivial.        
            unfold or3;left;trivial.
            apply idxPDidxSh2notEq.
            assert(Hconsdup: noDupConfigPagesList s) by trivial.
            unfold noDupConfigPagesList in *.
            apply Hconsdup in Hpart0.
            unfold getConfigPages in Hpart0.
            apply NoDup_cons_iff in Hpart0.
            intuition.
            apply pdPartNotNull with partition s;trivial.  }
          apply wellFormedRootDataStructAddIndirection with partition va entry0 entry;trivial.
          rewrite <- Hindeq;trivial.
          apply  indirectionDescriptionNotDefault in Hindesc;trivial.
+ assert(Hindeq: getIndirection entry0 va level stop s' = getIndirection entry0 va level stop s).
  { symmetry.
          apply getIndirectionMapMMUPage11 with entry;trivial.
          intros * Hi Hi1.
     assert(Hin: In tbl (getConfigPages partition0 s)).
     { assert(Hin: In tbl (getIndirections entry0 s)).
          { apply  getIndirectionInGetIndirections with va level stop0;trivial.
            apply nbLevelNotZero.
            apply beq_nat_false in Hi1;unfold not;intros ;subst;now contradict Hi1.
            rewrite getNbLevelEq with level;trivial.
            apply pdPartNotNull with partition0 s;trivial. } 
      unfold getConfigPages.
      simpl;right.
      apply inGetIndirectionsAuxInConfigPagesPD with entry0;trivial.
      apply nextEntryIsPPgetPd;trivial. }
     assert(Hinx: In indirection (getConfigPages partition s)).
     { unfold getConfigPages.
      simpl;right.
      apply inGetIndirectionsAuxInConfigPages with pd idxroot;trivial. }
      assert(Hkdi: configTablesAreDifferent s) by trivial. 
      unfold configTablesAreDifferent in *.
      unfold disjoint in *.
      contradict Hin.      
      apply Hkdi with partition;trivial.
      subst;trivial.
      apply pdPartNotNull with partition0 s;trivial. }
  apply wellFormedRootDataStructAddIndirection with partition0 va entry0 entry;trivial.
  rewrite <- Hindeq;trivial.
  apply  indirectionDescriptionNotDefault in Hindesc;trivial.
Qed.

     Lemma getIndirectionUpdateLastIndirectionSh1 lpred sstop s indirection va phySh1addr r w e entry : 
      forall (stop : nat) (level : level),
let s' :=
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr va (CLevel (level - sstop)))
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |})
              (memory s) pageEq idxEq |} in
forall pd : page,
isWellFormedFstShadow lpred phySh1addr s' ->
lookup indirection (StateLib.getIndexOfAddr va (CLevel (level - sstop))) (memory s) pageEq idxEq =
Some (PE entry) ->
~ In indirection (getIndirectionsAux pd s sstop) ->
(pageDefault =? phySh1addr) = false ->
phySh1addr <> indirection ->
getIndirection pd va level stop s' = Some indirection ->
getIndirection pd va level sstop s = Some indirection ->
level <= stop -> indirection <> pageDefault -> sstop >= level.
Proof.
induction sstop;simpl;intros * Hwell' Hlookup Hkey Hnotdefp H Hind Hmid1 Hix Hdefind0.
* destruct stop;simpl in *.  lia.
  case_eq(levelEq level levelMin);intros * Hll;rewrite Hll in *.
  unfold  levelEq in *.
  apply beq_nat_true in Hll.
  rewrite <- fstLevelIs0 in Hll.
  lia.
  inversion Hmid1.
  subst.
  assert(Hread: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va level)
  (add indirection (StateLib.getIndexOfAddr va (CLevel (level - 0)))
  (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |}) (memory s) pageEq idxEq) =
  Some phySh1addr). 
  { rewrite <- minus_n_O.
  rewrite CLevelIdentity1.
  apply readPhyEntryAddIndirectionSameTable. }
  rewrite Hread in *.
  rewrite Hnotdefp in Hind. 
  case_eq(StateLib.Level.pred level);intros * Hl;rewrite Hl in *; try now contradict Hind.
  destruct stop;simpl in *.          inversion Hind;subst. now contradict H.
  case_eq(levelEq l levelMin);intros Hli;rewrite Hli in *.
  inversion Hind;subst. now contradict H.
  unfold isWellFormedFstShadow in *.
  destruct Hwell' as [(_ &Hwell')|(_ &Hwell')];simpl in *.
  destruct Hwell' with (StateLib.getIndexOfAddr va l) as (Hw & _).
  simpl in *.
  rewrite Hw in Hind.
  rewrite <- beq_nat_refl in Hind.
  inversion Hind;subst.
  now contradict Hdefind0.
  destruct Hwell' with (StateLib.getIndexOfAddr va l) as (Hw & _).
  clear Hwell'.
  unfold StateLib.readPhyEntry, StateLib.readVirEntry in *;
  simpl in *. 
  destruct ( beqPairs (indirection, StateLib.getIndexOfAddr va (CLevel (level - 0)))
  (phySh1addr, StateLib.getIndexOfAddr va l) pageEq idxEq);simpl in *;subst; try now contradict Hw.
  destruct (  lookup phySh1addr (StateLib.getIndexOfAddr va l)
  (removeDup indirection (StateLib.getIndexOfAddr va (CLevel (level - 0))) 
  (memory s) pageEq idxEq) pageEq idxEq); simpl; subst.
  destruct v;try now contradict Hw.
  try now contradict Hw.
*
case_eq (levelEq level levelMin);intros * Hfst;rewrite  Hfst in *.
+ inversion Hmid1;subst.
  unfold levelEq in *.
  apply beq_nat_true in Hfst.
  unfold levelMin in *.
  unfold CLevel in Hfst.
  case_eq(lt_dec 0 nbLevel);intros * Hnb;rewrite Hnb in *;simpl in *.
  rewrite Hfst in Hind.
  simpl in *.
  lia.
  pose proof nbLevelNotZero.
  lia.
+ case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va level) (memory s));
 intros * Hpd;rewrite Hpd in *;try now contradict Hmid1.
 case_eq(pageDefault =? p);intros * Hp;rewrite Hp in *.
 - inversion Hmid1;subst. now contradict Hdefind0.
 - case_eq( StateLib.Level.pred level );intros * Hpred;rewrite Hpred in *;
 try now contradict Hmid1.
 apply not_or_and in Hkey.
 destruct Hkey as (Hkey1 & Hkey2).
 rewrite in_flat_map in Hkey2.
 apply NNPP.
 unfold not;intros Hfalse.
 contradict Hkey2.
 exists p;split.
 apply readPhyEntryInGetTablePages with (StateLib.getIndexOfAddr va level);
 try lia.
 destruct(StateLib.getIndexOfAddr va level);simpl;lia.
 apply beq_nat_false in Hp.
 unfold not;intros;subst;now contradict Hp.
 rewrite indexEqId;trivial.
 apply NNPP.
 unfold not at 1;intros.
 apply Hfalse. clear Hfalse.
 destruct stop;simpl in *.
 inversion Hind;subst.
 now contradict Hkey1.
 rewrite Hfst in Hind.       
 assert(Htruep:  StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va level)
     (add indirection (StateLib.getIndexOfAddr va (CLevel (level - S sstop)))
        (PE {| read := r; write := w; exec := e; present := true; user := true; 
        pa := phySh1addr |}) (memory s) pageEq idxEq) = Some p).
 { rewrite <- Hpd.
   symmetry.
   apply readPhyEntryMapMMUPage with entry;trivial.
   left;intuition. }
 rewrite Htruep in *.
 rewrite Hp in *.
 rewrite Hpred in *.
  assert(Hpredl: level -1 = l) by (apply levelPredMinus1Nat;trivial).
     assert(Hkey2: (level - S sstop = l - sstop)) by (rewrite <- Hpredl;lia).
     assert( sstop >= l).
 {    rewrite Hkey2 in *.
     apply IHsstop with stop p;trivial.

     lia. }
     lia.
Qed.

Lemma getIndirectionUpdateLastIndirectionSh2 lpred sstop s indirection va phySh1addr r w e entry : 
      forall (stop : nat) (level : level),
let s' :=
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr va (CLevel (level - sstop)))
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |})
              (memory s) pageEq idxEq |} in
forall pd : page,
isWellFormedSndShadow lpred phySh1addr s' ->
lookup indirection (StateLib.getIndexOfAddr va (CLevel (level - sstop))) (memory s) pageEq idxEq =
Some (PE entry) ->
~ In indirection (getIndirectionsAux pd s sstop) ->
(pageDefault =? phySh1addr) = false ->
phySh1addr <> indirection ->
getIndirection pd va level stop s' = Some indirection ->
getIndirection pd va level sstop s = Some indirection ->
level <= stop -> indirection <> pageDefault -> sstop >= level.
Proof.
induction sstop;simpl;intros * Hwell' Hlookup Hkey Hnotdefp H Hind Hmid1 Hix Hdefind0.
* destruct stop;simpl in *.  lia.
  case_eq(levelEq level levelMin);intros * Hll;rewrite Hll in *.
  +
  unfold  levelEq in *.
  apply beq_nat_true in Hll.
  rewrite <- fstLevelIs0 in Hll.
  lia.
  +
  inversion Hmid1.
  subst.
  assert(Hread: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va level)
  (add indirection (StateLib.getIndexOfAddr va (CLevel (level - 0)))
  (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |}) (memory s) pageEq idxEq) =
  Some phySh1addr). 
  { rewrite <- minus_n_O.
  rewrite CLevelIdentity1.
  apply readPhyEntryAddIndirectionSameTable. }
  rewrite Hread in *.
  rewrite Hnotdefp in Hind. 
  case_eq(StateLib.Level.pred level);intros * Hl;rewrite Hl in *; try now contradict Hind.
  destruct stop;simpl in *.
  -
  inversion Hind;subst. now contradict H.
  -
  case_eq(levelEq l levelMin);intros Hli;rewrite Hli in *.
  inversion Hind;subst. now contradict H.
  unfold isWellFormedFstShadow in *.
  destruct Hwell' as [(_ &Hwell')|(_ &Hwell')];simpl in *.
  destruct Hwell' with (StateLib.getIndexOfAddr va l) as (Hw & _).
  simpl in *.
  rewrite Hw in Hind.
  rewrite <- beq_nat_refl in Hind.
  inversion Hind;subst.
  now contradict Hdefind0.
  generalize(Hwell'  (StateLib.getIndexOfAddr va l)); intros Hw.
  clear Hwell'.
  unfold StateLib.readPhyEntry, StateLib.readVirtual in *;
  simpl in *. 
  destruct ( beqPairs (indirection, StateLib.getIndexOfAddr va (CLevel (level - 0)))
  (phySh1addr, StateLib.getIndexOfAddr va l) pageEq idxEq);simpl in *;subst; try now contradict Hw.
  destruct (  lookup phySh1addr (StateLib.getIndexOfAddr va l)
  (removeDup indirection (StateLib.getIndexOfAddr va (CLevel (level - 0))) 
  (memory s) pageEq idxEq) pageEq idxEq); simpl; subst.
  destruct v;try now contradict Hw.
  try now contradict Hw.
*
case_eq (levelEq level levelMin);intros * Hfst;rewrite  Hfst in *.
+ inversion Hmid1;subst.
  unfold levelEq in *.
  apply beq_nat_true in Hfst.
  unfold levelMin in *.
  unfold CLevel in Hfst.
  case_eq(lt_dec 0 nbLevel);intros * Hnb;rewrite Hnb in *;simpl in *.
  rewrite Hfst in Hind.
  simpl in *.
  lia.
  pose proof nbLevelNotZero.
  lia.
+ case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va level) (memory s));
 intros * Hpd;rewrite Hpd in *;try now contradict Hmid1.
 case_eq(pageDefault =? p);intros * Hp;rewrite Hp in *.
 - inversion Hmid1;subst. now contradict Hdefind0.
 - case_eq( StateLib.Level.pred level );intros * Hpred;rewrite Hpred in *;
 try now contradict Hmid1.
 apply not_or_and in Hkey.
 destruct Hkey as (Hkey1 & Hkey2).
 rewrite in_flat_map in Hkey2.
 apply NNPP.
 unfold not;intros Hfalse.
 contradict Hkey2.
 exists p;split.
 apply readPhyEntryInGetTablePages with (StateLib.getIndexOfAddr va level);
 try lia.
 destruct(StateLib.getIndexOfAddr va level);simpl;lia.
 apply beq_nat_false in Hp.
 unfold not;intros;subst;now contradict Hp.
 rewrite indexEqId;trivial.
 apply NNPP.
 unfold not at 1;intros.
 apply Hfalse. clear Hfalse.
 destruct stop;simpl in *.
 inversion Hind;subst.
 now contradict Hkey1.
 rewrite Hfst in Hind.       
 assert(Htruep:  StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va level)
     (add indirection (StateLib.getIndexOfAddr va (CLevel (level - S sstop)))
        (PE {| read := r; write := w; exec := e; present := true; user := true; 
        pa := phySh1addr |}) (memory s) pageEq idxEq) = Some p).
 { rewrite <- Hpd.
   symmetry.
   apply readPhyEntryMapMMUPage with entry;trivial.
   left;intuition. }
 rewrite Htruep in *.
 rewrite Hp in *.
 rewrite Hpred in *.
  assert(Hpredl: level -1 = l) by (apply levelPredMinus1Nat;trivial).
     assert(Hkey2: (level - S sstop = l - sstop)) by (rewrite <- Hpredl;lia).
     assert( sstop >= l).
 {    rewrite Hkey2 in *.
     apply IHsstop with stop p;trivial.

     lia. }
     lia.
Qed.

Lemma PCWellFormedRootDataStructSh1AddIndirection stop (level:level) phySh1addr idx  s e w r 
sstop vaToPrepare indirection lpred entry pd va :
let s':=  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := phySh1addr |}) (memory s) pageEq idxEq |}  in 
lookup indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop))) 
        (memory s) pageEq idxEq = Some (PE entry) -> 
isWellFormedFstShadow lpred phySh1addr s -> 
phySh1addr <> pageDefault -> 
phySh1addr <> indirection -> 
 stop <= level -> 
false = levelEq (CLevel (level - sstop)) levelMin -> 
StateLib.Level.pred (CLevel (level - sstop)) = Some lpred -> 
getIndirection pd va level sstop s = Some indirection -> 
getIndirection pd va level sstop s' = getIndirection pd va level sstop s -> 
indirection <> pageDefault ->
StateLib.getIndexOfAddr va (CLevel (level - sstop)) =
   StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)) ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
        (add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
           (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |})
           (memory s) pageEq idxEq) = Some phySh1addr -> 
getIndirection pd va level stop s' = Some phySh1addr -> 
pd <> pageDefault -> 
stop > sstop -> 
PCWellFormedRootDataStruct stop level phySh1addr idx s' idxShadow1.    
Proof.
intros * Hlookup Hwellmmu Hdefind00 H Hii Hnotfst Hlpred Hmid1 Heqindx 
Hdefind0 Horx Hnewind Hind Hrootnotdef Horxx.
move Hwellmmu at bottom.
unfold isWellFormedFstShadow in *.
unfold PCWellFormedRootDataStruct.
right;split;trivial.
   assert(Hwell': isWellFormedFstShadow lpred phySh1addr s').
  { apply isWellFormedFstShadowTablesAddIndirection with entry;trivial. }
assert( Horstop: stop < level \/ stop = level) by lia.    
assert((level - sstop)>0).
{ symmetry in Hnotfst.
  apply levelEqBEqNatFalse0 in Hnotfst.
  rewrite <- CLevelIdentity2 in Hnotfst.
  trivial.
  destruct level;simpl in *.
  lia. }
assert(Hlpred1: (level - sstop) -1 = lpred).
{ symmetry in Hnotfst.
  eapply levelPredMinus1Nat with (l':=lpred) in Hnotfst;trivial.
  rewrite <- Hnotfst.
  rewrite <- CLevelIdentity2 .
  trivial.
  destruct level;simpl in *.
  lia. }
destruct  Hwellmmu as [Hwellmmu|Hwellmmu].
-- destruct Horstop as [Horstop|Horstop]. 
   ++ subst. 
      left;split;trivial.
      destruct Hwellmmu as (_ & Hwellmmu).
      destruct Hwellmmu with idx as (Hwellmmu' & _).
      apply isPEMapMMUPage with entry; trivial.
      apply readPhyEntryIsPE with pageDefault;trivial.
   ++  
    assert(sstop+1 = stop \/ sstop+1 < stop). lia.
    destruct H1.
    **  subst.
        replace (level - sstop - 1 ) with (level - (sstop + 1) ) in * by lia.
        rewrite <- H1 in Hlpred1.
        destruct Hwellmmu as (Hkey1 & _).
        unfold levelMin in Hkey1.
        contradict Hkey1.
        intros. 
        assert(Hi:0= lpred). lia.
        revert Hi.
        clear.    
        intros.
        assert(0 = CLevel 0).
        apply CLevelIdentity2;trivial.
        apply nbLevelNotZero.
        rewrite H in Hi.
        symmetry.
        apply level_eq_l;trivial.
    **  assert(getIndirection pd va level (sstop+1) s' = Some phySh1addr). 
        apply getIndirectionStopS' with indirection;trivial. lia.
        rewrite Heqindx;trivial.
        simpl.
        rewrite <- Hnotfst.
        rewrite Horx.
        rewrite Hnewind.
        assert(Hnotdefp: (pageDefault =? phySh1addr) = false).
        rewrite Nat.eqb_neq.
        unfold not;intros;subst.
        contradict Hdefind00.
        symmetry.
        apply page_eq_p;trivial.
        rewrite Hnotdefp.
        rewrite Hlpred;trivial.
        move Hind at bottom.
        assert( In phySh1addr (getIndirectionsAux pd s' ((sstop+1)+1))).
        { apply getIndirectionInGetIndirections1  with va level;trivial.
        destruct level;simpl in *.
        lia. }
        assert(~ In phySh1addr (getIndirectionsAux pd s' stop)).
        apply getIndirectionInGetIndirections2' with va level;trivial.
        destruct level;simpl in *.
        lia.
        admit. (** NoDup (getIndirectionsAux pd s' nbLevel) (stop+1 = level+1 = nbLevel)*)
        lia.
        assert(incl (getIndirectionsAux pd s' (sstop+1+1)) (getIndirectionsAux pd s' stop)).
        subst.
        apply inclGetIndirectionsAuxLe.
        lia.
        unfold incl in *.
        contradict H4.
        apply H5;trivial.
-- destruct Horstop as [Horstop|Horstop]. 
   ++  subst. 
      assert( sstop - 1 = level).
      { destruct Hwellmmu as (Hkey1 & _).
      unfold levelMin in Hkey1.
      rewrite Hkey1 in Hlpred1.
      assert(Hi:0= lpred).
      assert(0 = CLevel 0).
      apply CLevelIdentity2;trivial.
      apply nbLevelNotZero.
      subst. trivial.
      subst.
      rewrite <- Hi in Hlpred1.
      lia. } lia.
   ++ subst. right;split. lia.
      left;split;trivial.
      apply isVEMapMMUPage with entry;trivial.
      destruct Hwellmmu as (_ & Hwellmmu).
      destruct Hwellmmu with idx as (Hwellmmu' & _).
      apply readVirEntryIsPE with vaddrDefault;trivial. 
Admitted.

Lemma PCWellFormedRootDataStructSh2AddIndirection stop (level:level) phySh2addr idx  s e w r 
sstop vaToPrepare indirection lpred entry pd va :
let s':=  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := phySh2addr |}) (memory s) pageEq idxEq |}  in 
lookup indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop))) 
        (memory s) pageEq idxEq = Some (PE entry) -> 
isWellFormedSndShadow lpred phySh2addr s -> 
phySh2addr <> pageDefault -> 
phySh2addr <> indirection -> 
 stop <= level -> 
false = levelEq (CLevel (level - sstop)) levelMin -> 
StateLib.Level.pred (CLevel (level - sstop)) = Some lpred -> 
getIndirection pd va level sstop s = Some indirection -> 
getIndirection pd va level sstop s' = getIndirection pd va level sstop s -> 
indirection <> pageDefault ->
StateLib.getIndexOfAddr va (CLevel (level - sstop)) =
   StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)) ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
        (add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
           (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh2addr |})
           (memory s) pageEq idxEq) = Some phySh2addr -> 
getIndirection pd va level stop s' = Some phySh2addr -> 
pd <> pageDefault -> 
stop > sstop -> 
PCWellFormedRootDataStruct stop level phySh2addr idx s' idxShadow2.    
Proof.
intros * Hlookup Hwellmmu Hdefind00 H Hii Hnotfst Hlpred Hmid1 Heqindx 
Hdefind0 Horx Hnewind Hind Hrootnotdef Horxx.
move Hwellmmu at bottom.
unfold isWellFormedFstShadow in *.
unfold PCWellFormedRootDataStruct.
right;split;trivial.
   assert(Hwell': isWellFormedSndShadow lpred phySh2addr s').
  { apply isWellFormedSndShadowTablesAddIndirection with entry;trivial. }
assert( Horstop: stop < level \/ stop = level) by lia.    
assert((level - sstop)>0).
{ symmetry in Hnotfst.
  apply levelEqBEqNatFalse0 in Hnotfst.
  rewrite <- CLevelIdentity2 in Hnotfst.
  trivial.
  destruct level;simpl in *.
  lia. }
assert(Hlpred1: (level - sstop) -1 = lpred).
{ symmetry in Hnotfst.
  eapply levelPredMinus1Nat with (l':=lpred) in Hnotfst;trivial.
  rewrite <- Hnotfst.
  rewrite <- CLevelIdentity2 .
  trivial.
  destruct level;simpl in *.
  lia. }
destruct  Hwellmmu as [Hwellmmu|Hwellmmu].
-- destruct Horstop as [Horstop|Horstop]. 
   ++ subst. 
      left;split;trivial.
      destruct Hwellmmu as (_ & Hwellmmu).
      destruct Hwellmmu with idx as (Hwellmmu' & _).
      apply isPEMapMMUPage with entry; trivial.
      apply readPhyEntryIsPE with pageDefault;trivial.
   ++  
    assert(sstop+1 = stop \/ sstop+1 < stop). lia.
    destruct H1.
    **  subst.
        replace (level - sstop - 1 ) with (level - (sstop + 1) ) in * by lia.
        rewrite <- H1 in Hlpred1.
        destruct Hwellmmu as (Hkey1 & _).
        unfold levelMin in Hkey1.
        contradict Hkey1.
        intros. 
        assert(Hi:0= lpred). lia.
        revert Hi.
        clear.    
        intros.
        assert(0 = CLevel 0).
        apply CLevelIdentity2;trivial.
        apply nbLevelNotZero.
        rewrite H in Hi.
        symmetry.
        apply level_eq_l;trivial.
    **  assert(getIndirection pd va level (sstop+1) s' = Some phySh2addr). 
        apply getIndirectionStopS' with indirection;trivial. lia.
        rewrite Heqindx;trivial.
        simpl.
        rewrite <- Hnotfst.
        rewrite Horx.
        rewrite Hnewind.
        assert(Hnotdefp: (pageDefault =? phySh2addr) = false).
        rewrite Nat.eqb_neq.
        unfold not;intros;subst.
        contradict Hdefind00.
        symmetry.
        apply page_eq_p;trivial.
        rewrite Hnotdefp.
        rewrite Hlpred;trivial.
        move Hind at bottom.
        assert( In phySh2addr (getIndirectionsAux pd s' ((sstop+1)+1))).
        { apply getIndirectionInGetIndirections1  with va level;trivial.
        destruct level;simpl in *.
        lia. }
        assert(~ In phySh2addr (getIndirectionsAux pd s' stop)).
        apply getIndirectionInGetIndirections2' with va level;trivial.
        destruct level;simpl in *.
        lia.
        admit. (** NoDup (getIndirectionsAux pd s' nbLevel) (stop+1 = level+1 = nbLevel)*)
        lia.
        assert(incl (getIndirectionsAux pd s' (sstop+1+1)) (getIndirectionsAux pd s' stop)).
        subst.
        apply inclGetIndirectionsAuxLe.
        lia.
        unfold incl in *.
        contradict H4.
        apply H5;trivial.
-- destruct Horstop as [Horstop|Horstop]. 
   ++  subst. 
      assert( sstop - 1 = level).
      { destruct Hwellmmu as (Hkey1 & _).
      unfold levelMin in Hkey1.
      rewrite Hkey1 in Hlpred1.
      assert(Hi:0= lpred).
      assert(0 = CLevel 0).
      apply CLevelIdentity2;trivial.
      apply nbLevelNotZero.
      subst. trivial.
      subst.
      rewrite <- Hi in Hlpred1.
      lia. } lia.
   ++ subst. right;split. lia.
      left;split;trivial.
      apply isVEMapMMUPage with entry;trivial.
      destruct Hwellmmu as (_ & Hwellmmu).
      generalize(Hwellmmu idx);intros Hwellmmu'. 
      apply readVirEntryIsPE with vaddrDefault;trivial. 
Admitted.
      
Lemma PCWellFormedRootDataStructAddIndirectionSh1 pd vaToPrepare (level lpred:level) sstop s indirection idx 
va  indirection0 stop phySh1addr r w e entry partition:
let s' := {|
currentPartition := currentPartition s;
memory := add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
    (PE
       {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |})
    (memory s) pageEq idxEq |} in 
NoDup (getIndirectionsAux pd s nbLevel) -> 
lookup indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop))) 
  (memory s) pageEq idxEq = Some (PE entry) -> 
isWellFormedFstShadow lpred phySh1addr s -> 
dataStructurePdSh1Sh2asRoot idxShadow1 s -> 
Some level = StateLib.getNbLevel -> 
In partition (getPartitions pageRootPartition s) ->
getIndirection pd vaToPrepare level sstop s = Some indirection -> 

getIndirection pd va level stop s' = Some indirection0 -> 
stop <= nbLevel - 1 ->
sstop <= level ->
stop > sstop -> 
sstop > 0 ->
(* isPE indirection idx s ->  *)
indirection <> pageDefault -> 
false = levelEq (CLevel (level - sstop)) levelMin -> 
(pageDefault =? phySh1addr) = false -> 
StateLib.Level.pred (CLevel (level - sstop)) = Some lpred -> 
nextEntryIsPP partition idxShadow1 pd s -> 
indirection0 <> pageDefault ->
pd <> pageDefault -> 
phySh1addr <> indirection -> 
PCWellFormedRootDataStruct stop level indirection0 idx s' idxShadow1.
Proof.
intros * Hdup Hlookup Hwellmmu Hgoal Hnblgen Hpart0 Hind1 (* Hmid1 Hmid2 *) Hind Hi Hsstop
  Horxx Hsstop0 (* Hispe *) Hdefind0 Hnotfst Hnotdefp Hlpred Hpp Hdefind00 Hrootnotdef.
intros.
assert(Hii: stop <= level).
rewrite <- getNbLevelEqNat;trivial. 
clear Hi.
assert(Hor : stop >= sstop) by lia.
pose proof getIndirectionMiddle as Hmid.
generalize (Hmid stop pd va level s' indirection0 sstop Hind Hdefind00 Hor);clear Hmid;
intros Hmid.
destruct Hmid as (middle & Hmid1 & Hmid2).
assert(Hkey: ~In indirection (getIndirectionsAux pd s sstop)).
{ assert(Hex: sstop + 1 <= nbLevel).
  destruct level;simpl in *.
  lia.
  apply getIndirectionInGetIndirections2' with vaToPrepare level;trivial.
  unfold getIndirections in *.
  apply noDupPreviousMMULevels with nbLevel ;trivial. }
assert(Heqindx: getIndirection pd va level sstop s' =getIndirection pd va level sstop s). 
{  apply getIndirectionAddIndirectionEq with entry;trivial. }
rewrite Heqindx in Hmid1.
assert(Heqmid: middle = indirection \/  middle <> indirection) by apply pageDecOrNot.
destruct Heqmid as [Heqmid|Heqmid].
- subst.
  assert( Horx: (StateLib.getIndexOfAddr va (CLevel (level - sstop))) =  
  (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))\/ 
  (StateLib.getIndexOfAddr va (CLevel (level - sstop))) <>  
  (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop))) ) by apply indexDecOrNot.
  destruct Horx as [Horx | Horx].
  destruct (stop - sstop) ;simpl in *.
  + inversion Hmid2.
    subst indirection0.
    right.
    split;trivial.
    assert(stop < level \/ stop = level) by lia.
    destruct H0.
    * pose proof sh1indirectionIsVE as Hisve.
      generalize (Hisve partition pd indirection va s Hrootnotdef Hgoal Hpp
      Hpart0 level sstop Hnblgen Hsstop Hmid1 Hdefind0 idx)
      ; clear Hisve;intros Hisve.
      destruct Hisve as [Hisve|Hisve]. 
      -- left. split;trivial.
         apply isPEMapMMUPage with entry;intuition.
      -- destruct Hisve.
         lia.
    *
     assert(Hix : level<= stop) by lia. 
      assert(Hwell': isWellFormedFstShadow lpred phySh1addr s').
      { apply isWellFormedFstShadowTablesAddIndirection with entry;trivial. }
      assert(Htrue: sstop>=level).
      { unfold s' in *. rewrite <- Horx in *.
        revert Hwell' Hlookup Hkey Hnotdefp H Hind Hmid1 (* Hdup *) (* Hsstop0 *) Hix Hdefind0 . 
        clear.
        set (s':= {| currentPartition := _ |}). 
        revert dependent pd.
        revert dependent level.
        revert dependent stop.           
        intros. 
        eapply getIndirectionUpdateLastIndirectionSh1; try eassumption.  }
      subst. assert(sstop = level). lia.
      subst.
      unfold levelEq in *.
      symmetry in Hnotfst.
      apply beq_nat_false in Hnotfst.
      replace (level - level) with 0 in * by lia.
      unfold levelMin in *.
      now contradict Hnotfst.
 + rewrite <- Hnotfst in *.
    assert(Hnewind:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va  (CLevel (level - sstop)))
    (add indirection (StateLib.getIndexOfAddr va  (CLevel (level - sstop)))
    (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |}) (memory s) pageEq idxEq) =
    Some phySh1addr). 
    { apply readPhyEntryAddIndirectionSameTable. }
    rewrite Horx in *. 
    rewrite Hnewind in Hmid2.
    rewrite Hnotdefp in Hmid2.
    rewrite Hlpred in Hmid2.
    destruct n; simpl in *.
    * inversion Hmid2;subst indirection0.
      apply PCWellFormedRootDataStructSh1AddIndirection with lpred entry pd va;trivial.
    * case_eq(levelEq lpred levelMin);intros * Hlpred0;rewrite Hlpred0 in *. 
      ++ inversion Hmid2;subst indirection0.
         apply PCWellFormedRootDataStructSh1AddIndirection with lpred entry pd va;trivial.
      ++ move Hwellmmu at bottom. 
         clear Hnewind.
         case_eq(  StateLib.readPhyEntry phySh1addr (StateLib.getIndexOfAddr va lpred)
            (add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
               (PE
                  {|
                  read := r;
                  write := w;
                  exec := e;
                  present := true;
                  user := true;
                  pa := phySh1addr |}) (memory s) pageEq idxEq));intros * Hreadv; rewrite Hreadv in *;try now contradict Hmid2.
         case_eq(pageDefault =? p);intros * Hp;rewrite Hp in *. 
         -- inversion Hmid2.
            unfold PCWellFormedRootDataStruct.
            left;trivial.
         -- case_eq( StateLib.Level.pred lpred );intros * Hpredl; rewrite Hpredl in *;try now contradict Hmid2.
        unfold PCWellFormedRootDataStruct.
        right.
        assert(Hwell': isWellFormedFstShadow lpred phySh1addr s').
      { apply isWellFormedFstShadowTablesAddIndirection with entry;trivial. }
      assert(stop < level \/ stop = level) by lia.
    destruct H0.
    ** split;trivial. left. split;trivial.
      unfold isWellFormedFstShadow in *.
      destruct Hwell' as [Hwell'| Hwell']. 
      destruct Hwell' as (_ & Hwell'1).
      destruct Hwell'1 with (StateLib.getIndexOfAddr va lpred) as (Hwell'x & _).
      clear Hwell'1.
      simpl in *.
      rewrite Hwell'x in Hreadv.
      inversion Hreadv;subst.
      apply beq_nat_false in Hp.
      now contradict Hp.
      destruct Hwell' as (Hix & _). 
      unfold levelEq in *.
      apply beq_nat_false in Hlpred0.
      subst.
      now contradict Hlpred0.
    ** subst.
    destruct n;simpl in *.
    inversion Hmid2.
    subst.
    assert((pageDefault =? indirection0) = true).
    unfold isWellFormedFstShadow in Hwell'.
     destruct Hwell' as [Hwell'| Hwell']. 
      destruct Hwell' as (_ & Hwell'1).
      destruct Hwell'1 with (StateLib.getIndexOfAddr va lpred) as (Hwell'x & _).
      clear Hwell'1.
      simpl in *.
      rewrite Hwell'x in Hreadv.
      inversion Hreadv;subst.
      apply beq_nat_false in Hp.
      now contradict Hp.
      destruct Hwell' as (Hix & _). 
      unfold levelEq in *.
      apply beq_nat_false in Hlpred0.
      subst.
      now contradict Hlpred0.
    rewrite Hp in H0.
    now contradict H0.
    assert((pageDefault =? p) = true).
        unfold isWellFormedFstShadow in Hwell'.
     destruct Hwell' as [Hwell'| Hwell']. 
      destruct Hwell' as (_ & Hwell'1).
      destruct Hwell'1 with (StateLib.getIndexOfAddr va lpred) as (Hwell'x & _).
      clear Hwell'1.
      simpl in *.
      rewrite Hwell'x in Hreadv.
      inversion Hreadv;subst.
      apply beq_nat_false in Hp.
      now contradict Hp.
      destruct Hwell' as (Hix & _). 
      unfold levelEq in *.
      apply beq_nat_false in Hlpred0.
      subst.
      now contradict Hlpred0.
    rewrite Hp in H0.
    now contradict H0.
 +  apply wellFormedRootDataStructAddIndirection  with partition va pd entry;trivial. 
    apply getIndirectionMiddle2  with sstop indirection;trivial.
    rewrite <- Hmid2.
    clear    Hind1 .
    assert(Hnodup: NoDup (getIndirectionsAux indirection s (stop - sstop))).
    eapply nodupLevelMinusN with sstop pd va level ;trivial.
    replace (sstop + (stop - sstop)) with stop by lia.
    apply noDupPreviousMMULevels with nbLevel;trivial.
    destruct level;simpl in *;lia.
    destruct level;simpl in *;lia.
    case_eq (stop - sstop);simpl;intros * Hc;rewrite Hc in *;trivial.
    case_eq(levelEq (CLevel (level - sstop)) levelMin);intros * Hl;trivial.
    assert(Hreadeq: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va (CLevel (level - sstop)))
    (add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
     (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh1addr |})
     (memory s) pageEq idxEq) =
     StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va (CLevel (level - sstop)))
     (memory s) ).
     symmetry.
     apply readPhyEntryMapMMUPage with entry;trivial.
     right;trivial.
     rewrite Hreadeq;clear Hreadeq.
    case_eq(StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va (CLevel (level - sstop))) (memory s));intros 
    *  Hre;trivial.
    case_eq (      pageDefault =? p);intros * Hp;trivial.
    case_eq( StateLib.Level.pred (CLevel (level - sstop)) );intros;trivial.
    apply beq_nat_false in Hp.
    assert(p <> pageDefault).
    { unfold not;intros;subst;now contradict Hp. }

    apply getIndirectionMapMMUPage11Stoplt with entry;trivial.
    intros.
    simpl in Hnodup.
    apply NoDup_cons_iff in Hnodup.
    destruct Hnodup as (Hnodup & _).
    rewrite in_flat_map in Hnodup.
    contradict Hnodup.
    exists p.
    split.
    * apply readPhyEntryInGetTablePages with (StateLib.getIndexOfAddr va (CLevel (level - sstop)));
      trivial.
      destruct (StateLib.getIndexOfAddr va (CLevel (level - sstop)));simpl;trivial.
      rewrite <- Hre.
      f_equal.
      apply indexEqId.
    * rewrite <- Hnodup.
      assert(In tbl (getIndirectionsAux p s (stop0+1))).
      apply getIndirectionInGetIndirections1 with va l;trivial.
      destruct level;simpl in *.
      lia.
      assert(Hdef: (pageDefault =? tbl) = false) by trivial.
      apply beq_nat_false in Hdef.
      unfold not;intros;subst;now contradict Hdef.
      pose proof inclGetIndirectionsAuxLe as Hproof.
      unfold incl in *.
      apply Hproof with (stop0 + 1);trivial.
      lia.
- apply wellFormedRootDataStructAddIndirection  with partition va pd entry;trivial.
  rewrite <- Hind.
  symmetry.
  apply getIndirectionEqAddIndirectionIndirectionIsMiddle with entry
  sstop indirection0;trivial.
  assert(Hori: StateLib.checkVAddrsEqualityWOOffset sstop vaToPrepare va level = true \/
               StateLib.checkVAddrsEqualityWOOffset sstop vaToPrepare va level = false).
  { destruct ( StateLib.checkVAddrsEqualityWOOffset sstop vaToPrepare va level);simpl.
    left;trivial.
    right;trivial. }
  destruct Hori;trivial.
  assert(Hkey1: getIndirection pd vaToPrepare level sstop s = getIndirection pd va level sstop s).

  apply getIndirectionEqStop;trivial.
  rewrite checkVAddrsEqualityWOOffsetPermut';trivial.
  rewrite Hind1 in Hkey1.
  rewrite Hmid1 in Hkey1.
  inversion Hkey1.
  now contradict Heqmid.
Qed.

Lemma PCWellFormedRootDataStructAddIndirectionSh2 pd vaToPrepare (level lpred:level) sstop s indirection idx 
va  indirection0 stop phySh2addr r w e entry partition:
let s' := {|
currentPartition := currentPartition s;
memory := add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
    (PE
       {| read := r; write := w; exec := e; present := true; user := true; pa := phySh2addr |})
    (memory s) pageEq idxEq |} in 
NoDup (getIndirectionsAux pd s nbLevel) -> 
lookup indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop))) 
  (memory s) pageEq idxEq = Some (PE entry) -> 
isWellFormedSndShadow lpred phySh2addr s -> 
dataStructurePdSh1Sh2asRoot idxShadow2 s -> 
Some level = StateLib.getNbLevel -> 
In partition (getPartitions pageRootPartition s) ->
getIndirection pd vaToPrepare level sstop s = Some indirection -> 

getIndirection pd va level stop s' = Some indirection0 -> 
stop <= nbLevel - 1 ->
sstop <= level ->
stop > sstop -> 
sstop > 0 ->
(* isPE indirection idx s ->  *)
indirection <> pageDefault -> 
false = levelEq (CLevel (level - sstop)) levelMin -> 
(pageDefault =? phySh2addr) = false -> 
StateLib.Level.pred (CLevel (level - sstop)) = Some lpred -> 
nextEntryIsPP partition idxShadow2 pd s -> 
indirection0 <> pageDefault ->
pd <> pageDefault -> 
phySh2addr <> indirection -> 
PCWellFormedRootDataStruct stop level indirection0 idx s' idxShadow2.
Proof.
intros * Hdup Hlookup Hwellmmu Hgoal Hnblgen Hpart0 Hind1 (* Hmid1 Hmid2 *) Hind Hi Hsstop
  Horxx Hsstop0 (* Hispe *) Hdefind0 Hnotfst Hnotdefp Hlpred Hpp Hdefind00 Hrootnotdef.
intros.
assert(Hii: stop <= level).
rewrite <- getNbLevelEqNat;trivial. 
clear Hi.
assert(Hor : stop >= sstop) by lia.
pose proof getIndirectionMiddle as Hmid.
generalize (Hmid stop pd va level s' indirection0 sstop Hind Hdefind00 Hor);clear Hmid;
intros Hmid.
destruct Hmid as (middle & Hmid1 & Hmid2).
assert(Hkey: ~In indirection (getIndirectionsAux pd s sstop)).
{ assert(Hex: sstop + 1 <= nbLevel).
  destruct level;simpl in *.
  lia.
  apply getIndirectionInGetIndirections2' with vaToPrepare level;trivial.
  unfold getIndirections in *.
  apply noDupPreviousMMULevels with nbLevel ;trivial. }
assert(Heqindx: getIndirection pd va level sstop s' =getIndirection pd va level sstop s). 
{  apply getIndirectionAddIndirectionEq with entry;trivial. }
rewrite Heqindx in Hmid1.
assert(Heqmid: middle = indirection \/  middle <> indirection) by apply pageDecOrNot.
destruct Heqmid as [Heqmid|Heqmid].
- subst.
  assert( Horx: (StateLib.getIndexOfAddr va (CLevel (level - sstop))) =  
  (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))\/ 
  (StateLib.getIndexOfAddr va (CLevel (level - sstop))) <>  
  (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop))) ) by apply indexDecOrNot.
  destruct Horx as [Horx | Horx].
  destruct (stop - sstop) ;simpl in *.
  + inversion Hmid2.
    subst indirection0.
    right.
    split;trivial.
    assert(stop < level \/ stop = level) by lia.
    destruct H0.
    * pose proof sh2indirectionIsVA as Hisve.
      generalize (Hisve partition pd indirection va s Hrootnotdef Hgoal Hpp
      Hpart0 level sstop Hnblgen Hsstop Hmid1 Hdefind0 idx)
      ; clear Hisve;intros Hisve.
      destruct Hisve as [Hisve|Hisve]. 
      -- left. split;trivial.
         apply isPEMapMMUPage with entry;intuition.
      -- destruct Hisve.
         lia.
    *
     assert(Hix : level<= stop) by lia. 
      assert(Hwell': isWellFormedSndShadow lpred phySh2addr s').
      { apply isWellFormedSndShadowTablesAddIndirection with entry;trivial. }
      assert(Htrue: sstop>=level).
      { unfold s' in *. rewrite <- Horx in *.
        revert Hwell' Hlookup Hkey Hnotdefp H Hind Hmid1 (* Hdup *) (* Hsstop0 *) Hix Hdefind0 . 
        clear.
        set (s':= {| currentPartition := _ |}). 
        revert dependent pd.
        revert dependent level.
        revert dependent stop.           
        intros. 
        eapply getIndirectionUpdateLastIndirectionSh2; try eassumption.  }
      subst. assert(sstop = level). lia.
      subst.
      unfold levelEq in *.
      symmetry in Hnotfst.
      apply beq_nat_false in Hnotfst.
      replace (level - level) with 0 in * by lia.
      unfold levelMin in *.
      now contradict Hnotfst.
 + rewrite <- Hnotfst in *.
    assert(Hnewind:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va  (CLevel (level - sstop)))
    (add indirection (StateLib.getIndexOfAddr va  (CLevel (level - sstop)))
    (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh2addr |}) (memory s) pageEq idxEq) =
    Some phySh2addr). 
    { apply readPhyEntryAddIndirectionSameTable. }
    rewrite Horx in *. 
    rewrite Hnewind in Hmid2.
    rewrite Hnotdefp in Hmid2.
    rewrite Hlpred in Hmid2.
    destruct n; simpl in *.
    * inversion Hmid2;subst indirection0.
      apply PCWellFormedRootDataStructSh2AddIndirection with lpred entry pd va;trivial.
    * case_eq(levelEq lpred levelMin);intros * Hlpred0;rewrite Hlpred0 in *. 
      ++ inversion Hmid2;subst indirection0.
         apply PCWellFormedRootDataStructSh2AddIndirection with lpred entry pd va;trivial.
      ++ move Hwellmmu at bottom. 
         clear Hnewind.
         case_eq(  StateLib.readPhyEntry phySh2addr (StateLib.getIndexOfAddr va lpred)
            (add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
               (PE
                  {|
                  read := r;
                  write := w;
                  exec := e;
                  present := true;
                  user := true;
                  pa := phySh2addr |}) (memory s) pageEq idxEq));intros * Hreadv; rewrite Hreadv in *;try now contradict Hmid2.
         case_eq(pageDefault =? p);intros * Hp;rewrite Hp in *. 
         -- inversion Hmid2.
            unfold PCWellFormedRootDataStruct.
            left;trivial.
         -- case_eq( StateLib.Level.pred lpred );intros * Hpredl; rewrite Hpredl in *;try now contradict Hmid2.
        unfold PCWellFormedRootDataStruct.
        right.
        assert(Hwell': isWellFormedSndShadow lpred phySh2addr s').
      { apply isWellFormedSndShadowTablesAddIndirection with entry;trivial. }
      assert(stop < level \/ stop = level) by lia.
    destruct H0.
    ** split;trivial. left. split;trivial.
      unfold isWellFormedSndShadow in *.
      destruct Hwell' as [Hwell'| Hwell']. 
      destruct Hwell' as (_ & Hwell'1).
      destruct Hwell'1 with (StateLib.getIndexOfAddr va lpred) as (Hwell'x & _).
      clear Hwell'1.
      simpl in *.
      rewrite Hwell'x in Hreadv.
      inversion Hreadv;subst.
      apply beq_nat_false in Hp.
      now contradict Hp.
      destruct Hwell' as (Hix & _). 
      unfold levelEq in *.
      apply beq_nat_false in Hlpred0.
      subst.
      now contradict Hlpred0.
    ** subst.
    destruct n;simpl in *.
    inversion Hmid2.
    subst.
    assert((pageDefault =? indirection0) = true).
    unfold isWellFormedFstShadow in Hwell'.
     destruct Hwell' as [Hwell'| Hwell']. 
      destruct Hwell' as (_ & Hwell'1).
      destruct Hwell'1 with (StateLib.getIndexOfAddr va lpred) as (Hwell'x & _).
      clear Hwell'1.
      simpl in *.
      rewrite Hwell'x in Hreadv.
      inversion Hreadv;subst.
      apply beq_nat_false in Hp.
      now contradict Hp.
      destruct Hwell' as (Hix & _). 
      unfold levelEq in *.
      apply beq_nat_false in Hlpred0.
      subst.
      now contradict Hlpred0.
    rewrite Hp in H0.
    now contradict H0.
    assert((pageDefault =? p) = true).
        unfold isWellFormedSndShadow in Hwell'.
     destruct Hwell' as [Hwell'| Hwell']. 
      destruct Hwell' as (_ & Hwell'1).
      destruct Hwell'1 with (StateLib.getIndexOfAddr va lpred) as (Hwell'x & _).
      clear Hwell'1.
      simpl in *.
      rewrite Hwell'x in Hreadv.
      inversion Hreadv;subst.
      apply beq_nat_false in Hp.
      now contradict Hp.
      destruct Hwell' as (Hix & _). 
      unfold levelEq in *.
      apply beq_nat_false in Hlpred0.
      subst.
      now contradict Hlpred0.
    rewrite Hp in H0.
    now contradict H0.
 +  apply wellFormedRootDataStructAddIndirection  with partition va pd entry;trivial. 
    apply getIndirectionMiddle2  with sstop indirection;trivial.
    rewrite <- Hmid2.
    clear    Hind1 .
    assert(Hnodup: NoDup (getIndirectionsAux indirection s (stop - sstop))).
    eapply nodupLevelMinusN with sstop pd va level ;trivial.
    replace (sstop + (stop - sstop)) with stop by lia.
    apply noDupPreviousMMULevels with nbLevel;trivial.
    destruct level;simpl in *;lia.
    destruct level;simpl in *;lia.
    case_eq (stop - sstop);simpl;intros * Hc;rewrite Hc in *;trivial.
    case_eq(levelEq (CLevel (level - sstop)) levelMin);intros * Hl;trivial.
    assert(Hreadeq: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va (CLevel (level - sstop)))
    (add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (level - sstop)))
     (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phySh2addr |})
     (memory s) pageEq idxEq) =
     StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va (CLevel (level - sstop)))
     (memory s) ).
     symmetry.
     apply readPhyEntryMapMMUPage with entry;trivial.
     right;trivial.
     rewrite Hreadeq;clear Hreadeq.
    case_eq(StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va (CLevel (level - sstop))) (memory s));intros 
    *  Hre;trivial.
    case_eq (      pageDefault =? p);intros * Hp;trivial.
    case_eq( StateLib.Level.pred (CLevel (level - sstop)) );intros;trivial.
    apply beq_nat_false in Hp.
    assert(p <> pageDefault).
    { unfold not;intros;subst;now contradict Hp. }

    apply getIndirectionMapMMUPage11Stoplt with entry;trivial.
    intros.
    simpl in Hnodup.
    apply NoDup_cons_iff in Hnodup.
    destruct Hnodup as (Hnodup & _).
    rewrite in_flat_map in Hnodup.
    contradict Hnodup.
    exists p.
    split.
    * apply readPhyEntryInGetTablePages with (StateLib.getIndexOfAddr va (CLevel (level - sstop)));
      trivial.
      destruct (StateLib.getIndexOfAddr va (CLevel (level - sstop)));simpl;trivial.
      rewrite <- Hre.
      f_equal.
      apply indexEqId.
    * rewrite <- Hnodup.
      assert(In tbl (getIndirectionsAux p s (stop0+1))).
      apply getIndirectionInGetIndirections1 with va l;trivial.
      destruct level;simpl in *.
      lia.
      assert(Hdef: (pageDefault =? tbl) = false) by trivial.
      apply beq_nat_false in Hdef.
      unfold not;intros;subst;now contradict Hdef.
      pose proof inclGetIndirectionsAuxLe as Hproof.
      unfold incl in *.
      apply Hproof with (stop0 + 1);trivial.
      lia.
- apply wellFormedRootDataStructAddIndirection  with partition va pd entry;trivial.
  rewrite <- Hind.
  symmetry.
  apply getIndirectionEqAddIndirectionIndirectionIsMiddle with entry
  sstop indirection0;trivial.
  assert(Hori: StateLib.checkVAddrsEqualityWOOffset sstop vaToPrepare va level = true \/
               StateLib.checkVAddrsEqualityWOOffset sstop vaToPrepare va level = false).
  { destruct ( StateLib.checkVAddrsEqualityWOOffset sstop vaToPrepare va level);simpl.
    left;trivial.
    right;trivial. }
  destruct Hori;trivial.
  assert(Hkey1: getIndirection pd vaToPrepare level sstop s = getIndirection pd va level sstop s).

  apply getIndirectionEqStop;trivial.
  rewrite checkVAddrsEqualityWOOffsetPermut';trivial.
  rewrite Hind1 in Hkey1.
  rewrite Hmid1 in Hkey1.
  inversion Hkey1.
  now contradict Heqmid.
Qed.

Lemma dataStructurePdSh1Sh2asRootSh1AddIndirection
s indirection nextIndirection idxroot  entry nbLgen  pd   vaToPrepare partition l lpred r w e
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr  :
dataStructurePdSh1Sh2asRoot idxShadow1 s->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
nextEntryIsPP partition idxroot pd s ->
In indirection (getIndirections pd s) ->
In partition (getPartitions pageRootPartition s) ->
(pageDefault =? nextIndirection) = false ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 

noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
consistency s -> 

(* isPartitionFalseAll s  ptSh1FstVA  ptSh1TrdVA ptSh1SndVA idxFstVA   idxSndVA   idxTrdVA -> *)
dataStructurePdSh1Sh2asRoot idxShadow1
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
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros * Hgoal  Hindor3  Hwell1 Hlpred Hor3 Hlookup Hnblgen Hindesc Hwellmmu Hnotfst Hppx Hinmmu Hpartin Hnewnotdef.
intros.
move Hgoal at bottom.
 unfold dataStructurePdSh1Sh2asRoot in *.
intros * Hpart0 * Hpp0 * Ht * Hllv * Hind .
 assert(Hdup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition idxroot;trivial. 
  assert(Hconsdup: noDupConfigPagesList s) by trivial.
  apply Hconsdup;trivial. }
assert(Hpart : forall part, In part (getPartitions pageRootPartition s) <-> In part (getPartitions pageRootPartition s')).
intros.
unfold s'.
eapply  getPartitionsAddIndirection;trivial;try eassumption;trivial.
rewrite <- Hpart in *.
assert(Hpp': nextEntryIsPP partition0 idxShadow1 entry0 s).
apply nextEntryIsPPMapMMUPage' with indirection (StateLib.getIndexOfAddr vaToPrepare l) 
  nextIndirection r w  e;trivial.
assert(Horx: partition = partition0 \/ partition <> partition0) by apply pageDecOrNot.
destruct Horx as[Horx | Horx].
+ subst partition0.
  move Hindesc at bottom.
  destruct Hindor3 as [(Hi1 & Hi2 & Hii3) | [(Hi1 & Hi2 & Hii3) | (Hi1 & Hi2 & Hii3)] ].
  - subst.
    clear Hpart.
    move Hinmmu at bottom.
    move Hppx at bottom.
    assert(Hindeq: getIndirection entry0 va level stop s' = getIndirection entry0 va level stop s).
    { symmetry.
      apply getIndirectionMapMMUPage11 with entry;trivial.
      intros * Hi Hi1.
      assert(Hin: In tbl (getIndirections entry0 s)).
      { apply  getIndirectionInGetIndirections with va level stop0;trivial.
        apply nbLevelNotZero.
        apply beq_nat_false in Hi1;unfold not;intros ;subst;now contradict Hi1.
        rewrite getNbLevelEq with level;trivial.
        apply sh1PartNotNull with partition s;trivial. }
        apply disjointPartitionDataStructure with entry0 pd idxShadow1  idxPageDir   partition s;trivial.        
        unfold or3;right;left;trivial.
        symmetrynot.
        apply idxPDidxSh1notEq. 
        assert(Hconsdup: noDupConfigPagesList s) by trivial.
        unfold noDupConfigPagesList in *.
        apply Hconsdup in Hpart0.
        unfold getConfigPages in Hpart0.
        apply NoDup_cons_iff in Hpart0.
        intuition.
        apply sh1PartNotNull with partition s;trivial.  }
      apply wellFormedRootDataStructAddIndirection with partition va entry0 entry;trivial.
      rewrite <- Hindeq;trivial.
      apply  indirectionDescriptionNotDefault in Hindesc;trivial.
  - assert(HingetInd : In indirection (getIndirections  entry0 s)).
    { apply indirectionDescriptionInGetIndirections with partition vaToPrepare l idxShadow1;trivial.
      right;left;trivial.
      subst;trivial. } 
    unfold indirectionDescription,  initPEntryTablePreconditionToPropagatePrepareProperties in *.
    destruct Hindesc as (tableroot & Hpp & Hrootnotdef & Hor). 
    subst phySh1Child. 
    subst.
    assert (pd = entry0).
    apply getSh1NextEntryIsPPEq with partition s;trivial.
    apply nextEntryIsPPgetFstShadow;trivial.
    subst entry0 .
    assert (pd = tableroot).
    apply getSh1NextEntryIsPPEq with partition s;trivial.
    apply nextEntryIsPPgetFstShadow;trivial.
    subst tableroot.
    rewrite <- Hnblgen in Hllv.
    inversion Hllv;subst nbLgen.
    clear Hpp0.
    destruct Hor as [(Hroot & Hnbl) | (nbl & sstop & Hnbl & Hsstop & Hind1 & Hnotdef & Hl)].
    * subst.
      rewrite <- Hnblgen in Hnbl.
      inversion Hnbl;subst. 
      apply PCWellFormedDataStructAddIndirectionsh1 with va entry partition lpred;trivial.
    * rewrite <- Hnblgen in Hnbl.
      inversion Hnbl;subst.
      clear Hllv Hpp' Hpart Hnbl.
      move Hnotfst at bottom.
      move Hlpred at bottom.

      
      assert(sstop=0 \/ sstop>0) as [Horsstop0|Hsstop0] by lia.
      -- subst;simpl in *.
         inversion Hind1;subst.
         rewrite CLevelIdentity' in *. (* 
          assert(stop=0 \/ stop>0) as [Horstop0|Hstop0] by lia.
          subst.
          simpl in *.
          inversion Hind;subst indirection0. *)

         apply PCWellFormedDataStructAddIndirectionsh1 with va entry partition lpred;trivial.
         unfold s' in *;trivial.
         rewrite CLevelIdentity' in *.
         trivial.
      -- assert(stop < sstop \/ stop = sstop \/ stop>sstop) as [Hor |[Hor|Hor]] by lia.
         ** assert(Heq : getIndirection pd va level stop s' =getIndirection pd va level stop s). 
            { symmetry.
              apply getIndirectionMapMMUPage11Stoplt with entry;trivial.        
              intros.
            assert(Hin: In tbl (getIndirectionsAux pd s (stop0+1))).
            { apply getIndirectionInGetIndirections1 with va level ;trivial.
              destruct level;simpl in *.  lia.
              assert(Hx: (pageDefault =? tbl) = false) by trivial.
              apply beq_nat_false in Hx;unfold not;intros;subst;now contradict Hx. }
           assert(~In indirection (getIndirectionsAux pd s (stop0+1))).
           { apply getIndirectionInGetIndirections2n with sstop vaToPrepare level;trivial.
             destruct level;simpl in *.
             lia.
             apply noDupPreviousMMULevels with nbLevel ;trivial.
             destruct level;simpl in *.
             lia.
             lia. }
            unfold not;intros ;subst; now contradict Hin. }
            rewrite Heq in Hind.
            apply wellFormedRootDataStructAddIndirection with partition va pd entry;trivial.
         ** subst.
            assert(Hkey: ~In indirection (getIndirectionsAux pd s sstop)).
            { assert(Hex: sstop + 1 <= nbLevel).
              destruct level;simpl in *.
              lia.
              apply getIndirectionInGetIndirections2' with vaToPrepare level;trivial.
              unfold getIndirections in *.
              apply noDupPreviousMMULevels with nbLevel ;trivial. }
            assert(Heqind: getIndirection pd va level sstop s' =getIndirection pd va level sstop s). 
            {  apply getIndirectionAddIndirectionEq with entry;trivial. }
            rewrite Heqind in Hind.
            apply wellFormedRootDataStructAddIndirection with partition va pd entry;trivial.
        ** assert(Hdefind0: indirection0 = pageDefault  \/ indirection0 <> pageDefault ) by apply pageDecOrNot. 
           destruct Hdefind0 as [Hdefind0|Hdefind0].
           left;trivial.
(*            right.  *)
           assert(Hkey: ~In indirection (getIndirectionsAux pd s sstop)).
           { assert(Hex: sstop + 1 <= nbLevel).
            destruct level;simpl in *.
            lia.
            apply getIndirectionInGetIndirections2' with vaToPrepare level;trivial.
            unfold getIndirections in *.
            apply noDupPreviousMMULevels with nbLevel ;trivial.
           }
          assert(Heqind: getIndirection pd vaToPrepare level sstop s' =getIndirection pd vaToPrepare level sstop s). 
               {  apply getIndirectionAddIndirectionEq with entry;trivial. }
          assert(Heqindx: getIndirection pd va level sstop s' =getIndirection pd va level sstop s). 
                {  apply getIndirectionAddIndirectionEq with entry;trivial. }
          assert(Hi: stop <= nbLevel-1 \/ stop > nbLevel -1) by lia.
          destruct Hi as [Hi | Hi].
          +++ apply PCWellFormedRootDataStructAddIndirectionSh1 with pd lpred va  entry partition;trivial.
          +++ pose proof nbLevelNotZero.  
               assert(Hx:  (nbLevel -1) = level).
              {  rewrite  CLevelIdentity2 with (nbLevel-1).
                 symmetry.
                 rewrite getNbLevelEq with level;trivial. 
                 lia. }
              assert(Hxp: PCWellFormedRootDataStruct (nbLevel - 1) level indirection0 idx s' idxShadow1).
              apply PCWellFormedRootDataStructAddIndirectionSh1 with pd lpred va  entry partition;trivial.
              apply getIndirectionStopLevelGT2 with stop;trivial.
              lia.
              assert(level>sstop). 
              symmetry in Hnotfst.
              apply levelEqBEqNatFalse0 in Hnotfst;trivial.
              rewrite <- CLevelIdentity2 in Hnotfst.
              subst.
              lia.
              rewrite <- CLevelIdentity2 in Hnotfst.
              subst.
              lia.
              lia. lia.
              unfold PCWellFormedRootDataStruct in Hxp.
              rewrite Hx in Hxp.
              destruct Hxp as [HdefaultPage|Hxp] ; [left ; trivial|right].
              destruct Hxp as [Hxp _] ; split; trivial.
              destruct Hxp as [HContradiction|Hxp].
              { inversion HContradiction as [Hlevel _].
                contradict Hlevel.
                lia.
              }
              destruct Hxp as [_ Hxp].
              right.
              split; trivial.
              rewrite Hx in Hi.
              lia.
      - subst.
        clear Hpart.
        move Hinmmu at bottom.
        move Hppx at bottom.
        assert(Hindeq: getIndirection entry0 va level stop s' = getIndirection entry0 va level stop s).
        { symmetry.
          apply getIndirectionMapMMUPage11 with entry;trivial.
          intros * Hi Hi1.
          assert(Hin: In tbl (getIndirections entry0 s)).
          { apply  getIndirectionInGetIndirections with va level stop0;trivial.
            apply nbLevelNotZero.
            apply beq_nat_false in Hi1;unfold not;intros ;subst;now contradict Hi1.
            rewrite getNbLevelEq with level;trivial.
            apply sh1PartNotNull with partition s;trivial. }
            apply disjointPartitionDataStructure with entry0 pd idxShadow1 idxShadow2 partition s;trivial.        
            unfold or3;right;left;trivial.
            symmetrynot.
            apply idxSh2idxSh1notEq.
            assert(Hconsdup: noDupConfigPagesList s) by trivial.
            unfold noDupConfigPagesList in *.
            apply Hconsdup in Hpart0.
            unfold getConfigPages in Hpart0.
            apply NoDup_cons_iff in Hpart0.
            intuition.
            apply sh1PartNotNull with partition s;trivial.  }
          apply wellFormedRootDataStructAddIndirection with partition va entry0 entry;trivial.
          rewrite <- Hindeq;trivial.
          apply  indirectionDescriptionNotDefault in Hindesc;trivial.
+ assert(Hindeq: getIndirection entry0 va level stop s' = getIndirection entry0 va level stop s).
  { symmetry.
          apply getIndirectionMapMMUPage11 with entry;trivial.
          intros * Hi Hi1.
     assert(Hin: In tbl (getConfigPages partition0 s)).
     { assert(Hin: In tbl (getIndirections entry0 s)).
          { apply  getIndirectionInGetIndirections with va level stop0;trivial.
            apply nbLevelNotZero.
            apply beq_nat_false in Hi1;unfold not;intros ;subst;now contradict Hi1.
            rewrite getNbLevelEq with level;trivial.
            apply sh1PartNotNull with partition0 s;trivial. } 
      unfold getConfigPages.
      simpl;right.
      apply inGetIndirectionsAuxInConfigPagesSh1 with entry0;trivial.
      apply nextEntryIsPPgetFstShadow;trivial. }
     assert(Hinx: In indirection (getConfigPages partition s)).
     { unfold getConfigPages.
      simpl;right.
      apply inGetIndirectionsAuxInConfigPages with pd idxroot;trivial. }
      assert(Hkdi: configTablesAreDifferent s) by trivial. 
      unfold configTablesAreDifferent in *.
      unfold disjoint in *.
      contradict Hin.      
      apply Hkdi with partition;trivial.
      subst;trivial.
      apply sh1PartNotNull with partition0 s;trivial. }
  apply wellFormedRootDataStructAddIndirection with partition0 va entry0 entry;trivial.
  rewrite <- Hindeq;trivial.
  apply  indirectionDescriptionNotDefault in Hindesc;trivial.
Qed.

Lemma dataStructurePdSh1Sh2asRootSh2AddIndirection
s indirection nextIndirection idxroot  entry nbLgen  pd   vaToPrepare partition l lpred r w e
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr  :
dataStructurePdSh1Sh2asRoot idxShadow2 s->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
nextEntryIsPP partition idxroot pd s ->
In indirection (getIndirections pd s) ->
In partition (getPartitions pageRootPartition s) ->
(pageDefault =? nextIndirection) = false ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
consistency s -> 
isWellFormedSndShadow lpred phySh2addr s -> 
dataStructurePdSh1Sh2asRoot idxShadow2
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
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros * Hgoal  Hindor3  Hwell1 Hlpred Hor3 Hlookup Hnblgen Hindesc Hwellmmu Hnotfst Hppx Hinmmu Hpartin Hnewnotdef.
intros.
move Hgoal at bottom.
 unfold dataStructurePdSh1Sh2asRoot in *.
intros * Hpart0 * Hpp0 * Ht * Hllv * Hind .
 assert(Hdup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition idxroot;trivial. 
  assert(Hconsdup: noDupConfigPagesList s) by trivial.
  apply Hconsdup;trivial. }
assert(Hpart : forall part, In part (getPartitions pageRootPartition s) <-> In part (getPartitions pageRootPartition s')).
intros.
unfold s'.
eapply  getPartitionsAddIndirection;trivial;try eassumption;trivial.
rewrite <- Hpart in *.
assert(Hpp': nextEntryIsPP partition0 idxShadow2 entry0 s).
apply nextEntryIsPPMapMMUPage' with indirection (StateLib.getIndexOfAddr vaToPrepare l) 
  nextIndirection r w  e;trivial.
assert(Horx: partition = partition0 \/ partition <> partition0) by apply pageDecOrNot.
destruct Horx as[Horx | Horx].
+ subst partition0.
  move Hindesc at bottom.
  destruct Hindor3 as [(Hi1 & Hi2 & Hii3) | [(Hi1 & Hi2 & Hii3) | (Hi1 & Hi2 & Hii3)] ].
  - subst.
    clear Hpart.
    move Hinmmu at bottom.
    move Hppx at bottom.
    assert(Hindeq: getIndirection entry0 va level stop s' = getIndirection entry0 va level stop s).
    { symmetry.
      apply getIndirectionMapMMUPage11 with entry;trivial.
      intros * Hi Hi1.
      assert(Hin: In tbl (getIndirections entry0 s)).
      { apply  getIndirectionInGetIndirections with va level stop0;trivial.
        apply nbLevelNotZero.
        apply beq_nat_false in Hi1;unfold not;intros ;subst;now contradict Hi1.
        rewrite getNbLevelEq with level;trivial.
        apply sh2PartNotNull with partition s;trivial. }
        apply disjointPartitionDataStructure with entry0 pd idxShadow2  idxPageDir   partition s;trivial.        
        unfold or3;right;right;trivial.
        symmetrynot.
        apply idxPDidxSh2notEq. 
        assert(Hconsdup: noDupConfigPagesList s) by trivial.
        unfold noDupConfigPagesList in *.
        apply Hconsdup in Hpart0.
        unfold getConfigPages in Hpart0.
        apply NoDup_cons_iff in Hpart0.
        intuition.
        apply sh2PartNotNull with partition s;trivial.  }
      apply wellFormedRootDataStructAddIndirection with partition va entry0 entry;trivial.
      rewrite <- Hindeq;trivial.
      apply  indirectionDescriptionNotDefault in Hindesc;trivial.
 - subst.
        clear Hpart.
        move Hinmmu at bottom.
        move Hppx at bottom.
        assert(Hindeq: getIndirection entry0 va level stop s' = getIndirection entry0 va level stop s).
        { symmetry.
          apply getIndirectionMapMMUPage11 with entry;trivial.
          intros * Hi Hi1.
          assert(Hin: In tbl (getIndirections entry0 s)).
          { apply  getIndirectionInGetIndirections with va level stop0;trivial.
            apply nbLevelNotZero.
            apply beq_nat_false in Hi1;unfold not;intros ;subst;now contradict Hi1.
            rewrite getNbLevelEq with level;trivial.
            apply sh2PartNotNull with partition s;trivial. }
            apply disjointPartitionDataStructure with entry0 pd idxShadow2 idxShadow1 partition s;trivial.        
            unfold or3;right;right;trivial.
            apply idxSh2idxSh1notEq.
            assert(Hconsdup: noDupConfigPagesList s) by trivial.
            unfold noDupConfigPagesList in *.
            apply Hconsdup in Hpart0.
            unfold getConfigPages in Hpart0.
            apply NoDup_cons_iff in Hpart0.
            intuition.
            apply sh2PartNotNull with partition s;trivial.  }
          apply wellFormedRootDataStructAddIndirection with partition va entry0 entry;trivial.
          rewrite <- Hindeq;trivial.
          apply  indirectionDescriptionNotDefault in Hindesc;trivial.
  - assert(HingetInd : In indirection (getIndirections  entry0 s)).
    { apply indirectionDescriptionInGetIndirections with partition vaToPrepare l idxShadow2;trivial.
      right;right;trivial.
      subst;trivial. } 
    unfold indirectionDescription,  initPEntryTablePreconditionToPropagatePrepareProperties in *.
    destruct Hindesc as (tableroot & Hpp & Hrootnotdef & Hor). 
    subst phySh2Child. 
    subst.
    assert (pd = entry0).
    apply getSh2NextEntryIsPPEq with partition s;trivial.
    apply nextEntryIsPPgetSndShadow;trivial.
    subst entry0 .
    assert (pd = tableroot).
    apply getSh2NextEntryIsPPEq with partition s;trivial.
    apply nextEntryIsPPgetSndShadow;trivial.
    subst tableroot.
    rewrite <- Hnblgen in Hllv.
    inversion Hllv;subst nbLgen.
    clear Hpp0.
    destruct Hor as [(Hroot & Hnbl) | (nbl & sstop & Hnbl & Hsstop & Hind1 & Hnotdef & Hl)].
    * subst.
      rewrite <- Hnblgen in Hnbl.
      inversion Hnbl;subst. 
      apply PCWellFormedDataStructAddIndirectionsh2 with va entry partition lpred;trivial.
    * rewrite <- Hnblgen in Hnbl.
      inversion Hnbl;subst.
      clear Hllv Hpp' Hpart Hnbl.
      move Hnotfst at bottom.
      move Hlpred at bottom.

      
      assert(sstop=0 \/ sstop>0) as [Horsstop0|Hsstop0] by lia.
      -- subst;simpl in *.
         inversion Hind1;subst.
         rewrite CLevelIdentity' in *. (* 
          assert(stop=0 \/ stop>0) as [Horstop0|Hstop0] by lia.
          subst.
          simpl in *.
          inversion Hind;subst indirection0. *)

         apply PCWellFormedDataStructAddIndirectionsh2 with va entry partition lpred;trivial.
         unfold s' in *;trivial.
         rewrite CLevelIdentity' in *.
         trivial.
      -- assert(stop < sstop \/ stop = sstop \/ stop>sstop) as [Hor |[Hor|Hor]] by lia.
         ** assert(Heq : getIndirection pd va level stop s' =getIndirection pd va level stop s). 
            { symmetry.
              apply getIndirectionMapMMUPage11Stoplt with entry;trivial.        
              intros.
            assert(Hin: In tbl (getIndirectionsAux pd s (stop0+1))).
            { apply getIndirectionInGetIndirections1 with va level ;trivial.
              destruct level;simpl in *.  lia.
              assert(Hx: (pageDefault =? tbl) = false) by trivial.
              apply beq_nat_false in Hx;unfold not;intros;subst;now contradict Hx. }
           assert(~In indirection (getIndirectionsAux pd s (stop0+1))).
           { apply getIndirectionInGetIndirections2n with sstop vaToPrepare level;trivial.
             destruct level;simpl in *.
             lia.
             apply noDupPreviousMMULevels with nbLevel ;trivial.
             destruct level;simpl in *.
             lia.
             lia. }
            unfold not;intros ;subst; now contradict Hin. }
            rewrite Heq in Hind.
            apply wellFormedRootDataStructAddIndirection with partition va pd entry;trivial.
         ** subst.
            assert(Hkey: ~In indirection (getIndirectionsAux pd s sstop)).
            { assert(Hex: sstop + 1 <= nbLevel).
              destruct level;simpl in *.
              lia.
              apply getIndirectionInGetIndirections2' with vaToPrepare level;trivial.
              unfold getIndirections in *.
              apply noDupPreviousMMULevels with nbLevel ;trivial. }
            assert(Heqind: getIndirection pd va level sstop s' =getIndirection pd va level sstop s). 
            {  apply getIndirectionAddIndirectionEq with entry;trivial. }
            rewrite Heqind in Hind.
            apply wellFormedRootDataStructAddIndirection with partition va pd entry;trivial.
        ** assert(Hdefind0: indirection0 = pageDefault  \/ indirection0 <> pageDefault ) by apply pageDecOrNot. 
           destruct Hdefind0 as [Hdefind0|Hdefind0].
           left;trivial.
(*            right.  *)
           assert(Hkey: ~In indirection (getIndirectionsAux pd s sstop)).
           { assert(Hex: sstop + 1 <= nbLevel).
            destruct level;simpl in *.
            lia.
            apply getIndirectionInGetIndirections2' with vaToPrepare level;trivial.
            unfold getIndirections in *.
            apply noDupPreviousMMULevels with nbLevel ;trivial.
           }
          assert(Heqind: getIndirection pd vaToPrepare level sstop s' =getIndirection pd vaToPrepare level sstop s). 
               {  apply getIndirectionAddIndirectionEq with entry;trivial. }
          assert(Heqindx: getIndirection pd va level sstop s' =getIndirection pd va level sstop s). 
                {  apply getIndirectionAddIndirectionEq with entry;trivial. }
          assert(Hi: stop <= nbLevel-1 \/ stop > nbLevel -1) by lia.
          destruct Hi as [Hi | Hi].
          +++ apply PCWellFormedRootDataStructAddIndirectionSh2 with pd lpred va  entry partition;trivial.
          +++ pose proof nbLevelNotZero.  
               assert(Hx:  (nbLevel -1) = level).
              {  rewrite  CLevelIdentity2 with (nbLevel-1).
                 symmetry.
                 rewrite getNbLevelEq with level;trivial. 
                 lia. }
              assert(Hxp: PCWellFormedRootDataStruct (nbLevel - 1) level indirection0 idx s' idxShadow2).
              apply PCWellFormedRootDataStructAddIndirectionSh2 with pd lpred va  entry partition;trivial.
              apply getIndirectionStopLevelGT2 with stop;trivial.
              lia.
              assert(level>sstop). 
              symmetry in Hnotfst.
              apply levelEqBEqNatFalse0 in Hnotfst;trivial.
              rewrite <- CLevelIdentity2 in Hnotfst.
              subst.
              lia.
              rewrite <- CLevelIdentity2 in Hnotfst.
              subst.
              lia.
              lia. lia.
              unfold PCWellFormedRootDataStruct in Hxp.
              rewrite Hx in Hxp.
              destruct Hxp as [HdefaultPage|Hxp] ; [left ; trivial|right].
              destruct Hxp as [Hxp _] ; split; trivial.
              destruct Hxp as [HContradiction|Hxp].
              { inversion HContradiction as [Hlevel _].
                contradict Hlevel.
                lia.
              }
              destruct Hxp as [_ Hxp].
              right.
              split; trivial.
              rewrite Hx in Hi.
              lia.
+ assert(Hindeq: getIndirection entry0 va level stop s' = getIndirection entry0 va level stop s).
  { symmetry.
          apply getIndirectionMapMMUPage11 with entry;trivial.
          intros * Hi Hi1.
     assert(Hin: In tbl (getConfigPages partition0 s)).
     { assert(Hin: In tbl (getIndirections entry0 s)).
          { apply  getIndirectionInGetIndirections with va level stop0;trivial.
            apply nbLevelNotZero.
            apply beq_nat_false in Hi1;unfold not;intros ;subst;now contradict Hi1.
            rewrite getNbLevelEq with level;trivial.
            apply sh2PartNotNull with partition0 s;trivial. } 
      unfold getConfigPages.
      simpl;right.
      apply inGetIndirectionsAuxInConfigPagesSh2 with entry0;trivial.
      apply nextEntryIsPPgetSndShadow;trivial. }
     assert(Hinx: In indirection (getConfigPages partition s)).
     { unfold getConfigPages.
      simpl;right.
      apply inGetIndirectionsAuxInConfigPages with pd idxroot;trivial. }
      assert(Hkdi: configTablesAreDifferent s) by trivial. 
      unfold configTablesAreDifferent in *.
      unfold disjoint in *.
      contradict Hin.      
      apply Hkdi with partition;trivial.
      subst;trivial.
      apply sh2PartNotNull with partition0 s;trivial. }
  apply wellFormedRootDataStructAddIndirection with partition0 va entry0 entry;trivial.
  rewrite <- Hindeq;trivial.
  apply  indirectionDescriptionNotDefault in Hindesc;trivial.
Qed.

Lemma currentPartitionInPartitionsListAddIndirection 
s indirection nextIndirection idxroot  entry nbLgen  pd   vaToPrepare partition l lpred r w e
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr :
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
nextEntryIsPP partition idxroot pd s ->
In indirection (getIndirections pd s) ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
currentPartitionInPartitionsList s ->
currentPartitionInPartitionsList
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
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}.
Proof.
unfold currentPartitionInPartitionsList in *. 
simpl in *.
intros.
rewrite <- getPartitionsAddIndirection;trivial;try eassumption;trivial.
Qed.

Lemma getMappedPagesAuxAddIndirectionEq s indirection nextIndirection  entry nbLgen valist pd   vaToPrepare partition l r w e root idxroot
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr:
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->
partitionDescriptorEntry s ->
nextEntryIsPP partition idxroot root s ->
In indirection (getIndirections root s) -> 


In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxPageDir pd s ->
nextIndirection <> indirection ->
(getMappedPagesAux pd valist s) =
(getMappedPagesAux pd valist {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}).
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hor3 Hindor3 Hlookup Hl Hroot Hdef  Hinit Hlevel Hnodupcons Hpde Hppkey Hkey.
intros Hgoal.
intros.
assert(Hnodup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition idxPageDir ;trivial.
unfold noDupConfigPagesList in *.
apply Hnodupcons;trivial.
left;trivial. }

{
unfold indirectionDescription,  initPEntryTablePreconditionToPropagatePrepareProperties in *.
destruct Hroot as (tableroot & Hpp & Hrootnotdef & Hor).
destruct Hor3 as [Hor3 | Ho3].
+ (** MMU **) unfold getMappedPagesAux.
 assert(Hpdor: tableroot=pd).
 { subst. apply getPdNextEntryIsPPEq with partition s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
  subst tableroot.
destruct Hor as [(Heq & HnbL) | Hor].
- (** root **) subst.
  assert(Hnoneind:getIndirection indirection vaToPrepare l (nbLevel - 1) s = Some pageDefault).
  { apply getIndirectionNbLevelEq with 1;try lia.
    rewrite  getNbLevelEq with l;trivial.
    apply nbLevelEq.
    symmetry in Hlevel.
    apply levelEqBEqNatFalse0 in Hlevel.
    lia.
    simpl.
    rewrite <- Hlevel.
    assert(Hread: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault).
    trivial.
    rewrite Hread.
    rewrite <- beq_nat_refl;trivial. }
  assert(Hnone: getMappedPage indirection s vaToPrepare = NonePage).
  { unfold getMappedPage.
    rewrite <- HnbL.
    rewrite Hnoneind.
    assert(Heq: true=(pageDefault =? pageDefault)).
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
induction valist;simpl in *;trivial.
case_eq(getMappedPage indirection s a );intros * Heq1.
* case_eq(getMappedPage indirection s' a );intros * Heq2. 
  assert(Hor : StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare a l = true \/
               StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare a l = false).
  { destruct ( StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare a l);intuition. }
  destruct Hor as [Hor | Hor].
  ** (** Same virtual address : contradiction **)
    assert(Hfalse: getMappedPage indirection s a = NonePage).
    rewrite <- Hnone.
    symmetry.
    apply getMappedPageEq with l;trivial.
    symmetry;trivial.
    rewrite Hfalse in Heq1.
    now contradict Heq1.
  ** assert(Hkeymap: getMappedPage indirection s' a = SomePage p).  
     apply getMappedPageSomeAddIndirectionSamePartSSI1 with entry partition ;trivial.
    unfold indirectionDescription in *.
    exists indirection.
    split;trivial.
     split;trivial.
     left;split;trivial.
     rewrite Hkeymap in Heq2.
     inversion Heq2;subst.
     f_equal.
     trivial.
  ** assert(Hkeymap: getMappedPage indirection s' a = SomePage p).  
     apply getMappedPageSomeAddIndirectionSamePartSSI1 with entry partition ;trivial.
    unfold indirectionDescription in *.
    exists indirection.
    split;trivial.
     split;trivial.
     left;split;trivial.
     rewrite Hkeymap in Heq2.
     inversion Heq2;subst.
   ** assert(Hkeymap: getMappedPage indirection s' a = SomePage p).  
     apply getMappedPageSomeAddIndirectionSamePartSSI1 with entry partition ;trivial.
    unfold indirectionDescription in *.
    exists indirection.
    split;trivial.
     split;trivial.
     left;split;trivial.
     rewrite Hkeymap in Heq2.
     inversion Heq2;subst.
  * case_eq(getMappedPage indirection s' a );intros * Heq2;trivial.
  assert(Hor : StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare a l = true \/
               StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare a l = false).
  { destruct ( StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare a l);intuition. }
  destruct Hor as [Hor | Hor].
  ** (** Same virtual address : contradiction **)
    assert(Hfalse: getMappedPage indirection s a = NonePage).
    rewrite <- Hnone.
    symmetry.
    apply getMappedPageEq with l;trivial.
    symmetry;trivial.
    rewrite Hfalse in Heq1.
    now contradict Heq1.
  ** assert(Hkeymap: getMappedPage indirection s a = SomePage p).  
    eapply getMappedPageSomeAddIndirectionSSI2  with indirection nextIndirection entry
    nbLgen pageDefault vaToPrepare partition l r w e root idxPageDir phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;trivial.
    unfold or3;left;trivial.
    unfold indirectionDescription. 
    exists indirection;split;trivial.
    split;trivial.
    left;split;trivial.
    unfold isEntryPage, StateLib.readPhyEntry in *. rewrite Hlookup in *. inversion Hdef;subst;f_equal;apply proof_irrelevance.
    rewrite <- beq_nat_refl;trivial. 
    unfold indirectionDescription in *.
    exists indirection.
    split;trivial.
    split;trivial.
    left;split;trivial.
    rewrite Hkeymap in Heq1.
    inversion Heq1;subst.
  * case_eq(getMappedPage indirection s' a );intros * Heq2;trivial.
  assert(Hor : StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare a l = true \/
               StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare a l = false).
  { destruct ( StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare a l);intuition. }
  destruct Hor as [Hor | Hor].
  ** (** Same virtual address : contradiction **)
    assert(Hkeymap: getMappedPage indirection s a = SomePage p).  
    eapply getMappedPageSomeAddIndirectionSSI2  with indirection nextIndirection entry
    nbLgen pageDefault vaToPrepare partition l r w e root idxPageDir phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;trivial.
    unfold or3;left;trivial.
    unfold indirectionDescription. 
    exists indirection;split;trivial.
    split;trivial.
    left;split;trivial.
    unfold isEntryPage, StateLib.readPhyEntry in *. rewrite Hlookup in *. inversion Hdef;subst;f_equal;apply proof_irrelevance.
    rewrite <- beq_nat_refl;trivial. 
    unfold indirectionDescription in *.
    exists indirection.
    split;trivial.
    split;trivial.
    left;split;trivial.
    rewrite Hkeymap in Heq1.
    inversion Heq1;subst.
  ** assert(Hkeymap: getMappedPage indirection s a = SomePage p).  
    eapply getMappedPageSomeAddIndirectionSSI2  with indirection nextIndirection entry
    nbLgen pageDefault vaToPrepare partition l r w e root idxPageDir phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;trivial.
    unfold or3;left;trivial.
    unfold indirectionDescription. 
    exists indirection;split;trivial.
    split;trivial.
    left;split;trivial.
    unfold isEntryPage, StateLib.readPhyEntry in *. rewrite Hlookup in *. inversion Hdef;subst;f_equal;apply proof_irrelevance.
    rewrite <- beq_nat_refl;trivial. 
    unfold indirectionDescription in *.
    exists indirection.
    split;trivial.
    split;trivial.
    left;split;trivial.
    rewrite Hkeymap in Heq1.
    inversion Heq1;subst.
 - destruct Hor as (nbl & stop & Hnbl & Hstop & Hind & Hdef0 & Hlstop) .
   induction valist;simpl in *;trivial.
   case_eq( getMappedPage pd s a );intros * Hmap. 
   * assert(Hkeymap: getMappedPage pd s' a = SomePage p).  
     {  apply getMappedPageSomeAddIndirectionSamePartSSI1 with entry partition ;trivial.
        unfold indirectionDescription in *.
        exists pd.
        split;trivial.
        split;trivial.
        right.
        exists nbl, stop;split;trivial.
        intuition. }
        rewrite Hkeymap.
        f_equal;trivial.
     * case_eq( getMappedPage pd s' a );intros * Hmap';trivial.
       assert(Hkeymap: getMappedPage pd s a = SomePage p). 
       { eapply getMappedPageSomeAddIndirectionSSI2  with indirection nextIndirection entry
         nbLgen pageDefault vaToPrepare partition l r w e root idxPageDir phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;trivial.
          unfold or3;left;trivial.
          subst;trivial.
          unfold indirectionDescription. 
          exists pd.
          split;trivial.
          split;trivial.
          right.
          exists nbl, stop;split;trivial.
          intuition.
          unfold isEntryPage, StateLib.readPhyEntry in *. rewrite Hlookup in *. inversion Hdef;subst;f_equal;apply proof_irrelevance.
          rewrite <- beq_nat_refl;trivial.
          unfold indirectionDescription. 
          exists pd.
          split;trivial.
          split;trivial.
          right.
          exists nbl, stop;split;trivial.
          intuition.
          subst;trivial. }
        rewrite Hkeymap in Hmap.
        now contradict Hmap.
      * case_eq( getMappedPage pd s' a );intros * Hmap';trivial.
       assert(Hkeymap: getMappedPage pd s a = SomePage p). 
       { eapply getMappedPageSomeAddIndirectionSSI2  with indirection nextIndirection entry
         nbLgen pageDefault vaToPrepare partition l r w e root idxPageDir phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;trivial.
          unfold or3;left;trivial.
          subst;trivial.
          unfold indirectionDescription. 
          exists pd.
          split;trivial.
          split;trivial.
          right.
          exists nbl, stop;split;trivial.
          intuition.
          unfold isEntryPage, StateLib.readPhyEntry in *. rewrite Hlookup in *. inversion Hdef;subst;f_equal;apply proof_irrelevance.
          rewrite <- beq_nat_refl;trivial.
          unfold indirectionDescription. 
          exists pd.
          split;trivial.
          split;trivial.
          right.
          exists nbl, stop;split;trivial.
          intuition.
          subst;trivial. }
        rewrite Hkeymap in Hmap.
        now contradict Hmap.
+ unfold getMappedPagesAux.
induction valist;simpl;trivial.
assert(Heq: getMappedPage pd s a = getMappedPage pd s' a).
apply getMappedPageAddIndirectionSh1Sh2 with nbLgen partition idxroot root entry;trivial. 
rewrite <- Heq. 
rewrite IHvalist;trivial.
 } 
Qed.

Lemma getMappedPagesAuxAddIndirectionSamePartEq s indirection nextIndirection  entry nbLgen valist pd   vaToPrepare partition l r w e
idxroot
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr root:
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->

lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->


nextEntryIsPP partition idxroot root s ->
In indirection (getIndirections root s) ->
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxPageDir pd s ->
nextIndirection <> indirection ->
(getMappedPagesAux pd valist s) =
(getMappedPagesAux pd valist {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}).
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hor3 Hindor3 Hlookup Hl Hroot Hdef (* Hdef' *) Hinit Hlevel Hnodupcons.
unfold getMappedPagesAux.
intros.
assert(Hnodup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition idxPageDir ;trivial.
unfold noDupConfigPagesList in *.
apply Hnodupcons;trivial.
left;trivial. }
eapply getMappedPagesAuxAddIndirectionEq ;try eassumption ;trivial.
Qed.


 Lemma getMappedPagesAddIndirectionSamePartEq s indirection nextIndirection  entry nbLgen  (* pd *)   vaToPrepare partition l r w e
idxroot
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr root:
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->

lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->


nextEntryIsPP partition idxroot root s ->
In indirection (getIndirections root s) ->
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
(* nextEntryIsPP partition PDidx pd s -> *)
nextIndirection <> indirection ->
(getMappedPages partition  s)=
 (getMappedPages partition {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}).
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hor3 Hindor3 Hlookup Hl Hroot Hdef (* Hdef' *) Hinit Hlevel Hnodupcons.

unfold getMappedPages.
intros.
assert(Hpd:  StateLib.getPd partition (memory s) = StateLib.getPd partition (memory s')).
symmetry.
apply getPdMapMMUPage with entry;trivial.
rewrite <- Hpd.
case_eq( StateLib.getPd partition (memory s) );intros * Hp.
apply getMappedPagesAuxAddIndirectionSamePartEq with entry nbLgen partition idxroot phyPDChild phyMMUaddr
phySh1Child phySh1addr phySh2Child phySh2addr root;trivial.
apply nextEntryIsPPgetPd;trivial.
split;trivial.
Qed.

Lemma noDupConfigPagesListAddIndirection 
s indirection nextIndirection idxroot  entry nbLgen  root   vaToPrepare partition l lpred r w e
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr :
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
nextEntryIsPP partition idxroot root s ->
In indirection (getIndirections root s) ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s ->
noDupConfigPagesList s ->
noDupConfigPagesList
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
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hor3 Hwell1 Hlpred Hindor Hlookup Hnbl Hnewcons2 Hnewcons Hnoduptree Hi1 Hi2 Hi3 Hi4 Hlevel Hind (* Hdef *)
 Ha1 Ha2 Ha3 Ha4 Ha5 Hwell Hgoal.
assert(Hpart : forall part, In part (getPartitions pageRootPartition s) <-> In part (getPartitions pageRootPartition s')).
intros.
unfold s'.
eapply  getPartitionsAddIndirection;trivial;try eassumption;trivial.
unfold noDupConfigPagesList in *.
intros partx Hpartx'.
assert(Hpartx:  In partx (getPartitions pageRootPartition s)).
rewrite getPartitionsAddIndirection;trivial;try eassumption;trivial.
clear Hpartx' Hpart.
assert(Hkey: forall part, In part (getPartitions pageRootPartition s) -> 
~In nextIndirection (getConfigPages part s)). admit.
assert(Hparteq: partition = partx \/ partition <> partx) by apply pageDecOrNot.
destruct Hparteq as [Hparteq|Hparteq].
+ subst partx.
  apply Hgoal in Hpartx.
  clear Hgoal.
  assert(Hinind: In nextIndirection (getIndirections root s')) by admit.  
  assert(Hinindnot: ~In nextIndirection (getIndirections root s)) by admit.  
  unfold getConfigPages in *.  
  rewrite NoDup_cons_iff in *.
  destruct Hpartx as (Hpartx & Hnodup).
  split.   
  contradict Hpartx.
  admit. 
  unfold getConfigPagesAux.
  unfold getConfigPagesAux in Hnodup.
  assert(Hpd :forall part, In part (getPartitions pageRootPartition s) -> 
   StateLib.getPd part (memory s) = StateLib.getPd part (memory s')).
  { intros;symmetry;  apply getPdMapMMUPage with entry;trivial. }
  rewrite <- Hpd;clear Hpd;trivial.
  assert(Hpd :forall part, In part (getPartitions pageRootPartition s) -> 
  StateLib.getFstShadow part (memory s) = StateLib.getFstShadow part (memory s')).  
  { intros;symmetry;  apply getFstShadowMapMMUPage with entry;trivial. }
  rewrite <- Hpd;clear Hpd;trivial.
  assert(Hpd :forall part, In part (getPartitions pageRootPartition s) -> 
  StateLib.getSndShadow part (memory s) = StateLib.getSndShadow part (memory s')).  
  { intros;symmetry;  apply getSndShadowMapMMUPage with entry;trivial. }
  rewrite <- Hpd;clear Hpd;trivial.
  assert(Hpd :forall part, In part (getPartitions pageRootPartition s) -> 
  StateLib.getConfigTablesLinkedList part (memory s) = StateLib.getConfigTablesLinkedList part (memory s')).  
  { intros;symmetry;  apply getConfigTablesLinkedListMapMMUPage with entry;trivial. }
  rewrite <- Hpd;clear Hpd;trivial.
  case_eq(StateLib.getPd partition (memory s) );[intros pd Hpd | intros Hpd];rewrite Hpd in *; try constructor.
  case_eq(StateLib.getFstShadow partition (memory s) );[intros sh1 Hsh1 | intros Hsh1];rewrite Hsh1 in *; try constructor.
  case_eq(StateLib.getSndShadow partition (memory s) );[intros sh2 Hsh2 | intros Hsh2];rewrite Hsh2 in *; try constructor.
  case_eq(StateLib.getConfigTablesLinkedList partition (memory s) );[intros LL HLL |intros HLL];rewrite HLL in *; try constructor.
  rewrite NoDupSplitInclIff in *.
  destruct Hnodup as ((Hnodup1 & Hnodup2) & Hnodup3).
  destruct Hindor as [Hindor | Hindor].
  - subst.
    assert(root=pd).
    apply getPdNextEntryIsPPEq with partition s;trivial.
    subst.
    repeat split.
    * revert Hwell Hor3 Hnodup1 Hinind Hinindnot Hlevel Hi2.
      clear.
      unfold getIndirections.
      revert pd.
      intros.
      assert (Hsplitlist : exists nbLevelIndirection  l1 l2,
         (getIndirectionsAux pd s nbLevel = l1 ++ [indirection] ++
          flat_map (fun p => getIndirectionsAux p s nbLevelIndirection   )
          (getTablePages indirection tableSize s)++ l2)
          /\
          getIndirectionsAux pd s' nbLevel  = l1 ++ [indirection] ++
           flat_map (fun p => getIndirectionsAux p s' nbLevelIndirection   )
          (getTablePages indirection tableSize s')++ l2) .
        { admit.  }
      destruct Hsplitlist as ( nbLevelIndirection &  l11 & l22 & Hsplitlist).
      destruct Hsplitlist as (Hsplitlist1 & Hsplitlist2).    
      assert(HchildrenS : exists l1 l2,
       getTablePages indirection tableSize s' = l1 ++ [nextIndirection] ++ l2 /\
       getTablePages indirection tableSize s = l1 ++l2).
      { admit. }
      destruct HchildrenS as (l1 & l2 & HchildrenS & Hchildrenprev).
      assert(Hnodupchildren : NoDup (getTablePages indirection tableSize s')) by admit.    
      assert(Hmappednull : getTablePages nextIndirection tableSize s' = nil) by admit.
      rewrite Hsplitlist1 in Hnodup1. (* ;clear Hsplitlist1. *)
      rewrite Hsplitlist2. (* ;clear Hsplitlist2. *)
      move Hsplitlist2 at top.
      move Hsplitlist1 at top.
      rewrite NoDupSplitInclIff.
      rewrite NoDupSplitInclIff in Hnodup1.
      destruct Hnodup1 as (Hnodup1 & Hnodup2).
      destruct Hnodup1 as (Hnodup1 & Hnodup3).
      simpl in *.
      rewrite NoDup_cons_iff in Hnodup3.
      destruct Hnodup3 as (Hnodup3 & Hnodup4).
      assert(Hzero : getIndirectionsAux nextIndirection s' nbLevelIndirection  = [nextIndirection] \/
        getIndirectionsAux nextIndirection s' nbLevelIndirection = [] ).
      { admit. }
      split.
      ++ split. 
         intuition.
         constructor.
         -- rewrite in_app_iff in *.
          apply Classical_Prop.not_or_and in Hnodup3 as (Hnodup3 & Hnodup5).
          apply Classical_Prop.and_not_or.
          split;trivial.
          rewrite  HchildrenS.
          rewrite Hchildrenprev in Hnodup3.
          rewrite flat_map_app_cons.
          rewrite flat_map_app in Hnodup3.
          rewrite in_app_iff in Hnodup3.
           apply Classical_Prop.not_or_and in Hnodup3 as (Hnodup3 & Hnodup6).
          rewrite in_app_iff.
          apply Classical_Prop.and_not_or.
          rewrite in_app_iff.
          split.
          contradict Hnodup3.
          ** rewrite in_flat_map in *.
             destruct Hnodup3 as (child & Hancestor1 & Hancestor2).
             exists child;split;trivial.
             assert(Hget : getIndirectionsAux child s nbLevelIndirection = 
             getIndirectionsAux child s' nbLevelIndirection) by admit. 
             trivial. 
             rewrite Hget;trivial.
          ** apply Classical_Prop.and_not_or.
            split.
            simpl.
            rewrite app_nil_r.
            destruct Hzero as [Hzero | Hzero]; rewrite Hzero.
            simpl.
            intuition.
            intuition.
            contradict Hnodup6.
            rewrite in_flat_map in *.
            destruct Hnodup6 as (child & Hancestor1 & Hancestor2).
            exists child;split;trivial.
            assert(Hget : getIndirectionsAux child s nbLevelIndirection = 
               getIndirectionsAux child s' nbLevelIndirection) by admit. 
            trivial. 
            rewrite Hget;trivial.
        -- rewrite NoDupSplitInclIff in *.
destruct Hnodup4 as ((Hnodup4 & Hnodup5) & Hnodup6).
split.
**  split;trivial.
rewrite HchildrenS.
rewrite Hchildrenprev in Hnodup4.
rewrite flat_map_app_cons.
rewrite flat_map_app in Hnodup4.
rewrite NoDupSplitInclIff in *.
destruct Hnodup4 as ((Hnodup4 & Hnodup7) & Hnodup8).
split.
--- split.
+++
{
assert(Hp1 : forall a , In a l1 ->  In a (getIndirections pd s)) by admit. 
assert(Hp2 : forall a , In a l1 -> 
~ In indirection (getIndirectionsAux a s nbLevelIndirection)) by admit. 
assert(Hp3 : forall a, In a l1 -> 
In a (getTablePages indirection tableSize s)) by admit. 
assert(Hp5 : incl l1 (getTablePages indirection tableSize s)).
rewrite Hchildrenprev. intuition.
assert(Hp6 : incl l1 (getTablePages indirection tableSize s')). 
rewrite HchildrenS. intuition. 
clear Hnodup8 HchildrenS Hchildrenprev.
induction l1.
simpl;trivial.
simpl.
apply NoDupSplitInclIff.
simpl in Hnodup4.
apply NoDupSplitInclIff in Hnodup4.
split.
split.
assert(Ha : getIndirectionsAux a s' nbLevelIndirection =getIndirectionsAux a s nbLevelIndirection) by admit. 
 rewrite Ha.
 intuition.
 apply IHl1.
 intuition.
 intros.
 apply Hp1.
 simpl.
 right;trivial.
 intros.
 apply Hp2;right;trivial.
 intros.
 apply Hp3;right;trivial.
 intros. (* 
 apply Hp4;right;trivial. *)
 unfold incl in *.
 intros. apply Hp5. simpl. right;trivial.
 unfold incl in *.
 intros. apply Hp6. simpl. right;trivial.   
 clear IHl1. 
destruct Hnodup4 as ((Hnodup4 & Hnodup9) & Hnodup10).
unfold disjoint in Hnodup10.
unfold disjoint.
intros x Hx.
 assert(Htrue : 
   getIndirectionsAux a s nbLevelIndirection =getIndirectionsAux a s' nbLevelIndirection
   ) by admit.
 rewrite <- Htrue in *. 
  apply Hnodup10 in Hx.
  contradict Hx.            

{      rewrite in_flat_map in *.
     destruct Hx as (child & Hancestor1 & Hancestor2).
     exists child;split;trivial.
     assert(Hget :getIndirectionsAux child s nbLevelIndirection = 
    getIndirectionsAux child s' nbLevelIndirection).
     { admit. }
      trivial. 
    rewrite Hget;trivial. } }
    +++
    simpl.
rewrite app_nil_r.
apply NoDupSplitInclIff.
split.
split. 
simpl.
destruct Hzero as [Hzero | Hzero]; rewrite Hzero.
 constructor;intuition.
 
 constructor. constructor.
{ assert(Hp1 : forall a , In a l2 ->  In a (getIndirections pd s)) by admit. 
assert(Hp2 : forall a , In a l2 -> 
~ In indirection (getIndirectionsAux a s nbLevelIndirection)) by admit. 
assert(Hp3 : forall a, In a l2 -> 
In a (getTablePages indirection tableSize s)) by admit. 
assert(Hp5 : incl l2 (getTablePages indirection tableSize s)).
rewrite Hchildrenprev. intuition.
assert(Hp6 : incl l2 (getTablePages indirection tableSize s')). 
rewrite HchildrenS. intuition. 
clear Hnodup8 HchildrenS Hchildrenprev.
induction l2.
simpl;trivial.
simpl.
apply NoDupSplitInclIff.
simpl in Hnodup7.
apply NoDupSplitInclIff in Hnodup7.
split.
split.
assert(Ha : getIndirectionsAux a s' nbLevelIndirection =getIndirectionsAux a s nbLevelIndirection) by admit. 
 rewrite Ha.
 intuition.
 apply IHl2.
 intuition.
 intros.
 apply Hp1.
 simpl.
 right;trivial.
 intros.
 apply Hp2;right;trivial.
 intros.
 apply Hp3;right;trivial.
 intros. (* 
 apply Hp4;right;trivial. *)
 unfold incl in *.
 intros. apply Hp5. simpl. right;trivial.
 unfold incl in *.
 intros. apply Hp6. simpl. right;trivial.   
 clear IHl2. 
destruct Hnodup7 as ((Hnodup7 & Hnodup9) & Hnodup10).
unfold disjoint in Hnodup10.
unfold disjoint.
intros x Hx.
 assert(Htrue : 
   getIndirectionsAux a s nbLevelIndirection =getIndirectionsAux a s' nbLevelIndirection
   ) by admit.
 rewrite <- Htrue in *. 
  apply Hnodup10 in Hx.
  contradict Hx.            

{      rewrite in_flat_map in *.
     destruct Hx as (child & Hancestor1 & Hancestor2).
     exists child;split;trivial.
     assert(Hget :getIndirectionsAux child s nbLevelIndirection = 
    getIndirectionsAux child s' nbLevelIndirection).
     { admit. }
      trivial. 
    rewrite Hget;trivial. } }
 destruct Hzero as [Hzero | Hzero]; rewrite Hzero.
unfold disjoint. 
 simpl.
intros x Hx.
destruct Hx as [Hx | Hx]; try now contradict  Hx.
   subst x.
   clear Hzero.
   rewrite in_flat_map.
   unfold not;intros Hfalse.
   destruct Hfalse as (x & Hx & Hxx).
   contradict Hxx.
    
 assert(Htrue : 
   getIndirectionsAux x s nbLevelIndirection =getIndirectionsAux x s' nbLevelIndirection
   ) by admit.     trivial. 
    rewrite <- Htrue;trivial.
  assert (Hicl : incl (getIndirectionsAux x s nbLevelIndirection) (getIndirections pd s)) by admit.
  assert (Hnotintree : ~ In nextIndirection (getIndirections pd s)) by admit.
      contradict Hnotintree.
      unfold incl in Hicl.
      apply Hicl;trivial.
      unfold disjoint.
      intros. 
      intuition.
---

unfold disjoint.
intros x Hdisjoint.
rewrite in_app_iff.
apply Classical_Prop.and_not_or.

split.
+++ 
 simpl.
 rewrite app_nil_r.
 destruct Hzero as [Hzero | Hzero]; rewrite Hzero.
 simpl.
 apply Classical_Prop.and_not_or.
 split;[|intuition].
     unfold not;intros Hfalse.
   subst x.
  rewrite in_flat_map in Hdisjoint.
   destruct Hdisjoint as (x & Hx & Hxx).
   contradict Hxx.
    
 
 
 assert(Htrue : 
   getIndirectionsAux x s nbLevelIndirection =getIndirectionsAux x s' nbLevelIndirection
   ) by admit. 
      trivial. 
    rewrite <- Htrue;trivial.
    assert (Hicl : incl (getIndirectionsAux x s nbLevelIndirection) (getIndirections pd s)) by admit.
 assert (Hnotintree : ~ In nextIndirection (getIndirections pd s)) by admit.
      contradict Hnotintree.
      unfold incl in Hicl.
      apply Hicl;trivial.
      unfold disjoint.
      intros. 
      intuition.
+++  
unfold disjoint in Hnodup8.
assert(Hpre : In x (flat_map (fun p : page => getIndirectionsAux p s nbLevelIndirection) l1)). 
rewrite in_flat_map in *.
destruct Hdisjoint as (x0 & Hx0 & Hx00).
exists x0; split;trivial.
assert(Htrue : 
   getIndirectionsAux x0 s nbLevelIndirection =getIndirectionsAux x0 s' nbLevelIndirection
   ) by admit. 
   
      trivial.
   
       
    rewrite  Htrue;trivial.
       apply Hnodup8 in Hpre.
       contradict Hpre.
 rewrite in_flat_map in *.
destruct Hpre as (x0 & Hx0 & Hx00).
exists x0; split;trivial.
 assert(Htrue : 
   getIndirectionsAux x0 s nbLevelIndirection =getIndirectionsAux x0 s' nbLevelIndirection
   ) by admit. 

      trivial.
   
       
    rewrite  Htrue;trivial.
    **
     unfold disjoint.
 unfold disjoint in Hnodup6.
intros x Hdisjoint.

rewrite HchildrenS in Hdisjoint.
rewrite flat_map_app_cons in Hdisjoint.
rewrite in_app_iff in Hdisjoint.
destruct Hdisjoint as [ Hdisjoint | Hdisjoint].
 +++
apply Hnodup6.
rewrite Hchildrenprev.
rewrite flat_map_app.
apply in_app_iff.
left.
rewrite in_flat_map in *.
destruct Hdisjoint as (x0 & Hx0 & Hx00).
exists x0; split;trivial.
 assert(Htrue : 
   getIndirectionsAux x0 s nbLevelIndirection =getIndirectionsAux x0 s' nbLevelIndirection
   ) by admit. 
      trivial.
   
rewrite Htrue;trivial.
 +++ rewrite in_app_iff in Hdisjoint.
destruct Hdisjoint as [ Hdisjoint | Hdisjoint].
--- simpl in *.
  rewrite app_nil_r in Hdisjoint.
 destruct Hzero as [Hzero | Hzero]; rewrite Hzero in *.
*** simpl in *.
intuition.
subst x.


    assert (Hicl : incl l22 (getIndirections pd s)).
    { unfold getIndirections.
    rewrite Hsplitlist1.
    intuition.
 }
    assert (Hnotintree : ~ In nextIndirection (getIndirections pd s)) by admit.

      contradict Hnotintree.
      unfold incl in Hicl.
      apply Hicl;trivial.
*** now contradict Hdisjoint.
---   apply Hnodup6.
rewrite Hchildrenprev.
rewrite flat_map_app.
apply in_app_iff.
right.
rewrite in_flat_map in *.
destruct Hdisjoint as (x0 & Hx0 & Hx00).
exists x0; split;trivial.
  assert(Htrue : 
   getIndirectionsAux x0 s nbLevelIndirection =getIndirectionsAux x0 s' nbLevelIndirection
   ) by admit. 
      trivial.
   
rewrite Htrue;trivial.
++
rewrite HchildrenS. 
      unfold disjoint.
      intros x Hx.
      simpl.
  
     
apply Classical_Prop.and_not_or.

unfold consistency in *.
assert(Hnoduptree : NoDup (getIndirections pd s)) by admit.
unfold getIndirections in Hnoduptree.
rewrite  Hsplitlist1 in Hnoduptree.
apply NoDupSplitInclIff in Hnoduptree.
destruct Hnoduptree as ((Hnodup8 & Hnodup9) &Hnodup10).
unfold disjoint in Hnodup10.
split. 
** apply Hnodup10 in Hx. clear Hnodup10.
simpl in *.
apply Classical_Prop.not_or_and in Hx as (Hnodup11 & Hnodup12).

trivial.
**
rewrite in_app_iff.
apply Classical_Prop.and_not_or.
split;trivial.
--
rewrite flat_map_app_cons.
simpl.

rewrite app_nil_r.
rewrite in_app_iff.
apply Classical_Prop.and_not_or.
split;trivial.  
+++ apply Hnodup10 in Hx. clear Hnodup10.
simpl in *.
apply Classical_Prop.not_or_and in Hx as (Hnodup11 & Hnodup12).

rewrite in_app_iff in Hnodup12.
apply Classical_Prop.not_or_and in Hnodup12 as (Hnodup12 & Hnodup13).
rewrite Hchildrenprev in Hnodup12.
rewrite flat_map_app in Hnodup12.
rewrite in_app_iff in Hnodup12.
apply Classical_Prop.not_or_and in Hnodup12 as 
(Hnodup12 & Hnodup14).
contradict Hnodup12.
rewrite in_flat_map in *.
destruct Hnodup12 as (x0 & Hx0 & Hx00).
exists x0; split;trivial.
   assert(Htrue : 
   getIndirectionsAux x0 s nbLevelIndirection =getIndirectionsAux x0 s' nbLevelIndirection
   ) by admit. 


      trivial.
   
rewrite Htrue;trivial.
+++  simpl. rewrite in_app_iff.
 apply Classical_Prop.and_not_or.
split;trivial.
***
destruct Hzero as [Hzero | Hzero]; rewrite Hzero in *.
simpl in *.
intuition.
subst x.


    assert (Hicl : incl l11 (getIndirections pd s)).
    { unfold getIndirections.
    rewrite Hsplitlist1.
    intuition.
 }
    assert (Hnotintree : ~ In nextIndirection (getIndirections pd s)) by admit.
      contradict Hnotintree.
      unfold incl in Hicl.
      apply Hicl;trivial.
 intuition.
*** apply Hnodup10 in Hx. clear Hnodup10.
simpl in *.
apply Classical_Prop.not_or_and in Hx as (Hnodup11 & Hnodup12).

rewrite in_app_iff in Hnodup12.
apply Classical_Prop.not_or_and in Hnodup12 as (Hnodup12 & Hnodup13).
rewrite Hchildrenprev in Hnodup12.
rewrite flat_map_app in Hnodup12.
rewrite in_app_iff in Hnodup12.
apply Classical_Prop.not_or_and in Hnodup12 as 
(Hnodup12 & Hnodup14).
contradict Hnodup14.
rewrite in_flat_map in *.
destruct Hnodup14 as (x0 & Hx0 & Hx00).
exists x0; split;trivial.
    assert(Htrue : 
   getIndirectionsAux x0 s nbLevelIndirection =getIndirectionsAux x0 s' nbLevelIndirection
   ) by admit. 


      trivial.
   
rewrite Htrue;trivial.
-- unfold consistency in *.
assert(Hnoduptree : NoDup (getIndirections pd s)) by admit.
unfold getIndirections in Hnoduptree.
rewrite  Hsplitlist1 in Hnoduptree.
apply NoDupSplitInclIff in Hnoduptree.
destruct Hnoduptree as (_ &Hnodup11).
unfold disjoint in Hnodup11.
 apply Hnodup11 in Hx. clear Hnodup11.
simpl in *.
apply Classical_Prop.not_or_and in Hx as (Hnodup11 & Hnodup12).
rewrite in_app_iff in Hnodup12.
intuition.

        
      (** ******* with induction **** 
      induction nbLevel;simpl;intros; try now contradict Hinind.
      apply not_or_and in Hinindnot as (Hx & Hinindnot).
      destruct Hinind as [Hinind | Hinind];subst;try now contradict Hx.
      apply NoDup_cons.
      ++
      rewrite in_flat_map.
      apply NoDup_cons_iff in Hnodup1.
      destruct Hnodup1 as (Hnodup1 & Hnodup2).
      unfold not;intros Hfalse.
      destruct Hfalse as (x0 & Hx0 & Hx00).
      contradict Hx00.
      rewrite in_flat_map in Hnodup1.
      contradict Hnodup1.  
      assert(Hor: x0 = nextIndirection \/ x0 <> nextIndirection) by apply pageDecOrNot.
      destruct Hor as [Hor | Hor].
      -- subst.
      rewrite in_flat_map in Hinindnot.
      assert(Hkeyi: (getIndirectionsAux nextIndirection s' n) = nil). admit.
      rewrite Hkeyi in *.
      now contradict Hnodup1.
      -- exists x0.
         split.
         clear Hnodup1.
       ** eapply getTablePagesAddIndirection;try eassumption;trivial.
       ** unfold s' in *.
       eapply getIndirectionsAuxAddIndirectionSameStructure;
       try eassumption;trivial.
       intuition.
     ++ destruct Hi2 as [Hi2 | Hi2].
        -- subst. admit. 
        --  rewrite in_flat_map in Hi2.
          destruct Hi2 as (x1 & Hx1 & Hx11).
        assert((getTablePages pd tableSize s') = (getTablePages pd tableSize s)) by admit. 
        rewrite H.
        clear H.
         admit.  *)
     *
        
 
Admitted.


Lemma consistencyAddIndirection
s indirection nextIndirection  entry nbLgen  pd idxroot  
(vaToPrepare vaNextInd : vaddr) phyDescChild l  
(currentPart currentPD ptMMUvaNextInd ptSh1VaNextInd: page) root r w e phyPDChild phyMMUaddr phySh1Child 
  phySh1addr phySh2Child phySh2addr lpred:
newIndirectionsAreNotMappedInChildrenAll s currentPart phyMMUaddr phySh1addr phySh2addr -> 
  consistency s ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child 
  phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedSndShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
(forall parts, In parts (getPartitions pageRootPartition s) ->
   ~ In nextIndirection (getAccessibleMappedPages parts s)) -> 
kernelDataIsolation s ->   
initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
verticalSharing s ->
In phyDescChild (getChildren currentPart s) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s phyDescChild indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s -> *)
(* (defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault->
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
nextEntryIsPP phyDescChild idxPageDir pd s ->
writeAccessibleRecPreparePostcondition currentPart nextIndirection s ->
In currentPart (getPartitions pageRootPartition s) ->
getTableAddrRoot ptMMUvaNextInd idxPageDir currentPart vaNextInd s->
isPE ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) s->
entryUserFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) false s ->
entryPresentFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) true s ->
nextEntryIsPP currentPart idxPageDir currentPD s ->
(pageDefault =? ptMMUvaNextInd) = false ->
isEntryPage ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) nextIndirection s ->
(* (exists va : vaddr,
  isEntryVA ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) va s /\ beqVAddr defaultVAddr va = true)-> *)
(pageDefault =? ptSh1VaNextInd) = false ->
getTableAddrRoot ptSh1VaNextInd idxShadow1 currentPart vaNextInd s ->
isVE ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) s ->

noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In phyDescChild (getPartitions pageRootPartition s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP phyDescChild idxroot root s ->
In indirection (getIndirections root s)-> 
In indirection (getConfigPages phyDescChild s) ->
isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s  ->
consistency
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
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}.
Proof.
intros * Hnotshared Hiso Hindor3 Hwell1 Hlpred Hor3 Hnotacces Hkdi (Hnotconf1 & Hnotconf2 & Hnotconf3).
intros. 
set(s':={|currentPartition:= _ |}) in *.
unfold consistency, isWellFormedTables in *. 
intuition.
+ (** partitionDescriptorEntry **)
 eapply partitionDescriptorEntryAddIndirection with (phySh1addr:=phySh1addr);trivial;try eassumption;trivial.
+ (** dataStructurePdSh1Sh2asRoot **)
 eapply dataStructurePdSh1Sh2asRootMMUAddIndirection;trivial;try eassumption;trivial.
 unfold consistency ;intuition.
+ (** dataStructurePdSh1Sh2asRoot **)
 eapply dataStructurePdSh1Sh2asRootSh1AddIndirection;trivial;try eassumption;trivial.
 unfold consistency ;intuition.
+ (** dataStructurePdSh1Sh2asRoot **)
 eapply dataStructurePdSh1Sh2asRootSh2AddIndirection;trivial;try eassumption;trivial.
 unfold consistency ;intuition.
+ (** currentPartitionInPartitionsList **)
 eapply currentPartitionInPartitionsListAddIndirection;trivial;try eassumption;trivial.
+ (** noDupMappedPagesList**)
 (* eapply noDupMappedPagesListAddIndirection;trivial;try eassumption;trivial.
+  *)

Admitted.

    
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
                 pa := nextIndirection |}) (memory s) pageEq idxEq |} ptMMUTrdVA phySh2addr
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
  + assert(Hi: indirectionDescription s descChildphy phyPDChild idxPageDir vaToPrepare l) 
    by (  unfold indirectionDescriptionAll in *; intuition).
    unfold indirectionDescription in *.
    destruct Hi as (root &Hroot & Hrootdef & Horx).
    destruct Horx as [(Heq & Horx)|Horx];subst.
    - apply fstIndirectionContainsPENbLevelGT1  with  idxPageDir l  vaToPrepare descChildphy ;trivial.
      symmetry;trivial.
    - apply middleIndirectionsContainsPE  with  idxPageDir l root vaToPrepare descChildphy ;trivial.
      symmetry;trivial.
  + assert(Hi: indirectionDescription s descChildphy phySh1Child idxShadow1 vaToPrepare l) 
    by (  unfold indirectionDescriptionAll in *; intuition).
    unfold indirectionDescription in *.
    destruct Hi as (root &Hroot & Hrootdef & Horx).
    destruct Horx as [(Heq & Horx)|Horx];subst.
    - apply fstIndirectionContainsPENbLevelGT1  with  idxShadow1 l  vaToPrepare descChildphy ;trivial.
      symmetry;trivial.
    - apply middleIndirectionsContainsPE  with  idxShadow1 l root vaToPrepare descChildphy ;trivial.
      symmetry;trivial.
   + assert(Hi: indirectionDescription s descChildphy phySh2Child idxShadow2 vaToPrepare l) 
    by (  unfold indirectionDescriptionAll in *; intuition).
    unfold indirectionDescription in *.
    destruct Hi as (root &Hroot & Hrootdef & Horx).
    destruct Horx as [(Heq & Horx)|Horx];subst.
    - apply fstIndirectionContainsPENbLevelGT1  with  idxShadow2 l  vaToPrepare descChildphy ;trivial.
          symmetry;trivial.
    - apply middleIndirectionsContainsPE  with  idxShadow2 l root vaToPrepare descChildphy ;trivial.
          symmetry;trivial. }   
assert(Hlookup: exists entry, lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry)). 
{ unfold isPE  in Hep.
  case_eq(lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq);intros * Hlookup;
  rewrite Hlookup in *;try now contradict Hep.
  destruct v;try now contradict Hep.
  exists p;trivial. }
destruct Hlookup as (entry & Hlookup).
assert( exists pdchild, nextEntryIsPP descChildphy idxPageDir pdchild s) as(pdchild & Hpdchild).
{ assert(Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
  unfold partitionDescriptorEntry in *.
  assert(Hchildpart: In descChildphy (getPartitions pageRootPartition s) ) by intuition.
  generalize (Hpde descChildphy Hchildpart idxPageDir);clear Hpde;intros Hpde.
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
     apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l idxPageDir;subst;trivial.
     apply nextEntryIsPPgetPd;trivial. 
    + intuition;subst.
     apply in_app_iff.
     right.
     apply in_app_iff.
     left.
     apply indirectionDescriptionInGetIndirections  with descChildphy vaToPrepare l idxShadow1;subst;trivial.
     apply nextEntryIsPPgetFstShadow;trivial.
     + intuition;subst.
     apply in_app_iff.
     right.
     apply in_app_iff.
     right.
     apply in_app_iff.
     left.
     apply indirectionDescriptionInGetIndirections  with descChildphy vaToPrepare l idxShadow2;subst;trivial.
     apply nextEntryIsPPgetSndShadow;trivial.
       }     
  assert(Haccessnotconfig: forall part, In part (getPartitions pageRootPartition s) ->
   ~In nextIndirection (getConfigPages part s)). 
   { destruct Hor as[(Hi1&Hi2&Hi3) |[(Hi1&Hi2&Hi3) | (Hi1&Hi2&Hi3)]];subst;
     assert(Hcons: initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr ) by intuition;
     unfold initPEntryTablePreconditionToPropagatePreparePropertiesAll in *;
     unfold initPEntryTablePreconditionToPropagatePrepareProperties in *; 
   intuition. }
   assert(Hchildpart:  In descChildphy (getPartitions pageRootPartition s)) by intuition.
  apply Haccessnotconfig in Hchildpart.
  assert(forall parts : page,
In parts (getPartitions pageRootPartition s) -> ~ In nextIndirection (getAccessibleMappedPages parts s)).
{   unfold newIndirectionsAreNotAccessible in *.
  assert(Hnotacces: newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr) by intuition.
unfold newIndirectionsAreNotAccessible in *.
  intros.
  apply Hnotacces;trivial.
  unfold nextIndirectionsOR in *.
  move Hor at bottom.
  intuition.
}
assert(Hread: StateLib.readPhyEntry phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault).
    {       intuition;subst.
      assert((pageDefault =? indMMUToPrepare) = true /\ isEntryPage phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s) as (Hi1 & Hi2).
      split;intuition.
      apply beq_nat_true in Hi1.
      unfold isEntryPage, StateLib.readPhyEntry in *.

      case_eq(lookup phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) 
    (memory s) pageEq idxEq);intros * Hlook;rewrite Hlook in *;try now contradict Hi1.
    destruct v;try now contradict Hi1.
      f_equal. destruct pageDefault;destruct indMMUToPrepare;simpl in *;subst. rewrite Hi2;f_equal;apply proof_irrelevance. }
unfold indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll in *;intuition;subst;trivial.
+ (** kernelDataIsolation **) 
apply toApplykernelDataIsolationAddIndirection with ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
phyMMUaddr phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
currentShadow1 descChildphy phySh1Child (currentPartition s) trdVA nextVA sndVA fstVA nbLgen 
(StateLib.getIndexOfAddr fstVA levelMin) (StateLib.getIndexOfAddr sndVA levelMin) (StateLib.getIndexOfAddr trdVA levelMin)
 (CIndex 0) lpred fstLL LLChildphy lastLLTable idxroot entry pdchild;trivial.
  unfold insertEntryIntoLLPC, propagatedPropertiesPrepare,  indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll ;intuition;subst;trivial.
+ (** partitionsIsolation *)
  eapply toApplyPartitionsIsolationAddIndirection  with ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
phyMMUaddr phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
currentShadow1 descChildphy phySh1Child (currentPartition s) trdVA nextVA sndVA fstVA nbLgen 
(StateLib.getIndexOfAddr fstVA levelMin) (StateLib.getIndexOfAddr sndVA levelMin) (StateLib.getIndexOfAddr trdVA levelMin)
 (CIndex 0) lpred fstLL LLChildphy lastLLTable idxroot entry pdchild;trivial.
 unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll ;intuition;subst;trivial.
+ (** verticalSharing *)
 eapply toApplyVerticalSharingAddIndirection  with ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
phyMMUaddr phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
currentShadow1 descChildphy phySh1Child (currentPartition s) trdVA nextVA sndVA fstVA nbLgen 
(StateLib.getIndexOfAddr fstVA levelMin) (StateLib.getIndexOfAddr sndVA levelMin) (StateLib.getIndexOfAddr trdVA levelMin)
 (CIndex 0) lpred fstLL LLChildphy lastLLTable idxroot entry pdchild;trivial.
 unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll ;intuition;subst;trivial.
+ (** Consistency *)

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
  MAL.writePhyEntry phyPDChild idxToPrepare phyMMUaddr true true true true true
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

