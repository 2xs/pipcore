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

 Lemma toApplykernelDataIsolationAddIndirection indirection nextIndirection ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
 phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (* idxToPrepare *) e w r idxroot entry pdchild s:
(forall part : page, In part (getPartitions multiplexer s) -> ~In nextIndirection (getConfigPages part s)) ->
~ In nextIndirection (getConfigPages descChildphy s) ->
In indirection (getConfigPages descChildphy s) ->
StateLib.readPhyEntry phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some defaultPage ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot->  
or3 idxroot ->
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) true ->
 lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex =
          Some (PE entry) ->
nextEntryIsPP descChildphy PDidx pdchild s ->          
(forall parts : page,
     In parts (getPartitions multiplexer s) -> ~In nextIndirection (getAccessibleMappedPages parts s)) ->

kernelDataIsolation
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
              (memory s) beqPage beqIndex |}.
Proof.              
intros Haccessnotconfig Hchildpart Hconfig Hread.
  unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, consistency, indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll.
intuition.
  unfold nextIndirectionsOR in *;intuition;subst;trivial.
  - 
    apply kernelDataIsolationAddIndirection with entry nbLgen pdchild PDidx fstVA descChildphy (currentPartition s)
      currentPD ptMMUFstVA ptSh1FstVA pdchild phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.       
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
    * assert(Hl: false = StateLib.Level.eqb l fstLevel) by trivial.
      assert(Hwellx: wellFormedShadows sh1idx s) by trivial.
      unfold wellFormedShadows in Hwellx.
      assert(Hi:  indirectionDescription s descChildphy phySh1Child sh1idx vaToPrepare l) by trivial.
      assert(Hii:  indirectionDescription s descChildphy phyPDChild PDidx vaToPrepare l) by trivial.
      unfold indirectionDescription in *.
      destruct Hi as (root &Hroot & Hrootdef & Horx).
      destruct Hii as (rootpd &Hrootpd & Hrootdefpd & Horxpd).
      destruct Horx as [(Heq & Horx)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)];subst.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)].
         ** subst.
            assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare l 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
            { apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
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
           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
            simpl in *. omega.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst.
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    omega. }
           subst;simpl in *.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare nbL 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = StateLib.Level.eqb nbL fstLevel) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
            simpl in *. omega.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst. 
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    omega. }
            subst;simpl in *.
            inversion Hind;subst root.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare nbL 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = StateLib.Level.eqb nbL fstLevel) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
           omega.
           apply CLevelIdentity2 in Hx.
           symmetry in Hx.
           rewrite  Hlll1 in Hx.
           assert(Hxx: nbL - stop1 < nbLevel).
           destruct nbL;simpl in *.
           omega.
           apply CLevelIdentity2 in Hxx.
           rewrite Hx in Hxx.
           omega.
 }

           subst stop1.
           
           pose proof nbLevelNotZero.
           assert(Hor: stop = nbL \/ stop < nbL) by omega.
           destruct Hor as [Hor | Hor].
           subst.
           unfold StateLib.Level.eqb in Hl.
            contradict Hl.
            unfold CLevel.
            case_eq(lt_dec (nbL - nbL) nbLevel);intros.
            simpl.
            unfold fstLevel.
            unfold CLevel.
            case_eq(lt_dec 0 nbLevel);intros * Hvv.
            simpl.
            replace (nbL - nbL) with 0 by omega.
            rewrite <- beq_nat_refl.
            auto.
            omega.
            omega.
           assert ( exists indirection2 : page,
            getIndirection root vaToPrepare nbL (stop+1) s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy rootpd defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              apply getIndirectionStopS1 with phyPDChild;trivial.
              omega.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
            
            apply getIndirectionStopSRead with root;trivial.
            omega.
            apply beq_nat_true in Htrue.
            destruct ind2; destruct defaultPage;simpl in *; inversion Htrue;subst;trivial.
            rewrite Hind2.
            f_equal.
            f_equal.
            apply proof_irrelevance.
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
    * assert(Hl: false = StateLib.Level.eqb l fstLevel) by trivial.
      assert(Hwellx: wellFormedShadows sh2idx s) by trivial.
      unfold wellFormedShadows in Hwellx.
      assert(Hi:  indirectionDescription s descChildphy phySh2Child sh2idx vaToPrepare l) by trivial.
      assert(Hii:  indirectionDescription s descChildphy phyPDChild PDidx vaToPrepare l) by trivial.
      unfold indirectionDescription in *.
      destruct Hi as (root &Hroot & Hrootdef & Horx).
      destruct Hii as (rootpd &Hrootpd & Hrootdefpd & Horxpd).
      destruct Horx as [(Heq & Horx)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)];subst.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)].
         ** subst.
            assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare l 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
            { apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
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
           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
            simpl in *. omega.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst.
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    omega. }
           subst;simpl in *.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare nbL 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = StateLib.Level.eqb nbL fstLevel) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
            simpl in *. omega.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst. 
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    omega. }
            subst;simpl in *.
            inversion Hind;subst root.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare nbL 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = StateLib.Level.eqb nbL fstLevel) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
           omega.
           apply CLevelIdentity2 in Hx.
           symmetry in Hx.
           rewrite  Hlll1 in Hx.
           assert(Hxx: nbL - stop1 < nbLevel).
           destruct nbL;simpl in *.
           omega.
           apply CLevelIdentity2 in Hxx.
           rewrite Hx in Hxx.
           omega.
 }

           subst stop1.
           
           pose proof nbLevelNotZero.
           assert(Hor: stop = nbL \/ stop < nbL) by omega.
           destruct Hor as [Hor | Hor].
           subst.
           unfold StateLib.Level.eqb in Hl.
            contradict Hl.
            unfold CLevel.
            case_eq(lt_dec (nbL - nbL) nbLevel);intros.
            simpl.
            unfold fstLevel.
            unfold CLevel.
            case_eq(lt_dec 0 nbLevel);intros * Hvv.
            simpl.
            replace (nbL - nbL) with 0 by omega.
            rewrite <- beq_nat_refl.
            auto.
            omega.
            omega.
           assert ( exists indirection2 : page,
            getIndirection root vaToPrepare nbL (stop+1) s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy rootpd defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              apply getIndirectionStopS1 with phyPDChild;trivial.
              omega.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
            
            apply getIndirectionStopSRead with root;trivial.
            omega.
            apply beq_nat_true in Htrue.
            destruct ind2; destruct defaultPage;simpl in *; inversion Htrue;subst;trivial.
            rewrite Hind2.
            f_equal.
            f_equal.
            apply proof_irrelevance. 
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault with (table := ptMMUTrdVA);trivial; try eassumption.
    * apply nextEntryIsPPgetSndShadow;trivial.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l sh2idx;subst;trivial.
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
(forall parts, In parts (getPartitions multiplexer s) ->
   ~ In nextIndirection (getAccessibleMappedPages parts s)) -> 
kernelDataIsolation s ->   
initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
verticalSharing s ->
In phyDescChild (getChildren currentPart s) ->
consistency s ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s phyDescChild indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s -> *)
(* (defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some defaultPage->
  
   
isWellFormedMMUTables phyMMUaddr s ->
false = StateLib.Level.eqb l fstLevel ->
nextEntryIsPP phyDescChild PDidx pd s ->
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
In phyDescChild (getPartitions multiplexer s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
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
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
Proof.
intros * Hnotshared Hiso Hindor3 Hwell1 Hlpred Hor3 Hnotacces Hkdi (Hnotconf1 & Hnotconf2 & Hnotconf3).
intros.
 
set(s':={|currentPartition:= _ |}) in *.
unfold partitionsIsolation in *.
simpl in *;intros * Hparent Hchild1 Hchild2 Hdist.
assert(Hpart : forall part, In part (getPartitions multiplexer s) <-> In part (getPartitions multiplexer s')).
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
assert(Hchild : In phyDescChild (getPartitions multiplexer s)) by trivial.
assert(Hnotsamepart : forall part, phyDescChild <> part -> 
In part (getPartitions multiplexer s) -> 
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
  (p = p0 \/ p = p1)) by omega.
  destruct
   H. left. 
   destruct H.
   split. 
   unfold not;intros.
   inversion H1.
   subst.
   omega.
   unfold not;intros.
   inversion H1.
   subst.
   omega.
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
(forall part : page, In part (getPartitions multiplexer s) -> ~In nextIndirection (getConfigPages part s)) ->
~ In nextIndirection (getConfigPages descChildphy s) ->
In indirection (getConfigPages descChildphy s) ->
StateLib.readPhyEntry phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some defaultPage ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot->  
or3 idxroot ->
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) true ->
 lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex =
          Some (PE entry) ->
nextEntryIsPP descChildphy PDidx pdchild s ->          
(forall parts : page,
     In parts (getPartitions multiplexer s) -> ~In nextIndirection (getAccessibleMappedPages parts s)) ->
In descChildphy (getChildren (currentPartition s) s) ->
partitionsIsolation
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
              (memory s) beqPage beqIndex |}.
Proof.              
intros Haccessnotconfig Hchildpart Hconfig Hread.
  unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, consistency, indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll.
intuition.
  unfold nextIndirectionsOR in *;intuition;subst;trivial.
  -   apply partitionsIsolationAddIndirection  with entry nbLgen pdchild PDidx fstVA descChildphy (currentPartition s) 
currentPD ptMMUFstVA ptSh1FstVA pdchild phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.       
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault;try eassumption.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l PDidx;subst;trivial.
  - pose proof pdSh1Sh2ListExistsNotNull as Hkey.
    destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
    apply partitionsIsolationAddIndirection with entry nbLgen pdchild sh1idx sndVA descChildphy (currentPartition s)
      currentPD ptMMUSndVA ptSh1SndVA sh1 phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.
    * assert(Hl: false = StateLib.Level.eqb l fstLevel) by trivial.
      assert(Hwellx: wellFormedShadows sh1idx s) by trivial.
      unfold wellFormedShadows in Hwellx.
      assert(Hi:  indirectionDescription s descChildphy phySh1Child sh1idx vaToPrepare l) by trivial.
      assert(Hii:  indirectionDescription s descChildphy phyPDChild PDidx vaToPrepare l) by trivial.
      unfold indirectionDescription in *.
      destruct Hi as (root &Hroot & Hrootdef & Horx).
      destruct Hii as (rootpd &Hrootpd & Hrootdefpd & Horxpd).
      destruct Horx as [(Heq & Horx)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)];subst.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)].
         ** subst.
            assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare l 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
            { apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
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
           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
            simpl in *. omega.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst.
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    omega. }
           subst;simpl in *.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare nbL 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = StateLib.Level.eqb nbL fstLevel) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
            simpl in *. omega.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst. 
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    omega. }
            subst;simpl in *.
            inversion Hind;subst root.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare nbL 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = StateLib.Level.eqb nbL fstLevel) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
           omega.
           apply CLevelIdentity2 in Hx.
           symmetry in Hx.
           rewrite  Hlll1 in Hx.
           assert(Hxx: nbL - stop1 < nbLevel).
           destruct nbL;simpl in *.
           omega.
           apply CLevelIdentity2 in Hxx.
           rewrite Hx in Hxx.
           omega.
 }

           subst stop1.
           
           pose proof nbLevelNotZero.
           assert(Hor: stop = nbL \/ stop < nbL) by omega.
           destruct Hor as [Hor | Hor].
           subst.
           unfold StateLib.Level.eqb in Hl.
            contradict Hl.
            unfold CLevel.
            case_eq(lt_dec (nbL - nbL) nbLevel);intros.
            simpl.
            unfold fstLevel.
            unfold CLevel.
            case_eq(lt_dec 0 nbLevel);intros * Hvv.
            simpl.
            replace (nbL - nbL) with 0 by omega.
            rewrite <- beq_nat_refl.
            auto.
            omega.
            omega.
           assert ( exists indirection2 : page,
            getIndirection root vaToPrepare nbL (stop+1) s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy rootpd defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              apply getIndirectionStopS1 with phyPDChild;trivial.
              omega.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
            
            apply getIndirectionStopSRead with root;trivial.
            omega.
            apply beq_nat_true in Htrue.
            destruct ind2; destruct defaultPage;simpl in *; inversion Htrue;subst;trivial.
            rewrite Hind2.
            f_equal.
            f_equal.
            apply proof_irrelevance.
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault with (table := ptMMUSndVA);trivial; try eassumption.
    * apply nextEntryIsPPgetFstShadow;trivial.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l sh1idx;subst;trivial.
      apply nextEntryIsPPgetFstShadow;trivial.
  - pose proof pdSh1Sh2ListExistsNotNull as Hkey.
    destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
    apply partitionsIsolationAddIndirection with entry nbLgen pdchild sh2idx trdVA descChildphy (currentPartition s)
      currentPD ptMMUTrdVA ptSh1TrdVA sh2 phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.
    * assert(Hl: false = StateLib.Level.eqb l fstLevel) by trivial.
      assert(Hwellx: wellFormedShadows sh2idx s) by trivial.
      unfold wellFormedShadows in Hwellx.
      assert(Hi:  indirectionDescription s descChildphy phySh2Child sh2idx vaToPrepare l) by trivial.
      assert(Hii:  indirectionDescription s descChildphy phyPDChild PDidx vaToPrepare l) by trivial.
      unfold indirectionDescription in *.
      destruct Hi as (root &Hroot & Hrootdef & Horx).
      destruct Hii as (rootpd &Hrootpd & Hrootdefpd & Horxpd).
      destruct Horx as [(Heq & Horx)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)];subst.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)].
         ** subst.
            assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare l 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
            { apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
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
           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
            simpl in *. omega.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst.
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    omega. }
           subst;simpl in *.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare nbL 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = StateLib.Level.eqb nbL fstLevel) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
            simpl in *. omega.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst. 
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    omega. }
            subst;simpl in *.
            inversion Hind;subst root.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare nbL 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = StateLib.Level.eqb nbL fstLevel) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
           omega.
           apply CLevelIdentity2 in Hx.
           symmetry in Hx.
           rewrite  Hlll1 in Hx.
           assert(Hxx: nbL - stop1 < nbLevel).
           destruct nbL;simpl in *.
           omega.
           apply CLevelIdentity2 in Hxx.
           rewrite Hx in Hxx.
           omega.
 }

           subst stop1.
           
           pose proof nbLevelNotZero.
           assert(Hor: stop = nbL \/ stop < nbL) by omega.
           destruct Hor as [Hor | Hor].
           subst.
           unfold StateLib.Level.eqb in Hl.
            contradict Hl.
            unfold CLevel.
            case_eq(lt_dec (nbL - nbL) nbLevel);intros.
            simpl.
            unfold fstLevel.
            unfold CLevel.
            case_eq(lt_dec 0 nbLevel);intros * Hvv.
            simpl.
            replace (nbL - nbL) with 0 by omega.
            rewrite <- beq_nat_refl.
            auto.
            omega.
            omega.
           assert ( exists indirection2 : page,
            getIndirection root vaToPrepare nbL (stop+1) s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy rootpd defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              apply getIndirectionStopS1 with phyPDChild;trivial.
              omega.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
            
            apply getIndirectionStopSRead with root;trivial.
            omega.
            apply beq_nat_true in Htrue.
            destruct ind2; destruct defaultPage;simpl in *; inversion Htrue;subst;trivial.
            rewrite Hind2.
            f_equal.
            f_equal.
            apply proof_irrelevance. 
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault with (table := ptMMUTrdVA);trivial; try eassumption.
    * apply nextEntryIsPPgetSndShadow;trivial.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l sh2idx;subst;trivial.
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
(forall parts, In parts (getPartitions multiplexer s) ->
   ~ In nextIndirection (getAccessibleMappedPages parts s)) -> 
kernelDataIsolation s ->   
initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
verticalSharing s ->
In phyDescChild (getChildren currentPart s) ->
consistency s ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s phyDescChild indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s -> *)
(* (defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some defaultPage->
  
   
isWellFormedMMUTables phyMMUaddr s ->
false = StateLib.Level.eqb l fstLevel ->
nextEntryIsPP phyDescChild PDidx pd s ->
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
In phyDescChild (getPartitions multiplexer s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
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
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
Proof.
intros * Hnotshared Hiso Hindor3 Hwell1 Hlpred Hor3 Hnotacces Hkdi (Hnotconf1 & Hnotconf2 & Hnotconf3).
intros. 
set(s':={|currentPartition:= _ |}) in *.
unfold verticalSharing in *.
simpl in *;intros * Hparent Hchild1.
assert(Hpart : forall part, In part (getPartitions multiplexer s) <-> In part (getPartitions multiplexer s')).
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
assert(Hchild : In phyDescChild (getPartitions multiplexer s)) by trivial.
assert(Hnotsamepart : forall part, phyDescChild <> part -> 
In part (getPartitions multiplexer s) -> 
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
(forall part : page, In part (getPartitions multiplexer s) -> ~In nextIndirection (getConfigPages part s)) ->
~ In nextIndirection (getConfigPages descChildphy s) ->
In indirection (getConfigPages descChildphy s) ->
StateLib.readPhyEntry phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some defaultPage ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot->  
or3 idxroot ->
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) true ->
 lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex =
          Some (PE entry) ->
nextEntryIsPP descChildphy PDidx pdchild s ->          
(forall parts : page,
     In parts (getPartitions multiplexer s) -> ~In nextIndirection (getAccessibleMappedPages parts s)) ->
In descChildphy (getChildren (currentPartition s) s) ->
verticalSharing
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
              (memory s) beqPage beqIndex |}.
Proof.              
intros Haccessnotconfig Hchildpart Hconfig Hread.
  unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, consistency, indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll.
intuition.
  unfold nextIndirectionsOR in *;intuition;subst;trivial.
  -   apply verticalSharingAddIndirection  with entry nbLgen pdchild PDidx fstVA descChildphy (currentPartition s) 
currentPD ptMMUFstVA ptSh1FstVA pdchild phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.       
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault;try eassumption.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l PDidx;subst;trivial.
  - pose proof pdSh1Sh2ListExistsNotNull as Hkey.
    destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
    apply verticalSharingAddIndirection with entry nbLgen pdchild sh1idx sndVA descChildphy (currentPartition s)
      currentPD ptMMUSndVA ptSh1SndVA sh1 phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.
    * assert(Hl: false = StateLib.Level.eqb l fstLevel) by trivial.
      assert(Hwellx: wellFormedShadows sh1idx s) by trivial.
      unfold wellFormedShadows in Hwellx.
      assert(Hi:  indirectionDescription s descChildphy phySh1Child sh1idx vaToPrepare l) by trivial.
      assert(Hii:  indirectionDescription s descChildphy phyPDChild PDidx vaToPrepare l) by trivial.
      unfold indirectionDescription in *.
      destruct Hi as (root &Hroot & Hrootdef & Horx).
      destruct Hii as (rootpd &Hrootpd & Hrootdefpd & Horxpd).
      destruct Horx as [(Heq & Horx)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)];subst.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)].
         ** subst.
            assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare l 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
            { apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
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
           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
            simpl in *. omega.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst.
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    omega. }
           subst;simpl in *.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare nbL 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = StateLib.Level.eqb nbL fstLevel) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
            simpl in *. omega.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst. 
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    omega. }
            subst;simpl in *.
            inversion Hind;subst root.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh1Child vaToPrepare nbL 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = StateLib.Level.eqb nbL fstLevel) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh1Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
           omega.
           apply CLevelIdentity2 in Hx.
           symmetry in Hx.
           rewrite  Hlll1 in Hx.
           assert(Hxx: nbL - stop1 < nbLevel).
           destruct nbL;simpl in *.
           omega.
           apply CLevelIdentity2 in Hxx.
           rewrite Hx in Hxx.
           omega.
 }

           subst stop1.
           
           pose proof nbLevelNotZero.
           assert(Hor: stop = nbL \/ stop < nbL) by omega.
           destruct Hor as [Hor | Hor].
           subst.
           unfold StateLib.Level.eqb in Hl.
            contradict Hl.
            unfold CLevel.
            case_eq(lt_dec (nbL - nbL) nbLevel);intros.
            simpl.
            unfold fstLevel.
            unfold CLevel.
            case_eq(lt_dec 0 nbLevel);intros * Hvv.
            simpl.
            replace (nbL - nbL) with 0 by omega.
            rewrite <- beq_nat_refl.
            auto.
            omega.
            omega.
           assert ( exists indirection2 : page,
            getIndirection root vaToPrepare nbL (stop+1) s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy rootpd defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              apply getIndirectionStopS1 with phyPDChild;trivial.
              omega.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
            
            apply getIndirectionStopSRead with root;trivial.
            omega.
            apply beq_nat_true in Htrue.
            destruct ind2; destruct defaultPage;simpl in *; inversion Htrue;subst;trivial.
            rewrite Hind2.
            f_equal.
            f_equal.
            apply proof_irrelevance.
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault with (table := ptMMUSndVA);trivial; try eassumption.
    * apply nextEntryIsPPgetFstShadow;trivial.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l sh1idx;subst;trivial.
      apply nextEntryIsPPgetFstShadow;trivial.
  - pose proof pdSh1Sh2ListExistsNotNull as Hkey.
    destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
    apply verticalSharingAddIndirection with entry nbLgen pdchild sh2idx trdVA descChildphy (currentPartition s)
      currentPD ptMMUTrdVA ptSh1TrdVA sh2 phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
      phySh2addr lpred;trivial.
    * unfold nextIndirectionsOR in *;intuition;subst;trivial.
    * unfold isWellFormedTables in *;intuition.
    * unfold consistency in *;intuition.
    * assert(Hl: false = StateLib.Level.eqb l fstLevel) by trivial.
      assert(Hwellx: wellFormedShadows sh2idx s) by trivial.
      unfold wellFormedShadows in Hwellx.
      assert(Hi:  indirectionDescription s descChildphy phySh2Child sh2idx vaToPrepare l) by trivial.
      assert(Hii:  indirectionDescription s descChildphy phyPDChild PDidx vaToPrepare l) by trivial.
      unfold indirectionDescription in *.
      destruct Hi as (root &Hroot & Hrootdef & Horx).
      destruct Hii as (rootpd &Hrootpd & Hrootdefpd & Horxpd).
      destruct Horx as [(Heq & Horx)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)];subst.
      ++ destruct Horxpd as [(Heq & Horxpd)|(nbL & stop & HnbL & Hstop & Hind & Hdef & Hlll)].
         ** subst.
            assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare l 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
            { apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
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
           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
            simpl in *. omega.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst.
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    omega. }
           subst;simpl in *.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare nbL 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = StateLib.Level.eqb nbL fstLevel) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
            simpl in *. omega.
            apply CLevelIdentity2  in Hnat.
            rewrite <- Hxxx in *.
            subst. 
             symmetry in Hl.
            apply levelEqBEqNatFalse0 in Hl.
    omega. }
            subst;simpl in *.
            inversion Hind;subst root.
           assert(Hlv: CLevel (nbL - 0) = nbL).
           apply CLevelIdentity'.
           rewrite Hlv in *.
           inversion Hind;subst. 
           assert ( exists indirection2 : page,
            getIndirection phySh2Child vaToPrepare nbL 1 s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy phyPDChild defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
           simpl in *.
           assert (Hf: false = StateLib.Level.eqb nbL fstLevel) by trivial.
           rewrite <- Hf in *.
           case_eq(  StateLib.readPhyEntry phySh2Child
                (StateLib.getIndexOfAddr vaToPrepare nbL) 
                (memory s));intros * Hr;rewrite Hr in *;try now contradict Hind2.

           case_eq(defaultPage =? p);intros * Heq;rewrite Heq in *;try now contradict Hind2.
           inversion Hind2;subst.
           apply beq_nat_true in Heq.
           f_equal;symmetry;trivial.
           destruct defaultPage;destruct p;simpl in *;subst;f_equal;apply proof_irrelevance.
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
           omega.
           apply CLevelIdentity2 in Hx.
           symmetry in Hx.
           rewrite  Hlll1 in Hx.
           assert(Hxx: nbL - stop1 < nbLevel).
           destruct nbL;simpl in *.
           omega.
           apply CLevelIdentity2 in Hxx.
           rewrite Hx in Hxx.
           omega.
 }

           subst stop1.
           
           pose proof nbLevelNotZero.
           assert(Hor: stop = nbL \/ stop < nbL) by omega.
           destruct Hor as [Hor | Hor].
           subst.
           unfold StateLib.Level.eqb in Hl.
            contradict Hl.
            unfold CLevel.
            case_eq(lt_dec (nbL - nbL) nbLevel);intros.
            simpl.
            unfold fstLevel.
            unfold CLevel.
            case_eq(lt_dec 0 nbLevel);intros * Hvv.
            simpl.
            replace (nbL - nbL) with 0 by omega.
            rewrite <- beq_nat_refl.
            auto.
            omega.
            omega.
           assert ( exists indirection2 : page,
            getIndirection root vaToPrepare nbL (stop+1) s = Some indirection2 /\
            (defaultPage =? indirection2) = true) as (ind2 & Hind2 & Htrue).
           {  apply Hwellx with descChildphy rootpd defaultPage;trivial.
              apply nextEntryIsPPgetPd;trivial.
              simpl.
              apply getIndirectionStopS1 with phyPDChild;trivial.
              omega.
              simpl.
              rewrite <- Hl.
              rewrite Hread.
              rewrite <- beq_nat_refl.
              trivial.
              rewrite <- beq_nat_refl;trivial. }
            
            apply getIndirectionStopSRead with root;trivial.
            omega.
            apply beq_nat_true in Htrue.
            destruct ind2; destruct defaultPage;simpl in *; inversion Htrue;subst;trivial.
            rewrite Hind2.
            f_equal.
            f_equal.
            apply proof_irrelevance. 
    * unfold isWellFormedTables in *;intuition.
    * unfold not;intros;subst.
      apply Haccessnotconfig with descChildphy;trivial.
    * eapply phyPageNotDefault with (table := ptMMUTrdVA);trivial; try eassumption.
    * apply nextEntryIsPPgetSndShadow;trivial.
    * apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l sh2idx;subst;trivial.
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
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
isWellFormedMMUTables phyMMUaddr s ->
false = StateLib.Level.eqb l fstLevel ->
nextEntryIsPP partition idxroot pd s ->
In indirection (getIndirections pd s) ->

StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some defaultPage -> 

noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->

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
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
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
        nextEntryIsPP partition0 idxroot0 entry s /\ entry <> defaultPage)) 
        as (Hi1 & Hi2 & Hi3) .
apply Hgoal;trivial.
assert(Hpart : forall part, In part (getPartitions multiplexer s) <-> In part (getPartitions multiplexer s')).
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




Lemma dataStructurePdSh1Sh2asRootMMUAddIndirection
s indirection nextIndirection idxroot  entry nbLgen  pd   vaToPrepare partition l lpred r w e
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr :
dataStructurePdSh1Sh2asRoot PDidx s->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
isWellFormedMMUTables phyMMUaddr s ->
false = StateLib.Level.eqb l fstLevel ->
nextEntryIsPP partition idxroot pd s ->
In indirection (getIndirections pd s) ->
In partition (getPartitions multiplexer s) ->

StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some defaultPage -> 

noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->

(* isPartitionFalseAll s  ptSh1FstVA  ptSh1TrdVA ptSh1SndVA idxFstVA   idxSndVA   idxTrdVA -> *)
dataStructurePdSh1Sh2asRoot PDidx
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
set(s':={|currentPartition:= _ |}) in *.
intros * Hgoal Hindor3  Hwell1 Hlpred Hor3 Hlookup Hnblgen Hindesc Hwellmmu Hnotfst Hppx Hinmmu Hpartin.
intros.
move Hgoal at bottom.
unfold dataStructurePdSh1Sh2asRoot in *. 
intros * Hpart0 * Hpp0 * Ht * Hllv * Hind .
assert(Hpart : forall part, In part (getPartitions multiplexer s) <-> In part (getPartitions multiplexer s')).
intros.
unfold s'.
eapply  getPartitionsAddIndirection;trivial;try eassumption;trivial.
rewrite <- Hpart in *.
assert(Hpp': nextEntryIsPP partition0 PDidx entry0 s).
apply nextEntryIsPPMapMMUPage' with indirection (StateLib.getIndexOfAddr vaToPrepare l) 
  nextIndirection r w  e;trivial.    
unfold indirectionDescription,  initPEntryTablePreconditionToPropagatePrepareProperties in *.
move Hindesc at bottom.
destruct Hindesc as (tableroot & Hpp & Hrootnotdef & Hor). 
assert(Horx: partition = partition0 \/ partition <> partition0) by apply pageDecOrNot.
destruct Horx as[Horx | Horx].
+ subst partition0.
  destruct Hindor3 as [(Hi1 & Hi2 & Hii3) | [(Hi1 & Hi2 & Hii3) | (Hi1 & Hi2 & Hii3)] ].
  - subst phyPDChild.
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
      assert(Hispe:isPE indirection idx s).
    { destruct Hor as [(Heq & HnbL) | Hor].
      + subst.
     assert(Heq: Some indirection = Some indirection ) by trivial.
(*     { f_equal. apply getPdNextEntryIsPPEq with partition s;trivial.
      apply nextEntryIsPPgetPd;trivial. } *)
      generalize (Hgoal partition Hpartin indirection Hpp' vaToPrepare  Ht l 0 HnbL indirection idx);
      clear Hgoal;intros Hgoal.
      simpl in *.
      generalize (Hgoal Heq);clear Hgoal;intros Hgoal.
      destruct Hgoal as [Hgoal | (Hgoal & Hnot)].
      subst.
      intuition.
      destruct Hgoal as [Hgoal | (Hll&Hgoal)].
      intuition.
       destruct Hgoal as [(_ & hi) | [(_ & hi)|(HH & hi)]];trivial;
       contradict hi.
       apply idxPDidxSh1notEq.
       apply idxPDidxSh2notEq.
    +  
    destruct Hor as (nbL & sstop & Hnbl & Hsstop & Hind1 & Hinddef & Hli).
      generalize (Hgoal partition Hpartin pd Hpp vaToPrepare  Ht nbL sstop Hnbl indirection idx Hind1);  
       clear Hgoal;intros Hgoal.
        destruct Hgoal as [Hgoal | (Hgoal & Hnot)].
      subst.
      intuition.
      destruct Hgoal as [Hgoal | (Hll&Hgoal)].
      intuition.
       destruct Hgoal as [(_ & hi) | [(_ & hi)|(HH & hi)]];trivial;
       contradict hi.
       apply idxPDidxSh1notEq.
       apply idxPDidxSh2notEq. }
    destruct Hor as [(Hroot & Hnbl) | (nbl & sstop & Hnbl & Hsstop & Hind1 & Hnotdef & Hl)].
    * subst.
    ++ assert(Hvaddr: StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare va l = true \/
  StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare va l = false)
  by (destruct (StateLib.checkVAddrsEqualityWOOffset);[left|right];trivial).
  destruct Hvaddr as [Hvaddr|Hvaddr].
  -- 
  destruct stop;simpl in *.
  **
  inversion Hind.
  subst indirection0.
  generalize(Hgoal partition Hpart0  indirection Hpp va Ht level 0 Hnblgen indirection idx);
  clear Hgoal;intros Hgoal.
  simpl in *.
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
  apply isPEMapMMUPage with entry;trivial.
  ** rewrite <- Hnblgen in Hnbl.
     inversion Hnbl;subst.
     rewrite <- Hnotfst in Hind.
     assert(Heq: (StateLib.getIndexOfAddr va level) = (StateLib.getIndexOfAddr vaToPrepare level)). 
     {  admit. }
     rewrite  Heq in Hind.
     assert(Hnewind:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare level)
           (add indirection (StateLib.getIndexOfAddr vaToPrepare level)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |}) (memory s) beqPage beqIndex) =
              Some phyMMUaddr). 
     { apply readPhyEntryAddIndirectionSameTable. }  
     rewrite Hnewind in Hind.
     assert(Hnotdef: (defaultPage =? phyMMUaddr) = false) by trivial.
     rewrite Hnotdef in Hind.
     rewrite Hlpred in Hind.
     destruct stop; simpl in *.
     +++ inversion Hind;subst indirection0.
       right.
       split. 
       --- assert(Horl:1 < level \/ 1 >= level) by omega.
       destruct Horl.
       left;split;trivial.
         apply isPEMapMMUPage with entry ;trivial.
         move Hwellmmu at bottom.
         unfold isWellFormedMMUTables in *.
         destruct Hwellmmu with idx as (Hi & _).
         unfold  StateLib.readPhyEntry, isPE in *.
         destruct (lookup phyMMUaddr idx (memory s) beqPage beqIndex);try now contradict Hi.
         destruct v;try now contradict Hi.
         trivial.
       right;split;trivial.
         right;right;split;trivial.
         apply isPEMapMMUPage with entry ;trivial.
         move Hwellmmu at bottom.
         unfold isWellFormedMMUTables in *.
         destruct Hwellmmu with idx as (Hi & _).
         unfold  StateLib.readPhyEntry, isPE in *.
         destruct (lookup phyMMUaddr idx (memory s) beqPage beqIndex);try now contradict Hi.
         destruct v;try now contradict Hi.
         trivial.
       --- apply beq_nat_false in Hnotdef. intuition.
           subst.
           apply Hnotdef;trivial.
     +++ case_eq(StateLib.Level.eqb lpred fstLevel);intros * Hlpred0;rewrite Hlpred0 in *. 
       --- inversion Hind;subst indirection0.     
           right.
           split. 
           *** assert(Horl:S (S stop)  < level \/ S (S stop)  >= level) by omega.
           destruct Horl.
           left;split;trivial.
             apply isPEMapMMUPage with entry ;trivial.
             move Hwellmmu at bottom.
             unfold isWellFormedMMUTables in *.
             destruct Hwellmmu with idx as (Hi & _).
             unfold  StateLib.readPhyEntry, isPE in *.
             destruct (lookup phyMMUaddr idx (memory s) beqPage beqIndex);try now contradict Hi.
             destruct v;try now contradict Hi.
             trivial.
           right;split;trivial.
             right;right;split;trivial.
             apply isPEMapMMUPage with entry ;trivial.
             move Hwellmmu at bottom.
             unfold isWellFormedMMUTables in *.
             destruct Hwellmmu with idx as (Hi & _).
             unfold  StateLib.readPhyEntry, isPE in *.
             destruct (lookup phyMMUaddr idx (memory s) beqPage beqIndex);try now contradict Hi.
             destruct v;try now contradict Hi.
             trivial.
            *** apply beq_nat_false in Hnotdef. intuition.
               subst.
               apply Hnotdef;trivial.
        --- assert(Hreadnext: StateLib.readPhyEntry phyMMUaddr (StateLib.getIndexOfAddr va lpred)
           (add indirection (StateLib.getIndexOfAddr vaToPrepare level)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |}) (memory s) beqPage beqIndex) = Some defaultPage) by admit.
            rewrite Hreadnext in *.
            rewrite <- beq_nat_refl in Hind.
            inversion Hind;subst.
            left;trivial.
  --  rewrite <- Hnbl in Hnblgen.
    inversion Hnblgen;subst.
    destruct stop;simpl in *.
    ** inversion Hind;subst indirection0.
       right.
       assert(Hx: 0 < l \/  0 >= l ) by omega.
       destruct Hx;
       split;trivial. 
       left;split;trivial.
       apply isPEMapMMUPage with entry;trivial.       
       right;split;trivial.
       right;right;trivial.
       split;trivial.
       apply isPEMapMMUPage with entry;trivial.       
    ** rewrite <- Hnotfst in Hind.
       assert(Horlst: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr va l) \/  
       (StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr va l) ) by apply indexDecOrNot. 
       destruct Horlst as [Horlst| Horlst].
       +++ rewrite Horlst in *. 
           assert(Hnewind:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
           (add indirection (StateLib.getIndexOfAddr va l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |}) (memory s) beqPage beqIndex) =
              Some phyMMUaddr). 
           { apply readPhyEntryAddIndirectionSameTable. }
           rewrite Hnewind in *.  
  assert(Hnotdef: (defaultPage =? phyMMUaddr) = false) by trivial.
     rewrite Hnotdef in Hind.
     rewrite Hlpred in Hind.
     destruct stop; simpl in *.
     --- inversion Hind;subst indirection0.
       right.
       split. 
       *** assert(Horl:1 < l \/ 1 >= l) by omega.
       destruct Horl.
       left;split;trivial.
         apply isPEMapMMUPage with entry ;trivial.
         rewrite Horlst in *;trivial.
         move Hwellmmu at bottom.
         unfold isWellFormedMMUTables in *.
         destruct Hwellmmu with idx as (Hi & _).
         unfold  StateLib.readPhyEntry, isPE in *.
         destruct (lookup phyMMUaddr idx (memory s) beqPage beqIndex);try now contradict Hi.
         destruct v;try now contradict Hi.
         trivial.
       right;split;trivial.
         right;right;split;trivial.
         apply isPEMapMMUPage with entry ;trivial.
         rewrite Horlst in *;trivial.
         move Hwellmmu at bottom.
         unfold isWellFormedMMUTables in *.
         destruct Hwellmmu with idx as (Hi & _).
         unfold  StateLib.readPhyEntry, isPE in *.
         destruct (lookup phyMMUaddr idx (memory s) beqPage beqIndex);try now contradict Hi.
         destruct v;try now contradict Hi.
         trivial.
       *** apply beq_nat_false in Hnotdef. intuition.
           subst.
           apply Hnotdef;trivial.
    --- case_eq(StateLib.Level.eqb lpred fstLevel);intros * Hlpred0;rewrite Hlpred0 in *. 
       *** inversion Hind;subst indirection0.     
           right.
           split. 
           assert(Horl:S (S stop)  < l \/ S (S stop)  >= l) by omega.
           destruct Horl.
           left;split;trivial.
             apply isPEMapMMUPage with entry ;trivial.
             rewrite Horlst in *;trivial.
             move Hwellmmu at bottom.
             unfold isWellFormedMMUTables in *.
             destruct Hwellmmu with idx as (Hi & _).
             unfold  StateLib.readPhyEntry, isPE in *.
             destruct (lookup phyMMUaddr idx (memory s) beqPage beqIndex);try now contradict Hi.
             destruct v;try now contradict Hi.
             trivial.
           right;split;trivial.
             right;right;split;trivial.
             apply isPEMapMMUPage with entry ;trivial.
             rewrite Horlst in *;trivial.
             move Hwellmmu at bottom.
             unfold isWellFormedMMUTables in *.
             destruct Hwellmmu with idx as (Hi & _).
             unfold  StateLib.readPhyEntry, isPE in *.
             destruct (lookup phyMMUaddr idx (memory s) beqPage beqIndex);try now contradict Hi.
             destruct v;try now contradict Hi.
             trivial.
            apply beq_nat_false in Hnotdef. intuition.
               subst.
               apply Hnotdef;trivial.
        *** assert(Hreadnext:  StateLib.readPhyEntry phyMMUaddr (StateLib.getIndexOfAddr va lpred)
           (add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |}) 
              (memory s) beqPage beqIndex) = Some defaultPage) by admit.
            rewrite Hreadnext in Hind.
            rewrite <- beq_nat_refl in Hind.
            inversion Hind;subst.
            left;trivial.
       +++ assert(Hreadeq: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
           (add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |}) 
              (memory s) beqPage beqIndex) =
              StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l)
          (memory s)).
          symmetry. apply readPhyEntryMapMMUPage with entry;trivial.
          right;trivial.
          intuition.
          rewrite Hreadeq in Hind.
          clear Hreadeq.
          case_eq(StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va l) (memory s));intros * Hnextind;
          rewrite Hnextind in *;try now contradict Hind.
          case_eq(defaultPage =? p);intros * Hdef; rewrite Hdef in *;try now contradict Hind.
          inversion Hind;subst.
          left;trivial.
          case_eq(StateLib.Level.pred l );intros * Hl; rewrite Hl in *;try now contradict Hind.
          assert(Hindeq:        getIndirection p va l0 stop s' = getIndirection p va l0 stop s). 
        SearchPattern (getIndirection _ _ _ _ _= getIndirection _ _ _ _ _).
        symmetry.  
        { apply getIndirectionMapMMUPage11 with entry;trivial.
(*********)
              intros * Hi1 Hi2.
     
     assert(Horstop : S(stop0+1) <= nbLevel \/ S(stop0+1) > nbLevel) by omega.
      destruct Horstop as [Horstop|Horstop].
      -
        assert(Hin:  In indirection (getIndirectionsAux indirection s (stop0+1) )).
      { replace (stop0+1) with (S stop0) by omega.
      simpl. left;trivial. }
      assert(~ In tbl (getIndirectionsAux indirection s (stop0+1) )).
     
      { apply getIndirectionInGetIndirections2' with va l;trivial. omega.
      replace (stop0+1) with (S stop0) by omega.
      simpl.
      rewrite <- Hnotfst
      .
      rewrite Hnextind.
      rewrite Hdef.
      rewrite Hl;trivial.
      apply noDupPreviousMMULevels with nbLevel;trivial.
admit.
     
      omega.
     
      apply beq_nat_falseNot;trivial.
           assert(Hlvlx: nbLevel - 1  = l).
       
      {
apply getNbLevelEq in Hnbl.
subst.
rewrite <- nbLevelEq;trivial. }
      omega.
      omega. }
     
      unfold not;intros;subst; now contradict Hin.

      - assert( getIndirection p va l0 (nbLevel -1 -1) s = Some tbl).
      assert(Hlvlx: nbLevel - 1  = l).
       
      {
apply getNbLevelEq in Hnbl.
subst.
rewrite <- nbLevelEq;trivial. }
pose proof Hl as Hpred'.
apply levelPredMinus1 in Hl. (*
unfold CLevel in Hpred.
case_eq(lt_dec (l - 1) nbLevel);intros * Hll;rewrite Hll in *.
simpl in *.
destruct l0.
inversion Hpred.
subst.
simpl in *.
subst.
rewrite Hpred.  *)
      apply getIndirectionStopLevelGT2 with (stop0);trivial.
      unfold CLevel in Hl.
case_eq(lt_dec (l - 1) nbLevel);intros * Hll;rewrite Hll in *.
subst.
simpl in *.
pose proof nbLevelNotZero as Hx.
subst.
rewrite <- Hlvlx.
assert(Hlnot0: l > 0) by admit.
omega.
assert(Hlnot0: l > 0) by admit.

omega.

      unfold CLevel in Hl.
case_eq(lt_dec (l - 1) nbLevel);intros * Hll;rewrite Hll in *.
subst.
simpl in *.
assert(Hlnot0: l > 0) by admit.

omega.
assert(Hlnot0: l > 0) by admit.

omega.
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
subst;omega. left;trivial.  }

 assert(~ In tbl (getIndirectionsAux indirection s (nbLevel-1) )).
     
      { pose proof nbLevelNotZero.
       apply getIndirectionInGetIndirections2' with va l;trivial.
        omega.
     

destruct (nbLevel-1);simpl.
subst;omega.
rewrite <- Hnotfst.
rewrite Hnextind.
rewrite Hdef.
rewrite Hl.
 
      replace (S n- 1) with n in * by omega.
      trivial.
     
unfold getIndirections in *.
replace  (nbLevel - 1 + 1) with nbLevel by omega.
trivial.
assert(Htruex:  (defaultPage =? tbl) = false) by trivial.
apply beq_nat_false in Htruex.
unfold not;intros;subst;try now contradict Htruex.
admit.
apply beq_nat_false in Hi2.
unfold not;intros;subst.
now contradict Hi2.
     
      omega. omega. }
      unfold not;intros ;subst;now contradict Hin.
            - apply beq_nat_false in Hdef.
unfold not;intros;subst;try now contradict Hdef. }
        
        (*********)
        
        
        (* 
         intros.
         assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by omega.
        destruct Hornbl as [Hornbl | Hornbl].
        ---  assert(Hlpredv: nbLevel - 2 = l0) by admit.
         assert(getIndirection p va l0 (nbLevel -2) s = Some tbl).
         eapply getIndirectionStopLevelGe with stop0;trivial;omega.
         assert(Hinind: In tbl (getIndirectionsAux p s ((nbLevel-2)+1))).
          { eapply getIndirectionInGetIndirections1.
          pose nbLevelNotZero.
          omega.
          eassumption.
          admit.
          admit.
          }

     assert(Hnotinnex: ~In indirection (getIndirectionsAux p s (nbLevel - 2 + 1))).
     admit. 
     admit. 
    --- admit. 
    --- admit. *) 
    --- rewrite Hindeq in Hind.
        assert(Hi: getIndirection indirection va l (S stop) s = Some indirection0). 
        simpl. 
        rewrite <- Hnotfst.
        rewrite Hnextind.
        rewrite Hdef.
        rewrite Hl.
        trivial.
        generalize(Hgoal partition Hpart0  indirection Hpp va Ht l  (S stop) Hnbl indirection0 idx Hi);
        clear Hgoal;intros Hgoal.
        destruct Hgoal as [Hgoal|Hgoal].
        left;trivial.
        right.
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
* rewrite <- Hnblgen in Hnbl.
  inversion Hnbl;subst.
  clear Hllv Hpp' Hpart Hnbl.
(*   assert((indirection= indirection0 )  \/ (indirection <> indirection0)) as [Horind|Horind] by apply pageDecOrNot.
  ++ subst indirection0.
  admit.
  ++  *)
assert(sstop=0 \/ sstop>0) as [Horsstop0|Hsstop0] by omega.
-- subst;simpl in *.
inversion Hind1;subst.
(** See the first case line 2318 ++ *)
admit.
--    assert(stop < sstop \/ stop = sstop \/ stop>sstop) as [Hor |[Hor|Hor]] by omega.

**




assert(getIndirection pd va level stop s' =getIndirection pd va level stop s). 
     {   symmetry.
        apply getIndirectionMapMMUPage11Stoplt with entry;trivial.
        
        intros.
       (*   assert(stop0 < sstop \/ stop0 = sstop \/ stop0>sstop) as [Hor |[Hor|Hor]] by omega.
       +  left.  *)
         assert(Hin: In tbl (getIndirectionsAux pd s (stop0+1))).
         { apply getIndirectionInGetIndirections1 with va level ;trivial.
         admit. (** ok *)}
         assert(~In indirection (getIndirectionsAux pd s (stop0+1))).
         { apply getIndirectionInGetIndirections2n with sstop vaToPrepare level;trivial.
         admit. (** OK *)
         admit. (** OK *)
         omega. }
        unfold not;intros ;subst; now contradict Hin. }
        admit. (** OK *)
** subst.
(*          assert(Horstop: checkVAddrsEqualityWOOffset sstop vaToPrepare va level = true \/
checkVAddrsEqualityWOOffset sstop vaToPrepare va level = false) .
{ destruct (checkVAddrsEqualityWOOffset sstop vaToPrepare va level).
  left;trivial.
  right;trivial. }
destruct Horstop as [Hstopor| Hstopor].
+++  *) assert(Hkey: ~In indirection (getIndirectionsAux pd s sstop)).
     { assert(Hex: sstop + 1 <= nbLevel).
destruct level;simpl in *.
omega.
     apply getIndirectionInGetIndirections2' with vaToPrepare level;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
admit. (** Ok *)
     }

assert(Heqind: getIndirection pd va level sstop s' =getIndirection pd va level sstop s). 
     {  apply getIndirectionAddIndirectionEq with entry;trivial. }
     admit. (** Ok *)
**
assert(Hdefind0: indirection0 = defaultPage  \/ indirection0 <> defaultPage ) by apply pageDecOrNot. 
destruct Hdefind0 as [Hdefind0|Hdefind0].
left;trivial.
right. 
assert(Hkey: ~In indirection (getIndirectionsAux pd s sstop)).
     { assert(Hex: sstop + 1 <= nbLevel).
destruct level;simpl in *.
omega.
     apply getIndirectionInGetIndirections2' with vaToPrepare level;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
admit. (** Ok *)
     }
assert(Heqind: getIndirection pd vaToPrepare level sstop s' =getIndirection pd vaToPrepare level sstop s). 
     {  apply getIndirectionAddIndirectionEq with entry;trivial. }
assert(Heqindx: getIndirection pd va level sstop s' =getIndirection pd va level sstop s). 
      {  apply getIndirectionAddIndirectionEq with entry;trivial. }     
 pose proof getIndirectionMiddle as Hmid. 
 generalize (Hmid stop pd va level s' indirection0 sstop Hind Hdefind0 Hor);clear Hmid;
 intros Hmid.
 destruct Hmid as (middle & Hmid1 & Hmid2).
 rewrite Heqindx in Hmid1.      
assert(Horstop: checkVAddrsEqualityWOOffset (sstop) vaToPrepare va level = true \/
checkVAddrsEqualityWOOffset (sstop) vaToPrepare va level = false) .
{ destruct (checkVAddrsEqualityWOOffset (sstop) vaToPrepare va level).
  left;trivial.
  right;trivial. }
destruct Horstop as [Hstopor| Hstopor].
+++ 
assert(Heq: getIndirection pd vaToPrepare level sstop s =
getIndirection pd va level sstop s) by (apply getIndirectionEqStop;trivial).
assert(Heq': getIndirection pd vaToPrepare level sstop s' =
getIndirection pd va level sstop s') by (apply getIndirectionEqStop;trivial).
 rewrite <- Heq in Hmid1.
 rewrite Hind1 in Hmid1.
 inversion Hmid1;subst middle.
 (** See the first case line 2318 ++ *)
(*  destruct (stop - sstop);simpl in *.
 
 admit. (** ok *) 
 rewrite <- Hnotfst in Hmid2.
 
 admit. (** to do *)
  *) admit.
 +++ assert(Heq: getIndirection pd va level stop s' = getIndirection pd va level stop s).
     { symmetry.
       apply getIndirectionMapMMUPage11 with entry;trivial.
       intros * Hi1 Hi2.
       assert(Hor0 : stop0 < sstop \/ stop0=sstop \/ stop0 > sstop) by omega.
  { destruct Hor0 as [Hor0 | [Hor0 | Hor0]].
  -  assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
  { apply getIndirectionInGetIndirections1 with va level;trivial.
  destruct level;simpl in *.
  omega.
  apply beq_nat_false in Hi2.
  unfold not;intros;subst;now contradict Hi2.
  }
  assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop0+1))).
  

  apply getIndirectionInGetIndirections2n with sstop vaToPrepare level;trivial.
  admit. (** ok **)
  admit. (** ok *)
  omega.
  unfold not;intros;subst;now contradict Hkey.
  -  subst stop0.
  
  assert(HsstopS: (S (sstop - 1)) = sstop) by omega.

    eapply pageTablesAreDifferentMiddle with (root1:=pd) (root2:=pd) (s:=s) 
    (va1:= va) (va2:= vaToPrepare) (stop0:= sstop-1) (level1:=level) ;trivial;try rewrite HsstopS;trivial.

admit. (** ok **)
admit. (** ok **)
rewrite <- checkVAddrsEqualityWOOffsetPermut';trivial.
left;split;trivial.
apply getNbLevelEq;trivial.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.

- SearchAbout getIndirectionsAux.
Set Nested Proofs Allowed.
Lemma disjointGetIndirectionsAuxMiddlen:

  forall (n : nat) (p0 p1 root : page) sstop vaToPrepare va(s : state) level,
  p0 <> p1 ->
  n >sstop->
  p0 <> defaultPage->
  p1 <> defaultPage ->
  NoDup (getIndirectionsAux root s n) ->
  getIndirection root vaToPrepare level sstop s = Some p1 -> 
  getIndirection root va level sstop s = Some p0 -> 
  disjoint (getIndirectionsAux p0 s (n - sstop)) (getIndirectionsAux p1 s (n - sstop)). 
Admitted.
pose proof disjointGetIndirectionsAuxMiddlen as Hi.
assert(Hmiddef: middle <> defaultPage) by admit. 
assert(Hid: middle<> indirection).
{ 
  assert(HsstopS: (S (sstop - 1)) = sstop) by omega.

    eapply pageTablesAreDifferentMiddle with (root1:=pd) (root2:=pd) (s:=s) 
    (va1:= va) (va2:= vaToPrepare) (stop0:= sstop-1) (level1:=level) ;trivial;try rewrite HsstopS;trivial.

admit. (** ok **)
admit. (** ok **)
rewrite <- checkVAddrsEqualityWOOffsetPermut';trivial.
left;split;trivial.
apply getNbLevelEq;trivial.

(* unfold not;intros;subst;now contradict Hi2. *)
}
assert(Hnodup:  NoDup (getIndirectionsAux pd s stop0)) by admit. (** need stop0<=nbLevel *)
generalize (Hi stop0 middle indirection pd sstop vaToPrepare va s level Hid Hor0 Hmiddef Hnotdef Hnodup
Hind1 Hmid1);
clear Hi;intros Hi.

 SearchAbout getIndirectionsAux.
 
 Lemma 
 stop0 > sstop ->
 getIndirection pd va level stop0 s = Some tbl -> 
 getIndirection pd va level sstop s = Some middle ->
 NoDup (getIndirectionsAux pd s stop0) ->
 In tbl ((getIndirectionsAux pd s sstop)++middle++(getIndirectionsAux middle s (stop0 - sstop)). 
 
 . 
disjointGetIndirectionsAuxMiddle:
disjoint (getIndirectionsAux p0 s (n - 1)) (getIndirectionsAux p1 s (n - 1))
intuition.
SearchAbout StateLib.getNbLevel.
unfold StateLib.getNbLevel in *.
  unfold getIndirections in *.
  apply noDupPreviousMMULevels with nbLevel ;trivial.
  omega.
  pose proof inclGetIndirectionsAuxLe as Hproof.
  contradict Hnotinind.
  unfold incl in Hproof.
  apply Hproof with (stop0+1).
  omega.
  subst;trivial.
  
      SearchPattern (getIndirection _ _ _ _ _= getIndirection _ _ _ _ _).
      }
 rewrite Heq in Hind.
 generalize(Hgoal partition Hpart0  pd Hpp va Ht level  stop Hnblgen indirection0 idx Hind);
 clear Hgoal;intros Hgoal.
 destruct Hgoal as [Hgoal | Hgoal];try now contradict Hgoal.
 
 admit. 
 
 
 assert(Hinind: ~ In indirection (getIndirectionsAux 
 assert(Hxx: getIndirection middle va (CLevel (level - sstop)) (stop - sstop) s' = Some indirection0 
pose proof getIndirectionInGetIndirections2n as Hkeyp.
generalize(Hkeyp sstop stop


assert(~In indirection 
 apply getIndirectionMiddle with sstop in Hind.
    
 SearchAbout getIndirection.
   
   
   getIndirectionStopS'
   
   
   
   pageTablesOrIndicesAreDifferentMiddle
rewrite <- Heq' in Hind.
assert(
admit. (** OK *)
tbl <> indirection)as [Hortbl| Hortbl]  by apply pageDecOrNot .
right. 
                  SearchAbout getIndirectionsAux.
        SearchAbout getIndirection.
        SearchAbout getIndirection.
(*       pose proof getIndirectionMapMMUPage11'   . *)
     pose proof getIndirectionMapMMUPage11xx.
     symmetry.
     generalize(H7 s va phyMMUaddr indirection pd e r w entry level stop vaToPrepare (CLevel (level - sstop)) );clear H7;
     intros H7.
     unfold s' in H7.
     generalize (H7 stop).
     destruct H7 with s'.
     destruct H7.
      apply H8 with entry.
      intros.
      
  simpl in *.

     Lemma tablesAreNotInNextLevel :
     
     NoDup(getIndirections pd s) ->
     
     
     
     assert(Hnodup: NoDup( getIndirections indirection s)) by admit.
     unfold getIndirections in Hnodup.
     
     
     
     pose proof nbLevelNotZero as Hnblmax.
     destruct nbLevel;try now contradict Hnblmax.
     simpl in *.
     replace (1

SearchAbout In getIndirectionsAux. 

        admit. 
  

eapply getIndirectionInGetIndirectionAuxMinus1 . with va l0 stop0;trivial.




 assert( getIndirection p va l0 (nbLevel - 1) s = Some tbl).
apply getIndirectionStopLevelGT2 with stop0;trivial.
  SearchAbout getIndirection.
  
  SearchPattern  (getIndirection _ _  _ (nbLevel - 1) _ = getIndirection _ _  _ _).


 apply getIndirectionInGetIndirections2 with va l0;trivial.
omega.
 }


        assert(Hinind:  In tbl (getIndirectionsAux p s (stop0 + 1))).
        apply getIndirectionInGetIndirections1 with va l0;trivial.
      assert( revert dependent indirection.
  
   assert(Hi: getIndirection indirection va level stop s = Some indirection0).
  
  
   assert(Hors: stop = l \/ stop <> l) by omega.
    destruct Hors;subst.
    
  
  
   induction stop;simpl in *.
  admit.
  
  
   assert(Hor : stop < l \/ stop=l \/ stop > l) by omega.
{ destruct Hor as [Hor | [Hor | Hor]].       
     
  destruct Hind
  
    
    
    
    
    
    destruct stop;simpl in *.
    ++ inversion Hind;subst indirection0.
         right. split;trivial.
         assert( 0 < level \/  0 >= level) as [Horstop|Horstop] by omega.
         --  left;split;trivial.
          unfold s'.    
          apply isPEMapMMUPage with entry;trivial.
          -- right.
          split;trivial.
          right;right.
          split;trivial.
          apply isPEMapMMUPage with entry;trivial.
     ++ assert(Hlvl: Some level = StateLib.getNbLevel) by trivial.
             rewrite <- Hlvl in Hnbl.
             inversion Hnbl;subst.
             rewrite <- Hnotfst in Hind.
          rewrite Hlpred in *.
          assert(Horidx: StateLib.getIndexOfAddr vaToPrepare level = StateLib.getIndexOfAddr va level \/
          StateLib.getIndexOfAddr vaToPrepare level <> StateLib.getIndexOfAddr va level) by apply indexDecOrNot. 
          destruct Horidx as [Horidx | Horidx ].
          -- rewrite <- Horidx in *.
          
          
          
          
  
      assert(Hread:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare level)
           (add indirection (StateLib.getIndexOfAddr vaToPrepare level)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := phyMMUaddr |}) (memory s) beqPage beqIndex) = Some phyMMUaddr).    
{                apply readPhyEntryAddIndirectionSameTable. }
                rewrite Hread in Hind.
                assert(Hdef: (defaultPage =? phyMMUaddr) = false) by trivial.
                rewrite Hdef in *.
                destruct stop;simpl in Hind.
                **
                inversion Hind; subst indirection0.
                assert(Hwell':  isWellFormedMMUTables phyMMUaddr s').
      apply isWellFormedMMUTablesAddIndirection with entry;trivial.
      unfold isWellFormedMMUTables in Hwell'.
      generalize(Hwell' idx ) ; clear Hwell'; intros (Hwell' & _).
               right. split;trivial;[|
        apply beq_nat_false in Hdef; unfold not;intros;subst;try now contradict Hdef]. 
        assert( 1 < level \/  1 >= level) as [Horstop|Horstop] by omega.
      +++ 
          left;split;trivial.
          unfold s'.
          unfold     StateLib.readPhyEntry , isPE in *;simpl in *.
           destruct (beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare level) (phyMMUaddr, idx) beqPage beqIndex);trivial.
           destruct(  lookup phyMMUaddr idx (removeDup indirection 
           (StateLib.getIndexOfAddr vaToPrepare level) (memory s) beqPage beqIndex) beqPage beqIndex);try now contradict Hwell';trivial.
           destruct v;try now contradict Hwell';trivial.
           trivial.
      +++  right.
          split;trivial.
          right;right.
          split;trivial.
            unfold s'.
          unfold     StateLib.readPhyEntry , isPE in *;simpl in *.
           destruct (beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare level) (phyMMUaddr, idx) beqPage beqIndex);trivial.
           destruct(  lookup phyMMUaddr idx (removeDup indirection 
           (StateLib.getIndexOfAddr vaToPrepare level) (memory s) beqPage beqIndex) beqPage beqIndex);try now contradict Hwell';trivial.
           destruct v;try now contradict Hwell';trivial.
           trivial.
      ** destruct ( StateLib.Level.eqb lpred fstLevel);simpl in *.
     inversion Hind;subst indirection0.
                     assert(Hwell':  isWellFormedMMUTables phyMMUaddr s').
      apply isWellFormedMMUTablesAddIndirection with entry;trivial.
      unfold isWellFormedMMUTables in Hwell'.
      generalize(Hwell' idx ) ; clear Hwell'; intros (Hwell' & _).
               right. split;trivial;[|
        apply beq_nat_false in Hdef; unfold not;intros;subst;try now contradict Hdef]. 
       assert(S (S stop)  < level \/ S (S stop) >= level) as [Horstop|Horstop] by omega.
      +++ 
          left;split;trivial.
          unfold s'.
          unfold     StateLib.readPhyEntry , isPE in *;simpl in *.
           destruct (beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare level) (phyMMUaddr, idx) beqPage beqIndex);trivial.
           destruct(  lookup phyMMUaddr idx (removeDup indirection 
           (StateLib.getIndexOfAddr vaToPrepare level) (memory s) beqPage beqIndex) beqPage beqIndex);try now contradict Hwell';trivial.
           destruct v;try now contradict Hwell';trivial.
           trivial.
      +++ right.
          split;trivial.
          right;right.
          split;trivial.
            unfold s'.
          unfold     StateLib.readPhyEntry , isPE in *;simpl in *.
           destruct (beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare level) (phyMMUaddr, idx) beqPage beqIndex);trivial.
           destruct(  lookup phyMMUaddr idx (removeDup indirection 
           (StateLib.getIndexOfAddr vaToPrepare level) (memory s) beqPage beqIndex) beqPage beqIndex);try now contradict Hwell';trivial.
           destruct v;try now contradict Hwell';trivial.
           trivial.
      
      
      
      +++       
    
      assert( pd = indirection \/ pd <> indirection) as [Hpdor | Hpdor] by apply pageDecOrNot. 
      ++ subst pd.     
         assert(Hvaddr: StateLib.checkVAddrsEqualityWOOffset (stop) vaToPrepare va level = true \/
  StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare va level = false)
  by (destruct (StateLib.checkVAddrsEqualityWOOffset);[left|right];trivial).
  destruct Hvaddr as [Hvaddr|Hvaddr].
  --
         destruct stop ;simpl in *.
         ** inversion Hxi;subst indirection0.
         right. split;trivial.
         assert( 0 < level \/  0 >= level) as [Horstop|Horstop] by omega.
          +++ 
          left;split;trivial.
          unfold s'.    
          apply isPEMapMMUPage with entry;trivial.
          +++ right.
          split;trivial.
          right;right.
          split;trivial.
          apply isPEMapMMUPage with entry;trivial.
          -- assert(Hlvl: Some level = StateLib.getNbLevel) by trivial.
             rewrite <- Hlvl in Hnbl.
             inversion Hnbl;subst.
             rewrite <- Hnotfst in Hxi.
          rewrite <- Hnotfst in *.
          rewrite Hlpred in *.
          case_eq(StateLib.getIndexOfAddr vaToPrepare level =? StateLib.getIndexOfAddr va level);intros * Hx;
          rewrite Hx in *.
          apply beq_nat_true in Hx.
          replace (StateLib.getIndexOfAddr va level) with (StateLib.getIndexOfAddr vaToPrepare level) in Hxi.
         
      assert(Hread:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare level)
           (add indirection (StateLib.getIndexOfAddr vaToPrepare level)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := phyMMUaddr |}) (memory s) beqPage beqIndex) = Some phyMMUaddr).    
                apply readPhyEntryAddIndirectionSameTable.
                rewrite Hread in Hxi.
                assert(Hdef: (defaultPage =? phyMMUaddr) = false) by trivial.
                rewrite Hdef in *.
                destruct stop;simpl in Hxi.
                inversion Hxi; subst indirection0.
                assert(Hwell':  isWellFormedMMUTables phyMMUaddr s').
      apply isWellFormedMMUTablesAddIndirection with entry;trivial.
      unfold isWellFormedMMUTables in Hwell'.
      generalize(Hwell' idx ) ; clear Hwell'; intros (Hwell' & _).
               right. split;trivial.
       assert( 1 < level \/  1 >= level) as [Horstop|Horstop] by omega.
      ** 
          left;split;trivial.
          unfold s'.
          unfold     StateLib.readPhyEntry , isPE in *;simpl in *.
           destruct (beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare level) (phyMMUaddr, idx) beqPage beqIndex);trivial.
           destruct(  lookup phyMMUaddr idx (removeDup indirection 
           (StateLib.getIndexOfAddr vaToPrepare level) (memory s) beqPage beqIndex) beqPage beqIndex);try now contradict Hwell';trivial.
           destruct v;try now contradict Hwell';trivial.
           trivial.
      **  right.
          split;trivial.
          right;right.
          split;trivial.
            unfold s'.
          unfold     StateLib.readPhyEntry , isPE in *;simpl in *.
           destruct (beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare level) (phyMMUaddr, idx) beqPage beqIndex);trivial.
           destruct(  lookup phyMMUaddr idx (removeDup indirection 
           (StateLib.getIndexOfAddr vaToPrepare level) (memory s) beqPage beqIndex) beqPage beqIndex);try now contradict Hwell';trivial.
           destruct v;try now contradict Hwell';trivial.
           trivial.
      **
      apply beq_nat_false in Hdef.
      unfold not;intros;subst. now contradict Hdef.
     **
     destruct ( StateLib.Level.eqb lpred fstLevel);simpl in *.
     inversion Hxi;subst indirection0.
                     assert(Hwell':  isWellFormedMMUTables phyMMUaddr s').
      apply isWellFormedMMUTablesAddIndirection with entry;trivial.
      unfold isWellFormedMMUTables in Hwell'.
      generalize(Hwell' idx ) ; clear Hwell'; intros (Hwell' & _).
               right. split;trivial.
       assert(S (S stop)  < level \/ S (S stop) >= level) as [Horstop|Horstop] by omega.
      +++ 
          left;split;trivial.
          unfold s'.
          unfold     StateLib.readPhyEntry , isPE in *;simpl in *.
           destruct (beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare level) (phyMMUaddr, idx) beqPage beqIndex);trivial.
           destruct(  lookup phyMMUaddr idx (removeDup indirection 
           (StateLib.getIndexOfAddr vaToPrepare level) (memory s) beqPage beqIndex) beqPage beqIndex);try now contradict Hwell';trivial.
           destruct v;try now contradict Hwell';trivial.
           trivial.
      +++ right.
          split;trivial.
          right;right.
          split;trivial.
            unfold s'.
          unfold     StateLib.readPhyEntry , isPE in *;simpl in *.
           destruct (beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare level) (phyMMUaddr, idx) beqPage beqIndex);trivial.
           destruct(  lookup phyMMUaddr idx (removeDup indirection 
           (StateLib.getIndexOfAddr vaToPrepare level) (memory s) beqPage beqIndex) beqPage beqIndex);try now contradict Hwell';trivial.
           destruct v;try now contradict Hwell';trivial.
           trivial.
     +++
      apply beq_nat_false in Hdef.
      unfold not;intros;subst. now contradict Hdef.
     +++
     destruct ( StateLib.Level.eqb lpred fstLevel);simpl in *.
     inversion Hxi;subst indirection0.
     
           }
          apply isPEMapMMUPage with entry;trivial.
          ** right.
          split;trivial.
          right;right.
          split;trivial.
          apply isPEMapMMUPage with entry;trivial.
      
      rewrite Hread in Hind.
          case_eq(  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va level)
          (add indirection (StateLib.getIndexOfAddr vaToPrepare level)
             (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |}) (memory s) beqPage beqIndex));intros * Hxx;
             rewrite Hxx in *.
           rewrite  readPhyEntryAddIndirectionSameTable in Hxx.  
          rewrite Hx in Hxi.
    assert(Horind : indirection = indirection0 \/ indirection <> indirection0) by apply pageDecOrNot. 
    destruct Horind.
    *
    subst indirection0. 
    assert(Horidx: idx= (StateLib.getIndexOfAddr vaToPrepare l) \/ idx <> (StateLib.getIndexOfAddr vaToPrepare l) ) by apply indexDecOrNot.
  destruct Horidx. 
  ++ subst.
  right. 
      split;trivial.
    assert( stop < level \/  stop >= level) as [Horstop|Horstop] by omega.
    left;split;trivial.
    unfold s'.
    unfold isPE.
    simpl.
    assert(HT: beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare l)
      (indirection, StateLib.getIndexOfAddr vaToPrepare l) beqPage beqIndex = true). 
    apply beqPairsTrue.
    split;trivial.
    rewrite HT;trivial.
    right. 
    split;trivial.
    right;right.
    split;trivial.
    unfold s'.
    unfold isPE.
    simpl.
    assert(HT: beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare l)
      (indirection, StateLib.getIndexOfAddr vaToPrepare l) beqPage beqIndex = true). 
    apply beqPairsTrue.
    split;trivial.
    rewrite HT;trivial.   
     assert(Hpdor: tableroot=pd).

 { apply getPdNextEntryIsPPEq with partition s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
  subst tableroot.
  admit. (* indirection <> defaultPage*)
  ++ right. 
      split;trivial.
      assert(Hispe:isPE indirection idx s).
    { destruct Hor as [(Heq & HnbL) | Hor].
      + subst.
      assert (Ht: True) by trivial.
     assert(Heq: Some pd = Some indirection ).
     { f_equal. apply getPdNextEntryIsPPEq with partition s;trivial.
      apply nextEntryIsPPgetPd;trivial. }
      generalize (Hgoal partition Hpartin pd Hpp' vaToPrepare  Ht l 0 HnbL indirection idx);
      clear Hgoal;intros Hgoal.
      simpl in *.
      generalize (Hgoal Heq);clear Hgoal;intros Hgoal.
      destruct Hgoal as [Hgoal | (Hgoal & Hnot)].
      subst.
      intuition.
      destruct Hgoal as [Hgoal | (Hll&Hgoal)].
      intuition.
       destruct Hgoal as [(_ & hi) | [(_ & hi)|(HH & hi)]];trivial;
       contradict hi.
       apply idxPDidxSh1notEq.
       apply idxPDidxSh2notEq.
    +    assert (Ht: True) by trivial.
    destruct Hor as (nbL & sstop & Hnbl & Hsstop & Hind & Hinddef & Hli).
      generalize (Hgoal partition Hpartin tableroot Hpp vaToPrepare  Ht nbL sstop Hnbl indirection idx Hind);  
       clear Hgoal;intros Hgoal.
        destruct Hgoal as [Hgoal | (Hgoal & Hnot)].
      subst.
      intuition.
      destruct Hgoal as [Hgoal | (Hll&Hgoal)].
      intuition.
       destruct Hgoal as [(_ & hi) | [(_ & hi)|(HH & hi)]];trivial;
       contradict hi.
       apply idxPDidxSh1notEq.
       apply idxPDidxSh2notEq. }
    assert( stop < level \/  stop >= level) as [Horstop|Horstop] by omega.
    --
    left;split;trivial.
    unfold s'.    
      apply isPEMapMMUPage with entry;trivial.
 -- right.
 split;trivial.
 right;right.
 split;trivial.
             apply isPEMapMMUPage with entry;trivial. 
  -- admit. (* indirection <> defaultPage*)         
  *  
  
  
   assert(Hgoal1: indirection0 = defaultPage \/
        (stop < level /\ isPE indirection0 idx s \/
         stop >= level /\
         (isVE indirection0 idx s /\ PDidx = sh1idx \/
          isVA indirection0 idx s /\ PDidx = sh2idx \/ isPE indirection0 idx s /\ PDidx = PDidx)) /\
        indirection0 <> defaultPage).
eapply Hgoal with (va:=va)(entry:= pd)(stop:=stop);try eassumption;trivial.
rewrite <- H11.
apply getIndirectionMapMMUPage11 with entry;intros;trivial.
rewrite <- H12. 
      
      simpl in *.
       
       
       

      destruct 
            generalize 
      subst pd.
      rewrite H in Hgoal.
      rewrite <- beq_nat_refl in Hgoal.
      assert(Hgoal1: indirection = defaultPage \/
        (stop < level /\ isPE indirection idx s \/
         stop >= level /\
         (isVE indirection idx s /\ PDidx = sh1idx \/
          isVA indirection idx s /\ PDidx = sh2idx \/ isPE indirection idx s /\ PDidx = PDidx)) /\
        indirection <> defaultPage).
        
eapply Hgoal with (va:=va) ;try eassumption;trivial.

indirec
        SearchAbout isPE.
    eapply  middleIndirectionsContainsPE with (idxroot:=PDidx) (currentPart:= partition)
    (rootind:=pd)(l0:=l) ;trivial.
    symmetry;trivial.
    apply pdPartNotNull with partition s;trivial.
    intuition.
    
    unfold isPE.
    simpl. 
    
     assert(HT: beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare l)
      (indirection, idx) beqPage beqIndex = false). 
    apply beqPairsFalse.
    right;intuition.
    rewrite HT;trivial.
    rewrite removeDupIdentity.
    SearchAbout isPE.

  intuition.

destruct Hor as [(Heq & HnbL) | Hor].
* (** root **) subst.
    
    assert(Hnoneind:getIndirection indirection vaToPrepare l (nbLevel - 1) s = Some defaultPage).
  { apply getIndirectionNbLevelEq with 1;try omega.
    rewrite  getNbLevelEq with l;trivial.
    apply nbLevelEq.
    symmetry in Hnotfst.
    apply levelEqBEqNatFalse0 in Hnotfst.
    omega.
    simpl.
    rewrite <- Hnotfst.
    rewrite H.
    rewrite <- beq_nat_refl.
    trivial. }
  assert(Hor :checkVAddrsEqualityWOOffset nbLevel vaToPrepare va l = true \/
         checkVAddrsEqualityWOOffset nbLevel vaToPrepare va l = false).
  { destruct (checkVAddrsEqualityWOOffset nbLevel vaToPrepare va l);intuition. }
  destruct Hor as [Hor | Hor].
  ++    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    
    assert(Haddror: 
    assert(Htrue:
    ( (indirection0 = indirection  /\ (StateLib.getIndexOfAddr va (CLevel (level-stop)) =  StateLib.getIndexOfAddr vaToPrepare l))) 
    \/ indirection0 <> indirection \/  
    ( indirection0 = indirection  /\ (StateLib.getIndexOfAddr va (CLevel (level-stop)) <>  StateLib.getIndexOfAddr vaToPrepare l)) )  .
    {  assert(Hi1: indirection0 = indirection \/
        indirection0 <> indirection) by apply pageDecOrNot.
        destruct Hi1 as [Hi1 | Hi1]. 
        assert( Hi2: StateLib.getIndexOfAddr va (CLevel (level - stop)) = StateLib.getIndexOfAddr vaToPrepare l \/ 
          StateLib.getIndexOfAddr va (CLevel (level - stop)) <> StateLib.getIndexOfAddr vaToPrepare l) by apply indexDecOrNot.
          destruct Hi2.
          left;intuition.
          right;right. intuition.
          right;left;intuition. }
    destruct Htrue as [(Htrue & Htr) | Htrue]. 
    * admit. 
    (*     right.
    split;trivial.
    assert( stop < level \/  stop >= level) as [Horstop|Horstop] by omega.
    left;split;trivial.
    unfold s'.
    unfold isPE.
    simpl.
    *)
    * assert(Hgoal1: indirection0 = defaultPage \/
        (stop < level /\ isPE indirection0 idx s \/
         stop >= level /\
         (isVE indirection0 idx s /\ PDidx = sh1idx \/
          isVA indirection0 idx s /\ PDidx = sh2idx \/ isPE indirection0 idx s /\ PDidx = PDidx)) /\
        indirection0 <> defaultPage).
eapply Hgoal with (va:=va);try eassumption;trivial.
rewrite <- H12.
apply getIndirectionMapMMUPage11xx with entry;intros;trivial.
rewrite <- H12. 


admit. 

 
     
      
 
 
 
 
 
 
 
 
 
 
 
 
 
 
    SearchAbout getIndirection.
generalize (Hgoal partition Hparts entry0  Hpp' va HT level0 stop Hlevel indirection idx Hind);clear Hgoal;
 intros Hpde.
destruct Hpde as [ Hpde | Hpde].
left. assumption.
right.
destruct Hpde as (Hpde & Hnotnull). 
split;trivial.
clear Hlevel.
destruct Hpde as [(Hlevel & Hpde) | (Hlevel & Hpde)].
+ left. split. assumption.
  apply isPEMapMMUPage with entry;trivial.
+ right. split; trivial. 
  destruct Hpde as [(Hvalue & Hidxpd) | [(Hvalue & Hidxpd) |(Hvalue & Hidxpd)]].
  - contradict Hidxpd.
    apply  idxPDidxSh1notEq.
  - contradict Hidxpd.
    apply idxPDidxSh2notEq.
  - do 2 right.
    split;trivial.
    apply isPEMapMMUPage with entry;trivial.




trivial.
split;trivial.
split.
apply isVAMapMMUPage with entry;trivial.
destruct Hi3 as (pp & Hpp & Hnotdef).
exists pp;split;trivial.

Qed.
                 
Lemma consistencyAddIndirection
s indirection nextIndirection  entry nbLgen  pd idxroot  
(vaToPrepare vaNextInd : vaddr) phyDescChild l  
(currentPart currentPD ptMMUvaNextInd ptSh1VaNextInd: page) root r w e phyPDChild phyMMUaddr phySh1Child 
  phySh1addr phySh2Child phySh2addr lpred:
newIndirectionsAreNotMappedInChildrenAll s currentPart phyMMUaddr phySh1addr phySh2addr -> 
  consistency s ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child 
  phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
(forall parts, In parts (getPartitions multiplexer s) ->
   ~ In nextIndirection (getAccessibleMappedPages parts s)) -> 
kernelDataIsolation s ->   
initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
verticalSharing s ->
In phyDescChild (getChildren currentPart s) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s phyDescChild indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s -> *)
(* (defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some defaultPage->
  
   
isWellFormedMMUTables phyMMUaddr s ->
false = StateLib.Level.eqb l fstLevel ->
nextEntryIsPP phyDescChild PDidx pd s ->
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
In phyDescChild (getPartitions multiplexer s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP phyDescChild idxroot root s ->
In indirection (getIndirections root s)-> 
In indirection (getConfigPages phyDescChild s) ->
isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s  ->

(* isPartitionFalseAll s  ptSh1FstVA  ptSh1TrdVA ptSh1SndVA idxFstVA   idxSndVA   idxTrdVA -> *)
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
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
Proof.
intros * Hnotshared Hiso Hindor3 Hwell1 Hlpred Hor3 Hnotacces Hkdi (Hnotconf1 & Hnotconf2 & Hnotconf3).
intros. 
set(s':={|currentPartition:= _ |}) in *.
unfold consistency in *. 
intuition.
+ (** partitionDescriptorEntry **)
 eapply partitionDescriptorEntryAddIndirection ;trivial;try eassumption;trivial.
+ (** dataStructurePdSh1Sh2asRoot **)
  
 
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
assert(Hread: StateLib.readPhyEntry phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some defaultPage).
    {       intuition;subst.
      assert((defaultPage =? indMMUToPrepare) = true /\ isEntryPage phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s) as (Hi1 & Hi2).
      split;intuition.
      apply beq_nat_true in Hi1.
      unfold isEntryPage, StateLib.readPhyEntry in *.

      case_eq(lookup phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) 
    (memory s) beqPage beqIndex);intros * Hlook;rewrite Hlook in *;try now contradict Hi1.
    destruct v;try now contradict Hi1.
      f_equal. destruct defaultPage;destruct indMMUToPrepare;simpl in *;subst. rewrite Hi2;f_equal;apply proof_irrelevance. }
unfold indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll in *;intuition;subst;trivial.
+ (** kernelDataIsolation **) 
apply toApplykernelDataIsolationAddIndirection with ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
phyMMUaddr phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
currentShadow1 descChildphy phySh1Child (currentPartition s) trdVA nextVA sndVA fstVA nbLgen 
(StateLib.getIndexOfAddr fstVA fstLevel) (StateLib.getIndexOfAddr sndVA fstLevel) (StateLib.getIndexOfAddr trdVA fstLevel)
 (CIndex 0) lpred fstLL LLChildphy lastLLTable idxroot entry pdchild;trivial.
  unfold insertEntryIntoLLPC, propagatedPropertiesPrepare,  indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll ;intuition;subst;trivial.
+ (** partitionsIsolation *)
  eapply toApplyPartitionsIsolationAddIndirection  with ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
phyMMUaddr phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
currentShadow1 descChildphy phySh1Child (currentPartition s) trdVA nextVA sndVA fstVA nbLgen 
(StateLib.getIndexOfAddr fstVA fstLevel) (StateLib.getIndexOfAddr sndVA fstLevel) (StateLib.getIndexOfAddr trdVA fstLevel)
 (CIndex 0) lpred fstLL LLChildphy lastLLTable idxroot entry pdchild;trivial.
 unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll ;intuition;subst;trivial.
+ (** verticalSharing *)
 eapply toApplyVerticalSharingAddIndirection  with ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
phyMMUaddr phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
currentShadow1 descChildphy phySh1Child (currentPartition s) trdVA nextVA sndVA fstVA nbLgen 
(StateLib.getIndexOfAddr fstVA fstLevel) (StateLib.getIndexOfAddr sndVA fstLevel) (StateLib.getIndexOfAddr trdVA fstLevel)
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

