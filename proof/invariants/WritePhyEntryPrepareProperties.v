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
assert(Hchild: In descChildphy (getChildren (currentPartition s) s)). 
{ eapply inGetChildren;admit.      }
  unfold consistency, indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll in *;intuition;subst;trivial.
+ (** kernelDataIsolation **) 
apply toApplykernelDataIsolationAddIndirection with ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
phyMMUaddr phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
currentShadow1 descChildphy phySh1Child (currentPartition s) trdVA nextVA sndVA fstVA nbLgen 
(StateLib.getIndexOfAddr fstVA fstLevel) (StateLib.getIndexOfAddr sndVA fstLevel) (StateLib.getIndexOfAddr trdVA fstLevel)
 (CIndex 0) lpred fstLL LLChildphy lastLLTable idxroot entry pdchild;trivial.
  unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, consistency, indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll ;intuition;subst;trivial.
+ (** partitionsIsolation *)
  eapply toApplyPartitionsIsolationAddIndirection  with ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
phyMMUaddr phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
currentShadow1 descChildphy phySh1Child (currentPartition s) trdVA nextVA sndVA fstVA nbLgen 
(StateLib.getIndexOfAddr fstVA fstLevel) (StateLib.getIndexOfAddr sndVA fstLevel) (StateLib.getIndexOfAddr trdVA fstLevel)
 (CIndex 0) lpred fstLL LLChildphy lastLLTable idxroot entry pdchild;trivial.
 unfold insertEntryIntoLLPC, propagatedPropertiesPrepare, consistency, indirectionDescriptionAll, writeAccessibleRecPreparePostconditionAll ;intuition;subst;trivial.
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

