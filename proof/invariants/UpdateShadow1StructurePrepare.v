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
   Admitted.