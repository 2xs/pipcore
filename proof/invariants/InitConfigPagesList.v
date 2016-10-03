(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2016)                 *)
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
Require Import StateLib Model.Hardware Model.ADT DependentTypeLemmas
WriteAccessibleRec .
Require Import Coq.Logic.ProofIrrelevance Omega Model.MAL List.

Lemma initConfigPagesList pdChild currentPart currentPD level ptRefChild descChild idxRefChild
      presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1
      ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list zero phyPDChild phySh1Child phySh2Child phyConfigPagesList 
      phyDescChild:
{{ fun s : state =>
   (propagatedProperties pdChild currentPart currentPD level ptRefChild descChild idxRefChild
      presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1
      ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild
      s /\
    zero = CIndex 0 /\
    isEntryPage ptPDChild idxPDChild phyPDChild s /\
    (forall idx : index, StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage) /\
    isEntryPage ptSh1Child idxSh1 phySh1Child s /\
    (forall idx : index, StateLib.readPhyEntry ptSh1Child idx (memory s) = Some defaultPage)) /\
   isEntryPage ptSh2Child idxSh2 phySh2Child s /\
   (forall idx : index, StateLib.readPhyEntry ptSh2Child idx (memory s) = Some defaultPage)
    }} 

  Internal.initConfigPagesList phyConfigPagesList zero 
  
  {{ fun _ s => (propagatedProperties pdChild currentPart currentPD level ptRefChild descChild idxRefChild
      presentRefChild ptPDChild idxPDChild presentPDChild ptSh1Child shadow1 idxSh1 presentSh1
      ptSh2Child shadow2 idxSh2 presentSh2 ptConfigPagesList idxConfigPagesList
      presentConfigPagesList currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1
      derivedPDChild ptSh1ChildFromSh1 derivedSh1Child childSh2 derivedSh2Child childListSh1
      derivedRefChildListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild
      s /\
    zero = CIndex 0 /\
    isEntryPage ptPDChild idxPDChild phyPDChild s /\
    (forall idx : index, StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage) /\
    isEntryPage ptSh1Child idxSh1 phySh1Child s /\
    (forall idx : index, StateLib.readPhyEntry ptSh1Child idx (memory s) = Some defaultPage)) /\
   isEntryPage ptSh2Child idxSh2 phySh2Child s /\
   (forall idx : index, StateLib.readPhyEntry ptSh2Child idx (memory s) = Some defaultPage)
   }}.
Proof.
unfold initConfigPagesList.
unfold initConfigPagesListAux.
(** TODO : To be proved *)
Admitted.