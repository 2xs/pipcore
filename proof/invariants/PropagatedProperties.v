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

Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Constants Pip.Model.Ops.
Require Import Pip.Proof.Consistency Pip.Proof.Isolation Pip.Proof.StateLib.
Require Import List Arith.
Import List.ListNotations.
Definition propagatedProperties  accessibleChild accessibleSh1 accessibleSh2 accessibleList 
pdChild currentPart currentPD level ptRefChild descChild idxRefChild presentRefChild
 ptPDChild idxPDChild presentPDChild  ptSh1Child shadow1 idxSh1
presentSh1  ptSh2Child shadow2 idxSh2 presentSh2  ptConfigPagesList 
idxConfigPagesList presentConfigPagesList 
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 derivedPDChild 
ptSh1ChildFromSh1 derivedSh1Child childSh2
derivedSh2Child childListSh1 derivedRefChildListSh1 list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s : Prop :=
partitionsIsolation s /\
kernelDataIsolation s /\
verticalSharing s /\
consistency s /\
Some level = StateLib.getNbLevel /\
false = checkVAddrsEqualityWOOffset nbLevel descChild pdChild level /\
false = checkVAddrsEqualityWOOffset nbLevel descChild shadow1 level /\
false = checkVAddrsEqualityWOOffset nbLevel descChild shadow2 level /\
false = checkVAddrsEqualityWOOffset nbLevel descChild list level /\
false = checkVAddrsEqualityWOOffset nbLevel pdChild shadow1 level /\
false = checkVAddrsEqualityWOOffset nbLevel pdChild shadow2 level /\
false = checkVAddrsEqualityWOOffset nbLevel pdChild list level /\
false = checkVAddrsEqualityWOOffset nbLevel shadow1 shadow2 level /\
false = checkVAddrsEqualityWOOffset nbLevel shadow1 list level /\
false = checkVAddrsEqualityWOOffset nbLevel shadow2 list level /\
(idxKernel =? nth (length descChild - (nbLevel - 1 + 2)) descChild idxDefault) = false /\
(idxKernel =? nth (length pdChild - (nbLevel - 1 + 2)) pdChild idxDefault) = false /\
(idxKernel =? nth (length shadow1 - (nbLevel - 1 + 2)) shadow1 idxDefault) = false /\
(idxKernel =? nth (length shadow2 - (nbLevel - 1 + 2)) shadow2 idxDefault) = false /\
(idxKernel =? nth (length list - (nbLevel - 1 + 2)) list idxDefault) = false /\
vaddrEq vaddrDefault pdChild = false /\ 
vaddrEq vaddrDefault shadow1 = false /\
vaddrEq vaddrDefault shadow2 = false /\ 
vaddrEq vaddrDefault list = false /\
currentPart = currentPartition s /\
nextEntryIsPP currentPart idxPageDir currentPD s /\
(forall idx : index,
StateLib.getIndexOfAddr descChild levelMin = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild idxPageDir currentPart descChild s) /\
(pageDefault =? ptRefChild) = false /\
StateLib.getIndexOfAddr descChild levelMin = idxRefChild /\
entryPresentFlag ptRefChild idxRefChild presentRefChild s /\
entryUserFlag ptRefChild idxRefChild accessibleChild s /\
(forall idx : index,
StateLib.getIndexOfAddr pdChild levelMin = idx ->
isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s) /\
(pageDefault =? ptPDChild) = false /\
StateLib.getIndexOfAddr pdChild levelMin = idxPDChild /\
entryPresentFlag ptPDChild idxPDChild presentPDChild s /\
entryUserFlag ptPDChild idxPDChild false s /\
(forall idx : index,
StateLib.getIndexOfAddr shadow1 levelMin = idx ->
isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s) /\
(pageDefault =? ptSh1Child) = false /\
StateLib.getIndexOfAddr shadow1 levelMin = idxSh1 /\
entryPresentFlag ptSh1Child idxSh1 presentSh1 s /\
entryUserFlag ptSh1Child idxSh1 accessibleSh1 s /\
(forall idx : index,
StateLib.getIndexOfAddr shadow2 levelMin = idx ->
isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child idxPageDir currentPart shadow2 s) /\
(pageDefault =? ptSh2Child) = false /\
StateLib.getIndexOfAddr shadow2 levelMin = idxSh2 /\
entryPresentFlag ptSh2Child idxSh2 presentSh2 s /\
entryUserFlag ptSh2Child idxSh2 accessibleSh2 s /\
(forall idx : index,
StateLib.getIndexOfAddr list levelMin = idx ->
isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList idxPageDir currentPart list s) /\
(pageDefault =? ptConfigPagesList) = false /\
StateLib.getIndexOfAddr list levelMin = idxConfigPagesList /\
entryPresentFlag ptConfigPagesList idxConfigPagesList presentConfigPagesList s /\
entryUserFlag ptConfigPagesList idxConfigPagesList accessibleList s /\
nextEntryIsPP currentPart idxShadow1 currentShadow1 s /\
(forall idx : index,
StateLib.getIndexOfAddr descChild levelMin = idx ->
isVE ptRefChildFromSh1 idx s /\
getTableAddrRoot ptRefChildFromSh1 idxShadow1 currentPart descChild s) /\
(pageDefault =? ptRefChildFromSh1) = false /\
(exists va : vaddr,
isEntryVA ptRefChildFromSh1 idxRefChild va s /\ vaddrEq vaddrDefault va = derivedRefChild) /\
(forall idx : index,
StateLib.getIndexOfAddr pdChild levelMin = idx ->
isVE ptPDChildSh1 idx s /\ getTableAddrRoot ptPDChildSh1 idxShadow1 currentPart pdChild s) /\
(pageDefault =? ptPDChildSh1) = false /\
(exists va : vaddr,
isEntryVA ptPDChildSh1 idxPDChild va s /\ vaddrEq vaddrDefault va = derivedPDChild) /\
(forall idx : index,
StateLib.getIndexOfAddr shadow1 levelMin = idx ->
isVE ptSh1ChildFromSh1 idx s /\
getTableAddrRoot ptSh1ChildFromSh1 idxShadow1 currentPart shadow1 s) /\
(pageDefault =? ptSh1ChildFromSh1) = false /\
(exists va : vaddr,
isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ vaddrEq vaddrDefault va = derivedSh1Child) /\
(forall idx : index,
StateLib.getIndexOfAddr shadow2 levelMin = idx ->
isVE childSh2 idx s /\ getTableAddrRoot childSh2 idxShadow1 currentPart shadow2 s) /\
(pageDefault =? childSh2) = false /\
(exists va : vaddr,
isEntryVA childSh2 idxSh2 va s /\ vaddrEq vaddrDefault va = derivedSh2Child) /\
(forall idx : index,
StateLib.getIndexOfAddr list levelMin = idx ->
isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 idxShadow1 currentPart list s) /\
(pageDefault =? childListSh1) = false /\
(exists va : vaddr,
isEntryVA childListSh1 idxConfigPagesList va s /\
vaddrEq vaddrDefault va = derivedRefChildListSh1) /\
isEntryPage ptPDChild idxPDChild phyPDChild s /\
(pageDefault =? phyPDChild) = false /\
(forall partition : page,
In partition (getPartitions pageRootPartition s) ->
~ (partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s))) /\
isEntryPage ptSh1Child idxSh1 phySh1Child s /\
(pageDefault =? phySh1Child) = false /\
(forall partition : page,
In partition (getPartitions pageRootPartition s) ->
~ (partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s))) /\
isEntryPage ptSh2Child idxSh2 phySh2Child s /\
(pageDefault =? phySh2Child) = false /\
(forall partition : page,
In partition (getPartitions pageRootPartition s) ->
~ (partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s))) /\
isEntryPage ptConfigPagesList idxConfigPagesList phyConfigPagesList s /\
(pageDefault =? phyConfigPagesList) = false /\
(forall partition : page,
In partition (getPartitions pageRootPartition s) ->
~ (partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s))) /\
isEntryPage ptRefChild idxRefChild phyDescChild s /\ (pageDefault =? phyDescChild) = false /\
(forall partition : page,
In partition (getPartitions pageRootPartition s) -> ~ In phyDescChild (getConfigPages partition s)) /\
isPartitionFalse ptSh1ChildFromSh1 idxSh1 s /\
isPartitionFalse childSh2 idxSh2 s /\
isPartitionFalse childListSh1 idxConfigPagesList s /\
isPartitionFalse ptRefChildFromSh1 idxRefChild s /\
isPartitionFalse ptPDChildSh1 idxPDChild s .

Definition initConfigPagesListPostCondition phyConfigPagesList s :=
StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) s.(memory)
= Some pageDefault /\
StateLib.readVirtual phyConfigPagesList (CIndex (tableSize - 2)) s.(memory)
= Some vaddrDefault /\
(forall idx : index,  Nat.Odd idx -> idx > (CIndex 1) -> idx < CIndex (tableSize -2) ->
exists idxValue, StateLib.readIndex phyConfigPagesList idx s.(memory) = Some idxValue)  /\ 
(forall idx : index,  Nat.Even idx -> idx > (CIndex 1) -> idx < CIndex (tableSize -2) -> 
StateLib.readVirtual phyConfigPagesList idx s.(memory) = Some vaddrDefault).

Definition newPropagatedProperties s zero nullv idxPR idxPD idxSH1 idxSH2
idxSH3 idxPPR  currentPart  level phyPDChild phySh1Child phySh2Child 
phyConfigPagesList phyDescChild := 
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyPDChild (getAccessibleMappedPages partition s)) /\
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phySh1Child (getAccessibleMappedPages partition s)) /\
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phySh2Child (getAccessibleMappedPages partition s)) /\
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyConfigPagesList (getAccessibleMappedPages partition s)) /\
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyDescChild (getAccessibleMappedPages partition s)) /\
zero = CIndex 0 /\
isWellFormedSndShadow level phySh2Child s /\
isWellFormedFstShadow level phySh1Child s /\
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some pageDefault /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) /\
initConfigPagesListPostCondition phyConfigPagesList s /\
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage /\
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) /\
(forall idx : index,
Nat.Even idx ->
exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) /\ *)
nullv = vaddrDefault /\
idxPR = idxPartDesc /\
idxPD = idxPageDir /\
idxSH1 = idxShadow1 /\
idxSH2 = idxShadow2 /\
idxSH3 = idxShadow3 /\
idxPPR = idxParentDesc /\
isVA phyDescChild idxPPR s /\
nextEntryIsPP phyDescChild idxPPR currentPart s /\
isVA phyDescChild idxSH3 s /\
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s /\
isVA phyDescChild idxSH2 s /\
nextEntryIsPP phyDescChild idxSH2 phySh2Child s /\
isVA phyDescChild idxSH1 s /\
nextEntryIsPP phyDescChild idxSH1 phySh1Child s /\
isVA phyDescChild idxPD s /\
nextEntryIsPP phyDescChild idxPD phyPDChild s /\
isVA phyDescChild idxPR s /\ nextEntryIsPP phyDescChild idxPR phyDescChild s.


Definition propagatedPropertiesAddVaddr s (vaInCurrentPartition vaChild: vaddr)  currentPart
currentShadow descChild idxDescChild ptDescChild ptVaInCurPart idxvaInCurPart
vainve isnotderiv currentPD ptVaInCurPartpd accessiblesrc presentmap ptDescChildpd idxDescChild1
presentDescPhy phyDescChild pdChildphy ptVaChildpd idxvaChild presentvaChild phyVaChild 
sh2Childphy ptVaChildsh2 level
:=
(partitionsIsolation s /\
kernelDataIsolation s /\
verticalSharing s /\ consistency s /\
vaddrEq vaddrDefault vaInCurrentPartition = false /\
vaddrEq vaddrDefault descChild = false /\
(idxKernel =?
nth
(length vaInCurrentPartition -
(nbLevel - 1 + 2)) vaInCurrentPartition
idxDefault) = false /\
(idxKernel =?
nth (length vaChild - (nbLevel - 1 + 2))
vaChild idxDefault) = false /\
currentPart = currentPartition s /\
Some level = StateLib.getNbLevel /\
nextEntryIsPP currentPart idxShadow1 currentShadow s /\
StateLib.getIndexOfAddr descChild levelMin =
idxDescChild /\
isVE ptDescChild
(StateLib.getIndexOfAddr descChild levelMin) s /\
getTableAddrRoot ptDescChild idxShadow1 currentPart
descChild s /\ (pageDefault =? ptDescChild) = false /\
entryPDFlag ptDescChild idxDescChild true s /\
isVE ptVaInCurPart
(StateLib.getIndexOfAddr vaInCurrentPartition
levelMin) s /\
getTableAddrRoot ptVaInCurPart idxShadow1 currentPart
vaInCurrentPartition s /\
(pageDefault =? ptVaInCurPart) = false /\
StateLib.getIndexOfAddr vaInCurrentPartition levelMin =
idxvaInCurPart /\
isEntryVA ptVaInCurPart idxvaInCurPart vainve s /\
vaddrEq vaddrDefault vainve = isnotderiv /\
nextEntryIsPP currentPart idxPageDir currentPD s /\
isPE ptVaInCurPartpd
(StateLib.getIndexOfAddr vaInCurrentPartition levelMin) s /\
getTableAddrRoot ptVaInCurPartpd idxPageDir currentPart
vaInCurrentPartition s /\
(pageDefault =? ptVaInCurPartpd) = false /\
entryUserFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc s /\
entryPresentFlag ptVaInCurPartpd idxvaInCurPart presentmap s /\
isPE ptDescChildpd
(StateLib.getIndexOfAddr descChild levelMin) s /\
getTableAddrRoot ptDescChildpd idxPageDir currentPart descChild s /\
(pageDefault =? ptDescChildpd) = false /\
StateLib.getIndexOfAddr descChild levelMin = idxDescChild1 /\
entryPresentFlag ptDescChildpd idxDescChild1 presentDescPhy s /\
isEntryPage ptDescChildpd idxDescChild1 phyDescChild s /\
In phyDescChild (getChildren (currentPartition s) s) /\
nextEntryIsPP phyDescChild idxPageDir pdChildphy s /\
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild levelMin) s /\
getTableAddrRoot ptVaChildpd idxPageDir phyDescChild vaChild s /\
(pageDefault =? ptVaChildpd) = false /\
StateLib.getIndexOfAddr vaChild levelMin = idxvaChild /\
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s /\
isEntryPage ptVaInCurPartpd idxvaInCurPart phyVaChild s /\
nextEntryIsPP phyDescChild idxShadow2 sh2Childphy s) /\

isVA ptVaChildsh2 (StateLib.getIndexOfAddr vaChild levelMin) s /\
getTableAddrRoot ptVaChildsh2 idxShadow2 phyDescChild vaChild s /\
(pageDefault =? ptVaChildsh2) = false.


Definition propagatedPropertiesRemoveVaddr s descChild (vaChild:vaddr) 
currentPart 
level 
(* currentShadow1 *)
idxDescChild
ptDescChild
(* ischild *) 
currentPD  ptDescChildFromPD 
idxDescChild1 
(* presentDescPhy *)
phyDescChild  pdChildphy 
idxvaChild 
ptVaChildpd  shadow1Child  ptVaChildFromSh1
(* childListSh1Isnull *) 
vainve 
sh2Childphy  ptVaChildsh2
vainparent vainparentdef 
currentShadow  ptVaInCurPart 
idxvainparent
(* defautvaddr *)
(* defaultpage *) 
ismapped isaccessible:=
partitionsIsolation s /\
    kernelDataIsolation s /\
    verticalSharing s /\
    consistency s /\
    (idxKernel =? nth (length vaChild - (nbLevel - 1 + 2)) vaChild idxDefault) =
    false /\
    currentPart = currentPartition s /\
    Some level = getNbLevel /\
    nextEntryIsPP currentPart idxShadow1 currentShadow s /\
    getIndexOfAddr descChild levelMin = idxDescChild /\
    isVE ptDescChild (getIndexOfAddr descChild levelMin) s /\
    getTableAddrRoot ptDescChild idxShadow1 currentPart descChild s /\
    (pageDefault =? ptDescChild) = false /\
    entryPDFlag ptDescChild idxDescChild true s /\
    nextEntryIsPP currentPart idxPageDir currentPD s /\
    isPE ptDescChildFromPD (getIndexOfAddr descChild levelMin) s /\
    getTableAddrRoot ptDescChildFromPD idxPageDir currentPart descChild s /\
    (pageDefault =? ptDescChildFromPD) = false /\
    getIndexOfAddr descChild levelMin = idxDescChild1 /\
    entryPresentFlag ptDescChildFromPD idxDescChild1 true s /\
    isEntryPage ptDescChildFromPD idxDescChild1 phyDescChild s /\
    In phyDescChild (getChildren (currentPartition s) s) /\
    nextEntryIsPP phyDescChild idxPageDir pdChildphy s /\
    getIndexOfAddr vaChild levelMin = idxvaChild /\
    isPE ptVaChildpd (getIndexOfAddr vaChild levelMin) s /\
    getTableAddrRoot ptVaChildpd idxPageDir phyDescChild vaChild s /\
    (pageDefault =? ptVaChildpd) = false /\
    entryUserFlag ptVaChildpd idxvaChild isaccessible s /\
    entryPresentFlag ptVaChildpd idxvaChild ismapped s /\
    nextEntryIsPP phyDescChild idxShadow1 shadow1Child s /\
    isVE ptVaChildFromSh1 (getIndexOfAddr vaChild levelMin) s /\
    getTableAddrRoot ptVaChildFromSh1 idxShadow1 phyDescChild vaChild s /\
    (pageDefault =? ptVaChildFromSh1) = false /\
    isEntryVA ptVaChildFromSh1 idxvaChild vainve s /\
    vaddrEq vaddrDefault vainve = true /\
    nextEntryIsPP phyDescChild idxShadow2 sh2Childphy s /\
    isVA ptVaChildsh2 (getIndexOfAddr vaChild levelMin) s /\
    getTableAddrRoot ptVaChildsh2 idxShadow2 phyDescChild vaChild s /\
    (pageDefault =? ptVaChildsh2) = false /\
    isVA' ptVaChildsh2 idxvaChild vainparentdef s /\
    isVE ptVaInCurPart (getIndexOfAddr vainparent levelMin) s /\
    getTableAddrRoot ptVaInCurPart idxShadow1 currentPart vainparent s /\
    (pageDefault =? ptVaInCurPart) = false /\  getIndexOfAddr vainparent levelMin = idxvainparent.

Definition indirectionDescription s descChildphy indirection idxroot vaToPrepare l:=
exists (tableroot : page), 
    nextEntryIsPP descChildphy idxroot tableroot s/\
    tableroot <> pageDefault /\  
    ( (tableroot = indirection /\ Some l = StateLib.getNbLevel ) \/
    (exists nbL stop, Some nbL = StateLib.getNbLevel /\ stop <= nbL /\
    StateLib.getIndirection tableroot vaToPrepare nbL stop s = Some indirection /\
    indirection <> pageDefault  /\ 
    l = CLevel (nbL - stop))).

Definition initPEntryTablePreconditionToPropagatePrepareProperties s table:=
(forall partition : page,  In partition (getPartitions pageRootPartition s) ->
  ~In table (getConfigPages partition s) )
  /\ (pageDefault =? table) = false.

Definition initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr:=
initPEntryTablePreconditionToPropagatePrepareProperties s phyMMUaddr /\
initPEntryTablePreconditionToPropagatePrepareProperties s phySh1addr /\
initPEntryTablePreconditionToPropagatePrepareProperties s phySh2addr.

Definition indirectionDescriptionAll s descChildphy phyPDChild phySh1Child phySh2Child vaToPrepare l:=
indirectionDescription s descChildphy phyPDChild idxPageDir vaToPrepare l/\ 
indirectionDescription s descChildphy phySh1Child idxShadow1 vaToPrepare l /\ 
indirectionDescription s descChildphy phySh2Child idxShadow2 vaToPrepare l.

Definition isPartitionFalseAll s  ptSh1FstVA  ptSh1TrdVA ptSh1SndVA idxFstVA   idxSndVA   idxTrdVA:=
isPartitionFalse  ptSh1FstVA  idxFstVA s /\
isPartitionFalse  ptSh1SndVA  idxSndVA s /\
isPartitionFalse  ptSh1TrdVA  idxTrdVA s. 

Definition propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable (s:state) ( ptMMUTrdVA phySh2addr phySh1addr
indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 
phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 
descChildphy phySh1Child currentPart: page) (trdVA  nextVA  vaToPrepare sndVA fstVA: vaddr) (nbLgen  l:level)
(userMMUFstVA userMMUSndVA userMMUTrdVA fstVAIsShared sndVAIsShared trdVAIsShared:bool)
(idxFstVA idxSndVA idxTrdVA zeroI n: index) :=

kernelDataIsolation s /\ 
partitionsIsolation s /\ 
verticalSharing s /\ 
consistency s /\ 
(StateLib.getIndexOfAddr fstVA levelMin) = idxFstVA /\
(StateLib.getIndexOfAddr sndVA levelMin)= idxSndVA /\
(StateLib.getIndexOfAddr trdVA levelMin) = idxTrdVA  /\
getTableAddrRoot ptMMUTrdVA idxPageDir (currentPartition s) trdVA s /\ 
isPE ptMMUTrdVA (StateLib.getIndexOfAddr trdVA levelMin) s /\ 
(* isVAUser phySh2addr storeFetchIndex nextVA s /\  *)
(pageDefault =? lastLLTable) = false /\ 
(exists va : vaddr, isEntryVA ptSh1TrdVA (StateLib.getIndexOfAddr trdVA levelMin) va s /\ vaddrEq vaddrDefault va = trdVAIsShared) /\ 
(pageDefault =? ptSh1TrdVA) = false /\ 
getTableAddrRoot ptSh1TrdVA idxShadow1 (currentPartition s) trdVA s/\ 
isVE ptSh1TrdVA (StateLib.getIndexOfAddr trdVA levelMin) s/\ 
isEntryPage ptMMUTrdVA (StateLib.getIndexOfAddr trdVA levelMin) phySh2addr s/\ 
entryPresentFlag ptMMUTrdVA (StateLib.getIndexOfAddr trdVA levelMin) true s/\ 
entryUserFlag ptMMUTrdVA (StateLib.getIndexOfAddr trdVA levelMin) userMMUTrdVA s/\ 

getTableAddrRoot ptMMUSndVA idxPageDir (currentPartition s) sndVA s/\ 
isPE ptMMUSndVA (StateLib.getIndexOfAddr sndVA levelMin) s/\ 
(exists va : vaddr, isEntryVA ptSh1SndVA (StateLib.getIndexOfAddr sndVA levelMin) va s /\ vaddrEq vaddrDefault va = sndVAIsShared)/\ 
(pageDefault =? ptMMUTrdVA) = false /\ 
(pageDefault =? ptSh1SndVA) = false/\ 
getTableAddrRoot ptSh1SndVA idxShadow1 (currentPartition s) sndVA s/\ 
isVE ptSh1SndVA (StateLib.getIndexOfAddr sndVA levelMin) s/\ 
(exists va : vaddr, isEntryVA ptSh1FstVA (StateLib.getIndexOfAddr fstVA levelMin) va s /\ vaddrEq vaddrDefault va = fstVAIsShared) /\ 
(pageDefault =? ptSh1FstVA) = false /\  
getTableAddrRoot ptSh1FstVA idxShadow1 (currentPartition s) fstVA s/\ 
isVE ptSh1FstVA (StateLib.getIndexOfAddr fstVA levelMin) s/\ 
false = checkVAddrsEqualityWOOffset nbLevel sndVA trdVA nbLgen /\ 
false = checkVAddrsEqualityWOOffset nbLevel fstVA trdVA nbLgen /\ 
false = checkVAddrsEqualityWOOffset nbLevel fstVA sndVA nbLgen /\ 
vaddrEq vaddrDefault trdVA = false /\ 
(* isVAUser phySh1addr storeFetchIndex trdVA s /\  *)
isEntryPage ptMMUSndVA (StateLib.getIndexOfAddr sndVA levelMin) phySh1addr s /\ 
entryPresentFlag ptMMUSndVA (StateLib.getIndexOfAddr sndVA levelMin) true s /\ 
entryUserFlag ptMMUSndVA (StateLib.getIndexOfAddr sndVA levelMin) userMMUSndVA s /\ 
getTableAddrRoot ptMMUFstVA idxPageDir (currentPartition s) fstVA s /\ 
isPE ptMMUFstVA (StateLib.getIndexOfAddr fstVA levelMin) s /\ 
vaddrEq vaddrDefault sndVA = false /\ 
(pageDefault =? ptMMUSndVA) = false /\ 
(* isVAUser phyMMUaddr storeFetchIndex sndVA s /\  *)
entryUserFlag ptMMUFstVA (StateLib.getIndexOfAddr fstVA levelMin) userMMUFstVA s /\ 
entryPresentFlag ptMMUFstVA (StateLib.getIndexOfAddr fstVA levelMin) true s /\ 
isEntryPage ptMMUFstVA (StateLib.getIndexOfAddr fstVA levelMin) phyMMUaddr s /\ 
(pageDefault =? ptMMUFstVA) = false /\ 
Some nbLgen = StateLib.getNbLevel /\ 
(pageDefault =? indMMUToPrepare) = indMMUToPreparebool /\ 
isEntryPage phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s /\ 

nextEntryIsPP (currentPartition s) idxShadow2 currentShadow2 s /\ 
nextEntryIsPP (currentPartition s) idxPageDir currentPD s /\ 
nextEntryIsPP (currentPartition s) idxShadow1 currentShadow1 s /\ 

vaddrEq vaddrDefault fstVA = false /\ 
 false = levelEq l levelMin /\ 
In descChildphy (getPartitions pageRootPartition s) /\ 
In descChildphy (getChildren (currentPartition s) s) /\
indirectionDescriptionAll s descChildphy phyPDChild phySh1Child phySh2Child vaToPrepare l /\
(currentPartition s) = currentPart /\  zeroI = CIndex 0 /\
initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr /\
getConfigTablesLinkedList descChildphy (memory s) = Some LLroot /\
In LLChildphy (getLLPages LLroot s (nbPage + 1)) /\
In newLastLLable (getLLPages LLroot s (nbPage + 1))/\
(exists NbFI, isIndexValue newLastLLable (CIndex 1) NbFI s /\ NbFI >=  n).
(* 
isPartitionFalse  ptSh1FstVA  idxFstVA s /\
isPartitionFalse  ptSh1SndVA  idxSndVA s /\
isPartitionFalse  ptSh1TrdVA  idxTrdVA s  *)



Definition writeAccessibleRecInternalPropertiesPrepare currentPart descParent ancestor pdAncestor pt va 
sh2 lastIndex ptsh2 vaInAncestor entry L defaultV ptvaInAncestor idxva s:=
In currentPart (getPartitions pageRootPartition s) /\
isAncestor currentPart descParent s /\
In descParent (getPartitions pageRootPartition s) /\
(pageDefault =? pa entry) = false /\
isPE pt (StateLib.getIndexOfAddr va levelMin) s /\
getTableAddrRoot pt idxPageDir descParent va s /\
(pageDefault =? pt) = false /\
entryPresentFlag pt (StateLib.getIndexOfAddr va levelMin) true s /\
entryUserFlag pt (StateLib.getIndexOfAddr va levelMin) false s /\
isEntryPage pt (StateLib.getIndexOfAddr va levelMin) (pa entry) s /\
pageRootPartition = pageRootPartition /\
false = pageEq descParent pageRootPartition /\
nextEntryIsPP descParent idxShadow2 sh2 s /\
Some L = StateLib.getNbLevel /\
StateLib.getIndexOfAddr va levelMin = lastIndex /\
isVA ptsh2 (StateLib.getIndexOfAddr va levelMin) s /\
getTableAddrRoot ptsh2 idxShadow2 descParent va s /\
(pageDefault =? ptsh2) = false /\
isVA' ptsh2 lastIndex vaInAncestor s /\
nextEntryIsPP descParent idxParentDesc ancestor s /\
nextEntryIsPP ancestor idxPageDir pdAncestor s /\
defaultV = vaddrDefault /\
false = vaddrEq defaultV vaInAncestor /\
isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) s /\
getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s /\
(pageDefault =? ptvaInAncestor) = false /\ StateLib.getIndexOfAddr vaInAncestor levelMin = idxva. 

Definition writeAccessibleRecRecurtionInvariantConj (va:vaddr) (descParent phypage pt:page) currentPart s:=
isAccessibleMappedPageInParent descParent va phypage s = true
/\ partitionsIsolation s
/\ consistency s 
/\ In currentPart (getPartitions pageRootPartition s) 
/\ isAncestor currentPart descParent s
/\ In descParent (getPartitions pageRootPartition s)
/\ (pageDefault =? phypage) = false
/\ isPE pt (StateLib.getIndexOfAddr va levelMin) s 
/\ getTableAddrRoot pt idxPageDir descParent va s
/\ (pageDefault =? pt) = false
/\ entryPresentFlag pt (StateLib.getIndexOfAddr va levelMin) true s
/\ entryUserFlag pt (StateLib.getIndexOfAddr va levelMin) false s
/\ isEntryPage pt (StateLib.getIndexOfAddr va levelMin) phypage s.

Definition preconditionToPropagateWriteAccessibleRecProperty s ptToUpdate vaToUpdate idxToUpdate:=
 (StateLib.getIndexOfAddr vaToUpdate levelMin) = idxToUpdate
/\ isPE ptToUpdate (StateLib.getIndexOfAddr vaToUpdate levelMin) s.

Definition writeAccessibleRecPreparePostcondition descParent phypage s:=
(forall partition : page,
    In partition (getAncestors descParent s) -> ~ In phypage (getAccessibleMappedPages partition s)).

Definition initPEntryTablePreconditionToProveNewProperty s table curidx:= 
forall idx : index, idx < curidx -> 
(StateLib.readPhyEntry table idx (memory s) = Some pageDefault) /\ 
                        StateLib.readPresent table idx (memory s) = Some false.
Definition isWellFormedMMUTables table  s:=
forall idx, StateLib.readPhyEntry table  idx s.(memory) = Some pageDefault /\ 
                        StateLib.readPresent table idx (memory s) = Some false .  
Definition initVEntryTablePreconditionToProveNewProperty s table curidx:= 
forall idx : index, idx < curidx -> 
(StateLib.readVirEntry table idx (memory s) = Some vaddrDefault) /\ 
                        StateLib.readPDflag table idx (memory s) = Some false.
Definition initVEntryTableNewProperty table  s:=
forall idx, StateLib.readVirEntry table  idx s.(memory) = Some vaddrDefault /\ 
                        StateLib.readPDflag table idx (memory s) = Some false .
Definition initVAddrTablePreconditionToProveNewProperty s table curidx:= 
forall idx : index, idx < curidx -> 
(StateLib.readVirtual table idx (memory s) = Some vaddrDefault).

Definition initVAddrTableNewProperty table  s:=
forall idx, StateLib.readVirtual table  idx s.(memory) = Some vaddrDefault. 

Definition PreCtoPropagateIsWellFormedMMUTables phyPage1 phyPage2 
va1 va2  (table1 table2 partition:page) level currentPD s:=
consistency s /\
(pageDefault =? table1) = false /\
(pageDefault =? table2) = false /\
nextEntryIsPP partition idxPageDir currentPD s /\
In partition (getPartitions pageRootPartition s)  /\
initPEntryTablePreconditionToPropagatePrepareProperties s phyPage1 /\
( (pageDefault =? phyPage1) = false) /\ 
isEntryPage table1 (StateLib.getIndexOfAddr va1 levelMin ) phyPage1 s /\
isEntryPage table2 (StateLib.getIndexOfAddr va2 levelMin) phyPage2 s /\
 isPE table1 (StateLib.getIndexOfAddr va1 levelMin ) s /\
 getTableAddrRoot table1 idxPageDir partition va1 s /\
isPE table2 (StateLib.getIndexOfAddr va2 levelMin) s /\ 
getTableAddrRoot table2 idxPageDir partition va2 s /\
Some level = StateLib.getNbLevel /\
false = checkVAddrsEqualityWOOffset nbLevel va2 va1 level /\
entryPresentFlag table1 (StateLib.getIndexOfAddr va1 levelMin ) true s /\ 
entryPresentFlag table2 (StateLib.getIndexOfAddr va2 levelMin) true s.

Definition PCToGeneralizePropagatedPropertiesPrepareUpdateShadow1Structure  b1 b2 b3 b4 b5 b6  
(vaValue fstVA sndVA trdVA:vaddr) (ptMMU ptSh1 pg ptSh1FstVA ptSh1SndVA ptSh1TrdVA phyMMUaddr 
phySh1addr phySh2addr ptMMUFstVA ptMMUSndVA ptMMUTrdVA :page) 
(idxFstVA idxSndVA idxTrdVA idx:index):=
(ptSh1 =ptSh1FstVA /\ idx= idxFstVA /\ vaValue = fstVA /\ pg=phyMMUaddr /\ ptMMU= ptMMUFstVA  /\ b1 = true /\ b4=false /\ b3 = b6 /\ b2 = b5) 
\/ (ptSh1 =ptSh1SndVA /\ idx= idxSndVA /\ vaValue = sndVA /\ pg=phySh1addr /\ ptMMU= ptMMUSndVA /\ b2 = true /\ b5=false /\ b1= b4 /\ b3 = b6) 
\/ (ptSh1 = ptSh1TrdVA/\ idx= idxTrdVA /\ vaValue = trdVA /\ pg=phySh2addr /\ ptMMU= ptMMUTrdVA /\ b3 = true /\ b6=false /\ b1=b4 /\ b2=b5).

Definition writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s:=
writeAccessibleRecPreparePostcondition currentPart phyMMUaddr s 
/\ writeAccessibleRecPreparePostcondition currentPart phySh1addr s 
/\ writeAccessibleRecPreparePostcondition currentPart phySh2addr s.

Definition  isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s :=
isWellFormedMMUTables phyMMUaddr s
/\ isWellFormedFstShadow lpred phySh1addr s 
/\ isWellFormedSndShadow lpred phySh2addr s.

 
Definition newIndirectionsAreNotAccessible s  phyMMUaddr phySh1addr phySh2addr :=
 forall parts nextIndirection, In parts (getPartitions pageRootPartition s) -> 
    (nextIndirection = phyMMUaddr \/ nextIndirection = phySh1addr \/ nextIndirection = phySh2addr) -> 
    ~ In nextIndirection (getAccessibleMappedPages parts s). 

Definition newIndirectionsAreNotMappedInChildren s currentPart newIndirection :=
forall child : page, In child (getChildren currentPart s) -> ~ In newIndirection (getMappedPages child s).

Definition newIndirectionsAreNotMappedInChildrenAll s currentPart phyMMUaddr phySh1addr phySh2addr :=
newIndirectionsAreNotMappedInChildren s currentPart phyMMUaddr /\
newIndirectionsAreNotMappedInChildren s currentPart phySh1addr /\
newIndirectionsAreNotMappedInChildren s currentPart phySh2addr.

Definition insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare 
ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD 
ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA 
zeroI lpred fstLL LLChildphy newLastLLable (n: index) indMMUToPreparebool:=
propagatedPropertiesPrepare indMMUToPreparebool fstLL LLChildphy newLastLLable s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
     currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
     currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false false false false idxFstVA idxSndVA idxTrdVA zeroI n /\
writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s /\
StateLib.Level.pred l = Some lpred /\
isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s /\
newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr /\
newIndirectionsAreNotMappedInChildrenAll s currentPart phyMMUaddr phySh1addr phySh2addr /\
isEntryVA ptSh1FstVA idxFstVA fstVA s /\ isEntryVA ptSh1SndVA idxSndVA sndVA s /\ isEntryVA ptSh1TrdVA idxTrdVA trdVA s.

Definition initSndShadowPreconditionToProveNewProperty nbL s table  curidx:=
(nbL <> levelMin /\  ( forall idx : index, idx < curidx -> 
(StateLib.readPhyEntry table idx (memory s) = Some pageDefault) /\ 
 StateLib.readPresent table idx (memory s) = Some false )) \/ 
 
 (nbL = levelMin /\ (forall idx : index, idx < curidx -> 
(StateLib.readVirtual table idx (memory s) = Some vaddrDefault))) .

Definition initFstShadowPreconditionToProveNewProperty nbL s table  curidx:=
 (nbL <> levelMin /\  ( forall idx : index, idx < curidx -> 
(StateLib.readPhyEntry table idx (memory s) = Some pageDefault) /\ 
 StateLib.readPresent table idx (memory s) = Some false )) \/ 
 (nbL = levelMin /\ (forall idx : index, idx < curidx -> 
(StateLib.readVirEntry table idx (memory s) = Some vaddrDefault) /\ 
 StateLib.readPDflag table idx (memory s) = Some false)). 

 
Definition postConditionYieldBlock1   (s : state)
                                      (userTargetInterrupt userCallerContextSaveIndex : userValue)
                                      (targetInterrupt callerContextSaveIndex idxVidtInLastMMUPage : index)
                                      (callerPartDesc callerPageDir callerVidtLastMMUPage callerVidt : page)
                                      (nbL             : level)
                                      :=
  partitionsIsolation s /\
  kernelDataIsolation s /\ verticalSharing s /\ consistency s /\
  userTargetInterrupt < tableSize /\
  targetInterrupt = CIndex userTargetInterrupt /\
  callerPartDesc = currentPartition s /\
  nextEntryIsPP callerPartDesc idxPageDir callerPageDir s /\
  Some nbL = StateLib.getNbLevel /\
  userCallerContextSaveIndex < tableSize /\
  callerContextSaveIndex = CIndex userCallerContextSaveIndex /\
  isPE callerVidtLastMMUPage
  (StateLib.getIndexOfAddr vaddrVIDT levelMin) s /\
  getTableAddrRoot callerVidtLastMMUPage idxPageDir callerPartDesc
  vaddrVIDT s /\ pageDefault <> callerVidtLastMMUPage /\
  StateLib.getIndexOfAddr vaddrVIDT levelMin =
  idxVidtInLastMMUPage /\
  entryPresentFlag callerVidtLastMMUPage idxVidtInLastMMUPage true s /\
  entryUserFlag callerVidtLastMMUPage idxVidtInLastMMUPage true s /\
  isEntryPage callerVidtLastMMUPage idxVidtInLastMMUPage callerVidt s.

Definition yieldPreWritingProperties
      (s : state)
      (userTargetInterrupt userCallerContextSaveIndex : userValue)
      (targetInterrupt callerContextSaveIndex idxVidtInLastMMUPage : index)
      (callerPartDesc callerPageDir callerVidtLastMMUPage callerVidt : page)
      (calleePartDesc calleePageDir calleeVidtLastMMUPage calleeVidt : page)
      (calleeContextVAddr calleeContextEndVAddr : vaddr)
      (calleeContextLastMMUPage calleeContextEndLastMMUPage : page)
      (idxCalleeContextPageInLastMMUPage idxCalleeContextEndPageInLastMMUPage : index)
      (nbL             : level)
      :=

  partitionsIsolation s /\
  kernelDataIsolation s /\
  verticalSharing s /\
  consistency s /\
  userTargetInterrupt < tableSize /\
  targetInterrupt = CIndex userTargetInterrupt /\
  callerPartDesc = currentPartition s /\
  nextEntryIsPP callerPartDesc idxPageDir callerPageDir s /\
  Some nbL = StateLib.getNbLevel /\
  userCallerContextSaveIndex < tableSize /\
  callerContextSaveIndex = CIndex userCallerContextSaveIndex /\
  isPE callerVidtLastMMUPage (StateLib.getIndexOfAddr vaddrVIDT levelMin) s /\
  getTableAddrRoot callerVidtLastMMUPage idxPageDir callerPartDesc vaddrVIDT s /\
  pageDefault <> callerVidtLastMMUPage /\
  StateLib.getIndexOfAddr vaddrVIDT levelMin = idxVidtInLastMMUPage /\
  entryPresentFlag callerVidtLastMMUPage idxVidtInLastMMUPage true s /\
  entryUserFlag callerVidtLastMMUPage idxVidtInLastMMUPage true s /\
  isEntryPage callerVidtLastMMUPage idxVidtInLastMMUPage callerVidt s /\
  In calleePartDesc (getPartitions pageRootPartition s) /\
  calleePartDesc <> pageDefault /\
  nextEntryIsPP calleePartDesc idxPageDir calleePageDir s /\
  pageDefault <> calleeVidtLastMMUPage /\
  getTableAddrRoot calleeVidtLastMMUPage idxPageDir calleePartDesc vaddrVIDT s /\
  (forall idx : index,
    StateLib.getIndexOfAddr vaddrVIDT levelMin = idx ->
    isPE calleeVidtLastMMUPage idx s) /\
  entryPresentFlag calleeVidtLastMMUPage idxVidtInLastMMUPage true s /\
  entryUserFlag calleeVidtLastMMUPage idxVidtInLastMMUPage true s /\
  isEntryPage calleeVidtLastMMUPage idxVidtInLastMMUPage calleeVidt s /\
  getTableAddrRoot calleeContextLastMMUPage idxPageDir calleePartDesc calleeContextVAddr s /\
  calleeContextLastMMUPage <> pageDefault /\
  (forall idx : index,
    StateLib.getIndexOfAddr calleeContextVAddr levelMin = idx ->
    isPE calleeContextLastMMUPage idx s) /\
  StateLib.getIndexOfAddr calleeContextVAddr levelMin = idxCalleeContextPageInLastMMUPage /\
  entryPresentFlag calleeContextLastMMUPage idxCalleeContextPageInLastMMUPage true s /\
  entryUserFlag calleeContextLastMMUPage idxCalleeContextPageInLastMMUPage true s /\
  getTableAddrRoot calleeContextEndLastMMUPage idxPageDir calleePartDesc calleeContextEndVAddr s /\
  calleeContextEndLastMMUPage <> pageDefault /\
  (forall idx : index,
    StateLib.getIndexOfAddr calleeContextEndVAddr levelMin = idx ->
    isPE calleeContextEndLastMMUPage idx s) /\
  StateLib.getIndexOfAddr calleeContextEndVAddr levelMin = idxCalleeContextEndPageInLastMMUPage /\
  entryPresentFlag calleeContextEndLastMMUPage idxCalleeContextEndPageInLastMMUPage true s /\
  entryUserFlag calleeContextEndLastMMUPage idxCalleeContextEndPageInLastMMUPage true s.

Definition PCWellFormedRootDataStruct n l table idx s idxroot:= 
table = pageDefault \/
(n < l /\ isPE table idx s \/
 n >= l /\
 (isVE table idx s /\ idxroot = idxShadow1 \/
  isVA table idx s /\ idxroot = idxShadow2 \/ isPE table idx s /\ idxroot = idxPageDir)) /\
table <> pageDefault.
