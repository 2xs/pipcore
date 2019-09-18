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

Require Import Isolation Consistency Model.Hardware Model.ADT StateLib .
Require Import List Arith Model.MALInternal.
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
(Kidx =? nth (length descChild - (nbLevel - 1 + 2)) descChild defaultIndex) = false /\
(Kidx =? nth (length pdChild - (nbLevel - 1 + 2)) pdChild defaultIndex) = false /\
(Kidx =? nth (length shadow1 - (nbLevel - 1 + 2)) shadow1 defaultIndex) = false /\
(Kidx =? nth (length shadow2 - (nbLevel - 1 + 2)) shadow2 defaultIndex) = false /\
(Kidx =? nth (length list - (nbLevel - 1 + 2)) list defaultIndex) = false /\
beqVAddr defaultVAddr pdChild = false /\ 
beqVAddr defaultVAddr shadow1 = false /\
beqVAddr defaultVAddr shadow2 = false /\ 
beqVAddr defaultVAddr list = false /\
currentPart = currentPartition s /\
nextEntryIsPP currentPart PDidx currentPD s /\
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) /\
(defaultPage =? ptRefChild) = false /\
StateLib.getIndexOfAddr descChild fstLevel = idxRefChild /\
entryPresentFlag ptRefChild idxRefChild presentRefChild s /\
entryUserFlag ptRefChild idxRefChild accessibleChild s /\
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) /\
(defaultPage =? ptPDChild) = false /\
StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild /\
entryPresentFlag ptPDChild idxPDChild presentPDChild s /\
entryUserFlag ptPDChild idxPDChild false s /\
(forall idx : index,
StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) /\
(defaultPage =? ptSh1Child) = false /\
StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1 /\
entryPresentFlag ptSh1Child idxSh1 presentSh1 s /\
entryUserFlag ptSh1Child idxSh1 accessibleSh1 s /\
(forall idx : index,
StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) /\
(defaultPage =? ptSh2Child) = false /\
StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2 /\
entryPresentFlag ptSh2Child idxSh2 presentSh2 s /\
entryUserFlag ptSh2Child idxSh2 accessibleSh2 s /\
(forall idx : index,
StateLib.getIndexOfAddr list fstLevel = idx ->
isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s) /\
(defaultPage =? ptConfigPagesList) = false /\
StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList /\
entryPresentFlag ptConfigPagesList idxConfigPagesList presentConfigPagesList s /\
entryUserFlag ptConfigPagesList idxConfigPagesList accessibleList s /\
nextEntryIsPP currentPart sh1idx currentShadow1 s /\
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isVE ptRefChildFromSh1 idx s /\
getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) /\
(defaultPage =? ptRefChildFromSh1) = false /\
(exists va : vaddr,
isEntryVA ptRefChildFromSh1 idxRefChild va s /\ beqVAddr defaultVAddr va = derivedRefChild) /\
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isVE ptPDChildSh1 idx s /\ getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) /\
(defaultPage =? ptPDChildSh1) = false /\
(exists va : vaddr,
isEntryVA ptPDChildSh1 idxPDChild va s /\ beqVAddr defaultVAddr va = derivedPDChild) /\
(forall idx : index,
StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
isVE ptSh1ChildFromSh1 idx s /\
getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) /\
(defaultPage =? ptSh1ChildFromSh1) = false /\
(exists va : vaddr,
isEntryVA ptSh1ChildFromSh1 idxSh1 va s /\ beqVAddr defaultVAddr va = derivedSh1Child) /\
(forall idx : index,
StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) /\
(defaultPage =? childSh2) = false /\
(exists va : vaddr,
isEntryVA childSh2 idxSh2 va s /\ beqVAddr defaultVAddr va = derivedSh2Child) /\
(forall idx : index,
StateLib.getIndexOfAddr list fstLevel = idx ->
isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 sh1idx currentPart list s) /\
(defaultPage =? childListSh1) = false /\
(exists va : vaddr,
isEntryVA childListSh1 idxConfigPagesList va s /\
beqVAddr defaultVAddr va = derivedRefChildListSh1) /\
isEntryPage ptPDChild idxPDChild phyPDChild s /\
(defaultPage =? phyPDChild) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s))) /\
isEntryPage ptSh1Child idxSh1 phySh1Child s /\
(defaultPage =? phySh1Child) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s))) /\
isEntryPage ptSh2Child idxSh2 phySh2Child s /\
(defaultPage =? phySh2Child) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s))) /\
isEntryPage ptConfigPagesList idxConfigPagesList phyConfigPagesList s /\
(defaultPage =? phyConfigPagesList) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s))) /\
isEntryPage ptRefChild idxRefChild phyDescChild s /\ (defaultPage =? phyDescChild) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) -> ~ In phyDescChild (getConfigPages partition s)) /\
isPartitionFalse ptSh1ChildFromSh1 idxSh1 s /\
isPartitionFalse childSh2 idxSh2 s /\
isPartitionFalse childListSh1 idxConfigPagesList s /\
isPartitionFalse ptRefChildFromSh1 idxRefChild s /\
isPartitionFalse ptPDChildSh1 idxPDChild s .

Definition initConfigPagesListPostCondition phyConfigPagesList s :=
StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) s.(memory)
= Some defaultPage /\
StateLib.readVirtual phyConfigPagesList (CIndex (tableSize - 2)) s.(memory)
= Some defaultVAddr /\
(forall idx : index,  Nat.Odd idx -> idx > (CIndex 1) -> idx < CIndex (tableSize -2) ->
exists idxValue, StateLib.readIndex phyConfigPagesList idx s.(memory) = Some idxValue)  /\ 
(forall idx : index,  Nat.Even idx -> idx > (CIndex 1) -> idx < CIndex (tableSize -2) -> 
StateLib.readVirtual phyConfigPagesList idx s.(memory) = Some defaultVAddr).

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
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) /\
initConfigPagesListPostCondition phyConfigPagesList s /\
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage /\
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) /\
(forall idx : index,
Nat.Even idx ->
exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) /\ *)
nullv = defaultVAddr /\
idxPR = PRidx /\
idxPD = PDidx /\
idxSH1 = sh1idx /\
idxSH2 = sh2idx /\
idxSH3 = sh3idx /\
idxPPR = PPRidx /\
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
beqVAddr defaultVAddr vaInCurrentPartition = false /\
beqVAddr defaultVAddr descChild = false /\
(Kidx =?
nth
(length vaInCurrentPartition -
(nbLevel - 1 + 2)) vaInCurrentPartition
defaultIndex) = false /\
(Kidx =?
nth (length vaChild - (nbLevel - 1 + 2))
vaChild defaultIndex) = false /\
currentPart = currentPartition s /\
Some level = StateLib.getNbLevel /\
nextEntryIsPP currentPart sh1idx currentShadow s /\
StateLib.getIndexOfAddr descChild fstLevel =
idxDescChild /\
isVE ptDescChild
(StateLib.getIndexOfAddr descChild fstLevel) s /\
getTableAddrRoot ptDescChild sh1idx currentPart
descChild s /\ (defaultPage =? ptDescChild) = false /\
entryPDFlag ptDescChild idxDescChild true s /\
isVE ptVaInCurPart
(StateLib.getIndexOfAddr vaInCurrentPartition
fstLevel) s /\
getTableAddrRoot ptVaInCurPart sh1idx currentPart
vaInCurrentPartition s /\
(defaultPage =? ptVaInCurPart) = false /\
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel =
idxvaInCurPart /\
isEntryVA ptVaInCurPart idxvaInCurPart vainve s /\
beqVAddr defaultVAddr vainve = isnotderiv /\
nextEntryIsPP currentPart PDidx currentPD s /\
isPE ptVaInCurPartpd
(StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) s /\
getTableAddrRoot ptVaInCurPartpd PDidx currentPart
vaInCurrentPartition s /\
(defaultPage =? ptVaInCurPartpd) = false /\
entryUserFlag ptVaInCurPartpd idxvaInCurPart accessiblesrc s /\
entryPresentFlag ptVaInCurPartpd idxvaInCurPart presentmap s /\
isPE ptDescChildpd
(StateLib.getIndexOfAddr descChild fstLevel) s /\
getTableAddrRoot ptDescChildpd PDidx currentPart descChild s /\
(defaultPage =? ptDescChildpd) = false /\
StateLib.getIndexOfAddr descChild fstLevel = idxDescChild1 /\
entryPresentFlag ptDescChildpd idxDescChild1 presentDescPhy s /\
isEntryPage ptDescChildpd idxDescChild1 phyDescChild s /\
In phyDescChild (getChildren (currentPartition s) s) /\
nextEntryIsPP phyDescChild PDidx pdChildphy s /\
isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s /\
getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s /\
(defaultPage =? ptVaChildpd) = false /\
StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild /\
entryPresentFlag ptVaChildpd idxvaChild presentvaChild s /\
isEntryPage ptVaInCurPartpd idxvaInCurPart phyVaChild s /\
nextEntryIsPP phyDescChild sh2idx sh2Childphy s) /\

isVA ptVaChildsh2 (StateLib.getIndexOfAddr vaChild fstLevel) s /\
getTableAddrRoot ptVaChildsh2 sh2idx phyDescChild vaChild s /\
(defaultPage =? ptVaChildsh2) = false.


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
    (Kidx =? nth (length vaChild - (nbLevel - 1 + 2)) vaChild defaultIndex) =
    false /\
    currentPart = currentPartition s /\
    Some level = getNbLevel /\
    nextEntryIsPP currentPart sh1idx currentShadow s /\
    getIndexOfAddr descChild fstLevel = idxDescChild /\
    isVE ptDescChild (getIndexOfAddr descChild fstLevel) s /\
    getTableAddrRoot ptDescChild sh1idx currentPart descChild s /\
    (defaultPage =? ptDescChild) = false /\
    entryPDFlag ptDescChild idxDescChild true s /\
    nextEntryIsPP currentPart PDidx currentPD s /\
    isPE ptDescChildFromPD (getIndexOfAddr descChild fstLevel) s /\
    getTableAddrRoot ptDescChildFromPD PDidx currentPart descChild s /\
    (defaultPage =? ptDescChildFromPD) = false /\
    getIndexOfAddr descChild fstLevel = idxDescChild1 /\
    entryPresentFlag ptDescChildFromPD idxDescChild1 true s /\
    isEntryPage ptDescChildFromPD idxDescChild1 phyDescChild s /\
    In phyDescChild (getChildren (currentPartition s) s) /\
    nextEntryIsPP phyDescChild PDidx pdChildphy s /\
    getIndexOfAddr vaChild fstLevel = idxvaChild /\
    isPE ptVaChildpd (getIndexOfAddr vaChild fstLevel) s /\
    getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s /\
    (defaultPage =? ptVaChildpd) = false /\
    entryUserFlag ptVaChildpd idxvaChild isaccessible s /\
    entryPresentFlag ptVaChildpd idxvaChild ismapped s /\
    nextEntryIsPP phyDescChild sh1idx shadow1Child s /\
    isVE ptVaChildFromSh1 (getIndexOfAddr vaChild fstLevel) s /\
    getTableAddrRoot ptVaChildFromSh1 sh1idx phyDescChild vaChild s /\
    (defaultPage =? ptVaChildFromSh1) = false /\
    isEntryVA ptVaChildFromSh1 idxvaChild vainve s /\
    beqVAddr defaultVAddr vainve = true /\
    nextEntryIsPP phyDescChild sh2idx sh2Childphy s /\
    isVA ptVaChildsh2 (getIndexOfAddr vaChild fstLevel) s /\
    getTableAddrRoot ptVaChildsh2 sh2idx phyDescChild vaChild s /\
    (defaultPage =? ptVaChildsh2) = false /\
    isVA' ptVaChildsh2 idxvaChild vainparentdef s /\
    isVE ptVaInCurPart (getIndexOfAddr vainparent fstLevel) s /\
    getTableAddrRoot ptVaInCurPart sh1idx currentPart vainparent s /\
    (defaultPage =? ptVaInCurPart) = false /\  getIndexOfAddr vainparent fstLevel = idxvainparent.

Definition indirectionDescription s descChildphy indirection idxroot vaToPrepare l:=
exists (tableroot : page), 
    nextEntryIsPP descChildphy idxroot tableroot s/\
    tableroot <> defaultPage /\  
    ( (tableroot = indirection /\ Some l = StateLib.getNbLevel ) \/
    (exists nbL stop, Some nbL = StateLib.getNbLevel /\ stop <= nbL /\
    StateLib.getIndirection tableroot vaToPrepare nbL stop s = Some indirection /\
    indirection <> defaultPage  /\ 
    l = CLevel (nbL - stop))).

Definition initPEntryTablePreconditionToPropagatePrepareProperties s table:=
(forall partition : page,  In partition (getPartitions multiplexer s) ->
  ~In table (getConfigPages partition s) )
  /\ (defaultPage =? table) = false.

Definition initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr:=
initPEntryTablePreconditionToPropagatePrepareProperties s phyMMUaddr /\
initPEntryTablePreconditionToPropagatePrepareProperties s phySh1addr /\
initPEntryTablePreconditionToPropagatePrepareProperties s phySh2addr.

Definition indirectionDescriptionAll s descChildphy phyPDChild phySh1Child phySh2Child vaToPrepare l:=
indirectionDescription s descChildphy phyPDChild PDidx vaToPrepare l/\ 
indirectionDescription s descChildphy phySh1Child sh1idx vaToPrepare l /\ 
indirectionDescription s descChildphy phySh2Child sh2idx vaToPrepare l.

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
(StateLib.getIndexOfAddr fstVA fstLevel) = idxFstVA /\
(StateLib.getIndexOfAddr sndVA fstLevel)= idxSndVA /\
(StateLib.getIndexOfAddr trdVA fstLevel) = idxTrdVA  /\
getTableAddrRoot ptMMUTrdVA PDidx (currentPartition s) trdVA s /\ 
isPE ptMMUTrdVA (StateLib.getIndexOfAddr trdVA fstLevel) s /\ 
(* isVAUser phySh2addr storeFetchIndex nextVA s /\  *)
(defaultPage =? lastLLTable) = false /\ 
(exists va : vaddr, isEntryVA ptSh1TrdVA (StateLib.getIndexOfAddr trdVA fstLevel) va s /\ beqVAddr defaultVAddr va = trdVAIsShared) /\ 
(defaultPage =? ptSh1TrdVA) = false /\ 
getTableAddrRoot ptSh1TrdVA sh1idx (currentPartition s) trdVA s/\ 
isVE ptSh1TrdVA (StateLib.getIndexOfAddr trdVA fstLevel) s/\ 
isEntryPage ptMMUTrdVA (StateLib.getIndexOfAddr trdVA fstLevel) phySh2addr s/\ 
entryPresentFlag ptMMUTrdVA (StateLib.getIndexOfAddr trdVA fstLevel) true s/\ 
entryUserFlag ptMMUTrdVA (StateLib.getIndexOfAddr trdVA fstLevel) userMMUTrdVA s/\ 

getTableAddrRoot ptMMUSndVA PDidx (currentPartition s) sndVA s/\ 
isPE ptMMUSndVA (StateLib.getIndexOfAddr sndVA fstLevel) s/\ 
(exists va : vaddr, isEntryVA ptSh1SndVA (StateLib.getIndexOfAddr sndVA fstLevel) va s /\ beqVAddr defaultVAddr va = sndVAIsShared)/\ 
(defaultPage =? ptMMUTrdVA) = false /\ 
(defaultPage =? ptSh1SndVA) = false/\ 
getTableAddrRoot ptSh1SndVA sh1idx (currentPartition s) sndVA s/\ 
isVE ptSh1SndVA (StateLib.getIndexOfAddr sndVA fstLevel) s/\ 
(exists va : vaddr, isEntryVA ptSh1FstVA (StateLib.getIndexOfAddr fstVA fstLevel) va s /\ beqVAddr defaultVAddr va = fstVAIsShared) /\ 
(defaultPage =? ptSh1FstVA) = false /\  
getTableAddrRoot ptSh1FstVA sh1idx (currentPartition s) fstVA s/\ 
isVE ptSh1FstVA (StateLib.getIndexOfAddr fstVA fstLevel) s/\ 
false = checkVAddrsEqualityWOOffset nbLevel sndVA trdVA nbLgen /\ 
false = checkVAddrsEqualityWOOffset nbLevel fstVA trdVA nbLgen /\ 
false = checkVAddrsEqualityWOOffset nbLevel fstVA sndVA nbLgen /\ 
beqVAddr defaultVAddr trdVA = false /\ 
(* isVAUser phySh1addr storeFetchIndex trdVA s /\  *)
isEntryPage ptMMUSndVA (StateLib.getIndexOfAddr sndVA fstLevel) phySh1addr s /\ 
entryPresentFlag ptMMUSndVA (StateLib.getIndexOfAddr sndVA fstLevel) true s /\ 
entryUserFlag ptMMUSndVA (StateLib.getIndexOfAddr sndVA fstLevel) userMMUSndVA s /\ 
getTableAddrRoot ptMMUFstVA PDidx (currentPartition s) fstVA s /\ 
isPE ptMMUFstVA (StateLib.getIndexOfAddr fstVA fstLevel) s /\ 
beqVAddr defaultVAddr sndVA = false /\ 
(defaultPage =? ptMMUSndVA) = false /\ 
(* isVAUser phyMMUaddr storeFetchIndex sndVA s /\  *)
entryUserFlag ptMMUFstVA (StateLib.getIndexOfAddr fstVA fstLevel) userMMUFstVA s /\ 
entryPresentFlag ptMMUFstVA (StateLib.getIndexOfAddr fstVA fstLevel) true s /\ 
isEntryPage ptMMUFstVA (StateLib.getIndexOfAddr fstVA fstLevel) phyMMUaddr s /\ 
(defaultPage =? ptMMUFstVA) = false /\ 
Some nbLgen = StateLib.getNbLevel /\ 
(defaultPage =? indMMUToPrepare) = indMMUToPreparebool /\ 
isEntryPage phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s /\ 

nextEntryIsPP (currentPartition s) sh2idx currentShadow2 s /\ 
nextEntryIsPP (currentPartition s) PDidx currentPD s /\ 
nextEntryIsPP (currentPartition s) sh1idx currentShadow1 s /\ 

beqVAddr defaultVAddr fstVA = false /\ 
 false = StateLib.Level.eqb l fstLevel /\ 
In descChildphy (getPartitions multiplexer s) /\ 
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
In currentPart (getPartitions multiplexer s) /\
isAncestor currentPart descParent s /\
In descParent (getPartitions multiplexer s) /\
(defaultPage =? pa entry) = false /\
isPE pt (StateLib.getIndexOfAddr va fstLevel) s /\
getTableAddrRoot pt PDidx descParent va s /\
(defaultPage =? pt) = false /\
entryPresentFlag pt (StateLib.getIndexOfAddr va fstLevel) true s /\
entryUserFlag pt (StateLib.getIndexOfAddr va fstLevel) false s /\
isEntryPage pt (StateLib.getIndexOfAddr va fstLevel) (pa entry) s /\
multiplexer = multiplexer /\
false = StateLib.Page.eqb descParent multiplexer /\
nextEntryIsPP descParent sh2idx sh2 s /\
Some L = StateLib.getNbLevel /\
StateLib.getIndexOfAddr va fstLevel = lastIndex /\
isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel) s /\
getTableAddrRoot ptsh2 sh2idx descParent va s /\
(defaultPage =? ptsh2) = false /\
isVA' ptsh2 lastIndex vaInAncestor s /\
nextEntryIsPP descParent PPRidx ancestor s /\
nextEntryIsPP ancestor PDidx pdAncestor s /\
defaultV = defaultVAddr /\
false = StateLib.VAddr.eqbList defaultV vaInAncestor /\
isPE ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) s /\
getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s /\
(defaultPage =? ptvaInAncestor) = false /\ StateLib.getIndexOfAddr vaInAncestor fstLevel = idxva. 

Definition writeAccessibleRecRecurtionInvariantConj (va:vaddr) (descParent phypage pt:page) currentPart s:=
isAccessibleMappedPageInParent descParent va phypage s = true
/\ partitionsIsolation s
/\ consistency s 
/\ In currentPart (getPartitions MALInternal.multiplexer s) 
/\ isAncestor currentPart descParent s
/\ In descParent (getPartitions MALInternal.multiplexer s)
/\ (defaultPage =? phypage) = false
/\ isPE pt (StateLib.getIndexOfAddr va fstLevel) s 
/\ getTableAddrRoot pt PDidx descParent va s
/\ (defaultPage =? pt) = false
/\ entryPresentFlag pt (StateLib.getIndexOfAddr va fstLevel) true s
/\ entryUserFlag pt (StateLib.getIndexOfAddr va fstLevel) false s
/\ isEntryPage pt (StateLib.getIndexOfAddr va fstLevel) phypage s.

Definition preconditionToPropagateWriteAccessibleRecProperty s ptToUpdate vaToUpdate idxToUpdate:=
 (StateLib.getIndexOfAddr vaToUpdate fstLevel) = idxToUpdate
/\ isPE ptToUpdate (StateLib.getIndexOfAddr vaToUpdate fstLevel) s.

Definition writeAccessibleRecPreparePostcondition descParent phypage s:=
(forall partition : page,
    In partition (getAncestors descParent s) -> ~ In phypage (getAccessibleMappedPages partition s)).

Definition initPEntryTablePreconditionToProveNewProperty s table curidx:= 
forall idx : index, idx < curidx -> 
(StateLib.readPhyEntry table idx (memory s) = Some defaultPage) /\ 
                        StateLib.readPresent table idx (memory s) = Some false.
Definition isWellFormedMMUTables table  s:=
forall idx, StateLib.readPhyEntry table  idx s.(memory) = Some defaultPage /\ 
                        StateLib.readPresent table idx (memory s) = Some false .  
Definition initVEntryTablePreconditionToProveNewProperty s table curidx:= 
forall idx : index, idx < curidx -> 
(StateLib.readVirEntry table idx (memory s) = Some defaultVAddr) /\ 
                        StateLib.readPDflag table idx (memory s) = Some false.
Definition initVEntryTableNewProperty table  s:=
forall idx, StateLib.readVirEntry table  idx s.(memory) = Some defaultVAddr /\ 
                        StateLib.readPDflag table idx (memory s) = Some false .
Definition initVAddrTablePreconditionToProveNewProperty s table curidx:= 
forall idx : index, idx < curidx -> 
(StateLib.readVirtual table idx (memory s) = Some defaultVAddr).

Definition initVAddrTableNewProperty table  s:=
forall idx, StateLib.readVirtual table  idx s.(memory) = Some defaultVAddr. 

Definition PreCtoPropagateIsWellFormedMMUTables phyPage1 phyPage2 
va1 va2  (table1 table2 partition:page) level currentPD s:=
consistency s /\
(defaultPage =? table1) = false /\
(defaultPage =? table2) = false /\
nextEntryIsPP partition PDidx currentPD s /\
In partition (getPartitions multiplexer s)  /\
initPEntryTablePreconditionToPropagatePrepareProperties s phyPage1 /\
( (defaultPage =? phyPage1) = false) /\ 
isEntryPage table1 (StateLib.getIndexOfAddr va1 fstLevel ) phyPage1 s /\
isEntryPage table2 (StateLib.getIndexOfAddr va2 fstLevel) phyPage2 s /\
 isPE table1 (StateLib.getIndexOfAddr va1 fstLevel ) s /\
 getTableAddrRoot table1 PDidx partition va1 s /\
isPE table2 (StateLib.getIndexOfAddr va2 fstLevel) s /\ 
getTableAddrRoot table2 PDidx partition va2 s /\
Some level = StateLib.getNbLevel /\
false = checkVAddrsEqualityWOOffset nbLevel va2 va1 level /\
entryPresentFlag table1 (StateLib.getIndexOfAddr va1 fstLevel ) true s /\ 
entryPresentFlag table2 (StateLib.getIndexOfAddr va2 fstLevel) true s.

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
 forall parts nextIndirection, In parts (getPartitions multiplexer s) -> 
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
(nbL <> fstLevel /\  ( forall idx : index, idx < curidx -> 
(StateLib.readPhyEntry table idx (memory s) = Some defaultPage) /\ 
 StateLib.readPresent table idx (memory s) = Some false )) \/ 
 
 (nbL = fstLevel /\ (forall idx : index, idx < curidx -> 
(StateLib.readVirtual table idx (memory s) = Some defaultVAddr))) .

Definition initFstShadowPreconditionToProveNewProperty nbL s table  curidx:=
 (nbL <> fstLevel /\  ( forall idx : index, idx < curidx -> 
(StateLib.readPhyEntry table idx (memory s) = Some defaultPage) /\ 
 StateLib.readPresent table idx (memory s) = Some false )) \/ 
 (nbL = fstLevel /\ (forall idx : index, idx < curidx -> 
(StateLib.readVirEntry table idx (memory s) = Some defaultVAddr) /\ 
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
  nextEntryIsPP callerPartDesc PDidx callerPageDir s /\
  Some nbL = StateLib.getNbLevel /\
  userCallerContextSaveIndex < tableSize /\
  callerContextSaveIndex = CIndex userCallerContextSaveIndex /\
  isPE callerVidtLastMMUPage
  (StateLib.getIndexOfAddr MALInternal.vidtVAddr fstLevel) s /\
  getTableAddrRoot callerVidtLastMMUPage PDidx callerPartDesc
  MALInternal.vidtVAddr s /\ defaultPage <> callerVidtLastMMUPage /\
  StateLib.getIndexOfAddr MALInternal.vidtVAddr fstLevel =
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
  nextEntryIsPP callerPartDesc PDidx callerPageDir s /\
  Some nbL = StateLib.getNbLevel /\
  userCallerContextSaveIndex < tableSize /\
  callerContextSaveIndex = CIndex userCallerContextSaveIndex /\
  isPE callerVidtLastMMUPage (StateLib.getIndexOfAddr vidtVAddr fstLevel) s /\
  getTableAddrRoot callerVidtLastMMUPage PDidx callerPartDesc vidtVAddr s /\
  defaultPage <> callerVidtLastMMUPage /\
  StateLib.getIndexOfAddr vidtVAddr fstLevel = idxVidtInLastMMUPage /\
  entryPresentFlag callerVidtLastMMUPage idxVidtInLastMMUPage true s /\
  entryUserFlag callerVidtLastMMUPage idxVidtInLastMMUPage true s /\
  isEntryPage callerVidtLastMMUPage idxVidtInLastMMUPage callerVidt s /\
  In calleePartDesc (getPartitions multiplexer s) /\
  calleePartDesc <> defaultPage /\
  nextEntryIsPP calleePartDesc PDidx calleePageDir s /\
  defaultPage <> calleeVidtLastMMUPage /\
  getTableAddrRoot calleeVidtLastMMUPage PDidx calleePartDesc vidtVAddr s /\
  (forall idx : index,
    StateLib.getIndexOfAddr vidtVAddr fstLevel = idx ->
    isPE calleeVidtLastMMUPage idx s) /\
  entryPresentFlag calleeVidtLastMMUPage idxVidtInLastMMUPage true s /\
  entryUserFlag calleeVidtLastMMUPage idxVidtInLastMMUPage true s /\
  isEntryPage calleeVidtLastMMUPage idxVidtInLastMMUPage calleeVidt s /\
  getTableAddrRoot calleeContextLastMMUPage PDidx calleePartDesc calleeContextVAddr s /\
  calleeContextLastMMUPage <> defaultPage /\
  (forall idx : index,
    StateLib.getIndexOfAddr calleeContextVAddr fstLevel = idx ->
    isPE calleeContextLastMMUPage idx s) /\
  StateLib.getIndexOfAddr calleeContextVAddr fstLevel = idxCalleeContextPageInLastMMUPage /\
  entryPresentFlag calleeContextLastMMUPage idxCalleeContextPageInLastMMUPage true s /\
  entryUserFlag calleeContextLastMMUPage idxCalleeContextPageInLastMMUPage true s /\
  getTableAddrRoot calleeContextEndLastMMUPage PDidx calleePartDesc calleeContextEndVAddr s /\
  calleeContextEndLastMMUPage <> defaultPage /\
  (forall idx : index,
    StateLib.getIndexOfAddr calleeContextEndVAddr fstLevel = idx ->
    isPE calleeContextEndLastMMUPage idx s) /\
  StateLib.getIndexOfAddr calleeContextEndVAddr fstLevel = idxCalleeContextEndPageInLastMMUPage /\
  entryPresentFlag calleeContextEndLastMMUPage idxCalleeContextEndPageInLastMMUPage true s /\
  entryUserFlag calleeContextEndLastMMUPage idxCalleeContextEndPageInLastMMUPage true s.


