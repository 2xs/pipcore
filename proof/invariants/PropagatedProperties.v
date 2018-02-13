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