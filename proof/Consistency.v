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
    This file contains the formalization of the consistency properties : 
for each one we summarize the description of its definition *)
Require Import Model.ADT Model.Hardware Model.MAL Model.Lib Lib Isolation 
StateLib.
Require Import  Omega List Coq.Logic.ProofIrrelevance.
Import List.ListNotations.

(** ** The [dataStructurePdSh1Sh2asRoot] property defines the type of different values 
stored into the page directory structure, the first shadow structure and 
the second shadow structure.
Configuation tables of the last level must contain :
 - Physical entries (the type [PEntry] is already definded in [Model.ADT]) for the page directory 
  data structure 
 - Virtual entries (the type [VEntry] is already definded in [Model.ADT] ) for the first shadow 
   data structure
 - Virtual addresses (the type [vaddr] is already definded in [Model.ADT]) for the second shadow 
  data structure
The other tables contain Physical entries  
    [idxroot] should be PDidx, sh1idx or sh2idx.
 (1)   
*)
Definition dataStructurePdSh1Sh2asRoot (idxroot : index) (s : state) :=
forall (partition : page),  
In partition (getPartitions multiplexer s) -> 
forall entry, nextEntryIsPP partition idxroot entry s ->  
forall va : vaddr, 
True -> forall level stop , Some level = getNbLevel -> 
forall indirection idx, getIndirection entry va level stop s = Some indirection -> 
( indirection = defaultPage \/ 
(( ( stop < level /\ isPE indirection idx s )\/  
   ( stop >= level /\ ( (isVE indirection idx s /\ idxroot = sh1idx) \/ 
                       (isVA indirection idx s /\ idxroot = sh2idx) \/ 
                       (isPE indirection idx s /\ idxroot = PDidx) ) ))
                       /\ 
  indirection <> defaultPage)) .

Definition wellFormedFstShadow (s : state) :=
forall partition,
In partition (getPartitions multiplexer s) -> 
forall va pg pd sh1,
StateLib.getPd partition (memory s) = Some pd -> 
StateLib.getFstShadow partition (memory s) = Some sh1 ->
getMappedPage pd s va= SomePage pg ->       
exists vainparent, getVirtualAddressSh1 sh1 s va = Some vainparent. 

Definition wellFormedSndShadow (s : state) :=
forall partition,
In partition (getPartitions multiplexer s) -> 
partition <> multiplexer -> 
forall va pg pd sh2,
StateLib.getPd partition (memory s) = Some pd -> 
StateLib.getSndShadow partition (memory s) = Some sh2 ->
getMappedPage pd s va= SomePage pg ->       
exists vainparent, getVirtualAddressSh2 sh2 s va = Some vainparent /\
beqVAddr defaultVAddr vainparent = false . 

Definition wellFormedShadows (idxroot : index) (s : state) :=
forall (partition : page),  
In partition (getPartitions multiplexer s) -> 
forall pdroot , 
StateLib.getPd partition (memory s) = Some pdroot -> 
forall structroot, nextEntryIsPP partition idxroot structroot s ->  
forall nbL stop , Some nbL = getNbLevel -> 
forall indirection1  va, 
getIndirection pdroot va nbL stop s = Some indirection1 ->
(defaultPage =? indirection1) = false -> 
(exists indirection2, 
getIndirection structroot va nbL stop s = Some indirection2 /\ 
(defaultPage =? indirection2) = false).  

(* Definition fstShadowWellFormed (s : state) :=
forall (partition : page),  
In partition (getPartitions multiplexer s) -> 
forall pdroot sh1Root, 
StateLib.getPd partition (memory s) = Some pdRoot -> 
StateLib.getFstShadow partition (memory s) = Some sh1Root ->
forall level stop , Some level = getNbLevel -> 
forall indirection1 indirection2 va, 
getIndirection pdRoot va level stop s = Some defaultPage ->
getIndirection sh1Root va level stop s = Some defaultPage.  *)

(** ** The [currentPartitionInPartitionsList] property specifies that the 
    current partition must be into the list of partitions retrieved from the 
    first created partition (multiplexer) 
    (2) *)
Definition currentPartitionInPartitionsList (s : state) := 
 In (currentPartition s) (getPartitions multiplexer s).

(** ** The [currentPartitionIsNotDefaultPage t] property specifies that the 
    current partition is not a default physical page  
    (2) *)
Definition currentPartitionIsNotDefaultPage (s : state) :=
 (currentPartition s) <> defaultPage. 
 
(** ** The [parentInPartitionList] property specifies that the parent of a given 
partition should be into the list of partitions retrieved from the 
    first created partition (multiplexer) 
    (3) *)
Definition parentInPartitionList (s : state) := 
forall partition, In partition (getPartitions multiplexer s) -> 
forall parent, nextEntryIsPP partition PPRidx parent s ->
In parent (getPartitions multiplexer s). 

(** ** The [partitionDescriptorEntry] defines some properties of the partition descriptor. 
    - A partition descriptor is a table containing virtual addresses and physical pages.
    - Indecie PDidx, sh1idx, sh2idx, PPRidx and PRidx should be less than ("tableSize" - 1) and 
      contain virtual addresses.
    - The successors of these indices contain physical pages which should not be 
      equal to "defaultPage".
    (4) *)
Definition partitionDescriptorEntry s := 
forall (partition : page),  
In partition (getPartitions multiplexer s) -> 
forall (idxroot : index), (idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx \/ 
idxroot = sh3idx \/
idxroot = PPRidx  \/ idxroot = PRidx ) ->
idxroot < tableSize - 1  /\
isVA partition idxroot  s /\ 
exists entry, nextEntryIsPP partition idxroot entry s  /\  
entry <> defaultPage.

(** ** The [multiplexerWithoutParent] specifies that the multiplexer is the root of
the partition tree *)
Definition multiplexerWithoutParent s :=
getParent multiplexer (memory s) = None.

(** ** The [noDupMappedPagesList] requires that mapped pages of a single partition
    are different 
    (5) *)
Definition noDupMappedPagesList s :=
forall (partition : page),  
In partition (getPartitions multiplexer s) ->  
 NoDup ((getMappedPages partition s)).
 
(** ** The [noDupConfigPagesList] requires that configuation tables of
    a single partition are different 
    (6) *)
Definition noDupConfigPagesList s :=
forall (partition : page),  
In partition (getPartitions multiplexer s) -> 
NoDup (getConfigPages partition s).
(* forall root, nextEntryIsPP partition idxroot root s->
 NoDup (getIndirections root s). 
 *)
(** ** The [accessibleVAIsNotPartitionDescriptor] requires that accessible virtual 
    addresses are not marked as partition descriptor into the first shadow configuation
    structure 
    (7) *)
Definition accessibleVAIsNotPartitionDescriptor s :=
forall partition va pd sh1 page, 
  In partition (getPartitions multiplexer s) -> 
  StateLib.getPd partition (memory s) = Some pd -> 
  StateLib.getFstShadow partition (memory s) = Some sh1 -> 
  getAccessibleMappedPage pd s va = SomePage page -> 
  getPDFlag sh1 va s = false.

(** ** The [accessibleChildPageIsAccessibleIntoParent] requires that all accessible physical 
      pages into a given partition should be accessible into its parent
    (8) *)
Definition  accessibleChildPageIsAccessibleIntoParent s := 
forall partition va pd  accessiblePage, 
  In partition (getPartitions multiplexer s) ->
  StateLib.getPd partition (memory s) = Some pd ->
  getAccessibleMappedPage pd s va = SomePage accessiblePage ->
  isAccessibleMappedPageInParent partition va accessiblePage s = true. 

(** ** The [noCycleInPartitionTree] requires that a partition and 
        its ancestors are different 
    (9) **)
Definition noCycleInPartitionTree s := 
forall ancestor partition, 
In partition (getPartitions multiplexer s) -> 
In ancestor (getAncestors partition s) -> 
ancestor <> partition.

(** ** The [configTablesAreDifferent] requires that configuation tables of different
        partitions are disjoint
      (10) **)
Definition configTablesAreDifferent s := 
forall partition1 partition2,
In partition1 (getPartitions multiplexer s) -> 
In partition2 (getPartitions multiplexer s) -> 
partition1 <> partition2 -> 
disjoint (getConfigPages partition1 s) (getConfigPages partition2 s).

(** ** The [isChild] specifies that a given partition should be a child of the 
        physical page stored as parent into the associated partition descriptor 
    (11) **)
Definition isChild  s :=
forall partition parent : page,
In partition (getPartitions multiplexer s) -> 
StateLib.getParent partition (memory s) = Some parent -> 
In partition (getChildren parent s).


(** ** The [isParent] specifies that if we take any child into the children list of any 
partition into the partition list so this partition should be the parent of this child 
 (..) **)
Definition isParent  s :=
forall partition parent : page,
In parent (getPartitions multiplexer s) -> 
In partition (getChildren parent s) -> 
StateLib.getParent partition (memory s) = Some parent.

(** ** The [isPresentNotDefaultIff] specifies that if the present flag of a physical 
    entry is equal to false so the associated physical page must be equal to the default 
    value 
    (12) **)
Definition isPresentNotDefaultIff s:=
forall table idx , 
 readPresent table idx (memory s) = Some false <-> 
 readPhyEntry table idx (memory s) = Some defaultPage .

(** ** The [physicalPageNotDerived] specifies that if a given physical
    page is marked as not derived in a parent so it is not mapped in any child
    (13)
**) 
Definition physicalPageNotDerived s := 
forall parent va pdParent pageParent, 
In parent (getPartitions multiplexer s) -> 
StateLib.getPd parent (memory s) = Some pdParent -> 
~ isDerived parent va s -> 
getMappedPage pdParent s va = SomePage pageParent -> 
forall child pdChild vaInChild pageChild , 
In child (getChildren parent s) -> 
StateLib.getPd child (memory s) = Some pdChild -> 
getMappedPage pdChild s vaInChild = SomePage  pageChild -> 
pageParent <> pageChild.

Definition noDupPartitionTree s :=
NoDup (getPartitions multiplexer s) .


Definition wellFormedFstShadowIfDefaultValues s :=
forall partition va pd sh1 , 
In partition (getPartitions multiplexer s) -> 
StateLib.getPd partition (memory s) = Some pd -> 
StateLib.getFstShadow partition (memory s) = Some sh1 -> 
getMappedPage pd s va = SomeDefault-> 
getPDFlag sh1 va s = false /\ 
getVirtualAddressSh1 sh1 s va = Some defaultVAddr.

Definition wellFormedFstShadowIfNone s :=
forall partition va pd sh1 , 
In partition (getPartitions multiplexer s) -> 
StateLib.getPd partition (memory s) = Some pd -> 
StateLib.getFstShadow partition (memory s) = Some sh1 -> 
getMappedPage pd s va =  NonePage -> 
getPDFlag sh1 va s = false /\ 
getVirtualAddressSh1 sh1 s va = None.


(** Consistency : Linked list properties **)
Definition LLconfiguration1 s:=
forall part fstLL LLtable,
In part (getPartitions multiplexer s) -> 
nextEntryIsPP part sh3idx fstLL s ->  
In LLtable (getLLPages part s nbPage) -> 
isI LLtable (CIndex 1) s.

Definition LLconfiguration2 s:=
forall part fstLL LLtable maxidx,
In part (getPartitions multiplexer s) -> 
nextEntryIsPP part sh3idx fstLL s ->  
In LLtable (getLLPages part s nbPage) -> 
StateLib.getMaxIndex = Some maxidx -> 
isPP LLtable maxidx s.

Definition LLconfiguration3 s:=
forall part fstLL LLtable,
In part (getPartitions multiplexer s) -> 
nextEntryIsPP part sh3idx fstLL s ->  
In LLtable (getLLPages part s (nbPage+1)) -> 
isI LLtable (CIndex 0) s.

Definition LLconfiguration4 s:=
forall part fstLL LLtable,
In part (getPartitions multiplexer s) -> 
nextEntryIsPP part sh3idx fstLL s ->  
In LLtable (getLLPages part s (nbPage+1)) -> 
exists FFI nextFFI,
StateLib.readIndex LLtable (CIndex 0) (memory s)= Some FFI 
/\ isVA LLtable FFI s /\ FFI < tableSize - 1 
/\ StateLib.Index.succ FFI = Some nextFFI
/\ isI LLtable nextFFI s.

Definition LLconfiguration5 s:=
forall part fstLL ,
In part (getPartitions multiplexer s) -> 
nextEntryIsPP part sh3idx fstLL s ->  
NoDup (getLLPages fstLL s (nbPage + 1)).

Definition LLconfiguration5 s:=
forall partition LL LLtable FFI nextFFI, 
In partition (getPartitions multiplexer s) ->
getConfigTablesLinkedList partition (memory s) = Some LL ->
In LLtable (getLLPages LL s (nbPage + 1)) ->
isIndexValue LLtable (CIndex 0) FFI s ->
StateLib.Index.succ FFI = Some nextFFI ->
StateLib.getMaxIndex <> Some nextFFI. 



(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(** ** Conjunction of all consistency properties *)
Definition consistency s := 
 partitionDescriptorEntry s /\  
 dataStructurePdSh1Sh2asRoot PDidx s /\
 dataStructurePdSh1Sh2asRoot sh1idx s /\
 dataStructurePdSh1Sh2asRoot sh2idx s /\
 currentPartitionInPartitionsList s /\
 noDupMappedPagesList s /\
 noDupConfigPagesList s  /\
 parentInPartitionList s /\
 accessibleVAIsNotPartitionDescriptor s /\
 accessibleChildPageIsAccessibleIntoParent s /\
 noCycleInPartitionTree s /\ 
 configTablesAreDifferent s /\ 
 isChild s /\
 isPresentNotDefaultIff s /\
 physicalPageNotDerived s /\
 multiplexerWithoutParent s /\
 isParent s /\
 noDupPartitionTree s /\
 wellFormedFstShadow s /\
 wellFormedSndShadow s /\
 wellFormedShadows sh1idx s /\
 wellFormedShadows sh2idx s /\
 currentPartitionIsNotDefaultPage s /\
 wellFormedFstShadowIfNone s /\
 wellFormedFstShadowIfDefaultValues s.