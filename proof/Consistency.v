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
   ( stop = level /\ ( (isVE indirection idx s /\ idxroot = sh1idx) \/ 
                       (isVA indirection idx s /\ idxroot = sh2idx) \/ 
                       (isPE indirection idx s /\ idxroot = PDidx) ) ))
                       /\ 
  indirection <> defaultPage)) .

(** ** The [currentPartitionInPartitionsList] property specifies that the 
    current partition must be into the list of partitions retrieved from the 
    first created partition (multiplexer) *)
Definition currentPartitionInPartitionsList (s : state) := 
In (currentPartition s) (getPartitions multiplexer s).

(** ** The [parentInPartitionList] property specifies that the parent of a given 
partition should be into the list of partitions retrieved from the 
    first created partition (multiplexer)  *)
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
 *)
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

(** ** The [noDupMappedPagesList] requires that mapped pages of a single partition
    are different *)
Definition noDupMappedPagesList s :=
forall (partition : page),  
In partition (getPartitions multiplexer s) ->  
 NoDup (getMappedPages partition s).
 
(** ** The [noDupConfigPagesList] requires that configuation tables of
    a single partition are different *)
Definition noDupConfigPagesList s :=
forall idxroot, (idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx) -> 
forall (partition : page),  
In partition (getPartitions multiplexer s) -> 
forall root, nextEntryIsPP partition idxroot root s->
 NoDup (getIndirections root s). 

(** ** Conjunction of all consistency properties *)
Definition consistency s := 
 partitionDescriptorEntry s /\  
 dataStructurePdSh1Sh2asRoot PDidx s /\
 dataStructurePdSh1Sh2asRoot sh1idx s /\
 dataStructurePdSh1Sh2asRoot sh2idx s /\
 currentPartitionInPartitionsList s /\
 noDupMappedPagesList s /\
 noDupConfigPagesList s  /\
 parentInPartitionList s . 