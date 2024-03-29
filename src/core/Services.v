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
    This file contains PIP memory services : [createPartition], 
      [deletePartition], [addVAddr], [removeVAddr], [countToMap], 
      [prepare] and [collect].

    The definitions of recursive functions like [countToMap], [prepare] and 
      [collect] match the same form :
      - part 1 : <<functionNameRec>> is the recursive funtion
      - part 2 : <<functionNameAux>> fixes the sufficient timeout value for recursion 
                 to complete 
      - part 3 : <<funtionName>> is the PIP service. It calls <<functionNameAux>> 
                with the required parameters *)

Require Import Pip.Model.IAL Pip.Model.Hardware Pip.Model.ADT Pip.Model.Lib Pip.Model.MAL Pip.Model.Constants.
Require Import Pip.Core.Internal.
Require Import Bool Arith List.
Import List.ListNotations.

(** ** The createPartition PIP service

    The [createPartition] function creates a new child (sub-partition) into the 
    current partition

    <<descChild>>       a virtual address into the current partition will be used as
                        the partition descriptor of the child 

    <<pdChild>>         a virtual address into the current partition will be used as
                        the page directory of the child (to map virtual addresses) 

    <<shadow1Child>>    a virtual address into the current partition will be used as
                        the root of the first shadow pages of the child (to keep 
                        information about new sub-partition of the child and 
                        the derivation status of mapped virtual addresses of the child) 

    <<shadow2Child>>    a virtual address into the current partition will be used as
                        the root of the second shadow pages of the child (to store 
                        some virtual addresses mapped into the parent. Each virtual 
                        address corresponds to a present page into the child and 
                        derived from his parent)

   <<ConfigPagesList>>  a virtual address into the current partition will be used as
                        the first page of configuration tables list of the child (to 
                        store some virtual addresses mapped into the parent. Each 
                        virtual address is used as configuration table for the child 
                        partition) *)
Definition createPartition (descChild pdChild shadow1Child shadow2Child 
                            ConfigPagesList :vaddr) : LLI bool :=
if (vaddrEq vaddrDefault descChild) 
then ret false
else 
  (** Get the number of MMU levels *) 
  perform nbL := getNbLevel in
  (** Check if virtual addresses are equal *)
  perform refPD := checkVAddrsEqualityWOOffset descChild pdChild nbL in
  perform refSh1 := checkVAddrsEqualityWOOffset descChild shadow1Child nbL in
  perform refSh2 := checkVAddrsEqualityWOOffset descChild shadow2Child nbL in
  perform refList := checkVAddrsEqualityWOOffset descChild ConfigPagesList nbL in
  perform pdSh1 := checkVAddrsEqualityWOOffset pdChild shadow1Child nbL in
  perform pdSh2 := checkVAddrsEqualityWOOffset pdChild shadow2Child nbL in
  perform pdList := checkVAddrsEqualityWOOffset pdChild ConfigPagesList nbL in
  perform sh1Sh2 := checkVAddrsEqualityWOOffset shadow1Child shadow2Child nbL in
  perform sh1List := checkVAddrsEqualityWOOffset shadow1Child ConfigPagesList nbL in
  perform sh2List := checkVAddrsEqualityWOOffset shadow2Child ConfigPagesList nbL in
  if (refPD || refSh1 || refSh2 || refList || pdSh1 || pdSh2 || pdList || sh1Sh2 ||
       sh1List || sh2List) then ret false else
  (** Check if virtual addresses correspond to kernel mapping *)
  perform kmapPR := checkKernelMap descChild in
  perform kmapPD := checkKernelMap pdChild in
  perform kmapSh1 := checkKernelMap shadow1Child in
  perform kmapSh2 := checkKernelMap shadow2Child in
  perform kmapList := checkKernelMap ConfigPagesList in 
  perform defPD :=  compareVAddrToNull pdChild in
  perform defSh1 := compareVAddrToNull shadow1Child in
  perform defSh2 := compareVAddrToNull shadow2Child in
  perform defList := compareVAddrToNull ConfigPagesList in 
  if negb kmapPR && negb kmapPD && negb kmapSh1 && negb kmapSh2 && negb kmapList && negb
  defPD && negb defSh1 && negb defSh2 && negb defList
  then
    (** Get the current partition  *)
    perform currentPart := getCurPartition in
    (** Get the pd of the current partition *)
    perform currentPD := getPd currentPart in
    (** Check if descChild is present and accessible (This information is stored into the
        the page directory structure of the parent) *)
    perform ptDescChildFromPD := getTableAddr currentPD descChild nbL in
    perform isNull := comparePageToNull ptDescChildFromPD in
    if isNull then ret false else
    perform idxDescChild := getIndexOfAddr descChild levelMin in
    (** True if present *)
    perform presentDescChild := readPresent ptDescChildFromPD idxDescChild in
    (** True if accessible *)
    perform accessDescChild := readAccessible ptDescChildFromPD idxDescChild in
    
    (**  Check if pdChild is present and accessible (This information is stored into the
        the page directory structure of the parent) *)
    perform ptPDChildFromPD := getTableAddr currentPD pdChild nbL in
    perform isNull := comparePageToNull ptPDChildFromPD in
    if isNull then ret false else
    perform idxPDChild := getIndexOfAddr pdChild levelMin in
    (** True if present *)
    perform presentPDChild := readPresent ptPDChildFromPD idxPDChild in
    (** True if accessible *)
    perform accessPDChild := readAccessible ptPDChildFromPD idxPDChild in

    (**  Check if shadow1Child is present and accessible (This information is stored into the
        the page directory structure of the parent) *)
    perform ptSh1ChildFromPD := getTableAddr currentPD shadow1Child nbL in
    perform isNull := comparePageToNull ptSh1ChildFromPD in
    if isNull then ret false else
    perform idxSh1Child := getIndexOfAddr shadow1Child levelMin in
    (** True if present *)
    perform presentSh1Child := readPresent ptSh1ChildFromPD idxSh1Child in
     (** True if accessible *)
    perform accessSh1Child := readAccessible ptSh1ChildFromPD idxSh1Child in

    (**  Check if shadow2Child is present and accessible (This information is stored into the
        the page directory structure of the parent) *)
    perform ptSh2ChildFromPD := getTableAddr currentPD shadow2Child nbL  in
    perform isNull := comparePageToNull ptSh2ChildFromPD in
    if isNull then ret false else
    perform idxSh2Child := getIndexOfAddr shadow2Child levelMin  in
    (** True if present *)
    perform presentSh2Child := readPresent ptSh2ChildFromPD idxSh2Child  in
     (** True if accessible *)
    perform accessSh2Child := readAccessible ptSh2ChildFromPD idxSh2Child  in

    (**  Check if configPagesListChild is present and accessible (This information is stored into the
        the page directory structure of the parent) *)
    perform ptConfigPagesList := getTableAddr currentPD ConfigPagesList nbL in
    perform isNull := comparePageToNull ptConfigPagesList in
    if isNull then ret false else
    perform idxConfigPagesList := getIndexOfAddr ConfigPagesList levelMin in
    (** True if present *)
    perform presentConfigPagesList := readPresent ptConfigPagesList idxConfigPagesList in
     (** True if accessible *)
    perform accessConfigPagesList := readAccessible ptConfigPagesList idxConfigPagesList in

    if (presentDescChild  && accessDescChild && presentPDChild && accessPDChild && 
        presentConfigPagesList && accessConfigPagesList && presentSh1Child  && 
        accessSh1Child && presentSh2Child && accessSh2Child )
    then (** all virtual addresses are accesible and present *)
      (** Check if descChild is already derived (this information is stored into
          the first shadow structure of the parent)  *)
      perform  currentShadow1 := getFstShadow currentPart in
      perform  ptDescChildFromSh1 := getTableAddr currentShadow1 descChild nbL in
      perform isNull := comparePageToNull ptDescChildFromSh1 in
      if isNull then ret false else
      (**  true if derived *)
      perform  derivedDescChild := checkDerivation ptDescChildFromSh1 idxDescChild in

      (** Check if pdChild is already derived (this information is stored into
          the first shadow structure of the parent)  *)
      perform ptPDChildFromSh1 := getTableAddr currentShadow1 pdChild nbL in
      perform isNull := comparePageToNull ptPDChildFromSh1 in
      if isNull then ret false else
      (**  true if derived *)
      perform  derivedPDChild := checkDerivation ptPDChildFromSh1 idxPDChild in

      (** Check if shadow1Child is already derived (this information is stored into
          the first shadow structure of the parent)  *)
       perform ptSh1ChildFromSh1 := getTableAddr currentShadow1 shadow1Child nbL in
      perform isNull := comparePageToNull ptSh1ChildFromSh1 in
      if isNull then ret false else
      (**  true if derived *)
      perform  derivedSh1Child := checkDerivation ptSh1ChildFromSh1 idxSh1Child in

      (** Check if shadow2Child is already derived (this information is stored into
          the first shadow structure of the parent)  *)
      perform  ptSh2ChildFromSh1 := getTableAddr currentShadow1 shadow2Child nbL in
      perform isNull := comparePageToNull ptSh2ChildFromSh1 in
      if isNull then ret false else
      (**  true if derived *)
      perform  derivedSh2Child := checkDerivation ptSh2ChildFromSh1  idxSh2Child in

      (** Check if descChild is already derived (this information is stored into
          the first shadow structure of the parent)  *)
      perform  ptConfigPagesListFromSh1 := getTableAddr currentShadow1 ConfigPagesList nbL in
      perform isNull := comparePageToNull ptConfigPagesListFromSh1 in
      if isNull then ret false else
      (**  true if not derived *)
      perform derivedConfigPagesList := checkDerivation ptConfigPagesListFromSh1 idxConfigPagesList in

      if (derivedDescChild && derivedPDChild && derivedSh1Child  && derivedSh2Child
      && derivedConfigPagesList )
      then (** all virtual addresses are not derived *)
                                   (** UPDATE MEMORY *)
        (** Get physical addresses of all given virtual addresses *)
        (** pdChild virtual address *)
        perform phyPDChild  := readPhyEntry ptPDChildFromPD idxPDChild in
        (* perform isNull := comparePageToNull phyPDChild in
        if isNull then ret false else *)

        (** shadow1Child virtual address *)
        perform phySh1Child := readPhyEntry ptSh1ChildFromPD idxSh1Child in
        (* perform isNull := comparePageToNull phySh1Child in
        if isNull then ret false else *)

        (** shadow2Child virtual address *)
        perform phySh2Child := readPhyEntry ptSh2ChildFromPD idxSh2Child in
        (* perform isNull := comparePageToNull phySh2Child in
        if isNull then ret false else *)

        (** ConfigPagesList virtual address *)
        perform  phyConfigPagesList := readPhyEntry ptConfigPagesList idxConfigPagesList in
        (* perform isNull := comparePageToNull phyConfigPagesList in
        if isNull then ret false else *)

        (** descChild virtual address *)
        perform phyDescChild := readPhyEntry ptDescChildFromPD idxDescChild in
        (* perform isNull := comparePageToNull phyDescChild in
        if isNull then ret false else *)

        (**  Set all given pages as not accessible *)
        writeAccessible ptPDChildFromPD idxPDChild false ;;
        writeAccessibleRec pdChild currentPart false ;;
        
        writeAccessible ptSh1ChildFromPD idxSh1Child false ;;
        writeAccessibleRec shadow1Child currentPart false ;;
         
        writeAccessible ptSh2ChildFromPD idxSh2Child false ;;
        writeAccessibleRec shadow2Child currentPart false;;
        
        writeAccessible ptConfigPagesList idxConfigPagesList false ;;
        writeAccessibleRec ConfigPagesList currentPart false;;
        
        writeAccessible ptDescChildFromPD idxDescChild false ;; 
        writeAccessibleRec descChild currentPart false;;
        (** Set all given pages as not accessible in all ancestors **)

        perform zero := getIdx0 in
        (** Initialize phyPDChild table *)
        initPEntryTable phyPDChild zero;;
        (** Add the kernel mapping *)
        perform kidx := getIdxKernel in
        mapKernel phyPDChild kidx;;
        (** Initialize phySh1Child table *)
        initFstShadow phySh1Child nbL zero;;


        (** Initialize phySh2Child table *)
        initSndShadow phySh2Child nbL zero;;

        (** Initialize phyConfigPagesList table *)
        initConfigPagesList phyConfigPagesList zero ;;

        (** Add descChild and its physical address into itself (the partion descriptor) *)
        perform nullVA :=  getVaddrDefault in
        perform idxPR := getIdxPartDesc in
        perform idxPD := getIdxPageDir in
        perform idxSh1 := getIdxShadow1 in
        perform idxSh2 := getIdxShadow2 in
        perform idxListConf := getIdxShadow3 in
        perform idxPRP := getIdxParentDesc in 
        updatePartitionDescriptor phyDescChild idxPR phyDescChild descChild ;;

        (** Add pdChild and its physical address into the partition descriptor page *)
        (* perform idxPD := getPDidx in *)
        updatePartitionDescriptor phyDescChild idxPD phyPDChild pdChild ;;

        (** Add shadow1Child and its physical address into the partition descriptor *)
        (* perform idxSh1 := getSh1idx in *)
        updatePartitionDescriptor phyDescChild idxSh1 phySh1Child shadow1Child ;;

        (** Add shadow2Child and its physical address into the partition descriptor *)
        (* perform idxSh2 := getSh2idx in *)
        updatePartitionDescriptor phyDescChild idxSh2 phySh2Child shadow2Child ;;

        (** Add ConfigPagesList and its physical address into the partition descriptor *)
        (* perform idxListConf := getSh3idx in *)
        updatePartitionDescriptor phyDescChild idxListConf phyConfigPagesList ConfigPagesList ;;

        (** Add parent physical address into the partition descriptor of the child*)
        (* perform idxPRP := getPPRidx in *)
        updatePartitionDescriptor phyDescChild idxPRP currentPart nullVA ;;

        (** Set the virtual address pdChild as derived by the new child *)
        writeVirEntry ptPDChildFromSh1 idxPDChild descChild ;;
        (**  Set the virtual address shadow1Child as derived by the new child *)
        writeVirEntry ptSh1ChildFromSh1 idxSh1Child descChild ;; 
        (**  Set the virtual address shadow2Child as derived by the new child *)
        writeVirEntry ptSh2ChildFromSh1 idxSh2Child descChild ;; 
        (**  Set the virtual address list as derived by the new child *)
        writeVirEntry ptConfigPagesListFromSh1 idxConfigPagesList descChild ;;

        
        (** Set the virtual address descChild as a partition (new child) in parent *)
        writePDflag ptDescChildFromSh1 idxDescChild true ;; 
        ret true
      else ret false
    else ret false
  else ret false.

(** ** The countToMap PIP service 

    This service returns the amount of configuration tables needed to perform a 
    mapping for a given virtual address *)
(** - The [countToMapRec] is the recursive function of [countToMap]

     <<timeout>>                fixes how many times the function should be called 
                                before the program terminates

     <<pdChild>>                a physical address of an indirection into a child
                                page directory

     <<configPagesListChild>>   a physical address of a page into the a child 
                                configuration tables linked list

     <<va>>                     The virtual address to map

     <<nbL>>                    a level number of the MMU *)
Fixpoint countToMapRec timeout (pdChild configPagesListChild: page) (va : vaddr) (nbL : level)  :=
  match timeout with
  | 0 => getCount0 
  | S timeout1 =>
  perform isNotfstLevel := levelGtM nbL levelMin in 
    if isNotfstLevel
    then
      (** Get the index in va that corresponds to the current level *)
      perform idx := getIndexOfAddr va nbL in
      (** Get the page stored at this index into pdChild *)
      perform addr := readPhyEntry pdChild idx in
      (** Compare the page to the default page *)
      perform null := getPageDefault in
      perform cmp := pageEqM  addr null in

      (**  If we have no table here, we're done : (level - 1) is the amount of
        pages we need, and we need the same amount for both shadow pages *)
      if cmp
        then
        (**  Now we have to check if we have enough space in shadow 3 to map all this *)
        perform zeroI := getIdx0 in
        perform zeroC := getCount0 in
        perform lastLLTable := checkEnoughEntriesLinkedList configPagesListChild in 
        perform isNull := comparePageToNull lastLLTable in
        (* Check if we need to insert a new page at the end of the linked list *)  
        if (isNull) then (* We don't need to link a new LL table *)  
            perform prod3 := countFromLevelM nbL in
            countSuccM prod3  (**  Not enough space, we need another shadow 3 page *)
          else countFromLevelM nbL (**  Enough space, never mind *)
        else
        perform levelPred := levelPredM nbL in
        countToMapRec timeout1 addr configPagesListChild va levelPred
    else getCount0 (**  Everything is mapped : we need no additional pages *)
  end.

(** - The [countToMapAux] fixes the timout value of [countToMapRec] *)
Definition countToMapAux  (pdChild configPagesListChild: page) (va : vaddr)  (nbL : level):=
  countToMapRec nbLevel  pdChild configPagesListChild va nbL.

(** - The [countToMap] prepares the [countToMapAux] required parameters 

    [descChild] The partition descriptor of the child 

    [vaChild]   The virtual address in which we will perform the mapping
 *)
Definition countToMap (descChild vaChild : vaddr) :=
  (**  Get the current partition  *)
  perform currentPart := getCurPartition in
  (** Get the pd of the current partition *)
  perform currentPD := getPd currentPart in
  (** Get the number of levels *)
  perform nbL :=  getNbLevel in
  (** Get the physical address of the reference page of the child *)
  perform ptDescChildFromPD := getTableAddr currentPD descChild nbL in
  perform isNull := comparePageToNull ptDescChildFromPD in 
  if isNull then getCount0 else
  perform idxDescChild := getIndexOfAddr descChild levelMin in
  perform phyDescChild := readPhyEntry ptDescChildFromPD idxDescChild in
  (** Get the physical address of the page directory of the child *)
  perform phyPDChild := getPd phyDescChild in
  (** Get the third shadow of the child *)
  perform configPagesListChild := getConfigTablesLinkedList phyDescChild in 
  (** Call  countToMapAux *)
  countToMapAux phyPDChild configPagesListChild vaChild nbL.

(** ** The prepare PIP service 

    This service adds required configuration tables into a child partition to map new 
    virtual address *)
(** - The [prepareRec] is the recursive function of [prepare] 

      <<timeout>> fixes how many times the function should be called 
                  before the program terminates

      <<descChild>> the virtual address of the child partition descriptor

      <<phyPDChild>> the physical address of an indirection into the page directory
                     configuration tables structure. This indirection corresponds 
                     to the given MMU level number <<nbL>> and virtual address <<va>>

      <<phySh1Child>> the physical address of an indirection into the first shadow
                     configuration tables structure. This indirection corresponds 
                     to the given MMU level number <<nbL>> and virtual address <<va>>

      <<phySh2Child>> the physical address of an indirection into the second shadow
                     configuration tables structure. This indirection corresponds 
                     to the given MMU level number <<nbL>> and virtual address <<va>>

      <<phyConfigPagesList>> the physical address of the child configuration tables
                             list 

      <<va>> the virtual address to prepare

      <<fstVA>> the virtual address of the first new configuration table to add by 
                prepare

      <<needNewConfigPagesList>> is true if we need to link a new page into the 
                                 configuration tables list 

      <<nbL>> a level number of the MMU
 *) 
Fixpoint prepareRec timeout (descChild : vaddr) (phyDescChild phyPDChild phySh1Child 
phySh2Child lastLLtable : page)(vaToPrepare : vaddr) (fstVA : vaddr) 
 (nbL : level) : LLI boolvaddr :=
  match timeout with
  | 0 => prepareType false fstVA
  | S timeout1 =>
  perform islevel0 := levelEqM nbL levelMin in
  if islevel0 then prepareType true fstVA
  else 
  perform isNull := compareVAddrToNull fstVA in 
  if isNull then prepareType false fstVA
  else
    (*  Get the current partition  *)
    perform currentPart := getCurPartition in
    (* Get current partition data structures *)
    perform currentPD := getPd currentPart in
    perform currentSh1 := getFstShadow currentPart in
    perform currentSh2 := getSndShadow currentPart in
    (* Check if the current MMU level needs to be configued *)
    perform idxToPrepare := getIndexOfAddr vaToPrepare nbL in (**  Get index of address at the current indirection level *)
    perform indMMUToPrepare := readPhyEntry phyPDChild idxToPrepare in (**  Read stored address *)
    perform isNull := comparePageToNull indMMUToPrepare in
    if (negb isNull) then 
    (* This MMU level is already configued *)
    perform levelPred := levelPredM nbL in
    perform indSh1ToPrepare := readPhyEntry phySh1Child idxToPrepare in 
    perform indSh2ToPrepare := readPhyEntry phySh2Child idxToPrepare in
    (* Move to the next MMU level *)
    prepareRec timeout1 descChild phyDescChild indMMUToPrepare indSh1ToPrepare indSh2ToPrepare lastLLtable vaToPrepare fstVA levelPred
    else (* The current level should be configued *)
      perform nbLgen := getNbLevel in
      perform idxstorefetch := getIdxStoreFetch in 
   (* Get the FIRST virtual addresses and check if null, present and accessible *)
      perform idxFstVA :=  getIndexOfAddr fstVA levelMin in
      perform ptMMUFstVA := getTableAddr currentPD  fstVA nbLgen in
      (* fstVA : check if there is a mapping *) 
      perform isNull := comparePageToNull ptMMUFstVA in 
      if isNull then prepareType false fstVA else 
      (* fstVA : check if accessible *) 
      perform fstVAisAccessible := readAccessible ptMMUFstVA idxFstVA in
      if negb fstVAisAccessible then prepareType false fstVA else 
      (* fstVA : check if present *) 
      perform fstVAisPresent := readPresent ptMMUFstVA idxFstVA in
      if negb fstVAisPresent then prepareType false fstVA else 
      (* fstVA : get the physical page *)
      perform phyMMUaddr := readPhyEntry ptMMUFstVA idxFstVA in
      (* read the content of fstVA : it should be sndVA *)
      perform sndVA := readVirtualUser phyMMUaddr idxstorefetch in 
      (* check if sndVA is null *)
      perform isNull := compareVAddrToNull sndVA in 
      if isNull then prepareType false fstVA else
   (* Get the SECOND virtual addresses and check if null, present and accessible *)
      perform idxSndVA :=  getIndexOfAddr sndVA levelMin in
      perform ptMMUSndVA := getTableAddr currentPD  sndVA nbLgen in
      (* fstVA : check if there is a mapping *) 
      perform isNull := comparePageToNull ptMMUSndVA in 
      if isNull then prepareType false fstVA else 
      (* fstVA : check if accessible *) 
      perform sndVAisAccessible := readAccessible ptMMUSndVA idxSndVA in
      if negb sndVAisAccessible then prepareType false fstVA else 
      (* fstVA : check if present *) 
      perform sndVAisPresent := readPresent ptMMUSndVA idxSndVA in
      if negb sndVAisPresent then prepareType false sndVA else 
      (* fstVA : get the physical page *)
      perform physh1addr := readPhyEntry ptMMUSndVA idxSndVA in
      (* read the content of fstVA : it should be sndVA *)
      perform trdVA := readVirtualUser physh1addr idxstorefetch in 
      (* check if sndVA is null *)
      perform isNull := compareVAddrToNull trdVA in 
      if isNull then prepareType false fstVA else
      perform zeroI := getIdx0 in
      (** Check if virtual addresses are equal *)
      perform v1v2 := checkVAddrsEqualityWOOffset fstVA sndVA nbLgen in
      perform v1v3 := checkVAddrsEqualityWOOffset fstVA trdVA nbLgen in
      perform v2v3 := checkVAddrsEqualityWOOffset sndVA trdVA nbLgen in
      if (v1v2 || v1v3 || v2v3) then prepareType false fstVA else
      (* Check if the next three virtual addresses could be lent to the kernel *)

      (** FST addr : check sharing *)
      perform ptSh1FstVA := getTableAddr currentSh1 fstVA nbLgen in
      perform isNull := comparePageToNull ptSh1FstVA in
      if isNull then prepareType false fstVA else
      perform fstVAnotShared := checkDerivation ptSh1FstVA idxFstVA in

      (** SND addr : check sharing *)
      perform ptSh1SndVA := getTableAddr currentSh1 sndVA nbLgen in
      perform isNull := comparePageToNull ptSh1SndVA in
      if isNull then prepareType false fstVA else
      perform sndVAnotShared := checkDerivation ptSh1SndVA idxSndVA in

      (** TRD Addr *)
      (* Get the THIRD virtual addresses and check if null, present and accessible *)
      perform idxTrdVA :=  getIndexOfAddr trdVA levelMin in
      perform ptMMUTrdVA := getTableAddr currentPD  trdVA nbLgen in
      (* fstVA : check if there is a mapping *) 
      perform isNull := comparePageToNull ptMMUTrdVA in 
      if isNull then prepareType false fstVA else 
      (* fstVA : check if accessible *) 
      perform trdVAisAccessible := readAccessible ptMMUTrdVA idxTrdVA in
      if negb trdVAisAccessible then prepareType false fstVA else 
      (* fstVA : check if present *) 
      perform trdVAisPresent := readPresent ptMMUTrdVA idxTrdVA in
      if negb trdVAisPresent then prepareType false trdVA else 
      (* fstVA : get the physical page *)
      perform physh2addr := readPhyEntry ptMMUTrdVA idxTrdVA in
      (* Check sharing *)
      perform ptSh1TrdVA := getTableAddr currentSh1 trdVA nbLgen in
      perform isNull := comparePageToNull ptSh1TrdVA in
      if isNull then prepareType false fstVA else
      perform trdVAnotShared := checkDerivation ptSh1TrdVA idxTrdVA in

      (* Check if the current MMU level could be configued according to the properties about the first free pages given by the partition *)
      if (fstVAnotShared && sndVAnotShared && trdVAnotShared) then
      perform newLastLLable := checkEnoughEntriesLinkedList lastLLtable in 
      perform isNull := comparePageToNull newLastLLable in
      (* Check if we need to insert a new page at the end of the linked list *)  
      if (negb isNull) then (* We don't need to link a new LL table *)  
        (* read the content of trdVA : it should be nextVA *)
        perform nextVA := readVirtualUser physh2addr idxstorefetch in 
        (**  Set all given pages as not accessible into parent and ancestors *)
        writeAccessible ptMMUFstVA idxFstVA false ;;
        writeAccessibleRec fstVA currentPart false ;;
        writeAccessible ptMMUSndVA idxSndVA false ;;
        writeAccessibleRec sndVA currentPart false ;;
        writeAccessible ptMMUTrdVA idxTrdVA false ;;
        writeAccessibleRec trdVA currentPart false ;;

        (* Initialize tables *)
        perform nbLPred := levelPredM nbL in
        initPEntryTable phyMMUaddr zeroI;;
        initFstShadow physh1addr nbLPred zeroI;;
        initSndShadow physh2addr nbLPred zeroI;;

        (* Set used pages as shared *)
        writeVirEntry ptSh1FstVA idxFstVA fstVA ;;
        writeVirEntry ptSh1SndVA idxSndVA sndVA ;;
        writeVirEntry ptSh1TrdVA idxTrdVA trdVA ;;

        (* Store phy/virt addresses into LL *)
        insertEntryIntoLL newLastLLable fstVA phyMMUaddr ;;
        insertEntryIntoLL newLastLLable sndVA physh1addr ;;
        insertEntryIntoLL newLastLLable trdVA physh2addr ;;

        (*  Insert pages into the current level *)
        writePhyEntry phyPDChild idxToPrepare phyMMUaddr true true true true true ;; 
        writePhyEntry phySh1Child idxToPrepare physh1addr true true true true true ;;
        writePhyEntry phySh2Child idxToPrepare physh2addr true true true true true ;;

        prepareRec timeout1 descChild phyDescChild phyMMUaddr physh1addr physh2addr lastLLtable vaToPrepare nextVA  nbLPred
        else 

        (* FTH Addr *)
        (* Get the next Virtual address *)

        perform fthVA := readTableVirtual trdVA idxstorefetch in     
        perform isNull := compareVAddrToNull fthVA in 
        if isNull then prepareType false fstVA
        else 
        (*** Check equality *)
        perform v4v1 := checkVAddrsEqualityWOOffset fthVA fstVA nbLgen in
        perform v4v2 := checkVAddrsEqualityWOOffset fthVA sndVA nbLgen in
        perform v4v3 := checkVAddrsEqualityWOOffset fthVA trdVA nbLgen in
        if (v4v1 || v4v2 || v4v3) then prepareType false fstVA else
        (* Get the page table and the index in which sndVA is mapped *)
        perform idxFthVA :=  getIndexOfAddr fthVA levelMin in
        perform ptMMUFthVA := getTableAddr currentPD  fthVA nbLgen in
        perform ptSh1FthVA := getTableAddr currentSh1 fthVA nbLgen in
        perform fthVAisOK := verifyProperties ptMMUFthVA ptSh1FthVA idxFthVA in 
        if (negb fthVAisOK) then prepareType false fstVA
        else 
        (**  Get the physical address *)
        perform newFstLL := readPhyEntry ptMMUFthVA idxFthVA in
        perform nextVA := readTableVirtual fthVA idxstorefetch in

        (** set fthVA as not accessible **)
        writeAccessible ptMMUFthVA idxFthVA false ;;
        writeAccessibleRec fthVA currentPart false ;;

        (* Set used pages as shared *)
        writeVirEntry ptSh1FthVA idxFthVA fthVA ;;

        (** link new page in LL *) 
        PushNewPageOntoLL phyDescChild newFstLL fthVA ;;

        (*  Get physical addresses *)
        perform phyMMUaddr := readPhyEntry ptMMUFstVA idxFstVA in 
        perform physh1addr := readPhyEntry ptMMUSndVA idxSndVA in 
        perform physh2addr := readPhyEntry ptMMUTrdVA idxTrdVA in 

        (**  Set all given pages as not accessible into parent and ancestors *)
        writeAccessible ptMMUFstVA idxFstVA false ;;
        writeAccessibleRec fstVA currentPart false ;;
        writeAccessible ptMMUSndVA idxSndVA false ;;
        writeAccessibleRec sndVA currentPart false ;;
        writeAccessible ptMMUTrdVA idxTrdVA false ;;
        writeAccessibleRec trdVA currentPart false ;;

        (* Initialize tables *)
        perform nbLPred := levelPredM nbL in
        initPEntryTable phyMMUaddr zeroI;;
        initFstShadow physh1addr nbLPred zeroI;;
        initSndShadow physh2addr nbLPred zeroI;;

        (* Set used pages as shared *)
        writeVirEntry ptSh1FstVA idxFstVA fstVA ;;
        writeVirEntry ptSh1SndVA idxSndVA sndVA ;;
        writeVirEntry ptSh1TrdVA idxTrdVA trdVA ;;

        (* Store phy/virt addresses into LL *)
        insertEntryIntoLL newFstLL fstVA phyMMUaddr ;;
        insertEntryIntoLL newFstLL sndVA physh1addr ;;
        insertEntryIntoLL newFstLL trdVA physh2addr ;;

        (*  Insert pages into the current level *)
        writePhyEntry phyPDChild idxToPrepare phyMMUaddr true true true true true ;; 
        writePhyEntry phySh1Child idxToPrepare physh1addr true true true true true ;;
        writePhyEntry phySh2Child idxToPrepare physh2addr true true true true true ;;

        prepareRec timeout1 descChild phyDescChild phyMMUaddr physh1addr physh2addr newFstLL vaToPrepare nextVA nbLPred  

    else prepareType false fstVA  
  end.

(** - The [prepareAux] fixes the timout value of [prepareRec] *)
Definition prepareAux (descChild : vaddr) (phyDescChild pd : page) (phySh1Child : page) (phySh2Child : page) (phyConfigPagesList : page) (va : vaddr)
  (fstVA : vaddr) (nbL : level) :=
  prepareRec boundNbLevel descChild phyDescChild pd phySh1Child phySh2Child phyConfigPagesList va fstVA  nbL.

(** The [prepare] function fixes the [prepareAux] required parameters values

    <<descChild>> The virtual address of the partition descriptor of the child

    <<va>> The virtual address to map into the child

    <<fstVA>> The first virtual address to be used as a configuration tables into
              child (the partition must provide to PIP a linkList of virtual 
              addresses which will be used as configuration tables into the 
              child partion; fstVA is the header of this linkList)

Before starting configuration we should verifiy that  <<descChild>> is a child partition
  *)
Definition prepare (descChild : vaddr)  (va : vaddr) (fstVA : vaddr): LLI boolvaddr :=
  (**  Get the current partition  *)
  perform currentPart := getCurPartition in
  (** Get the pd of the current partition *)
  perform currentPD := getPd currentPart in
  perform nbL :=  getNbLevel in
  perform check := checkChild currentPart nbL descChild in
  if(check)
  then
    perform ptDescChildFromPD := getTableAddr currentPD descChild nbL in
    perform isNull := comparePageToNull ptDescChildFromPD in if isNull then prepareType false fstVA else
    perform idxDescChild := getIndexOfAddr descChild levelMin in
    perform presentPhyDesc := readPresent ptDescChildFromPD idxDescChild in
    if negb presentPhyDesc 
     then prepareType false fstVA
     else
      perform phyDescChild := readPhyEntry ptDescChildFromPD idxDescChild in
      perform phyPDChild := getPd phyDescChild in
      perform phySh1Child := getFstShadow phyDescChild in
      perform phySh2Child := getSndShadow phyDescChild in
      perform phyConfigPagesList  := getConfigTablesLinkedList phyDescChild in
      prepareAux descChild phyDescChild phyPDChild phySh1Child phySh2Child phyConfigPagesList va fstVA  nbL
  else prepareType false fstVA.

(** ** The addVAddr PIP service *)
(** The [addVAddr] function maps a virtual address into the given child 

    <<vaInCurrentPartition>> The virtual address mapped into parent

    <<descChild>>            The virtual address of the partition descriptor of 
                           the child

    <<vaChild>>              The virtual address to be mapped into the child 
    
    <<r w e>>            Read, write and execute rights
  *)
Definition addVAddr (vaInCurrentPartition : vaddr) (descChild : vaddr) (vaChild : vaddr) (r w e : bool) : LLI bool :=
  perform vaisnull1 := compareVAddrToNull vaInCurrentPartition in 
  if vaisnull1 then ret false else 
  perform vaisnull2 := compareVAddrToNull descChild in 
  if vaisnull2 then ret false else 
  perform kmapVaParent := checkKernelMap vaInCurrentPartition in
  perform kmapVaChild := checkKernelMap vaChild in
  if (negb kmapVaParent && negb kmapVaChild)
  then
    perform rcheck := checkRights r w e in
    if (rcheck)
    then
      (**  Get the current partition  *)
      perform currentPart := getCurPartition in
      (** Get the number of levels *)
      perform nbL :=  getNbLevel in
      (** check whether pd is a pd or not *)
      perform check := checkChild currentPart nbL descChild in
      if(check)
      then
        (** access to the first shadow page of the current page directory *)
        perform currentShadow1 := getFstShadow currentPart in
        perform ptVACurPartFromSh1 := getTableAddr currentShadow1 vaInCurrentPartition nbL in
        perform isNull := comparePageToNull ptVACurPartFromSh1 in if isNull then ret false else
        perform idxVaInCurrentPartition := getIndexOfAddr vaInCurrentPartition levelMin in
        (** 1 if the page is derived (use boolean) *)
        perform deriv := checkDerivation ptVACurPartFromSh1 idxVaInCurrentPartition in
        (** Get the pd of the current partition *)
        perform currentPD := getPd currentPart in
        (** Get the page table of the current pd in which the virtual address vaInCurrentPartition is mapped  *)
        perform ptVaInCurrentPartitionFromPD := getTableAddr currentPD vaInCurrentPartition nbL in
        perform isNull := comparePageToNull ptVaInCurrentPartitionFromPD in if isNull then ret false else
        (** true if the page is accessible *)
        perform access := readAccessible ptVaInCurrentPartitionFromPD idxVaInCurrentPartition in

        (*FIXED*) perform presentmap := readPresent ptVaInCurrentPartitionFromPD idxVaInCurrentPartition in

        (** Get the physical address of the reference page of the child *)
        perform ptDescChildFromPD := getTableAddr currentPD descChild nbL in
        perform isNull := comparePageToNull ptDescChildFromPD in if isNull then ret false else
        perform idxDescChild := getIndexOfAddr descChild levelMin in

        (*FIXED*) perform presentPhyDesc := readPresent ptDescChildFromPD idxDescChild in

        if (negb presentPhyDesc) then ret false else
        perform phyDescChild := readPhyEntry ptDescChildFromPD idxDescChild in
        (** Get the physical address of the page directory of the child *)
        perform phyPDChild := getPd phyDescChild in
        (** Get the page table and the index in which the new address will be mapped *)
        perform ptVaChildFromPD := getTableAddr phyPDChild vaChild nbL in
        perform isNull := comparePageToNull ptVaChildFromPD in if isNull then ret false else
        perform idxDescChild := getIndexOfAddr vaChild levelMin in
        (** 1 if there is a mapping into the target entry *)
        perform present := readPresent ptVaChildFromPD idxDescChild in
        (** if the page is accessible in the current virtual space,
          not derived and there is no mapping into the target entry *)
        if ( deriv  && access && presentmap && ( negb present ) )
        then
          (** Get the value of the entry in which the page is mapped *)
          perform phyVaInCurrentPartition := readPhyEntry ptVaInCurrentPartitionFromPD idxVaInCurrentPartition in
          (** Add the virtual address vaInCurrentPartition into the second shadow page of the child *)
          perform shadow2Child := getSndShadow phyDescChild in
          perform ptVaChildFromSh2 := getTableAddr shadow2Child vaChild nbL in
          perform isNull := comparePageToNull ptVaChildFromSh2 in if isNull then ret false else
          writeVirtual ptVaChildFromSh2 idxDescChild vaInCurrentPartition;; 
          (** mark the page as derived (write the virtual
            address of the page directory into the current space) *)
          writeVirEntry ptVACurPartFromSh1 idxVaInCurrentPartition descChild ;;
          (** Add mapping (physical page - accessible - present *)
          writePhyEntry ptVaChildFromPD idxDescChild phyVaInCurrentPartition true true r w e ;;   
          ret true
        else ret false
      else ret false
    else ret false
  else ret false.

Definition mappedInChild (vaChild : vaddr) : LLI vaddr := 
  (**  Get the current partition  *)
  perform currentPart := getCurPartition in
  (** Get the number of levels *)
  perform nbL :=  getNbLevel in
      (** Get the pd of the current partition *)
    perform currentPD := getPd currentPart in
    (** Check if descChild is present and accessible (This information is stored into the
        the page directory structure of the parent) *)
    perform ptDescChildFromPD := getTableAddr currentPD vaChild nbL in
    perform isNull := comparePageToNull ptDescChildFromPD in
    if isNull then ret vaddrDefault else
    perform idxDescChild := getIndexOfAddr vaChild levelMin in
    (** True if present *)
    perform presentDescChild := readPresent ptDescChildFromPD idxDescChild in
    (** True if accessible *)
    perform accessDescChild := readAccessible ptDescChildFromPD idxDescChild in
 if (presentDescChild  && accessDescChild) then   
  (** access to the first shadow page of the current page directory *)
  perform currentShadow1 := getFstShadow currentPart in
  perform ptVaChildFromSh1 := getTableAddr currentShadow1 vaChild nbL in
  perform isNull := comparePageToNull ptVaChildFromSh1 in if isNull then ret vaddrDefault else
  perform idxVaChild := getIndexOfAddr vaChild levelMin in
  (** 1 if the page is derived (use boolean) *)
  readVirEntry ptVaChildFromSh1 idxVaChild
else ret vaddrDefault.



(** ** The removeVAddr PIP service *)
(** The [removeVAddr] function removes a given mapping from a given child 

    <<descChild>>  The virtual address of the partition descriptor of the child

    <<vaChild>>    The mapping to remove
*)
Definition removeVAddr (descChild : vaddr) (vaChild : vaddr) :=
  perform kmapVaChild := checkKernelMap vaChild in
  if kmapVaChild then ret false else
    (**  Get the current partition  *)
    perform currentPart := getCurPartition in
    (** Get the number of levels *)
    perform nbL := getNbLevel in
    (** check whether pd is a pd or not *)
    perform check := checkChild currentPart nbL descChild in
    if(negb check) then ret false (*getDefaultVAddr*) else
    (** Get the pd of the current partition *)
    perform currentPD := getPd currentPart in
      (** Get the physical address of the reference page of the child *)
      perform ptDescChildFromPD := getTableAddr currentPD descChild nbL in
      perform isNull := comparePageToNull ptDescChildFromPD in if isNull then ret false else
      perform idxDescChild := getIndexOfAddr descChild levelMin in
      perform present := readPresent ptDescChildFromPD idxDescChild in
      if (negb present) then ret false else 
      perform phyDescChild := readPhyEntry ptDescChildFromPD idxDescChild in
      (** Get the physical address of the page directory of the child *)
      perform phyPDChild := getPd phyDescChild in
      (** Get the page table and the index in which the address is mapped *)
      perform idxvaChild := getIndexOfAddr vaChild levelMin in
      perform ptvaChildFromPD := getTableAddr phyPDChild vaChild nbL in
      perform isNull := comparePageToNull ptvaChildFromPD in if isNull then ret false else
      (**  true if accessible *)
      perform access := readAccessible ptvaChildFromPD idxvaChild in
      (**  true if present *)
      perform present := readPresent ptvaChildFromPD idxvaChild in
      (**  access to the first shadow page of the child to test whether the page is derived or not *)
      perform shadow1Child := getFstShadow phyDescChild in
      perform ptVaChildFromSh1 := getTableAddr shadow1Child vaChild nbL in
      perform isNull := comparePageToNull ptVaChildFromSh1 in if isNull then ret false else
      (**  false if not derived *)
      perform deriv := checkDerivation ptVaChildFromSh1 idxvaChild in
      if (access && deriv && present )
      then
       
        (**  access to the second shadow page of the child to determine the
          virtual address which map this page into the current page directory *)
        perform shadow2Child := getSndShadow phyDescChild in
        perform ptVaChildFromSh2 := getTableAddr shadow2Child vaChild nbL in
        perform isNull := comparePageToNull ptVaChildFromSh2 in if isNull then ret false else
        (**  Get the virtual address into the current page directory *)
        perform vaInParent := readVirtual ptVaChildFromSh2 idxvaChild in
        (**  access to the first shadow page of the current page directory
          to mark the entry that correspond to the virtual address vaInCurrentPartition as underived*)
        perform currentSh1 := getFstShadow currentPart in
        perform ptVaInParentFromSh1 := getTableAddr currentSh1 vaInParent nbL in
        perform isNull := comparePageToNull ptVaInParentFromSh1 in if isNull then ret false else
        perform idxVaInParent := getIndexOfAddr vaInParent levelMin in
        (**  mark page as not derived *)
        perform null := getVaddrDefault in
         (**  Set the page as not present for the child *)
        perform nullAddr := getPageDefault in
        writePhyEntry ptvaChildFromPD idxvaChild nullAddr false false false false false ;; 
        writeVirtual ptVaChildFromSh2 idxvaChild null ;; 
        writeVirEntry ptVaInParentFromSh1 idxVaInParent null ;;
        ret  true (*vaInParent*)
      
    else ret false.


(** ** The deletePartition PIP service *)
(** The [deletePartition] function removes a child partition and puts all its used
       pages back in parent (the current partition) 

    [descChild] The partition descriptor of the child

  *)
Definition deletePartition (descChild : vaddr) :=
  (**  Get the current partition  *)
  perform currentPart := getCurPartition in
  (** Get the number of levels *)
  perform nbL :=  getNbLevel in
  (** check whether pd is a pd or not *)
  perform check := checkChild currentPart nbL descChild in
  if(check)
  then
    (**  Get the physical address of the child partition *)
    perform currentPD := getPd currentPart in
    perform ptDescChildFromPD := getTableAddr currentPD descChild nbL in
    perform isNull := comparePageToNull ptDescChildFromPD in if isNull then ret false else
    perform idxDescChild := getIndexOfAddr descChild levelMin in
    perform phyDescChild := readPhyEntry ptDescChildFromPD idxDescChild in 

    (**  Get the physical address of the second shadow page of the child *)
    perform phyChildSh2 := getSndShadow phyDescChild in

    (**  Get the list of virtual addresses of mapped pages *)
    perform nullAddrV := getVaddrDefault in

    (**  Set mapped pages as underived *)
    perform currentSh1 := getFstShadow currentPart in
    perform maxindex := getMaxIndex in
    perform mappedVAddrList := unmapChildPages currentSh1 phyChildSh2 in

    (**  Get the configuration pages list of the child  *)
    perform phyConfigPagesListChild := getConfigTablesLinkedList phyDescChild in
    perform vaConfigPagesListChild := getConfigTablesLinkedListVaddr phyDescChild in
    perform zero := getIdx0 in
    perform indexone := idxSuccM zero in
    perform indextwo := idxSuccM indexone in
    perform currentPD := getPd currentPart in

    (**  Set indirection pages as accessible and underived *)
    perform configPagesList := putIndirectionsBack phyConfigPagesListChild indextwo mappedVAddrList currentPD  currentSh1 nbL vaConfigPagesListChild in

    (**  unmark child partition  *)
    perform ptDescChildFromCurrentSh1 := getTableAddr currentSh1 descChild nbL in
    perform isNull := comparePageToNull ptDescChildFromCurrentSh1 in if isNull then ret false else
    writePDflag ptDescChildFromCurrentSh1 idxDescChild false ;;

    (**  Set accesible and underived: the virtual addresses used as descChild , pdChild, phySh1Child, phySh2Child, phyConfigPagesList *)
    perform zero := getIdx0 in
    putShadowsBack phyDescChild zero currentPD  currentSh1 nbL configPagesList  ;;

    (**  Add PD to the list of indirection tables *)
    (*storeVirtual pdChild zero configPagesList ;;
      ret configPagesList *)
    ret true
  else ret false.

(** ** The collect PIP service 

    This service removes the empty configuration tables which are not 
    required anymore and gives it back to the parent  *)

(** - The [collectRec] is the recursive function of [collect]

       <<timeout>> fixes how many times the function should be called 
                  before the program terminates

      <<phyPDChild>> the physical address of the child page directory

      <<phySh1Child>> the physical address of the child first shadow
                    
      <<phySh2Child>> the physical address of the child second shadow
                    

      <<phyConfigPagesList>> the physical address of the child configuration tables
                             list 

      <<vaToCollect>> the virtual address to collect associated configuration tables

      <<currentLevel>> a level number of the MMU

 *)
Fixpoint collectRec timeout (phyPDChild : page) (phySh1Child : page) (phySh2Child : page)
  (phyConfigPagesList : page) (vaToCollect : vaddr)  (currentLevel : level) (lst : vaddr) :=
  match timeout with
  | 0 => ret false (* getDefaultVAddr*)
  | S timeout1 =>

    perform isFstLevel := levelEqM currentLevel levelMin in 
    if isFstLevel then ret true else
    perform ptVaToCollectFromPDChild := getTableAddr phyPDChild vaToCollect currentLevel in (** Get indirection table address, last nbL *)

    perform isNull := comparePageToNull ptVaToCollectFromPDChild in if isNull then ret false else
    perform maxindex := getMaxIndex  in (** Get table size *)
    perform ept := checkEmptyTable ptVaToCollectFromPDChild maxindex currentLevel in (** Is page table empty ? *)
    if(ept)
    then
      (** Yep : collect this ! *)
      perform zero := getIdx0 in
      perform fstindex := idxSuccM zero in
      perform twoI := idxSuccM fstindex in
      perform ptVaToCollectFromSh1Child := getTableAddr phySh1Child vaToCollect currentLevel in  (** Get shadow 1 table *)
      perform isNull := comparePageToNull ptVaToCollectFromSh1Child in if isNull then ret false else
      perform ptVaToCollectFromSh2Child := getTableAddr phySh2Child vaToCollect currentLevel in (** Get shadow 2 table *)
      perform isNull := comparePageToNull ptVaToCollectFromSh2Child in if isNull then ret false else
      (** Parse the shadow 3 and Get virtual addresses *)
      perform vaPtVaToCollectFromPDChild := parseConfigPagesList phyConfigPagesList twoI ptVaToCollectFromPDChild in
      perform vaPtVaToCollectFromSh1Child := parseConfigPagesList phyConfigPagesList twoI ptVaToCollectFromSh1Child in
      perform vaPtVaToCollectFromSh2Child := parseConfigPagesList phyConfigPagesList twoI ptVaToCollectFromSh2Child in
      (** Now unmap this page table, get nbL - 1 *)
      perform levelPred := levelPredM currentLevel in
      perform nextIndFromPDChild := getTableAddr phyPDChild vaToCollect levelPred in (** Get parent table *)
      perform isNull := comparePageToNull nextIndFromPDChild in if isNull then ret false else
      perform nextIndFromSh1Child := getTableAddr phySh1Child vaToCollect levelPred in (** shadow 1 parent *)
      perform isNull := comparePageToNull nextIndFromSh1Child in if isNull then ret false else
      perform nextIndFromSh2Child := getTableAddr phySh2Child vaToCollect levelPred in (** shadow 2 parent *)
      perform isNull := comparePageToNull nextIndFromSh2Child in if isNull then ret false else
      perform idxCurrentLevel :=  getIndexOfAddr vaToCollect currentLevel in (** Get address index in parent table *)
      perform nullAddr :=  getPageDefault (** null address *) in
      (** Clear table entries *)
      writePhyEntry nextIndFromPDChild idxCurrentLevel nullAddr false false false false false ;; 
      writePhyEntry nextIndFromSh1Child idxCurrentLevel nullAddr false false false false false ;; 
      writePhyEntry nextIndFromSh2Child idxCurrentLevel nullAddr false false false false false ;; 

      (** Update page properties *)
      (** We should have the VAddr in our parent context : for table, shadow 1 and shadow 2,
        find entry and update properties *)
      perform currentPart := getCurPartition in
      perform currentPD :=  getPd currentPart  in
      (** Get virtual addresses indexes in last indirection table *)
      perform nbIdx :=  getNbLevel in
      perform vaPtVaToCollectFromPDChildIndex := getIndexOfAddr vaPtVaToCollectFromPDChild levelMin in
      perform vaPtVaToCollectFromSh1ChildIndex := getIndexOfAddr vaPtVaToCollectFromSh1Child levelMin in
      perform vaPtVaToCollectFromSh2ChildIndex := getIndexOfAddr vaPtVaToCollectFromSh2Child levelMin in

      (** Get page table and shadow tables *)
      perform parentPT := getTableAddr currentPD vaPtVaToCollectFromPDChild nbIdx in
      perform isNull := comparePageToNull parentPT in if isNull then ret false else
      perform parentSh1 := getTableAddr currentPD vaPtVaToCollectFromSh1Child nbIdx in
      perform isNull := comparePageToNull parentSh1 in if isNull then ret false else
      perform parentSh2 := getTableAddr currentPD vaPtVaToCollectFromSh2Child nbIdx in
      perform isNull := comparePageToNull parentSh2 in if isNull then ret false else

      (** Update properties now : user uccess *)
      writeAccessible parentPT vaPtVaToCollectFromPDChildIndex true ;;
      writeAccessibleRec vaPtVaToCollectFromPDChild currentPart true;;
      writeAccessible parentSh1 vaPtVaToCollectFromSh1ChildIndex true ;;
      writeAccessibleRec vaPtVaToCollectFromSh1Child currentPart true;;
      writeAccessible parentSh2 vaPtVaToCollectFromSh2ChildIndex true ;;
      writeAccessibleRec vaPtVaToCollectFromSh2Child currentPart true;;
      (** Get the first shadow of the current partition *)
      perform currentShadow1 := getFstShadow currentPart in
      (** Get page table and shadow tables *)
      perform pdChildFromSh1Parent := getTableAddr currentShadow1 vaPtVaToCollectFromPDChild nbIdx in
      perform isNull := comparePageToNull pdChildFromSh1Parent in if isNull then ret false else
      perform sh1ChildFromSh1Parent := getTableAddr currentShadow1 vaPtVaToCollectFromSh1Child nbIdx in
      perform isNull := comparePageToNull sh1ChildFromSh1Parent in if isNull then ret false else
      perform sh2ChildFromSh1Parent := getTableAddr currentShadow1 vaPtVaToCollectFromSh2Child nbIdx in
      perform isNull := comparePageToNull sh2ChildFromSh1Parent in if isNull then ret false else
      perform nullVA :=  getVaddrDefault in
      (** Update properties now : derivation *)
      writeVirEntry pdChildFromSh1Parent vaPtVaToCollectFromPDChildIndex nullVA ;;
      writeVirEntry sh1ChildFromSh1Parent vaPtVaToCollectFromSh1ChildIndex nullVA ;;
      writeVirEntry sh2ChildFromSh1Parent vaPtVaToCollectFromSh2ChildIndex nullVA ;;

      (** Link returning pages *)
      (*perform zero := getIdx0 in
        perform nullAddrV :=  getDefaultVAddr in
        storeVirtual vaPtVaToCollectFromPDChild zero vaPtVaToCollectFromSh1Child ;;
        storeVirtual vaPtVaToCollectFromSh1Child zero vaPtVaToCollectFromSh2Child ;;
        storeVirtual vaPtVaToCollectFromSh2Child zero lst ;;*)
      (** Recursive call on parent table *)
      collectRec timeout1 phyPDChild phySh1Child phySh2Child phyConfigPagesList 
      vaToCollect levelPred vaPtVaToCollectFromPDChild
    else  (** firstVAd := linkList lst false *)(*  ret false *) ret true
  end.

(** - The [collectAux] function fixes the timout value of  [collectRec] *)
Definition collectAux (phyPDChild : page) (phySh1Child : page) (phySh2Child : page)
  (phyConfigPagesList : page) (vaToCollect : vaddr)  (currentLevel : level) (lst : vaddr):=
  collectRec N phyPDChild phySh1Child phySh2Child phyConfigPagesList vaToCollect currentLevel lst.

(** - The [collect] function fixes the [collectAux] required parameters values

    [descChild]   The virtual address of partition descriptor of the child

    [vaToCollect] The virtual address to collect (remove only empty configuration 
                  tables that correspond to this virtual address) 
 *)
Definition collect (descChild : vaddr) (vaToCollect : vaddr) :=
  perform iskernel := checkKernelMap vaToCollect in
  if negb iskernel
  then  
    (**  Get the current partition  *)
    perform currentPart := getCurPartition in
    (** Get the phyPDChild of the current partition *)
    perform currentPD := getPd currentPart in
    (** Get the MMU levels number *)
    perform nbL :=  getNbLevel in
    (** Check if the given virtual address corresponds to a partition descriptor 
     of a child partition *)
    perform check := checkChild currentPart nbL descChild in
    if(check)
    then
      (** Get the physical address of the child partition descriptor *) 
      perform ptDescChildFromPD := getTableAddr currentPD descChild nbL in
      perform isNull := comparePageToNull ptDescChildFromPD in if isNull then ret false else
      perform idxDescChild := getIndexOfAddr descChild levelMin in
      perform phyDescChild := readPhyEntry ptDescChildFromPD idxDescChild in
      (** Get the page directory of the child *)
      perform phyPDChild := getPd phyDescChild in
      (** Get the first shadow of the child *)
      perform phySh1Child := getFstShadow phyDescChild in
      (** Get the second shadow of the child *)
      perform phySh2Child := getSndShadow phyDescChild in
      (** Get the config tables list shadow of the child *)
      perform phyConfigPagesList  := getConfigTablesLinkedList phyDescChild in
      perform defAddr := getVaddrDefault in
      (** Call collectAux with required parameters *)
      collectAux phyPDChild phySh1Child phySh2Child phyConfigPagesList vaToCollect nbL defAddr
    else ret false
  else ret false.

Definition switchContextCont (targetPartDesc : page)
                             (targetPageDir  : page)
                             (flagsOnYield   : interruptMask)
                             (targetContext  : contextAddr)
                             : LLI yield_checks :=

  setInterruptMask flagsOnYield ;;
  updateMMURoot targetPageDir ;;
  updateCurPartition targetPartDesc ;;
  perform flagsOnWake := getInterruptMaskFromCtx targetContext in
  setInterruptMask flagsOnWake ;;
  (* allow root partition to prevent Pip from enforcing interrupts *)
  perform rootPartition := getPageRootPartition in
  perform targetIsRoot := pageEqM rootPartition targetPartDesc in
  perform targetReqNoInterrupt := noInterruptRequest flagsOnWake in
  (
  if (targetIsRoot && targetReqNoInterrupt)
  then
    loadContext targetContext false
  else
    loadContext targetContext true
  ) ;;
  (* Actually never reached *)
  ret SUCCESS.

Definition saveSourceContextCont (targetPartDesc           : page)
                                 (targetPageDir            : page)
                                 (sourcePageDir            : page)
                                 (sourceContextSaveVAddr   : vaddr)
                                 (nbL                      : level)
                                 (flagsOnYield             : interruptMask)
                                 (flagsOnWake              : interruptMask)
                                 (sourceInterruptedContext : contextAddr)
                                 (targetContext            : contextAddr)
                                     : LLI yield_checks :=
  (* check contextSaveAddr validity *)
  perform sourceCtxLastMMUPage := getTableAddr sourcePageDir sourceContextSaveVAddr nbL in
  perform sourceCtxLastMMUPageIsNull := comparePageToNull sourceCtxLastMMUPage in
  if sourceCtxLastMMUPageIsNull then
    ret FAIL_CALLER_CONTEXT_SAVE
  else

  perform idxSourceCtxInLastMMUPage := getIndexOfAddr sourceContextSaveVAddr levelMin in
  perform sourceCtxPageIsPresent := readPresent sourceCtxLastMMUPage idxSourceCtxInLastMMUPage in
  if negb sourceCtxPageIsPresent then
    ret FAIL_CALLER_CONTEXT_SAVE
  else

  perform sourceCtxPageIsAccessible := readAccessible sourceCtxLastMMUPage idxSourceCtxInLastMMUPage in
  if negb sourceCtxPageIsAccessible then
    ret FAIL_CALLER_CONTEXT_SAVE
  else
  (*--------------------------*)

  (* get end ctx address *)
  perform sourceContextEndSaveVAddr := getNthVAddrFrom sourceContextSaveVAddr contextSizeMinusOne in
  perform endAddrOverflow := firstVAddrGreaterThanSecond sourceContextSaveVAddr sourceContextEndSaveVAddr in
  if endAddrOverflow then
    ret FAIL_CALLER_CONTEXT_SAVE
  else
  (*--------------------------*)

  (* check context save address *)
  perform sourceCtxEndLastMMUPage := getTableAddr sourcePageDir sourceContextEndSaveVAddr nbL in
  perform sourceCtxEndLastMMUPageisNull := comparePageToNull sourceCtxEndLastMMUPage in
  if sourceCtxEndLastMMUPageisNull then
    ret FAIL_CALLER_CONTEXT_SAVE
  else

  perform idxSourceCtxEndInLastMMUPage := getIndexOfAddr sourceContextEndSaveVAddr levelMin in
  perform sourceCtxEndPageIsPresent := readPresent sourceCtxEndLastMMUPage idxSourceCtxEndInLastMMUPage in
  if negb sourceCtxEndPageIsPresent then
    ret FAIL_CALLER_CONTEXT_SAVE
  else

  perform sourceCtxEndPageIsAccessible := readAccessible sourceCtxEndLastMMUPage idxSourceCtxEndInLastMMUPage in
  if negb sourceCtxEndPageIsAccessible then
    ret FAIL_CALLER_CONTEXT_SAVE
  else

  writeContext sourceInterruptedContext sourceContextSaveVAddr flagsOnWake ;;
  switchContextCont targetPartDesc targetPageDir flagsOnYield targetContext.

Definition getTargetContextCont (targetPartDesc : page)
				                        (targetPageDir  : page)
				                        (targetVidt     : page)
				                        (sourcePageDir  : page)
                                (sourceContextSaveVaddr : vaddr)
				                        (targetInterrupt : index)
				                        (nbL : level)
				                        (flagsOnYield   : interruptMask)
				                        (flagsOnWake    : interruptMask)
				                        (sourceInterruptedContext : contextAddr)
                                : LLI yield_checks :=
  (* retrieving the callee's handler context *)
  perform targetContextVAddr := readVirtualUser targetVidt targetInterrupt in
  perform targetContextLastMMUPage := getTableAddr targetPageDir targetContextVAddr nbL in
  perform targetContextLastMMUPageisNull := comparePageToNull targetContextLastMMUPage in
  if targetContextLastMMUPageisNull then
    ret FAIL_UNAVAILABLE_TARGET_CTX
  else

  perform idxTargetContextPageInLastMMUPage := getIndexOfAddr targetContextVAddr levelMin in

  perform targetContextPageIsPresent := readPresent targetContextLastMMUPage idxTargetContextPageInLastMMUPage in
  if negb targetContextPageIsPresent then
    ret FAIL_UNAVAILABLE_TARGET_CTX
  else
  perform targetContextPageIsAccessible := readAccessible targetContextLastMMUPage idxTargetContextPageInLastMMUPage in
  if negb targetContextPageIsAccessible then
    ret FAIL_UNAVAILABLE_TARGET_CTX
  else

  (* get ctx end addr *)
  perform targetContextEndVAddr := getNthVAddrFrom targetContextVAddr contextSizeMinusOne in
  perform targetContextEndVAddrOverflow := firstVAddrGreaterThanSecond targetContextVAddr targetContextEndVAddr in
  if targetContextEndVAddrOverflow then
    ret FAIL_UNAVAILABLE_TARGET_CTX
  else

  (* check context end save address *)
  perform targetContextEndLastMMUPage := getTableAddr targetPageDir targetContextEndVAddr nbL in
  perform targetContextEndLastMMUPageisNull := comparePageToNull targetContextEndLastMMUPage in
  if targetContextEndLastMMUPageisNull then
    ret FAIL_UNAVAILABLE_TARGET_CTX
  else

  perform idxTargetContextEndPageInLastMMUPage := getIndexOfAddr targetContextEndVAddr levelMin in
  perform targetContextEndPageIsPresent := readPresent targetContextEndLastMMUPage idxTargetContextEndPageInLastMMUPage in
  if negb targetContextEndPageIsPresent then
    ret FAIL_UNAVAILABLE_TARGET_CTX
  else

  perform targetContextEndPageIsAccessible := readAccessible targetContextEndLastMMUPage idxTargetContextEndPageInLastMMUPage in
  if negb targetContextEndPageIsAccessible then
    ret FAIL_UNAVAILABLE_TARGET_CTX
  else

  perform targetContext := vaddrToContextAddr targetContextVAddr in

  perform sourceContextSaveVaddrIsNull := compareVAddrToNull sourceContextSaveVaddr in
  if (sourceContextSaveVaddrIsNull)
  then
    switchContextCont targetPartDesc
                      targetPageDir
                      flagsOnYield
                      targetContext
  else
    saveSourceContextCont targetPartDesc
                          targetPageDir
                          sourcePageDir
                          sourceContextSaveVaddr
                          nbL
                          flagsOnYield
                          flagsOnWake
                          sourceInterruptedContext
                          targetContext.

Definition getTargetVidtCont (targetPartDesc : page)
				                     (sourcePageDir : page)
				                     (vidtVAddr : vaddr)
				                     (sourceContextSaveVAddr : vaddr)
				                     (targetInterrupt : index)
				                     (nbL : level)
				                     (idxVidtInLastMMUPage : index)
				                     (flagsOnYield : interruptMask)
				                     (flagsOnWake : interruptMask)
				                     (sourceInterruptedContext : contextAddr)
                             : LLI yield_checks :=
  (* check if callee vidt is available *)
  perform targetPageDir := getPd targetPartDesc in

  perform targetVidtLastMMUPage := getTableAddr targetPageDir vidtVAddr nbL in
  perform targetVidtLastMMUPageisNull := comparePageToNull targetVidtLastMMUPage in
  if targetVidtLastMMUPageisNull then
    ret FAIL_UNAVAILABLE_TARGET_VIDT
  else

  perform targetVidtIsPresent := readPresent targetVidtLastMMUPage idxVidtInLastMMUPage in
  if negb targetVidtIsPresent then
    ret FAIL_UNAVAILABLE_TARGET_VIDT
  else

  perform targetVidtIsAccessible := readAccessible targetVidtLastMMUPage idxVidtInLastMMUPage in
  if negb targetVidtIsAccessible then
    ret FAIL_UNAVAILABLE_TARGET_VIDT
  else

  perform targetVidt := readPhyEntry targetVidtLastMMUPage idxVidtInLastMMUPage in
  getTargetContextCont targetPartDesc
				               targetPageDir
				               targetVidt
				               sourcePageDir
                       sourceContextSaveVAddr
				               targetInterrupt
				               nbL
				               flagsOnYield
				               flagsOnWake
				               sourceInterruptedContext.

Definition getSourceVidtCont (targetPartDesc : page)
				                     (sourcePageDir  : page)
				                     (targetInterrupt : index)
				                     (sourceContextSaveIndex : index)
				                     (nbL                    : level)
				                     (flagsOnYield : interruptMask)
				                     (flagsOnWake  : interruptMask)
				                     (sourceInterruptedContext : contextAddr)
                             : LLI yield_checks :=
  perform vidtVAddr := getVaddrVIDT in
  perform idxVidtInLastMMUPage := getIndexOfAddr vidtVAddr levelMin in

  (* retrieve caller vidt *)
  perform sourceVidtLastMMUPage := getTableAddr sourcePageDir vidtVAddr nbL in
  perform sourceVidtLastMMUPageisNull := comparePageToNull sourceVidtLastMMUPage in
  if sourceVidtLastMMUPageisNull then
    ret FAIL_UNAVAILABLE_CALLER_VIDT
  else

  perform sourceVidtIsPresent := readPresent sourceVidtLastMMUPage idxVidtInLastMMUPage in
  if negb sourceVidtIsPresent then
    ret FAIL_UNAVAILABLE_CALLER_VIDT
  else

  perform sourceVidtIsAccessible := readAccessible sourceVidtLastMMUPage idxVidtInLastMMUPage in
  if negb sourceVidtIsAccessible then
    ret FAIL_UNAVAILABLE_CALLER_VIDT
  else

  perform sourceVidt := readPhyEntry sourceVidtLastMMUPage idxVidtInLastMMUPage in

  (* save caller context if needed *)
  perform sourceContextSaveVAddr := readVirtualUser sourceVidt sourceContextSaveIndex in
  getTargetVidtCont targetPartDesc
				            sourcePageDir
				            vidtVAddr
				            sourceContextSaveVAddr
				            targetInterrupt
				            nbL
				            idxVidtInLastMMUPage
				            flagsOnYield
				            flagsOnWake
				            sourceInterruptedContext.

(* 

Definition checkIntMaskCont(calleePartDesc : page)
                           (calleePageDir  : page)
                           (calleeVidt     : page)
                           (callerPageDir  : page)
                           (vidtVaddr              : vaddr)
                           (targetInterrupt        : index)
                           (callerContextSaveIndex : index)
                           (nbL                    : level)
                           (idxVidtInLastMMUPage   : index)
                           (flagsOnYield : interruptMask)
                           (flagsOnWake  : interruptMask)
                           (callerInterruptedContext : contextAddr)
                           : LLI yield_checks :=


  (* checking if interruption is not masked *)
  perform calleeInterruptMask := readInterruptMask calleeVidt in
  perform calleeMaskedInterrupt := isInterruptMasked calleeInterruptMask targetInterrupt in
  if calleeMaskedInterrupt then
    ret FAIL_MASKED_INTERRUPT
  else

  getCalleeContextCont calleePartDesc
				               calleePageDir
				               calleeVidt
				               callerPageDir
				               vidtVaddr
				               callerContextSaveIndex
				               targetInterrupt
				               nbL
				               idxVidtInLastMMUPage
				               flagsOnYield
				               flagsOnWake
				               callerInterruptedContext.
 *)



Definition getParentPartDescCont (sourcePartDesc : page)
				                         (sourcePageDir : page)
				                         (targetInterrupt : index)
				                         (sourceContextSaveIndex : index)
				                         (nbL : level)
				                         (flagsOnYield : interruptMask)
				                         (flagsOnWake : interruptMask)
				                         (sourceInterruptedContext : contextAddr)
                                 : LLI yield_checks :=

  (* check if partition is root *)
  perform rootPartition := getPageRootPartition in
  perform sourcePartitionIsRoot := pageEqM rootPartition sourcePartDesc in
  if sourcePartitionIsRoot then
    ret FAIL_ROOT_CALLER
  else

  (*############################*)

  (* check if target vidt is available *)
  perform targetPartDesc := getParent sourcePartDesc in
  getSourceVidtCont targetPartDesc
				            sourcePageDir
				            targetInterrupt
				            sourceContextSaveIndex
				            nbL
				            flagsOnYield
				            flagsOnWake
				            sourceInterruptedContext.

Definition getChildPartDescCont (sourcePartDesc : page)
				                        (sourcePageDir : page)
				                        (targetPartDescVAddr : vaddr)
				                        (targetInterrupt : index)
				                        (sourceContextSaveIndex : index)
				                        (nbL : level)
				                        (flagsOnYield : interruptMask)
				                        (flagsOnWake : interruptMask)
				                        (sourceInterruptedContext : contextAddr)
                                : LLI yield_checks :=
  (* checking child validity *)
  perform childLastMMUTable := getTableAddr sourcePageDir targetPartDescVAddr nbL in
  perform childLastMMUTableIsNull := comparePageToNull childLastMMUTable in
  if childLastMMUTableIsNull then
    ret FAIL_INVALID_CHILD
  else
  perform idxChildPartDesc := getIndexOfAddr targetPartDescVAddr levelMin in
  perform childPartDescIsPresent := readPresent childLastMMUTable idxChildPartDesc in
  if negb childPartDescIsPresent then
    ret FAIL_INVALID_CHILD
  else

  perform validChild := checkChild sourcePartDesc nbL targetPartDescVAddr in
  if negb validChild then
    ret FAIL_INVALID_CHILD
  else

  (* retrieving child page directory *)
  perform targetPartDesc := readPhyEntry childLastMMUTable idxChildPartDesc in
  getSourceVidtCont targetPartDesc
				            sourcePageDir
				            targetInterrupt
				            sourceContextSaveIndex
				            nbL
				            flagsOnYield
				            flagsOnWake
				            sourceInterruptedContext.

Definition checkCtxSaveIdxCont (targetPartDescVAddr : vaddr)
				                       (targetInterrupt : index)
				                       (userSourceContextSaveIndex : userValue)
				                       (flagsOnYield : interruptMask)
				                       (flagsOnWake : interruptMask)
				                       (sourceInterruptedContext : contextAddr)
                               : LLI yield_checks :=

  (* check context save index *)
  perform sourceContextSaveIndexIsValid := checkIndexPropertyLTB userSourceContextSaveIndex in
  if negb sourceContextSaveIndexIsValid then
    ret FAIL_INVALID_CTX_SAVE_INDEX
  else

  perform sourceContextSaveIndex := userValueToIndex userSourceContextSaveIndex in

  perform sourcePartDesc := getCurPartition in
  perform sourcePageDir := getPd sourcePartDesc in
  perform nbL := getNbLevel in


  perform targetPartDescVAddrIsDefault := compareVAddrToNull targetPartDescVAddr in
  if targetPartDescVAddrIsDefault then
    getParentPartDescCont sourcePartDesc
				                  sourcePageDir
				                  targetInterrupt
				                  sourceContextSaveIndex
				                  nbL
				                  flagsOnYield
				                  flagsOnWake
				                  sourceInterruptedContext
  else
    getChildPartDescCont sourcePartDesc
				                 sourcePageDir
				                 targetPartDescVAddr
				                 targetInterrupt
				                 sourceContextSaveIndex
				                 nbL
				                 flagsOnYield
				                 flagsOnWake
				                 sourceInterruptedContext.


Definition checkIntLevelCont (targetPartDescVAddr : vaddr)
				                     (userTargetInterrupt : userValue)
				                     (userSourceContextSaveIndex : userValue)
				                     (flagsOnYield : interruptMask)
				                     (flagsOnWake : interruptMask)
				                     (sourceInterruptedContext : contextAddr)
                 : LLI yield_checks :=

  (* checkIndexPropertyLTB *)
  perform userTargetInterruptIsValidIndex := checkIndexPropertyLTB userTargetInterrupt in
  if negb userTargetInterruptIsValidIndex then
    ret FAIL_INVALID_INT_LEVEL
  else

  perform targetInterrupt := userValueToIndex userTargetInterrupt in

  checkCtxSaveIdxCont targetPartDescVAddr
				              targetInterrupt
				              userSourceContextSaveIndex
				              flagsOnYield
				              flagsOnWake
				              sourceInterruptedContext.
