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
    This file contains some internal functions used by services *)
Require Import Model.Hardware Model.ADT Model.MAL Model.MALInternal Model.IAL Bool Arith List Coq.Init.Peano.
Definition N := 100.

(** The [getPd] function returns the page directory of a given partition *)
Definition getPd partition :=
  perform idxPD := getPDidx in
  perform idx := MALInternal.Index.succ idxPD in
  readPhysical partition idx.

(** The [getFstShadow] returns the first shadow page of a given partition *)
Definition getFstShadow (partition : page):=
  perform idx11 := getSh1idx in
  perform idx := MALInternal.Index.succ idx11 in
  readPhysical partition idx.

(** The [getSndShadow] returns the second shadow page of a given partition *)
Definition getSndShadow partition :=
  perform idxSh2 := getSh2idx in
  perform idx := MALInternal.Index.succ idxSh2 in
  readPhysical partition idx.

(** The [getConfigTablesLinkedList] returns the first physical page of the configuration 
    tables linked list of a given partition *)
Definition getConfigTablesLinkedList partition :=
  perform idxSh3 := getSh3idx in
  perform idx := MALInternal.Index.succ idxSh3 in
  readPhysical partition idx.

(** The [getConfigTablesLinkedList] returns the virtual address of the first physical page of the configuration 
    tables linked list of a given partition *)
Definition getConfigTablesLinkedListVaddr partition :=
  perform idxSh3 := getSh3idx in
  readVirtual partition idxSh3.

(** The [getParent] function returns the parent of a given partition *)
Definition getParent partition :=
  perform idxPPR := getPPRidx in
  perform idx := MALInternal.Index.succ idxPPR in
  readPhysical partition idx.

(** The [updatePartitionDescriptor] function update an entry into a given partition 
    descriptor table *)
Definition updatePartitionDescriptor partition idxV phypd virtpd :=
  writeVirtual partition idxV virtpd ;;
  perform idxP := MALInternal.Index.succ idxV in
  writePhysical partition idxP phypd .

(** The [comparePageToNull] returns true if the given page is equal to the fixed
    default page (null) *) 
Definition comparePageToNull (p :page) : LLI bool :=
  perform nullPaddr := getDefaultPage in
  MALInternal.Page.eqb nullPaddr p.

(** The [compareVAddrToNull] returns true if the given virtual address is equal 
    to the fixed default virtual address (null) *) 
Definition compareVAddrToNull va :=
  perform defaultVAddr := getDefaultVAddr in
  perform res := MALInternal.VAddr.eqbList defaultVAddr va in
  ret res.

(** The [getTableAddrAux] returns the reference to the last page table  *)
Fixpoint getTableAddrAux timeout (pd : page) (va : vaddr) (l : level) :=
  match timeout with
  | 0 => getDefaultPage
  |S timeout1 =>
  perform isFstLevel := MALInternal.Level.eqb l fstLevel in 
    if isFstLevel 
    then  ret pd
    else
      perform idx :=  getIndexOfAddr va l in
      perform addr :=  readPhyEntry pd idx in 
      perform isNull := comparePageToNull addr in
      if isNull then getDefaultPage else
      perform p := MALInternal.Level.pred l in
      getTableAddrAux timeout1 addr va p
  end .

(** [getTableAddr] fixes the value of [getTableAddrAux] timeout *)
Definition  getTableAddr (pd : page) (va : vaddr) (l : level)  :=
  getTableAddrAux nbLevel pd va l.

(** The [setUnderived] function marks the given virtual addresse as underived 
    into the given partition  *)
Definition setUnderived va currentShadow1 l1 :=
  perform nullAddrV :=  getDefaultVAddr in
  perform res := MALInternal.VAddr.eqbList nullAddrV va in
  if negb (res)
  then
    perform pt := getTableAddr currentShadow1 va l1 in
    perform isNull := comparePageToNull pt in
    if isNull then ret tt else
    perform idx :=  getIndexOfAddr va fstLevel in
    perform null :=  getDefaultVAddr in
    writeVirEntry pt idx null
  else ret tt.

(** The [setDerived] function marks the given virtual addresse as derived into 
    the given partition  *)
Definition setDerived va currentShadow1 descChild l1 :=
  perform nullAddrV :=  getDefaultVAddr in
  perform res := MALInternal.VAddr.eqbList nullAddrV va in
  if negb (res)
  then
    perform pt := getTableAddr currentShadow1 va l1 in
    perform isNull := comparePageToNull pt in
    if isNull then ret tt else
    perform idx :=  getIndexOfAddr va fstLevel in
    writeVirEntry pt idx descChild
  else ret tt.

(** The [setAccessible] function marks the given virtual addresse as Accessible 
    into the given partition  *)
Definition setAccessible va currentPD L u :=
  perform nullAddrV :=  getDefaultVAddr in
  perform res := MALInternal.VAddr.eqbList nullAddrV va in
  if negb (res )
  then
    perform pt := getTableAddr currentPD va L in
    perform isNull := comparePageToNull pt in
    if isNull then ret false else
    perform idx := getIndexOfAddr va fstLevel in
    writeAccessible pt idx u;; ret true
  else ret false.

(** The [writeAccessibleRec] function updates the user access flag of a physical page which 
    corresponds to a given virtual address [va] in all ancestors of a given partition [descParent]. 
*) 
(* Fixpoint writeAccessibleRec timout (va : vaddr) (descParent : page) (flag : bool):=
match timout with 
| 0 => ret false
| S timout1 =>   
perform multiplexer := getMultiplexer in 
perform isMultiplexer := MALInternal.Page.eqb descParent multiplexer in
if isMultiplexer (** stop if parent is the multiplexer *)
then ret true
else 
(** get the snd shadow of the parent to get back the virtual address into the first ancestor *)
perform sh2Parent := getSndShadow descParent in 
perform L:= getNbLevel in
perform idx := getIndexOfAddr va fstLevel in  
perform ptsh2 := getTableAddr sh2Parent va  L in 
perform isNull := comparePageToNull ptsh2 in
if isNull then ret false else
(** read the virtual address into the first ancestor *)
perform vaInAncestor := readVirtual ptsh2 idx in 
(** get the first ancestor partition descriptor *)
perform ancestor := getParent descParent in
(** get the page directory of the ancestor partition descriptor *)
perform pdAncestor := getPd ancestor in 
(** set access rights of the virtual address *)
perform isaccess := setAccessible vaInAncestor pdAncestor L flag in 
if isaccess 
then
(** recursion **)
writeAccessibleRec timout1 vaInAncestor ancestor flag 
else ret false
end. *)

Fixpoint writeAccessibleRecAux timout (va : vaddr) (descParent : page) (flag : bool):=
match timout with 
| 0 => ret false
| S timout1 =>   
perform multiplexer := getMultiplexer in 
perform isMultiplexer := MALInternal.Page.eqb descParent multiplexer in
if isMultiplexer (** stop if parent is the multiplexer *)
then ret true
else 
(** get the snd shadow of the parent to get back the virtual address into the first ancestor *)
perform sh2Parent := getSndShadow descParent in 
perform L:= getNbLevel in
perform idx := getIndexOfAddr va fstLevel in  
perform ptsh2 := getTableAddr sh2Parent va  L in 
perform isNull := comparePageToNull ptsh2 in
if isNull then ret false else
(** read the virtual address into the first ancestor *)
perform vaInAncestor := readVirtual ptsh2 idx in 
(** get the first ancestor partition descriptor *)
perform ancestor := getParent descParent in
(** get the page directory of the ancestor partition descriptor *)
perform pdAncestor := getPd ancestor in 
(** set access rights of the virtual address *)
  perform nullAddrV :=  getDefaultVAddr in
  perform res := MALInternal.VAddr.eqbList nullAddrV vaInAncestor in
  if (res )
  then ret false
  else
    perform pt := getTableAddr pdAncestor vaInAncestor L in
    perform isNull := comparePageToNull pt in
    if isNull then ret false else
    perform idx := getIndexOfAddr vaInAncestor fstLevel in
    writeAccessible pt idx flag ;;
(** recursion **)
writeAccessibleRecAux timout1 vaInAncestor ancestor flag 
end.

Definition writeAccessibleRec (va : vaddr) (descParent : page) (flag : bool):=
writeAccessibleRecAux (nbPage+1) va descParent flag.
(** The [checkDerivation] tests if the given entry (table+idx) contains a 
    derivation *)
Definition checkDerivation table idx : LLI bool :=
  perform va := readVirEntry table idx in
  compareVAddrToNull va .


(** The [verifyProperties] returns true if the given virtual address could be lent to the kernel *)
Definition verifyProperties (ptMMUva ptSh1va: page) (idxva: index): LLI bool:=
perform isNull := comparePageToNull ptMMUva in 
if isNull then ret false 
else
(** True if present *)
perform fstVAisPresent := readPresent ptMMUva idxva in
if negb fstVAisPresent then ret false
else
(** True if accessible *)
perform fstVAisAccessible := readAccessible ptMMUva idxva in
if negb fstVAisAccessible then ret false 
else 
perform isNull := comparePageToNull ptSh1va in 
(* True if no shadow data structure *)
if isNull then ret false 
else 
perform vaSh1 := readVirEntry ptSh1va idxva in
perform isNull := compareVAddrToNull vaSh1 in 
ret isNull.


(** The [getPTPagesAux] marks as underived all virtual address stored into the 
    given table [ptSh2Child] *)
Fixpoint  getPTPagesAux timeout ptSh2Child (maxindex : index) (buf : vaddr) 
                        parentSh1 (l1 : level) :=
  match timeout with
  | 0 => getDefaultVAddr
  | S timeout1 =>
    perform zero := MALInternal.Index.zero in
    perform isEq := MALInternal.Index.eqb maxindex zero in
    if (isEq)
    then perform va := readVirtual ptSh2Child maxindex in (** read the virtual address into the given table at index [maxindex *)
      perform null := getDefaultVAddr in
      perform eq := MALInternal.VAddr.eqbList va null  in  (** compare virtual address to null *)
      if negb eq (** do not add the null address to the list *)
      then
        (** link this, and now forget about buffer, and consider va as our new buffer *)
        perform zero := MALInternal.Index.zero in
       (*  storeVirtual va zero buf ;; *)
        (** set the virtual address underived into the current partition *)
        setUnderived va parentSh1 l1 ;;
        perform maxindexPred := MALInternal.Index.pred maxindex in
        getPTPagesAux timeout1 ptSh2Child maxindexPred va parentSh1 l1(** recursive call on next entry *)

      else ret buf (** return the first entry of our list *)
    else
      perform va :=  readVirtual ptSh2Child maxindex in (** read the virtual address *)
      perform null :=  getDefaultVAddr in
      perform eq :=  MALInternal.VAddr.eqbList va null  in    (** compare virtual address to null *)
      if negb eq (** do not add the null address to the list *)
      then
        (** link this, and now forget about buffer, and consider va as our new buffer *)
        perform zero := MALInternal.Index.zero in
        (* storeVirtual va zero buf ;; *)
        setUnderived va parentSh1 l1 ;;
        perform maxindexPred := MALInternal.Index.pred maxindex in
        getPTPagesAux timeout1 ptSh2Child maxindexPred va parentSh1 l1(** recursive call on next entry *)

      else(** empty page - go to next entry *)
        perform maxindexPred := MALInternal.Index.pred maxindex in
        getPTPagesAux timeout1 ptSh2Child maxindexPred buf parentSh1 l1
  end. 
(** The [getPTPages] fixes the timeout value of [getPTPagesAux] *)
Definition  getPTPages ptSh2Child (maxindex : index) (buf : vaddr) parentSh1 l1:=
  getPTPagesAux N ptSh2Child (maxindex : index) (buf : vaddr) parentSh1 l1.


(**  The [putMappedPagesBackAux] marks all virtual address of the given child as 
     underived (must revise the kernel index) *)
Fixpoint putMappedPagesBackAux timeout currentSh1 ptSh2Child (pos : index) l1 buf:=
  match timeout with
  | 0 => getDefaultVAddr
  | S timeout1 =>
    perform maxLevel := getNbLevel in
    perform nullAddr := getDefaultPage in
    perform maxindex := getMaxIndex in
    perform islevel := MALInternal.Level.eqb l1 maxLevel in
    perform isfstlevel := MALInternal.Level.eqb l1 fstLevel in
    if (islevel)  (* Page Directory *)
    then
      perform zero := MALInternal.Index.zero in
      perform one := MALInternal.Index.succ zero in
      perform indextwo := MALInternal.Index.succ one in
      perform res := MALInternal.Index.geb pos indextwo in
      if res  (** 0 for shadow 1 , 1 for kernel pages , 2 is the first used entry *)
      then    (** We can parse this *)
        perform pt :=   readPhyEntry ptSh2Child pos in 
        perform cmp :=   MALInternal.Page.eqb nullAddr pt in
        if negb cmp
        then    (** get only the sub-pages, ignoring the current ones, and store them in linked list lst *)
          perform maxindexPred := MALInternal.Index.pred maxindex in
          perform levelPred := MALInternal.Level.pred l1 in
          perform lst :=  putMappedPagesBackAux timeout1 currentSh1  pt maxindexPred levelPred buf  in
          perform pospred := MALInternal.Index.pred pos in
          putMappedPagesBackAux timeout1 currentSh1 ptSh2Child pospred l1 lst (** lst is the new buffer *)
        else
          perform pospred := MALInternal.Index.pred pos in
          putMappedPagesBackAux timeout1 currentSh1 ptSh2Child pospred l1 buf  (** else go on *)
      else   (** We dont parse entry 1 and 2. We're done here *)
        ret buf  (** First entries of page directory : return buffer, we're done ! *)
    else if isfstlevel  (** Last indirection : get tables *)
      then
        getPTPages ptSh2Child maxindex  buf currentSh1  maxLevel
        (** get table entries - buf is the new endpoint *)

      else   (** Intermediate table : parse all entries, getting a list for each *)
        perform zero := MALInternal.Index.zero in
        perform un := MALInternal.Index.succ zero in
        perform res := MALInternal.Index.gtb pos un in
        if (res)  (** more elements to check ? *)
        then
          perform pt :=   readPhyEntry ptSh2Child pos in
          perform cmp :=   MALInternal.Page.eqb pt nullAddr in
          if negb cmp
          then
            perform levelPred := MALInternal.Level.pred l1 in
            perform lst :=  putMappedPagesBackAux timeout1  currentSh1 pt maxindex levelPred buf  in(** Get pages for sub-entry, emptying buffer *)
            perform posPred := MALInternal.Index.pred pos in
            putMappedPagesBackAux timeout1 currentSh1 ptSh2Child posPred l1 lst
            (** Continue parsing this page, filling the buffer with the
              newly-got elements *)
          else perform pospred := MALInternal.Index.pred pos in
            putMappedPagesBackAux timeout1  currentSh1  ptSh2Child pospred l1 buf
        else   (** last entry : just parse it on the next level *)
          perform pt := readPhyEntry ptSh2Child pos in 
          perform cmp := MALInternal.Page.eqb pt nullAddr in
          if negb cmp
          then
            perform levelPred := MALInternal.Level.pred l1 in
            putMappedPagesBackAux timeout1 currentSh1  pt maxindex levelPred buf  (** Continue linking *)
          else ret buf
  end.  (** nothing to do, just return our buffer *)

(** The [putMappedPagesBack] fixes the timeout value of [putMappedPagesBackAux] *)
Definition putMappedPagesBack ( currentSh1 ptSh2Child : page) (pos : index)  (l1 : level) (buf : vaddr) : LLI vaddr:=
  putMappedPagesBackAux N  currentSh1 ptSh2Child pos l1 buf.

(** The [insertEntryIntoConfigPagesListAux] function inserts an entry into the 
    list of partition configuration pages *)
Definition insertEntryIntoConfigPagesList (va : vaddr) (pa LL : page) :=
perform zero := MALInternal.Index.zero in
perform curIdx :=  readIndex LL zero in (** Get index stored at first entry*) (*1*)
(** We have a free entry : go on*)
writeVirtual LL curIdx va ;; (** Write virtual address*)
perform curIdxSucc := MALInternal.Index.succ curIdx in
perform  nextFreeIndex :=  readIndex LL curIdxSucc in (** Get next index*)
writePhysical LL curIdxSucc pa ;; (** Write physical address *)
writeIndex LL zero nextFreeIndex.

(** The [putIndirectionsBack] marks as accessible and underived all virtual 
    addresses used for partition configuration except those stored into the
    partition descriptor *)
Fixpoint putIndirectionsBackAux timeout list (curIdx : index) buf currentPD  currentSh1 l1 listVAddrInParent :=
  match timeout with
  | 0 => getDefaultVAddr
  | S timeout1 =>
    perform zero := MALInternal.Index.zero in
    perform one := MALInternal.Index.succ zero in
    perform two := MALInternal.Index.succ one in
    perform maxindex := getMaxIndex in
    perform maxindexPred := MALInternal.Index.pred maxindex in
    perform res := MALInternal.Index.eqb curIdx maxindexPred  in
    if (res) (**  if last entry *)
    then
      (** set the list page underived and accessible now that we're done handling it *)
      (** TODO should we purge it ? *)
      setUnderived listVAddrInParent currentSh1 l1 ;;
      setAccessible listVAddrInParent currentPD l1 true;;
      perform currentPart := getCurPartition in
      writeAccessibleRec listVAddrInParent currentPart true;;
      (**  get the address of the next page *)
      perform next :=  readPhysical list maxindex in
      perform nextVAddrInParent := readVirtual list maxindexPred in
      perform null :=  getDefaultPage in
      perform cmp :=  MALInternal.Page.eqb next null in
      if cmp (**  no more pages ? *)
      (**  stop  *)
      then ret buf
        (**  else : recursion on the next page *)
      else
        putIndirectionsBackAux timeout1 next two  buf currentPD  currentSh1 l1 nextVAddrInParent
    else
      perform va :=  readVirtual list curIdx in 
      perform succ := MALInternal.Index.succ curIdx in
      perform succ11:= MALInternal.Index.succ succ in
      perform null :=  getDefaultVAddr in
      perform cmp2 :=  MALInternal.VAddr.eqbList va null in
      if cmp2 (**  not a virtual address ? *)
      (**  recursion on the next index  *)
      then putIndirectionsBackAux timeout1 list succ11 buf currentPD  currentSh1 l1 listVAddrInParent
      else (**  else : there is a virtual address *)
        (**  recursion on the next index *)
        (**  Insert page into the linked list*)
        (* storeVirtual va zero buf ;; *)
        setUnderived va currentSh1 l1 ;;
        setAccessible va currentPD l1 true;;
        perform currentPart := getCurPartition in 
        writeAccessibleRec  va currentPart true;;
        (**  Recursive call, using va as our new link head *)
        putIndirectionsBackAux timeout1 list succ11 buf currentPD  currentSh1 l1 listVAddrInParent
  end.

(** The [putIndirectionsBack] fixes the timeout value of the [putIndirectionsBackAux] *)
Definition putIndirectionsBack list (curIdx : index) buf currentPD  currentSh1 l1 listVAddrInParent :=
  putIndirectionsBackAux N list curIdx buf currentPD  currentSh1 l1 listVAddrInParent.

(** The [putShadowsBackAux] marks as accessible and underived virtual addresses 
    stored into the partition descriptor table, except LinkedList pages.
    Note: the LinkedList pages were marked as accessible and underived in putIndirectionsBack *)
Fixpoint putShadowsBackAux timeout (phyRefPart : page) (pos : index) (currentPD  currentSh1 : page)
  (l1 : level) (buf : vaddr) :=
  match timeout with
  | 0 => ret tt
  | S timeout1 =>
    (** check if we reached the LinkedList index *)
    perform idxSh3 := getSh3idx in
    perform isEqIdx := MALInternal.Index.eqb pos idxSh3 in 
    if isEqIdx
    (** no need to "free" it, the whole list was freed during putIndirectionsBack *)
    then ret tt
    else
      perform va :=  readVirtual phyRefPart pos in
      setUnderived va currentSh1 l1;;
      setAccessible va currentPD l1 true;;
      perform currentPart := getCurPartition in
      writeAccessibleRec  va currentPart true;;
      (* perform zero := MALInternal.Index.zero in *)
      (* storeVirtual va zero buf ;; *)

      perform succ := MALInternal.Index.succ pos in
      perform succ11 := MALInternal.Index.succ succ in
      putShadowsBackAux timeout1 phyRefPart succ11 currentPD currentSh1 l1 buf
  end.

(** The [putShadowsBack] fixes the timeout value of [putShadowsBackAux] *)
Definition putShadowsBack (phyRefPart : page) (pos : index) (currentPD  currentSh1 : page)
  (l1 : level) (buf : vaddr):=
  putShadowsBackAux N phyRefPart pos currentPD  currentSh1 l1 buf.

(** The [checkEmptyTable] function returns True if the given Page Table is empty 
    (contains only default values), False otherwise *)
Fixpoint  checkEmptyTableAux timeout tbl idx lvl  :=
  match timeout with
  | 0 => ret false
  | S timeout1 =>
    perform leveltwo := MALInternal.Level.succ fstLevel in
    perform isSndLevel := MALInternal.Level.eqb lvl leveltwo in
    if isSndLevel
    then
      perform addr :=  readPhyEntry tbl idx in (** Read entry, idx - 1 -> 0 (** 1023 *) *) 
      perform defa :=  getDefaultPage in (** Get null address *)
      perform cmp :=  MALInternal.Page.eqb addr defa in
      if cmp (** Is entry null ? *)
      then (** Yea *)
        perform zero := MALInternal.Index.zero in
        perform lebzero := MALInternal.Index.leb idx zero in 
        if lebzero 
        then  (** Last entry ? *)
          ret true (** Return true : we're done ! *)
        else perform idxpred := MALInternal.Index.pred idx in
          checkEmptyTableAux timeout1 tbl idxpred lvl (** Nop : continue until we parsed every entry *)
      else ret false
    else
      perform addr :=  readPhyEntry tbl idx in (** Read entry, idx - 1 -> 0 (** 1023 *) *) 
      perform defa :=  getDefaultPage in (** Get null address *)
      perform cmp :=  MALInternal.Page.eqb addr defa in
      if cmp (** Is entry null ? *)
      then (** Yea *)
        perform zero := MALInternal.Index.zero in
        perform res := MALInternal.Index.leb idx zero in
        if res
        then  (** Last entry ? *)
          ret true (** Return true : we're done ! *)
        else perform idxpred := MALInternal.Index.pred idx in
          checkEmptyTableAux timeout1 tbl idxpred lvl  (** Nop : continue until we parsed every entry *)

      else ret false
  end. (** Nop : table is not empty, ret false *)

(** The [checkEmptyTable] fixes the timeout value of [checkEmptyTableAux] *)
Definition checkEmptyTable tbl idx lvl :=
  checkEmptyTableAux tableSize tbl idx lvl .


(** The [parseConfigPagesListAux] function parses the list of the partition 
    configuration tables to find a virtual address in the parent context corresponding 
    to a given physical page *)
Fixpoint parseConfigPagesListAux timeout (sh : page) (curIdx : index) (tbl :page)  :=
  match timeout with
  | 0 => getDefaultVAddr
  | S timeout1 =>
    perform maxindex :=  getMaxIndex in (** Our last index is table size - 1, as we're indexed on zero*)
    perform maxindexPred := MALInternal.Index.pred maxindex in
    perform res := MALInternal.Index.eqb curIdx maxindexPred in
    if (res)
    then
      perform nextIndirection :=  readPhysical sh maxindex  in (** get next table *) 
      perform nullAddr :=  getDefaultPage in
      perform cmp2 :=  MALInternal.Page.eqb nextIndirection nullAddr in
      if cmp2 (** ensure we're not on an empty table *)
      then getDefaultVAddr (** Failed ? This should not happen... *)
      else
        perform zero := MALInternal.Index.zero in
        perform un := MALInternal.Index.succ zero in
        parseConfigPagesListAux timeout1 nextIndirection un tbl (** Recursive call on the next table *)
    else
      perform idxsucc := MALInternal.Index.succ curIdx in
      perform va := readVirtual sh curIdx in
      perform defaultVAddr := getDefaultVAddr in
      perform cmpva :=  MALInternal.VAddr.eqbList va defaultVAddr in
      if (cmpva)
      then
        perform idxsucc11 := MALInternal.Index.succ idxsucc in
        parseConfigPagesListAux timeout1 sh idxsucc11 tbl
      else  (** Recursive call on this table *)
        perform pad :=  readPhysical sh idxsucc in (** Get entry in table *)
        perform cmp :=  MALInternal.Page.eqb pad tbl in
        if cmp
        then
          perform vaRet :=  readVirtual sh curIdx  in  (** Read associated vaddr*)
          (** Now we have to delete this entry*)
          perform zero := MALInternal.Index.zero in
          perform curNextIdx :=  readIndex sh zero in (** Get next entry index *)
          writeIndex sh idxsucc curNextIdx ;; (** Link this *)
          writeIndex sh zero curIdx ;;
          (* update the number of available entries into this current page **)
          perform one := MALInternal.Index.succ zero in 
          perform nbfi := readIndex sh one in 
          perform nbfisucc := MALInternal.Index.succ nbfi in 
          writeIndex sh one nbfisucc ;;
          (* initialize the virtual entry *)
          perform nullAddrV :=  getDefaultVAddr in
          writeVirtual sh curIdx nullAddrV ;; 
          ret vaRet
        else
          perform idxsucc := MALInternal.Index.succ curIdx in
          perform idxsucc11 := MALInternal.Index.succ idxsucc in
          parseConfigPagesListAux timeout1 sh idxsucc11 tbl
  end.  (** Recursive call on this table *)

(** The [parseConfigPagesList] function fixes the timeout value of [parseConfigPagesListAux] *)
Definition parseConfigPagesList (sh : page) (idx : index) (tbl :page) :=
  parseConfigPagesListAux N sh idx tbl.

(** The 'getnbFreeEntriesLL' function returns the number of the available entries into a given LL table *)
Definition getnbFreeEntriesLL sh3 :=
perform zeroI :=  MALInternal.Index.zero in
perform oneI :=  MALInternal.Index.succ zeroI in 
readIndex sh3 oneI.

(** The [checkEnoughEntriesLinkedListAux] function checks if there are [cnt]
    availeble entries into the partition configuration pages list *)
Fixpoint checkEnoughEntriesLLAux timeout (LL : page) (* the table *)
 : LLI page:= 
match timeout with
 | 0 => getDefaultPage
 | S timeout1 =>
  perform threeI := MALInternal.Index.const3 in
  (* this entry contains the number of available entries *)
  perform nbfree := getnbFreeEntriesLL LL in 
  perform res := MALInternal.Index.geb nbfree threeI in
  if(res) 
  then ret LL (** this page contains at least three available entries *)
  else
   (** move to the next LL table *)
   perform maxidx := getMaxIndex in
   perform nextLL :=  readPhysical LL maxidx in
   perform isNull := comparePageToNull nextLL in 
   if isNull 
   then getDefaultPage (* No available pages *)
   else
    checkEnoughEntriesLLAux timeout1 nextLL
end.

Definition checkEnoughEntriesLinkedList (lasttable : page): LLI page:=
checkEnoughEntriesLLAux nbPage lasttable. 

Fixpoint checkEnoughEntriesLLToPrepareAllAux timeout fstLLtable nbL :=
match timeout with
 | 0 => getDefaultPage
 | S timeout1 =>
    perform islevel0 := Level.eqb nbL fstLevel in
    if islevel0 
    then ret fstLLtable
    else 
      perform nextLLtable := checkEnoughEntriesLinkedList fstLLtable  in 
      perform isNull := comparePageToNull nextLLtable in 
      if (isNull) then   getDefaultPage
      else 
        perform nbLpred := MALInternal.Level.pred nbL in 
        checkEnoughEntriesLLToPrepareAllAux timeout1 nextLLtable nbLpred
end.

Definition checkEnoughEntriesLLToPrepareAll fstLLtable nbL:=
 checkEnoughEntriesLLToPrepareAllAux nbLevel fstLLtable nbL.

Definition insertEntryIntoLL LLtable va (pa: page): LLI unit :=
perform zeroI := MALInternal.Index.zero in
perform idx :=  readIndex LLtable zeroI in
writeVirtual LLtable idx va ;; (** Write virtual address*)
perform curIdxSucc := MALInternal.Index.succ idx in
perform  nextFreeIndex :=  readIndex LLtable curIdxSucc in (** Get next index*)

writePhysical LLtable curIdxSucc pa ;; (** Write physical address *)
(* update the first free entry value *)
writeIndex LLtable zeroI nextFreeIndex ;;
(* update the number of available entry in current LL table *)
perform oneI := MALInternal.Index.succ zeroI in
perform nbfi := readIndex LLtable oneI in
perform nbfipred := MALInternal.Index.pred nbfi in 
writeIndex LLtable oneI nbfipred.

 
(** The [initConfigPagesListAux] function initializes the partition configuration
    pages list *)
Fixpoint initConfigPagesListAux timeout shadow3 idx :=
  match timeout with
  | 0 => ret tt
  | S timeout1 =>
    perform zeroI :=  MALInternal.Index.zero in
    perform mi :=  getMaxIndex in (* 7 *)
    perform mipred := MALInternal.Index.pred mi in 
    perform res := MALInternal.Index.geb idx mipred in
    perform res11 := MALInternal.Index.eqb idx zeroI in
    if (res) (** Check if the current index is he last index into the table **)
    then
     (** The last entry must contain the next physical page of the configuration tables linked list, 
     in this case we put the defaultPage *)
      perform nullP :=  getDefaultPage in
      perform nullV :=  getDefaultVAddr in
      writeVirtual shadow3 mipred nullV ;;
      writePhysical shadow3 mi nullP ;;
      perform maxentries := maxFreeLL in 
      perform oneI :=  MALInternal.Index.succ zeroI in 
      perform twoI :=  MALInternal.Index.succ oneI in 
      writeIndex shadow3 zeroI twoI ;;
      writeIndex shadow3 oneI maxentries 
    else if (res11) (** Check if the current index is the first index **)
      then
       (** The first entry must contain the first available entry, in this case the index 1 
       is the position of the next available entry  **)  
        perform oneI :=  MALInternal.Index.succ zeroI in 
        perform twoI :=  MALInternal.Index.succ oneI in 
        initConfigPagesListAux timeout1 shadow3 twoI
      else 
       (** For the other indices : every odd position must contain the default virtual address 
          and evrey even position must contain the next available entry. 
          An available entry contain the default virtual address value **)
        perform nullV :=  getDefaultVAddr in
        writeVirtual shadow3 idx nullV ;;
        perform nextIdx :=  MALInternal.Index.succ idx in
        perform nextIdx11 :=  MALInternal.Index.succ nextIdx in
        writeIndex shadow3 nextIdx nextIdx11 ;;
        initConfigPagesListAux timeout1 shadow3 nextIdx11
  end.



(** The [initConfigPagesList] function fixes the timeout value of 
    [initConfigPagesListAux] *)
Definition initConfigPagesList shadow3 idx:=
  initConfigPagesListAux tableSize shadow3 idx.

(** The [initVEntryTable] function initialize virtual entries [VEntry] of a 
    given table [shadow1] by default value (defaultVAddr for [va] and false for
    [pd] flag *)
Fixpoint initVEntryTableAux timeout shadow1 idx :=
  match timeout with
  | 0 => ret tt
  | S timeout1 =>

    perform maxindex := getMaxIndex in
    perform res := MALInternal.Index.ltb idx maxindex in
    if (res)
    then
      perform defaultVAddr := getDefaultVAddr in
      writeVirEntry shadow1 idx defaultVAddr;;
      perform nextIdx :=  MALInternal.Index.succ idx in
      initVEntryTableAux timeout1 shadow1 nextIdx
    else
      perform defaultVAddr := getDefaultVAddr in
      writeVirEntry shadow1 idx defaultVAddr
  end.

(**  The [initVEntryTable] function fixes the timeout value of [initVEntryTableAux] *)
Definition initVEntryTable  shadow1 idx  :=
  initVEntryTableAux tableSize  shadow1 idx .

(** The [initVAddrTable] function initializes virtual addresses [vaddr] of a 
    given table [shadow2] by default value (defaultVAddr) *)
Fixpoint initVAddrTableAux timeout shadow2 idx :=
  match timeout with
  | 0 => ret tt
  | S timeout1 =>
    perform maxindex := getMaxIndex in
    perform res := MALInternal.Index.ltb idx maxindex in
    if (res)
    then
      perform defaultVAddr := getDefaultVAddr in
      writeVirtual shadow2 idx defaultVAddr;;
      perform nextIdx :=  MALInternal.Index.succ idx in
      initVAddrTableAux timeout1 shadow2 nextIdx
    else  perform defaultVAddr := getDefaultVAddr in
      writeVirtual shadow2 idx defaultVAddr
  end.

(**  The [initVEntryTable] function fixes the timeout value of [initVEntryTableAux] *)
Definition initVAddrTable sh2 n :=
  initVAddrTableAux tableSize sh2 n.

(** The [initPEntryTableAux] function initialize physical entries [PEntry] of 
    a given table [ind] by default value (defaultPage for [pa] and false for 
    other flags *) 
Fixpoint initPEntryTableAux timeout table idx :=
  match timeout with
  |0 =>  ret tt
  | S timeout1 => perform maxindex := getMaxIndex in
    perform res := MALInternal.Index.ltb idx maxindex in
    if (res)
    then perform defaultPage := getDefaultPage in
      writePhyEntry table idx defaultPage false false false false false;;
      perform nextIdx :=  MALInternal.Index.succ idx in
      initPEntryTableAux timeout1 table nextIdx
    else  perform defaultPage := getDefaultPage in
      writePhyEntry table idx defaultPage false false false false false 
  end.

(** The [initPEntryTable] function fixes the timeout value of [initPEntryTableAux] *)
Definition initPEntryTable (table : page) (idx : index) :=
  initPEntryTableAux tableSize table idx.

(** The [linkNewPageIntoLL] function links a new page to the
    partition configuration tables linked list as a first element *)
Definition PushNewPageOntoLL partition newLL v : LLI unit:=
(* initialize the new table *)
perform zeroI :=  MALInternal.Index.zero in
initConfigPagesList newLL zeroI ;;
(* get the head of LL Vaddr/phy *)
perform fstLLva := getConfigTablesLinkedListVaddr partition in 
perform fstLL := getConfigTablesLinkedList partition in 
(* Update the new table : Point the previous first table of LL *)
perform maxindex := getMaxIndex in
perform maxindexPred := MALInternal.Index.pred maxindex in 
writeVirtual newLL maxindexPred fstLLva ;;
writePhysical newLL maxindex fstLL;;
(* push a new top onto LL : modify the partition descriptor *)
perform idxLL := getSh3idx in
updatePartitionDescriptor partition idxLL newLL v.

(** The [checkChild] function checks whether the given virtual address [va] is 
    marked as a child of a given partition *)
Definition checkChild partition (l1 : level) (va : vaddr): LLI bool :=
  perform sh1 :=  getFstShadow partition in
  perform idxVA :=  getIndexOfAddr va fstLevel in
  perform tbl :=  getTableAddr sh1 va l1 in
  perform isNull := comparePageToNull tbl in
  if isNull 
  then ret false 
  else
  readPDflag tbl idxVA.

(** The [checkKernalMap] function checks if the given virtual address corresponds
    to a kernel mapping *)
Definition checkKernelMap (va : vaddr) : LLI bool:=
  perform kidx := getKidx in
  perform l1 := getNbLevel in
  perform idxVA :=  getIndexOfAddr va l1 in
  MALInternal.Index.eqb kidx idxVA.

(** The [checkVAddrsEqualityWOOffsetAux] checks if given virtual addresses are equal
    without taking into account offset values *)
Fixpoint checkVAddrsEqualityWOOffsetAux timeout (va1 va2 : vaddr) (l1 : level) :=
  match timeout with
  |0 =>  ret true
  |S timeout1 =>
    perform idx1 := getIndexOfAddr va1 l1 in
    perform idx2 := getIndexOfAddr va2 l1 in
    perform isFstLevel := MALInternal.Level.eqb l1 fstLevel in
    if isFstLevel 
    then
      MALInternal.Index.eqb idx1 idx2
    else
      perform levelpred := MALInternal.Level.pred l1 in
      perform idxsEq := MALInternal.Index.eqb idx1 idx2 in 
      if idxsEq
      then checkVAddrsEqualityWOOffsetAux timeout1 va1 va2 levelpred
      else ret false
  end.
(** The [checkVAddrsEqualityWOOffset] function fixes the timout value of 
    [checkVAddrsEqualityWOOffsetAux] *)
Definition checkVAddrsEqualityWOOffset (va1 va2 : vaddr) (l1 : level) :=
  checkVAddrsEqualityWOOffsetAux nbLevel va1 va2 l1.

Definition initFstShadow table nbL zero := 
perform res := MALInternal.Level.eqb nbL fstLevel in 
if res
then 
initVEntryTable table zero
else 
initPEntryTable table zero. 

Definition initSndShadow table nbL zero := 
perform res := MALInternal.Level.eqb nbL fstLevel in 
if res
then 
initVAddrTable table zero
else 
initPEntryTable table zero.

Definition isVAddrAccessible (pageVAddr : vaddr) (pageDirectory : page) : LLI bool :=
(* checking last mmu table  *)
perform nbL := getNbLevel in
perform pageLastMMUTable := getTableAddr pageDirectory pageVAddr nbL in
perform pageLastMMUTableisNull := comparePageToNull pageLastMMUTable in
if pageLastMMUTableisNull then
  ret false
else

perform idxPageInTable := getIndexOfAddr pageVAddr nbL in
perform pageIsPresent := readPresent pageLastMMUTable idxPageInTable in
if negb pageIsPresent then
  ret false
else

perform pageIsAccessible := readAccessible pageLastMMUTable idxPageInTable in
if negb pageIsAccessible then
  ret false
else
  ret true.

Definition checkVidtAccessibility (pageDirectory : page) : LLI bool :=
perform vidtVaddr := getVidtVAddr in
perform vidtIsAccessible := isVAddrAccessible vidtVaddr pageDirectory in
ret vidtIsAccessible.

(* Definition getContextEndAddr (contextAddr : vaddr) : LLI vaddr :=
  perform contextEndAddr := getNthVAddrFrom contextAddr contextSizeMinusOne in
  ret contextEndAddr. *)

