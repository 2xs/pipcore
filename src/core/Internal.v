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
Require Import Model.Hardware Model.ADT Model.MAL Bool Arith List Coq.Init.Peano.
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


(** The [verifyProperties] returns true if the given virtual address is not 
    derived, accessible, present and is not a default virtual address *)
Definition verifyProperties currentPD currentSh1 l1 (va : vaddr) : LLI bool :=
  perform ptVA := getTableAddr currentPD va l1 in
  perform isNull := comparePageToNull ptVA in
  if isNull then ret false else
  perform idxVA := getIndexOfAddr va fstLevel in
  perform presentVA := readPresent ptVA idxVA in
  perform accessVA := readAccessible ptVA idxVA in
  perform ptVAFromCurrentSh1 := getTableAddr currentSh1 va l1 in
  perform isNull := comparePageToNull ptVAFromCurrentSh1 in
  if isNull then ret false else
  perform isnotderived := checkDerivation ptVAFromCurrentSh1 idxVA in
  perform defaultVAddr := getDefaultVAddr in
  perform isNull := MALInternal.VAddr.eqbList defaultVAddr va in
  ret (negb isNull && presentVA && accessVA && isnotderived).

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
Fixpoint insertEntryIntoConfigPagesListAux timeout (va : vaddr) (pa sh3 : page) :=
  match timeout with
  | 0 => ret tt
  | S timeout1 =>
    perform zero := MALInternal.Index.zero in
    perform curIdx :=  readIndex sh3 zero in (** Get index stored at first entry*) (*1*)
    perform maxindex :=  getMaxIndex in
    (* perform tblsizepred := MALInternal.Index.pred tblsize in  *)
    perform res := MALInternal.Index.eqb curIdx maxindex in
    if(res) (** Are we at the end of our table ? *)
    then
      (** Next page : recursive call *)
      perform nextIndirection :=  readPhyEntry sh3 curIdx in 
      insertEntryIntoConfigPagesListAux timeout1 va pa nextIndirection
    else
      (** We have a free entry : go on*)
      (* 			perform  nextFreeIndex :=  readIndex sh3 curIdx in (** Get next index*)  *)
      writeVirtual sh3 curIdx va ;; (** Write virtual address*)
      perform curIdxSucc := MALInternal.Index.succ curIdx in
      perform  nextFreeIndex :=  readIndex sh3 curIdxSucc in (** Get next index*)
      writePhyEntry sh3 curIdxSucc pa false false false false false;; (** Write physical address *)
      writeIndex sh3 zero nextFreeIndex
  end. (** Update index *)

(** The [insertEntryIntoConfigPagesList] fixes the timeout value of 
    [insertEntryIntoConfigPagesListAux] *) 
Definition insertEntryIntoConfigPagesList (va : vaddr) (pa sh3 : page) :=
  insertEntryIntoConfigPagesListAux N va pa sh3.

(** The [putIndirectionsBack] marks as accessible and underived all virtual 
    addresses used for partition configuration except those stored into the
    partition descriptor *)
Fixpoint putIndirectionsBackAux timeout list (curIdx : index) buf currentPD  currentSh1 l1 :=
  match timeout with
  | 0 => getDefaultVAddr
  | S timeout1 =>
    perform zero := MALInternal.Index.zero in
    perform one := MALInternal.Index.succ zero in
    perform maxindex := getMaxIndex in
    perform res := MALInternal.Index.eqb curIdx maxindex  in
    if (res) (**  if last entry *)
    then
      (**  get the address of the next page *)
      perform next :=  readPhyEntry list maxindex in 
      perform null :=  getDefaultPage in
      perform cmp :=  MALInternal.Page.eqb next null in
      if cmp (**  no more pages ? *)
      (**  stop  *)
      then ret buf
        (**  else : recursion on the next page *)
      else
        putIndirectionsBackAux timeout1 next one  buf currentPD  currentSh1 l1
    else
      perform va :=  readVirtual list curIdx in 
      perform succ := MALInternal.Index.succ curIdx in
      perform succ11:= MALInternal.Index.succ succ in
      perform null :=  getDefaultVAddr in
      perform cmp2 :=  MALInternal.VAddr.eqbList va null in
      if cmp2 (**  not a virtual address ? *)
      (**  recursion on the next index  *)
      then putIndirectionsBackAux timeout1 list succ11 buf currentPD  currentSh1 l1
      else (**  else : there is a virtual address *)
        (**  recursion on the next index *)
        (**  Insert page into the linked list*)
        (* storeVirtual va zero buf ;; *)
        setUnderived va currentSh1 l1 ;;
        setAccessible va currentPD l1 true;;
        perform currentPart := getCurPartition in 
        writeAccessibleRec  va currentPart true;;
        (**  Recursive call, using va as our new link head *)
        putIndirectionsBackAux timeout1 list succ11 buf currentPD  currentSh1 l1
  end.

(** The [putIndirectionsBack] fixes the timeout value of the [putIndirectionsBackAux] *)
Definition putIndirectionsBack list (curIdx : index) buf currentPD  currentSh1 l1  :=
  putIndirectionsBackAux N list curIdx buf currentPD  currentSh1 l1 .

(** The [putShadowsBackAux] marks as accessible and underived virtual addresses 
    stored into the partition descriptor table *)
Fixpoint putShadowsBackAux timeout (phyRefPart : page) (pos : index) (currentPD  currentSh1 : page)
  (l1 : level) (buf : vaddr) :=
  match timeout with
  | 0 => ret tt
  | S timeout1 => 
    perform va :=  readVirtual phyRefPart pos in
    setUnderived va currentSh1 l1;;
    setAccessible va currentPD l1 true;;
    perform currentPart := getCurPartition in 
    writeAccessibleRec  va currentPart true;;
    perform zero := MALInternal.Index.zero in
    (* storeVirtual va zero buf ;; *)
    perform idxSh3 := getSh3idx in
    perform isEqIdx := MALInternal.Index.eqb pos idxSh3 in 
    if isEqIdx
    then ret tt
    else
      perform succ := MALInternal.Index.succ pos in
      perform succ11 := MALInternal.Index.succ succ in
      putShadowsBackAux timeout1 phyRefPart succ11 currentPD  currentSh1 l1 buf
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
Fixpoint parseConfigPagesListAux timeout (sh : page) (idx : index) (tbl :page)  :=
  match timeout with
  | 0 => getDefaultVAddr
  | S timeout1 =>
    perform maxindex :=  getMaxIndex in (** Our last index is table size - 1, as we're indexed on zero*)
    perform res := MALInternal.Index.eqb idx maxindex in
    if (res)
    then
      perform nextIndirection :=  readPhyEntry sh maxindex  in (** get next table *) 
      perform nullAddr :=  getDefaultPage in
      perform cmp2 :=  MALInternal.Page.eqb nextIndirection nullAddr in
      if cmp2 (** ensure we're not on an empty table *)
      then getDefaultVAddr (** Failed ? This should not happen... *)
      else
        perform zero := MALInternal.Index.zero in
        perform un := MALInternal.Index.succ zero in
        parseConfigPagesListAux timeout1 nextIndirection un tbl (** Recursive call on the next table *)
    else
      perform idxsucc := MALInternal.Index.succ idx in
      perform va := readVirtual sh idx in
      perform defaultVAddr := getDefaultVAddr in
      perform cmpva :=  MALInternal.VAddr.eqbList va defaultVAddr in
      if (cmpva)
      then
        perform idxsucc11 := MALInternal.Index.succ idxsucc in
        parseConfigPagesListAux timeout1 sh idxsucc11 tbl
      else  (** Recursive call on this table *)
        perform pad :=  readPhyEntry sh idxsucc in (** Get entry in table *)
        perform cmp :=  MALInternal.Page.eqb pad tbl in
        if cmp
        then
          perform vaRet :=  readVirtual sh idx  in  (** Read associated vaddr*)
          (** Now we have to delete this entry*)
          perform zero := MALInternal.Index.zero in
          perform curNextIdx :=  readIndex sh zero in (** Get next entry index *)
          writeIndex sh idxsucc curNextIdx ;; (** Link this *)
          writeIndex sh zero idx ;;
          perform nullAddrV :=  getDefaultVAddr in
          writeVirtual sh idx nullAddrV ;; 
          ret vaRet
        else
          perform idxsucc := MALInternal.Index.succ idx in
          perform idxsucc11 := MALInternal.Index.succ idxsucc in
          parseConfigPagesListAux timeout1 sh idxsucc11 tbl
  end.  (** Recursive call on this table *)

(** The [parseConfigPagesList] function fixes the timeout value of [parseConfigPagesListAux] *)
Definition parseConfigPagesList (sh : page) (idx : index) (tbl :page) :=
  parseConfigPagesListAux N sh idx tbl.

(** The [enoughConfigPagesListEntriesAux] function checks if there are [cnt]
    availeble entries into the partition configuration pages list *)
Fixpoint enoughConfigPagesListEntriesAux timeout (sh : page) (idx : index)
 (cnt : count) ( indir : level):=
  match timeout with
  | 0 => ret false
  | S timeout1 =>
    perform prod := MALInternal.Count.mul3 indir in
    perform res := MALInternal.Count.geb cnt prod in
    if(res) (** 3 free entries per indirection or more : ret True *)
    then ret true
    else
      perform zero := MALInternal.Index.zero in
      perform res := MALInternal.Index.eqb idx zero in
      if(res)
      then (** First call on table : get first free index *)
        perform nextIdx :=  readIndex sh zero in
        (** puthexIndex nextIdx *)
        enoughConfigPagesListEntriesAux timeout1 sh nextIdx cnt indir

      else perform maxindex :=  getMaxIndex in
       perform res := MALInternal.Index.eqb idx maxindex in
        if(res) (** End of table ? *)
        then
          perform nextIndirection :=  readPhyEntry sh idx in (** Get next table addr*) 
          perform nullAddr :=  getDefaultPage in
          perform cmp :=  MALInternal.Page.eqb nextIndirection nullAddr in
          if cmp (** No next table ? *)
          then ret false
          else enoughConfigPagesListEntriesAux timeout1 nextIndirection zero cnt indir
            (** Recursive call on next table *)
        else
          (** Not at end of table : increment and recursive call to next entry *)
          perform idx11 := MALInternal.Index.succ idx in
          perform nextIdx :=  readIndex sh idx11 in
          perform countsucc := MALInternal.Count.succ cnt in
          enoughConfigPagesListEntriesAux timeout1 sh nextIdx countsucc indir
  end.

(** The [enoughConfigPagesListEntries] function fixes the timeout value of [parseConfigPagesListAux] *)
Definition enoughConfigPagesListEntries (sh : page) (idx : index) (cnt : count) ( indir : level):=
  enoughConfigPagesListEntriesAux N sh idx cnt indir.

(** The [initConfigPagesListAux] function initializes the partition configuration
    pages list *)
Fixpoint initConfigPagesListAux timeout shadow3 idx :=
  match timeout with
  | 0 => ret tt
  | S timeout1 =>
    perform zero :=  MALInternal.Index.zero in
    perform maxindex := getMaxIndex in (* 7 *)
    perform res := MALInternal.Index.eqb idx maxindex in
    perform res11 := MALInternal.Index.eqb idx zero in
    if (res) (** Check if the current index is he last index into the table **)
    then
     (** The last entry must contain the next physical page of the configuration tables linked list, 
     in this case we put the defaultPage *)
      perform nullP :=  getDefaultPage in
      writePhysical shadow3 idx nullP 
    else if (res11) (** Check if the current index is the first index **)
      then
       (** The first entry must contain the first available entry, in this case the index 1 
       is the position of the next available entry  **)  
        perform nextIdx :=  MALInternal.Index.succ idx in 
        writeIndex shadow3 idx nextIdx ;;
        initConfigPagesListAux timeout1 shadow3 nextIdx
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
Fixpoint initPEntryTableAux timeout  table idx :=
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

(** The [linkNewListToConfigPagesListAux] function links a new list (page) to the
    partition configuration tables linked list *)
Fixpoint linkNewListToConfigPagesListAux timeout sh p v :=
  match timeout with
  |0 =>  ret tt
  | S timeout1 =>
    perform zero := MALInternal.Index.zero in
    perform maxindex :=  getMaxIndex in
    perform nextPage :=  readPhyEntry sh maxindex in 
    perform nullAddr :=  getDefaultPage in
    perform cmp :=  MALInternal.Page.eqb nextPage nullAddr in
    if cmp
    then
      writePhyEntry sh maxindex p false false false false false;;
      initConfigPagesList p zero ;;
      insertEntryIntoConfigPagesList v p p
    else linkNewListToConfigPagesListAux timeout1 nextPage p v
  end.

(** The [linkNewListToConfigPagesList] function fixes the timeout value of 
    [linkNewListToConfigPagesListAux] *)
Definition linkNewListToConfigPagesList (sh3 : page) (n : page) (v : vaddr) :=
  linkNewListToConfigPagesListAux N sh3 n v.



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