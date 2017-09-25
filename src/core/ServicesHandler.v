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
    This file contains the PIP services handlers to check whether the parameters 
    passed into the handler are of the expected dada types *)

Require Import Model.Hardware Model.ADT Model.Lib Model.MAL 
Model.MALInternal Bool Arith Core.Services.

Fixpoint vaddrWellTyped (va : preVaddr) (l : level) bound : LLI bool := 
match bound with
| 0 => ret false
| S bound1 =>
  perform i := extractPreIndex va l in
  perform isIndex :=  PreIndex.ltb i tableSize in
  if isIndex
  then 
    perform islastlevel := Level.eqb l fstLevel in
    if islastlevel
    then ret true
    else 
      perform l1 := Level.pred l in vaddrWellTyped va l1 bound1
  else ret false
end.

Definition createPartitionHandler (descChild pdChild shadow1Child shadow2Child 
                            ConfigPagesList :preVaddr) : LLI bool :=
perform nbprelevel := getNbLevel in
perform w1 := vaddrWellTyped descChild nbprelevel nbLevel in
perform w2 := vaddrWellTyped pdChild nbprelevel nbLevel in
perform w3 := vaddrWellTyped shadow1Child nbprelevel nbLevel in
perform w4 := vaddrWellTyped shadow2Child nbprelevel nbLevel in
perform w5 := vaddrWellTyped ConfigPagesList nbprelevel nbLevel in
if w1 && w2 && w3 && w4 && w5
then
  perform descChildW := preVaddrToVaddr descChild in
  perform pdChildW := preVaddrToVaddr pdChild in
  perform shadow1ChildW := preVaddrToVaddr shadow1Child in
  perform shadow2ChildW := preVaddrToVaddr shadow2Child in
  perform ConfigPagesListW := preVaddrToVaddr ConfigPagesList in
  createPartition descChildW pdChildW shadow1ChildW shadow2ChildW ConfigPagesListW
else ret false.

Definition countToMapHandler (descChild vaChild : preVaddr) :=
perform nbprelevel := getNbLevel in
perform w1 := vaddrWellTyped descChild nbprelevel nbLevel in
perform w2 := vaddrWellTyped vaChild nbprelevel nbLevel in
if w1 && w2
then
  perform descChildW := preVaddrToVaddr descChild in
  perform vaChildW := preVaddrToVaddr vaChild in
  countToMap descChildW vaChildW
else  MALInternal.Count.zero.

Definition prepareHandler (descChild  va fstVA: preVaddr)
(needNewConfigPagesList : bool) : LLI bool :=
perform nbprelevel := getNbLevel in
perform w1 := vaddrWellTyped descChild nbprelevel nbLevel in
perform w2 := vaddrWellTyped va nbprelevel nbLevel in
perform w3 := vaddrWellTyped fstVA nbprelevel nbLevel in
if w1 && w2 && w3
then
  perform descChildW := preVaddrToVaddr descChild in
  perform vaW := preVaddrToVaddr va in
  perform fstVAW := preVaddrToVaddr fstVA in
  prepare descChildW vaW fstVAW needNewConfigPagesList
else ret false.

Definition addVAddrHandler (vaInCurrentPartition descChild vaChild: preVaddr)
(r w e : bool) : LLI bool :=
perform nbprelevel := getNbLevel in
perform w1 := vaddrWellTyped vaInCurrentPartition nbprelevel nbLevel in
perform w2 := vaddrWellTyped descChild nbprelevel nbLevel in
perform w3 := vaddrWellTyped vaChild nbprelevel nbLevel in
if w1 && w2 && w3 
then
  perform vaInCurrentPartitionW := preVaddrToVaddr descChild in
  perform descChildW := preVaddrToVaddr descChild in
  perform vaChildW := preVaddrToVaddr vaChild in
  addVAddr vaInCurrentPartitionW descChildW vaChildW r w e
else ret false.

Definition mappedInChildHandler (vaChild : preVaddr) : LLI vaddr := 
perform nbprelevel := getNbLevel in
perform w1 := vaddrWellTyped vaChild nbprelevel nbLevel in
if w1 
then
  perform vaChildW := preVaddrToVaddr vaChild in
  mappedInChild vaChildW
else ret defaultVAddr.

Definition removeVAddrHandler (descChild vaChild : preVaddr) :=
perform nbprelevel := getNbLevel in
perform w1 := vaddrWellTyped descChild nbprelevel nbLevel in
perform w2 := vaddrWellTyped vaChild nbprelevel nbLevel in
if w1 && w2
then
  perform descChildW := preVaddrToVaddr descChild in
  perform vaChildW := preVaddrToVaddr vaChild in
  removeVAddr descChildW vaChildW
else ret false.

Definition deletePartitionHandler (descChild : preVaddr) :=
perform nbprelevel := getNbLevel in
perform w1 := vaddrWellTyped descChild nbprelevel nbLevel in
if w1 
then
  perform descChildW := preVaddrToVaddr descChild in
  deletePartition descChildW
else ret false.

Definition collectHandler (descChild vaToCollect: preVaddr):=
perform nbprelevel := getNbLevel in
perform w1 := vaddrWellTyped descChild nbprelevel nbLevel in
perform w2 := vaddrWellTyped vaToCollect nbprelevel nbLevel in
if w1 && w2
then
  perform descChildW := preVaddrToVaddr descChild in
  perform vaToCollectW := preVaddrToVaddr vaToCollect in
  collect descChildW vaToCollectW
else ret false.