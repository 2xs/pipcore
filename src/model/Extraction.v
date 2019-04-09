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
(**  * Summary 
      In this file we define the required configuration to extract the  MALInternal, MAL, Internal and 
      Services functions from Coq to JSON.
      The JSON output will be analyzed to generate the corresponding C implementation *)
Require Import Model.MAL Model.Hardware Model.ADT Core.Services Core.Internal.
Require Extraction.
Extraction Language JSON.

(** Coq standard library *)
Extract Inductive unit => "()" [ "()" ].
Extract Inductive bool => "Bool" [ "True" "False" ].
Extract Inlined Constant ret => "return".
Extract Inlined Constant negb => "not".
Extract Inlined Constant andb => "(&&)".
Extract Inlined Constant bind => "(>>=)".
Extract Inlined Constant orb => "(||)".
Extract Inductive nat => Int [ "0" "succ" ]. (* only for recursion bound *) 

(** Types and functions used by Services and Internal *)
Extract Inductive index => "index" [ "index"]. 
Extract Inductive page => "page" [ "page"].
Extract Inductive vaddr => "vaddr" [ "vaddr"].
Extract Inductive Pentry => "Pentry" [ "Pentry"].
Extract Inductive Ventry => "Ventry" [ "Ventry"].
Extract Inductive level => "level" [ "level"].
Extract Inductive count => "Count" [ "Count"].

(** EXTRACTION *)
Extraction Library MALInternal. 
Extraction Library MAL.
Extraction Library Internal .
Extraction Library Services.

