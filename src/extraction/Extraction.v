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
Require Import Pip.Model.MAL Pip.Model.Hardware Pip.Model.ADT Pip.Core.Services Pip.Core.Internal.

Require Extraction.
Extraction Language JSON.

(*
   Place the extracted AST inside the "build" folder at root
   What ? Stop staring at me like that, even CompCert uses this. Yikes
   https://github.com/AbsInt/CompCert/blob/master/extraction/extraction.v#L158
*)
Cd "build".

(** Coq standard library *)
(* Tell Coq to extract those names verbatim, instead of using if-then-else *)
Extract Inlined Constant andb => "andb".
Extract Inlined Constant orb => "orb".

(** EXTRACTION *)
Extraction Library IAL.
Extraction Library MALInternal.
Extraction Library MAL.
Extraction Library Internal.
Extraction Library Services.

Cd "..".
