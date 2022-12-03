From Pip.Model.Meta Require Import TypesModel StateModel InterfaceModel.
From Pip.Core Require Import ModelAgnosticCode.

From Pip.Model.Hollow Require Import HollowModel.

Require Extraction.
Extraction Language Haskell.

(*
   Place the extracted AST inside the "build" folder at root
   What ? Stop staring at me like that, even CompCert uses this. Yikes
   https://github.com/AbsInt/CompCert/blob/master/extraction/extraction.v#L158
*)
Cd "build".

(** EXTRACTION *)
Module Code := ModelAgnosticCode HollowTypes HollowState HollowInterface.
Separate Extraction Code.

Cd "..".