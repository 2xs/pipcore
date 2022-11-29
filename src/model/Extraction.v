From Pip.Model.Meta Require Import TypesModel StateModel InterfaceModel.
From Pip.Core Require Import ModelAgnosticCode.

From Pip.Model.Hollow Require Import HollowModel.

Require Extraction.
Extraction Language Haskell.

(** EXTRACTION *)
Module Code := ModelAgnosticCode HollowTypes HollowState HollowInterface.
Separate Extraction Code.
