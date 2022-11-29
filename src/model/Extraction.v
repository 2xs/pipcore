From Pip.Model Require Import CoreTypes.
From Pip.Model Require Import StateParameter.
From Pip.Model Require Import StateParameterizedMonadType.
From Pip.Model Require Import MonadInterfaceParameters.
From Pip.Model Require Import AMServices.

From Pip.Model Require Import AbstractMonad.

Require Extraction.
Extraction Language Haskell.

(** EXTRACTION *)
Module Code := MonadDependentCode AbstractState AbstractMonad.
Separate Extraction Code.
