(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2017)                 *)
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

Require Import List NPeano Omega Coq.Logic.Classical_Prop Bool.
Import List.ListNotations.

(** * Summary 
    This file contains required functions to manipulate an association list *) 
Fixpoint eqList {A : Type} (l1 l2 : list A) (eq : A -> A -> bool) : bool := 
 match l1, l2 with 
 |nil,nil => true
 |a::l1' , b::l2' => if  eq a b then eqList l1' l2' eq else false
 |_ , _ => false
end.

Definition beqPairs {A B: Type} (a : (A*B)) (b : (A*B)) (eqA : A -> A -> bool) (eqB : B -> B -> bool) :=
if (eqA (fst a) (fst b)) && (eqB (snd a) (snd b))  then true else false.

Fixpoint lookup {A B C: Type} (k : A) (i : B)  (assoc : list ((A * B)*C))  (eqA : A -> A -> bool) (eqB : B -> B -> bool) :=
  match assoc with
    | nil => None  
    | (a, b) :: assoc' => if beqPairs a (k,i) eqA eqB then Some b else lookup k i assoc' eqA eqB
  end. 
 
Fixpoint removeDup {A B C: Type} (k : A) (i : B) (assoc : list ((A * B)*C) )(eqA : A -> A -> bool) (eqB : B -> B -> bool)   :=
  match assoc with
    | nil => nil
    | (a, b) :: assoc' => if beqPairs a (k,i) eqA eqB then removeDup k i assoc' eqA eqB else (a, b) :: (removeDup k i assoc' eqA eqB)
  end.

Definition add {A B C: Type} (k : A) (i : B) (v : C) (assoc : list ((A * B)*C) ) (eqA : A -> A -> bool) (eqB : B -> B -> bool)  :=
  (k,i,v) :: removeDup k i assoc eqA eqB.