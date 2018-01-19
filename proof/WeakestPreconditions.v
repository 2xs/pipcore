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

(** * Summary  
    In this file we formalize and prove the weakest precondition of the 
    MAL and MALInternal functions *)
Require Import Model.ADT Model.Hardware Model.MAL Model.Lib 
Omega List StateLib.
Lemma ret  (A : Type) (a : A) (P : A -> state -> Prop) : {{ P a }} ret a {{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma bind  (A B : Type) (m : LLI A) (f : A -> LLI B) (P : state -> Prop)( Q : A -> state -> Prop) (R : B -> state -> Prop) :
  (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} m {{ Q }} -> {{ P }} perform x := m in f x {{ R }}.
Proof. 
intros H1 H2 s H3; unfold bind; case_eq (m s); [intros [a s'] H4 | intros k s' H4];
apply H2 in H3; rewrite H4 in H3; trivial.
case_eq (f a s'); [intros [b s''] H5 |  intros k s'' H5];
apply H1 in H3; rewrite H5 in H3; trivial.
Qed. 

Lemma put  (s : state) (P : unit -> state -> Prop) : {{ fun _ => P tt s }} put s {{ P }}.
Proof.
intros s0 H;trivial.
Qed.

Lemma get  (P : state -> state -> Prop) : {{ fun s => P s s }} get {{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma undefined  (A : Type)(a : nat) (P : A -> state -> Prop) : {{ fun s => False }} undefined  a{{ P }}.
Proof.
intros s H; trivial.
Qed.

Lemma weaken (A : Type) (m : LLI A) (P Q : state -> Prop) (R : A -> state -> Prop) :
  {{ Q }} m {{ R }} -> (forall s, P s -> Q s) -> {{ P }} m {{ R }}.
Proof.
intros H1 H2 s H3.
case_eq (m s); [intros [a s'] H4 | intros a H4 ];
apply H2 in H3; apply H1 in H3; try rewrite H4 in H3; trivial.
intros. rewrite H in H3. assumption. 
Qed.
Lemma strengthen (A : Type) (m : LLI A) (P: state -> Prop) (Q R: A -> state -> Prop) :
  {{ P }} m {{ R }} -> (forall s a, R a s -> Q a s) -> {{ P }} m {{ Q }}.
Proof.
intros H1 H2 s H3.
case_eq (m s);[ intros  [a s'] H4 | intros H4];
apply H1 in H3.
 rewrite H4 in H3; apply H2 in H3;trivial.
intros. rewrite H in H3. assumption. 
Qed.


Lemma bindRev (A B : Type) (m : LLI A) (f : A -> LLI B) (P : state -> Prop)( Q : A -> state -> Prop) (R : B -> state -> Prop) :
  {{ P }} m {{ Q }} -> (forall a, {{ Q a }} f a {{ R }}) -> {{ P }} perform x := m in f x {{ R }}.
Proof.
intros; eapply bind ; eassumption.
Qed.

Lemma modify  f (P : unit -> state -> Prop) : {{ fun s => P tt (f s) }} modify f {{ P }}.
Proof.
unfold modify.
eapply bind .
intros.
eapply put .
simpl.
eapply weaken.
eapply get .
intros. simpl.
assumption.
Qed.


Lemma getCurPartition   (P: page -> state -> Prop) :
{{wp P MAL.getCurPartition}} MAL.getCurPartition {{P}}.
Proof.
apply wpIsPrecondition.
Qed.

Lemma getPDidx   (P: index -> state -> Prop) :
{{ wp P getPDidx }} getPDidx {{ P }}.
Proof.
apply wpIsPrecondition.
Qed.

Lemma getSh1idx   (P: index -> state -> Prop) :
{{ wp P getSh1idx }} getSh1idx {{ P }}.
Proof.
apply wpIsPrecondition.
Qed.
Lemma getSh2idx   (P: index -> state -> Prop) :
{{ wp P getSh2idx }} getSh2idx {{ P }}.
Proof.
apply wpIsPrecondition.
Qed.

Lemma getSh3idx   (P: index -> state -> Prop) :
{{ wp P getSh3idx }} getSh3idx {{ P }}.
Proof.
apply wpIsPrecondition.
Qed.

Lemma getPPRidx   (P: index -> state -> Prop) :
{{ wp P getPPRidx }} getPPRidx {{ P }}.
Proof.
apply wpIsPrecondition.
Qed.

Lemma getPRidx   (P: index -> state -> Prop) :
{{ wp P getPRidx }} getPRidx {{ P }}.
Proof.
apply wpIsPrecondition.
Qed.

Lemma getKidx  (P : index -> state -> Prop) : 
{{ wp P getKidx}} getKidx {{P}}.
Proof.
apply wpIsPrecondition.
Qed.

Module Index.
Lemma eqb  index1 index2 (P : bool -> state -> Prop):
{{ fun s : state => P (StateLib.Index.eqb index1 index2)  s }} 
  MALInternal.Index.eqb index1 index2 {{ fun s => P s}}.
Proof.
unfold MALInternal.Index.eqb, StateLib.Index.eqb.
eapply weaken.
eapply ret .
trivial.
Qed.

Lemma gtb  index1 index2 (P : bool -> state -> Prop):
{{ fun s : state => P (StateLib.Index.gtb index1 index2)  s }} 
  MALInternal.Index.gtb index1 index2 {{ fun s => P s}}.
Proof.
unfold MALInternal.Index.gtb, StateLib.Index.gtb.
eapply weaken.
eapply ret .
trivial.
Qed.

Lemma ltb  index1 index2 (P : bool -> state -> Prop):
{{ fun s : state => P (StateLib.Index.ltb index1 index2)  s }} 
  MALInternal.Index.ltb index1 index2 {{ fun s => P s}}.
Proof.
unfold MALInternal.Index.ltb, StateLib.Index.ltb.
eapply weaken.
eapply ret .
trivial.
Qed.

Lemma leb  index1 index2 (P : bool -> state -> Prop):
{{ fun s : state => P (StateLib.Index.leb index1 index2)  s }} 
  MALInternal.Index.leb index1 index2 {{ fun s => P s}}.
Proof.
unfold MALInternal.Index.leb, StateLib.Index.leb.
eapply weaken.
eapply ret .
trivial.
Qed.

Lemma geb  index1 index2 (P : bool -> state -> Prop):
{{ fun s : state => P (StateLib.Index.geb index1 index2)  s }} 
  MALInternal.Index.geb index1 index2 {{ fun s => P s}}.
Proof.
unfold MALInternal.Index.geb, StateLib.Index.geb.
eapply weaken.
eapply ret .
trivial.
Qed.

Lemma succ  (idx : index) (P: index -> state -> Prop) :
{{fun s => idx < (tableSize -1) /\ forall  l : idx + 1 < tableSize , 
    P {| i := idx + 1; Hi := MALInternal.Index.succ_obligation_1 idx l |} s}} MALInternal.Index.succ idx {{ P }}.
Proof.
unfold MALInternal.Index.succ.
case_eq (lt_dec (idx + 1) tableSize) .
intros. simpl.
eapply weaken.
eapply ret .
intros. intuition.
intros. eapply weaken.
eapply undefined .
simpl. intros.
destruct idx. simpl in *.
destruct H0.
destruct n. 
(* BEGIN SIMULATION
unfold tableSize in *.
   END SIMULATION *)
omega.
Qed.
End Index.

Module Level.
Lemma pred  (level1 : level) (P: level -> state -> Prop) :
{{ fun s : state => level1 > 0 /\ forall Hl : level1 - 1 < nbLevel,  
                   P {| l := level1 -1; Hl := Hl |} s }} MALInternal.Level.pred level1 {{ P }}.
Proof.
unfold MALInternal.Level.pred.
destruct level1.
simpl.
case_eq ( gt_dec l 0) .
intros.
eapply weaken.
eapply ret .
intros. intuition.
intros. eapply weaken.
eapply undefined .
simpl. intros.
omega.
Qed.

Lemma gtb  level1 level2 (P : bool -> state -> Prop):
{{ fun s : state => P (StateLib.Level.gtb level1 level2)  s }} 
  MALInternal.Level.gtb level1 level2 {{ fun s => P s}}.
Proof.
unfold MALInternal.Level.gtb, StateLib.Level.gtb.
eapply weaken.
eapply ret .
trivial.
Qed.

Lemma eqb level1 level2 (P : bool -> state -> Prop):
{{ fun s : state => P (StateLib.Level.eqb level1 level2)  s }} 
  MALInternal.Level.eqb level1 level2 {{ fun s => P s}}.
Proof.
unfold MALInternal.Level.eqb, StateLib.Level.eqb.
eapply weaken.
eapply ret .
trivial.
Qed.
End Level. 

Module Page.
Lemma eqb  page1 page2 (P : bool -> state -> Prop):
{{ fun s : state => P (StateLib.Page.eqb page1 page2)  s }} 
  MALInternal.Page.eqb page1 page2 {{ fun s => P s}}.
Proof.
unfold MALInternal.Page.eqb, StateLib.Page.eqb.
eapply weaken.
eapply ret .
trivial.
Qed.
End Page.

Module VAddr.
Lemma eqbList(vaddr1 : vaddr) (vaddr2 : vaddr) (P : bool -> state -> Prop) :
{{ fun s : state => P (StateLib.VAddr.eqbList vaddr1 vaddr2)  s }} 
  MALInternal.VAddr.eqbList vaddr1 vaddr2 {{ fun s => P s}}.
Proof.
unfold MALInternal.VAddr.eqbList, StateLib.VAddr.eqbList.
eapply weaken.
eapply ret .
trivial.
Qed.
End VAddr.

Lemma readPhyEntry  table idx  (P : page -> state -> Prop) :
{{fun  s => exists entry, lookup table idx s.(memory) beqPage beqIndex = Some (PE entry) /\ 
             P entry.(pa) s }} MAL.readPhyEntry table idx {{P}}.
Proof.
unfold readPhyEntry.
eapply bind .
  - intro s. simpl. 
    case_eq (lookup table idx s.(memory) beqPage beqIndex).
     + intros v Hpage.
        instantiate (1:= fun s s0 => s=s0 /\ exists entry ,
                   lookup table idx s.(memory) beqPage beqIndex = Some (PE entry) /\ P (entry.(pa)) s).
       simpl.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       intros s0 H0; try destruct H0 as (Hs & p1& Hpage' & Hret);
       try rewrite Hpage in Hpage';
       subst;try inversion Hpage'.
       unfold Hardware.ret.
       eassumption.  
       intuition.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0.  destruct H0 as (Hs & p1 & Hpage' & Hret) .
       rewrite Hpage in Hpage'.
       subst. inversion Hpage'.
  - eapply weaken. eapply get . intuition.  
Qed.
Lemma readVirEntry  table idx  (P : vaddr -> state -> Prop) :
{{fun  s => exists entry, lookup table idx s.(memory) beqPage beqIndex = Some ( VE entry) /\ 
             P entry.(va) s }} MAL.readVirEntry table idx {{P}}.
Proof.
unfold MAL.readVirEntry.
eapply bind .
  - intro s. simpl. 
    case_eq (lookup table idx s.(memory) beqPage beqIndex).
     + intros v Hpage.
        instantiate (1:= fun s s0 => s=s0 /\ exists entry ,
                   lookup table idx s.(memory) beqPage beqIndex = Some (VE entry) /\ P (entry.(va)) s).
       simpl.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       intros s0 H0; try destruct H0 as (Hs & p1 & Hpage' & Hret);
       try rewrite Hpage in Hpage';
       subst;try inversion Hpage'.
       unfold Hardware.ret.
       eassumption.  
       intuition.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0.  destruct H0 as (Hs & p1 & Hpage' & Hret) .
       rewrite Hpage in Hpage'.
       subst. inversion Hpage'.
  - eapply weaken. eapply get . intuition.  
Qed.

Lemma readVirtual  table idx  (P : vaddr -> state -> Prop) :
{{fun  s => exists entry : vaddr, lookup table idx s.(memory) beqPage beqIndex = Some ( VA entry) /\ 
             P entry s }} MAL.readVirtual table idx {{P}}.
Proof.
unfold readVirtual.
eapply bind .
  - intro s. simpl. 
    case_eq (lookup table idx s.(memory) beqPage beqIndex).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s=s0 /\ exists entry ,
         lookup table idx s.(memory) beqPage beqIndex = Some (VA entry) /\ P entry s).
       simpl.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       intros s0 H0; try destruct H0 as (Hs & p1 & Hpage' & Hret);
       try rewrite Hpage in Hpage';
       subst;try inversion Hpage'.
       unfold Hardware.ret.
       eassumption.  
       intuition.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0.  destruct H0 as (Hs & p1 & Hpage' & Hret) .
       rewrite Hpage in Hpage'.
       subst. inversion Hpage'.
  - eapply weaken. eapply get . intuition.  
Qed.

Lemma writePhyEntry  table idx (addr : page) (p u r w e : bool)  (P : unit -> state -> Prop) :
{{fun  s => P tt {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE {| read := r; write := w; exec := e; present := p; user := u; pa := addr |})
              (memory s) beqPage beqIndex |} }} writePhyEntry table idx addr p u r w e  {{P}}.
Proof.
unfold writePhyEntry.
eapply weaken.
eapply modify .
intros. simpl.
assumption.  
Qed.

Lemma writeVirtual  table idx (addr : vaddr)  (P : unit -> state -> Prop) :
{{fun  s => P tt {|
  currentPartition := currentPartition s;
  memory := add table idx (VA addr) (memory s) beqPage beqIndex |} }} writeVirtual table idx addr  {{P}}.
Proof.
unfold writeVirtual.
eapply weaken.
eapply modify .
intros. simpl.
assumption.  
Qed.

Lemma writeVirEntry  table idx (addr : vaddr)  (P : unit -> state -> Prop) :
{{fun  s => P tt {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := false; va := addr |} ) (memory s) beqPage beqIndex |} }} writeVirEntry table idx addr  {{P}}.
Proof.
unfold writeVirEntry.
eapply weaken.
eapply modify .
intros. simpl.
assumption.  
Qed.

Lemma writePhysical table idx (addr : page) (P : unit -> state -> Prop) :
{{fun  s => P tt {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PP addr )
              (memory s) beqPage beqIndex |} }} writePhysical table idx addr  {{P}}.
Proof.
unfold writePhysical.
eapply weaken.
eapply modify .
intros. simpl.
assumption.  
Qed.

Lemma writeIndex table idx (indexValue : index) (P : unit -> state -> Prop) :
{{fun  s => P tt {|
  currentPartition := currentPartition s;
  memory := add table idx
              (I indexValue )
              (memory s) beqPage beqIndex |} }} writeIndex table idx indexValue  {{P}}.
Proof.
unfold writeIndex.
eapply weaken.
eapply modify .
intros. simpl.
assumption.  
Qed.

Lemma writeAccessible  (table : page) (idx : index) (flag : bool)  (P : unit -> state -> Prop) :
{{fun  s => exists entry , lookup table idx s.(memory) beqPage beqIndex = Some (PE entry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add table idx
              (PE {| read := entry.(read); write :=entry.(write); exec := entry.(exec); 
                     present := entry.(present); user := flag; pa := entry.(pa) |})
              (memory s) beqPage beqIndex |} }} writeAccessible table idx flag  {{P}}.
Proof.
unfold writeAccessible.
eapply bind .
  - intro s. simpl.
   case_eq (lookup table idx s.(memory) beqPage beqIndex).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s = s0 /\ exists entry , lookup table idx s.(memory) beqPage beqIndex = Some (PE entry) /\ 
                                              P tt {| currentPartition := currentPartition s;
                                                      memory := add table idx
                                                                  (PE {| read := entry.(read); write :=entry.(write); exec := entry.(exec); 
                                                                         present := entry.(present); user := flag; pa := entry.(pa) |})
                                                                  (memory s) beqPage beqIndex |}).
       simpl in *.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       subst;
       cbn; intros;   
       try destruct H as (Hs & x & H1 & Hp); subst;
       try rewrite H1 in Hpage; inversion Hpage; subst; try assumption.
       eapply modify .
       intros.
       simpl.
       assumption.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0. destruct H0 as (Hs & x & H1 & Hp).
       rewrite H1 in Hpage.
       inversion Hpage.
  - eapply weaken. eapply get . intuition.
Qed.

Lemma readPhysical  table idx  (P : page -> state -> Prop) :
{{fun  s => exists p1, lookup table idx s.(memory) beqPage beqIndex = Some (PP p1) /\ 
             P p1 s }} MAL.readPhysical table idx {{P}}.
Proof.
unfold readPhysical.
eapply bind .
  - intro s. simpl. 
    case_eq (lookup table idx s.(memory) beqPage beqIndex).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s=s0 /\ exists p1 ,
                   lookup table idx s.(memory) beqPage beqIndex = Some (PP p1) /\ P p1 s).
       simpl.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       intros s0 H0; try destruct H0 as (Hs & p1 & Hpage' & Hret);
       try rewrite Hpage in Hpage';
       subst;try inversion Hpage'.
       unfold Hardware.ret.
       eassumption.  
       intuition.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0.  destruct H0 as (Hs & p1 & Hpage' & Hret) .
       rewrite Hpage in Hpage'.
       subst. inversion Hpage'.
  - eapply weaken. 
    eapply get . intuition.   
Qed.

Lemma readPresent  table idx (P : bool -> state -> Prop) : 
{{fun s =>  exists entry, lookup table idx s.(memory) beqPage beqIndex = Some (PE entry) /\ 
             P entry.(present) s }} MAL.readPresent table idx {{P}}.
Proof.
unfold readPresent.
eapply bind .
  - intro s. simpl. 
    case_eq (lookup table idx s.(memory) beqPage beqIndex).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s=s0 /\ exists p1 ,
                   lookup table idx s.(memory) beqPage beqIndex = Some (PE p1) /\ P (present p1) s).
       simpl.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       intros s0 H0; try destruct H0 as (Hs & p1 & Hpage' & Hret);
       try rewrite Hpage in Hpage';
       subst;try inversion Hpage'.
       unfold Hardware.ret.
       eassumption.  
       intuition.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0.  destruct H0 as (Hs & p1 & Hpage' & Hret) .
       rewrite Hpage in Hpage'.
       subst. inversion Hpage'.
  - eapply weaken.
   eapply get . intuition.
Qed.
   Lemma writePDflag  table idx  (flag: bool)  (P : unit -> state -> Prop) :
{{fun  s => exists v , lookup table idx (memory s) beqPage beqIndex = Some (VE v) /\
P tt {|
         currentPartition := currentPartition s;
         memory := add table idx (VE {| pd := flag; va := va v |}) 
                     (memory s) beqPage beqIndex |} }} writePDflag table idx flag {{P}}.
Proof.
unfold writePDflag.
eapply bindRev.
+
eapply weaken.
eapply get.
simpl.
intros.
instantiate(1:= fun s s0 =>
              s=s0 /\ exists v : Ventry,
              lookup table idx (memory s) beqPage beqIndex = Some (VE v) /\
              P tt
                {|
                currentPartition := currentPartition s;
                memory := add table idx (VE {| pd := flag; va := va v |}) 
                            (memory s) beqPage beqIndex |}).
simpl.
intuition.
+
intros s.
simpl.
case_eq (lookup table idx s.(memory) beqPage beqIndex).
- intros v Hentry.

  case_eq v; [| intros;
 simpl;
 eapply weaken;
try eapply modify ;
intros; simpl;
destruct H0 as  (Hs &ve & Htrue & Hp);
inversion Htrue;subst;
assumption | | |];
  
    intros;
    eapply weaken;
    try eapply undefined ;simpl;
    intros;simpl in *;
    intuition;
    subst;
    destruct H2 as (v &Hv & Hp);
    inversion Hv;
    intros.
 - intros;
    eapply weaken;
    try eapply undefined ;simpl;
    intros;simpl in *;
    intuition;
    subst;
    destruct H2 as (v &Hv & Hp);
    inversion Hv;
    intros.
    Qed.
    
Lemma readAccessible  table idx (P : bool -> state -> Prop) : 
{{fun s =>  exists entry, lookup table idx s.(memory) beqPage beqIndex = Some (PE entry) /\ 
             P entry.(user) s }} MAL.readAccessible table idx {{P}}.
Proof.
unfold readAccessible.
eapply bind .
  - intro s. simpl. 
    case_eq (lookup table idx s.(memory) beqPage beqIndex).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s=s0 /\ exists p1 ,
                   lookup table idx s.(memory) beqPage beqIndex = 
                   Some (PE p1) /\ P (user p1) s).
       simpl.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       intros s0 H0; try destruct H0 as (Hs & p1 & Hpage' & Hret);
       try rewrite Hpage in Hpage';
       subst;try inversion Hpage'.
       unfold Hardware.ret.
       eassumption.  
       intuition.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0.  destruct H0 as (Hs & p1 & Hpage' & Hret) .
       rewrite Hpage in Hpage'.
       subst. inversion Hpage'.
  - eapply weaken.
   eapply get . intuition.
Qed.

Lemma getNbLevel  (P : level -> state -> Prop) :
{{fun s => nbLevel > 0  /\ (forall H, P {|
           l := nbLevel -1;
           Hl := MAL.getNbLevel_obligation_1 H
           |}  s) }} 
MAL.getNbLevel 
{{P}}.
Proof.
unfold MAL.getNbLevel.
eapply weaken. 
- instantiate (1:= fun s => nbLevel > 0 /\ forall H , P {|
           l := nbLevel-1;
           Hl := MAL.getNbLevel_obligation_1 H|}  s) .
  case_eq ( gt_dec nbLevel 0).
  + intros.
    eapply weaken.
    * eapply ret .
    * intros. destruct H0.
      generalize ( H1 g).  
      intros. intuition.
  + intros. eapply weaken. eapply undefined . intros. intuition.
  - intuition.
 Qed.  

Lemma getIndexOfAddr  (va : vaddr) (level1 : level) (P: index -> state -> Prop) :
{{ fun s =>  P (nth (length va - (level1+ 2)) va defaultIndex) s }} 
   MAL.getIndexOfAddr va level1 
{{P}}.
Proof.
unfold getIndexOfAddr.
eapply weaken.
eapply ret .
intros. intuition.
Qed.

Lemma getMultiplexer  (P : page -> state -> Prop) : 
{{ wp P getMultiplexer}} getMultiplexer {{P}}.
Proof.
apply wpIsPrecondition.
Qed.

Lemma readPDflag  table idx (P : bool -> state -> Prop) : 
{{fun s =>  exists entry, lookup table idx s.(memory) beqPage beqIndex = Some (VE entry) /\ 
             P entry.(pd) s }} MAL.readPDflag table idx {{P}}.
Proof.
unfold readPDflag.
eapply bind .
  - intro s. simpl. 
    case_eq (lookup table idx s.(memory) beqPage beqIndex).
     + intros v Hpage.
       instantiate (1:= fun s s0 => s=s0 /\ exists p1 ,
                   lookup table idx s.(memory) beqPage beqIndex = 
                   Some (VE p1) /\ P (pd p1) s).
       simpl.
       case_eq v; intros; eapply weaken; try eapply undefined ;simpl;
       intros s0 H0; try destruct H0 as (Hs & p1 & Hpage' & Hret);
       try rewrite Hpage in Hpage';
       subst;try inversion Hpage'.
       unfold Hardware.ret.
       eassumption.  
       intuition.
     + intros Hpage; eapply weaken; try eapply undefined ;simpl.
       intros s0 H0.  destruct H0 as (Hs & p1 & Hpage' & Hret) .
       rewrite Hpage in Hpage'.
       subst. inversion Hpage'.
  - eapply weaken.
   eapply get . intuition.
Qed.

Lemma activate (partitionDescriptor : page) (P : unit -> state -> Prop) :
{{fun  s => P tt {|
  currentPartition := partitionDescriptor;
  memory := memory s |} }}activate partitionDescriptor {{P}}.
Proof.
unfold activate.
eapply weaken.
eapply modify .
intros. simpl.
assumption.  
Qed.