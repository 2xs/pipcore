(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2024)                *)
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
    This file contains the invariant of [writePhyEntry].
    We prove that this instruction preserves the isolation property  *)

Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib Pip.Model.MAL.
Require Import Pip.Core.Services.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.InternalLemmas
Pip.Proof.InternalLemmas2 Pip.Proof.Isolation Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Invariants Lib GetTableAddr MapMMUPage PropagatedProperties WriteAccessible .
Import Arith Bool Classical_Prop Coq.Logic.ProofIrrelevance Lia List.

 (* %%%%%%%%%%%%%%%%%%%%%%%%%%%%% InternalLemmas %%%%%%%%%%%%%%%%%%%%%%%% *)

Definition nextIndirectionsOR (indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr: page) idxroot:=
(indirection = phyPDChild /\ nextIndirection = phyMMUaddr /\ idxroot = idxPageDir) \/ 
(indirection = phySh1Child/\ nextIndirection = phySh1addr /\ idxroot = idxShadow1 ) \/ 
(indirection = phySh2Child/\ nextIndirection = phySh2addr /\ idxroot = idxShadow2).

 Lemma getIndirectionMapMMUPage11' s a (phyVaChild ptVaChildpd pd:page) e r w   entry nbL stop1 a1 (li : level):  
  (forall (stop : nat) (tbl : page) ,
        getIndirection pd a nbL stop s = Some tbl -> (pageDefault =? tbl) = false ->
        tbl <> ptVaChildpd \/  ( tbl = ptVaChildpd  /\ (StateLib.getIndexOfAddr a (CLevel (nbL-stop)) <>  StateLib.getIndexOfAddr a1 li))) ->
       lookup ptVaChildpd (StateLib.getIndexOfAddr a1 li) (memory s) pageEq idxEq = Some (PE entry) ->
       pd <> pageDefault ->
       getIndirection pd a nbL stop1 s =
       getIndirection pd a nbL stop1
         {|
         currentPartition := currentPartition s;
         memory := add ptVaChildpd  (StateLib.getIndexOfAddr a1 li)
                     (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyVaChild |})
                     (memory s) pageEq idxEq |}.
                     Proof.

                     
   revert pd nbL li ptVaChildpd entry.
   induction stop1.
   simpl;trivial.
   intros *  Hmykey  Hlookup Hpdnotnull.
   set(s':= {|
  currentPartition := _|}).
   simpl in *.

    case_eq( levelEq nbL levelMin);intros;trivial.
    assert(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a nbL)
    (add ptVaChildpd  (StateLib.getIndexOfAddr a1 li)
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) pageEq idxEq) =
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a nbL)
    (memory s)). symmetry.
    apply readPhyEntryMapMMUPage with entry;trivial.
    generalize (Hmykey 0 pd );clear Hmykey;intros Hmykey.
    simpl in *.
    assert(Hx: pd <> ptVaChildpd \/
         pd = ptVaChildpd /\ StateLib.getIndexOfAddr a  (CLevel (nbL - 0)) <> StateLib.getIndexOfAddr a1 li).
         
         apply Hmykey;trivial.
    apply NPeano.Nat.eqb_neq.
    unfold not;intros.
    subst.
    destruct pageDefault;destruct pd;simpl in *;subst.
    contradict Hpdnotnull.
    f_equal. apply  proof_irrelevance.
    destruct Hx.
    left;trivial.
    right.

rewrite CLevelIdentity'  in H0.
intuition.
    rewrite H0.
    case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a nbL) (memory s));intros;trivial.
    case_eq(pageDefault =? p);intros;trivial.
    case_eq(StateLib.Level.pred nbL );intros;trivial.
    apply IHstop1 with entry;trivial.
    intros.
    assert(tbl <> ptVaChildpd \/
         tbl = ptVaChildpd /\
         StateLib.getIndexOfAddr a (CLevel (nbL - (S stop))) <>
         StateLib.getIndexOfAddr a1 li) as Hgen.
         
    apply Hmykey .
    simpl.    
     
     rewrite H3 in *.
     rewrite H.
     rewrite H1.
     rewrite H2;trivial.
     trivial.
 replace (nbL - S stop) with (l - stop) in *.
 destruct Hgen.
 left;trivial.
 right.
 intuition.
 assert(l = CLevel (nbL - 1)).
 apply levelPredMinus1;trivial.
 rewrite H6.
unfold CLevel .
case_eq( lt_dec (nbL - 1) nbLevel);intros * Hl;simpl.
lia.
destruct nbL. simpl in *. lia.  apply beq_nat_false in H2.
     unfold not;intros.
     subst.
 now contradict H2.
Qed.



 Lemma getIndirectionMapMMUPage11xx s a (phyVaChild ptVaChildpd pd:page) e r w   entry nbL stop1 a1 (li : level):  
let s':= {|
         currentPartition := currentPartition s;
         memory := add ptVaChildpd  (StateLib.getIndexOfAddr a1 li)
                     (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyVaChild |})
                     (memory s) pageEq idxEq |} in 
  (forall (stop : nat) (tbl : page) ,
        getIndirection pd a nbL stop s' = Some tbl -> (pageDefault =? tbl) = false ->
        tbl <> ptVaChildpd \/  ( tbl = ptVaChildpd  /\ (StateLib.getIndexOfAddr a (CLevel (nbL-stop)) <>  StateLib.getIndexOfAddr a1 li))) ->
       lookup ptVaChildpd (StateLib.getIndexOfAddr a1 li) (memory s) pageEq idxEq = Some (PE entry) ->
       pd <> pageDefault ->
       getIndirection pd a nbL stop1 s =
       getIndirection pd a nbL stop1 s'.
                     Proof.

                     
   revert pd nbL li ptVaChildpd entry.
   induction stop1.
   simpl;trivial.
   intros *  Hmykey  Hlookup Hpdnotnull.
   simpl in *.

    case_eq( levelEq nbL levelMin);intros;trivial.
    assert(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a nbL)
    (add ptVaChildpd  (StateLib.getIndexOfAddr a1 li)
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) pageEq idxEq) =
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a nbL)
    (memory s)). symmetry.
    apply readPhyEntryMapMMUPage with entry;trivial.
    generalize (Hmykey 0 pd );clear Hmykey;intros Hmykey.
    simpl in *.
    assert(Hx: pd <> ptVaChildpd \/
         pd = ptVaChildpd /\ StateLib.getIndexOfAddr a  (CLevel (nbL - 0)) <> StateLib.getIndexOfAddr a1 li).
         
         apply Hmykey;trivial.
    apply NPeano.Nat.eqb_neq.
    unfold not;intros.
    subst.
    destruct pageDefault;destruct pd;simpl in *;subst.
    contradict Hpdnotnull.
    f_equal. apply  proof_irrelevance.
    destruct Hx.
    left;trivial.
    right.

rewrite CLevelIdentity'  in H0.
intuition.
    rewrite H0.
    case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a nbL) (memory s));intros;trivial.
    case_eq(pageDefault =? p);intros;trivial.
    case_eq(StateLib.Level.pred nbL );intros;trivial.
    apply IHstop1 with entry;trivial.
    intros.
    assert(tbl <> ptVaChildpd \/
         tbl = ptVaChildpd /\
         StateLib.getIndexOfAddr a (CLevel (nbL - (S stop))) <>
         StateLib.getIndexOfAddr a1 li) as Hgen.
         
    apply Hmykey .
    simpl.    
     
     rewrite H3 in *.
     rewrite H.
     rewrite H0.
     rewrite H1.
     rewrite H2;trivial.
     trivial.
 replace (nbL - S stop) with (l - stop) in *.
 destruct Hgen.
 left;trivial.
 right.
 intuition.
 assert(l = CLevel (nbL - 1)).
 apply levelPredMinus1;trivial.
 rewrite H6.
unfold CLevel .
case_eq( lt_dec (nbL - 1) nbLevel);intros * Hl;simpl.
lia.
destruct nbL. simpl in *. lia.  apply beq_nat_false in H2.
     unfold not;intros.
     subst.
 now contradict H2.
Qed.

     Set Nested Proofs Allowed.
     Lemma getIndirectionAddIndirectionEq stop :
      forall s pd  indirection phyMMUaddr e w r  va entry idx level,
     lookup indirection idx
            (memory s) pageEq idxEq = Some (PE entry) ->
     ~ In indirection (getIndirectionsAux pd s stop) -> 
     getIndirection pd va level stop {|
      currentPartition := currentPartition s;
      memory := add indirection idx
                  (PE
                     {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |})
                  (memory s) pageEq idxEq |} =getIndirection pd va level stop s.
     Proof.
     induction stop;simpl.
     intros;trivial.
     intros * Hlook HI.
     apply not_or_and in HI.
     destruct HI as (Hi1 & Hi2).
     case_eq(levelEq level levelMin);intros * Hisfst;trivial.
     assert(HreadEq:  StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va level)
    (add indirection idx
       (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyMMUaddr |})
       (memory s) pageEq idxEq) = StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va level) (memory s) ). 
       { symmetry. apply readPhyEntryMapMMUPage with entry;trivial.
          left;trivial. }
          rewrite HreadEq.
          clear HreadEq.
     case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va level) (memory s));intros * Hread;
     trivial.
     case_eq( pageDefault =? p);intros * Hdef;trivial.
     case_eq(StateLib.Level.pred level );intros * Hpred;trivial.
     rewrite in_flat_map in Hi2.
     
     apply IHstop with entry;trivial.
     contradict Hi2.
     exists p;split;trivial.
     apply readPhyEntryInGetTablePages with (StateLib.getIndexOfAddr va level) ;trivial.
     destruct(StateLib.getIndexOfAddr va level);simpl;lia.
     apply beq_nat_false in Hdef.
     unfold not;intros;subst; now contradict Hdef.
     rewrite <- Hread.
     f_equal.
     apply indexEqId.
     Qed.

Lemma  readPhyEntryAddIndirectionSameTable indirection idx pg r w e p s:
StateLib.readPhyEntry indirection idx
(add indirection idx
(PE {| read := r; write := w; exec := e; present := p; user := true; pa := pg |})
(memory s) pageEq idxEq) = Some pg.
Proof.
unfold  StateLib.readPhyEntry.
simpl.
assert(Hpairs: beqPairs (indirection, idx) (indirection, idx) pageEq idxEq = true).
apply beqPairsTrue;split;trivial.
rewrite Hpairs;simpl;trivial.
Qed.

Lemma  isWellFormedMMUTablesAddIndirection nextIndirection indirection idx entry s r w e:
lookup indirection idx
      (memory s) pageEq idxEq = Some (PE entry) ->
nextIndirection <> indirection ->
isWellFormedMMUTables nextIndirection s ->
isWellFormedMMUTables nextIndirection {|
currentPartition := currentPartition s;
memory := add indirection idx
            (PE
               {|
               read := r;
               write := w;
               exec := e;
               present := true;
               user := true;
               pa := nextIndirection |}) (memory s) pageEq idxEq |}.
Proof.
intros Hlookup Hdef Hwell.
unfold isWellFormedMMUTables in *.
simpl.
intros.
generalize (Hwell idx0 ); clear Hwell ; intros (Hi1 & Hi2).
rewrite <- Hi1.
rewrite <- Hi2.
split.
symmetry.
apply readPhyEntryMapMMUPage with entry;trivial.
left;intuition.
symmetry.
apply readPresentMapMMUPage with entry;trivial.
intuition.
Qed.

Lemma isWellFormedFstShadowTablesAddIndirection nextIndirection indirection  entry  vaToPrepare l lpred s e w r:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l)
      (memory s) pageEq idxEq = Some (PE entry) ->
nextIndirection <> indirection -> 
isWellFormedFstShadow lpred nextIndirection s ->
isWellFormedFstShadow lpred nextIndirection 
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |}) 
              (memory s) pageEq idxEq |}.
Proof.
intros Hlookup Hdef Hwell.
unfold isWellFormedFstShadow in *.
simpl.
intros.
destruct Hwell as [(Hl & Hwell)|(Hl & Hwell)];intros.
+ left.
split;trivial.
intros.
generalize (Hwell idx ); clear Hwell ; intros (Hi1 & Hi2).
rewrite <- Hi1.
rewrite <- Hi2.
split.
symmetry.
apply readPhyEntryMapMMUPage with entry;trivial.
left;intuition.
symmetry.
apply readPresentMapMMUPage with entry;trivial.
intuition.
+ right.

split;trivial.
intros.
generalize (Hwell idx ); clear Hwell ; intros (Hi1 & Hi2).
rewrite <- Hi1.
rewrite <- Hi2.
split.
symmetry.
apply readVirEntryMapMMUPage  with entry;trivial.
apply readPDflagMapMMUPage with entry;trivial.
Qed.

Lemma isWellFormedSndShadowTablesAddIndirection nextIndirection indirection  entry  vaToPrepare l lpred s e w r:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l)
      (memory s) pageEq idxEq = Some (PE entry) ->
nextIndirection <> indirection -> 
isWellFormedSndShadow lpred nextIndirection s ->
isWellFormedSndShadow lpred nextIndirection 
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |}) 
              (memory s) pageEq idxEq |}.
Proof.
intros Hlookup Hdef Hwell.
unfold isWellFormedSndShadow in *.
simpl.
intros.
destruct Hwell as [(Hl & Hwell)|(Hl & Hwell)];intros.
+ left.
split;trivial.
intros.
generalize (Hwell idx ); clear Hwell ; intros (Hi1 & Hi2).
rewrite <- Hi1.
rewrite <- Hi2.
split.
symmetry.
apply readPhyEntryMapMMUPage with entry;trivial.
left;intuition.
symmetry.
apply readPresentMapMMUPage with entry;trivial.
intuition.
+ right.

split;trivial.
intros.
generalize (Hwell idx ); clear Hwell ; intros Hi1.
rewrite <- Hi1.
apply readVirtualMapMMUPage with entry;trivial.
Qed.

Lemma getIndirectionAddIndirectionCheckVaddrsFalse  vapg l indirection vaToPrepare nextIndirection p pg  entry partition  s r e  w:
let s' := {|
      currentPartition := currentPartition s;
      memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := nextIndirection |}) (memory s) pageEq idxEq |} in
 
 getIndirection indirection vapg l (nbLevel - 1) s' = Some p ->
 (pageDefault =? p) = false ->
 Some l = StateLib.getNbLevel ->
 false = levelEq l levelMin ->

lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq =
          Some (PE entry) ->
nextEntryIsPP partition idxPageDir indirection s ->
indirection <> pageDefault ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
(pageDefault =? nextIndirection) = false ->
 isWellFormedMMUTables nextIndirection s ->
 nextIndirection <> indirection ->
pg <> pageDefault ->
noDupConfigPagesList s ->
StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s') = Some true ->
StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s') = Some pg  ->


partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
               
 getIndirection indirection vapg l (nbLevel - 1) s =
 getIndirection indirection vapg l (nbLevel - 1)  s'.
Proof.
intros s' Hindx' Hnotdefp Hl Hlevel  Hlookup Hpp Hrootnotdef Hdef (* Hdef' *)
Hnextnotdef Hinit Hnextnoteq HHkey Hnodupcons Hpres Hread .
intros.
rewrite Hindx'.
assert(Hnodup : NoDup (getIndirections indirection s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition idxPageDir ;trivial.
apply Hnodupcons;trivial.
left;trivial. }
assert(Hlvl: nbLevel - 1  = l).
{ apply getNbLevelEq in Hl.
  subst.
  rewrite <- nbLevelEq;trivial. }
assert(Hnotfstl: l > 0) by (apply levelEqBEqNatFalse0;symmetry;trivial).
assert(HnbLgt: (nbLevel-1) > 0) by lia.
assert(Htruenbl:  (nbLevel - 1) <= l) by lia.
destruct (nbLevel - 1);simpl in *;trivial.
rewrite <- Hlevel in *.
assert( (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vapg l) \/
(StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vapg l))as [Hvadsl|Hvadsl] by apply indexDecOrNot.
+ case_eq( StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin)
            (add indirection (StateLib.getIndexOfAddr vaToPrepare l)
               (PE
                  {|
                  read := r;
                  write := w;
                  exec := e;
                  present := true;
                  user := true;
                  pa := nextIndirection |}) (memory s) pageEq idxEq));intros * Hxx;rewrite Hxx in *;try now contradict Hvapg.
        assert(Hreads:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vapg l)
               (memory s) = Some pageDefault).
        {  
        rewrite <- Hvadsl.
        trivial. }
        rewrite Hreads in *.
        assert(Hreads': StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vapg l)
             (add indirection (StateLib.getIndexOfAddr vapg l)
                (PE
                   {|
                   read := r;
                   write := w;
                   exec := e;
                   present := true;
                   user := true;
                   pa := nextIndirection |}) (memory s) pageEq idxEq) = Some nextIndirection).
        apply readPhyEntryAddIndirectionSameTable.
        rewrite Hvadsl in *.
        rewrite Hreads' in *.
        rewrite Hnextnotdef in *.
       (*  rewrite <- Hindx'. *)
        rewrite <- beq_nat_refl .        
        case_eq(StateLib.Level.pred l);intros * Hpred;rewrite Hpred in *.
       
       
       
       
         assert(Hs0: n=0 \/ n >0) by lia.
        destruct Hs0.
        subst;simpl in *.
        inversion Hindx'.
        subst p.
        case_eq(b);intros * Hb;rewrite Hb in *;try now contradict Hvapg. (*
       
        move Hvapg at bottom. *)
        assert(Hkey : StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vapg levelMin)
            (add indirection (StateLib.getIndexOfAddr vapg l)
               (PE
                  {|
                  read := r;
                  write := w;
                  exec := e;
                  present := true;
                  user := true;
                  pa := nextIndirection |}) (memory s) pageEq idxEq) = Some pageDefault).
          { assert(Hwell':  isWellFormedMMUTables nextIndirection s').
          apply isWellFormedMMUTablesAddIndirection with entry;trivial.
          rewrite Hvadsl;trivial.
          unfold isWellFormedMMUTables in Hwell'.
          generalize (Hwell' (StateLib.getIndexOfAddr vapg levelMin) ) ; clear Hwell'; intros (Hwell'1 & Hwell'2) .
          simpl in *.
          rewrite <- Hvadsl.
          trivial. }
          rewrite Hkey in Hread.
          inversion Hread.
          subst.
          now contradict HHkey.
          now contradict Hpres.
         
          destruct n;simpl in *;try lia.
          case_eq(levelEq l0 levelMin);intros * Hpredl0;rewrite Hpredl0 in *.
           case_eq(b);intros * Hb;rewrite Hb in *;try now contradict Hvapg.
        inversion Hindx';subst p.
        assert(Hkey : StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vapg levelMin)
            (add indirection (StateLib.getIndexOfAddr vapg l)
               (PE
                  {|
                  read := r;
                  write := w;
                  exec := e;
                  present := true;
                  user := true;
                  pa := nextIndirection |}) (memory s) pageEq idxEq) = Some pageDefault).
          assert(Hwell':  isWellFormedMMUTables nextIndirection s').
          apply isWellFormedMMUTablesAddIndirection with entry;trivial.
          rewrite Hvadsl;trivial.
          unfold isWellFormedMMUTables in Hwell'.
          generalize (Hwell' (StateLib.getIndexOfAddr vapg levelMin) ) ; clear Hwell'; intros (Hwell'1 & Hwell'2) .
          simpl in *.
          rewrite Hvadsl in *.
          trivial.
          rewrite Hkey in Hread.
          inversion Hread.
          subst.
          now contradict HHkey.
          now contradict Hpres.
         
         
         
              case_eq(b);intros * Hb;rewrite Hb in *;try now contradict Hvapg.

        assert(Hkey : StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vapg l0)
             (add indirection (StateLib.getIndexOfAddr vaToPrepare l)
                (PE
                   {|
                   read := r;
                   write := w;
                   exec := e;
                   present := true;
                   user := true;
                   pa := nextIndirection |}) (memory s) pageEq idxEq) = Some pageDefault).
          assert(Hwell':  isWellFormedMMUTables nextIndirection s').
          apply isWellFormedMMUTablesAddIndirection with entry;trivial.
          rewrite Hvadsl;trivial.
          unfold isWellFormedMMUTables in Hwell'.
          generalize (Hwell' (StateLib.getIndexOfAddr vapg l0) ) ; clear Hwell'; intros (Hwell'1 & Hwell'2) .
          simpl in *.
          rewrite Hvadsl in *.
          trivial.
          rewrite Hkey in Hindx'.
          assert(Htruedef: (pageDefault =? pageDefault) = true).
          symmetry. apply beq_nat_refl.
          rewrite Htruedef in *.
          inversion Hindx';subst.
          trivial.
          now contradict Hindx'.
                    now contradict Hindx'.
                              now contradict Hpres.
          +
   
  assert(Hreads:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vapg l) (memory s)  =
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vapg l)
             (add indirection (StateLib.getIndexOfAddr vaToPrepare l)
                (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
                (memory s) pageEq idxEq)).
  {              apply readPhyEntryMapMMUPage with entry;trivial.
                right;intuition. }
                rewrite <- Hreads in *. clear Hreads.
   case_eq(StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vapg l) (memory s));intros * Hreadss;rewrite Hreadss in *
   ;try now contradict Hindx'.
   case_eq(pageDefault =? p0);intros * Hdef2;rewrite Hdef2 in *;trivial.
   case_eq(StateLib.Level.pred l );intros * Hpred;rewrite Hpred in *;try now contradict Hindx'.
   rewrite <- Hindx'.
 apply  getIndirectionMapMMUPage11 with entry;trivial.
      intros * Hi1 Hi2.
     
     assert(Horstop : S(stop+1) <= nbLevel \/ S(stop+1) > nbLevel) by lia.
      destruct Horstop as [Horstop|Horstop].
      -
        assert(Hin:  In indirection (getIndirectionsAux indirection s (stop+1) )).
      { replace (stop+1) with (S stop) by lia.
      simpl. left;trivial. }
      assert(~ In tbl (getIndirectionsAux indirection s (stop+1) )).
     
      { apply getIndirectionInGetIndirections2' with vapg l;trivial. lia.
      replace (stop+1) with (S stop) by lia.
      simpl.
      rewrite <- Hlevel
      .
      rewrite Hreadss.
      rewrite Hdef2.
      rewrite Hpred;trivial.
      apply noDupPreviousMMULevels with nbLevel;trivial.

     
      lia.
     
      apply beq_nat_falseNot;trivial.
           assert(Hlvlx: nbLevel - 1  = l).
       
      {
apply getNbLevelEq in Hl.
subst.
rewrite <- nbLevelEq;trivial. }
      lia.
      lia. }
     
      unfold not;intros;subst; now contradict Hin.

      - assert( getIndirection p0 vapg l0 (nbLevel -1 -1) s = Some tbl).
      assert(Hlvlx: nbLevel - 1  = l).
       
      {
apply getNbLevelEq in Hl.
subst.
rewrite <- nbLevelEq;trivial. }
pose proof Hpred as Hpred'.
apply levelPredMinus1 in Hpred. (*
unfold CLevel in Hpred.
case_eq(lt_dec (l - 1) nbLevel);intros * Hll;rewrite Hll in *.
simpl in *.
destruct l0.
inversion Hpred.
subst.
simpl in *.
subst.
rewrite Hpred.  *)
      apply getIndirectionStopLevelGT2 with (stop);trivial.
      unfold CLevel in Hpred.
case_eq(lt_dec (l - 1) nbLevel);intros * Hll;rewrite Hll in *.
subst.
simpl in *.
lia.
lia.

      unfold CLevel in Hpred.
case_eq(lt_dec (l - 1) nbLevel);intros * Hll;rewrite Hll in *.
subst.
simpl in *.
lia.
lia.
symmetry;trivial.

 assert(Hll: l = CLevel (nbLevel - 1)).
apply getNbLevelEq;trivial.
pose proof nbLevelEq as Heq.
rewrite <- Hll in Heq.
assert(Ll: l> 0).
apply levelEqBEqNatFalse0;trivial.
      symmetry;trivial.
              assert(Hin:  In indirection (getIndirectionsAux indirection s (nbLevel-1) )).
      { destruct (nbLevel-1);simpl.
subst;lia. left;trivial.  }

 assert(~ In tbl (getIndirectionsAux indirection s (nbLevel-1) )).
     
      { pose proof nbLevelNotZero.
       apply getIndirectionInGetIndirections2' with vapg l;trivial.
        lia.
     

destruct (nbLevel-1);simpl.
subst;lia.
rewrite <- Hlevel.
rewrite Hreadss.
rewrite Hdef2.
rewrite Hpred.
 
      replace (S n0 - 1) with n0 in * by lia.
      trivial.
     
unfold getIndirections in *.
replace  (nbLevel - 1 + 1) with nbLevel by lia.
trivial.
assert(Htruex:  (pageDefault =? tbl) = false) by trivial.
apply beq_nat_false in Htruex.
unfold not;intros;subst;try now contradict Htruex.
     
      lia. lia. }
      unfold not;intros ;subst;now contradict Hin.
            - apply beq_nat_false in Hdef2.
unfold not;intros;subst;try now contradict Hdef2.
Qed.



Lemma getMappedPageSomeAddIndirectionSamePartSSI1 s (indirection nextIndirection :page) vaToPrepare entry  vavalue pd pg partition l
 r w e:
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
nextEntryIsPP partition idxPageDir pd s ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
(pageDefault =? nextIndirection) = false ->
indirectionDescription s partition indirection idxPageDir vaToPrepare l ->
getMappedPage pd s vavalue = SomePage pg ->
false = levelEq l levelMin ->
 getMappedPage pd  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |} vavalue = SomePage pg.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hpde Hpart Hnodupcons Hprescons Hconfigdiff Hlookup Hpd Hcurind Hdefcurind (* Hdefnextind *) Hindfromroot Hmap Hfstl.
unfold getMappedPage, indirectionDescription in *.
destruct Hindfromroot as (root & Hpdroot & Hrootdef & Hrem).
assert(Hnodup : NoDup (getIndirections root s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition idxPageDir ;trivial.
apply Hnodupcons;trivial.
left;trivial. }
assert(root = pd).
apply getPdNextEntryIsPPEq with partition s;trivial.
apply nextEntryIsPPgetPd;trivial.
subst.
destruct Hrem as [(Heq & HnbL) | (nbL & stop & HnbL & Hstop & Hindi & Hnotdef & Hstopl)].
+ subst indirection;rewrite <- HnbL in *.
  assert(Hvaddr: StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vavalue l = true \/
  StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vavalue l = false)
  by (destruct (StateLib.checkVAddrsEqualityWOOffset);[left|right];trivial).
  destruct Hvaddr as [Hvaddr|Hvaddr].
  - case_eq(getIndirection pd vavalue l (nbLevel - 1) s );[intros tbl Htbl |intros Htbl]; rewrite Htbl in *;try now contradict Hmap. (** ici il faut montrer que indMMUToPrepare = tbl**)
    case_eq(pageDefault =? tbl);intros Hinddef;rewrite Hinddef in *; try now contradict Hmap.
    assert(Hind :  getIndirection pd vaToPrepare l (nbLevel - 1) s = Some pageDefault).
    { apply getIndirectionNbLevelEq with 1; try lia.
      apply getNbLevelEq in HnbL.
      subst.
      apply nbLevelEq.
      symmetry in Hfstl.
      apply levelEqBEqNatFalse0 in Hfstl.
      lia.
      simpl.
      rewrite <- Hfstl.
      assert(Hkey2: StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vaToPrepare l) (memory s)  = Some pageDefault).
      { trivial. }
      rewrite Hkey2.
      rewrite <- beq_nat_refl;trivial. }
      assert(Htrue : getIndirection pd vavalue l (nbLevel - 1) s =
      getIndirection pd vaToPrepare l (nbLevel - 1) s).
      symmetry.
      apply getIndirectionEq;trivial.
      destruct l;simpl;lia.
      rewrite Hind in Htrue.
      rewrite Htbl in Htrue.
      inversion Htrue.
      subst.
      apply beq_nat_false in Hinddef.
      lia.
 - assert(Hidxeq: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vavalue l) \/
 (StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vavalue l)) by apply indexDecOrNot.
  destruct Hidxeq as [Hidxeq |Hidxeq].
  * rewrite  Hidxeq in Hcurind.
    assert(Hind :  getIndirection pd vavalue l (nbLevel - 1) s = Some pageDefault).
    { apply getIndirectionNbLevelEq with 1; try lia.
      apply getNbLevelEq in HnbL.
      subst.
      apply nbLevelEq.
      symmetry in Hfstl.
      apply levelEqBEqNatFalse0 in Hfstl.
      lia.
      simpl.
      rewrite <- Hfstl.
      assert(Hkey2: StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l) (memory s)  = Some pageDefault).
      { trivial. }
      rewrite Hkey2.
     
      rewrite <- beq_nat_refl;trivial. }
    rewrite Hind in Hmap.
    assert(Htrue : (pageDefault =? pageDefault )=true).
    symmetry. apply beq_nat_refl.
    rewrite Htrue in *.
    now contradict Hmap.
  * assert (getIndirection pd vavalue l (nbLevel - 1) s = getIndirection pd vavalue l (nbLevel - 1) s').
  { clear Hmap.  
 destruct (nbLevel - 1); simpl. trivial.
 case_eq (levelEq l levelMin); intros * Hflst;trivial.

  assert(Hread: StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l)
    (add pd (StateLib.getIndexOfAddr vaToPrepare l)
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := nextIndirection |}) (memory s) pageEq idxEq) =StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l) (memory s)).
   {       symmetry. apply readPhyEntryMapMMUPage with entry;trivial.
          right;trivial.
          intuition. }
   rewrite Hread.
   case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l) (memory s));intros;trivial.        
   case_eq(pageDefault =? p);intros notdef;trivial.
   case_eq ( StateLib.Level.pred l);intros * Hlpred;trivial.  
  apply getIndirectionMapMMUPage11 with entry;trivial.
  intros.
 {
  pose proof indirectionNotInPreviousMMULevelAux.
  assert(Hor: stop < l \/ stop >= l) by lia.
  destruct Hor as [Hor | Hor].
 
*
  generalize(H2 vavalue s (S stop) pd l tbl);clear H2;intros H2.
  replace (S stop - 1) with stop in * by lia.
 
  assert(Hprevious: exists prevtab : page,
       getIndirection pd vavalue l stop s = Some prevtab /\
       prevtab <> pageDefault /\
       StateLib.readPhyEntry prevtab (StateLib.getIndexOfAddr vavalue (CLevel (l - stop))) (memory s) = Some tbl).
 { apply H2;clear H2;try lia.
 intuition.
  simpl.
  rewrite <- Hfstl.
  rewrite H.
  rewrite notdef.
  rewrite Hlpred;trivial.
  trivial. }
  destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev).
assert(~ In tbl (getIndirectionsAux pd s (stop + 1))).
{ apply getIndirectionInGetIndirections2 with prevtab vavalue l;
simpl; subst;
trivial.
destruct l;simpl in *.
lia.
replace(stop + 1 - 1) with stop in * by lia.
trivial.
replace(stop + 1 - 1) with stop in * by lia.
trivial.

unfold getIndirections in Hnodup.
apply noDupPreviousMMULevels with nbLevel.
trivial.
destruct l.
simpl in *.
lia.
assert((pageDefault =? tbl) = false) as Hnotdef  by trivial.
apply beq_nat_false in Hnotdef.
unfold not;intros;subst.
now contradict Hnotdef.
destruct l.
simpl in *.
lia.
}
assert( In pd (getIndirectionsAux pd s (stop + 1))).
{ replace  (stop + 1) with (S stop) by lia.
  simpl.
  left;trivial. }
unfold not;intros.
subst.
now contradict H4.
* assert(getIndirection p vavalue l0 (nbLevel -2) s = Some tbl ).
unfold StateLib.Level.pred in *.
case_eq( gt_dec l 0);intros * Hl0;rewrite Hl0 in *; try now contradict Hlpred.
inversion Hlpred.
apply getIndirectionStopLevelGT2 with stop;simpl in *;
subst;trivial.
lia.
assert(Hl: l = CLevel (nbLevel - 1)).
apply getNbLevelEq;trivial.
pose proof nbLevelEq as Heq.
rewrite <- Hl in Heq.
rewrite <- Heq.
lia.
  generalize(H2 vavalue s (nbLevel - 1) pd l tbl);clear H2;intros H2.
(*   replace (S stop - 1) with stop in * by lia.
   *)
   assert(Hl: l = CLevel (nbLevel - 1)).
apply getNbLevelEq;trivial.
pose proof nbLevelEq as Heq.
rewrite <- Hl in Heq.

pose proof nbLevelNotZero as nblnot0.
assert(l > 0).
apply levelEqBEqNatFalse0;trivial.
  assert(Hprevious: exists prevtab : page,
       getIndirection pd vavalue l (nbLevel - 1 -1) s = Some prevtab /\
       prevtab <> pageDefault /\
       StateLib.readPhyEntry prevtab (StateLib.getIndexOfAddr vavalue (CLevel (l - (nbLevel - 1 - 1)))) (memory s) = Some tbl).
 { apply H2;clear H2;try lia.
intuition.



replace (nbLevel - 1) with (nbLevel - 2 + 1) by lia.
clear H0.

replace (nbLevel - 2 + 1) with (S (nbLevel - 2)) by lia.
simpl.
rewrite <- Hfstl.
rewrite H.
rewrite notdef.
rewrite Hlpred;trivial.
trivial. }

 destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev).
assert(~ In tbl (getIndirectionsAux pd s ((nbLevel - 2) + 1))).
{ apply getIndirectionInGetIndirections2 with prevtab vavalue l;
simpl; subst;
trivial.

replace (nbLevel - 1) with (nbLevel - 2 + 1) by lia.
clear H0.

lia.
replace(nbLevel - 2 + 1 - 1) with  (nbLevel - 1 - 1) in * by lia.
trivial.

replace(nbLevel - 2 + 1 - 1) with  (nbLevel - 1 - 1) in * by lia.
trivial.
replace(nbLevel - 2 + 1 + 1) with  (nbLevel )  by lia.
unfold getIndirections in Hnodup.
trivial.
assert((pageDefault =? tbl) = false) as Hnotdef  by trivial.
apply beq_nat_false in Hnotdef.
unfold not;intros;subst.
now contradict Hnotdef.
replace(nbLevel - 2 + 1) with  (nbLevel - 1 ) in * by lia.
lia.
}
assert( In pd (getIndirectionsAux pd s (nbLevel - 2 + 1))) .
{ replace (nbLevel - 2 + 1) with (S(nbLevel -2)) by lia.
  simpl.
  left;trivial. }
unfold not;intros.
subst.
now contradict H4. }
*



   apply beq_nat_false in notdef.
   intuition.
   subst. now contradict notdef.
   }
   rewrite <- H.
    case_eq( getIndirection pd vavalue l (nbLevel - 1) s);intros * Htbl;trivial;rewrite Htbl in *.
case_eq( pageDefault =? p); intros * Hp;rewrite Hp in *;trivial.
assert( pd<>p).
 assert(Hl: l = CLevel (nbLevel - 1)).
apply getNbLevelEq;trivial.
pose proof nbLevelEq as Heq.
rewrite <- Hl in Heq.
assert(Ll: l> 0).
apply levelEqBEqNatFalse0;trivial.

symmetry;trivial.

assert(Hin:~ In p (getIndirectionsAux pd s (nbLevel - 1))).



 apply indirectionNotInPreviousMMULevel' with (StateLib.getIndexOfAddr vavalue levelMin)
 
 vavalue partition l idxPageDir ;trivial.
 left;trivial.
 symmetry;trivial.
 subst;trivial.
 rewrite Heq;trivial.


 
 assert( In pd (getIndirectionsAux pd s (nbLevel - 1))) .
 
 subst.
 destruct (nbLevel - 1);simpl.
 subst.
 lia.
 left;trivial.
 

unfold not;intros.
subst.
now contradict Hin.
assert(StateLib.readPresent p (StateLib.getIndexOfAddr vavalue levelMin) (memory s') =
StateLib.readPresent p (StateLib.getIndexOfAddr vavalue levelMin) (memory s)).
symmetry.
apply readPresentMapMMUPage with entry;trivial.
left;intuition.
rewrite H1.

assert(Hread: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue levelMin) (memory s)
= StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue levelMin) (memory s')).
apply readPhyEntryMapMMUPage with entry;trivial.
left;trivial.
intuition.
rewrite <- Hread.
trivial.

trivial.
+ rewrite <- HnbL in *.
assert (Hstp: stop + 1 <= nbL).
{ subst. assert((nbL - stop) > 0).
symmetry in Hfstl.
apply levelEqBEqNatFalse0 in Hfstl ;trivial.
unfold CLevel in Hfstl.
case_eq(lt_dec (nbL - stop) nbLevel);intros * Hlt;rewrite Hlt in *.
simpl in *;trivial.
destruct nbL;simpl in *.
lia.

lia. }
 assert(Hvaddr: StateLib.checkVAddrsEqualityWOOffset (stop+1) vaToPrepare vavalue nbL = true \/
  StateLib.checkVAddrsEqualityWOOffset (stop+1) vaToPrepare vavalue nbL = false)
  by (destruct (StateLib.checkVAddrsEqualityWOOffset);[left|right];trivial).
  destruct Hvaddr as [Hvaddr|Hvaddr].
  -
assert(Hinstop1: getIndirection pd vaToPrepare nbL (stop+1) s = Some pageDefault).
{  
   (** ici il faut montrer que indMMUToPrepare = tbl**)
pose proof getIndirectionEqStop as Hindeq.
assert( getIndirection pd vavalue nbL stop s = Some indirection).
rewrite <- Hindi.
symmetry.
apply Hindeq;trivial.
subst.
apply checkVAddrsEqualityWOOffsetTrueLe with (stop+1);trivial.
  lia.
apply getIndirectionProp' with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indirection entry;
subst;trivial.
symmetry;trivial.
unfold isEntryPage,  StateLib.readPhyEntry in *.
rewrite Hlookup in *.
inversion Hcurind ;subst;trivial.

}
assert(HindeqStop: getIndirection pd vaToPrepare nbL (stop + 1) s=
getIndirection pd vavalue nbL (stop + 1) s).

apply getIndirectionEqStop;subst;trivial.
(* apply beq_nat_true in Hdefcurind. *)
rewrite HindeqStop in Hinstop1.
assert(Hdef: getIndirection pd vavalue nbL (nbLevel - 1) s = Some pageDefault).
{ apply getIndirectionNbLevelEq with (stop+1);trivial.
  lia.
  apply getNbLevelEq in HnbL.
  subst.
  apply nbLevelEq.

(* rewrite Hinstop1.
f_equal.
destruct indMMUToPrepare;simpl in *;subst;destruct defaultPage;simpl;subst;trivial.
f_equal.
apply proof_irrelevance;trivial. *) }
rewrite Hdef in *.
assert(Htru: (pageDefault =? pageDefault) = true).
symmetry.
apply beq_nat_refl.
rewrite Htru in *.
now contradict Hmap.

-
case_eq(getIndirection pd vavalue nbL (nbLevel - 1) s);intros * Hind;rewrite Hind in *;try now contradict Hmap.
case_eq(pageDefault =? p);intros * Hnotdef';rewrite Hnotdef' in *;try now contradict Hmap.
(* case_eq( getIndirection pd vavalue nbL (nbLevel - 1) s');intros * Hind'. *)

assert(Heq: getIndirection pd vavalue nbL (nbLevel - 1) s =
            getIndirection pd vavalue nbL (nbLevel - 1) s').
{  assert(Horlst: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vavalue l) \/  
(StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vavalue l) ) by apply indexDecOrNot.
destruct Horlst as [Horlst| Horlst].
+


 assert( Hnewvaddr: StateLib.checkVAddrsEqualityWOOffset (stop ) vaToPrepare vavalue nbL = false ).
{ apply checkVAddrsEqualityWOOffsetFalseS;trivial.

subst;trivial. }
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
-

subst.
assert(Hor: stop=0 \/ stop > 0) by lia.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
case_eq( levelEq nbL levelMin);intros * Hlvl;rewrite Hlvl in *.
rewrite CLevelIdentity' in Hfstl.
rewrite <- Hfstl in Hlvl.
now contradict Hlvl.
 now contradict Hvaddr.
* assert(Hrn: S (stop-1) = stop) by lia.
  apply pageTablesAreDifferentMiddle with (stop-1) s nbLevel pd pd nbL  vavalue vaToPrepare
 stop;trivial;try rewrite Hrn;trivial.
 rewrite checkVAddrsEqualityWOOffsetPermut';trivial.
 left;trivial.
 split;trivial.
 apply getNbLevelEq;trivial.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
-
assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try lia.
apply getIndirectionStopLevelGe with stop0;trivial.
lia.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try lia.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
+ assert(StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = true \/
StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = false) .
{ destruct (StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL).
  left;trivial.
  right;trivial. }
destruct H.
**  assert(Hinstop1: getIndirection pd vaToPrepare nbL (stop+1) s = Some pageDefault).
{  
   (** ici il faut montrer que indMMUToPrepare = tbl**)
pose proof getIndirectionEqStop as Hindeq.
assert( getIndirection pd vavalue nbL stop s = Some indirection).
rewrite <- Hindi.
symmetry.
apply Hindeq;trivial.
subst.
apply getIndirectionProp' with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indirection entry;
subst;trivial.
symmetry;trivial.
unfold isEntryPage in *.
unfold StateLib.readPhyEntry in *.
rewrite Hlookup in *.
inversion Hcurind;subst;trivial.
}
assert(HindeqStop: getIndirection pd vaToPrepare nbL stop s=
getIndirection pd vavalue nbL stop  s).

apply getIndirectionEqStop;subst;trivial.
(* apply beq_nat_true in Hdefcurind. *)

apply getIndirectionMapMMUPage11' with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
{ assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
 }

pose proof inclGetIndirectionsAuxLe as Hproof.
left.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
-
right.  

subst.
intuition.
rewrite <- HindeqStop in Hi1.
rewrite Hindi in Hi1.
inversion  Hi1;trivial.


-
assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try lia.
apply getIndirectionStopLevelGe with stop0;trivial.
lia.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }left.

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try lia.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }
left.

unfold not;intros;subst;now contradict Hnotinind.
 }
**
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
-

subst.
assert(Hor: stop=0 \/ stop > 0) by lia.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
inversion Hi1;subst.

inversion Hindi;subst.
now contradict H.
* assert(Hrn: S (stop-1) = stop) by lia.
  apply pageTablesAreDifferentMiddle with (stop-1) s nbLevel pd pd nbL  vavalue vaToPrepare
 stop;trivial;try rewrite Hrn;trivial.
 rewrite checkVAddrsEqualityWOOffsetPermut';trivial.
 left;trivial.
 split;trivial.
 apply getNbLevelEq;trivial.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.

-
assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try lia.
apply getIndirectionStopLevelGe with stop0;trivial.
lia.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try lia.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
 } }
 rewrite <- Heq.
 rewrite Hind.
 rewrite Hnotdef'.
 assert(Hkey: p <> indirection \/ StateLib.getIndexOfAddr vavalue levelMin <> StateLib.getIndexOfAddr vaToPrepare l).
{    subst.
    assert(Horx: stop = nbL \/ stop <> nbL) by lia.
    destruct Horx as [Horx | Horx].
    subst.
    replace (nbL - nbL) with 0 in Hfstl.
    unfold levelMin in Hfstl.
    unfold levelEq in Hfstl.
    rewrite <- beq_nat_refl in Hfstl.
    now contradict Hfstl.
    lia.
    assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }
 assert(~In p (getIndirectionsAux pd s (stop+1))).
{
pose proof nbLevelNotZero as HnbL0.
 
apply getIndirectionInGetIndirections2n with (nbLevel - 1) vavalue nbL;trivial;try lia.
replace (nbLevel - 1 + 1) with nbLevel by lia.
unfold getIndirections in *.
trivial.
apply beq_nat_false in Hnotdef'.
unfold not;intros;subst;now contradict Hnotdef'. }
assert(In indirection (getIndirectionsAux pd s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
 left.
 unfold not;intros;subst;now contradict H0.
 }
 
 assert(Hpres: StateLib.readPresent p (StateLib.getIndexOfAddr vavalue levelMin) (memory s)=
 StateLib.readPresent p (StateLib.getIndexOfAddr vavalue levelMin) (memory s')).
 {  apply readPresentMapMMUPage with entry;trivial. }
 assert(Hread: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue levelMin) (memory s)=
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue levelMin) (memory s')).
 {  apply readPhyEntryMapMMUPage with entry;trivial. }
 

 rewrite <- Hread.
 rewrite <- Hpres.
 trivial.
 Qed.

Lemma getAccessibleMappedPageAddIndirectionSh1Sh2 nbLgen  pd s vapg indirection vaToPrepare partition 
idxroot l r w e nextIndirection root entry:
let s':= {|
      currentPartition := currentPartition s;
      memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
                  (PE
                     {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
                  (memory s) pageEq idxEq |} in
Some nbLgen = StateLib.getNbLevel ->
partitionDescriptorEntry s ->
 idxroot = idxShadow1 \/ idxroot = idxShadow2 -> 

lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq =
          Some (PE entry) ->
In indirection (getIndirections root s) -> 
nextEntryIsPP partition idxroot root s ->
In partition (getPartitions pageRootPartition s) ->
nextEntryIsPP partition idxPageDir pd s->
noDupConfigPagesList s ->
getAccessibleMappedPage pd s vapg = getAccessibleMappedPage pd s' vapg.
Proof. 
intros * Hl Hpde Hor3.
intros.
unfold getAccessibleMappedPage.
rewrite <- Hl.
assert(Haux: forall stop tbl, getIndirection pd vapg nbLgen stop s = Some tbl -> 
(pageDefault =? tbl) = false ->
tbl <> indirection ).
{ intros.
 assert(Hconfdiff: noDupConfigPagesList s ) by intuition.
  unfold noDupConfigPagesList in *.
 assert(Hpart: In partition (getPartitions pageRootPartition s)) by trivial.
  generalize(Hconfdiff partition Hpart);clear Hconfdiff; intros Hconfdiff.
  unfold getConfigPages in Hconfdiff.
apply NoDup_cons_iff in Hconfdiff.
destruct Hconfdiff as (_ & Hconfdiff).
unfold getConfigPagesAux in *.
pose proof pdSh1Sh2ListExistsNotNull as Hprof.
generalize(Hprof s Hpde partition Hpart);clear Hprof;intros Hprof.
apply pdSh1Sh2ListExistsNotNull  with s partition in Hpde;trivial.
destruct Hpde as ((pd1 & Hpd1 & Hpdnotnull)
  & (sh1 & Hsh1 & Hsh1notnull) & (sh2 & Hsh2 & Hsh2notnull) &
  (sh3 & Hsh3 & Hsh3notnull)).
unfold getConfigPages.
unfold getConfigPagesAux.
rewrite Hpd1, Hsh1, Hsh2, Hsh3 in Hconfdiff.

apply NoDupSplitInclIff in Hconfdiff.
destruct Hconfdiff as (Hconfigdiff1 & Hconfdiff).
unfold disjoint in *.
assert(pd=pd1) by (apply getPdNextEntryIsPPEq with partition s;trivial).
subst.
assert(mykey: In tbl (getIndirections  pd1 s)).
{ apply getIndirectionInGetIndirections with vapg nbLgen stop;trivial.
  apply nbLevelNotZero.
  apply beq_nat_falseNot;trivial.
  apply getNbLevelLe;trivial. }

apply Hconfdiff in mykey.
rewrite in_app_iff in mykey.
apply not_or_and in mykey.

rewrite in_app_iff in mykey.
destruct mykey as (mykey1 &mykey2).
apply not_or_and in mykey2.
unfold not;intros;subst.
destruct Hor3 as [Hor3|Hor3];subst.
+  assert(root = sh1).
apply getSh1NextEntryIsPPEq with partition s;trivial.
subst root.
 
intuition.
+ assert(root = sh2).
apply getSh2NextEntryIsPPEq with partition s;trivial.
subst root.
 
intuition. }
assert(Hindeq: getIndirection pd vapg nbLgen (nbLevel - 1) s =
getIndirection pd vapg nbLgen (nbLevel - 1) s').
{  apply getIndirectionMapMMUPage11 with entry
;trivial.
+ apply pdPartNotNull with partition s;trivial. }
  rewrite <- Hindeq.
  case_eq (getIndirection pd vapg nbLgen (nbLevel - 1) s);intros * Hx;trivial.
  case_eq(pageDefault =? p);intros * Hp;trivial.
 
assert(Hpres:  StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s)=
 StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s')).
 apply readPresentMapMMUPage with entry;trivial.
 left.
 apply Haux with (nbLevel - 1);trivial.
 rewrite <- Hpres.
assert(Hread:  StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s)=
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s')).
 apply readPhyEntryMapMMUPage with entry;trivial.
 left.
 apply Haux with (nbLevel - 1);trivial.
 rewrite <- Hread;trivial.
 assert(Hacc:  StateLib.readAccessible p (StateLib.getIndexOfAddr vapg levelMin) (memory s)=
 StateLib.readAccessible p (StateLib.getIndexOfAddr vapg levelMin) (memory s')).
 symmetry. apply readAccessibleMapMMUPage ;trivial.
 left.
 apply Haux with (nbLevel - 1);trivial.
 rewrite <- Hacc;trivial.
Qed.


Lemma getAccessibleMappedPageSomeAddIndirectionSamePartSSI1 s (indirection nextIndirection :page) vaToPrepare entry  vavalue pd pg partition l lpred r w e
idxroot rootx
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr :
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
nextEntryIsPP partition idxroot rootx s ->
In indirection (getIndirections rootx s) -> 
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
nextEntryIsPP partition idxPageDir pd s ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
(pageDefault =? nextIndirection) = false ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
getAccessibleMappedPage pd s vavalue = SomePage pg ->
false = levelEq l levelMin ->
 getAccessibleMappedPage pd  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |} vavalue = SomePage pg.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hindor3 Hwell1 Hllpred  Hor3 Hpp Hindin  Hpde Hpart Hnodupcons Hprescons Hconfigdiff Hlookup Hpd Hcurind (* Hdefcurind *) Hdefnextind Hindfromroot Hmap Hfstl.


 unfold nextIndirectionsOR in *.
 destruct Hindor3 as [(Hi1 & Hi2 & Hii3) | Hindor3].
 { destruct Hindfromroot as (root & Hpdroot & Hrootdef & Hrem).
 unfold getAccessibleMappedPage, indirectionDescription in *.
 subst phyPDChild.
  subst phyMMUaddr.
  subst.
assert(Hnodup : NoDup (getIndirections root s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition idxPageDir ;trivial.
apply Hnodupcons;trivial.
 }
assert(root = pd).
apply getPdNextEntryIsPPEq with partition s;trivial.
apply nextEntryIsPPgetPd;trivial.
subst.
destruct Hrem as [(Heq & HnbL) | (nbL & stop & HnbL & Hstop & Hindi & Hnotdef & Hstopl)].
+ subst indirection;rewrite <- HnbL in *.
  assert(Hvaddr: StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vavalue l = true \/
  StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vavalue l = false)
  by (destruct (StateLib.checkVAddrsEqualityWOOffset);[left|right];trivial).
  destruct Hvaddr as [Hvaddr|Hvaddr].
  - case_eq(getIndirection pd vavalue l (nbLevel - 1) s );[intros tbl Htbl |intros Htbl]; rewrite Htbl in *;try now contradict Hmap. (** ici il faut montrer que indMMUToPrepare = tbl**)
    case_eq(pageDefault =? tbl);intros Hinddef;rewrite Hinddef in *; try now contradict Hmap.
    assert(Hind :  getIndirection pd vaToPrepare l (nbLevel - 1) s = Some pageDefault).
    { apply getIndirectionNbLevelEq with 1; try lia.
      apply getNbLevelEq in HnbL.
      subst.
      apply nbLevelEq.
      symmetry in Hfstl.
      apply levelEqBEqNatFalse0 in Hfstl.
      lia.
      simpl.
      rewrite <- Hfstl.
      assert(Hkey2: StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vaToPrepare l) (memory s)  = Some pageDefault).
      { trivial. }
      rewrite Hkey2.
      rewrite <- beq_nat_refl;trivial. }
      assert(Htrue : getIndirection pd vavalue l (nbLevel - 1) s =
      getIndirection pd vaToPrepare l (nbLevel - 1) s).
      symmetry.
      apply getIndirectionEq;trivial.
      destruct l;simpl;lia.
      rewrite Hind in Htrue.
      rewrite Htbl in Htrue.
      inversion Htrue.
      subst.
      apply beq_nat_false in Hinddef.
      lia.
 - assert(Hidxeq: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vavalue l) \/
 (StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vavalue l)) by apply indexDecOrNot.
  destruct Hidxeq as [Hidxeq |Hidxeq].
  * rewrite  Hidxeq in Hcurind.
    assert(Hind :  getIndirection pd vavalue l (nbLevel - 1) s = Some pageDefault).
    { apply getIndirectionNbLevelEq with 1; try lia.
      apply getNbLevelEq in HnbL.
      subst.
      apply nbLevelEq.
      symmetry in Hfstl.
      apply levelEqBEqNatFalse0 in Hfstl.
      lia.
      simpl.
      rewrite <- Hfstl.
      assert(Hkey2: StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l) (memory s)  = Some pageDefault).
      { trivial. }
      rewrite Hkey2.
      rewrite <- beq_nat_refl;trivial. }
    rewrite Hind in Hmap.
    assert(Htrue : (pageDefault =? pageDefault )=true).
    symmetry. apply beq_nat_refl.
    rewrite Htrue in *.
    now contradict Hmap.
  * assert (getIndirection pd vavalue l (nbLevel - 1) s = getIndirection pd vavalue l (nbLevel - 1) s').
  { clear Hmap.  
 destruct (nbLevel - 1); simpl. trivial.
 case_eq (levelEq l levelMin); intros * Hflst;trivial.

  assert(Hread: StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l)
    (add pd (StateLib.getIndexOfAddr vaToPrepare l)
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := nextIndirection |}) (memory s) pageEq idxEq) =StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l) (memory s)).
   {       symmetry. apply readPhyEntryMapMMUPage with entry;trivial.
          right;trivial.
          intuition. }
   rewrite Hread.
   case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l) (memory s));intros;trivial.        
   case_eq(pageDefault =? p);intros notdef;trivial.
   case_eq ( StateLib.Level.pred l);intros * Hlpred;trivial.  
  apply getIndirectionMapMMUPage11 with entry;trivial.
  intros.
 {
  pose proof indirectionNotInPreviousMMULevelAux.
  assert(Hor: stop < l \/ stop >= l) by lia.
  destruct Hor as [Hor | Hor].
 
*
  generalize(H2 vavalue s (S stop) pd l tbl);clear H2;intros H2.
  replace (S stop - 1) with stop in * by lia.
 
  assert(Hprevious: exists prevtab : page,
       getIndirection pd vavalue l stop s = Some prevtab /\
       prevtab <> pageDefault /\
       StateLib.readPhyEntry prevtab (StateLib.getIndexOfAddr vavalue (CLevel (l - stop))) (memory s) = Some tbl).
 { apply H2;clear H2;try lia.
 intuition.
  simpl.
  rewrite <- Hfstl.
  rewrite H.
  rewrite notdef.
  rewrite Hlpred;trivial.
  trivial. }
  destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev).
assert(~ In tbl (getIndirectionsAux pd s (stop + 1))).
{ apply getIndirectionInGetIndirections2 with prevtab vavalue l;
simpl; subst;
trivial.
destruct l;simpl in *.
lia.
replace(stop + 1 - 1) with stop in * by lia.
trivial.
replace(stop + 1 - 1) with stop in * by lia.
trivial.

unfold getIndirections in Hnodup.
apply noDupPreviousMMULevels with nbLevel.
trivial.
destruct l.
simpl in *.
lia.
assert((pageDefault =? tbl) = false) as Hnotdef  by trivial.
apply beq_nat_false in Hnotdef.
unfold not;intros;subst.
now contradict Hnotdef.
destruct l.
simpl in *.
lia.
}
assert( In pd (getIndirectionsAux pd s (stop + 1))).
{ replace  (stop + 1) with (S stop) by lia.
  simpl.
  left;trivial. }
unfold not;intros.
subst.
now contradict H4.
* assert(getIndirection p vavalue l0 (nbLevel -2) s = Some tbl ).
unfold StateLib.Level.pred in *.
case_eq( gt_dec l 0);intros * Hl0;rewrite Hl0 in *; try now contradict Hlpred.
inversion Hlpred.
apply getIndirectionStopLevelGT2 with stop;simpl in *;
subst;trivial.
lia.
assert(Hl: l = CLevel (nbLevel - 1)).
apply getNbLevelEq;trivial.
pose proof nbLevelEq as Heq.
rewrite <- Hl in Heq.
rewrite <- Heq.
lia.
  generalize(H2 vavalue s (nbLevel - 1) pd l tbl);clear H2;intros H2.
(*   replace (S stop - 1) with stop in * by lia.
   *)
   assert(Hl: l = CLevel (nbLevel - 1)).
apply getNbLevelEq;trivial.
pose proof nbLevelEq as Heq.
rewrite <- Hl in Heq.

pose proof nbLevelNotZero as nblnot0.
assert(l > 0).
apply levelEqBEqNatFalse0;trivial.
  assert(Hprevious: exists prevtab : page,
       getIndirection pd vavalue l (nbLevel - 1 -1) s = Some prevtab /\
       prevtab <> pageDefault /\
       StateLib.readPhyEntry prevtab (StateLib.getIndexOfAddr vavalue (CLevel (l - (nbLevel - 1 - 1)))) (memory s) = Some tbl).
 { apply H2;clear H2;try lia.
intuition.



replace (nbLevel - 1) with (nbLevel - 2 + 1) by lia.
clear H0.

replace (nbLevel - 2 + 1) with (S (nbLevel - 2)) by lia.
simpl.
rewrite <- Hfstl.
rewrite H.
rewrite notdef.
rewrite Hlpred;trivial.
trivial. }

 destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev).
assert(~ In tbl (getIndirectionsAux pd s ((nbLevel - 2) + 1))).
{ apply getIndirectionInGetIndirections2 with prevtab vavalue l;
simpl; subst;
trivial.

replace (nbLevel - 1) with (nbLevel - 2 + 1) by lia.
clear H0.

lia.
replace(nbLevel - 2 + 1 - 1) with  (nbLevel - 1 - 1) in * by lia.
trivial.

replace(nbLevel - 2 + 1 - 1) with  (nbLevel - 1 - 1) in * by lia.
trivial.
replace(nbLevel - 2 + 1 + 1) with  (nbLevel )  by lia.
unfold getIndirections in Hnodup.
trivial.
assert((pageDefault =? tbl) = false) as Hnotdef  by trivial.
apply beq_nat_false in Hnotdef.
unfold not;intros;subst.
now contradict Hnotdef.
replace(nbLevel - 2 + 1) with  (nbLevel - 1 ) in * by lia.
lia.
}
assert( In pd (getIndirectionsAux pd s (nbLevel - 2 + 1))) .
{ replace (nbLevel - 2 + 1) with (S(nbLevel -2)) by lia.
  simpl.
  left;trivial. }
unfold not;intros.
subst.
now contradict H4. }
*



   apply beq_nat_false in notdef.
   intuition.
   subst. now contradict notdef.
   }
   rewrite <- H.
    case_eq( getIndirection pd vavalue l (nbLevel - 1) s);intros * Htbl;trivial;rewrite Htbl in *.
case_eq( pageDefault =? p); intros * Hp;rewrite Hp in *;trivial.
assert( pd<>p).
 assert(Hl: l = CLevel (nbLevel - 1)).
apply getNbLevelEq;trivial.
pose proof nbLevelEq as Heq.
rewrite <- Hl in Heq.
assert(Ll: l> 0).
apply levelEqBEqNatFalse0;trivial.

symmetry;trivial.

assert(Hin:~ In p (getIndirectionsAux pd s (nbLevel - 1))).



 apply indirectionNotInPreviousMMULevel' with (StateLib.getIndexOfAddr vavalue levelMin)
 
 vavalue partition l idxPageDir;trivial.

 symmetry;trivial.
 subst;trivial.
 rewrite Heq;trivial.


 
 assert( In pd (getIndirectionsAux pd s (nbLevel - 1))) .
 
 subst.
 destruct (nbLevel - 1);simpl.
 subst.
 lia.
 left;trivial.
 

unfold not;intros.
subst.
now contradict Hin.
assert(StateLib.readPresent p (StateLib.getIndexOfAddr vavalue levelMin) (memory s') =
StateLib.readPresent p (StateLib.getIndexOfAddr vavalue levelMin) (memory s)).
symmetry.
apply readPresentMapMMUPage with entry;trivial.
left;intuition.
rewrite H1.

assert(StateLib.readAccessible p (StateLib.getIndexOfAddr vavalue levelMin) (memory s') =
StateLib.readAccessible p (StateLib.getIndexOfAddr vavalue levelMin) (memory s)).
apply readAccessibleMapMMUPage ;trivial.
left;intuition.
rewrite H2.

assert(Hread: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue levelMin) (memory s)
= StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue levelMin) (memory s')).
apply readPhyEntryMapMMUPage with entry;trivial.
left;trivial.
intuition.
rewrite <- Hread.
trivial.

trivial.
+ rewrite <- HnbL in *.
assert (Hstp: stop + 1 <= nbL).
{ subst. assert((nbL - stop) > 0).
symmetry in Hfstl.
apply levelEqBEqNatFalse0 in Hfstl ;trivial.
unfold CLevel in Hfstl.
case_eq(lt_dec (nbL - stop) nbLevel);intros * Hlt;rewrite Hlt in *.
simpl in *;trivial.
destruct nbL;simpl in *.
lia.

lia. }
 assert(Hvaddr: StateLib.checkVAddrsEqualityWOOffset (stop+1) vaToPrepare vavalue nbL = true \/
  StateLib.checkVAddrsEqualityWOOffset (stop+1) vaToPrepare vavalue nbL = false)
  by (destruct (StateLib.checkVAddrsEqualityWOOffset);[left|right];trivial).
  destruct Hvaddr as [Hvaddr|Hvaddr].
  -
assert(Hinstop1: getIndirection pd vaToPrepare nbL (stop+1) s = Some pageDefault).
{  
   (** ici il faut montrer que indMMUToPrepare = tbl**)
pose proof getIndirectionEqStop as Hindeq.
assert( getIndirection pd vavalue nbL stop s = Some indirection).
rewrite <- Hindi.
symmetry.
apply Hindeq;trivial.
subst.
apply checkVAddrsEqualityWOOffsetTrueLe with (stop+1);trivial.
  lia.
apply getIndirectionProp' with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indirection entry;
subst;trivial.
symmetry;trivial.
unfold isEntryPage, StateLib.readPhyEntry in *. rewrite Hlookup in *. inversion Hcurind;trivial.
}
assert(HindeqStop: getIndirection pd vaToPrepare nbL (stop + 1) s=
getIndirection pd vavalue nbL (stop + 1) s).

apply getIndirectionEqStop;subst;trivial.
(* apply beq_nat_true in Hdefcurind. *)
rewrite HindeqStop in Hinstop1.
assert(Hdef: getIndirection pd vavalue nbL (nbLevel - 1) s = Some pageDefault).
{ apply getIndirectionNbLevelEq with (stop+1);trivial.
  lia.
  apply getNbLevelEq in HnbL.
  subst.
  apply nbLevelEq. }
rewrite Hdef in *.
assert(Htru: (pageDefault =? pageDefault) = true).
symmetry.
apply beq_nat_refl.
rewrite Htru in *.
now contradict Hmap.

-
case_eq(getIndirection pd vavalue nbL (nbLevel - 1) s);intros * Hind;rewrite Hind in *;try now contradict Hmap.
case_eq(pageDefault =? p);intros * Hnotdef';rewrite Hnotdef' in *;try now contradict Hmap.
(* case_eq( getIndirection pd vavalue nbL (nbLevel - 1) s');intros * Hind'. *)

assert(Heq: getIndirection pd vavalue nbL (nbLevel - 1) s =
            getIndirection pd vavalue nbL (nbLevel - 1) s').
{ assert(Horlst: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vavalue l) \/  
(StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vavalue l) ) by apply indexDecOrNot.
destruct Horlst as [Horlst| Horlst].
+


 assert( Hnewvaddr: StateLib.checkVAddrsEqualityWOOffset (stop ) vaToPrepare vavalue nbL = false ).
{ apply checkVAddrsEqualityWOOffsetFalseS;trivial.

 subst;trivial. }
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
-

subst.
assert(Hor: stop=0 \/ stop > 0) by lia.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
case_eq( levelEq nbL levelMin);intros * Hlvl;rewrite Hlvl in *.
rewrite CLevelIdentity' in Hfstl.
rewrite <- Hfstl in Hlvl.
now contradict Hlvl.
 now contradict Hvaddr.
* assert(Hrn: S (stop-1) = stop) by lia.
  apply pageTablesAreDifferentMiddle with (stop-1) s nbLevel pd pd nbL  vavalue vaToPrepare
 stop;trivial;try rewrite Hrn;trivial.
 rewrite checkVAddrsEqualityWOOffsetPermut';trivial.
 left;trivial.
 split;trivial.
 apply getNbLevelEq;trivial.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
-
assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try lia.
apply getIndirectionStopLevelGe with stop0;trivial.
lia.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try lia.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
+ assert(StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = true \/
StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = false) .
{ destruct (StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL).
  left;trivial.
  right;trivial. }
destruct H.
**  assert(Hinstop1: getIndirection pd vaToPrepare nbL (stop+1) s = Some pageDefault).
{  
   (** ici il faut montrer que indMMUToPrepare = tbl**)
pose proof getIndirectionEqStop as Hindeq.
assert( getIndirection pd vavalue nbL stop s = Some indirection).
rewrite <- Hindi.
symmetry.
apply Hindeq;trivial.
subst.
apply getIndirectionProp' with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indirection entry;
subst;trivial.
symmetry;trivial.
unfold isEntryPage, StateLib.readPhyEntry in *. rewrite Hlookup in *. inversion Hcurind;trivial.
}
assert(HindeqStop: getIndirection pd vaToPrepare nbL stop s=
getIndirection pd vavalue nbL stop  s).

apply getIndirectionEqStop;subst;trivial.


apply getIndirectionMapMMUPage11' with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
{ assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
 }

pose proof inclGetIndirectionsAuxLe as Hproof.
left.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
-
right.  

subst.
intuition.
rewrite <- HindeqStop in Hi1.
rewrite Hindi in Hi1.
inversion  Hi1;trivial.


-
assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try lia.
apply getIndirectionStopLevelGe with stop0;trivial.
lia.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }left.

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try lia.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }
left.

unfold not;intros;subst;now contradict Hnotinind.
 }
**
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
-

subst.
assert(Hor: stop=0 \/ stop > 0) by lia.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
inversion Hi1;subst.

inversion Hindi;subst.
now contradict H.
* assert(Hrn: S (stop-1) = stop) by lia.
  apply pageTablesAreDifferentMiddle with (stop-1) s nbLevel pd pd nbL  vavalue vaToPrepare
 stop;trivial;try rewrite Hrn;trivial.
 rewrite checkVAddrsEqualityWOOffsetPermut';trivial.
 left;trivial.
 split;trivial.
 apply getNbLevelEq;trivial.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.

-
assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try lia.
apply getIndirectionStopLevelGe with stop0;trivial.
lia.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try lia.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
 } }
 rewrite <- Heq.
 rewrite Hind.
 rewrite Hnotdef'.
 assert(Hkey: p <> indirection \/ StateLib.getIndexOfAddr vavalue levelMin <> StateLib.getIndexOfAddr vaToPrepare l).
{    subst.
    assert(Horx: stop = nbL \/ stop <> nbL) by lia.
    destruct Horx as [Horx | Horx].
    subst.
    replace (nbL - nbL) with 0 in Hfstl.
    unfold levelMin in Hfstl.
    unfold levelEq in Hfstl.
    rewrite <- beq_nat_refl in Hfstl.
    now contradict Hfstl.
    lia.
    assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }
 assert(~In p (getIndirectionsAux pd s (stop+1))).
{
pose proof nbLevelNotZero as HnbL0.
 
apply getIndirectionInGetIndirections2n with (nbLevel - 1) vavalue nbL;trivial;try lia.
replace (nbLevel - 1 + 1) with nbLevel by lia.
unfold getIndirections in *.
trivial.
apply beq_nat_false in Hnotdef'.
unfold not;intros;subst;now contradict Hnotdef'. }
assert(In indirection (getIndirectionsAux pd s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
 left.
 unfold not;intros;subst;now contradict H0.
 }
 
 assert(Hpres: StateLib.readPresent p (StateLib.getIndexOfAddr vavalue levelMin) (memory s)=
 StateLib.readPresent p (StateLib.getIndexOfAddr vavalue levelMin) (memory s')).
 {  apply readPresentMapMMUPage with entry;trivial. }
 assert(Haccess: StateLib.readAccessible p (StateLib.getIndexOfAddr vavalue levelMin) (memory s') =
StateLib.readAccessible p (StateLib.getIndexOfAddr vavalue levelMin) (memory s)).
apply readAccessibleMapMMUPage ;trivial.

 assert(Hread: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue levelMin) (memory s)=
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue levelMin) (memory s')).
 {  apply readPhyEntryMapMMUPage with entry;trivial. }
 

 rewrite <- Hread.
 rewrite  Haccess.
 rewrite <- Hpres.
 trivial. }
 
 rewrite <- Hmap.
 symmetry.
 destruct Hindfromroot as (root & Hpdroot & Hrootdef & Hrem).
 destruct Hrem as [(Heq & HnbL) | (nbL & stop & HnbL & Hstop & Hindi & Hnotdef & Hstopl)].
 +
 apply getAccessibleMappedPageAddIndirectionSh1Sh2 with l partition idxroot rootx entry;trivial.
intuition.
 + apply getAccessibleMappedPageAddIndirectionSh1Sh2 with nbL partition idxroot rootx entry;trivial.
intuition.
 Qed.


Set Nested Proofs Allowed.
Lemma getMappedPageAddIndirectionSh1Sh2 nbLgen  pd s vapg indirection vaToPrepare partition 
idxroot l r w e nextIndirection root entry:
let s':= {|
      currentPartition := currentPartition s;
      memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
                  (PE
                     {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
                  (memory s) pageEq idxEq |} in
Some nbLgen = StateLib.getNbLevel ->
partitionDescriptorEntry s ->
 idxroot = idxShadow1 \/ idxroot = idxShadow2 -> 

lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq =
          Some (PE entry) ->
In indirection (getIndirections root s) -> 
nextEntryIsPP partition idxroot root s ->
In partition (getPartitions pageRootPartition s) ->
nextEntryIsPP partition idxPageDir pd s->
noDupConfigPagesList s ->
getMappedPage pd s vapg = getMappedPage pd s' vapg.
Proof. 
intros * Hl Hpde Hor3.
intros.
unfold getMappedPage.
rewrite <- Hl.
assert(Haux: forall stop tbl, getIndirection pd vapg nbLgen stop s = Some tbl -> 
(pageDefault =? tbl) = false ->
tbl <> indirection ).
{ intros.
 assert(Hconfdiff: noDupConfigPagesList s ) by intuition.
  unfold noDupConfigPagesList in *.
 assert(Hpart: In partition (getPartitions pageRootPartition s)) by trivial.
  generalize(Hconfdiff partition Hpart);clear Hconfdiff; intros Hconfdiff.
  unfold getConfigPages in Hconfdiff.
apply NoDup_cons_iff in Hconfdiff.
destruct Hconfdiff as (_ & Hconfdiff).
unfold getConfigPagesAux in *.
pose proof pdSh1Sh2ListExistsNotNull as Hprof.
generalize(Hprof s Hpde partition Hpart);clear Hprof;intros Hprof.
apply pdSh1Sh2ListExistsNotNull  with s partition in Hpde;trivial.
destruct Hpde as ((pd1 & Hpd1 & Hpdnotnull)
  & (sh1 & Hsh1 & Hsh1notnull) & (sh2 & Hsh2 & Hsh2notnull) &
  (sh3 & Hsh3 & Hsh3notnull)).
unfold getConfigPages.
unfold getConfigPagesAux.
rewrite Hpd1, Hsh1, Hsh2, Hsh3 in Hconfdiff.

apply NoDupSplitInclIff in Hconfdiff.
destruct Hconfdiff as (Hconfigdiff1 & Hconfdiff).
unfold disjoint in *.
assert(pd=pd1) by (apply getPdNextEntryIsPPEq with partition s;trivial).
subst.
assert(mykey: In tbl (getIndirections  pd1 s)).
{ apply getIndirectionInGetIndirections with vapg nbLgen stop;trivial.
  apply nbLevelNotZero.
  apply beq_nat_falseNot;trivial.
  apply getNbLevelLe;trivial. }

apply Hconfdiff in mykey.
rewrite in_app_iff in mykey.
apply not_or_and in mykey.

rewrite in_app_iff in mykey.
destruct mykey as (mykey1 &mykey2).
apply not_or_and in mykey2.
unfold not;intros;subst.
destruct Hor3 as [Hor3|Hor3];subst.
+  assert(root = sh1).
apply getSh1NextEntryIsPPEq with partition s;trivial.
subst root.
 
intuition.
+ assert(root = sh2).
apply getSh2NextEntryIsPPEq with partition s;trivial.
subst root.
 
intuition. }
assert(Hindeq: getIndirection pd vapg nbLgen (nbLevel - 1) s =
getIndirection pd vapg nbLgen (nbLevel - 1) s').
{  apply getIndirectionMapMMUPage11 with entry
;trivial.
+ apply pdPartNotNull with partition s;trivial. }
  rewrite <- Hindeq.
  case_eq (getIndirection pd vapg nbLgen (nbLevel - 1) s);intros * Hx;trivial.
  case_eq(pageDefault =? p);intros * Hp;trivial.
 
assert(Hpres:  StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s)=
 StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s')).
 apply readPresentMapMMUPage with entry;trivial.
 left.
 apply Haux with (nbLevel - 1);trivial.
 rewrite <- Hpres.
assert(Hread:  StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s)=
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s')).
 apply readPhyEntryMapMMUPage with entry;trivial.
 left.
 apply Haux with (nbLevel - 1);trivial.
 rewrite <- Hread;trivial.
Qed.

Lemma getMappedPagesAuxAddIndirectionSSI1 s indirection nextIndirection  entry nbLgen valist pd pg  vaToPrepare partition l r w e root idxroot
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr:
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->
partitionDescriptorEntry s ->
nextEntryIsPP partition idxroot root s ->
In indirection (getIndirections root s) -> 

In pg (getMappedPagesAux pd valist s) ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxPageDir pd s ->
nextIndirection <> indirection ->

 In pg  (getMappedPagesAux pd valist {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}).
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hor3 Hindor3 Hlookup Hl Hroot Hdef  Hinit Hlevel Hnodupcons Hpde Hppkey Hkey.
unfold getMappedPagesAux.
intros Hgoal.
intros.
assert(Hnodup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition idxPageDir ;trivial.
unfold noDupConfigPagesList in *.
apply Hnodupcons;trivial.
left;trivial. }

{
rewrite filterOptionInIff in *.
unfold getMappedPagesOption in *.
rewrite in_map_iff in *.
destruct Hgoal as (vapg & Hvapg & Hinvalist).
exists vapg;split;trivial.
unfold indirectionDescription,  initPEntryTablePreconditionToPropagatePrepareProperties in *.
destruct Hroot as (tableroot & Hpp & Hrootnotdef & Hor).
destruct Hor3 as [Hor3 | Ho3].
+ (** MMU **)
 assert(Hpdor: tableroot=pd).
 { subst. apply getPdNextEntryIsPPEq with partition s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
  subst tableroot.
destruct Hor as [(Heq & HnbL) | Hor].
- (** root **) subst.
  assert(Hnoneind:getIndirection indirection vaToPrepare l (nbLevel - 1) s = Some pageDefault).
  { apply getIndirectionNbLevelEq with 1;try lia.
    rewrite  getNbLevelEq with l;trivial.
    apply nbLevelEq.
    symmetry in Hlevel.
    apply levelEqBEqNatFalse0 in Hlevel.
    lia.
    simpl.
    rewrite <- Hlevel.
    assert(Hread: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault).
    trivial.
    rewrite Hread.
    rewrite <- beq_nat_refl;trivial. }
  assert(Hnone: getMappedPage indirection s vaToPrepare = NonePage).
  { unfold getMappedPage.
    rewrite <- HnbL.
    rewrite Hnoneind.
    assert(Heq: true=(pageDefault =? pageDefault)).
    apply beq_nat_refl.
    rewrite <- Heq.
    trivial. }
    (* assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\
StateLib.checkVAddrsEqualityWOOffset nbLevel vaInCurrentPartition va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1.
split;trivial.
rewrite <- H.*)
  assert(Hor :StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = true \/
         StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = false).
  { destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l);intuition. }
  destruct Hor as [Hor | Hor].
  * (** Same virtual address : contradiction **)
    assert(Hfalse: getMappedPage indirection s vapg = NonePage).
    rewrite <- Hnone.
    symmetry.
    apply getMappedPageEq with l;trivial.
    symmetry;trivial.
    rewrite Hfalse in Hvapg.
    now contradict Hvapg.
  *  apply getMappedPageSomeAddIndirectionSamePartSSI1 with entry partition ;trivial.
    unfold indirectionDescription in *.
    exists indirection.
    split;trivial.
     split;trivial.
     left;split;trivial.
     
 -  apply getMappedPageSomeAddIndirectionSamePartSSI1 with entry partition ;trivial.
     unfold indirectionDescription in *.
    exists pd.
    split;trivial.
     split;trivial.
     right;trivial.
+ rewrite <- Hvapg.
symmetry.
apply getMappedPageAddIndirectionSh1Sh2 with nbLgen partition idxroot root entry;trivial. } 
Qed.

 Lemma  isPresentNotDefaultIffMapMMUPage  s phyVaChild  ptVaChildpd idxvaChild r w e
     (* idxvaInCurPart ptVaInCurPartpd *)
entry
:
lookup ptVaChildpd idxvaChild (memory s) pageEq idxEq = Some (PE entry) ->
(* entryPresentFlag ptVaInCurPartpd idxvaInCurPart false s ->
isEntryPage ptVaInCurPartpd idxvaInCurPart phyVaChild s ->  *)
phyVaChild <> pageDefault ->
isPresentNotDefaultIff s ->
isPresentNotDefaultIff {|
      currentPartition := currentPartition s;
      memory := add ptVaChildpd idxvaChild
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := phyVaChild |}) (memory s) pageEq idxEq |}.
Proof.
unfold isPresentNotDefaultIff.
intros Hlookup (* Hi1 Hi2 *)  Hmykey Hi4.
simpl.
intros.

 assert(Hor : (  (table <> ptVaChildpd \/
idx <>
idxvaChild) \/  (~ (table <> ptVaChildpd \/
idx <>
idxvaChild)))).
{ apply classic. }
destruct Hor as [Hor | Hor];trivial.
+ assert(Hpres :StateLib.readPresent table idx
  (add ptVaChildpd idxvaChild
     (PE
        {|
        read := r;
        write := w;
        exec := e;
        present := true;
        user := true;
        pa := phyVaChild |}) (memory s) pageEq idxEq)=
         StateLib.readPresent table idx (memory s) ).
   symmetry.
  apply readPresentMapMMUPage with entry;trivial.
  rewrite Hpres.
  assert(Hacces :StateLib.readPhyEntry table idx
  (add ptVaChildpd idxvaChild
     (PE
        {|
        read := r;
        write := w;
        exec := e;
        present := true;
        user := true;
        pa := phyVaChild |}) (memory s) pageEq idxEq)=
         StateLib.readPhyEntry table idx (memory s) ).
   symmetry.
  apply readPhyEntryMapMMUPage with entry;trivial.
  rewrite Hacces.
  trivial.
+
apply not_or_and in Hor.
destruct Hor as(Hi5 & Hi6) .
subst.
apply NNPP in Hi5.
apply NNPP in Hi6.
rewrite Hi6 in *. clear Hi6.
subst.
assert(Htrue: beqPairs (ptVaChildpd, idxvaChild) (ptVaChildpd, idxvaChild) pageEq
           idxEq = true).
  { apply beqPairsTrue; split;trivial. }
split.
* intros. unfold StateLib.readPresent in *.
  simpl in *.
  rewrite Htrue in *.
  simpl in *.
  inversion H.
* intros.
  intros. unfold StateLib.readPresent.
  unfold StateLib.readPhyEntry in H.
    simpl in *.
  rewrite Htrue in *.
  simpl in *.
  inversion H;subst.
  now contradict Hmykey.
Qed.
Lemma getIndirectionMapMMUPage11Stoplt:
forall (stop1 : nat) (s : state) (a : vaddr) (phyVaChild ptVaChildpd pd : page) (e r w : bool) (idxvaChild : index)
   (entry : Pentry) (level : level) ,
 (forall (stop : nat) (tbl : page),
  getIndirection pd a level stop s = Some tbl -> (pageDefault =? tbl) = false -> stop1>  stop -> tbl <> ptVaChildpd) ->
 lookup ptVaChildpd idxvaChild (memory s) pageEq idxEq = Some (PE entry) ->
 pd <> pageDefault ->
 getIndirection pd a level stop1 s =
 getIndirection pd a level stop1
   {|
   currentPartition := currentPartition s;
   memory := add ptVaChildpd idxvaChild
               (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyVaChild |})
               (memory s) pageEq idxEq |}.
Proof.
   induction stop1.
   simpl;trivial.
   simpl in *.
   intros *  Hmykey Hlookup Hpdnotnull.
    case_eq( levelEq level levelMin);intros;trivial.
    assert(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a level)
    (add ptVaChildpd idxvaChild
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) pageEq idxEq) =
          StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a level)
    (memory s)). symmetry.
    apply readPhyEntryMapMMUPage with entry;trivial.
    left.
    generalize (Hmykey 0 pd);clear Hmykey;intros Hmykey.
    simpl in *.
    apply Hmykey;trivial.
    apply NPeano.Nat.eqb_neq.
    unfold not;intros.
    subst.
    destruct pageDefault;destruct pd;simpl in *;subst.
    contradict Hpdnotnull.
    f_equal. apply  proof_irrelevance.
    lia.
    rewrite H0.
    case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a level) (memory s));intros;trivial.
    case_eq(pageDefault =? p);intros;trivial.
    case_eq(StateLib.Level.pred level );intros;trivial.
    apply IHstop1 with entry;trivial.
    intros.
    apply Hmykey with (S stop).
    simpl.    
     
     rewrite H3 in *.
     rewrite H.
     rewrite H1.
     rewrite H2;trivial.
     trivial.
     lia.
     
     apply beq_nat_false in H2.
     unfold not;intros.
     subst. now contradict H2.
Qed.

Lemma getMappedPageSomeAddIndirectionSSI2 s indirection nextIndirection vapg entry nbLgen  pd pg indMMUToPrepare vaToPrepare partition l r w e root idxroot
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr:
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isPresentNotDefaultIff s ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(pageDefault =? indMMUToPrepare) = true ->
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->


indirectionDescription s partition indirection idxroot vaToPrepare l ->
getMappedPage pd  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |} vapg = SomePage pg ->
nextEntryIsPP partition idxroot root s -> 
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxPageDir pd s ->
nextIndirection <> indirection ->
getMappedPage pd s vapg = SomePage pg.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hor3 Hindor3 Hprecons Hlookup Hl Hroot Hdef Hdef' Hinit Hlevel Hnodupcons Hdescind Hvapg.
intros.

unfold indirectionDescription,  initPEntryTablePreconditionToPropagatePrepareProperties in *.
destruct Hroot as (tableroot & Hpp & Hrootnotdef & Hor).
destruct Hor3 as [Hor3 | Ho3].
{ (** MMU **)
 subst.
 unfold nextIndirectionsOR in *.
 destruct Hindor3 as [(Hi1 & Hi2 & Hii3) | Hindor3].
 { subst phyPDChild.
  subst phyMMUaddr.
  
 assert(Hpdor: tableroot=pd).

 { apply getPdNextEntryIsPPEq with partition s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
  subst tableroot.
 assert(Hnodup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition idxPageDir ;trivial.
apply Hnodupcons;trivial.
left;trivial. }

destruct Hor as [(Heq & HnbL) | Hor].
- (** root **) subst.
  assert(Hnoneind:getIndirection indirection vaToPrepare l (nbLevel - 1) s = Some pageDefault).
  { apply getIndirectionNbLevelEq with 1;try lia.
    rewrite  getNbLevelEq with l;trivial.
    apply nbLevelEq.
    symmetry in Hlevel.
    apply levelEqBEqNatFalse0 in Hlevel.
    lia.
    simpl.
    rewrite <- Hlevel.
    assert(Hread: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some indMMUToPrepare).
    apply isEntryPageReadPhyEntry1;trivial.
    rewrite Hread.
    rewrite Hdef';trivial. }
  assert(Hnone: getMappedPage indirection s vaToPrepare = NonePage).
  { unfold getMappedPage.
    rewrite <- HnbL.
    rewrite Hnoneind.
    assert(Heq: true=(pageDefault =? pageDefault)).
    apply beq_nat_refl.
    rewrite <- Heq.
    trivial. }
  assert(Hfalse: getMappedPage indirection s' vaToPrepare = NonePage \/
     getMappedPage indirection s' vaToPrepare = SomeDefault ).
    { revert Hnone.
      unfold getMappedPage.
      rewrite <- HnbL.
      intros.
      case_eq (getIndirection indirection vaToPrepare l (nbLevel - 1) s' );intros * Hind;
      trivial;[|left;trivial].
      symmetry in Hlevel.
      assert(Hnotfstl: l > 0) by (apply levelEqBEqNatFalse0;trivial).
      assert(HnbLgt: (nbLevel-1) > 0).
      { assert(Hx: nbLevel - 1 = l).
        {
        apply getNbLevelEq in HnbL.
        subst.
        rewrite <- nbLevelEq;trivial. }
        lia. }
      destruct (nbLevel - 1);
      simpl in Hind;try lia.
      rewrite Hlevel in Hind.
      simpl in Hind.
     
      assert(Hread:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l)
           (add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq) = Some nextIndirection).    
                apply readPhyEntryAddIndirectionSameTable.
      rewrite Hread in Hind.
      assert(Hnext: (pageDefault =? nextIndirection) = false) by trivial.
      rewrite Hnext in Hind.
      assert(Hwell':  isWellFormedMMUTables nextIndirection s').
      apply isWellFormedMMUTablesAddIndirection with entry;trivial.
      unfold isWellFormedMMUTables in Hwell'.
     
      case_eq( StateLib.Level.pred l );intros * Hpred;rewrite Hpred in *;try now contradict Hind.
      destruct n;simpl in Hind.
      +  generalize (Hwell'  (StateLib.getIndexOfAddr vaToPrepare levelMin) ); clear Hwell'; intros (Hi1 & Hi2).
       inversion Hind. subst p.
      rewrite Hnext.                    
     
      rewrite Hi2.
       right;trivial.
      +  
        case_eq(levelEq l0 levelMin);intros * Hl0;rewrite Hl0 in *.
        - generalize (Hwell'  (StateLib.getIndexOfAddr vaToPrepare levelMin) ); clear Hwell'; intros (Hi1 & Hi2).
          inversion Hind;subst p.
          rewrite Hnext.
          rewrite Hi2.
           right;trivial.
        - generalize (Hwell'  (StateLib.getIndexOfAddr vaToPrepare l0) ); clear Hwell'; intros (Hi1 & Hi2).
          simpl in *.
          rewrite   Hi1 in Hind.
       assert(Hdeftrue: (pageDefault =? pageDefault)=true). symmetry. apply beq_nat_refl.
       rewrite Hdeftrue in *.
       inversion Hind;subst.
       rewrite Hdeftrue.
       left;trivial.
      }
    (* assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\
StateLib.checkVAddrsEqualityWOOffset nbLevel vaInCurrentPartition va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1.
split;trivial.
rewrite <- H.*)
  assert(Hor :StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = true \/
         StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = false).
  { destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l);intuition. }
  destruct Hor as [Hor | Hor].
  * (** Same virtual address : contradiction **)
    assert(Heq:  getMappedPage indirection s' vapg =
    getMappedPage indirection s' vaToPrepare).
    symmetry.
        apply getMappedPageEq with l;trivial.
       
    symmetry;trivial.
   
   
      destruct Hfalse as [Hfalse| Hfalse];
    rewrite Heq in Hvapg;
    rewrite Hvapg in Hfalse;
    now contradict Hfalse.
  *
 assert(HHkey: pg<> pageDefault) .
  {
   revert Hvapg Hlookup Hprecons.
    assert(Hnotdef: (pageDefault =? nextIndirection) = false) by trivial.
    revert Hnotdef.
    clear .
    unfold getMappedPage.
    intros.
    destruct (StateLib.getNbLevel);try now contradict Hvapg.
    destruct ( getIndirection indirection vapg l0 (nbLevel - 1) s');try now contradict Hvapg.
    destruct (pageDefault =? p);try now contradict Hvapg.
    case_eq( StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s') );intros * Hpres;rewrite Hpres in *;try now contradict Hvapg.
    case_eq (b);intros * Hb ;rewrite Hb in *;try now contradict Hvapg.
    case_eq(StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s'));intros * Hread;
    rewrite Hread in *;try now contradict Hvapg.
   
    inversion Hvapg;subst.
    assert(Hcons':  isPresentNotDefaultIff s').
    { intros. eapply isPresentNotDefaultIffMapMMUPage with entry;trivial.
    apply beq_nat_falseNot;trivial.
   
   
    }
    unfold isPresentNotDefaultIff in Hcons'.
    generalize(Hcons' p (StateLib.getIndexOfAddr vapg levelMin) );clear Hcons';
    intros Hcons'.
    destruct Hcons' as (Hcons'1 & Hcons'2).
    unfold not;intros ;subst.
    apply Hcons'2 in Hread.
    rewrite Hread in Hpres.
    now contradict Hpres.
     }
  assert(Htrue :forall pi,  getMappedPage indirection s' vaToPrepare <> SomePage pi).
  intros.
  destruct Hfalse as [Hfalse | Hfalse];
  rewrite Hfalse;
  unfold not;intros Hxx;now contradict Hxx.
  move Htrue at top.
  move Hfalse at top.

    unfold getMappedPage in *.
    rewrite <- Hl in *.
    rewrite <- HnbL in Hl.
    inversion HnbL.
    subst nbLgen.
    clear Hnone.

     case_eq( getIndirection indirection vapg l (nbLevel - 1) s' );intros * Hindx'; rewrite Hindx' in Hvapg;try now contradict Hvapg.
      case_eq(pageDefault =? p);intros * Hnotdefp;rewrite Hnotdefp in Hvapg;try now contradict Hnotdefp.
    case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s'));intros * Hpres;rewrite Hpres in *;try now contradict Hvapg.
    case_eq(b);intros * Hb;rewrite Hb in *;subst;try now contradict Hvapg.
    case_eq(StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s'));intros * Hread;
    rewrite Hread in *;try now contradict Hvapg.
    inversion Hvapg;subst.
    assert(Hindeq: getIndirection indirection vapg l (nbLevel - 1) s =
    getIndirection indirection vapg l (nbLevel - 1) s').
    { apply getIndirectionAddIndirectionCheckVaddrsFalse with p pg  entry partition;trivial.
     apply beq_nat_true in Hdef';subst. unfold isEntryPage, StateLib.readPhyEntry in *. rewrite Hlookup in *. rewrite Hdef. symmetry;f_equal;trivial.
    destruct pageDefault;destruct indMMUToPrepare;simpl in *;inversion Hdef';subst;f_equal;apply proof_irrelevance.  }
    rewrite <- Hindeq in *.
    case_eq(getIndirection indirection vapg l (nbLevel - 1) s);intros * Hine;rewrite Hine in *; try now contradict Hvapg.
    case_eq(pageDefault =? p);intros * Hdefi;rewrite Hdefi in *; try now contradict Hvapg.
inversion Hindx'.
subst.
    assert(Hkey: p <> indirection).
{ assert(Hx: nbLevel - 1 = l).
{
apply getNbLevelEq in Hl.
subst.
rewrite <- nbLevelEq;trivial. }
    assert(nbLevel-1 >0) .
    rewrite Hx.
    apply  levelEqBEqNatFalse0;trivial.
    symmetry;trivial.
    assert(Ht1: In indirection (getIndirectionsAux indirection s (nbLevel-1) )).
    { destruct (nbLevel-1);simpl.
    lia.
    left;trivial. }
    assert(Ht2: ~In p (getIndirectionsAux indirection s (nbLevel-1))).
    { apply getIndirectionInGetIndirections2' with vapg l;trivial.
    lia.
    unfold noDupConfigPagesList in *.
    unfold getIndirections in *.
    replace (nbLevel -1 + 1) with nbLevel by lia.
    trivial.
    apply beq_nat_false in Hdefi.
    destruct pageDefault;simpl in *;destruct p;simpl in *.
    unfold not;intros xxx;simpl in *.
    inversion xxx.
    subst.
    now contradict Hdefi.
   
lia. }

unfold not;intros;subst;now contradict Ht2. }

assert(Hpreseq: StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s')=
StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s)).
symmetry.
apply readPresentMapMMUPage with entry;trivial.
left;trivial.
assert(Hreadeq: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s')=
StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s)).
symmetry.
apply readPhyEntryMapMMUPage with entry;trivial.
left;trivial.  
 rewrite <- Hpreseq.
 rewrite Hpres.
 rewrite <- Hreadeq.
 rewrite Hread;trivial.
 rewrite Hdefi;trivial.

 - destruct Hor as (nbL & stop & HnbL & Hstop & Hind & Hnotdef & Hv).
 unfold getMappedPage in *.
 rewrite <- HnbL in *.
 assert (Hstp: stop + 1 <= nbL).
{ subst. assert((nbL - stop) > 0).
symmetry in Hlevel.
apply levelEqBEqNatFalse0 in Hlevel ;trivial.
unfold CLevel in Hlevel.
case_eq(lt_dec (nbL - stop) nbLevel);intros * Hlt;rewrite Hlt in *.
simpl in *;trivial.
destruct nbL;simpl in *.
lia.

lia. }

assert(Hvaddr: StateLib.checkVAddrsEqualityWOOffset (stop+1) vaToPrepare vapg nbL = true \/
  StateLib.checkVAddrsEqualityWOOffset (stop+1) vaToPrepare vapg nbL = false)
  by (destruct (StateLib.checkVAddrsEqualityWOOffset);[left|right];trivial).
  destruct Hvaddr as [Hvaddr|Hvaddr].
  + assert(Hinstop1: getIndirection pd vaToPrepare nbL (stop+1) s = Some indMMUToPrepare).
    {  
       (** ici il faut montrer que indMMUToPrepare = tbl**)
    pose proof getIndirectionEqStop as Hindeq.
    assert( getIndirection pd vapg nbL stop s = Some indirection).
    rewrite <- Hind.
    symmetry.
    apply Hindeq;trivial.
    subst.
    apply checkVAddrsEqualityWOOffsetTrueLe with (stop+1);trivial.
      lia.
    apply getIndirectionProp' with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indirection entry;
    subst;trivial.
    symmetry;trivial.
    }
    assert(HindeqStopi: getIndirection pd vaToPrepare nbL (stop + 1) s=
    getIndirection pd vapg nbL (stop + 1) s).  
    apply getIndirectionEqStop;subst;trivial.
    assert(HindeqStop: getIndirection pd vaToPrepare nbL (stop + 1) s'=
    getIndirection pd vapg nbL (stop + 1) s').  
    apply getIndirectionEqStop;subst;trivial.
    apply beq_nat_true in Hdef'.
    (* rewrite HindeqStop in Hinstop1. *)
    case_eq(getIndirection pd vapg nbL (nbLevel - 1) s' );intros * Hinds'; rewrite Hinds' in *;
    try now contradict Hvapg.
    case_eq(pageDefault =? p);intros * Hdefs';rewrite Hdefs' in *;try now contradict Hvapg.
    move Hind at bottom.
    assert(Hi: getIndirection pd vaToPrepare nbL (stop+1) s' = Some nextIndirection).
    { apply getIndirectionStopS1 with indirection;trivial.
    +
      rewrite <- Hind.
      symmetry.

      apply getIndirectionMapMMUPage11Stoplt with entry
;trivial.
intros * Hi1 Hi2 Hi3.

 assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
+ simpl. subst.
  rewrite <- Hlevel.
  rewrite readPhyEntryAddIndirectionSameTable.
  assert(Hnext: (pageDefault =? nextIndirection) = false) by trivial.
  rewrite Hnext.
  case_eq( StateLib.Level.pred (CLevel (nbL - stop)));intros * Hpred;trivial.
  symmetry in Hlevel.
  apply levelPredNone in Hlevel.
  now contradict Hlevel.
   }
     assert (Hnbleq: nbLevel - 1 = nbL).
      {  apply getNbLevelEq in HnbL.
      subst.
      apply nbLevelEq. }
    assert(Hor: stop + 1+1 <= nbLevel-1 \/ stop + 1+1 > nbLevel-1 ) by lia.
    destruct Hor as [Hor | Hor].
    * rewrite HindeqStop in Hi.
     
    assert(Hii:  getIndirection pd vapg nbL (stop + 1 +1 ) s' = Some pageDefault).
    {  apply getIndirectionStopS1 with nextIndirection;trivial. lia.
        apply beq_nat_falseNot;trivial.
        simpl.
      case_eq(levelEq (CLevel (nbL - (stop + 1))) levelMin);intros * Hfst.
      apply levelEqBEqNatTrue0 in Hfst.
      rewrite <- Hnbleq in Hfst.
      unfold CLevel in Hfst.
      case_eq(lt_dec (nbLevel - 1 - (stop + 1)) nbLevel) ; intros * Hls;rewrite Hls in *;simpl in *.
      rewrite <- Hnbleq in Hstp.
      lia.
      lia.
      rewrite Hv.
      assert(Hread:  StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vapg (CLevel (nbL - (stop + 1))))
      (memory s') = Some pageDefault).
      { assert(Hwell':  isWellFormedMMUTables nextIndirection s').
          apply isWellFormedMMUTablesAddIndirection with entry;trivial.
          unfold isWellFormedMMUTables in Hwell'.
          generalize (Hwell'(StateLib.getIndexOfAddr vapg (CLevel (nbL - (stop + 1)))) ) ; clear Hwell'; intros .
          intuition.
     }
     simpl in Hread.
     rewrite <- Hv.
 rewrite Hread.
 rewrite <- beq_nat_refl;trivial.
     }
    assert(Hdefx: getIndirection pd vapg nbL (nbLevel - 1) s' = Some pageDefault).
    { apply getIndirectionNbLevelEq with (stop+1 +1);trivial.
      lia.
      rewrite <- Hnbleq.
      trivial. }
      rewrite Hinds' in Hdefx.
      inversion Hdefx.
      subst.
      rewrite <- beq_nat_refl in Hdefs'.
      now contradict Hdefx.
    *  assert(Htrueeq: stop+1 = nbL) by lia.
      rewrite Htrueeq in *.
      rewrite Hnbleq in *.
      rewrite HindeqStop in Hi.
      rewrite Hinds' in Hi.
      inversion Hi;subst.
      assert(Hconspres: StateLib.readPresent nextIndirection (StateLib.getIndexOfAddr vapg levelMin)
       (memory s') = Some false).
             assert(Hwell':  isWellFormedMMUTables nextIndirection s').
          apply isWellFormedMMUTablesAddIndirection with entry;trivial.
          unfold isWellFormedMMUTables in Hwell'.
          generalize (Hwell' (StateLib.getIndexOfAddr vapg levelMin) ) ; clear Hwell'; intros .
          intuition.
          rewrite Hconspres in *.
          now contradict Hvapg.
+ case_eq ( getIndirection pd vapg nbL (nbLevel - 1) s');intros * Hinds';rewrite Hinds' in *;try now contradict Hvapg.
  case_eq(pageDefault =? p) ; intros * Hps';rewrite Hps' in *;try now contradict Hvapg.
  assert(Heqs':  getIndirection pd vapg nbL (nbLevel - 1) s =
   getIndirection pd vapg nbL (nbLevel - 1) s').
  {  assert(Horlst: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vapg l) \/  
(StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vapg l) ) by apply indexDecOrNot.
destruct Horlst as [Horlst| Horlst].
+


 assert( Hnewvaddr: StateLib.checkVAddrsEqualityWOOffset (stop ) vaToPrepare vapg nbL = false ).
{ apply checkVAddrsEqualityWOOffsetFalseS;trivial.

 subst;trivial. }
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vapg nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
- subst.
assert(Hor: stop=0 \/ stop > 0) by lia.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
case_eq( levelEq nbL levelMin);intros * Hlvl;rewrite Hlvl in *.
rewrite CLevelIdentity' in Hlevel.
rewrite <- Hlevel in Hlvl.
now contradict Hlvl.
 now contradict Hvaddr.
* assert(Hrn: S (stop-1) = stop) by lia.
  apply pageTablesAreDifferentMiddle with (stop-1) s nbLevel pd pd nbL  vapg vaToPrepare
 stop;trivial;try rewrite Hrn;trivial.
 rewrite checkVAddrsEqualityWOOffsetPermut';trivial.
 left;trivial.
 split;trivial.
 apply getNbLevelEq;trivial.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
-
assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vapg nbL;trivial;try lia.
apply getIndirectionStopLevelGe with stop0;trivial.
lia.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vapg nbL;trivial;try lia.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
+ assert(Horstop: StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vapg nbL = true \/
StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vapg nbL = false) .
{ destruct (StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vapg nbL).
  left;trivial.
  right;trivial. }
destruct Horstop as [Hstopor| Hstopor].
**  assert(Hinstop1: getIndirection pd vaToPrepare nbL (stop+1) s = Some indMMUToPrepare).
{  
   (** ici il faut montrer que indMMUToPrepare = tbl**)
pose proof getIndirectionEqStop as Hindeq.
assert( getIndirection pd vapg nbL stop s = Some indirection).
rewrite <- Hind.
symmetry.
apply Hindeq;trivial.
subst.
apply getIndirectionProp' with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indirection entry;
subst;trivial.
symmetry;trivial.
}
assert(HindeqStop: getIndirection pd vaToPrepare nbL stop s=
getIndirection pd vapg nbL stop  s).

apply getIndirectionEqStop;subst;trivial.
apply beq_nat_true in Hdef'.

apply getIndirectionMapMMUPage11' with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vapg nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
{ assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
 }

pose proof inclGetIndirectionsAuxLe as Hproof.
left.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
-
right.  

subst.
intuition.
rewrite <- HindeqStop in Hi1.
rewrite Hind in Hi1.
inversion  Hi1;trivial.


-
assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{
 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vapg nbL;trivial;try lia.
apply getIndirectionStopLevelGe with stop0;trivial.
lia.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }left.

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vapg nbL;trivial;try lia.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }
left.

unfold not;intros;subst;now contradict Hnotinind.
 }
**
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vapg nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
-

subst.
assert(Hor: stop=0 \/ stop > 0) by lia.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
inversion Hi1;subst.

inversion Hind;subst.
now contradict H.
* assert(Hrn: S (stop-1) = stop) by lia.
  apply pageTablesAreDifferentMiddle with (stop-1) s nbLevel pd pd nbL  vapg vaToPrepare
 stop;trivial;try rewrite Hrn;trivial.
 rewrite checkVAddrsEqualityWOOffsetPermut';trivial.
 left;trivial.
 split;trivial.
 apply getNbLevelEq;trivial.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.

-
assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vapg nbL;trivial;try lia.
apply getIndirectionStopLevelGe with stop0;trivial.
lia.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vapg nbL;trivial;try lia.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
 } }
rewrite  Heqs'.
 rewrite Hinds'.
 rewrite Hps'.
 assert(Hkey: p <> indirection \/ StateLib.getIndexOfAddr vapg levelMin <> StateLib.getIndexOfAddr vaToPrepare l).
{    subst.
    assert(Horx: stop = nbL \/ stop <> nbL) by lia.
    destruct Horx as [Horx | Horx].
    subst.
    replace (nbL - nbL) with 0 in Hlevel.
    unfold levelMin in Hlevel.
    unfold levelEq in Hlevel.
    rewrite <- beq_nat_refl in Hlevel.
    now contradict Hlevel.
    lia.
    assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }
 assert(~In p (getIndirectionsAux pd s (stop+1))).
{
pose proof nbLevelNotZero as HnbL0.
 
apply getIndirectionInGetIndirections2n with (nbLevel - 1) vapg nbL;trivial;try lia.
rewrite Heqs';trivial.
replace (nbLevel - 1 + 1) with nbLevel by lia.
unfold getIndirections in *.
trivial.
apply beq_nat_false in Hps'.
unfold not;intros;subst;now contradict Hps'. }
assert(In indirection (getIndirectionsAux pd s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
 left.
 unfold not;intros;subst;now contradict H0.
 }
 
 assert(Hpres: StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s)=
 StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s')).
 {  apply readPresentMapMMUPage with entry;trivial. }
 assert(Hread: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s)=
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s')).
 {  apply readPhyEntryMapMMUPage with entry;trivial. }
 

 rewrite  Hread.
 rewrite  Hpres.
 trivial.
 }
assert(Hfalse: idxPageDir<> idxShadow1) by apply idxPDidxSh1notEq.
assert(Hfalse1: idxPageDir <> idxShadow2) by apply idxPDidxSh2notEq.
destruct Hindor3 as [(Hi1 & Hi2 & Hii3)|(Hi1 & Hi2 & Hii3)];subst.

now contradict Hfalse1.

now contradict Hfalse.
}
rewrite <- Hvapg.
apply getMappedPageAddIndirectionSh1Sh2  with nbLgen partition idxroot root entry;trivial.  
apply indirectionDescriptionInGetIndirections with partition vaToPrepare l idxroot;trivial.
destruct Ho3.
right;trivial.
left;trivial.
right;right;trivial.


Qed.



Lemma getAccessibleMappedPageSomeAddIndirectionSSI2 s indirection nextIndirection 
vapg entry nbLgen  pd pg  vaToPrepare partition l r w e root idxroot
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr:
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isPresentNotDefaultIff s ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->
getAccessibleMappedPage pd  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |} vapg = SomePage pg ->
nextEntryIsPP partition idxroot root s ->
In indirection (getIndirections root s) -> 

partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxPageDir pd s ->
nextIndirection <> indirection ->
getAccessibleMappedPage pd s vapg = SomePage pg.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hor3 Hindor3 Hprecons Hlookup Hl Hroot Hdef (* Hdef' *) Hinit Hlevel Hnodupcons Hvapg.
intros.
unfold indirectionDescription,  initPEntryTablePreconditionToPropagatePrepareProperties in *.
destruct Hindor3 as [(Hi1 & Hi2 & Hi3)|Hindor3].
{ subst phyPDChild.
  subst phyMMUaddr.
  subst.

destruct Hroot as (tableroot & Hpp & Hrootnotdef & Hor).
 assert(Hpdor: tableroot=pd).

 { apply getPdNextEntryIsPPEq with partition s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
  subst tableroot.
 assert(Hnodup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition idxPageDir ;trivial.
apply Hnodupcons;trivial.
 }

destruct Hor as [(Heq & HnbL) | Hor].
- (** root **) subst .
  assert(Hnoneind:getIndirection indirection vaToPrepare l (nbLevel - 1) s = Some pageDefault).
  { apply getIndirectionNbLevelEq with 1;try lia.
    rewrite  getNbLevelEq with l;trivial.
    apply nbLevelEq.
    symmetry in Hlevel.
    apply levelEqBEqNatFalse0 in Hlevel.
    lia.
    simpl.
    rewrite <- Hlevel.
    assert(Hread: StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault).
    
 trivial.
    rewrite Hread.
    rewrite <- beq_nat_refl;trivial. }
  assert(Hnone: getAccessibleMappedPage indirection s vaToPrepare = NonePage).
  { unfold getAccessibleMappedPage.
    rewrite <- HnbL.
    rewrite Hnoneind.
    assert(Heq: true=(pageDefault =? pageDefault)).
    apply beq_nat_refl.
    rewrite <- Heq.
    trivial. }
  assert(Hfalse: getAccessibleMappedPage indirection s' vaToPrepare = NonePage \/
     getAccessibleMappedPage indirection s' vaToPrepare = SomeDefault ).
    { revert Hnone.
      unfold getAccessibleMappedPage.
      rewrite <- HnbL.
      intros.
      case_eq (getIndirection indirection vaToPrepare l (nbLevel - 1) s' );intros * Hind;
      trivial;[|left;trivial].
      symmetry in Hlevel.
      assert(Hnotfstl: l > 0) by (apply levelEqBEqNatFalse0;trivial).
      assert(HnbLgt: (nbLevel-1) > 0).
      { assert(Hx: nbLevel - 1 = l).
        {
        apply getNbLevelEq in HnbL.
        subst.
        rewrite <- nbLevelEq;trivial. }
        lia. }
      destruct (nbLevel - 1);
      simpl in Hind;try lia.
      rewrite Hlevel in Hind.
      simpl in Hind.
     
      assert(Hread:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l)
           (add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq) = Some nextIndirection).    
                apply readPhyEntryAddIndirectionSameTable.
      rewrite Hread in Hind.
      assert(Hnext: (pageDefault =? nextIndirection) = false) by trivial.
      rewrite Hnext in Hind.
      assert(Hwell':  isWellFormedMMUTables nextIndirection s').
      apply isWellFormedMMUTablesAddIndirection with entry;trivial.
      unfold isWellFormedMMUTables in Hwell'.
     
      case_eq( StateLib.Level.pred l );intros * Hpred;rewrite Hpred in *;try now contradict Hind.
      destruct n;simpl in Hind.
      +  generalize (Hwell'  (StateLib.getIndexOfAddr vaToPrepare levelMin) ); clear Hwell'; intros (Hi1 & Hi2).
       inversion Hind. subst p.
      rewrite Hnext.                    
     
      rewrite Hi2.
       left;trivial.
      +  
        case_eq(levelEq l0 levelMin);intros * Hl0;rewrite Hl0 in *.
        - generalize (Hwell'  (StateLib.getIndexOfAddr vaToPrepare levelMin) ); clear Hwell'; intros (Hi1 & Hi2).
          inversion Hind;subst p.
          rewrite Hnext.
          rewrite Hi2.
           left;trivial.
        - generalize (Hwell'  (StateLib.getIndexOfAddr vaToPrepare l0) ); clear Hwell'; intros (Hi1 & Hi2).
          simpl in *.
          rewrite   Hi1 in Hind.
       assert(Hdeftrue: (pageDefault =? pageDefault)=true). symmetry. apply beq_nat_refl.
       rewrite Hdeftrue in *.
       inversion Hind;subst.
       rewrite Hdeftrue.
       left;trivial.
      }
    (* assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\
StateLib.checkVAddrsEqualityWOOffset nbLevel vaInCurrentPartition va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1.
split;trivial.
rewrite <- H.*)
  assert(Hor :StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = true \/
         StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = false).
  { destruct (StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l);intuition. }
  destruct Hor as [Hor | Hor].
  * (** Same virtual address : contradiction **)
    assert(Heq:  getAccessibleMappedPage indirection s' vapg =
    getAccessibleMappedPage indirection s' vaToPrepare).
    symmetry.
        apply getAccessibleMappedPageEq with l;trivial.
       
    symmetry;trivial.
   
   
      destruct Hfalse as [Hfalse| Hfalse];
    rewrite Heq in Hvapg;
    rewrite Hvapg in Hfalse;
    now contradict Hfalse.
  *
 assert(HHkey: pg<> pageDefault) .
  {
   revert Hvapg Hlookup Hprecons.
    assert(Hnotdef: (pageDefault =? nextIndirection) = false) by trivial.
    revert Hnotdef.
    clear .
    unfold getAccessibleMappedPage.
    intros.
    destruct (StateLib.getNbLevel);try now contradict Hvapg.
    destruct ( getIndirection indirection vapg l0 (nbLevel - 1) s');try now contradict Hvapg.
    destruct (pageDefault =? p);try now contradict Hvapg.
    case_eq( StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s') );intros * Hpres;rewrite Hpres in *;try now contradict Hvapg.
    case_eq (b);intros * Hb ;rewrite Hb in *;try now contradict Hvapg.
    case_eq( StateLib.readAccessible p (StateLib.getIndexOfAddr vapg levelMin) (memory s'));intros * Haccess;rewrite Haccess in *;try now contradict Hvapg.
    case_eq b0; intros * Hb0;rewrite Hb0 in *;try now contradict Hvapg.
    case_eq(StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s'));intros * Hread;
    rewrite Hread in *;try now contradict Hvapg.
   
    inversion Hvapg;subst.
    assert(Hcons':  isPresentNotDefaultIff s').
    { intros. eapply isPresentNotDefaultIffMapMMUPage with entry;trivial.
    apply beq_nat_falseNot;trivial.
   
   
    }
    unfold isPresentNotDefaultIff in Hcons'.
    generalize(Hcons' p (StateLib.getIndexOfAddr vapg levelMin) );clear Hcons';
    intros Hcons'.
    destruct Hcons' as (Hcons'1 & Hcons'2).
    unfold not;intros ;subst.
    apply Hcons'2 in Hread.
    rewrite Hread in Hpres.
    now contradict Hpres.
     }
  assert(Htrue :forall pi,  getAccessibleMappedPage indirection s' vaToPrepare <> SomePage pi).
  intros.
  destruct Hfalse as [Hfalse | Hfalse];
  rewrite Hfalse;
  unfold not;intros Hxx;now contradict Hxx.
  move Htrue at top.
  move Hfalse at top.

    unfold getAccessibleMappedPage in *.
    rewrite <- Hl in *.
    rewrite <- HnbL in Hl.
    inversion HnbL.
    subst nbLgen.
    clear Hnone.

     case_eq( getIndirection indirection vapg l (nbLevel - 1) s' );intros * Hindx'; rewrite Hindx' in Hvapg;try now contradict Hvapg.
      case_eq(pageDefault =? p);intros * Hnotdefp;rewrite Hnotdefp in Hvapg;try now contradict Hnotdefp.
    case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s'));intros * Hpres;rewrite Hpres in *;try now contradict Hvapg.
    case_eq(b);intros * Hb;rewrite Hb in *;subst;try now contradict Hvapg.
    case_eq( StateLib.readAccessible p (StateLib.getIndexOfAddr vapg levelMin) (memory s'));intros * Haccess;rewrite Haccess in *;try now contradict Hvapg.
    case_eq b; intros * Hb0;rewrite Hb0 in *;try now contradict Hvapg.
    case_eq(StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s'));intros * Hread;
    rewrite Hread in *;try now contradict Hvapg.
    inversion Hvapg;subst.
    assert(Hindeq: getIndirection indirection vapg l (nbLevel - 1) s =
    getIndirection indirection vapg l (nbLevel - 1) s').
    { apply getIndirectionAddIndirectionCheckVaddrsFalse with p pg  entry partition;trivial. }
    rewrite <- Hindeq in *.
    case_eq(getIndirection indirection vapg l (nbLevel - 1) s);intros * Hine;rewrite Hine in *; try now contradict Hvapg.
    case_eq(pageDefault =? p);intros * Hdefi;rewrite Hdefi in *; try now contradict Hvapg.
inversion Hindx'.
subst.
    assert(Hkey: p <> indirection).
{ assert(Hx: nbLevel - 1 = l).
{
apply getNbLevelEq in Hl.
subst.
rewrite <- nbLevelEq;trivial. }
    assert(nbLevel-1 >0) .
    rewrite Hx.
    apply  levelEqBEqNatFalse0;trivial.
    symmetry;trivial.
    assert(Ht1: In indirection (getIndirectionsAux indirection s (nbLevel-1) )).
    { destruct (nbLevel-1);simpl.
    lia.
    left;trivial. }
    assert(Ht2: ~In p (getIndirectionsAux indirection s (nbLevel-1))).
    { apply getIndirectionInGetIndirections2' with vapg l;trivial.
    lia.
    unfold noDupConfigPagesList in *.
    unfold getIndirections in *.
    replace (nbLevel -1 + 1) with nbLevel by lia.
    trivial.
    apply beq_nat_false in Hdefi.
    destruct pageDefault;simpl in *;destruct p;simpl in *.
    unfold not;intros xxx;simpl in *.
    inversion xxx.
    subst.
    now contradict Hdefi.
   
lia. }

unfold not;intros;subst;now contradict Ht2. }

assert(Hpreseq: StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s')=
StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s)).
symmetry.
apply readPresentMapMMUPage with entry;trivial.
left;trivial.
assert(Haccessx: StateLib.readAccessible p (StateLib.getIndexOfAddr vapg levelMin) (memory s')=
StateLib.readAccessible p (StateLib.getIndexOfAddr vapg levelMin) (memory s)).
apply readAccessibleMapMMUPage;trivial.
left;trivial.  
assert(Hreadeq: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s')=
StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s)).
symmetry.
apply readPhyEntryMapMMUPage with entry;trivial.
left;trivial.
rewrite Hdefi.  
 rewrite <- Hpreseq.
 rewrite Hpres.
 rewrite <- Haccessx.
 rewrite Haccess.
 
 rewrite <- Hreadeq.
 rewrite Hread;trivial.
 

 - destruct Hor as (nbL & stop & HnbL & Hstop & Hind & Hnotdef & Hv).
 unfold getAccessibleMappedPage in *.
 rewrite <- HnbL in *.
 assert (Hstp: stop + 1 <= nbL).
{ subst. assert((nbL - stop) > 0).
symmetry in Hlevel.
apply levelEqBEqNatFalse0 in Hlevel ;trivial.
unfold CLevel in Hlevel.
case_eq(lt_dec (nbL - stop) nbLevel);intros * Hlt;rewrite Hlt in *.
simpl in *;trivial.
destruct nbL;simpl in *.
lia.

lia. }

assert(Hvaddr: StateLib.checkVAddrsEqualityWOOffset (stop+1) vaToPrepare vapg nbL = true \/
  StateLib.checkVAddrsEqualityWOOffset (stop+1) vaToPrepare vapg nbL = false)
  by (destruct (StateLib.checkVAddrsEqualityWOOffset);[left|right];trivial).
  destruct Hvaddr as [Hvaddr|Hvaddr].
  + assert(Hinstop1: getIndirection pd vaToPrepare nbL (stop+1) s = Some pageDefault).
    {  
       (** ici il faut montrer que indMMUToPrepare = tbl**)
    pose proof getIndirectionEqStop as Hindeq.
    assert( getIndirection pd vapg nbL stop s = Some indirection).
    rewrite <- Hind.
    symmetry.
    apply Hindeq;trivial.
    subst.
    apply checkVAddrsEqualityWOOffsetTrueLe with (stop+1);trivial.
      lia.
    apply getIndirectionProp' with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indirection entry;
    subst;trivial.
    symmetry;trivial.
    
unfold isEntryPage, StateLib.readPhyEntry in *. rewrite Hlookup in *. inversion Hdef;trivial.
    }
    assert(HindeqStopi: getIndirection pd vaToPrepare nbL (stop + 1) s=
    getIndirection pd vapg nbL (stop + 1) s).  
    apply getIndirectionEqStop;subst;trivial.
    assert(HindeqStop: getIndirection pd vaToPrepare nbL (stop + 1) s'=
    getIndirection pd vapg nbL (stop + 1) s').  
    apply getIndirectionEqStop;subst;trivial.

    unfold getAccessibleMappedPage.
    (* rewrite HindeqStop in Hinstop1. *)
    case_eq(getIndirection pd vapg nbL (nbLevel - 1) s' );intros * Hinds'; rewrite Hinds' in *;
    try now contradict Hvapg.
    case_eq(pageDefault =? p);intros * Hdefs';rewrite Hdefs' in *;try now contradict Hvapg.
    move Hind at bottom.
    assert(Hi: getIndirection pd vaToPrepare nbL (stop+1) s' = Some nextIndirection).
    { apply getIndirectionStopS1 with indirection;trivial.
    +
      rewrite <- Hind.
      symmetry.

      apply getIndirectionMapMMUPage11Stoplt with entry
;trivial.
intros * Hi1 Hi2 Hi3.

 assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
+ simpl. subst.
  rewrite <- Hlevel.
  rewrite readPhyEntryAddIndirectionSameTable.
  assert(Hnext: (pageDefault =? nextIndirection) = false) by trivial.
  rewrite Hnext.
  case_eq( StateLib.Level.pred (CLevel (nbL - stop)));intros * Hpred;trivial.
  symmetry in Hlevel.
  apply levelPredNone in Hlevel.
  now contradict Hlevel.
   }
     assert (Hnbleq: nbLevel - 1 = nbL).
      {  apply getNbLevelEq in HnbL.
      subst.
      apply nbLevelEq. }
    assert(Hor: stop + 1+1 <= nbLevel-1 \/ stop + 1+1 > nbLevel-1 ) by lia.
    destruct Hor as [Hor | Hor].
    * rewrite HindeqStop in Hi.
     
    assert(Hii:  getIndirection pd vapg nbL (stop + 1 +1 ) s' = Some pageDefault).
    {  apply getIndirectionStopS1 with nextIndirection;trivial. lia.
        apply beq_nat_falseNot;trivial.
        simpl.
      case_eq(levelEq (CLevel (nbL - (stop + 1))) levelMin);intros * Hfst.
      apply levelEqBEqNatTrue0 in Hfst.
      rewrite <- Hnbleq in Hfst.
      unfold CLevel in Hfst.
      case_eq(lt_dec (nbLevel - 1 - (stop + 1)) nbLevel) ; intros * Hls;rewrite Hls in *;simpl in *.
      rewrite <- Hnbleq in Hstp.
      lia.
      lia.
      rewrite Hv.
      assert(Hread:  StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vapg (CLevel (nbL - (stop + 1))))
      (memory s') = Some pageDefault).
      { assert(Hwell':  isWellFormedMMUTables nextIndirection s').
          apply isWellFormedMMUTablesAddIndirection with entry;trivial.
          unfold isWellFormedMMUTables in Hwell'.
          generalize (Hwell'(StateLib.getIndexOfAddr vapg (CLevel (nbL - (stop + 1)))) ) ; clear Hwell'; intros .
          intuition.
     }
     simpl in Hread.
     rewrite <- Hv.
 rewrite Hread.
 rewrite <- beq_nat_refl;trivial.
     }
    assert(Hdefx: getIndirection pd vapg nbL (nbLevel - 1) s' = Some pageDefault).
    { apply getIndirectionNbLevelEq with (stop+1 +1);trivial.
      lia.
      rewrite <- Hnbleq.
      trivial. }
      rewrite Hinds' in Hdefx.
      inversion Hdefx.
      subst.
      rewrite <- beq_nat_refl in Hdefs'.
      now contradict Hdefx.
    *  assert(Htrueeq: stop+1 = nbL) by lia.
      rewrite Htrueeq in *.
      rewrite Hnbleq in *.
      rewrite HindeqStop in Hi.
      rewrite Hinds' in Hi.
      inversion Hi;subst.
      assert(Hconspres: StateLib.readPresent nextIndirection (StateLib.getIndexOfAddr vapg levelMin)
       (memory s') = Some false).
             assert(Hwell':  isWellFormedMMUTables nextIndirection s').
          apply isWellFormedMMUTablesAddIndirection with entry;trivial.
          unfold isWellFormedMMUTables in Hwell'.
          generalize (Hwell' (StateLib.getIndexOfAddr vapg levelMin) ) ; clear Hwell'; intros .
          intuition.
          rewrite Hconspres in *.
          now contradict Hvapg.
+ case_eq ( getIndirection pd vapg nbL (nbLevel - 1) s');intros * Hinds';rewrite Hinds' in *;try now contradict Hvapg.
  case_eq(pageDefault =? p) ; intros * Hps';rewrite Hps' in *;try now contradict Hvapg.
  assert(Heqs':  getIndirection pd vapg nbL (nbLevel - 1) s =
   getIndirection pd vapg nbL (nbLevel - 1) s').
  {  assert(Horlst: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vapg l) \/  
(StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vapg l) ) by apply indexDecOrNot.
destruct Horlst as [Horlst| Horlst].
+


 assert( Hnewvaddr: StateLib.checkVAddrsEqualityWOOffset (stop ) vaToPrepare vapg nbL = false ).
{ apply checkVAddrsEqualityWOOffsetFalseS;trivial.

 subst;trivial. }
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vapg nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
- subst.
assert(Hor: stop=0 \/ stop > 0) by lia.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
case_eq( levelEq nbL levelMin);intros * Hlvl;rewrite Hlvl in *.
rewrite CLevelIdentity' in Hlevel.
rewrite <- Hlevel in Hlvl.
now contradict Hlvl.
 now contradict Hvaddr.
* assert(Hrn: S (stop-1) = stop) by lia.
  apply pageTablesAreDifferentMiddle with (stop-1) s nbLevel pd pd nbL  vapg vaToPrepare
 stop;trivial;try rewrite Hrn;trivial.
 rewrite checkVAddrsEqualityWOOffsetPermut';trivial.
 left;trivial.
 split;trivial.
 apply getNbLevelEq;trivial.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
-
assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vapg nbL;trivial;try lia.
apply getIndirectionStopLevelGe with stop0;trivial.
lia.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vapg nbL;trivial;try lia.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
+ assert(Horstop: StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vapg nbL = true \/
StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vapg nbL = false) .
{ destruct (StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vapg nbL).
  left;trivial.
  right;trivial. }
destruct Horstop as [Hstopor| Hstopor].
**  assert(Hinstop1: getIndirection pd vaToPrepare nbL (stop+1) s = Some pageDefault).
{  
   (** ici il faut montrer que indMMUToPrepare = tbl**)
pose proof getIndirectionEqStop as Hindeq.
assert( getIndirection pd vapg nbL stop s = Some indirection).
rewrite <- Hind.
symmetry.
apply Hindeq;trivial.
subst.
apply getIndirectionProp' with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indirection entry;
subst;trivial.
symmetry;trivial.

unfold isEntryPage, StateLib.readPhyEntry in *. rewrite Hlookup in *. inversion Hdef;trivial.
}
assert(HindeqStop: getIndirection pd vaToPrepare nbL stop s=
getIndirection pd vapg nbL stop  s).

apply getIndirectionEqStop;subst;trivial.

apply getIndirectionMapMMUPage11' with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vapg nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
{ assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
 }

pose proof inclGetIndirectionsAuxLe as Hproof.
left.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
-
right.  

subst.
intuition.
rewrite <- HindeqStop in Hi1.
rewrite Hind in Hi1.
inversion  Hi1;trivial.


-
assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{
 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vapg nbL;trivial;try lia.
apply getIndirectionStopLevelGe with stop0;trivial.
lia.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }left.

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vapg nbL;trivial;try lia.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }
left.

unfold not;intros;subst;now contradict Hnotinind.
 }
**
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vapg nbL;trivial.
destruct nbL;simpl in *.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
lia.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
lia.
subst;trivial.
-

subst.
assert(Hor: stop=0 \/ stop > 0) by lia.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
inversion Hi1;subst.

inversion Hind;subst.
now contradict H.
* assert(Hrn: S (stop-1) = stop) by lia.
  apply pageTablesAreDifferentMiddle with (stop-1) s nbLevel pd pd nbL  vapg vaToPrepare
 stop;trivial;try rewrite Hrn;trivial.
 rewrite checkVAddrsEqualityWOOffsetPermut';trivial.
 left;trivial.
 split;trivial.
 apply getNbLevelEq;trivial.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.

-
assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vapg nbL;trivial;try lia.
apply getIndirectionStopLevelGe with stop0;trivial.
lia.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
assert(Hex: stop + 1 <= nbLevel) by lia.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vapg nbL;trivial;try lia.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
lia.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
 } }
rewrite  Heqs'.
 rewrite Hinds'.
 rewrite Hps'.
 assert(Hkey: p <> indirection \/ StateLib.getIndexOfAddr vapg levelMin <> StateLib.getIndexOfAddr vaToPrepare l).
{    subst.
    assert(Horx: stop = nbL \/ stop <> nbL) by lia.
    destruct Horx as [Horx | Horx].
    subst.
    replace (nbL - nbL) with 0 in Hlevel.
    unfold levelMin in Hlevel.
    unfold levelEq in Hlevel.
    rewrite <- beq_nat_refl in Hlevel.
    now contradict Hlevel.
    lia.
    assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }
 assert(~In p (getIndirectionsAux pd s (stop+1))).
{
pose proof nbLevelNotZero as HnbL0.
 
apply getIndirectionInGetIndirections2n with (nbLevel - 1) vapg nbL;trivial;try lia.
rewrite Heqs';trivial.
replace (nbLevel - 1 + 1) with nbLevel by lia.
unfold getIndirections in *.
trivial.
apply beq_nat_false in Hps'.
unfold not;intros;subst;now contradict Hps'. }
assert(In indirection (getIndirectionsAux pd s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
lia.
 }
 left.
 unfold not;intros;subst;now contradict H0.
 }
 
 assert(Hpres: StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s)=
 StateLib.readPresent p (StateLib.getIndexOfAddr vapg levelMin) (memory s')).
 {  apply readPresentMapMMUPage with entry;trivial. }
  assert(Haccess: StateLib.readAccessible p (StateLib.getIndexOfAddr vapg levelMin) (memory s)=
 StateLib.readAccessible p (StateLib.getIndexOfAddr vapg levelMin) (memory s')).
 { symmetry.  apply readAccessibleMapMMUPage;trivial. }
 assert(Hread: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s)=
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg levelMin) (memory s')).
 {  apply readPhyEntryMapMMUPage with entry;trivial. }
 

 rewrite  Hread.
 rewrite  Haccess.
 rewrite  Hpres.
 trivial. }
 rewrite <- Hvapg.
apply getAccessibleMappedPageAddIndirectionSh1Sh2  with nbLgen partition idxroot root entry;trivial.
intuition.
Qed.

Lemma getMappedPagesAuxAddIndirectionSSI2 s indirection nextIndirection  entry nbLgen valist pd pg (* indMMUToPrepare *) vaToPrepare partition l r w e idxroot root
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr:
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->

isPresentNotDefaultIff s ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->
 In pg  (getMappedPagesAux pd valist {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}) ->

nextEntryIsPP partition idxroot root s ->
In indirection (getIndirections root s) ->
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxPageDir pd s ->
nextIndirection <> indirection ->
                 
In pg (getMappedPagesAux pd valist s).
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hor3 Hindor3 Hprecons Hlookup Hl Hroot Hdef (* Hdef' *) Hinit Hlevel Hnodupcons.
unfold getMappedPagesAux.
intros Hgoal.
intros.
rewrite filterOptionInIff in *.
unfold getMappedPagesOption in *.
rewrite in_map_iff in *.
destruct Hgoal as (vapg & Hvapg & Hinvalist).
exists vapg;split;trivial.
apply getMappedPageSomeAddIndirectionSSI2  with indirection nextIndirection entry
nbLgen pageDefault vaToPrepare partition l r w e root idxroot phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;trivial.
unfold isEntryPage, StateLib.readPhyEntry in *. rewrite Hlookup in *. inversion Hdef;subst;f_equal;apply proof_irrelevance.
rewrite <- beq_nat_refl;trivial. 
Qed.

     

Lemma getMappedPagesAuxAddIndirectionSamePart s indirection nextIndirection  entry nbLgen valist pd pg  vaToPrepare partition l r w e
idxroot
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr root:
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->

lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->


nextEntryIsPP partition idxroot root s ->
In indirection (getIndirections root s) ->
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxPageDir pd s ->
nextIndirection <> indirection ->
In pg (getMappedPagesAux pd valist s) <->
 In pg  (getMappedPagesAux pd valist {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}).
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hor3 Hindor3 Hlookup Hl Hroot Hdef (* Hdef' *) Hinit Hlevel Hnodupcons.
unfold getMappedPagesAux.
intros.
assert(Hnodup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition idxPageDir ;trivial.
unfold noDupConfigPagesList in *.
apply Hnodupcons;trivial.
left;trivial. }
split;intros Hgoal.
eapply getMappedPagesAuxAddIndirectionSSI1 ;try eassumption ;trivial.
eapply getMappedPagesAuxAddIndirectionSSI2;try eassumption;trivial.
Qed.

Lemma getMappedPagesAddIndirectionSamePart s indirection nextIndirection  entry nbLgen  pd pg  vaToPrepare partition l r w e
idxroot
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr root:
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->

lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->


nextEntryIsPP partition idxroot root s ->
In indirection (getIndirections root s) ->
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxPageDir pd s ->
nextIndirection <> indirection ->
In pg (getMappedPages partition  s) <->
 In pg  (getMappedPages partition {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}).
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hor3 Hindor3 Hlookup Hl Hroot Hdef (* Hdef' *) Hinit Hlevel Hnodupcons.

unfold getMappedPages.
intros.
assert(Hpd:  StateLib.getPd partition (memory s) = StateLib.getPd partition (memory s')).
symmetry.
apply getPdMapMMUPage with entry;trivial.
rewrite <- Hpd.
case_eq( StateLib.getPd partition (memory s) );intros * Hp.
apply getMappedPagesAuxAddIndirectionSamePart with entry nbLgen partition idxroot phyPDChild phyMMUaddr
phySh1Child phySh1addr phySh2Child phySh2addr root;trivial.
apply nextEntryIsPPgetPd;trivial.
split;trivial.
Qed.


Lemma getMappedPageEqAddIndirectionNotSamePart s  indirection nextIndirection  entry nbLgen a pd   vaToPrepare partition l r w e idxroot
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr:
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->

lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->


partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxroot pd s ->
nextIndirection <> indirection ->

forall part pdpart,
part <> partition ->
In part (getPartitions pageRootPartition s) ->
nextEntryIsPP part idxPageDir pdpart s ->
getMappedPage pdpart s a = getMappedPage pdpart {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |} a.
Proof.
intros Hor3 Hindor3.
set(s':= {|
  currentPartition := _ |}).
intros.
unfold getMappedPage.
case_eq(StateLib.getNbLevel);intros;trivial.
assert(Hin2: In indirection (getConfigPages partition s)).
{ right.
 destruct Hor3 as [Hor3 | [Hor3 | Hor3]];subst.
  + apply inGetIndirectionsAuxInConfigPagesPD with pd;trivial.
  apply indirectionDescriptionInGetIndirections with partition vaToPrepare l idxPageDir;trivial.
  left;trivial.
  apply nextEntryIsPPgetPd;trivial.
  + apply inGetIndirectionsAuxInConfigPagesSh1 with pd;trivial.
  apply indirectionDescriptionInGetIndirections with partition vaToPrepare l idxShadow1;trivial.
  right;left;trivial.
  apply nextEntryIsPPgetFstShadow;trivial.
  + apply inGetIndirectionsAuxInConfigPagesSh2 with pd;trivial.
  apply indirectionDescriptionInGetIndirections with partition vaToPrepare l idxShadow2;trivial.
  right;right;trivial.
  apply nextEntryIsPPgetSndShadow;trivial. }
assert(Hdisjoint: configTablesAreDifferent s) by trivial.
unfold configTablesAreDifferent in *.
assert(Hpartx : In part (getPartitions pageRootPartition s)) by trivial.
assert(Hpart:In partition (getPartitions pageRootPartition s)) by trivial.
assert(Hor:part <> partition) by trivial.
assert(Hind : getIndirection pdpart a l0 (nbLevel - 1) s  =
getIndirection pdpart a l0 (nbLevel - 1) s').
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.

assert(Hin1: In tbl (getConfigPages part s)).
{ unfold getConfigPages.
  simpl. right.
  apply inGetIndirectionsAuxInConfigPagesPD with pdpart;trivial.
  apply getIndirectionInGetIndirections with a l0 stop;trivial.
  apply nbLevelNotZero.
  apply beq_nat_falseNot;trivial.
  apply getNbLevelLe;trivial.
  symmetry;trivial.
  apply pdPartNotNull with part s;trivial.
  apply nextEntryIsPPgetPd;trivial.
  }
generalize(Hdisjoint part partition Hpartx Hpart Hor);clear Hdisjoint;intros Hdisjoint.
unfold disjoint in *.
contradict Hin2.
unfold getConfigPages in *.
apply Hdisjoint.
subst;trivial.
apply pdPartNotNull with part s;trivial.
rewrite <- Hind. clear Hind.
case_eq(getIndirection pdpart a l0 (nbLevel - 1) s);intros * Hind;trivial.
case_eq(pageDefault =? p);intros * Hp;trivial.
assert( p <> indirection).
{
assert(Hin1: In p (getConfigPages part s)).
{ unfold getConfigPages.
  simpl. right.
  apply inGetIndirectionsAuxInConfigPagesPD with pdpart;trivial.
  apply getIndirectionInGetIndirections with a l0 (nbLevel - 1);trivial.
  apply nbLevelNotZero.
  apply beq_nat_falseNot;trivial.
  apply getNbLevelLe;trivial.
  symmetry;trivial.
  apply pdPartNotNull with part s;trivial.
  apply nextEntryIsPPgetPd;trivial.
  }
generalize(Hdisjoint part partition Hpartx Hpart Hor);clear Hdisjoint;intros Hdisjoint.
unfold disjoint in *.
contradict Hin2.
unfold getConfigPages in *.
apply Hdisjoint.
subst;trivial.
}

 
assert(Hpres:  StateLib.readPresent p (StateLib.getIndexOfAddr a levelMin) (memory s) =
 StateLib.readPresent p (StateLib.getIndexOfAddr a levelMin) (memory s')).
 apply readPresentMapMMUPage with entry;trivial. left. trivial.
 rewrite Hpres.
assert(Hread:  StateLib.readPhyEntry p (StateLib.getIndexOfAddr a levelMin) (memory s) =
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr a levelMin) (memory s')).
 apply readPhyEntryMapMMUPage with entry;trivial. left. trivial.
 rewrite Hread.
 trivial.
Qed.

Lemma getAccessibleMappedPageEqAddIndirectionNotSamePart s  indirection 
nextIndirection  entry nbLgen a    vaToPrepare partition l lpred r w e
 idxroot root
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr :
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
nextEntryIsPP partition idxroot root s ->
In indirection (getIndirections root s) -> 
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->


partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->

nextIndirection <> indirection ->

forall part pdpart,
part <> partition ->
In part (getPartitions pageRootPartition s) ->
nextEntryIsPP part idxPageDir pdpart s ->
getAccessibleMappedPage pdpart s a = getAccessibleMappedPage pdpart {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |} a.
Proof.
set(s':= {|
  currentPartition := _ |}).
intros Hindor3 Hwell1 Hllpred Hor3.
intros.
unfold getAccessibleMappedPage.
case_eq(StateLib.getNbLevel);intros;trivial.
assert(Hin2: In indirection (getConfigPages partition s)).
{ unfold getConfigPages.
simpl;right.
 destruct Hor3 as [Hor3 | [Hor3 | Hor3]];subst.
  + apply inGetIndirectionsAuxInConfigPagesPD with root;trivial.
  apply nextEntryIsPPgetPd;trivial.
  + apply inGetIndirectionsAuxInConfigPagesSh1 with root;trivial.
  apply nextEntryIsPPgetFstShadow;trivial.
  + apply inGetIndirectionsAuxInConfigPagesSh2 with root;trivial.
  apply nextEntryIsPPgetSndShadow;trivial. }
assert(Hdisjoint: configTablesAreDifferent s) by trivial.
unfold configTablesAreDifferent in *.
assert(Hpartx : In part (getPartitions pageRootPartition s)) by trivial.
assert(Hpart:In partition (getPartitions pageRootPartition s)) by trivial.
assert(Hor:part <> partition) by trivial.
assert(Hind : getIndirection pdpart a l0 (nbLevel - 1) s  =
getIndirection pdpart a l0 (nbLevel - 1) s').
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.

assert(Hin1: In tbl (getConfigPages part s)).
{ unfold getConfigPages.
  simpl. right.
  apply inGetIndirectionsAuxInConfigPagesPD with pdpart;trivial.
  apply getIndirectionInGetIndirections with a l0 stop;trivial.
  apply nbLevelNotZero.
  apply beq_nat_falseNot;trivial.
  apply getNbLevelLe;trivial.
  symmetry;trivial.
  apply pdPartNotNull with part s;trivial.
  apply nextEntryIsPPgetPd;trivial.
  }
generalize(Hdisjoint part partition Hpartx Hpart Hor);clear Hdisjoint;intros Hdisjoint.
unfold disjoint in *.
contradict Hin2.
unfold getConfigPages in *.
apply Hdisjoint.
subst;trivial.
apply pdPartNotNull with part s;trivial.
rewrite <- Hind. clear Hind.
case_eq(getIndirection pdpart a l0 (nbLevel - 1) s);intros * Hind;trivial.
case_eq(pageDefault =? p);intros * Hp;trivial.
assert( p <> indirection).
{
assert(Hin1: In p (getConfigPages part s)).
{ unfold getConfigPages.
  simpl. right.
  apply inGetIndirectionsAuxInConfigPagesPD with pdpart;trivial.
  apply getIndirectionInGetIndirections with a l0 (nbLevel - 1);trivial.
  apply nbLevelNotZero.
  apply beq_nat_falseNot;trivial.
  apply getNbLevelLe;trivial.
  symmetry;trivial.
  apply pdPartNotNull with part s;trivial.
  apply nextEntryIsPPgetPd;trivial.
  }
generalize(Hdisjoint part partition Hpartx Hpart Hor);clear Hdisjoint;intros Hdisjoint.
unfold disjoint in *.
contradict Hin2.
unfold getConfigPages in *.
apply Hdisjoint.
subst;trivial.
}

 
assert(Hpres:  StateLib.readPresent p (StateLib.getIndexOfAddr a levelMin) (memory s) =
 StateLib.readPresent p (StateLib.getIndexOfAddr a levelMin) (memory s')).
 apply readPresentMapMMUPage with entry;trivial. left. trivial.
 rewrite Hpres.
assert(Haccess:  StateLib.readAccessible p (StateLib.getIndexOfAddr a levelMin) (memory s) =
 StateLib.readAccessible p (StateLib.getIndexOfAddr a levelMin) (memory s')).
 symmetry.
 apply readAccessibleMapMMUPage ;trivial. left. trivial.
 rewrite Haccess.
assert(Hread:  StateLib.readPhyEntry p (StateLib.getIndexOfAddr a levelMin) (memory s) =
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr a levelMin) (memory s')).
 apply readPhyEntryMapMMUPage with entry;trivial. left. trivial.
 rewrite Hread.
 trivial.
Qed.
Lemma getMappedPagesAuxAddIndirectionNotSamePart s  indirection nextIndirection  entry nbLgen valist pd   vaToPrepare partition idxroot l r w e
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->

Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->

partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxroot pd s ->
nextIndirection <> indirection ->

forall part pdpart,
part <> partition ->
In part (getPartitions pageRootPartition s) ->
nextEntryIsPP part idxPageDir pdpart s ->
getMappedPagesAux pdpart valist s = getMappedPagesAux pdpart valist {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}.
Proof.
intros Hlookup.
intros.
set(s':=  {|
  currentPartition := _ |}).
unfold getMappedPagesAux.
f_equal.
unfold getMappedPagesOption.
induction valist;simpl;trivial.
f_equal;trivial.
apply getMappedPageEqAddIndirectionNotSamePart with entry nbLgen pd  partition idxroot  
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr part ;trivial.
Qed.



Lemma getMappedPagesAuxAddIndirection s indirection nextIndirection  entry nbLgen valist pd pg (* indMMUToPrepare *) vaToPrepare partition l r w e idxroot
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr:
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l)
       (memory s) = Some pageDefault ->
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->

In indirection (getIndirections pd s) ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxroot pd s ->
nextIndirection <> indirection ->

forall part pdpart,
In part (getPartitions pageRootPartition s) ->
nextEntryIsPP part idxPageDir pdpart s ->
In pg (getMappedPagesAux pdpart valist s) <->
 In pg  (getMappedPagesAux pdpart valist {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}).
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hor3 Hindor3 Hlookup Hl Hroot Hdef (* Hdef' *) Hinit Hlevel Hnodupcons.
intros.
assert(Hnodup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition idxroot ;trivial.
unfold noDupConfigPagesList in *.
apply Hnodupcons;trivial.
 }
assert(Hor: part = partition \/ part <> partition) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
+ subst.
unfold getMappedPagesAux.
split;intros Hgoal.
eapply getMappedPagesAuxAddIndirectionSSI1;try eassumption;trivial.

eapply getMappedPagesAuxAddIndirectionSSI2;try eassumption;trivial.
+ assert(Heq: getMappedPagesAux pdpart valist s = getMappedPagesAux pdpart valist s').
  apply  getMappedPagesAuxAddIndirectionNotSamePart with entry nbLgen pd
 partition idxroot  
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr part;trivial.
rewrite Heq.  split;intros Hgoal;trivial.
Qed.





Lemma checkChildAddIndirectionSamePartPdSh2 indirection idx  vavalue nextIndirection idxroot nbLgen part  e w r entry pd s:
 or2 idxroot ->
lookup indirection idx (memory s) pageEq idxEq = Some (PE entry) ->
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
nextEntryIsPP part idxroot pd s ->
In indirection (getIndirections pd s) ->
In part (getPartitions pageRootPartition s)  ->
Some nbLgen = StateLib.getNbLevel ->
 checkChild part nbLgen s vavalue  =
checkChild part nbLgen  {|
  currentPartition := currentPartition s;
  memory := add indirection  idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present :=true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |} vavalue .
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hor Hlookup Hpde Hconfdiff Hpd Hkey Hpart Hnbl.
unfold checkChild.
simpl.
assert(Hgetsh1 : forall part, StateLib.getFstShadow part (memory s) =
 StateLib.getFstShadow part
    (add indirection  idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq )).
{ intros. symmetry.
  apply getFstShadowMapMMUPage with entry;trivial. }
rewrite <- Hgetsh1. clear Hgetsh1.
 unfold noDupConfigPagesList in *.
generalize(Hconfdiff part Hpart);clear Hconfdiff; intros Hconfdiff.
unfold getConfigPages in Hconfdiff.
apply NoDup_cons_iff in Hconfdiff.
destruct Hconfdiff as (_ & Hconfdiff).
unfold getConfigPagesAux in *.
pose proof pdSh1Sh2ListExistsNotNull as Hprof.
generalize(Hprof s Hpde part Hpart);clear Hprof;intros Hprof.
apply pdSh1Sh2ListExistsNotNull  with s part in Hpde.
destruct Hpde as ((pd1 & Hpd1 & Hpdnotnull)
  & (sh1 & Hsh1 & Hsh1notnull) & (sh2 & Hsh2 & Hsh2notnull) &
  (sh3 & Hsh3 & Hsh3notnull)).
unfold getConfigPages.
unfold getConfigPagesAux.
rewrite Hpd1, Hsh1, Hsh2, Hsh3 in Hconfdiff.
(* assert(pd = pd1).
apply getPdNextEntryIsPPEq with part s;trivial.
subst pd1. *)
rewrite Hsh1.
assert(Hind : getIndirection sh1 vavalue nbLgen (nbLevel - 1) s  =
getIndirection sh1 vavalue nbLgen (nbLevel - 1) s' ).
{ apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
apply NoDupSplitInclIff in Hconfdiff.
destruct Hconfdiff as (Hconfigdiff1 & Hconfdiff).
unfold disjoint in *.
destruct Hor as [Hor|Hor];subst.
+  assert(pd = pd1).
apply getPdNextEntryIsPPEq with part s;trivial.
subst pd1. 
apply Hconfdiff in Hkey.
clear Hconfdiff.
rewrite in_app_iff in Hkey.
apply not_or_and in Hkey.
destruct Hkey as (Hkey & _).
assert (Hkey2: In tbl (getIndirections sh1 s)).
apply getIndirectionInGetIndirections with vavalue nbLgen stop;trivial.
apply nbLevelNotZero.
apply beq_nat_falseNot;trivial.
apply getNbLevelLe;trivial.
unfold not;intros;subst;try now contradict Hkey2.
+  assert(pd = sh2).
apply getSh2NextEntryIsPPEq with part s;trivial.
subst pd.
destruct Hconfigdiff1 as (Hconfigdiff1 & Hconfigdiff2).
apply NoDupSplitInclIff in Hconfigdiff2.
 destruct Hconfigdiff2 as ( _ & Hconfigdiff2).
unfold disjoint in *.

assert (Hkey2: In tbl (getIndirections sh1 s)).
apply getIndirectionInGetIndirections with vavalue nbLgen stop;trivial.
apply nbLevelNotZero.
apply beq_nat_falseNot;trivial.
apply getNbLevelLe;trivial.
unfold not;intros;subst;try now contradict Hkey2.

apply Hconfigdiff2 in Hkey2.
rewrite in_app_iff in Hkey2.
apply not_or_and in Hkey2.
destruct Hkey2 as (Hkey2 & _).
now contradict Hkey2.
  }
  rewrite <- Hind.  
case_eq(getIndirection sh1 vavalue nbLgen (nbLevel - 1) s);intros * Hp;rewrite Hp in *.
 case_eq( p =? pageDefault);intros * Hdef;trivial.
assert(Hpdflag: StateLib.readPDflag p (StateLib.getIndexOfAddr vavalue levelMin) (memory s) =
 StateLib.readPDflag p (StateLib.getIndexOfAddr vavalue levelMin)
    (add indirection idx
       (PE
          {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
       (memory s) pageEq idxEq)).
       symmetry.
       apply readPDflagMapMMUPage with entry;trivial.
     rewrite Hpdflag;trivial.
     trivial.
     trivial.
Qed.
Lemma getIndirectionAddIndirectionCheckVaddrsFalseGen s vaToPrepare l sh1 nextIndirection vavalue e w r entry:
let s':={|
currentPartition := currentPartition s;
memory := add sh1 (StateLib.getIndexOfAddr vaToPrepare l)
          (PE
             {| 
             read := r;
             write := w;
             exec := e;
             present := true;
             user := true;
             pa := nextIndirection |}) (memory s) pageEq idxEq |}  in 
lookup sh1 (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
StateLib.getIndexOfAddr vaToPrepare l <> StateLib.getIndexOfAddr vavalue l ->
sh1 <> pageDefault -> 
levelEq l levelMin = false -> 
 NoDup (getIndirections sh1 s) -> 
 Some l = StateLib.getNbLevel -> 
getIndirection sh1 vavalue l (nbLevel - 1) s = getIndirection sh1 vavalue l (nbLevel - 1) s'.
Proof.
intros * Hlookup Hidxeq Hrootnotdef Hlevel Hnodup HnbL.
destruct (nbLevel - 1); simpl. trivial.
case_eq (levelEq l levelMin); intros * Hflst;trivial.
assert(Hread': StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr vavalue l)
(add sh1 (StateLib.getIndexOfAddr vaToPrepare l)
     (PE
        {|
        read := r;
        write := w;
        exec := e;
        present := true;
        user := true;
        pa := nextIndirection |}) (memory s) pageEq idxEq)=
StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr vavalue l) (memory s)).
{ symmetry. apply readPhyEntryMapMMUPage with entry;trivial.
  right;trivial.
  intuition. }
rewrite Hread'.
case_eq(StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr vavalue l) (memory s));intros;trivial.        
case_eq(pageDefault =? p);intros notdef;trivial.
case_eq ( StateLib.Level.pred l);intros * Hlpred;trivial.  
apply getIndirectionMapMMUPage11 with entry;trivial.
intros.
{ pose proof indirectionNotInPreviousMMULevelAux.
  assert(Hor: stop < l \/ stop >= l) by lia.
  destruct Hor as [Hor | Hor].
  * generalize(H2 vavalue s (S stop) sh1 l tbl);clear H2;intros H2.
    replace (S stop - 1) with stop in * by lia.
    assert(Hprevious: exists prevtab : page,
    getIndirection sh1 vavalue l stop s = Some prevtab /\
    prevtab <> pageDefault /\
    StateLib.readPhyEntry prevtab (StateLib.getIndexOfAddr vavalue (CLevel (l - stop))) (memory s) = Some tbl).
    { apply H2;clear H2;try lia.
    intuition.
    simpl.
    rewrite Hlevel.
    rewrite H.
    rewrite notdef.
    rewrite Hlpred;trivial.
    trivial. }
    destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev).
    assert(~ In tbl (getIndirectionsAux sh1 s (stop + 1))).
    { apply getIndirectionInGetIndirections2 with prevtab vavalue l;
    simpl; subst;
    trivial.
    destruct l;simpl in *.
    lia.
    replace(stop + 1 - 1) with stop in * by lia.
    trivial.
    replace(stop + 1 - 1) with stop in * by lia.
    trivial.

    unfold getIndirections in Hnodup.
    apply noDupPreviousMMULevels with nbLevel.
    trivial.
    destruct l.
    simpl in *.
    lia.
    assert((pageDefault =? tbl) = false) as Hnotdef  by trivial.
    apply beq_nat_false in Hnotdef.
    unfold not;intros;subst.
    now contradict Hnotdef.
    destruct l.
    simpl in *.
    lia.
    }
    assert( In sh1 (getIndirectionsAux sh1 s (stop + 1))).
    { replace  (stop + 1) with (S stop) by lia.
    simpl.
    left;trivial. }
    unfold not;intros.
    subst.
    now contradict H4.
    * assert(getIndirection p vavalue l0 (nbLevel -2) s = Some tbl ).
    unfold StateLib.Level.pred in *.
    case_eq( gt_dec l 0);intros * Hl0;rewrite Hl0 in *; try now contradict Hlpred.
    inversion Hlpred.
    apply getIndirectionStopLevelGT2 with stop;simpl in *;
    subst;trivial.
    lia.
    assert(Hlx: l = CLevel (nbLevel - 1)).
    apply getNbLevelEq;trivial.
    pose proof nbLevelEq as Heq.
    rewrite <- Hlx in Heq.
    rewrite <- Heq.
    lia.
    generalize(H2 vavalue s (nbLevel - 1) sh1 l tbl);clear H2;intros H2.
    (*   replace (S stop - 1) with stop in * by lia.
    *)
    assert(Hlx: l = CLevel (nbLevel - 1)).
    apply getNbLevelEq;trivial.
    pose proof nbLevelEq as Heq.
    rewrite <- Hlx in Heq.

    pose proof nbLevelNotZero as nblnot0.
    assert(l > 0).
    apply levelEqBEqNatFalse0;trivial.
    assert(Hprevious: exists prevtab : page,
    getIndirection sh1 vavalue l (nbLevel - 1 -1) s = Some prevtab /\
    prevtab <> pageDefault /\
    StateLib.readPhyEntry prevtab (StateLib.getIndexOfAddr vavalue (CLevel (l - (nbLevel - 1 - 1)))) (memory s) = Some tbl).
    { apply H2;clear H2;try lia.
    intuition.
    replace (nbLevel - 1) with (nbLevel - 2 + 1) by lia.
    clear H0.
    replace (nbLevel - 2 + 1) with (S (nbLevel - 2)) by lia.
    simpl.
    rewrite Hlevel.
    rewrite H.
    rewrite notdef.
    rewrite Hlpred;trivial.
    trivial. }
    destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev).
    assert(~ In tbl (getIndirectionsAux sh1 s ((nbLevel - 2) + 1))).
    { apply getIndirectionInGetIndirections2 with prevtab vavalue l;
    simpl; subst;
    trivial.
    replace (nbLevel - 1) with (nbLevel - 2 + 1) by lia.
    clear H0.
    lia.
    replace(nbLevel - 2 + 1 - 1) with  (nbLevel - 1 - 1) in * by lia.
    trivial.

    replace(nbLevel - 2 + 1 - 1) with  (nbLevel - 1 - 1) in * by lia.
    trivial.
    replace(nbLevel - 2 + 1 + 1) with  (nbLevel )  by lia.
    unfold getIndirections in Hnodup.
    trivial.
    assert((pageDefault =? tbl) = false) as Hnotdef  by trivial.
    apply beq_nat_false in Hnotdef.
    unfold not;intros;subst.
    now contradict Hnotdef.
    replace(nbLevel - 2 + 1) with  (nbLevel - 1 ) in * by lia.
    lia.
    }
    assert( In sh1 (getIndirectionsAux sh1 s (nbLevel - 2 + 1))) .
    { replace (nbLevel - 2 + 1) with (S(nbLevel -2)) by lia.
    simpl.
    left;trivial. }
    unfold not;intros.
    subst.
    now contradict H4. }
  * apply beq_nat_false in notdef.
    intuition.
    subst. now contradict notdef.
Qed.

Lemma checkChildAddIndirectionSamePartSh1 indirection   vavalue nextIndirection 
vaToPrepare nbLgen part  e w r entry sh1 l lpred s b:
lookup indirection  (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
nextEntryIsPP part idxShadow1 sh1 s ->
In indirection (getIndirections sh1 s) ->
indirectionDescription s part indirection idxShadow1 vaToPrepare l ->
In part (getPartitions pageRootPartition s)  ->
Some nbLgen = StateLib.getNbLevel ->
levelEq l levelMin = false ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault ->
StateLib.Level.pred l = Some lpred ->
isWellFormedFstShadow lpred nextIndirection s ->
 checkChild part nbLgen s vavalue  = b ->
 (pageDefault =? nextIndirection) = false ->
 nextIndirection <> indirection ->
checkChild part nbLgen  {|
  currentPartition := currentPartition s;
  memory := add indirection   (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present :=true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |} vavalue = b.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros  Hlookup Hpde Hconfdiff Hcons1 Hcons2 Hcons3 Hpd Hkey Hroot Hpart Hl Hlevel Hread Hwell1 Hwell2 Hvapg
Hnextnotdef Hindnoteq.
unfold checkChild in *.
simpl.
assert(Hgetsh1 : forall part, StateLib.getFstShadow part (memory s) =
 StateLib.getFstShadow part
    (add indirection   (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq )).
{ intros. symmetry.
  apply getFstShadowMapMMUPage with entry;trivial. }
rewrite <- Hgetsh1. 

 unfold noDupConfigPagesList in *.
generalize(Hconfdiff part Hpart);clear Hconfdiff; intros Hconfdiff.
rewrite nextEntryIsPPgetFstShadow in *.
rewrite Hpd in *.
assert(Hnodup : NoDup (getIndirections sh1 s)).
{ eapply noDupConfigPagesListNoDupGetIndirections with part idxShadow1 ;trivial.
right;left;trivial.
apply nextEntryIsPPgetFstShadow;trivial. }
move Hgetsh1 at top.
unfold indirectionDescription,  initPEntryTablePreconditionToPropagatePrepareProperties in *.
destruct Hroot as (tableroot & Hpp & Hrootnotdef & Hor).
assert(Hpdor: tableroot=sh1).
{ apply getSh1NextEntryIsPPEq with part s;trivial. }
subst tableroot.
(* generalize (Hread (StateLib.getIndexOfAddr vaToPrepare l));clear Hread;intros Hread.   *)
destruct Hor as [(Heq & HnbL) | (nbL & stop & HnbL & Hstop & Hindi & Hnotdef & Hstopl)].
+ subst indirection;rewrite <- HnbL in *.
  inversion Hl;subst nbLgen.
  assert(Hvaddr: StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vavalue l = true \/
  StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vavalue l = false)
  by (destruct (StateLib.checkVAddrsEqualityWOOffset);[left|right];trivial).
  destruct Hvaddr as [Hvaddr|Hvaddr].
  - destruct b.
    * case_eq(getIndirection sh1 vavalue l (nbLevel - 1) s );[intros tbl Htbl |intros Htbl]; rewrite Htbl in *;
      try now contradict Hvapg. (** ici il faut montrer que indMMUToPrepare = tbl**)
      case_eq(tbl =? pageDefault);intros Hinddef;rewrite Hinddef in *;try now contradict Hvapg.
      assert(Hind :  getIndirection sh1 vaToPrepare l (nbLevel - 1) s = Some pageDefault).
      { apply getIndirectionNbLevelEq with 1; try lia.
      apply getNbLevelEq in HnbL.
      subst.
      inversion Hl;subst.
      apply nbLevelEq.
      apply levelEqBEqNatFalse0 in Hlevel.
      lia.
      simpl.
      rewrite  Hlevel.
      rewrite Hread.
      rewrite <- beq_nat_refl;trivial. }
      assert(Htrue : getIndirection sh1 vavalue l (nbLevel - 1) s =
      getIndirection sh1 vaToPrepare l (nbLevel - 1) s).
      { symmetry.
        apply getIndirectionEq;trivial.
        destruct l;simpl;lia. }
      rewrite Hind in Htrue.
      rewrite Htbl in Htrue.
      inversion Htrue.
      subst.
      apply beq_nat_false in Hinddef.
      lia.
    * assert(Hidxeq: (StateLib.getIndexOfAddr vavalue l) = (StateLib.getIndexOfAddr vaToPrepare l)).  
      { symmetry.
        apply checkVAddrsEqualityWOOffsetTrue' with nbLevel l;trivial.
        destruct l;simpl;lia. }
      rewrite <- Hidxeq in *.        
      destruct (nbLevel -1);simpl in *. 
      -- assert(Htru: (sh1 =? pageDefault) = false ).
       {  apply Nat.eqb_neq;trivial.  contradict Hrootnotdef.
          destruct sh1;destruct pageDefault;simpl in *.
          subst. f_equal. apply proof_irrelevance. }        
          rewrite Htru in *.
          assert(Hflag: StateLib.readPDflag sh1 (StateLib.getIndexOfAddr vavalue levelMin)
            (add sh1 (StateLib.getIndexOfAddr vavalue l)
            (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
            (memory s) pageEq idxEq) = StateLib.readPDflag sh1 (StateLib.getIndexOfAddr vavalue levelMin) (memory s)).
          { apply readPDflagMapMMUPage with entry;trivial. }          
          rewrite Hflag; trivial.
       -- rewrite Hlevel in *.
          rewrite Hread in Hvapg.
          assert(Hreadeq:  StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr vavalue l)
          (add sh1 (StateLib.getIndexOfAddr vavalue l)
          (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
          (memory s) pageEq idxEq) = Some nextIndirection ) by apply readPhyEntryAddIndirectionSameTable.
          rewrite <- Hidxeq in *. 
          rewrite Hreadeq.
          assert(Hnext:(pageDefault =? nextIndirection) = false) by trivial.
          rewrite Hnext.
          rewrite Hwell1.
          assert(Hpdflag: StateLib.readPDflag nextIndirection (StateLib.getIndexOfAddr vavalue levelMin)
            (add sh1 (StateLib.getIndexOfAddr vavalue l)
            (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
            (memory s) pageEq idxEq) = StateLib.readPDflag nextIndirection (StateLib.getIndexOfAddr vavalue levelMin) (memory s)
            ).
          { apply readPDflagMapMMUPage with entry;trivial.
           }
          destruct n;simpl;trivial.
          ++
            assert(Hnext':(nextIndirection =? pageDefault) = false).
            { apply beq_nat_false in Hnext .
            apply Nat.eqb_neq.
            intuition. }
            rewrite Hnext'.
            unfold isWellFormedFstShadow in *.
            rewrite Hpdflag.
            move Hwell2 at bottom.      
            destruct Hwell2 as [(Hlpred &Hwell2)|(Hlpred &Hwell2)].
            ** generalize(Hwell2 (StateLib.getIndexOfAddr vavalue levelMin) ); clear Hwell2; intros (Hwell2 & _).
               unfold StateLib.readPhyEntry , StateLib.readPDflag in *.
               case_eq( lookup nextIndirection (StateLib.getIndexOfAddr vavalue levelMin) (memory s) pageEq idxEq);intros *
               Hwell22;rewrite Hwell22 in *;trivial.
               destruct v;trivial.
               now contradict Hwell2.
            ** generalize(Hwell2 (StateLib.getIndexOfAddr vavalue levelMin) ); clear Hwell2; intros (_ & Hwell2).
               rewrite Hwell2;trivial.
          ++ case_eq( levelEq lpred levelMin);intros.
             ** assert(Hnext':(nextIndirection =? pageDefault) = false).
               { apply beq_nat_false in Hnext .
                 apply Nat.eqb_neq.
                 intuition. }
              rewrite Hnext'.
              rewrite Hpdflag. 
              move Hwell2 at bottom.      
              destruct Hwell2 as [(Hlpred &Hwell2)|(Hlpred &Hwell2)].
              generalize(Hwell2 (StateLib.getIndexOfAddr vavalue levelMin) ); clear Hwell2; intros (Hwell2 & _).
              unfold StateLib.readPhyEntry , StateLib.readPDflag in *.
              case_eq( lookup nextIndirection (StateLib.getIndexOfAddr vavalue levelMin) (memory s) pageEq idxEq);intros *
              Hwell22;rewrite Hwell22 in *;trivial.
              destruct v;trivial.
              now contradict Hwell2.
              generalize(Hwell2 (StateLib.getIndexOfAddr vavalue levelMin) ); clear Hwell2; intros (_ & Hwell2).
              rewrite Hwell2;trivial.
             ** assert(Hup: StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vavalue lpred)
                    (add sh1 (StateLib.getIndexOfAddr vaToPrepare l)
                    (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
                    (memory s) pageEq idxEq)=
                    StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vavalue lpred) (memory s) ).
                { symmetry. apply readPhyEntryMapMMUPage with entry;trivial.
                intuition. rewrite <- Hidxeq in *;trivial. } 
                rewrite Hup.
                clear Hup.
                move Hwell2 at bottom.      
                destruct Hwell2 as [(Hlpred &Hwell2)|(Hlpred &Hwell2)].
                generalize(Hwell2 (StateLib.getIndexOfAddr vavalue lpred) ); clear Hwell2; intros (Hwell2 & _).
                rewrite Hwell2.
                assert(Hok: (pageDefault =? pageDefault) = true).
                symmetry. apply beq_nat_refl.
                rewrite Hok.
                rewrite Hok;trivial.
                generalize(Hwell2 (StateLib.getIndexOfAddr vavalue lpred) ); clear Hwell2; intros (_ & Hwell2).
                unfold StateLib.readPhyEntry , StateLib.readPDflag in *.
                case_eq( lookup nextIndirection (StateLib.getIndexOfAddr vavalue lpred) (memory s) pageEq idxEq);intros *
                Hwell22;rewrite Hwell22 in *;trivial.
                destruct v;trivial.
                now contradict Hwell2.
  - assert(Hidxeq: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vavalue l) \/
                  (StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vavalue l)) by apply indexDecOrNot.
    destruct Hidxeq as [Hidxeq |Hidxeq].
    * rewrite  Hidxeq in Hread.
      assert(Hind :  getIndirection sh1 vavalue l (nbLevel - 1) s = Some pageDefault).
      { apply getIndirectionNbLevelEq with 1; try lia.
        apply getNbLevelEq in HnbL.
        subst.
        inversion Hl;subst.
        apply nbLevelEq.
        apply levelEqBEqNatFalse0 in Hlevel.
        lia.
        simpl.
        rewrite  Hlevel.
        rewrite Hread.
        rewrite <- beq_nat_refl;trivial. } 
      destruct (nbLevel - 1); simpl in *.
      -- assert(Htru: (sh1 =? pageDefault) = false ).
       {  apply Nat.eqb_neq;trivial.  contradict Hrootnotdef.
          destruct sh1;destruct pageDefault;simpl in *.
          subst. f_equal. apply proof_irrelevance. }        
          rewrite Htru in *.
          rewrite Hidxeq.
          assert(Hflag: StateLib.readPDflag sh1 (StateLib.getIndexOfAddr vavalue levelMin)
            (add sh1 (StateLib.getIndexOfAddr vavalue l)
            (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
            (memory s) pageEq idxEq) = StateLib.readPDflag sh1 (StateLib.getIndexOfAddr vavalue levelMin) (memory s)).
          { apply readPDflagMapMMUPage with entry;trivial.
            rewrite <- Hidxeq.
            trivial. }
          rewrite Hflag; trivial.
      -- rewrite Hind in Hvapg.
          assert(Htrue : (pageDefault =? pageDefault )=true).
          symmetry. apply beq_nat_refl.
          rewrite Htrue in *.
          subst b.
          rewrite Hlevel in *.
          rewrite Hidxeq.
          assert(Hreadeq:  StateLib.readPhyEntry sh1 (StateLib.getIndexOfAddr vavalue l)
          (add sh1 (StateLib.getIndexOfAddr vavalue l)
          (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
          (memory s) pageEq idxEq) = Some nextIndirection ) by apply readPhyEntryAddIndirectionSameTable.
          rewrite Hreadeq.
          rewrite Hread in *.
          assert(Hnext:(pageDefault =? nextIndirection) = false) by trivial.
          rewrite Hnext.
          case_eq(StateLib.Level.pred l );intros;trivial.
          assert(Hpdflag: StateLib.readPDflag nextIndirection (StateLib.getIndexOfAddr vavalue levelMin)
            (add sh1 (StateLib.getIndexOfAddr vavalue l)
            (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
            (memory s) pageEq idxEq) = StateLib.readPDflag nextIndirection (StateLib.getIndexOfAddr vavalue levelMin) (memory s)
            ).
          { apply readPDflagMapMMUPage with entry;trivial.
            rewrite <- Hidxeq. trivial. }
          destruct n;simpl;trivial.
          ++
            assert(Hnext':(nextIndirection =? pageDefault) = false).
            { apply beq_nat_false in Hnext .
            apply Nat.eqb_neq.
            intuition. }
            rewrite Hnext'.
            unfold isWellFormedFstShadow in *.
            rewrite Hpdflag.
            move Hwell2 at bottom.      
            destruct Hwell2 as [(Hlpred &Hwell2)|(Hlpred &Hwell2)].
            ** generalize(Hwell2 (StateLib.getIndexOfAddr vavalue levelMin) ); clear Hwell2; intros (Hwell2 & _).
               unfold StateLib.readPhyEntry , StateLib.readPDflag in *.
               case_eq( lookup nextIndirection (StateLib.getIndexOfAddr vavalue levelMin) (memory s) pageEq idxEq);intros *
               Hwell22;rewrite Hwell22 in *;trivial.
               destruct v;trivial.
               now contradict Hwell2.
            ** generalize(Hwell2 (StateLib.getIndexOfAddr vavalue levelMin) ); clear Hwell2; intros (_ & Hwell2).
               rewrite Hwell2;trivial.
          ++ case_eq( levelEq l0 levelMin);intros.
             ** assert(Hnext':(nextIndirection =? pageDefault) = false).
               { apply beq_nat_false in Hnext .
                 apply Nat.eqb_neq.
                 intuition. }
              rewrite Hnext'.
              rewrite Hpdflag. 
              move Hwell2 at bottom.      
              destruct Hwell2 as [(Hlpred &Hwell2)|(Hlpred &Hwell2)].
              generalize(Hwell2 (StateLib.getIndexOfAddr vavalue levelMin) ); clear Hwell2; intros (Hwell2 & _).
              unfold StateLib.readPhyEntry , StateLib.readPDflag in *.
              case_eq( lookup nextIndirection (StateLib.getIndexOfAddr vavalue levelMin) (memory s) pageEq idxEq);intros *
              Hwell22;rewrite Hwell22 in *;trivial.
              destruct v;trivial.
              now contradict Hwell2.
              generalize(Hwell2 (StateLib.getIndexOfAddr vavalue levelMin) ); clear Hwell2; intros (_ & Hwell2).
              rewrite Hwell2;trivial.
             ** assert(Hup: StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vavalue l0)
                    (add sh1 (StateLib.getIndexOfAddr vaToPrepare l)
                    (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
                    (memory s) pageEq idxEq)=
                    StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vavalue l0) (memory s) ).
                { symmetry. apply readPhyEntryMapMMUPage with entry;trivial.
                intuition. } 
                rewrite Hup.
                clear Hup.
                move Hwell2 at bottom.      
                destruct Hwell2 as [(Hlpred &Hwell2)|(Hlpred &Hwell2)].
                generalize(Hwell2 (StateLib.getIndexOfAddr vavalue l0) ); clear Hwell2; intros (Hwell2 & _).
                rewrite Hwell2.
                assert(Hok: (pageDefault =? pageDefault) = true).
                symmetry. apply beq_nat_refl.
                rewrite Hok.
                rewrite Hok;trivial.
                generalize(Hwell2 (StateLib.getIndexOfAddr vavalue l0) ); clear Hwell2; intros (_ & Hwell2).
                unfold StateLib.readPhyEntry , StateLib.readPDflag in *.
                case_eq( lookup nextIndirection (StateLib.getIndexOfAddr vavalue l0) (memory s) pageEq idxEq);intros *
                Hwell22;rewrite Hwell22 in *;trivial.
                destruct v;trivial.
                now contradict Hwell2.
    * assert (Hindeq: getIndirection sh1 vavalue l (nbLevel - 1) s = getIndirection sh1 vavalue l (nbLevel - 1) s').
      { clear Hvapg.  
        apply getIndirectionAddIndirectionCheckVaddrsFalseGen with entry;trivial.  }
      rewrite <- Hindeq.
      case_eq( getIndirection sh1 vavalue l (nbLevel - 1) s);intros * Htbl;trivial;rewrite Htbl in *.
      case_eq( p =? pageDefault); intros * Hp;rewrite Hp in *;trivial.
      assert( sh1 <>p).
      assert(Hlx: l = CLevel (nbLevel - 1)).
      apply getNbLevelEq;trivial.
      pose proof nbLevelEq as Heq.
      rewrite <- Hlx in Heq.
      assert(Ll: l> 0).
      apply levelEqBEqNatFalse0;trivial.
      assert(Hin:~ In p (getIndirectionsAux sh1 s (nbLevel - 1))).
      { apply indirectionNotInPreviousMMULevel' with (StateLib.getIndexOfAddr vavalue levelMin)
            vavalue part l idxShadow1;trivial.
        right;left;trivial.
        symmetry;trivial.
        apply beq_nat_false in Hp.
        apply Nat.eqb_neq.
        intuition.
        subst;trivial.
        rewrite Heq;trivial. }
      assert( In sh1 (getIndirectionsAux sh1 s (nbLevel - 1))) .
      subst.
      destruct (nbLevel - 1);simpl.
      subst.
      lia.
      left;trivial.
      unfold not;intros.
      subst.
      now contradict Hin.
      assert(Hpdflag: StateLib.readPDflag p (StateLib.getIndexOfAddr vavalue levelMin) (memory s') =
      StateLib.readPDflag p (StateLib.getIndexOfAddr vavalue levelMin) (memory s)).
      apply readPDflagMapMMUPage with entry;trivial.
      simpl in Hpdflag.
      rewrite  Hpdflag;trivial.
      trivial.
+ rewrite <- HnbL in *.
  inversion Hl;subst nbLgen.
  assert (Hstp: stop + 1 <= nbL).
  { subst. assert((nbL - stop) > 0).
    apply levelEqBEqNatFalse0 in Hlevel ;trivial.
    unfold CLevel in Hlevel.
    case_eq(lt_dec (nbL - stop) nbLevel);intros * Hlt;rewrite Hlt in *.
    simpl in *;trivial.
    destruct nbL;simpl in *.
    lia. lia. }
  assert(Hvaddr: StateLib.checkVAddrsEqualityWOOffset (stop+1) vaToPrepare vavalue nbL = true \/
  StateLib.checkVAddrsEqualityWOOffset (stop+1) vaToPrepare vavalue nbL = false)
  by (destruct (StateLib.checkVAddrsEqualityWOOffset);[left|right];trivial).
  destruct Hvaddr as [Hvaddr|Hvaddr].
  - assert(Hinstop1: getIndirection sh1 vaToPrepare nbL (stop+1) s = Some pageDefault).
    {  (** ici il faut montrer que indMMUToPrepare = tbl**)
      pose proof getIndirectionEqStop as Hindeq.
      assert( getIndirection sh1 vavalue nbL stop s = Some indirection).
      rewrite <- Hindi.
      symmetry.
      apply Hindeq;trivial.
      subst.
      apply checkVAddrsEqualityWOOffsetTrueLe with (stop+1);trivial.
      lia.
      apply getIndirectionProp' with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indirection entry;
      subst;trivial.
      unfold 
      isEntryPage, StateLib.readPhyEntry in *.
      destruct ( lookup indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) (memory s) pageEq idxEq );simpl in *;trivial;
      try now contradict Hread.
      destruct v;try now contradict Hread.
      inversion Hread;trivial.  }
  assert(HindeqStopi: getIndirection sh1 vaToPrepare nbL (stop + 1) s=
  getIndirection sh1 vavalue nbL (stop + 1) s) by ( apply getIndirectionEqStop;subst;trivial).
  assert(HindeqStop: getIndirection sh1 vaToPrepare nbL (stop + 1) s'=
   getIndirection sh1 vavalue nbL (stop + 1) s') by ( apply getIndirectionEqStop;subst;trivial).
  destruct b.
  { assert(Hind :  getIndirection sh1 vavalue nbL (nbLevel - 1) s = Some pageDefault).
    { apply getIndirectionNbLevelEq with (stop+1); try lia.
        apply getNbLevelEq in HnbL.
        subst.
        inversion Hl;subst.
        apply nbLevelEq.
        rewrite <- Hinstop1.
        symmetry.
        apply getIndirectionEqStop;trivial. }
     rewrite Hind in Hvapg.
     rewrite <- beq_nat_refl in Hvapg.
     now contradict Hvapg.
   }
    case_eq(getIndirection sh1 vavalue nbL (nbLevel - 1) s' );intros * Hinds';trivial.
    case_eq(p =? pageDefault);intros * Hdefs';trivial.
    assert(Hi: getIndirection sh1 vaToPrepare nbL (stop+1) s' = Some nextIndirection).
    { apply getIndirectionStopS1 with indirection;trivial.
      + rewrite <- Hindi.
        symmetry. apply getIndirectionMapMMUPage11Stoplt with entry;trivial.
        intros * Hi1 Hi2 Hi3.
        assert(Hinind: In tbl (getIndirectionsAux sh1  s (stop0+1))).
        { apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
          destruct nbL;simpl in *.
          lia.
          apply beq_nat_false in Hi2.
          unfold not;intros;subst;now contradict Hi2.
         }
        assert(Hnotinind: ~ In indirection (getIndirectionsAux sh1 s (stop))).
        assert(Hex: stop + 1 <= nbLevel).
        destruct nbL;simpl in *.
        lia.
        apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
        unfold getIndirections in *.
        apply noDupPreviousMMULevels with nbLevel ;trivial.
        lia.
        pose proof inclGetIndirectionsAuxLe as Hproof.
        contradict Hnotinind.
        unfold incl in Hproof.
        apply Hproof with (stop0+1).
        lia.
        subst;trivial.
      + simpl. subst.
        rewrite Hlevel.
        rewrite readPhyEntryAddIndirectionSameTable.
        assert(Hnext: (pageDefault =? nextIndirection) = false) by trivial.
        rewrite Hnext.
        case_eq( StateLib.Level.pred (CLevel (nbL - stop)));intros * Hpred;trivial.
        symmetry in Hlevel.
        symmetry in Hlevel.
        apply levelPredNone in Hlevel.
        now contradict Hlevel. }
     assert (Hnbleq: nbLevel - 1 = nbL).
      {  apply getNbLevelEq in HnbL.
      subst.
      apply nbLevelEq. }
       assert(Hwell':  isWellFormedFstShadow lpred nextIndirection s').
        apply isWellFormedFstShadowTablesAddIndirection with entry;trivial.
    assert(Hor: stop + 1+1 <= nbLevel-1 \/ stop + 1+1 > nbLevel-1 ) by lia.
    destruct Hor as [Hor | Hor].
    * rewrite HindeqStop in Hi.
      assert (Hlvlpred: lpred = levelMin \/ lpred <> levelMin ) by  apply levelDecOrNot.
      destruct Hlvlpred. 
      ++ subst.
         assert((CLevel (nbL - stop)) -1 = 0).
         {  eapply levelPredMinus1  in Hwell1.
          unfold levelMin in *. (* 
          SearchAbout CLevel.
          assert(0 = (CLevel (nbL - stop) - 1) ).*) 
          
          move Hwell1 at bottom.
          { unfold CLevel at 3 in Hwell1.
            unfold CLevel.
          case_eq(lt_dec (nbL - stop) nbLevel );intros * Hxx;rewrite Hxx in *;simpl in *;
          [|destruct nbL;simpl in *;
          lia].
          unfold CLevel at 2 in Hwell1.
          case_eq(lt_dec (nbL - stop - 1) nbLevel  );intros * Hxxx;rewrite Hxxx in *;
          [|destruct nbL;simpl in *;
          lia].
          unfold CLevel in Hwell1.
          pose proof nbLevelNotZero.
          case_eq(lt_dec 0 nbLevel);intros * Hii; rewrite Hii in *;try lia.
          inversion Hwell1;trivial. }
          
          trivial. }
         assert(( (nbL - stop)) -1 = 0).
         {  eapply levelPredMinus1  in Hwell1.
          unfold levelMin in *. (* 
          SearchAbout CLevel.
          assert(0 = (CLevel (nbL - stop) - 1) ).*) 
          
          move Hwell1 at bottom.
          { unfold CLevel at 3 in Hwell1.
          case_eq(lt_dec (nbL - stop) nbLevel );intros * Hxx;rewrite Hxx in *;simpl in *;
          [|destruct nbL;simpl in *;
          lia].
          unfold CLevel at 2 in Hwell1.
          case_eq(lt_dec (nbL - stop - 1) nbLevel  );intros * Hxxx;rewrite Hxxx in *;
          [|destruct nbL;simpl in *;
          lia].
          unfold CLevel in Hwell1.
          pose proof nbLevelNotZero.
          case_eq(lt_dec 0 nbLevel);intros * Hii; rewrite Hii in *;try lia.
          inversion Hwell1;trivial. }
          
          trivial. }
         assert(Hkeyeq: nbLevel-1 = stop+1).
         assert(Hx: nbLevel - 1 = nbL).
         { apply getNbLevelEq in HnbL.
           subst.
           rewrite <- nbLevelEq;trivial. }
          lia.        
         rewrite <- Hkeyeq in Hi.
         rewrite Hi in Hinds'.
         inversion Hinds';subst.
         subst. 
         destruct Hwell' as [(Heqq & Hwell' )| (Heqq & Hwell')] ;try now contradict Heqq.
         generalize (Hwell' (StateLib.getIndexOfAddr vavalue levelMin) ) ; clear Hwell'; intros (_ & Hwell').
         simpl in Hwell'.
         rewrite Hwell';trivial.
      ++  destruct Hwell' as [(Heqq & Hwell' )| (Heqq & Hwell')] ;try now contradict Heqq.
   assert(Hii:  getIndirection sh1 vavalue nbL (stop + 1 +1 ) s' = Some pageDefault).
    {  apply getIndirectionStopS1 with nextIndirection;trivial. lia.
        apply beq_nat_falseNot;trivial.
        simpl.
      case_eq(levelEq (CLevel (nbL - (stop + 1))) levelMin);intros * Hfst.
      apply levelEqBEqNatTrue0 in Hfst.
      rewrite <- Hnbleq in Hfst.
      unfold CLevel in Hfst.
      case_eq(lt_dec (nbLevel - 1 - (stop + 1)) nbLevel) ; intros * Hls;rewrite Hls in *;simpl in *.
      rewrite <- Hnbleq in Hstp.
      lia.
      lia.
      rewrite Hstopl.
      assert(Hreadx:  StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vavalue (CLevel (nbL - (stop + 1))))
      (memory s') = Some pageDefault).
      {    generalize (Hwell'(StateLib.getIndexOfAddr vavalue (CLevel (nbL - (stop + 1)))) ) ; clear Hwell'; intros .
          intuition.    }
     simpl in Hreadx.
     subst.
     rewrite  Hreadx.
     rewrite <- beq_nat_refl;trivial. }
    assert(Hdefx: getIndirection sh1 vavalue nbL (nbLevel - 1) s' = Some pageDefault).
    { apply getIndirectionNbLevelEq with (stop+1 +1);trivial.
      lia.
      rewrite <- Hnbleq.
      trivial. }
      rewrite Hinds' in Hdefx.
      inversion Hdefx.
      subst.
      rewrite <- beq_nat_refl in Hdefs'.
      now contradict Hdefx.
    *  assert(Htrueeq: stop+1 = nbL) by lia.
      rewrite Htrueeq in *.
      rewrite Hnbleq in *.
      rewrite HindeqStop in Hi.
      rewrite Hinds' in Hi.
      inversion Hi;subst.
      destruct Hwell' as [(Heqq & Hwell' )| (Heqq & Hwell')] ;try now contradict Heqq.
      ++
         generalize (Hwell' (StateLib.getIndexOfAddr vavalue levelMin) ) ; clear Hwell'; intros (_ & Hwell').
         simpl in Hwell'.
       unfold   StateLib.readPresent, StateLib.readPDflag in *.
      case_eq(lookup nextIndirection (StateLib.getIndexOfAddr vavalue levelMin)
             (add indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop)))
                (PE
                   {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
                (memory s) pageEq idxEq) pageEq idxEq);intros * Hpres;rewrite Hpres in *;trivial.
                destruct v;trivial.
                now contradict Hwell'.
       ++ generalize (Hwell' (StateLib.getIndexOfAddr vavalue levelMin) ) ; clear Hwell'; intros(_ & Hwell') .
         simpl in Hwell'.
         rewrite Hwell';trivial.   
  - assert(Heq: getIndirection sh1 vavalue nbL (nbLevel - 1) s =
    getIndirection sh1 vavalue nbL (nbLevel - 1) s').
    {  assert(Horlst: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vavalue l) \/  
        (StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vavalue l) ) by apply indexDecOrNot.
    destruct Horlst as [Horlst| Horlst].
    + assert( Hnewvaddr: StateLib.checkVAddrsEqualityWOOffset (stop ) vaToPrepare vavalue nbL = false ).
      { apply checkVAddrsEqualityWOOffsetFalseS;trivial.
        subst;trivial. }
      apply getIndirectionMapMMUPage11 with entry ;trivial.
      intros * Hi1 Hi2.
      assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
      destruct Hor as [Hor | [Hor | Hor]].
      - assert(Hinind: In tbl (getIndirectionsAux sh1  s (stop0+1))).
        { apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
          destruct nbL;simpl in *.
          lia.
          apply beq_nat_false in Hi2.
          unfold not;intros;subst;now contradict Hi2. }
        assert(Hnotinind: ~ In indirection (getIndirectionsAux sh1 s (stop))).
        assert(Hex: stop + 1 <= nbLevel).
        destruct nbL;simpl in *.
        lia.
        apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
        unfold getIndirections in *.
        apply noDupPreviousMMULevels with nbLevel ;trivial.
        lia.
        pose proof inclGetIndirectionsAuxLe as Hproof.
        contradict Hnotinind.
        unfold incl in Hproof.
        apply Hproof with (stop0+1).
        lia.
        subst;trivial.
      - subst.
        assert(Hor: stop=0 \/ stop > 0) by lia.
        destruct Hor as [Hor | Hor].
        * subst. simpl in *.
          case_eq( levelEq nbL levelMin);intros * Hlvl;rewrite Hlvl in *.
          rewrite CLevelIdentity' in Hlevel.
          rewrite  Hlevel in Hlvl.
          now contradict Hlvl.
          now contradict Hvaddr.
        * assert(Hrn: S (stop-1) = stop) by lia.
          apply pageTablesAreDifferentMiddle with (stop-1) s nbLevel sh1 sh1 nbL  vavalue vaToPrepare
          stop;trivial;try rewrite Hrn;trivial.
          rewrite checkVAddrsEqualityWOOffsetPermut';trivial.
          left;trivial.
          split;trivial.
          apply getNbLevelEq;trivial.
          apply beq_nat_false in Hi2.
          unfold not;intros;subst;now contradict Hi2.
      - assert(Hx: nbLevel - 1 = nbL).
        { apply getNbLevelEq in HnbL.
          subst.
          rewrite <- nbLevelEq;trivial. }
        assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
        destruct Hornbl as [Hornbl | Hornbl].
        * assert(Hinind: In indirection (getIndirectionsAux sh1  s (stop+1))).
          { apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial. lia. }
        assert(Hex: stop + 1 <= nbLevel) by lia.
        assert(Hnotinind: ~ In tbl (getIndirectionsAux sh1 s (stop+1))).
        { apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try lia.
          apply getIndirectionStopLevelGe with stop0;trivial.
          lia.
          unfold getIndirections in *.
          apply noDupPreviousMMULevels with nbLevel ;trivial.
          lia.
          apply beq_nat_false in Hi2.
          unfold not;intros;subst;now contradict Hi2. }
        unfold not;intros;subst;now contradict Hnotinind.
        * assert(Hinind: In indirection (getIndirectionsAux sh1  s (stop+1))).
        { apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial. lia. }
        assert(Hex: stop + 1 <= nbLevel) by lia.
        assert(Hnotinind: ~ In tbl (getIndirectionsAux sh1 s (stop+1))).
        { apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try lia.
          unfold getIndirections in *.
          apply noDupPreviousMMULevels with nbLevel ;trivial.
          lia.
          apply beq_nat_false in Hi2.
          unfold not;intros;subst;now contradict Hi2. }
        unfold not;intros;subst;now contradict Hnotinind.
  + assert(StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = true \/
  StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = false) .
  { destruct (StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL).
  left;trivial.
  right;trivial. }
  destruct H.
  **  assert(Hinstop1: getIndirection sh1 vaToPrepare nbL (stop+1) s = Some pageDefault).
  {  
  (** ici il faut montrer que indMMUToPrepare = tbl**)
  pose proof getIndirectionEqStop as Hindeq.
  assert( getIndirection sh1 vavalue nbL stop s = Some indirection).
  rewrite <- Hindi.
  symmetry.
  apply Hindeq;trivial.
  subst.
  apply getIndirectionProp' with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indirection entry;
  subst;trivial.
  unfold 
  isEntryPage, StateLib.readPhyEntry in *.
  destruct ( lookup indirection (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) (memory s) pageEq idxEq );simpl in *;trivial;
  try now contradict Hread.
  destruct v; try now contradict Hread.
  inversion Hread;trivial.
  }
  assert(HindeqStop: getIndirection sh1 vaToPrepare nbL stop s=
  getIndirection sh1 vavalue nbL stop  s).

  apply getIndirectionEqStop;subst;trivial.
  (* apply beq_nat_true in Hdefcurind. *)

  apply getIndirectionMapMMUPage11' with entry
  ;trivial.
  intros * Hi1 Hi2.
  assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
  { destruct Hor as [Hor | [Hor | Hor]].
  - assert(Hinind: In tbl (getIndirectionsAux sh1  s (stop0+1))).
  { apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
  destruct nbL;simpl in *.
  lia.
  apply beq_nat_false in Hi2.
  unfold not;intros;subst;now contradict Hi2.
  }
  assert(Hnotinind: ~ In indirection (getIndirectionsAux sh1 s (stop))).
  { assert(Hex: stop + 1 <= nbLevel).
  destruct nbL;simpl in *.
  lia.


  apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
  unfold getIndirections in *.
  apply noDupPreviousMMULevels with nbLevel ;trivial.
  lia.
  }

  pose proof inclGetIndirectionsAuxLe as Hproof.
  left.
  contradict Hnotinind.
  unfold incl in Hproof.
  apply Hproof with (stop0+1).
  lia.
  subst;trivial.
  -
  right.  

  subst.
  intuition.
  rewrite Hindi in HindeqStop.
  rewrite Hi1 in HindeqStop.
  inversion HindeqStop;subst;trivial. 
  -
  assert(Hx: nbLevel - 1 = nbL).
  {
  apply getNbLevelEq in HnbL.
  subst.
  rewrite <- nbLevelEq;trivial. }

  assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
  destruct Hornbl as [Hornbl | Hornbl].

  *

  assert(Hinind: In indirection (getIndirectionsAux sh1  s (stop+1))).
  { apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
  lia.
  }
  assert(Hex: stop + 1 <= nbLevel) by lia.

  assert(Hnotinind: ~ In tbl (getIndirectionsAux sh1 s (stop+1))).
  {



  apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try lia.
  apply getIndirectionStopLevelGe with stop0;trivial.
  lia.

  unfold getIndirections in *.
  apply noDupPreviousMMULevels with nbLevel ;trivial.
  lia.
  apply beq_nat_false in Hi2.
  unfold not;intros;subst;now contradict Hi2. }left.

  unfold not;intros;subst;now contradict Hnotinind.
  *   assert(Hinind: In indirection (getIndirectionsAux sh1  s (stop+1))).
  { apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
  lia.
  }
  assert(Hex: stop + 1 <= nbLevel) by lia.

  assert(Hnotinind: ~ In tbl (getIndirectionsAux sh1 s (stop+1))).
  {


  apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try lia.
  unfold getIndirections in *.
  apply noDupPreviousMMULevels with nbLevel ;trivial.
  lia.
  apply beq_nat_false in Hi2.
  unfold not;intros;subst;now contradict Hi2. }
  left.

  unfold not;intros;subst;now contradict Hnotinind.
  }
  **

  apply getIndirectionMapMMUPage11 with entry
  ;trivial.
  intros * Hi1 Hi2.
  assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by lia.
  { destruct Hor as [Hor | [Hor | Hor]].
  - assert(Hinind: In tbl (getIndirectionsAux sh1  s (stop0+1))).
  { apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
  destruct nbL;simpl in *.
  lia.
  apply beq_nat_false in Hi2.
  unfold not;intros;subst;now contradict Hi2.
  }
  assert(Hnotinind: ~ In indirection (getIndirectionsAux sh1 s (stop))).
  assert(Hex: stop + 1 <= nbLevel).
  destruct nbL;simpl in *.
  lia.


  apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
  unfold getIndirections in *.
  apply noDupPreviousMMULevels with nbLevel ;trivial.
  lia.
  pose proof inclGetIndirectionsAuxLe as Hproof.
  contradict Hnotinind.
  unfold incl in Hproof.
  apply Hproof with (stop0+1).
  lia.
  subst;trivial.
  -

  subst.
  assert(Hor: stop=0 \/ stop > 0) by lia.
  destruct Hor as [Hor | Hor].
  * subst. simpl in *.
  inversion Hi1;subst.

  inversion Hindi;subst.
  now contradict H.
  * assert(Hrn: S (stop-1) = stop) by lia.
  apply pageTablesAreDifferentMiddle with (stop-1) s nbLevel sh1 sh1 nbL  vavalue vaToPrepare
  stop;trivial;try rewrite Hrn;trivial.
  rewrite checkVAddrsEqualityWOOffsetPermut';trivial.
  left;trivial.
  split;trivial.
  apply getNbLevelEq;trivial.
  apply beq_nat_false in Hi2.
  unfold not;intros;subst;now contradict Hi2.

  -
  assert(Hx: nbLevel - 1 = nbL).
  {
  apply getNbLevelEq in HnbL.
  subst.
  rewrite <- nbLevelEq;trivial. }

  assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by lia.
  destruct Hornbl as [Hornbl | Hornbl].

  *

  assert(Hinind: In indirection (getIndirectionsAux sh1  s (stop+1))).
  { apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
  lia.
  }
  assert(Hex: stop + 1 <= nbLevel) by lia.

  assert(Hnotinind: ~ In tbl (getIndirectionsAux sh1 s (stop+1))).
  {



  apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try lia.
  apply getIndirectionStopLevelGe with stop0;trivial.
  lia.

  unfold getIndirections in *.
  apply noDupPreviousMMULevels with nbLevel ;trivial.
  lia.
  apply beq_nat_false in Hi2.
  unfold not;intros;subst;now contradict Hi2. }

  unfold not;intros;subst;now contradict Hnotinind.
  *   assert(Hinind: In indirection (getIndirectionsAux sh1  s (stop+1))).
  { apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
  lia.
  }
  assert(Hex: stop + 1 <= nbLevel) by lia.

  assert(Hnotinind: ~ In tbl (getIndirectionsAux sh1 s (stop+1))).
  {


  apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try lia.
  unfold getIndirections in *.
  apply noDupPreviousMMULevels with nbLevel ;trivial.
  lia.
  apply beq_nat_false in Hi2.
  unfold not;intros;subst;now contradict Hi2. }

  unfold not;intros;subst;now contradict Hnotinind.
  } }

  rewrite <- Heq.
  destruct  b.
  *  
  case_eq(getIndirection sh1 vavalue nbL (nbLevel - 1) s);intros * Hind;
  rewrite Hind in *;try now contradict Hvapg.
  case_eq(p =? pageDefault);intros * Hnotdef';rewrite Hnotdef' in *;try now contradict Hvapg.


  assert(Hpres: StateLib.readPDflag p (StateLib.getIndexOfAddr vavalue levelMin) (memory s)=
  StateLib.readPDflag p (StateLib.getIndexOfAddr vavalue levelMin) (memory s')).
  { symmetry. apply readPDflagMapMMUPage with entry;trivial. }
  simpl in *.

  rewrite <- Hpres;trivial.
  *



  case_eq(getIndirection sh1 vavalue nbL (nbLevel - 1) s);intros * Hind;
  rewrite Hind in *;trivial.
  case_eq(p =? pageDefault);intros * Hnotdef';rewrite Hnotdef' in *;trivial.

  assert(Hpres: StateLib.readPDflag p (StateLib.getIndexOfAddr vavalue levelMin) (memory s)=
  StateLib.readPDflag p (StateLib.getIndexOfAddr vavalue levelMin) (memory s')).
  { symmetry. apply readPDflagMapMMUPage with entry;trivial. }
  simpl in *.

  rewrite <- Hpres;trivial.
Qed.

 
Lemma checkChildAddIndirection indirection   vaToPrepare  l lpred vavalue nextIndirection idxroot nbLgen part  e w r entry pd b s partx
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr:
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
lookup indirection  (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
nextEntryIsPP part idxroot pd s ->
In indirection (getIndirections pd s) ->
In part (getPartitions pageRootPartition s)  ->
Some nbLgen = StateLib.getNbLevel ->
StateLib.Level.pred l = Some lpred ->
 isWellFormedFstShadow lpred phySh1addr s ->
In partx (getPartitions pageRootPartition s) ->
 checkChild partx nbLgen s vavalue  = b ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault ->
isPresentNotDefaultIff s -> 
indirectionDescription s part indirection idxroot vaToPrepare l  ->
levelEq l levelMin = false ->
(pageDefault =? nextIndirection) = false ->
nextIndirection <> indirection ->
checkChild partx nbLgen  {|
  currentPartition := currentPartition s;
  memory := add indirection   (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present :=true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |} vavalue = b.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros * Hor3 Hindor3 Hlookup Hpde Hconfdiff Hdisjoint Hpd Hkey Hpart Hnbl Hlpred Hwell  Hpartx  Hgoal.
intros.

assert(Hor: partx = part \/ partx <> part) by apply pageDecOrNot.
destruct Hor as [Hor|Hor].
+ destruct Hor3 as [Hor3 | [Hor3|Hor3]].
  - symmetry. subst.
  apply checkChildAddIndirectionSamePartPdSh2 with idxPageDir entry pd ;trivial.
  unfold or2;left;trivial.
  -  apply checkChildAddIndirectionSamePartSh1 with entry pd lpred;subst;trivial.  (* checkChildAddIndirectionSamePartSh1 *)
  unfold nextIndirectionsOR in *;intuition;subst;trivial.
  assert(Hfalse: idxPageDir<> idxShadow1).
  apply idxPDidxSh1notEq.
  now contradict Hfalse.
  assert(Hfalse: idxShadow2 <> idxShadow1) by apply idxSh2idxSh1notEq.
  now contradict Hfalse.  
  - subst. symmetry.
    apply checkChildAddIndirectionSamePartPdSh2 with idxShadow2 entry pd ;trivial.
  unfold or2;right;trivial.
+ subst. unfold checkChild.
  assert(Hgetsh1 : forall part, StateLib.getFstShadow part (memory s) =
    StateLib.getFstShadow part
    (add indirection  (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq )).
{ intros. symmetry.
  apply getFstShadowMapMMUPage with entry;trivial. }
rewrite <- Hgetsh1. clear Hgetsh1.
case_eq(StateLib.getFstShadow partx (memory s));intros * Hsh1;trivial.
assert(Hindeq: getIndirection p vavalue nbLgen (nbLevel - 1) s =
 getIndirection p vavalue nbLgen (nbLevel - 1) s').
{ apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hin1: In tbl (getConfigPages partx s)).
{ unfold getConfigPages.
  simpl. right.
  apply inGetIndirectionsAuxInConfigPagesSh1 with p;trivial.
  apply getIndirectionInGetIndirections with vavalue nbLgen stop;trivial.
  apply nbLevelNotZero.
  apply beq_nat_falseNot;trivial.
  apply getNbLevelLe;trivial.
  apply sh1PartNotNull with partx s;trivial.
  apply nextEntryIsPPgetFstShadow;trivial.
  }
assert(Hin2: In indirection (getConfigPages part s)).
{ unfold getConfigPages;simpl.
right.
destruct Hor3 as [Hor3 | [Hor3 | Hor3]];subst.
+ apply inGetIndirectionsAuxInConfigPagesPD with pd;trivial.
apply nextEntryIsPPgetPd;trivial.
+ apply inGetIndirectionsAuxInConfigPagesSh1 with pd;trivial.
  apply nextEntryIsPPgetFstShadow;trivial.
+ apply inGetIndirectionsAuxInConfigPagesSh2 with pd;trivial.
  apply nextEntryIsPPgetSndShadow;trivial. }
unfold configTablesAreDifferent in *.
generalize(Hdisjoint partx part Hpartx Hpart Hor);clear Hdisjoint;intros Hdisjoint.
unfold disjoint in *.
contradict Hin2.
unfold getConfigPages in *.
apply Hdisjoint.
subst;trivial.
apply sh1PartNotNull with partx s;trivial.
apply nextEntryIsPPgetFstShadow;trivial. }
rewrite <- Hindeq.
case_eq(getIndirection p vavalue nbLgen (nbLevel - 1) s);intros * Hp;rewrite Hp in *; trivial.
(*[| split;intros;trivial]. *)
 case_eq( p0 =? pageDefault);intros * Hdef;trivial.
     (*   split;intros;trivial. *)
assert(Hpdflag: StateLib.readPDflag p0 (StateLib.getIndexOfAddr vavalue levelMin) (memory s) =
 StateLib.readPDflag p0 (StateLib.getIndexOfAddr vavalue levelMin)
    (add indirection  (StateLib.getIndexOfAddr vaToPrepare l)
       (PE
          {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
       (memory s) pageEq idxEq)).
       symmetry.
       apply readPDflagMapMMUPage with entry;trivial.
     rewrite Hpdflag;trivial.
(*      cbn. 
      split;intros;trivial.
 *) Qed.


Lemma getPdsVAddrAddIndirection indirection  lpred  nextIndirection vaToPrepare l idxroot nbLgen partition part pd entry e w r s 
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr :
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
lookup indirection  (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
nextEntryIsPP part idxroot pd s ->
In indirection (getIndirections pd s) ->
In part (getPartitions pageRootPartition s)  ->
In partition (getPartitions pageRootPartition s)  ->
Some nbLgen = StateLib.getNbLevel ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault ->
isPresentNotDefaultIff s ->
indirectionDescription s part indirection idxroot vaToPrepare l ->
levelEq l levelMin = false ->
(pageDefault =? nextIndirection) = false ->
nextIndirection <> indirection ->
(getPdsVAddr partition nbLgen getAllVAddrWithOffset0 s) =
(getPdsVAddr partition nbLgen getAllVAddrWithOffset0  {|
  currentPartition := currentPartition s;
  memory := add indirection   (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}).
Proof.
set (s':= {|
  currentPartition := _ |}).
unfold getPdsVAddr.
induction getAllVAddrWithOffset0;simpl;trivial;
intros.
(* + split;trivial.
+ split.
  - intros Hgoal. *)
    case_eq(checkChild partition nbLgen s a);intros * Ha;trivial.
    * case_eq(checkChild partition nbLgen s' a);intros * Ha1.
      ++ simpl in *. f_equal.
         apply IHl0;trivial.
      ++ simpl in *.
         assert(Htrue: checkChild partition nbLgen s' a = true).
         apply  checkChildAddIndirection with lpred idxroot part entry pd 
         phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;trivial.
         rewrite Htrue in *.
         now contradict Ha. (** contradiction *)
     * case_eq(checkChild partition nbLgen s' a);intros * Ha1.
      ++ assert(Htrue: checkChild partition nbLgen s' a = false). 
         apply  checkChildAddIndirection with lpred idxroot part entry pd
         phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;trivial.
         rewrite Htrue in *.
         now contradict Ha.
      ++ apply IHl0;trivial.
Qed.                

Lemma getChildrenAddIndirection s indirection nextIndirection idxroot entry nbLgen  pd lpred (* indMMUToPrepare *) vaToPrepare partition l child r w e
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr :
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
or3 idxroot ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
nextEntryIsPP partition idxroot pd s ->
In indirection (getIndirections pd s) ->

StateLib.Level.pred l = Some lpred ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault  ->
(* True -> *)
(* indirectionDescription s partition indirection sh1idx vaToPrepare l -> *)
levelEq l levelMin = false ->
(* StateLib.Level.pred l = Some lpred -> *)
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
forall part,
In part (getPartitions pageRootPartition s) ->
In child (getChildren part s) <->
In child (getChildren part {|
  currentPartition := currentPartition s;
  memory := add indirection  (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}).
Proof.
set(s':={|currentPartition:= _ |}) in *.
unfold getChildren.
intros Hindor3 Hwellsh1 Hor3 Hlookup Hl Hroot (* Hdef Hdef' *) Hinit Hlevel Hpd.
intros.
assert(Hgetpd : forall partition, StateLib.getPd partition
  (add indirection  (StateLib.getIndexOfAddr vaToPrepare l) (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := nextIndirection |})
     (memory s) pageEq idxEq ) = StateLib.getPd partition (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
intros.
rewrite Hgetpd in *. clear Hgetpd.
rewrite <- Hl in *.
case_eq( StateLib.getPd part (memory s));intros * Hpd0;[|split;trivial].
assert(Hpds : (getPdsVAddr part nbLgen getAllVAddrWithOffset0 s)=
(getPdsVAddr part nbLgen getAllVAddrWithOffset0 s')) .
{ intros. apply getPdsVAddrAddIndirection with lpred idxroot partition pd entry
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;trivial. }
rewrite <-Hpds.
unfold s'.
apply getMappedPagesAuxAddIndirection with   entry nbLgen pd 
partition idxroot phyPDChild phyMMUaddr phySh1Child phySh1addr
phySh2Child phySh2addr part;trivial.
apply nextEntryIsPPgetPd;trivial.
Qed.

Lemma getPartitionsAddIndirection
s indirection nextIndirection idxroot  entry nbLgen  pd   vaToPrepare partition l lpred r w e
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr :
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
nextEntryIsPP partition idxroot pd s ->
In indirection (getIndirections pd s) ->

StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 

noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
forall part,
In part (getPartitions pageRootPartition s) <->
In part (getPartitions pageRootPartition {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}).
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hor3 Hwell1 Hlpred Hindor Hlookup Hnewcons2 Hnewcons Hnoduptree Hi1 Hi2 Hi3 Hi4 Hlevel Hind (* Hdef *)
 Ha1 Ha2 Ha3 Ha4 Ha5 .
unfold getPartitions.
assert(Hmult: In pageRootPartition (getPartitions pageRootPartition s)).
{ unfold getPartitions.
  destruct (nbPage);simpl; left;trivial. }
revert Hmult.
generalize pageRootPartition at 1 3 4.
induction (nbPage + 1);trivial;simpl.
intros. intuition.
intros mult Hmult part .
split.
intros Hpart.
destruct Hpart as [Hpart | Hpart].
left;trivial.
right.
rewrite in_flat_map in *.
destruct Hpart as(child & Hchild1 & Hpart).
exists child.
split.
+
unfold s'.
rewrite <- getChildrenAddIndirection with (entry:=entry)   (nbLgen:= nbLgen) (* (indMMUToPrepare:= indMMUToPrepare) *)
(pd:=pd) (partition:= partition);try eassumption.
symmetry;trivial.
+  apply IHn;trivial.

apply childrenPartitionInPartitionList with mult;trivial.
+ intros Hpart.
destruct Hpart as [Hpart | Hpart].
left;trivial.
right.
rewrite in_flat_map in *.
destruct Hpart as(child & Hchild1 & Hpart).
exists child.
split.
*
unfold s'.
rewrite  getChildrenAddIndirection with (entry:=entry)   (nbLgen:= nbLgen) 
(pd:=pd) (partition:= partition) (indirection:= indirection)(vaToPrepare:=vaToPrepare)(l:=l)
(nextIndirection:=nextIndirection);trivial;try eassumption.
symmetry;trivial.
*  apply IHn;trivial.

apply childrenPartitionInPartitionList with mult;trivial.
rewrite  getChildrenAddIndirection with (entry:=entry)   (nbLgen:= nbLgen)
(pd:=pd) (partition:= partition) (indirection:= indirection)(vaToPrepare:=vaToPrepare)(l:=l)
(nextIndirection:=nextIndirection);try eassumption;trivial.
symmetry;trivial.
Qed.

Lemma getAccessibleMappedPagesAuxAddIndirection s indirection nextIndirection  entry nbLgen valist pd pg
  vaToPrepare partition l lpred r w e idxroot root
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr :
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
nextEntryIsPP partition idxroot root s ->
In indirection (getIndirections root s) -> 

lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->


partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxPageDir pd s ->
nextIndirection <> indirection ->

forall part pdpart,
In part (getPartitions pageRootPartition s) ->
nextEntryIsPP part idxPageDir pdpart s ->
In pg (getAccessibleMappedPagesAux pdpart valist s) <->
 In pg  (getAccessibleMappedPagesAux pdpart valist {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}).
Proof.
set(s':=  {|
     currentPartition := _ |}).
intros.
assert(Hparts : part=partition \/ part<> partition) by apply pageDecOrNot.
destruct Hparts as [Hparts | Hparts].
+ subst.
(* assert(Hmaps: In pg (getMappedPagesAux pdpart valist s) <->
In pg  (getMappedPagesAux pdpart valist s')).
{  apply getMappedPagesAuxAddIndirection with entry nbLgen pd indMMUToPrepare partition part;trivial. }
destruct Hmaps as (Hi1 & Hi2). *)
 unfold getAccessibleMappedPagesAux in *.


split; intros Hgoal.
(* pose proof accessibleMappedPagesInMappedPages as Hmap.
unfold incl in *.
 *)
 - rewrite filterOptionInIff in *.
 unfold getAccessibleMappedPagesOption in *.
 rewrite in_map_iff in *.
 destruct Hgoal as (x & Hx1 & Hx2).
 exists x;split;trivial.
 apply getAccessibleMappedPageSomeAddIndirectionSamePartSSI1
  with entry partition lpred idxroot root phyPDChild phyMMUaddr phySh1Child phySh1addr
phySh2Child phySh2addr ;trivial.
- rewrite filterOptionInIff in *.
 unfold getAccessibleMappedPagesOption in *.
 rewrite in_map_iff in *.
 destruct Hgoal as (x & Hx1 & Hx2).
 exists x;split;trivial.
 apply getAccessibleMappedPageSomeAddIndirectionSSI2 with indirection nextIndirection entry nbLgen
 vaToPrepare partition l r w e root idxroot phyPDChild phyMMUaddr phySh1Child
phySh1addr phySh2Child phySh2addr;trivial.
+  unfold getAccessibleMappedPagesAux in *.
split; intros Hgoal;
 rewrite filterOptionInIff in *;
 unfold getAccessibleMappedPagesOption in *;
 rewrite in_map_iff in *;
 destruct Hgoal as (x & Hx1 & Hx2);
 exists x;split;trivial;
 rewrite <- Hx1;
 [symmetry|];
 apply getAccessibleMappedPageEqAddIndirectionNotSamePart  with entry nbLgen partition lpred idxroot root phyPDChild
phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr part;trivial.
Qed.


Lemma getAccessibleMappedPagesAddIndirection s indirection nextIndirection  entry nbLgen pd pg  vaToPrepare partition l lpred r w e
idxroot root
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr :
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedFstShadow lpred phySh1addr s ->
StateLib.Level.pred l = Some lpred ->
or3 idxroot ->
nextEntryIsPP partition idxroot root s ->
In indirection (getIndirections root s) -> 
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
(* isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true -> *)
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->


partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxPageDir pd s ->
nextIndirection <> indirection ->

forall part,
In part (getPartitions pageRootPartition s) ->
In pg (getAccessibleMappedPages part  s) <->
 In pg  (getAccessibleMappedPages part  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) pageEq idxEq |}).
Proof.
set(s':=  {|
     currentPartition := _ |}).
intros.
assert(Hpd: forall partx, StateLib.getPd partx (memory s) =
StateLib.getPd partx (memory s')).
{ symmetry. apply getPdMapMMUPage with entry;trivial. }
assert(Hparts : part=partition \/ part<> partition) by apply pageDecOrNot.
destruct Hparts as [Hparts | Hparts].
+ subst.
(* assert(Hmaps: In pg (getMappedPagesAux pdpart valist s) <->
In pg  (getMappedPagesAux pdpart valist s')).
{  apply getMappedPagesAuxAddIndirection with entry nbLgen pd indMMUToPrepare partition part;trivial. }
destruct Hmaps as (Hi1 & Hi2). *)
 unfold getAccessibleMappedPages in *.
rewrite <- Hpd.
case_eq(StateLib.getPd partition (memory s));intros * Hpdpar;trivial;
[|split;intros;trivial].
unfold getAccessibleMappedPagesAux in *.
split; intros Hgoal.

(* pose proof accessibleMappedPagesInMappedPages as Hmap.
unfold incl in *.
 *)
 - rewrite filterOptionInIff in *.
 unfold getAccessibleMappedPagesOption in *.
 rewrite in_map_iff in *.
 destruct Hgoal as (x & Hx1 & Hx2).
 exists x;split;trivial.
 apply getAccessibleMappedPageSomeAddIndirectionSamePartSSI1
 
  with entry partition lpred idxroot root phyPDChild phyMMUaddr
phySh1Child phySh1addr phySh2Child phySh2addr ;trivial.
  apply nextEntryIsPPgetPd;trivial.
- rewrite filterOptionInIff in *.
 unfold getAccessibleMappedPagesOption in *.
 rewrite in_map_iff in *.
 destruct Hgoal as (x & Hx1 & Hx2).
 exists x;split;trivial.
 apply getAccessibleMappedPageSomeAddIndirectionSSI2 with  indirection nextIndirection entry nbLgen vaToPrepare partition l
r w e root idxroot phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr;trivial.
apply nextEntryIsPPgetPd;trivial.
+  unfold getAccessibleMappedPages, getAccessibleMappedPagesAux in *.
rewrite <- Hpd.
case_eq(StateLib.getPd part (memory s));intros * Hpdpar;trivial;
[|split;intros;trivial];
split; intros Hgoal;
 rewrite filterOptionInIff in *;
 unfold getAccessibleMappedPagesOption in *;
 rewrite in_map_iff in *;
 destruct Hgoal as (x & Hx1 & Hx2);
 exists x;split;trivial;
 rewrite <- Hx1;
 [symmetry|];
 apply getAccessibleMappedPageEqAddIndirectionNotSamePart
  with entry nbLgen partition lpred idxroot root phyPDChild
phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr part;trivial.

  apply nextEntryIsPPgetPd;trivial.
    apply nextEntryIsPPgetPd;trivial.
Qed.
  Lemma getTablePagesAddIndirectionDefault s indirection 
   lpred  nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
    phySh2addr xx e w r vaToPrepare idxroot l:
  let s' := {|
      currentPartition := currentPartition s;
      memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
                  (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
                  (memory s) pageEq idxEq |} in
  indirection <> nextIndirection ->
isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr
  idxroot -> ~ In xx (getTablePages nextIndirection tableSize s').
  Proof.
  induction tableSize;simpl in *;try auto.
  intros * Hnotind Hwell Hindor3.
  case_eq(beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare l) (nextIndirection, CIndex n) pageEq idxEq);intros * Heq.
  ++ simpl in *.
     apply beqPairsTrue in Heq.
     intuition.
  ++ case_eq(  lookup nextIndirection (CIndex n) (removeDup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq) pageEq
     idxEq);intros;trivial;try apply IHn;trivial.
     destruct v;try apply IHn;trivial.
     case_eq(pa p =? pageDefault);intros * Hi;try apply IHn;trivial.
     rewrite in_app_iff.
     apply and_not_or.
     split;try apply IHn;trivial.
     simpl.
     apply and_not_or.
     split;[|auto]. 
     subst.
     rewrite removeDupIdentity in H;[|auto].
     destruct Hindor3 as [(Hi1 & Hi2 & Hii3)| [(Hi1 & Hi2 & Hii3) | (Hi1 & Hi2 & Hii3)]];subst .
     ** assert(Hreadwell: forall idx, StateLib.readPhyEntry phyMMUaddr idx (memory s) = Some pageDefault).
        { assert(Hwell':isWellFormedMMUTables phyMMUaddr s ) by 
         (unfold isWellFormedTables in *;intuition).          
         unfold isWellFormedMMUTables in *.
         intros.
         generalize(Hwell' idx );clear Hwell; intros (Hwell  & _ );trivial. }
         generalize(Hreadwell (CIndex n) );clear Hwell; intros Hwell (* & _ ).*).
        unfold StateLib.readPhyEntry  in *.
        rewrite H in Hwell.
        apply beq_nat_false in Hi.
        inversion Hwell as (Hwelli).
        contradict Hi.
        rewrite Hwelli.
        trivial.
     **  assert(Hwell':isWellFormedFstShadow lpred phySh1addr s ) by 
         (unfold isWellFormedTables in *;intuition).          
         unfold isWellFormedFstShadow in *.
         destruct Hwell' as [(Hl & Hwell') | (Hl & Hwell')];
         generalize(Hwell' (CIndex n) );clear Hwell; intros (Hwell & _ ).
         +++  unfold StateLib.readPhyEntry  in *.
              rewrite H in Hwell.
              apply beq_nat_false in Hi.
              inversion Hwell as (Hwelli).
              contradict Hi.
              rewrite Hwelli.
              trivial.
         +++ unfold  StateLib.readVirEntry in Hwell.
              rewrite H in Hwell.
              now contradict Hwell.
     ** assert(Hwell':isWellFormedSndShadow lpred phySh2addr s ) by 
         (unfold isWellFormedTables in *;intuition).          
         unfold isWellFormedSndShadow in *.
         destruct Hwell' as [(Hl & Hwell') | (Hl & Hwell')];
         generalize(Hwell' (CIndex n) );clear Hwell;[ intros (Hwell & _ )|intros Hwell].
         +++  unfold StateLib.readPhyEntry  in *.
        rewrite H in Hwell.
        apply beq_nat_false in Hi.
        inversion Hwell as (Hwelli).
        contradict Hi.
        rewrite Hwelli.
        trivial.
         +++ unfold  StateLib.readVirtual in Hwell.
              rewrite H in Hwell.
              now contradict Hwell.
Qed.

Lemma getTablePagesAddIndirection indirection nextIndirection
e r w 
vaToPrepare 
s 
l pd x0 :
In x0
  (getTablePages pd tableSize
     {|
     currentPartition := currentPartition s;
     memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
                 (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
                 (memory s) pageEq idxEq |}) -> x0 <> nextIndirection -> In x0 (getTablePages pd tableSize s).
Proof.                 
induction tableSize;simpl in *;try auto.
  intros Hx0 Hor.
 case_eq(beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare l) (pd, CIndex n) pageEq idxEq);
 intros * Heq;rewrite Heq in *.
  ++ simpl in *.
     apply  beqPairsTrue in Heq.
     intuition.
     subst.
     case_eq( nextIndirection =? pageDefault);intros * Hdef;rewrite Hdef in *.
     ** case_eq ( lookup pd (CIndex n) (memory s) pageEq idxEq);intros.
     destruct v;try apply IHn;trivial.
       case_eq(pa p =? pageDefault);intros;try apply IHn;trivial.
     rewrite in_app_iff.
     left. try apply IHn;trivial.
     apply IHn;trivial.
     **  case_eq ( lookup pd (CIndex n) (memory s) pageEq idxEq);intros.
     rewrite in_app_iff in Hx0.
     simpl in *.
     intuition.
      destruct v;try apply IHn;trivial.
       case_eq(pa p =? pageDefault);intros;try apply IHn;trivial.
     rewrite in_app_iff.
     left. 
     try apply IHn;trivial.
     rewrite in_app_iff in Hx0.
     simpl in *.
     intuition.
 ++ rewrite removeDupIdentity in Hx0.
      case_eq ( lookup pd (CIndex n) (memory s) pageEq idxEq);intros * Hlook;rewrite Hlook in *.
     destruct v;try apply IHn;trivial.
     
       case_eq(pa p =? pageDefault);intros * Hdef;rewrite Hdef in *;try apply IHn;trivial.
     rewrite in_app_iff in *.
     intuition. try apply IHn;trivial.
     apply beqPairsFalse in Heq.
     intuition.
     Qed.
Lemma getIndirectionsAuxAddIndirectionSameStructure n indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr
 phySh2Child phySh2addr idxroot lpred  e r w vaToPrepare x s l  : 
let s' := {|
      currentPartition := currentPartition s;
      memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
                  (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
                  (memory s) pageEq idxEq |} in 
isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child
            phySh2addr idxroot ->
indirection <> nextIndirection -> 
x <> nextIndirection -> 
forall pd : page, In x (getIndirectionsAux pd s' n) -> In x (getIndirectionsAux pd s n).
Proof.
induction n;simpl in *;trivial.
intros *   Hwell Hindor3  Hnotind   Hkey1 pd Hkey2;simpl in *.
destruct Hkey2 as [Hkey2 | Hkey2].
- left;trivial.
- right.
rewrite in_flat_map in *.
destruct Hkey2 as (x0 & Hx0 & Hx0'). (* 
destruct Hinmmu as [Ha1 | Ha1].
subst. *)
exists x0. 
split.
* assert(Hor: x0 = nextIndirection \/ x0 <> nextIndirection) by apply pageDecOrNot.
  destruct Hor as [Hor | Hor].
  --
  subst.
  clear IHn.
  destruct n;simpl in *; try now contradict Hx0'.
  destruct Hx0';try now contradict Hkey1.
  rewrite in_flat_map in *.
  destruct H as (xx & Hxx & Hxx').
  contradict Hxx.
  revert Hnotind Hwell Hindor3.
  clear.
  unfold isWellFormedMMUTables in *.

intros. eapply getTablePagesAddIndirectionDefault; try eassumption;trivial.
-- revert Hx0 Hor.
clear.
     intros.
     eapply getTablePagesAddIndirection;try eassumption;trivial.
* apply IHn;trivial.
Qed.

Lemma getIndirectionsAddIndirectionSameStructure indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot lpred  e r w vaToPrepare x s l  pd: 
let s' := {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |}) 
              (memory s) pageEq idxEq |} in 
isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s -> 
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->

indirection <> nextIndirection ->
x <> nextIndirection -> 
In x (getIndirections pd s') ->
In x (getIndirections pd s).
Proof.
intros *   Hwell Hindor3  Hnotind  Hkey1 Hkey2 .
unfold getIndirections in *.

revert dependent pd.

intros.
eapply getIndirectionsAuxAddIndirectionSameStructure;try eassumption;trivial.
Qed. 

 Lemma getConfigPagesAddIndirectionNotSamePage x nextIndirection partition s pdpart vaToPrepare l lpred indirection entry r w e  idxroot
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr:
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->
isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s ->
(* (forall idx : index,
StateLib.readPhyEntry indirection idx (memory s) = Some defaultPage)-> *)
   consistency s ->
      x <> nextIndirection -> 
      indirection<> nextIndirection -> 
In x (getConfigPages partition {|
      currentPartition := currentPartition s;
      memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
                  (PE
                     {|
                     read := r;
                     write := w;
                     exec := e;
                     present := true;
                     user := true;
                     pa := nextIndirection |}) (memory s) pageEq idxEq |})->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
In partition (getPartitions pageRootPartition s) ->
nextEntryIsPP partition idxroot pdpart s ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->

In x (getConfigPages partition s).
Proof.
set(s':= {|
     currentPartition := _|}).
intros Hor3 Hindor3  Hwell Hcons Hkey1 Hnotind Hkey2 Hlookup Hpart Hpdpart.
intros.
(* rewrite nextEntryIsPPgetPd in *. *)
unfold getConfigPages in *.
simpl in *.
destruct Hkey2 as [Hkey2 | Hkey2].
left;trivial.
right.
unfold getConfigPagesAux in *.
assert(Hpd: forall partx, StateLib.getPd partx (memory s) =
StateLib.getPd partx (memory s')).
{ symmetry. apply getPdMapMMUPage with entry;trivial. }
rewrite <- Hpd in Hkey2.
clear Hpd.
assert(Hpd: forall partx, StateLib.getFstShadow partx (memory s) =
StateLib.getFstShadow partx (memory s')).
{ symmetry. apply getFstShadowMapMMUPage with entry;trivial. }
rewrite <- Hpd in Hkey2.
clear Hpd.

assert(Hpd: forall partx, StateLib.getSndShadow partx (memory s) =
StateLib.getSndShadow partx (memory s')).
{ symmetry. apply getSndShadowMapMMUPage with entry;trivial. }
rewrite <- Hpd in Hkey2.
clear Hpd.

assert(Hpd: forall partx, StateLib.getConfigTablesLinkedList partx (memory s) =
StateLib.getConfigTablesLinkedList partx (memory s')).
{ symmetry. apply getConfigTablesLinkedListMapMMUPage with entry;trivial. }
rewrite <- Hpd in Hkey2.
clear Hpd.
assert(Hinmmu: In indirection (getIndirections pdpart s)). 
{ apply indirectionDescriptionInGetIndirections with partition vaToPrepare l idxroot;trivial.
}
case_eq ( StateLib.getPd partition (memory s)) ; [intros pd Hpd1|intros Hpd1];rewrite Hpd1 in *;trivial.
case_eq ( StateLib.getFstShadow partition (memory s)) ; [intros sh1 Hsh1|intros Hsh1];rewrite Hsh1 in *;trivial.
case_eq ( StateLib.getSndShadow partition (memory s) ) ; [intros sh2 Hsh2|intros Hsh2];rewrite Hsh2 in *;trivial.
case_eq ( StateLib.getConfigTablesLinkedList partition (memory s) ) ; [intros ll Hll|intros Hll];rewrite Hll in *;trivial.
rewrite in_app_iff in *.
destruct Hkey2 as [Hkey2 | Hkey2].
+ left.

 apply getIndirectionsAddIndirectionSameStructure with  indirection nextIndirection  phyPDChild phyMMUaddr phySh1Child
phySh1addr phySh2Child phySh2addr idxroot lpred e r w vaToPrepare l;trivial.
(* 

 assert (Hsh1ind: getIndirections pd s =  getIndirections pd s').
  { apply getIndirectionsMapMMUPage1 with entry;trivial.
    assert(Hconfigdiff: noDupConfigPagesList s) by (unfold consistency in *;intuition).
    unfold noDupConfigPagesList in *.
    generalize(Hconfigdiff partition Hpart);clear Hconfigdiff;intros Hnodup.
    unfold getConfigPages in *.
    apply NoDup_cons_iff in Hnodup as (Hnotin & Hnodup).
    unfold getConfigPagesAux in Hnodup.
    rewrite Hpd1 in Hnodup.
    rewrite Hsh1 in Hnodup.
    rewrite Hsh2 in Hnodup.
    rewrite Hll in Hnodup.
    rewrite NoDupSplitInclIff in Hnodup.
    destruct Hnodup as ((Hn1 & Hn2) & Hn3).
    unfold disjoint in *.
    contradict Hinmmu.
    apply Hn3 in Hinmmu.
    rewrite in_app_iff in Hinmmu.
    destruct Hindor3 as [(Hi1 & Hi2 & Hii3)|(Hi1 & Hi2 & Hii3)];subst.
    + apply nextEntryIsPPgetFstShadow in Hpdpart.
      rewrite Hpdpart in Hsh1.
      inversion Hsh1;subst.
      intuition.
    + apply nextEntryIsPPgetSndShadow in Hpdpart.
      rewrite Hpdpart in Hsh2.
      inversion Hsh2;subst.
      intuition. }
  rewrite Hsh1ind;trivial.
 *)
+ rewrite in_app_iff in *.
 destruct Hkey2 as [Hkey2 | Hkey2].
 - right;left.
 
 apply getIndirectionsAddIndirectionSameStructure with  indirection nextIndirection  phyPDChild phyMMUaddr phySh1Child
phySh1addr phySh2Child phySh2addr idxroot lpred e r w vaToPrepare l;trivial.

 - right;right.
  rewrite in_app_iff in *.
 destruct Hkey2 as [Hkey2 | Hkey2].
 left.
 apply getIndirectionsAddIndirectionSameStructure with  indirection nextIndirection  phyPDChild phyMMUaddr phySh1Child
phySh1addr phySh2Child phySh2addr idxroot lpred e r w vaToPrepare l;trivial.
right. 



assert(Hconfigdiff: noDupConfigPagesList s) by (unfold consistency in *;intuition).
 unfold noDupConfigPagesList in *.
  generalize(Hconfigdiff partition Hpart);clear Hconfigdiff;intros Hnodup.
  unfold getConfigPages in *.
apply NoDup_cons_iff in Hnodup as (Hnotin & Hnodup).
 unfold getConfigPagesAux in Hnodup.
 rewrite Hpd1 in Hnodup.
 rewrite Hsh1 in Hnodup.
 rewrite Hsh2 in Hnodup.
 rewrite Hll in Hnodup.
 rewrite NoDupSplitInclIff in Hnodup.

 assert (Hllind: getLLPages ll s (nbPage + 1) =  getLLPages ll s' (nbPage + 1)).
{  destruct Hnodup as ((Hn1 & Hn2) & Hn3). apply getLLPagesMapMMUPage with entry;trivial.
 destruct Hor3 as [Hor3|[Hor3 | Hor3]];subst.
 * unfold disjoint in *.
    apply nextEntryIsPPgetPd in Hpdpart.
    rewrite Hpdpart in Hpd1.
    inversion Hpd1;subst.
 apply Hn3 in Hinmmu.
 rewrite in_app_iff in Hinmmu.
 apply not_or_and in Hinmmu as (_ & Hinmmu).
 
 rewrite in_app_iff in Hinmmu.
 apply not_or_and in Hinmmu as (_ & Hinmmu);trivial.
 *   rewrite NoDupSplitInclIff in Hn2.
 destruct Hn2 as ((_ & _) & Hn2).
 
  unfold disjoint in Hn2.
    apply nextEntryIsPPgetFstShadow in Hpdpart.
    rewrite Hpdpart in Hsh1.
    inversion Hsh1;subst.
 apply Hn2 in Hinmmu.
 rewrite in_app_iff in Hinmmu.
 apply not_or_and in Hinmmu as (_ & Hinmmu);trivial.
 * rewrite NoDupSplitInclIff in Hn2.
 destruct Hn2 as ((_ & Hn2) & _).
 rewrite NoDupSplitInclIff in Hn2.
  destruct Hn2 as ((_ & _) & Hn2).
  unfold disjoint in Hn2.
    apply nextEntryIsPPgetSndShadow in Hpdpart.
    rewrite Hpdpart in Hsh2.
    inversion Hsh2;subst.
 apply Hn2 in Hinmmu;trivial.
 }
 rewrite Hllind in *.
 trivial.
Qed.

Lemma getMappedPagesAddIndirectionNotSamePart  s  indirection nextIndirection  entry nbLgen  pd   vaToPrepare partition idxroot l r w e
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr:
let s':= {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |}) 
              (memory s) pageEq idxEq |}  in 
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->

Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->
indirectionDescription s partition indirection idxroot vaToPrepare l ->

partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP partition idxroot pd s ->
nextIndirection <> indirection ->

forall part ,
part <> partition ->
In part (getPartitions pageRootPartition s) ->
getMappedPages part s = getMappedPages part s'.
Proof. 
intros * Hlookup.
intros.
unfold getMappedPages.
assert(Hpd: forall partx, StateLib.getPd partx (memory s) =
StateLib.getPd partx (memory s')).
{ symmetry. apply getPdMapMMUPage with entry;trivial. }
rewrite <- Hpd.
case_eq(StateLib.getPd part (memory s));intros;trivial.
apply getMappedPagesAuxAddIndirectionNotSamePart with entry nbLgen pd
 partition idxroot  
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr part;trivial.
apply nextEntryIsPPgetPd;trivial.
Qed.

Lemma getUsedPagesAddIndirectionNotSamePart s  indirection nextIndirection  entry nbLgen  pd   vaToPrepare phyDescChild idxroot l r w e
phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr:
let s':= {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |}) 
              (memory s) pageEq idxEq |}  in 
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) pageEq idxEq = Some (PE entry) ->
or3 idxroot ->
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr idxroot ->

Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s phyDescChild indirection idxroot vaToPrepare l ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) = Some pageDefault -> 
isWellFormedMMUTables phyMMUaddr s ->
false = levelEq l levelMin ->
noDupConfigPagesList s ->
indirectionDescription s phyDescChild indirection idxroot vaToPrepare l ->

partitionDescriptorEntry s ->
In phyDescChild (getPartitions pageRootPartition s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(pageDefault =? nextIndirection) = false ->
nextEntryIsPP phyDescChild idxroot pd s ->
nextIndirection <> indirection ->
In indirection (getConfigPages phyDescChild s) ->
forall part ,
part <> phyDescChild ->
In part (getPartitions pageRootPartition s) ->
getUsedPages part s = getUsedPages part s'.
Proof.
intros.
  unfold getUsedPages.
  assert(Hconf: getConfigPages part s=getConfigPages part s').
  { apply getConfigPagesMapMMUPage with phyDescChild entry;trivial.
    intuition. intuition. }
  rewrite Hconf.
  assert(Hmaps: getMappedPages part s = getMappedPages part s').
  { apply getMappedPagesAddIndirectionNotSamePart  with entry nbLgen pd
     phyDescChild idxroot  
    phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr ;trivial.
 }
  rewrite Hmaps.
  trivial.
Qed. 

