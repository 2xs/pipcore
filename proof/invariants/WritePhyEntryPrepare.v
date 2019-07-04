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
    This file contains the invariant of [writePhyEntry].
    We prove that this instruction preserves the isolation property  *)
Require Import  Model.ADT Model.Hardware Core.Services Isolation
Consistency Invariants WeakestPreconditions Model.Lib StateLib
Model.MAL Lib InternalLemmas DependentTypeLemmas GetTableAddr PropagatedProperties WriteAccessible MapMMUPage.
 Require Import Omega Bool  Coq.Logic.ProofIrrelevance List.
 (* %%%%%%%%%%%%%%%%%%%%%%%%%%%%% InternalLemmas %%%%%%%%%%%%%%%%%%%%%%%% *)
Lemma noDupPreviousMMULevels s:
forall m n pd,
NoDup(getIndirectionsAux pd s m) -> 
n  <= m ->
NoDup(getIndirectionsAux pd s n ).
Proof.
induction m;simpl;intros.
+
replace n with 0 by omega.
simpl.
constructor.
+
revert dependent pd.
revert H0.
induction n.
-
intros.
simpl.
constructor.
-
intros.
simpl.
apply NoDup_cons_iff in H.
destruct H.
rewrite in_flat_map in H.
constructor.
*
rewrite in_flat_map.
contradict H.
destruct H as (x & Hxtrue & Hxfalse).
exists x.
split;trivial.


pose proof inclGetIndirectionsAuxLe.
unfold incl in *.
apply H with n;trivial.
omega.
* clear H. 
induction (getTablePages pd tableSize s);simpl.
constructor.
simpl in *.
apply NoDupSplitInclIff in H1.
intuition.
apply NoDupSplitInclIff.
intuition.
unfold disjoint in *.
intros.
rewrite in_flat_map.
contradict H4.
unfold not;intros.
destruct H4 as (x0 & Hx0 & Hx00).
pose proof inclGetIndirectionsAuxLe.
unfold incl in *.

assert(Htrue: ~ In x (flat_map (fun p : page => getIndirectionsAux p s m) l)).
apply H2.
apply H4 with n;trivial.
omega.
contradict Htrue.
rewrite in_flat_map.
exists x0;split;trivial.
apply H4 with n;trivial.
omega.
Qed.

Lemma indirectionNotInPreviousMMULevel' s (ptVaChildpd:page) idxvaChild (* phyVaChild *)  
  pdChildphy (* currentPart *) 
(* presentvaChild *) vaChild phyDescChild level (* entry *):
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
(* In currentPart (getPartitions multiplexer s) ->  *)
(* In phyVaChild (getAccessibleMappedPages currentPart s) -> *) 
(* lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) ->  *)
StateLib.getNbLevel = Some level -> 
(* negb presentvaChild = true ->  *)
In phyDescChild (getPartitions multiplexer s) -> 
(*  isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s ->  *)
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
(*  entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->   *)
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
pdChildphy <> defaultPage -> 
getIndirection pdChildphy vaChild level (nbLevel - 1) s =
            Some ptVaChildpd -> 
            nbLevel -1 > 0 -> 
~ In ptVaChildpd (getIndirectionsAux pdChildphy s (nbLevel - 1)).
Proof.
intros Hpde Hpresdef Hnodupconf Hconfigdiff (* Hparts *) (* Haccess *) (* Hlookup *) Hlevel 
 (* Hnotpresent *) Hchildpart (* Hpe Htblroot *) Hdefaut Hidx (* Hentrypresent *)
Hpdchild Hpdchildnotnull Hindchild H0.
 {  assert(0<nbLevel) by apply nbLevelNotZero.
      assert(nbLevel - 1 + 1 = nbLevel) by omega. 
 assert(Hprevious : exists prevtab,
      getIndirection pdChildphy vaChild level (nbLevel - 2) s =
            Some prevtab /\prevtab <> defaultPage /\  StateLib.readPhyEntry prevtab
  (StateLib.getIndexOfAddr vaChild (CLevel (level- ((nbLevel - 1) - 1)))) (memory s) =
Some ptVaChildpd). 
{   revert Hindchild   Hdefaut  (*  H0 *).


  assert(Hstooo : level > (nbLevel - 1 -1)).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    omega. (* 
    unfold CLevel in H0.
    rewrite H0 in *.
    simpl in *.
     *)
    omega. } 

  
  assert(Htpp : 0 < nbLevel -1).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    omega.
    omega.
    
     } 
  assert(Hnotdef : pdChildphy <> defaultPage) by intuition. 
  revert Hstooo Htpp Hnotdef.
  clear. 
 
  replace (nbLevel -2) with (nbLevel -1 -1) by omega.  
  revert pdChildphy level ptVaChildpd.
  induction (nbLevel-1);simpl.
  intros.
  omega.
  intros. 
  case_eq(StateLib.Level.eqb level fstLevel);intros;
  rewrite H in *.
  apply levelEqBEqNatTrue0 in H. 
  omega.
   case_eq(StateLib.readPhyEntry pdChildphy
                (StateLib.getIndexOfAddr vaChild level) (memory s));intros;
    rewrite H0 in *;try now contradict Hindchild.
    case_eq(defaultPage =? p);intros;rewrite H1 in *.
    apply beq_nat_false in Hdefaut.
    inversion Hindchild.
    subst.
    now contradict Hdefaut.
    case_eq(StateLib.Level.pred level );intros;rewrite H2 in *.
    + replace (n-0) with n by omega.
    assert(Hooo : n = 0 \/ 0 < n) by omega.
    destruct Hooo.
    *
    subst. 
    simpl in *. 
    exists  pdChildphy;split;trivial.
    inversion Hindchild. 
    subst. 
    rewrite <- H0.
    split.  trivial. 
    f_equal.
    f_equal.
    rewrite <- minus_n_O.
    apply CLevelIdentity1.
    * assert(Hii : l > n - 1  ) .
    apply levelPredMinus1 in H2.
    subst.
   unfold CLevel.
    case_eq( lt_dec (level - 1) nbLevel );intros.
    simpl.
    omega.
    destruct level.
    simpl in *.
    omega.
    trivial.
    assert(Hi1 : p <> defaultPage).
    apply beq_nat_false in H1.
    intuition.
    subst.
    now contradict H1. 
      generalize(IHn p l ptVaChildpd Hii H3 Hi1 Hindchild Hdefaut
       );clear IHn ; intros iHn .
       destruct iHn as (prevtab & Hindprev & Hdef & Hread).
       exists prevtab;split;trivial.
       intros.
       assert(Hs :S(n-1) = n) by omega.
       rewrite <- Hs.
       simpl.
       rewrite H.
       rewrite H0. 
       rewrite H1.
       rewrite H2;trivial.
       split;trivial.
       rewrite <- Hread.
       f_equal.
       f_equal.
       f_equal.
apply levelPredMinus1 in H2.
rewrite H2.
unfold CLevel.
case_eq(lt_dec (level - 1) nbLevel);intros. 
simpl. 
omega.
destruct level. 
simpl in *.
omega.
trivial.
+ assert(Hnotnone : StateLib.Level.pred level <> None).
apply levelPredNone;trivial. now contradict Hnotnone.  }
destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev). 
apply getIndirectionInGetIndirections2 with prevtab vaChild level;
simpl; subst;
trivial.
omega.
simpl.
rewrite <- Hprevtable.
f_equal.
omega.
rewrite H1.
assert(Hdup :   noDupConfigPagesList s) by intuition.
apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
apply Hdup;trivial.
left;trivial.
apply beq_nat_false in Hdefaut.
unfold not;intros;subst.
now contradict Hdefaut. 
move Hlevel at bottom.
symmetry in Hlevel.

apply getNbLevelEq in Hlevel.
rewrite Hlevel.
unfold CLevel. 
case_eq(lt_dec (nbLevel - 1) nbLevel);intros. 
simpl. 
omega.
omega.
}
Qed.
Lemma indexDecOrNot :
forall p1 p2 : index, p1 = p2 \/ p1<>p2.
Proof.
destruct p1;simpl in *;subst;destruct p2;simpl in *;subst.
assert (Heq :i=i0 \/ i<> i0) by omega.
destruct Heq as [Heq|Heq].
subst.
left;f_equal;apply proof_irrelevance.
right. unfold not;intros.
inversion H.
subst.
now contradict Heq.
Qed.


 Lemma getIndirectionNoDup :
forall  stop2 stop1  pd x1 x2  (l:level) vavalue s,
 NoDup (getIndirectionsAux pd s (l+1)) ->
   getIndirection pd vavalue l stop1 s = Some x1 ->
   getIndirection pd vavalue l stop2 s= Some x2 ->
   stop1 < stop2 -> stop1 < l -> x1 <> defaultPage -> x2 <> defaultPage -> x1 <> x2.
Proof.
   induction stop2.
   - simpl in *;intros. inversion H1. subst. omega.
   - simpl; intros. 
   case_eq(StateLib.Level.eqb l fstLevel);intros * Hfstl;rewrite Hfstl in *.
   * admit. (** contradict *)
   *
   case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l) (memory s) );
   intros * Hread;rewrite Hread in *;try now contradict H1.
   case_eq(defaultPage =? p);intros Hdef;rewrite Hdef in *. 
   -- admit. (** contradict H1*)

   -- case_eq(StateLib.Level.pred l );intros * Hlpred;rewrite Hlpred in *; try now contradict H1.
      
pose proof getIndirectionInGetIndirections2. 
(* getIndirections
assert(~ In x2 (getIndirectionsAux x1 s l)).
apply H6 with  p vavalue l. *)
   Admitted.
 
 
(*Lemma getIndirectionNoDup' :
forall stop1 stop2 pd x1 x2  (l:level) vavalue s,
 NoDup (getIndirectionsAux pd s (l+1)) ->
   getIndirection pd vavalue l stop1 s = Some x1 ->
   getIndirection pd vavalue l stop2 s= Some x2 ->
   stop1 < l ->  stop1 <> stop2 -> x1 <> defaultPage -> x2 <> defaultPage -> x1 <> x2.
Proof.
   induction stop1.
   -
   simpl.
   intro.
   intros.
   inversion H0.
   subst.
   clear H0.
   revert dependent x1.
   revert dependent x2.
   revert dependent l.
   revert dependent stop2.
   induction    stop2.
   intros.
   omega.
   intros.
   simpl in *.
   case_eq(StateLib.Level.eqb l fstLevel);intros * Hl;rewrite Hl in *.
   admit.
    (** contradiction *)
   case_eq(StateLib.readPhyEntry x1 (StateLib.getIndexOfAddr vavalue l) (memory s));
   intros * Hread;rewrite Hread in *.
   +
   case_eq(defaultPage =? p); intros * Hdef;rewrite Hdef in *.
   *
   admit. (** contradiction **)
   * case_eq(StateLib.Level.pred l);intros * Hpred;rewrite Hpred in *.
   -- destruct stop2;simpl in *. apply IHstop2 with l;trivial.
   destruct stop2;simpl in *;try omega.
   inversion H1;subst.
   
   revert 
   
   
   
    destruct (l). simpl in *.
   induction
    l1;simpl in *.
   now contradict H2.
   apply NoDup_cons_iff in H.
   destruct H.
   rewrite in_flat_map in H.
   contradict H.
   exists p.
   split.
   admit.
   contradict H. 
   induction tableSize;simpl.
    admit.
    
   intuition.
   simpl in *. apply IHstop2 with l0.
   destruct stop2
   
   unfold not;intros.
   subst.
   admit. (** nodup**)
   - induction stop2;simpl; intros.
case_eq(StateLib.Level.eqb l fstLevel);intros * Hfstl;rewrite Hfstl in *.
   * 
   subst. apply levelEqBEqNatTrue0 in Hfstl.
   omega.
   *
   case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l) (memory s) );
   intros * Hread;rewrite Hread in *;try now contradict H1.
   case_eq(defaultPage =? p);intros Hdef;rewrite Hdef in *.
   --    inversion H0;subst.
   now contradict H4.
   -- case_eq(StateLib.Level.pred l );intros * Hlpred;rewrite Hlpred in *.
      ++ inversion H1;subst. admit. (** nodup**)
      ++  now contradict H0.
      
      
  *  case_eq(StateLib.Level.eqb l fstLevel);intros * Hfstl;rewrite Hfstl in *.
   -- apply levelEqBEqNatTrue0 in Hfstl.
   omega.
   --
   case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l) (memory s) );
   intros * Hread;rewrite Hread in *;try now contradict H1.
   case_eq(defaultPage =? p);intros Hdef;rewrite Hdef in *.
   ++    inversion H1;subst;trivial.
   ++  case_eq(StateLib.Level.pred l );intros * Hlpred;rewrite Hlpred in *.
    ** apply IHstop1 with stop2 p l0 vavalue s;trivial.
    admit. (** nodup *)
    unfold StateLib.Level.pred in *.
     apply levelEqBEqNatFalse0 in Hfstl.
     case_eq ( gt_dec l 0 );intros * Hl;try omega;rewrite Hl in *.
     inversion Hlpred.
     simpl in *.
     omega.
     omega.
    ** now contradict H0.
Admitted.     *)
 Set Nested Proofs Allowed.
Lemma indirectionNotInPreviousMMULevelAux vaChild s :
forall (stop : nat) (pdChildphy : page) (level : level) (ptVaChildpd : page),
level > stop - 1 ->
0 < stop ->
pdChildphy <> defaultPage ->
getIndirection pdChildphy vaChild level stop s = Some ptVaChildpd ->
(defaultPage =? ptVaChildpd) = false ->
exists prevtab : page,
  getIndirection pdChildphy vaChild level (stop - 1) s = Some prevtab /\
  prevtab <> defaultPage /\
  StateLib.readPhyEntry prevtab (StateLib.getIndexOfAddr vaChild (CLevel (level - (stop - 1)))) (memory s) = Some ptVaChildpd. 
  Proof.
  induction stop;simpl.
  intros * Hstooo Htpp Hnotdef Hindchild Hdefaut.
  omega.
intros * Hstooo Htpp Hnotdef Hindchild Hdefaut.
  case_eq(StateLib.Level.eqb level fstLevel);intros;
  rewrite H in *.
  apply levelEqBEqNatTrue0 in H. 
  omega.
   case_eq(StateLib.readPhyEntry pdChildphy
                (StateLib.getIndexOfAddr vaChild level) (memory s));intros;
    rewrite H0 in *;try now contradict Hindchild.
    case_eq(defaultPage =? p);intros;rewrite H1 in *.
    apply beq_nat_false in Hdefaut.
    inversion Hindchild.
    subst.
    now contradict Hdefaut.
    case_eq(StateLib.Level.pred level );intros;rewrite H2 in *.
    + replace (stop-0) with stop by omega.
    assert(Hooo : stop = 0 \/ 0 < stop) by omega.
    destruct Hooo.
    *
    subst. 
    simpl in *. 
    exists  pdChildphy;split;trivial.
    inversion Hindchild. 
    subst. 
    rewrite <- H0.
    split.  trivial. 
    f_equal.
    f_equal.
    rewrite <- minus_n_O.
    apply CLevelIdentity1.
    * assert(Hii : l > stop - 1  ) .
    apply levelPredMinus1 in H2.
    subst.
   unfold CLevel.
    case_eq( lt_dec (level - 1) nbLevel );intros.
    simpl.
    omega.
    destruct level.
    simpl in *.
    omega.
    trivial.
    assert(Hi1 : p <> defaultPage).
    apply beq_nat_false in H1.
    intuition.
    subst.
    now contradict H1. 
      generalize(IHstop p l ptVaChildpd Hii H3 Hi1 Hindchild Hdefaut
       );clear IHstop ; intros iHn .
       destruct iHn as (prevtab & Hindprev & Hdef & Hread).
       exists prevtab;split;trivial.
       intros.
       assert(Hs :S(stop-1) = stop) by omega.
       rewrite <- Hs.
       simpl.
       rewrite H.
       rewrite H0. 
       rewrite H1.
       rewrite H2;trivial.
       split;trivial.
       rewrite <- Hread.
       f_equal.
       f_equal.
       f_equal.
apply levelPredMinus1 in H2.
rewrite H2.
unfold CLevel.
case_eq(lt_dec (level - 1) nbLevel);intros. 
simpl. 
omega.
destruct level. 
simpl in *.
omega.
trivial.
+ assert(Hnotnone : StateLib.Level.pred level <> None).
apply levelPredNone;trivial. now contradict Hnotnone.
Qed.
Lemma indirectionNotInPreviousMMULevel s ptVaChildpd idxvaChild phyVaChild  
  pdChildphy currentPart 
presentvaChild vaChild phyDescChild level entry:
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) -> 
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions multiplexer s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild fstLevel) s -> 
 getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s -> 
 (defaultPage =? ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild fstLevel = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild PDidx pdChildphy s -> 
pdChildphy <> defaultPage -> 
getIndirection pdChildphy vaChild level (nbLevel - 1) s =
            Some ptVaChildpd -> 
            nbLevel -1 > 0 -> 
~ In ptVaChildpd (getIndirectionsAux pdChildphy s (nbLevel - 1)).
Proof.
intros Hpde Hpresdef Hnodupconf Hconfigdiff Hparts Haccess Hlookup Hlevel 
 Hnotpresent Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild Hpdchildnotnull Hindchild H0.
 assert(0<nbLevel) by apply nbLevelNotZero.
      assert(nbLevel - 1 + 1 = nbLevel) by omega. 
 assert(Hprevious : exists prevtab,
      getIndirection pdChildphy vaChild level (nbLevel - 2) s =
            Some prevtab /\prevtab <> defaultPage /\  StateLib.readPhyEntry prevtab
  (StateLib.getIndexOfAddr vaChild (CLevel (level- ((nbLevel - 1) - 1)))) (memory s) =
Some ptVaChildpd). 
{   revert Hindchild   Hdefaut  (*  H0 *).


  assert(Hstooo : level > (nbLevel - 1 -1)).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    omega. (* 
    unfold CLevel in H0.
    rewrite H0 in *.
    simpl in *.
     *)
    omega. } 

  
  assert(Htpp : 0 < nbLevel -1).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    omega.
    omega.
    
     } 
  assert(Hnotdef : pdChildphy <> defaultPage) by intuition. 
  revert Hstooo Htpp Hnotdef.
  clear. 
  
  replace (nbLevel -2) with (nbLevel -1 -1) by omega.
  revert pdChildphy level ptVaChildpd.
  
  generalize   (nbLevel - 1 ) as stop.
  apply indirectionNotInPreviousMMULevelAux.
   }
destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev). 
apply getIndirectionInGetIndirections2 with prevtab vaChild level;
simpl; subst;
trivial.
omega.
simpl.
rewrite <- Hprevtable.
f_equal.
omega.
rewrite H1.
assert(Hdup :   noDupConfigPagesList s) by intuition.
apply noDupConfigPagesListNoDupGetIndirections with phyDescChild PDidx;trivial.
apply Hdup;trivial.
left;trivial.
apply beq_nat_false in Hdefaut.
unfold not;intros;subst.
now contradict Hdefaut. 
move Hlevel at bottom.
symmetry in Hlevel.

apply getNbLevelEq in Hlevel.
rewrite Hlevel.
unfold CLevel. 
case_eq(lt_dec (nbLevel - 1) nbLevel);intros. 
simpl. 
omega.
omega.
Qed.



Lemma getMappedPageSomeAddIndirection s (indirection nextIndirection :page) vaToPrepare entry  vavalue pd pg partition l
indMMUToPrepare:
partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
nextEntryIsPP partition PDidx pd s ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
(defaultPage =? nextIndirection) = false ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
getMappedPage pd s vavalue = SomePage pg -> 
false = StateLib.Level.eqb l fstLevel ->
 getMappedPage pd  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l) 
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |} vavalue = SomePage pg.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hpde Hpart Hnodupcons Hprescons Hconfigdiff Hlookup Hpd Hcurind Hdefcurind Hdefnextind Hindfromroot Hmap Hfstl.
SearchAbout getIndirection.
unfold getMappedPage, indirectionDescription in *.
destruct Hindfromroot as (root & Hpdroot & Hrootdef & Hrem).
assert(Hnodup : NoDup (getIndirections root s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition PDidx ;trivial.
apply Hnodupcons;trivial.
left;trivial. }
assert(root = pd).
apply getPdNextEntryIsPPEq with partition s;trivial.
apply nextEntryIsPPgetPd;trivial.
subst.
destruct Hrem as [(Heq & HnbL) | (nbL & stop & HnbL & Hstop & Hind & Hnotdef & Hstopl)].
+ subst indirection;rewrite <- HnbL in *.
  assert(Hvaddr: StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vavalue l = true \/
  StateLib.checkVAddrsEqualityWOOffset nbLevel vaToPrepare vavalue l = false)
  by (destruct (StateLib.checkVAddrsEqualityWOOffset);[left|right];trivial).
  destruct Hvaddr as [Hvaddr|Hvaddr].
  - case_eq(getIndirection pd vavalue l (nbLevel - 1) s );[intros tbl Htbl |intros Htbl]; rewrite Htbl in *;try now contradict Hmap. (** ici il faut montrer que indMMUToPrepare = tbl**) 
    case_eq(defaultPage =? tbl);intros Hinddef;rewrite Hinddef in *; try now contradict Hmap.
    assert(Hind :  getIndirection pd vaToPrepare l (nbLevel - 1) s = Some defaultPage).
    { apply getIndirectionNbLevelEq with 1; try omega. 
      apply getNbLevelEq in HnbL.
      subst.
      apply nbLevelEq.
      symmetry in Hfstl.
      apply levelEqBEqNatFalse0 in Hfstl.
      omega.
      simpl.
      rewrite <- Hfstl.
      assert(Hkey2: StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vaToPrepare l) (memory s)  = Some indMMUToPrepare). 
      { apply isEntryPageReadPhyEntry1;trivial. }
      rewrite Hkey2.
      rewrite Hdefcurind;trivial. }
      assert(Htrue : getIndirection pd vavalue l (nbLevel - 1) s =
      getIndirection pd vaToPrepare l (nbLevel - 1) s). 
      symmetry.
      apply getIndirectionEq;trivial.
      destruct l;simpl;omega.
      rewrite Hind in Htrue.
      rewrite Htbl in Htrue.
      inversion Htrue.
      subst.
      apply beq_nat_false in Hinddef.
      omega.
 - assert(Hidxeq: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vavalue l) \/ 
 (StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vavalue l)) by apply indexDecOrNot.
  destruct Hidxeq as [Hidxeq |Hidxeq].
  * rewrite  Hidxeq in Hcurind.
    assert(Hind :  getIndirection pd vavalue l (nbLevel - 1) s = Some defaultPage).
    { apply getIndirectionNbLevelEq with 1; try omega. 
      apply getNbLevelEq in HnbL.
      subst.
      apply nbLevelEq.
      symmetry in Hfstl.
      apply levelEqBEqNatFalse0 in Hfstl.
      omega.
      simpl.
      rewrite <- Hfstl.
      assert(Hkey2: StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l) (memory s)  = Some indMMUToPrepare). 
      { apply isEntryPageReadPhyEntry1;trivial. }
      rewrite Hkey2.
      rewrite Hdefcurind;trivial. }
    rewrite Hind in Hmap.
    assert(Htrue : (defaultPage =? defaultPage )=true).
    symmetry. apply beq_nat_refl.
    rewrite Htrue in *.
    now contradict Hmap.
  * assert (getIndirection pd vavalue l (nbLevel - 1) s = getIndirection pd vavalue l (nbLevel - 1) s'). 
  { clear Hmap.  
 destruct (nbLevel - 1); simpl. trivial.
 case_eq (StateLib.Level.eqb l fstLevel); intros * Hflst;trivial.

  assert(Hread: StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l)
    (add pd (StateLib.getIndexOfAddr vaToPrepare l)
       (PE
          {|
          read := true;
          write := true;
          exec := true;
          present := true;
          user := true;
          pa := nextIndirection |}) (memory s) beqPage beqIndex) =StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l) (memory s)). 
   {       symmetry. apply readPhyEntryMapMMUPage with entry;trivial.
          right;trivial.
          intuition. }
   rewrite Hread.
   case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr vavalue l) (memory s));intros;trivial.         
   case_eq(defaultPage =? p);intros notdef;trivial.
   case_eq ( StateLib.Level.pred l);intros * Hlpred;trivial.   
  apply getIndirectionMapMMUPage11 with entry;trivial.
  intros.
  
  pose proof indirectionNotInPreviousMMULevelAux.
  assert(Hor: stop < l \/ stop >= l) by omega.
  destruct Hor as [Hor | Hor].
  
*
  generalize(H2 vavalue s (S stop) pd l tbl);clear H2;intros H2.
  replace (S stop - 1) with stop in * by omega.
  
  assert(Hprevious: exists prevtab : page,
       getIndirection pd vavalue l stop s = Some prevtab /\
       prevtab <> defaultPage /\
       StateLib.readPhyEntry prevtab (StateLib.getIndexOfAddr vavalue (CLevel (l - stop))) (memory s) = Some tbl).
 { apply H2;clear H2;try omega.
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
omega.
replace(stop + 1 - 1) with stop in * by omega.
trivial.
replace(stop + 1 - 1) with stop in * by omega.
trivial.

unfold getIndirections in Hnodup.
apply noDupPreviousMMULevels with nbLevel.
trivial.
destruct l.
simpl in *.
omega.
assert((defaultPage =? tbl) = false) as Hnotdef  by trivial.
apply beq_nat_false in Hnotdef.
unfold not;intros;subst.
now contradict Hnotdef.
destruct l.
simpl in *.
omega.
}
assert( In pd (getIndirectionsAux pd s (stop + 1))).
{ replace  (stop + 1) with (S stop) by omega.
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
omega.
assert(Hl: l = CLevel (nbLevel - 1)).
apply getNbLevelEq;trivial.
pose proof nbLevelEq as Heq.
rewrite <- Hl in Heq.
rewrite <- Heq.
omega.
  generalize(H2 vavalue s (nbLevel - 1) pd l tbl);clear H2;intros H2.
(*   replace (S stop - 1) with stop in * by omega.
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
       prevtab <> defaultPage /\
       StateLib.readPhyEntry prevtab (StateLib.getIndexOfAddr vavalue (CLevel (l - (nbLevel - 1 - 1)))) (memory s) = Some tbl).
 { apply H2;clear H2;try omega.
intuition.



replace (nbLevel - 1) with (nbLevel - 2 + 1) by omega.
clear H0.

replace (nbLevel - 2 + 1) with (S (nbLevel - 2)) by omega.
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

replace (nbLevel - 1) with (nbLevel - 2 + 1) by omega.
clear H0.

omega.
replace(nbLevel - 2 + 1 - 1) with  (nbLevel - 1 - 1) in * by omega.
trivial.

replace(nbLevel - 2 + 1 - 1) with  (nbLevel - 1 - 1) in * by omega.
trivial.
replace(nbLevel - 2 + 1 + 1) with  (nbLevel )  by omega.
unfold getIndirections in Hnodup.
trivial.
assert((defaultPage =? tbl) = false) as Hnotdef  by trivial.
apply beq_nat_false in Hnotdef.
unfold not;intros;subst.
now contradict Hnotdef.
replace(nbLevel - 2 + 1) with  (nbLevel - 1 ) in * by omega.
omega.
}
assert( In pd (getIndirectionsAux pd s (nbLevel - 2 + 1))) .
{ replace (nbLevel - 2 + 1) with (S(nbLevel -2)) by omega.
  simpl.
  left;trivial. }
unfold not;intros.
subst.
now contradict H4.
*



   apply beq_nat_false in notdef.
   intuition.
   subst. now contradict notdef.
   }
   rewrite <- H.
    case_eq( getIndirection pd vavalue l (nbLevel - 1) s);intros * Htbl;trivial;rewrite Htbl in *.
case_eq( defaultPage =? p); intros * Hp;rewrite Hp in *;trivial.
assert( pd<>p).
 assert(Hl: l = CLevel (nbLevel - 1)).
apply getNbLevelEq;trivial.
pose proof nbLevelEq as Heq.
rewrite <- Hl in Heq.
assert(Ll: l> 0).
apply levelEqBEqNatFalse0;trivial.

symmetry;trivial.

assert(Hin:~ In p (getIndirectionsAux pd s (nbLevel - 1))). 



 apply indirectionNotInPreviousMMULevel' with (StateLib.getIndexOfAddr vavalue fstLevel) 
 
 vavalue partition l ;trivial.
 symmetry;trivial.
 subst;trivial.
 rewrite Heq;trivial.


 
 assert( In pd (getIndirectionsAux pd s (nbLevel - 1))) .
 
 subst.
 destruct (nbLevel - 1);simpl.
 subst.
 omega.
 left;trivial.
 

unfold not;intros.
subst.
now contradict Hin.
assert(StateLib.readPresent p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s') =
StateLib.readPresent p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s)).
symmetry.
apply readPresentMapMMUPage with entry;trivial.
left;intuition.
rewrite H1.

assert(Hread: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s)
= StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s')).
apply readPhyEntryMapMMUPage with entry;trivial.
left;trivial.
intuition.
rewrite <- Hread.
trivial.

trivial.
+ rewrite <- HnbL in *.

admit.
Admitted.
(* 
Lemma twoAreDifferent indirection ind1 ind2 v1 v2 l s:
getIndirection indirection v1 l (nbLevel - 1) s = Some ind1 ->
getIndirection indirection v2 l (nbLevel - 1) s = Some ind2 ->
noDupConfigPagesList s ->
checkVAddrsEqualityWOOffset nbLevel v1 v2 l = false ->
ind1 <> ind2.
Proof.
intros.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\
StateLib.checkVAddrsEqualityWOOffset nbLevel v1 va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).
assert(Hmap1: getMappedPage p s va1 = SomePage phy1).
rewrite <- H.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.
clear H.

assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\
StateLib.checkVAddrsEqualityWOOffset nbLevel v2 va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va2 & Hva2 & Hva22).
assert(Hmap2: getMappedPage p s va2 = SomePage phy2).
rewrite <- H0.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.
clear H0.
assert(Hx :StateLib.checkVAddrsEqualityWOOffset nbLevel  va2 v1 nbL = false).
apply checkVAddrsEqualityWOOffsetTrans with v2;trivial.
rewrite <- Hva22.
assert(StateLib.getNbLevel = Some (CLevel (nbLevel - 1))).
apply getNbLevelEqOption.
rewrite  H in *.
inversion H2;trivial.
apply checkVAddrsEqualityWOOffsetPermut.
assert(Hvax :StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 nbL = false).
apply checkVAddrsEqualityWOOffsetTrans with v1;trivial.
rewrite <- Hva11.
assert(StateLib.getNbLevel = Some (CLevel (nbLevel - 1))).
apply getNbLevelEqOption.
rewrite  H in *.
inversion H2;trivial.
apply checkVAddrsEqualityWOOffsetPermut.
clear H3 Hva11 Hva22 Hx.
revert dependent va1.
revert dependent va2.
revert H1 H2.
revert phy1 phy2 p nbL.
clear v1 v2.

induction getAllVAddrWithOffset0.
intuition.
intros.
destruct Hva2; destruct Hva1.
subst.
(* rewrite H2 in H4. *)
contradict Hvax.
rewrite  Bool.not_false_iff_true.
apply checkVAddrsEqualityWOOffsetEqTrue.
subst.
simpl in *.
rewrite Hmap2 in H1.
apply NoDup_cons_iff in H1.
destruct H1.
assert(In phy1 (filterOption (map (getMappedPage p s) l))).
apply filterOptionInIff.
apply in_map_iff.
exists va1; split; trivial.
unfold not; intros.
subst.
now contradict H3.
subst.
simpl in *.
rewrite Hmap1 in H1.
apply NoDup_cons_iff in H1.
destruct H1.
assert(In phy2 (filterOption (map (getMappedPage p s) l))).
apply filterOptionInIff.
apply in_map_iff.
exists va2; split; trivial.
unfold not; intros.
subst.
now contradict H0.
subst.
apply IHl with  p nbL va2 va1; trivial.
simpl in H1.
destruct(getMappedPage p s a ).
apply NoDup_cons_iff in H1.
intuition.
assumption.
trivial.
Qed. *)


Lemma getMappedPagesAuxAddIndirection s indirection nextIndirection  entry nbLgen valist pd pg indMMUToPrepare vaToPrepare partition l:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
In pg (getMappedPagesAux pd valist s)  -> In pg  (getMappedPagesAux pd valist {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}).
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hlookup Hl Hroot Hdef Hdef' Hinit Hlevel.
unfold getMappedPagesAux.
intros Hgoal.
rewrite filterOptionInIff in *.
unfold getMappedPagesOption in *.
rewrite in_map_iff in *.
destruct Hgoal as (vapg & Hvapg & Hinvalist).
exists vapg;split;trivial.
unfold indirectionDescription,  initPEntryTablePreconditionToPropagatePrepareProperties in *.
destruct Hroot as (tableroot & Hpp & Hrootnotdef & Hor).
assert(Hpdor: tableroot = pd \/ tableroot <> pd) by apply pageDecOrNot.
destruct Hpdor as [Hpdor| Hpdor];subst.
+ (** same partition **)
destruct Hor as [(Heq & HnbL) | Hor].
- (** root **) subst.
  assert(Hnoneind:getIndirection indirection vaToPrepare l (nbLevel - 1) s = Some defaultPage).
  { apply getIndirectionNbLevelEq with 1;try omega.
    rewrite  getNbLevelEq with l;trivial.
    apply nbLevelEq.
    symmetry in Hlevel.
    apply levelEqBEqNatFalse0 in Hlevel.
    omega.
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
    assert(Heq: true=(defaultPage =? defaultPage)).
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
  assert(Hor :checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = true \/
         checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = false).
  { destruct (checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l);intuition. }
  destruct Hor as [Hor | Hor].
  * (** Same virtual address : contradiction **)
    assert(Hfalse: getMappedPage indirection s vapg = NonePage).
    rewrite <- Hnone.
    symmetry.
    apply getMappedPageEq with l;trivial.
    symmetry;trivial.
    rewrite Hfalse in Hvapg.
    now contradict Hvapg.
  * (* rewrite <- Hvapg.
    symmetry. *)
    unfold getMappedPage.
    unfold getMappedPage in Hvapg.
rewrite <- HnbL in *.
    case_eq(getIndirection indirection vapg l (nbLevel - 1) s)
    ;[intros ind Hind | intros Hind];rewrite Hind in *;try now contradict Hvapg.
    case_eq(defaultPage =? ind) ;intros Hi;rewrite Hi in *;try now contradict Hvapg.
    case_eq(getIndirection indirection vapg l (nbLevel - 1) s');[intros ind' Hind'|intros Hind'].

  admit.
  admit.
  - admit.
  + admit.
 

(* (* induction valist;simpl;intros pd Hmap;trivial.
case_eq( getMappedPage pd s a); [intros x Hx | intros Hx | intros Hx] ;rewrite Hx in *.
+ case_eq (getMappedPage pd s' a );intros.
  -
simpl in *.
  destruct Hmap;subst.
  *
  assert(Hor: p = pg \/ p <> pg ) by apply pageDecOrNot.
  destruct Hor as [Hor | Hor];[left;trivial|].
  right.

admit. (*contradiction *)
* right.
  apply IHvalist;trivial.
  - simpl in *.
  destruct Hmap;subst.
  admit.  (**contradiction**)
  apply IHvalist;trivial.
  - simpl in *.
  destruct Hmap;subst.
  admit.  (**contradiction**)
  apply IHvalist;trivial. *)
 
+ case_eq( getMappedPage pd s' vapg );intros.
simpl. trivial. right.
apply IHvalist;trivial.
apply IHvalist;trivial.
apply IHvalist;trivial.
+ case_eq(getMappedPage pd s' a );intros.
 simpl. right.
 apply IHvalist;trivial.
  apply IHvalist;trivial.
   apply IHvalist;trivial. *)
Admitted.



Lemma getChildrenAddIndirection s indirection nextIndirection idxToPrepare partition entry nbLgen:
lookup indirection idxToPrepare (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
getChildren partition s = getChildren partition {|
  currentPartition := currentPartition s;
  memory := add indirection idxToPrepare
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':={|currentPartition:= _ |}) in *.
unfold getChildren.
intros Hlookup HnbL.
assert(Hgetpd : forall partition, StateLib.getPd partition
  (add indirection idxToPrepare(PE
                     {|
                     read := true;
                     write := true;
                     exec := true;
                     present := true;
                     user := true;
                     pa := nextIndirection |})
     (memory s) beqPage beqIndex ) = StateLib.getPd partition (memory s)).
{ intros. apply getPdMapMMUPage with entry;trivial. }
intros.
rewrite Hgetpd in *. clear Hgetpd.
case_eq(StateLib.getPd partition (memory s) );[intros pd Hpd |intros Hpd];
trivial.
assert(Hpds : getPdsVAddr partition nbLgen getAllVAddrWithOffset0 s =
getPdsVAddr partition nbLgen getAllVAddrWithOffset0 s') by admit.
rewrite <- HnbL.
rewrite <-Hpds.
assert(Hmap: forall valist, getMappedPagesAux pd valist s =
getMappedPagesAux pd valist s') by admit.
apply Hmap.
Admitted.
Lemma getPartitionsAddIndirection s indirection nextIndirection idxToPrepare:
getPartitions multiplexer s = getPartitions multiplexer {|
  currentPartition := currentPartition s;
  memory := add indirection idxToPrepare
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
Proof.
set(s':={|currentPartition:= _ |}) in *.
unfold getPartitions.
generalize multiplexer at 1 2.
induction (nbPage + 1);simpl;trivial;intros.
f_equal;trivial.
assert(Hchild: forall partition, getChildren partition s = getChildren partition s') by admit.
rewrite <- Hchild.
clear Hchild.
induction (getChildren p s);simpl;trivial.
f_equal.
apply IHn;trivial.
trivial.
Admitted.                

Lemma kernelDataIsolationAddIndirection s indirection nextIndirection idxToPrepare:
kernelDataIsolation s ->
kernelDataIsolation
  {|
  currentPartition := currentPartition s;
  memory := add indirection idxToPrepare
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
Proof.
intros HKDI.
set(s':={|currentPartition:= _ |}) in *.
unfold kernelDataIsolation in *.
simpl in *;intros partition1 partition2 Hpart1 Hpart2.
assert(Hparts: getPartitions multiplexer s = getPartitions multiplexer s').

Admitted.
 
 
Lemma insertEntryIntoLLPCAddIndirection  ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
 phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable idxToPrepare:
forall s : state,
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) true ->
insertEntryIntoLLPC
  {|
  currentPartition := currentPartition s;
  memory := add phyPDChild idxToPrepare
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := phyMMUaddr |}) (memory s) beqPage beqIndex |} ptMMUTrdVA phySh2addr
  phySh1addr phyMMUaddr ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2
  phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
  descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l
  idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy lastLLTable
  (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) false.
Proof.
intros.
unfold insertEntryIntoLLPC in *;intuition.
unfold propagatedPropertiesPrepare in *.
intuition;subst;trivial.
+

Admitted.    
Lemma writePhyEntryAddIndirection ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
     phyMMUaddr phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA
     ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart
     trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred
     fstLL LLChildphy lastLLTable idxToPrepare :
 {{ fun s : state =>
   insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
     phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA
     ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart
     trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred
     fstLL LLChildphy lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1))  true}}
  writePhyEntry phyPDChild idxToPrepare phyMMUaddr true true true true true
 {{ fun _ s =>  insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr phyMMUaddr ptMMUFstVA
     phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA
     ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart
     trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred
     fstLL LLChildphy lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) false}}.
Proof.
eapply weaken.
eapply WP.writePhyEntry.
simpl.
unfold insertEntryIntoLLPC, propagatedPropertiesPrepare in *.
intuition.

Admitted.
