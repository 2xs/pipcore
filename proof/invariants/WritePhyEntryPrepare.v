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
    Require Import Arith Lia.

(* Fixpoint icheck (n : nat) P Q :=
 ((P n =? Q n) &&
 (match n with O => true | S n1 => icheck n1 P Q end))%bool.

Lemma icheck_correct m P Q :
  icheck m P Q = true ->
  forall n, n < S m -> P n = Q n.
Proof.
induction m as [|m IH]; simpl.
- intros HP [|n] H. admit.   try lia.
  now destruct (Nat.eqb_spec (P 0) (Q 0)).
- intros H1 n H.
  destruct (Nat.eqb_spec (P (S m)) (Q (S m))); try discriminate.
  assert (H2 : n = S m \/ n < S m) by lia.
  destruct H2; subst.
  + now destruct (Nat.eqb_spec (P (S m)) (Q (S m))).
  + now apply IH.
Qed.
 *)



Require Import  Model.ADT Model.Hardware Core.Services Isolation
Consistency Invariants WeakestPreconditions Model.Lib StateLib
Model.MAL Lib InternalLemmas DependentTypeLemmas GetTableAddr PropagatedProperties WriteAccessible MapMMUPage.
 Require Import Omega Bool  Coq.Logic.ProofIrrelevance List.
 (* %%%%%%%%%%%%%%%%%%%%%%%%%%%%% InternalLemmas %%%%%%%%%%%%%%%%%%%%%%%% *)
 Lemma getIndirectionStop1' s indirection x idxind va l entry : 
StateLib.Level.eqb l fstLevel = false ->  indirection <> defaultPage ->
lookup indirection idxind (memory s) beqPage beqIndex = Some (PE x) -> 
isEntryPage indirection idxind entry s ->
StateLib.getIndexOfAddr va l  =  idxind -> 
StateLib.getIndirection indirection va l 1 s = Some  entry.
Proof.
intros Hlnotzero Hindnotnull Hlookup Hep Hidx .
unfold isEntryPage in *.
rewrite Hlookup in Hep. subst entry. 
unfold StateLib.getIndirection.
  case_eq (StateLib.Level.eqb l fstLevel).
  - intros H2. rewrite H2 in Hlnotzero.
    contradict Hlnotzero.  intuition.
  - intros H2. 
    unfold  StateLib.getIndexOfAddr in *.
    case_eq ( ge_dec l (length va)).
    * intros.
      destruct va.
      simpl in *.
      subst.
      destruct l. simpl in *.
      contradict H.
      omega.
   * unfold runvalue in Hidx.
     intros.
     unfold StateLib.readPhyEntry.
     inversion Hidx.
     rewrite H0.
     rewrite Hlookup.
     case_eq(defaultPage =? pa x).
     intros.
     apply beq_nat_true in H1.
     f_equal.
     unfold defaultPage in *.
     unfold CPage.
     unfold CPage in H1.
     destruct(lt_dec 0 nbPage).
     subst.
     simpl in *.
     destruct x.
     simpl in *.
     subst.
     destruct pa.
     simpl in *.
     subst.
     assert (Hp = ADT.CPage_obligation_1 0 l0).
     apply proof_irrelevance.
     subst.
     reflexivity.
     destruct page_d.
     destruct pa.
     simpl in *.
     subst.
     assert (Hp0 = Hp).
     apply proof_irrelevance.
     subst. reflexivity.
     intros.
     unfold StateLib.Level.pred.
     case_eq (gt_dec l 0).
     intros g H4; reflexivity.
     intros.
     subst.
     apply levelEqBEqNatFalse0 in H2.
     contradict H2.
     assumption.  

Qed.
 Lemma getIndirectionStopS' :
forall  stop (s : state) (nbL : level)  nextind pd va indirection, 
stop + 1 <= nbL -> indirection <> defaultPage ->
StateLib.getIndirection pd va nbL stop s = Some indirection-> 
StateLib.getIndirection indirection va (CLevel (nbL - stop)) 1 s = Some nextind ->  
StateLib.getIndirection pd va nbL (stop + 1) s = Some nextind.
Proof.
induction stop.
- intros. simpl.
  cbn in *.
  inversion H1.
  subst.
  rewrite NPeano.Nat.sub_0_r in H2.
  unfold CLevel in H2.
  destruct (lt_dec nbL nbLevel ).
  simpl in *.
  destruct nbL.
  simpl in *.
  assert (Hl = ADT.CLevel_obligation_1 l0 l ).
  apply proof_irrelevance.
  subst.
  assumption.
  destruct nbL. simpl in *.
  contradict n.
  omega.
- intros.
  simpl .
  simpl in H1.
  case_eq (StateLib.Level.eqb nbL fstLevel).
  + intros. rewrite <- H2.
    inversion H1.
    subst. 
    symmetry.
    rewrite H3 in H5. inversion H5. subst.
    simpl. clear H1.
    apply levelEqBEqNatTrue in H3.
    case_eq (StateLib.Level.eqb (CLevel (nbL - S stop)) fstLevel).
    intros.
    reflexivity.
    intros.
    apply levelEqBEqNatFalse0 in H1.
    
    contradict H1.
    unfold CLevel.
    case_eq ( lt_dec (nbL - S stop) nbLevel ).
    intros. simpl . rewrite H3.
    unfold fstLevel.
    unfold CLevel.
    case_eq(lt_dec 0 nbLevel ).
    intros.
    simpl. omega.
    intros.
    assert(0 < nbLevel).
    apply nbLevelNotZero.
    contradict H6. omega.
    intros.  
    Opaque StateLib.getIndirection.
    simpl in *.
    unfold fstLevel in H3.
    unfold CLevel in H3.
    case_eq (lt_dec 0 nbLevel).
    intros.
    rewrite H4 in H3.
    simpl in *.
    destruct nbL.
    simpl in *.
    subst.
    inversion H3.
    subst. omega.
    intros.
    assert (0 < nbLevel).
    apply nbLevelNotZero.
    omega.
  + intros Hftlevel.  
    rewrite Hftlevel in H1.
    case_eq (StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va nbL) (memory s)).
    { intros. rewrite H3 in H1. 
      case_eq ( defaultPage =? p).
      - intros. rewrite H4 in H1.
        inversion H1.
       contradict H0. intuition.
      - intros. rewrite H4 in H1.
        case_eq (StateLib.Level.pred nbL ).
        + intros. rewrite H5 in H1.
          unfold StateLib.Level.pred in H5.
          case_eq (gt_dec nbL 0).
          intros.
          rewrite H6 in H5.
          generalize (IHstop s l nextind p va indirection);clear IHstop;intros IHstop.
          apply IHstop.
          inversion H5.
          simpl in *.
          omega. 
          assumption.
          assumption.
          clear IHstop.
          inversion H5.
          Opaque StateLib.getIndirection.
          simpl in *.
          subst. 
          replace (nbL - 1 - stop) with (nbL - S stop).
          assumption.
          omega.
          intros.
          apply levelEqBEqNatFalse0 in Hftlevel.
          contradict Hftlevel.
          omega.
          Transparent StateLib.getIndirection.
        + intros.  rewrite H5 in H1. inversion H1.  
    
     }
     { intros. rewrite H3 in H1.    inversion H1. }
Qed. 

Lemma getIndirectionProp' :
forall stop s nextind idxind indirection pd va (nbL : level) entry,
stop +1 <= nbL -> indirection <> defaultPage ->
StateLib.Level.eqb (CLevel (nbL - stop)) fstLevel = false -> 
StateLib.getIndexOfAddr va (CLevel (nbL - stop)) = idxind ->
lookup indirection idxind (memory s) beqPage beqIndex = Some (PE entry)->
isEntryPage  indirection idxind nextind s ->
StateLib.getIndirection pd va nbL stop s = Some indirection ->
StateLib.getIndirection pd va nbL (stop + 1) s = Some nextind. 
Proof.
intros.
apply getIndirectionStopS' with indirection;trivial.
apply getIndirectionStop1'  with entry idxind ;trivial.
Qed.

Lemma getIndirectionEqStop :
forall (stop : nat) (nbL : level) (va1 va2 : vaddr) (pd : page)  (s : state),
stop <= nbL ->
checkVAddrsEqualityWOOffset stop va1 va2 nbL = true ->
getIndirection pd va1 nbL stop s = getIndirection pd va2 nbL stop s.
Proof.
(* intro.
assert(Hgen: stop <= stop) by omega.
revert Hgen.
generalize stop at 1 4. *)
induction stop;simpl;intros;trivial.
case_eq(StateLib.Level.eqb nbL fstLevel);intros * Hl;trivial;rewrite Hl in *.
case_eq(StateLib.Level.pred nbL);intros * Hlpred;rewrite Hlpred in *.
+ case_eq (StateLib.getIndexOfAddr va1 nbL =? StateLib.getIndexOfAddr va2 nbL);intros * Hvas;rewrite Hvas in *;
try now contradict H0.
apply beq_nat_true in Hvas.
destruct(StateLib.getIndexOfAddr va1 nbL);simpl in *.
destruct(StateLib.getIndexOfAddr va2 nbL);simpl in *.
subst.
assert(Hi = Hi0) by apply proof_irrelevance.
subst.
destruct (StateLib.readPhyEntry pd {| i := i0; Hi := Hi0 |} (memory s));trivial.
destruct( defaultPage =? p );trivial.
apply IHstop;trivial.
apply levelPredMinus1 in Hlpred;trivial.
SearchAbout CLevel.
symmetry in Hlpred.
unfold CLevel in *.
case_eq(lt_dec (nbL - 1) nbLevel );intros * Hcl;rewrite Hcl in *.
simpl in *.
destruct l;simpl in *.
inversion Hlpred.
subst.
omega.
destruct nbL;simpl in *.
omega.
+ apply levelPredNone in Hl;trivial.
contradict Hl.
trivial.
Qed.

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


(*  Lemma getIndirectionNoDup :
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
   Admitted. *)
 
 
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

Lemma pageTablesAreDifferentMiddle stop0 s:

True ->
forall (n : nat) (root1 root2 table1 table2 : page) (level1 : level) (va1 va2 : vaddr) (stop : nat),
NoDup (getIndirectionsAux root1 s n) ->
NoDup (getIndirectionsAux root2 s n) ->
checkVAddrsEqualityWOOffset (S stop0) va1 va2 level1 = false ->
level1 = CLevel (n - 1) /\ root1 = root2 \/
level1 < CLevel (n - 1) /\
(disjoint (getIndirectionsAux root1 s n) (getIndirectionsAux root2 s n) /\ root1 <> root2 \/ root1 = root2) ->
table1 <> defaultPage ->
table2 <> defaultPage ->
getIndirection root1 va1 level1 (S stop0) s = Some table1 ->
getIndirection root2 va2 level1 (S stop0) s = Some table2 ->
S stop0 <= stop ->
root1 <> defaultPage -> root2 <> defaultPage -> S stop0 <= level1 -> n <= nbLevel -> table1 <> table2.
Proof. intro H0.   induction (S stop0);
  intros  * HNoDup1 HNoDup2 Hvas Hlevel Hnotnull1 Hnotnull2 
  Htableroot1 (* Hstop *) Htableroot2 (* H0 *) Hs Hroot1 Hroot2 (* Hroot12 *) Hzero Hnbl. 
  simpl in *. now contradict Hvas. 
  intros.
  simpl in *.
  case_eq (StateLib.Level.eqb level1 fstLevel); intros ;rewrite H in *.
  -  apply levelEqBEqNatTrue0 in H. 
  omega.
  -
    clear H. 
    case_eq (StateLib.readPhyEntry root1 (StateLib.getIndexOfAddr va1 level1) (memory s)) ;
    [intros p Hread1 | intros Hread1];
    rewrite Hread1 in *; [ | inversion Htableroot1].   
    case_eq (StateLib.readPhyEntry root2 (StateLib.getIndexOfAddr va2 level1) (memory s) );
    [intros p0 Hread2 | intros Hread2];
    rewrite Hread2 in *; [ | inversion Htableroot2].
    case_eq (defaultPage =? p); intros Hnull1;
    rewrite Hnull1 in *.
    inversion Htableroot1.
    subst. now contradict Hnotnull1.
    case_eq (defaultPage =? p0); intros Hnull2;
    rewrite Hnull2 in *.
    inversion Htableroot2.
    subst. now contradict Hnotnull2.
    case_eq(StateLib.Level.pred level1); [intros pred Hpred | intros Hpred];  rewrite Hpred in *; 
    [ | inversion Htableroot1].     
    case_eq (StateLib.getIndexOfAddr va1 level1 =? StateLib.getIndexOfAddr va2 level1);
            intros Hidx;
            rewrite Hidx in Hvas; trivial. 
    * generalize (IHn (n0 -1) p p0 table1 table2 pred va1 va2 stop); clear IHn; intros IHn.
      assert (StateLib.Level.eqb level1 fstLevel = true \/ StateLib.Level.eqb level1 fstLevel = false).
      { unfold StateLib.Level.eqb.
        rewrite NPeano.Nat.eqb_eq.  rewrite NPeano.Nat.eqb_neq.
        omega. }
      destruct H.
      { apply levelEqBEqNatTrue in H. subst.
        unfold StateLib.Level.pred in Hpred.
        unfold fstLevel in Hpred.
        unfold CLevel in Hpred.
        case_eq (lt_dec 0 nbLevel ); intros;
        rewrite H in Hpred; [simpl in *;inversion Hpred |
        assert (0 < nbLevel) by apply nbLevelNotZero;
        now contradict H1]. }
      { apply IHn;trivial; try omega; clear IHn.
        + apply nodupLevelMinus1  with root1 (StateLib.getIndexOfAddr va1 level1); trivial.
          apply beq_nat_false in Hnull1.
          unfold not. intros.
          contradict Hnull1. subst. trivial.
        + apply nodupLevelMinus1  with root2 (StateLib.getIndexOfAddr va2 level1); trivial.
          apply beq_nat_false in Hnull2.
          unfold not. intros.
          contradict Hnull2. subst. trivial.
        + destruct Hlevel as [(Hlevel& Hroot) | Hlevel ].
          - left. 
            split.
            apply levelPredMinus1 in Hpred; trivial.
            unfold CLevel in Hpred. 
            case_eq(lt_dec (level1 - 1) nbLevel ); intros;
            rewrite H1 in Hpred.
            destruct level1. simpl in *.
            destruct pred.
            inversion Hpred. subst.
            apply levelEqBEqNatFalse0 in H.
            simpl in *.
            clear Htableroot2 Htableroot1 Hvas Hidx
            Hread2  Hread1 HNoDup2 HNoDup1
            Hnull1 Hnull2 Hnotnull2 Hnotnull1 Hroot2 Hroot1.
            unfold CLevel in *.
            case_eq (lt_dec (n0 - 1) nbLevel); 
            intros; rewrite H2 in *.
            simpl in *.
            case_eq (lt_dec (n0 - 1 - 1) nbLevel);
            intros.
            inversion Hlevel. subst.
            assert(Hl0 = ADT.CLevel_obligation_1 (n0 - 1 - 1) l2 ) by apply proof_irrelevance.
            subst. reflexivity. 
            simpl in *. omega. omega.
            destruct level1.
            simpl in *.
            omega.
            subst.
            apply beq_nat_true in Hidx.
            destruct (StateLib.getIndexOfAddr va2 (CLevel (n0 - 1))).
            destruct (StateLib.getIndexOfAddr va1 (CLevel (n0 - 1))).
            simpl in *.
            subst. assert (Hi = Hi0) by apply proof_irrelevance.
            subst. rewrite Hread1 in Hread2.
            inversion Hread2. trivial.
          - destruct Hlevel as (Hlevellt &  [(Hlevel & Hll) | Hlevel ]).
            * right. split.
              { apply levelPredMinus1 in Hpred; trivial.
                unfold CLevel in Hpred. 
                case_eq(lt_dec (level1 - 1) nbLevel ); intros;
                rewrite H1 in Hpred.
                destruct level1. simpl in *.
                inversion Hpred. subst.
                apply levelEqBEqNatFalse0 in H.
                simpl in *.
                clear H2 Htableroot2 Htableroot1 Hvas Hidx
                Hread2  Hread1 Hlevel HNoDup2 HNoDup1 H0 
                Hnull1 Hnull2 Hnotnull2 Hnotnull1 Hroot2 Hroot1.
                unfold CLevel in *.
                case_eq (lt_dec (n0 - 1) nbLevel); 
                intros; rewrite H0 in *.
                simpl in *.
                case_eq (lt_dec (n0 - 1 - 1) nbLevel);
                intros.
                simpl in *.
                  
                  omega. omega.  
                case_eq (lt_dec (n0 - 1 - 1) nbLevel);
                intros.
                simpl in *. omega. omega.
                destruct level1. simpl in *. omega. }
              { assert (n0 <= 1 \/ n0 > 1) as Hn0. omega.
                destruct Hn0.
                apply levelEqBEqNatFalse0 in H.
                assert (CLevel
                (n0 - 1) > 1).
                omega.
                contradict H1.
                unfold CLevel in Hlevellt, H2.
                case_eq ( lt_dec (n0 - 1) nbLevel); intros;  rewrite H1 in *;
                simpl in *. omega.
                apply le_lt_or_eq in Hnbl.
                destruct Hnbl.
                omega.
                assert (n0 > 0).
                assert (0 < nbLevel) by apply nbLevelNotZero.
                omega.
                omega.
                left. split. 
                apply inclDisjoint with (getIndirectionsAux root1 s n0) (getIndirectionsAux root2 s n0); trivial.
                apply inclGetIndirectionsAuxMinus1 with (StateLib.getIndexOfAddr va1 level1); trivial.
                apply inclGetIndirectionsAuxMinus1 with (StateLib.getIndexOfAddr va2 level1); trivial.
                assert (In p (getIndirectionsAux root1 s n0) ) as Hp.
                apply readPhyEntryInGetIndirectionsAux; trivial.
                apply beq_nat_false in Hnull1. unfold not. contradict Hnull1.
                subst. trivial. 
                apply readPhyEntryInGetTablePages with (StateLib.getIndexOfAddr va1 level1); trivial.
                destruct (StateLib.getIndexOfAddr va1 level1 ); simpl in *; trivial.
                apply beq_nat_false in Hnull1. unfold not. contradict Hnull1.
                subst. trivial.
                assert ((StateLib.getIndexOfAddr va1 level1) = (CIndex (StateLib.getIndexOfAddr va1 level1))).
                symmetry. apply indexEqId. rewrite <- H2. assumption.
                generalize(Hlevel p  Hp); intros Hpage0.
                assert (In p0 (getIndirectionsAux root2 s n0) ) as Hp0.
                apply readPhyEntryInGetIndirectionsAux; trivial.
                apply beq_nat_false in Hnull2. unfold not. contradict Hnull2.
                subst. trivial. 
                apply readPhyEntryInGetTablePages with (StateLib.getIndexOfAddr va2 level1); trivial.
                destruct (StateLib.getIndexOfAddr va2 level1 ); simpl in *; trivial.
                apply beq_nat_false in Hnull2. unfold not. contradict Hnull2.
                subst. trivial.
                assert ((StateLib.getIndexOfAddr va2 level1) = (CIndex (StateLib.getIndexOfAddr va2 level1))) as Hcidx.
                symmetry. apply indexEqId. rewrite <- Hcidx. assumption.
                destruct (getIndirectionsAux root2 s n0). simpl in *. now contradict Hp0.
                simpl in *. unfold not in *.
                intros. apply Hpage0.
                destruct Hp0. subst. left. trivial.
                subst.
                right; trivial. }
            * right. split.
              apply levelPredMinus1 in Hpred; trivial.
              unfold CLevel in Hpred. 
              case_eq(lt_dec (level1 - 1) nbLevel ); intros;
              rewrite H1 in Hpred.
              destruct level1. simpl in *.
              inversion Hpred. subst.
              apply levelEqBEqNatFalse0 in H.
              simpl in *.
              clear H2 Htableroot2 Htableroot1 Hvas Hidx
              Hread2  Hread1 HNoDup2 HNoDup1 H0 
              Hnull1 Hnull2 Hnotnull2 Hnotnull1 Hroot2 Hroot1.
              unfold CLevel in *.
              case_eq (lt_dec (n0 - 1) nbLevel); 
              intros; rewrite H0 in *.
              simpl in *.
              case_eq (lt_dec (n0 - 1 - 1) nbLevel);
              intros.
              simpl in *. omega. omega.  
              case_eq (lt_dec (n0 - 1 - 1) nbLevel);
              intros;
              simpl in *. contradict H0. omega. omega.
              destruct level1. simpl in *. omega.
              right. 
              subst.
              apply beq_nat_true in Hidx.
              destruct (StateLib.getIndexOfAddr va2 level1).
              destruct (StateLib.getIndexOfAddr va1 level1).
              simpl in *.
              subst. assert (Hi = Hi0) by apply proof_irrelevance.
              subst. rewrite Hread1 in Hread2.
              inversion Hread2. trivial.  
        + apply beq_nat_false in Hnull1.
          unfold not. intros.
          contradict Hnull1. subst. trivial.
        + apply beq_nat_false in Hnull2.
          unfold not. intros.
          contradict Hnull2. subst. trivial.
        + apply levelPredMinus1 in Hpred; trivial.
          unfold CLevel in Hpred. 
          case_eq(lt_dec (level1 - 1) nbLevel ); intros;
          rewrite H1 in Hpred.
          destruct level1. simpl in *.
          inversion Hpred. subst.
          apply levelEqBEqNatFalse0 in H.
          simpl in *.
          omega.
          destruct level1;simpl in *.
          omega. 
         }
    * clear IHn. 
      clear stop0 stop (* Hstop *) Hs Hvas . 
      destruct Hlevel as [(Hlevel& Hroot) | (Hlevel& [(Hroot & Heq) | Hroot] ) ]; subst.
      { assert (n0 <= 1 \/ n0 > 1) as Hn0. omega.
        destruct Hn0 as [Hn0 | Hn0].
        + assert(n0 = 0 \/ n0 =1) as Hn01. omega.
          destruct Hn01;subst;  simpl in *;
          unfold StateLib.Level.pred in *; [
          case_eq(gt_dec (CLevel 0) 0 ); intros g Hnb0;rewrite Hnb0 in Hpred;
          [ | now contradict Hpred];
          unfold CLevel in g |]. 
          case_eq (lt_dec 0 nbLevel); intros nbl0 Hnbl0;
          [ |
          assert(0 < nbLevel) by apply nbLevelNotZero; omega].
          clear Hpred Hnb0. 
          rewrite Hnbl0 in *; simpl in *.  now contradict g.
          case_eq(gt_dec (CLevel 0) 0 ); intros g Hnb0;rewrite Hnb0 in Hpred;
          [ | 
          now contradict Hpred].
          unfold CLevel in g.
          case_eq (lt_dec 0 nbLevel); intros nbl0 Hnbl0; [ |
          assert(0 < nbLevel) by apply nbLevelNotZero; omega].
          clear Hpred Hnb0. 
          rewrite Hnbl0 in *; simpl in *.  now contradict g.
       + assert( p0 <> p).
          { apply getTablePagesNoDup with root2 (StateLib.getIndexOfAddr va2 (CLevel (n0 - 1)))
          (StateLib.getIndexOfAddr va1 (CLevel (n0 - 1))) s; trivial.  
          destruct (StateLib.getIndexOfAddr va2 (CLevel (n0 - 1))). simpl in *; trivial.
          destruct (StateLib.getIndexOfAddr va1 (CLevel (n0 - 1))). simpl in *; trivial.
          destruct n0; [now contradict Hn0 |].
          simpl in HNoDup2. apply NoDup_cons_iff in HNoDup2.
          destruct HNoDup2 as (_ & HNoDup2).
          apply getTablePagesNoDupFlatMap  with n0; trivial. omega.
          assert (H :(CIndex (StateLib.getIndexOfAddr va2 (CLevel (n0 - 1)))) =
          (StateLib.getIndexOfAddr va2 (CLevel (n0 - 1)))).
          apply indexEqId. rewrite H; trivial. 
          assert (H2 :(CIndex (StateLib.getIndexOfAddr va1 (CLevel (n0 - 1)))) =
          (StateLib.getIndexOfAddr va1 (CLevel (n0 - 1)))).
          apply indexEqId. rewrite H2. trivial.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in Hidx.
          apply beq_nat_false in Hidx. now contradict Hidx.
          apply beq_nat_false in Hnull1.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *.
          now contradict Hnull1.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *.
          apply beq_nat_false in Hnull2. now contradict Hnull2. }
        assert( disjoint (getIndirectionsAux p s (n0 -1)) 
       (getIndirectionsAux p0 s (n0 -1))) as Hdisjoint.
         apply disjointGetIndirectionsAuxMiddle with root2
         (StateLib.getIndexOfAddr va2 (CLevel (n0 - 1)))
         (StateLib.getIndexOfAddr va1 (CLevel (n0 - 1))) ; trivial. 
         assert (In table1 (getIndirectionsAux  p s (n0 -1))) as Htbl1p.
         apply getIndirectionInGetIndirectionAuxMinus1 with va1 pred n (CLevel (n0 - 1)); trivial.
         unfold CLevel.
         case_eq( lt_dec (n0 - 1) nbLevel). intros. simpl.
         omega.
         intros.
         contradict H1. omega.
         assert (In table2 (getIndirectionsAux  p0 s (n0 -1))) as Htb2p0.
         apply getIndirectionInGetIndirectionAuxMinus1 with va2 pred n (CLevel (n0 - 1)); trivial.
         unfold CLevel.
         case_eq( lt_dec (n0 - 1) nbLevel). intros. simpl.
         omega.
         intros.
         contradict H1. omega.
         unfold disjoint in *.
         apply Hdisjoint in Htbl1p.
         unfold not. intros.
         apply Htbl1p. subst.
         assumption. }
      { assert (n0 <= 1 \/ n0 > 1) as Hn0. omega.
        destruct Hn0 as [Hn0 | Hn0].
        + assert(n0 = 0 \/ n0 =1) as Hn01. omega.
          destruct Hn01;subst;  simpl in *;
          destruct level1; simpl in *;
          unfold CLevel in Hlevel; 
          case_eq ( lt_dec 0 nbLevel); intros; rewrite H in *;
          simpl in *; omega.
        +  assert (level1 > 0). 
             {unfold StateLib.Level.pred in *.
         case_eq (  gt_dec level1 0) ; intros;
         rewrite H in *.
         inversion Hpred.
         destruct pred.
         destruct level1. simpl in *.
         inversion H2. omega.
         inversion Hpred.
         }
        assert (In table1 (getIndirectionsAux  p s (n0 -1))) as Htbl1p.
         apply getIndirectionInGetIndirectionAuxMinus1 with va1 pred n level1; trivial.
         omega.
          assert (In table2 (getIndirectionsAux  p0 s (n0 -1))) as Htbl2p0.
         apply getIndirectionInGetIndirectionAuxMinus1 with va2 pred n level1; trivial.
          omega.

          apply inclGetIndirectionsAuxMinus1 with n0 root1 (StateLib.getIndexOfAddr va1 level1)
           p s in Hread1; trivial.
           apply inclGetIndirectionsAuxMinus1 with n0 root2 (StateLib.getIndexOfAddr va2 level1)
           p0 s in Hread2; trivial. 
           unfold incl, disjoint in *.
           apply Hread1 in Htbl1p.
           apply Hread2 in Htbl2p0.
           apply Hroot in Htbl1p.
           unfold not. intros.
           apply Htbl1p. subst.
           assumption.   
            }
        { assert (n0 <= 1 \/ n0 > 1) as Hn0. omega.
        destruct Hn0 as [Hn0 | Hn0].
        + assert(n0 = 0 \/ n0 =1) as Hn01. omega.
        destruct Hn01;subst;  simpl in *;
          destruct level1; simpl in *;
          unfold CLevel in Hlevel; 
          case_eq ( lt_dec 0 nbLevel); intros; rewrite H in *;
          simpl in *; omega.
          
       + assert( p0 <> p).
         { apply getTablePagesNoDup with root2 (StateLib.getIndexOfAddr va2 level1)
          (StateLib.getIndexOfAddr va1 level1) s; trivial.  
          destruct (StateLib.getIndexOfAddr va2 level1). simpl in *; trivial.
          destruct (StateLib.getIndexOfAddr va1 level1). simpl in *; trivial.
          destruct n0; [now contradict Hn0 |].
          simpl in HNoDup2. apply NoDup_cons_iff in HNoDup2.
          destruct HNoDup2 as (_ & HNoDup2).
          apply getTablePagesNoDupFlatMap  with n0; trivial. omega.
          assert (H :(CIndex (StateLib.getIndexOfAddr va2 level1)) =
          (StateLib.getIndexOfAddr va2 level1)).
          apply indexEqId. rewrite H; trivial. 
          assert (H2 :(CIndex (StateLib.getIndexOfAddr va1 level1)) =
          (StateLib.getIndexOfAddr va1 level1)).
          apply indexEqId. rewrite H2. trivial.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in Hidx.
          apply beq_nat_false in Hidx. now contradict Hidx.
          apply beq_nat_false in Hnull1.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *.
          now contradict Hnull1.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *.
          apply beq_nat_false in Hnull2. now contradict Hnull2. }
      assert( disjoint (getIndirectionsAux p s (n0 -1)) 
       (getIndirectionsAux p0 s (n0 -1))) as Hdisjoint.
         apply disjointGetIndirectionsAuxMiddle with root2
         (StateLib.getIndexOfAddr va2 level1)
         (StateLib.getIndexOfAddr va1 level1) ; trivial.
         assert (In table1 (getIndirectionsAux  p s (n0 -1))) as Htbl1p.
         apply getIndirectionInGetIndirectionAuxMinus1 with va1 pred n level1; trivial.
         unfold StateLib.Level.pred in *.
         case_eq (  gt_dec level1 0) ; intros;
         rewrite H1 in *.
         inversion Hpred.
         destruct pred.
         destruct level1. simpl in *.
         inversion H3. omega.
         inversion Hpred.
         omega.
         assert (In table2 (getIndirectionsAux  p0 s (n0 -1))) as Htb2p0.
         apply getIndirectionInGetIndirectionAuxMinus1 with va2 pred n level1; trivial.
         unfold StateLib.Level.pred in *.
         case_eq (  gt_dec level1 0) ; intros;
         rewrite H1 in *.
         inversion Hpred.
         destruct pred.
         destruct level1. simpl in *.
         inversion H3. omega.
         inversion Hpred.
         omega.
         unfold disjoint in *.
         apply Hdisjoint in Htbl1p.
         unfold not. intros.
         apply Htbl1p. subst.
         assumption. }
Qed.
Lemma pageTablesOrIndicesAreDifferentMiddle stop0 s:

True ->
forall (n : nat) (root1 root2 table1 table2 : page) (level1 : level) (va1 va2 : vaddr) (stop : nat) ,
NoDup (getIndirectionsAux root1 s n) ->
NoDup (getIndirectionsAux root2 s n) ->
checkVAddrsEqualityWOOffset (S stop0) va1 va2 level1 = false ->
level1 = CLevel (n - 1) /\ root1 = root2 \/
level1 < CLevel (n - 1) /\
(disjoint (getIndirectionsAux root1 s n) (getIndirectionsAux root2 s n) /\ root1 <> root2 \/ root1 = root2) ->
table1 <> defaultPage ->
table2 <> defaultPage ->
getIndirection root1 va1 level1 stop0 s = Some table1 ->
getIndirection root2 va2 level1 stop0 s = Some table2 ->
S stop0 <= stop ->
root1 <> defaultPage -> root2 <> defaultPage -> S stop0 <= level1 -> n <= nbLevel -> 
table1 <> table2 \/ 
StateLib.getIndexOfAddr va1 (CLevel (level1 -stop0)) <> StateLib.getIndexOfAddr va2 (CLevel (level1 -stop0)) .
Proof. intro H0.   induction stop0;
  intros  * HNoDup1 HNoDup2 Hvas Hlevel Hnotnull1 Hnotnull2 
  Htableroot1 (* Hstop *) Htableroot2 (* H0 *) Hs Hroot1 Hroot2 (* Hroot12 *) Hzero Hnbl. 
  simpl in *.
  +
  case_eq( StateLib.getIndexOfAddr va1 level1 =? StateLib.getIndexOfAddr va2 level1);intros Hv;
  rewrite Hv in *.
  *   case_eq (StateLib.Level.eqb level1 fstLevel); intros; rewrite H in *;try now contradict Hvas.
  case_eq(StateLib.Level.pred level1);intros * Hlv;rewrite Hlv in *;try now contradict Hvas.
  * right. apply beq_nat_false in Hv.
   replace (CLevel (level1 - 0)) with level1. unfold not;intros Hx;rewrite Hx in *.
   now contradict Hv.
   rewrite Nat.sub_0_r.
   symmetry. apply
    CLevelIdentity1.
  + simpl in *.
  case_eq (StateLib.Level.eqb level1 fstLevel); intros ;rewrite H in *.
  -  apply levelEqBEqNatTrue0 in H. 
  omega.
  -
    clear H. 
    case_eq (StateLib.readPhyEntry root1 (StateLib.getIndexOfAddr va1 level1) (memory s)) ;
    [intros p Hread1 | intros Hread1];
    rewrite Hread1 in *; [ | inversion Htableroot1].   
    case_eq (StateLib.readPhyEntry root2 (StateLib.getIndexOfAddr va2 level1) (memory s) );
    [intros p0 Hread2 | intros Hread2];
    rewrite Hread2 in *; [ | inversion Htableroot2].
    case_eq (defaultPage =? p); intros Hnull1;
    rewrite Hnull1 in *.
    inversion Htableroot1.
    subst. now contradict Hnotnull1.
    case_eq (defaultPage =? p0); intros Hnull2;
    rewrite Hnull2 in *.
    inversion Htableroot2.
    subst. now contradict Hnotnull2.
    case_eq(StateLib.Level.pred level1); [intros pred Hpred | intros Hpred];  rewrite Hpred in *; 
    [ | inversion Htableroot1].     
    case_eq (StateLib.getIndexOfAddr va1 level1 =? StateLib.getIndexOfAddr va2 level1);
            intros Hidx;
            rewrite Hidx in Hvas; trivial. 
    * generalize (IHstop0 (n-1) p p0 table1 table2 pred va1 va2 stop); clear IHstop0; intros IHn.
      assert (StateLib.Level.eqb level1 fstLevel = true \/ StateLib.Level.eqb level1 fstLevel = false).
      { unfold StateLib.Level.eqb.
        rewrite NPeano.Nat.eqb_eq.  rewrite NPeano.Nat.eqb_neq.
        omega. }
      destruct H.
      { apply levelEqBEqNatTrue in H. subst.
        unfold StateLib.Level.pred in Hpred.
        unfold fstLevel in Hpred.
        unfold CLevel in Hpred.
        case_eq (lt_dec 0 nbLevel ); intros;
        rewrite H in Hpred; [simpl in *;inversion Hpred |
        assert (0 < nbLevel) by apply nbLevelNotZero;
        now contradict H1]. }
      { replace (CLevel (level1 - S stop0)) with (CLevel (pred - stop0)).
        2:{  f_equal.
        apply levelPredMinus1 in Hpred;trivial.
        rewrite Hpred.
        apply levelEqBEqNatFalse0 in H.
        unfold CLevel.
        case_eq(lt_dec (level1 - 1) nbLevel);intros * Hx;simpl.
        omega.
        destruct level1.
        simpl in *.
        omega. }
      apply IHn;trivial; try omega; clear IHn.
        + apply nodupLevelMinus1  with root1 (StateLib.getIndexOfAddr va1 level1); trivial.
          apply beq_nat_false in Hnull1.
          unfold not. intros.
          contradict Hnull1. subst. trivial. 
        + apply nodupLevelMinus1  with root2 (StateLib.getIndexOfAddr va2 level1); trivial.
          apply beq_nat_false in Hnull2.
          unfold not. intros.
          contradict Hnull2. subst. trivial.
        + destruct Hlevel as [(Hlevel& Hroot) | Hlevel ].
          - left. 
            split.
            apply levelPredMinus1 in Hpred; trivial.
            unfold CLevel in Hpred. 
            case_eq(lt_dec (level1 - 1) nbLevel ); intros;
            rewrite H1 in Hpred.
            destruct level1. simpl in *.
            destruct pred.
            inversion Hpred. subst.
            apply levelEqBEqNatFalse0 in H.
            simpl in *.
            clear Htableroot2 Htableroot1 Hvas Hidx
            Hread2  Hread1 HNoDup2 HNoDup1
            Hnull1 Hnull2 Hnotnull2 Hnotnull1 Hroot2 Hroot1.
            unfold CLevel in *.
            case_eq (lt_dec (n - 1) nbLevel); 
            intros; rewrite H2 in *.
            simpl in *.
            case_eq (lt_dec (n - 1 - 1) nbLevel);
            intros.
            inversion Hlevel. subst.
            assert(Hl0 = ADT.CLevel_obligation_1 (n - 1 - 1) l2 ) by apply proof_irrelevance.
            subst. reflexivity. 
            simpl in *. omega. omega.
            destruct level1.
            simpl in *.
            omega.
            subst.
            apply beq_nat_true in Hidx.
            destruct (StateLib.getIndexOfAddr va2 (CLevel (n - 1))).
            destruct (StateLib.getIndexOfAddr va1 (CLevel (n - 1))).
            simpl in *.
            subst. assert (Hi = Hi0) by apply proof_irrelevance.
            subst. rewrite Hread1 in Hread2.
            inversion Hread2. trivial.
          - destruct Hlevel as (Hlevellt &  [(Hlevel & Hll) | Hlevel ]).
            * right. split.
              { apply levelPredMinus1 in Hpred; trivial.
                unfold CLevel in Hpred. 
                case_eq(lt_dec (level1 - 1) nbLevel ); intros;
                rewrite H1 in Hpred.
                destruct level1. simpl in *.
                inversion Hpred. subst.
                apply levelEqBEqNatFalse0 in H.
                simpl in *.
                clear H2 Htableroot2 Htableroot1 Hvas Hidx
                Hread2  Hread1 Hlevel HNoDup2 HNoDup1 H0 
                Hnull1 Hnull2 Hnotnull2 Hnotnull1 Hroot2 Hroot1.
                unfold CLevel in *.
                case_eq (lt_dec (n - 1) nbLevel); 
                intros; rewrite H0 in *.
                simpl in *.
                case_eq (lt_dec (n - 1 - 1) nbLevel);
                intros.
                simpl in *.
                  
                  omega. omega.  
                case_eq (lt_dec (n - 1 - 1) nbLevel);
                intros.
                simpl in *. omega. omega.
                destruct level1. simpl in *. omega. }
              { assert (n <= 1 \/ n > 1) as Hn0. omega.
                destruct Hn0.
                apply levelEqBEqNatFalse0 in H.
                assert (CLevel
                (n - 1) > 1).
                omega.
                contradict H1.
                unfold CLevel in Hlevellt, H2.
                case_eq ( lt_dec (n - 1) nbLevel); intros;  rewrite H1 in *;
                simpl in *. omega.
                apply le_lt_or_eq in Hnbl.
                destruct Hnbl.
                omega.
                assert (n > 0).
                assert (0 < nbLevel) by apply nbLevelNotZero.
                omega.
                omega.
                left. split. 
                apply inclDisjoint with (getIndirectionsAux root1 s n) (getIndirectionsAux root2 s n); trivial.
                apply inclGetIndirectionsAuxMinus1 with (StateLib.getIndexOfAddr va1 level1); trivial.
                apply inclGetIndirectionsAuxMinus1 with (StateLib.getIndexOfAddr va2 level1); trivial.
                assert (In p (getIndirectionsAux root1 s n) ) as Hp.
                apply readPhyEntryInGetIndirectionsAux; trivial.
                apply beq_nat_false in Hnull1. unfold not. contradict Hnull1.
                subst. trivial. 
                apply readPhyEntryInGetTablePages with (StateLib.getIndexOfAddr va1 level1); trivial.
                destruct (StateLib.getIndexOfAddr va1 level1 ); simpl in *; trivial.
                apply beq_nat_false in Hnull1. unfold not. contradict Hnull1.
                subst. trivial.
                assert ((StateLib.getIndexOfAddr va1 level1) = (CIndex (StateLib.getIndexOfAddr va1 level1))).
                symmetry. apply indexEqId. rewrite <- H2. assumption.
                generalize(Hlevel p  Hp); intros Hpage0.
                assert (In p0 (getIndirectionsAux root2 s n) ) as Hp0.
                apply readPhyEntryInGetIndirectionsAux; trivial.
                apply beq_nat_false in Hnull2. unfold not. contradict Hnull2.
                subst. trivial. 
                apply readPhyEntryInGetTablePages with (StateLib.getIndexOfAddr va2 level1); trivial.
                destruct (StateLib.getIndexOfAddr va2 level1 ); simpl in *; trivial.
                apply beq_nat_false in Hnull2. unfold not. contradict Hnull2.
                subst. trivial.
                assert ((StateLib.getIndexOfAddr va2 level1) = (CIndex (StateLib.getIndexOfAddr va2 level1))) as Hcidx.
                symmetry. apply indexEqId. rewrite <- Hcidx. assumption.
                destruct (getIndirectionsAux root2 s n). simpl in *. now contradict Hp0.
                simpl in *. unfold not in *.
                intros. apply Hpage0.
                destruct Hp0. subst. left. trivial.
                subst.
                right; trivial. }
            * right. split.
              apply levelPredMinus1 in Hpred; trivial.
              unfold CLevel in Hpred. 
              case_eq(lt_dec (level1 - 1) nbLevel ); intros;
              rewrite H1 in Hpred.
              destruct level1. simpl in *.
              inversion Hpred. subst.
              apply levelEqBEqNatFalse0 in H.
              simpl in *.
              clear H2 Htableroot2 Htableroot1 Hvas Hidx
              Hread2  Hread1 HNoDup2 HNoDup1 H0 
              Hnull1 Hnull2 Hnotnull2 Hnotnull1 Hroot2 Hroot1.
              unfold CLevel in *.
              case_eq (lt_dec (n - 1) nbLevel); 
              intros; rewrite H0 in *.
              simpl in *.
              case_eq (lt_dec (n - 1 - 1) nbLevel);
              intros.
              simpl in *. omega. omega.  
              case_eq (lt_dec (n - 1 - 1) nbLevel);
              intros;
              simpl in *. contradict H0. omega. omega.
              destruct level1. simpl in *. omega.
              right. 
              subst.
              apply beq_nat_true in Hidx.
              destruct (StateLib.getIndexOfAddr va2 level1).
              destruct (StateLib.getIndexOfAddr va1 level1).
              simpl in *.
              subst. assert (Hi = Hi0) by apply proof_irrelevance.
              subst. rewrite Hread1 in Hread2.
              inversion Hread2. trivial.  
        + apply beq_nat_false in Hnull1.
          unfold not. intros.
          contradict Hnull1. subst. trivial.
        + apply beq_nat_false in Hnull2.
          unfold not. intros.
          contradict Hnull2. subst. trivial.
        + apply levelPredMinus1 in Hpred; trivial.
          unfold CLevel in Hpred. 
          case_eq(lt_dec (level1 - 1) nbLevel ); intros;
          rewrite H1 in Hpred.
          destruct level1. simpl in *.
          inversion Hpred. subst.
          apply levelEqBEqNatFalse0 in H.
          simpl in *.
          omega.
          destruct level1;simpl in *.
          omega. 
         }
    * clear IHstop0. 
(*       clear stop0 stop (* Hstop *) Hs Hvas .  *)
      destruct Hlevel as [(Hlevel& Hroot) | (Hlevel& [(Hroot & Heq) | Hroot] ) ]; subst.
      { assert (n <= 1 \/ n > 1) as Hn0. omega.
        destruct Hn0 as [Hn0 | Hn0].
        + assert(n = 0 \/ n =1) as Hn01. omega.
          destruct Hn01;subst;  simpl in *;
          unfold StateLib.Level.pred in *; [
          case_eq(gt_dec (CLevel 0) 0 ); intros g Hnb0;rewrite Hnb0 in Hpred;
          [ | now contradict Hpred];
          unfold CLevel in g |]. 
          case_eq (lt_dec 0 nbLevel); intros nbl0 Hnbl0;
          [ |
          assert(0 < nbLevel) by apply nbLevelNotZero; omega].
          clear Hpred Hnb0. 
          rewrite Hnbl0 in *; simpl in *.  now contradict g.
          case_eq(gt_dec (CLevel 0) 0 ); intros g Hnb0;rewrite Hnb0 in Hpred;
          [ | 
          now contradict Hpred].
          unfold CLevel in g.
          case_eq (lt_dec 0 nbLevel); intros nbl0 Hnbl0; [ |
          assert(0 < nbLevel) by apply nbLevelNotZero; omega].
          clear Hpred Hnb0. 
          rewrite Hnbl0 in *; simpl in *.  now contradict g.
       + assert( p0 <> p).
          { apply getTablePagesNoDup with root2 (StateLib.getIndexOfAddr va2 (CLevel (n - 1)))
          (StateLib.getIndexOfAddr va1 (CLevel (n - 1))) s; trivial.  
          destruct (StateLib.getIndexOfAddr va2 (CLevel (n - 1))). simpl in *; trivial.
          destruct (StateLib.getIndexOfAddr va1 (CLevel (n - 1))). simpl in *; trivial.
          destruct n; [now contradict Hn0 |].
          simpl in HNoDup2. apply NoDup_cons_iff in HNoDup2.
          destruct HNoDup2 as (_ & HNoDup2).
          apply getTablePagesNoDupFlatMap  with n; trivial. omega.
          assert (H :(CIndex (StateLib.getIndexOfAddr va2 (CLevel (n - 1)))) =
          (StateLib.getIndexOfAddr va2 (CLevel (n - 1)))).
          apply indexEqId. rewrite H; trivial. 
          assert (H2 :(CIndex (StateLib.getIndexOfAddr va1 (CLevel (n - 1)))) =
          (StateLib.getIndexOfAddr va1 (CLevel (n - 1)))).
          apply indexEqId. rewrite H2. trivial.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in Hidx.
          apply beq_nat_false in Hidx. now contradict Hidx.
          apply beq_nat_false in Hnull1.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *.
          now contradict Hnull1.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *.
          apply beq_nat_false in Hnull2. now contradict Hnull2. }
        assert( disjoint (getIndirectionsAux p s (n -1)) 
       (getIndirectionsAux p0 s (n -1))) as Hdisjoint.
         apply disjointGetIndirectionsAuxMiddle with root2
         (StateLib.getIndexOfAddr va2 (CLevel (n - 1)))
         (StateLib.getIndexOfAddr va1 (CLevel (n - 1))) ; trivial. 
         assert (In table1 (getIndirectionsAux  p s (n -1))) as Htbl1p.
         { apply getIndirectionInGetIndirectionAuxMinus1 with va1 pred stop0 (CLevel (n - 1)); trivial.
         unfold CLevel.
         case_eq( lt_dec (n - 1) nbLevel). intros. simpl.
         omega.
         intros.
         contradict H1. omega. }
         assert (In table2 (getIndirectionsAux  p0 s (n -1))) as Htb2p0.
         apply getIndirectionInGetIndirectionAuxMinus1 with va2 pred stop0 (CLevel (n - 1)); trivial.
         unfold CLevel.
         case_eq( lt_dec (n - 1) nbLevel). intros. simpl.
         omega.
         intros.
         contradict H1. omega.
         unfold disjoint in *.
         apply Hdisjoint in Htbl1p.
         unfold not. intros.
         left. intros.
         apply Htbl1p. subst.
         assumption. }
      { assert (n <= 1 \/ n > 1) as Hn0. omega.
        destruct Hn0 as [Hn0 | Hn0].
        + assert(n = 0 \/ n =1) as Hn01. omega.
          destruct Hn01;subst;  simpl in *;
          destruct level1; simpl in *;
          unfold CLevel in Hlevel; 
          case_eq ( lt_dec 0 nbLevel); intros; rewrite H in *;
          simpl in *; omega.
        +  assert (level1 > 0). 
             {unfold StateLib.Level.pred in *.
         case_eq (  gt_dec level1 0) ; intros;
         rewrite H in *.
         inversion Hpred.
         destruct pred.
         destruct level1. simpl in *.
         inversion H2. omega.
         inversion Hpred.
         }
        assert (In table1 (getIndirectionsAux  p s (n -1))) as Htbl1p.
         apply getIndirectionInGetIndirectionAuxMinus1 with va1 pred stop0 level1; trivial.
         omega.
          assert (In table2 (getIndirectionsAux  p0 s (n -1))) as Htbl2p0.
         apply getIndirectionInGetIndirectionAuxMinus1 with va2 pred stop0 level1; trivial.
          omega.

          apply inclGetIndirectionsAuxMinus1 with n root1 (StateLib.getIndexOfAddr va1 level1)
           p s in Hread1; trivial.
           apply inclGetIndirectionsAuxMinus1 with n root2 (StateLib.getIndexOfAddr va2 level1)
           p0 s in Hread2; trivial. 
           unfold incl, disjoint in *.
           apply Hread1 in Htbl1p.
           apply Hread2 in Htbl2p0.
           apply Hroot in Htbl1p.
           unfold not. intros.
           left;intros.
           apply Htbl1p. subst.
           assumption.   
            }
        { assert (n <= 1 \/ n > 1) as Hn0. omega.
        destruct Hn0 as [Hn0 | Hn0].
        + assert(n = 0 \/ n =1) as Hn01. omega.
        destruct Hn01;subst;  simpl in *;
          destruct level1; simpl in *;
          unfold CLevel in Hlevel; 
          case_eq ( lt_dec 0 nbLevel); intros; rewrite H in *;
          simpl in *; omega.
          
       + assert( p0 <> p).
         { apply getTablePagesNoDup with root2 (StateLib.getIndexOfAddr va2 level1)
          (StateLib.getIndexOfAddr va1 level1) s; trivial.  
          destruct (StateLib.getIndexOfAddr va2 level1). simpl in *; trivial.
          destruct (StateLib.getIndexOfAddr va1 level1). simpl in *; trivial.
          destruct n; [now contradict Hn0 |].
          simpl in HNoDup2. apply NoDup_cons_iff in HNoDup2.
          destruct HNoDup2 as (_ & HNoDup2).
          apply getTablePagesNoDupFlatMap  with n; trivial. omega.
          assert (H :(CIndex (StateLib.getIndexOfAddr va2 level1)) =
          (StateLib.getIndexOfAddr va2 level1)).
          apply indexEqId. rewrite H; trivial. 
          assert (H2 :(CIndex (StateLib.getIndexOfAddr va1 level1)) =
          (StateLib.getIndexOfAddr va1 level1)).
          apply indexEqId. rewrite H2. trivial.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in Hidx.
          apply beq_nat_false in Hidx. now contradict Hidx.
          apply beq_nat_false in Hnull1.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *.
          now contradict Hnull1.
          apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *.
          apply beq_nat_false in Hnull2. now contradict Hnull2. }
      assert( disjoint (getIndirectionsAux p s (n -1)) 
       (getIndirectionsAux p0 s (n -1))) as Hdisjoint.
         apply disjointGetIndirectionsAuxMiddle with root2
         (StateLib.getIndexOfAddr va2 level1)
         (StateLib.getIndexOfAddr va1 level1) ; trivial.
         assert (In table1 (getIndirectionsAux  p s (n -1))) as Htbl1p.
         apply getIndirectionInGetIndirectionAuxMinus1 with va1 pred stop0 level1; trivial.
         unfold StateLib.Level.pred in *.
         case_eq (  gt_dec level1 0) ; intros;
         rewrite H1 in *.
         inversion Hpred.
         destruct pred.
         destruct level1. simpl in *.
         inversion H3. omega.
         inversion Hpred.
         omega.
         assert (In table2 (getIndirectionsAux  p0 s (n -1))) as Htb2p0.
         apply getIndirectionInGetIndirectionAuxMinus1 with va2 pred stop0 level1; trivial.
         unfold StateLib.Level.pred in *.
         case_eq (  gt_dec level1 0) ; intros;
         rewrite H1 in *.
         inversion Hpred.
         destruct pred.
         destruct level1. simpl in *.
         inversion H3. omega.
         inversion Hpred.
         omega.
         unfold disjoint in *.
         apply Hdisjoint in Htbl1p.
         unfold not. intros.
         left;intros.
         apply Htbl1p. subst.
         assumption. }
Qed.
Lemma getIndirectionInGetIndirections2' (stop : nat) s 
(va : vaddr) (level1 : level) (table root : page) :
(stop+1) <= nbLevel ->
getIndirection root va level1 stop s = Some table ->
NoDup (getIndirectionsAux root s (stop+1)) -> 
table <> defaultPage -> 
root <> defaultPage -> 
stop <= level1 -> 
stop > 0 ->
~ In table (getIndirectionsAux root s stop).
Proof. 
intros.
apply indirectionNotInPreviousMMULevelAux in H0;trivial.
destruct H0 as ( prevtab & Hi1 & Hi2 & Hi3 ). 
apply getIndirectionInGetIndirections2  with prevtab va level1;trivial. 
omega.
rewrite  Nat.eqb_neq.
destruct defaultPage;simpl in *;destruct table;simpl in *;intuition.
subst.
apply H2.
f_equal.
apply proof_irrelevance.

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
destruct Hrem as [(Heq & HnbL) | (nbL & stop & HnbL & Hstop & Hindi & Hnotdef & Hstopl)].
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
assert (Hstp: stop + 1 <= nbL).
{ subst. assert((nbL - stop) > 0).
symmetry in Hfstl.
apply levelEqBEqNatFalse0 in Hfstl ;trivial.
unfold CLevel in Hfstl.
case_eq(lt_dec (nbL - stop) nbLevel);intros * Hlt;rewrite Hlt in *.
simpl in *;trivial.
destruct nbL;simpl in *.
omega.

omega. }
 assert(Hvaddr: StateLib.checkVAddrsEqualityWOOffset (stop+1) vaToPrepare vavalue nbL = true \/
  StateLib.checkVAddrsEqualityWOOffset (stop+1) vaToPrepare vavalue nbL = false)
  by (destruct (StateLib.checkVAddrsEqualityWOOffset);[left|right];trivial).
  destruct Hvaddr as [Hvaddr|Hvaddr].
  -  
  assert(Hinstop1: getIndirection pd vaToPrepare nbL (stop+1) s = Some indMMUToPrepare).
{  
   (** ici il faut montrer que indMMUToPrepare = tbl**) 
pose proof getIndirectionEqStop as Hindeq.
assert( getIndirection pd vavalue nbL stop s = Some indirection).
rewrite <- Hindi.
symmetry.
apply Hindeq;trivial.
subst.
admit. 
apply getIndirectionProp' with (StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop))) indirection entry;
subst;trivial.
symmetry;trivial.
}
assert(HindeqStop: getIndirection pd vaToPrepare nbL (stop + 1) s=
getIndirection pd vavalue nbL (stop + 1) s).

apply getIndirectionEqStop;subst;trivial.
apply beq_nat_true in Hdefcurind.
rewrite HindeqStop in Hinstop1.
assert(Hdef: getIndirection pd vavalue nbL (nbLevel - 1) s = Some defaultPage).
{ apply getIndirectionNbLevelEq with (stop+1);trivial.
  omega.
  apply getNbLevelEq in HnbL.
  subst.
  apply nbLevelEq.

rewrite Hinstop1.
f_equal.
destruct indMMUToPrepare;simpl in *;subst;destruct defaultPage;simpl;subst;trivial.
f_equal.
apply proof_irrelevance;trivial. }
rewrite Hdef in *.
assert(Htru: (defaultPage =? defaultPage) = true).
symmetry.
apply beq_nat_refl.
rewrite Htru in *.
now contradict Hmap.
-
case_eq(getIndirection pd vavalue nbL (nbLevel - 1) s);intros * Hind;rewrite Hind in *;try now contradict Hmap.
case_eq(defaultPage =? p);intros * Hnotdef';rewrite Hnotdef' in *;try now contradict Hmap.
case_eq( getIndirection pd vavalue nbL (nbLevel - 1) s');intros * Hind'.
* 
assert(Heq: getIndirection pd vavalue nbL (nbLevel - 1) s =
            getIndirection pd vavalue nbL (nbLevel - 1) s'). 
{
          
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros. 
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by omega.
destruct Hor as [Hor | [Hor | Hor]].
- assert(In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
destruct nbL;simpl in *.
omega.

admit. (** ok **) }
assert(~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel). 
destruct nbL;simpl in *.
omega.
    

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict H2.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
subst;trivial.
- 
subst. eapply pageTablesAreDifferentMiddle;admit.
- admit.
}



Admitted.

(* assert(Hs: (nbLevel-1) > stop) by admit. 
replace   (nbLevel - 1) with (stop + ((nbLevel-1) - stop)) in Hind by omega . *)
apply getIndirectionStopMiddle1  with stop s nbL p pd vavalue in Hind as (indMiddl & Hindmid1 & Hindmid2); try
omega.
apply getIndirectionStopMiddle1  with stop s' nbL p0 pd vavalue in Hind' as (indMiddl' & Hindmid1' & Hindmid2') .
assert(Hkey: indirection <> indMiddl \/
 StateLib.getIndexOfAddr vaToPrepare ( CLevel (nbL - stop)) <> StateLib.getIndexOfAddr vavalue ( CLevel (nbL - stop))
).
{ replace (stop+1) with (S stop) in * by omega. 
apply pageTablesOrIndicesAreDifferentMiddle with  s nbLevel pd pd nbL;trivial.
left;trivial.
split;trivial.
apply getNbLevelEq;trivial.
apply beq_nat_true in Hdefcurind.
intuition.
 }





  
  assert (stop =0 \/ stop >0) by admit.
  destruct H;subst.
  simpl in *.
  inversion Hindmid1;subst indMiddl.
  inversion Hindmid1';subst indMiddl'.
  inversion Hindi; subst indirection.
            assert( StateLib.Level.eqb nbL fstLevel = false) by admit.
            rewrite H in *.        
admit. 

Lemma xxx  pd ind1 ind2 va1 va2 stop (nbL: level) s:
NoDup (getIndirectionsAux pd s (stop+1)) ->
stop > 0 ->
stop <= nbL ->
checkVAddrsEqualityWOOffset (stop + 1) va1 va2 nbL = false ->
getIndirection pd va1 nbL stop s = Some ind1 ->
getIndirection pd va2 nbL stop s = Some ind2 ->
ind1 <> ind2.
Proof.
revert pd ind1 ind2 va1 va2  nbL s.
induction stop;simpl.
intros. omega.
intros.
case_eq(StateLib.Level.eqb nbL fstLevel);intros * Hfst;rewrite Hfst in *.
admit. (** contradict fstLevel**)
case_eq( StateLib.Level.pred nbL);intros * Hpred;rewrite Hpred in *.
+ case_eq(StateLib.getIndexOfAddr va1 nbL =? StateLib.getIndexOfAddr va2 nbL);intros * Hvads;
rewrite Hvads in *.
- 

Admitted.
assert(exists ind , getIndirection pd vavalue nbL stop s = Some ind) as (indx & Hindx) by admit.

SearchAbout checkVAddrsEqualityWOOffset false.
(** j'etais en train de regarder comment generaliser ce lemme pageTablesOrIndicesAreDifferent. J'ai pas encore compris pourquoi 
jetraite fslLevel comme etage intermédiaire **)

Lemma pageTablesOrIndicesAreDifferent (root1 root2 table1 table2 : page ) 
(va1 va2 : vaddr) (level1 : level)  (stop : nat)  s:
root1 <> defaultPage -> root2 <> defaultPage -> 
NoDup (getIndirections root1 s) ->
NoDup (getIndirections root2 s) -> 
StateLib.checkVAddrsEqualityWOOffset stop va1 va2 level1 = false -> 
( (level1 = CLevel (nbLevel -1) /\ root1 = root2) \/ (level1 < CLevel (nbLevel -1) /\(
(disjoint (getIndirections root1 s) (getIndirections root2 s)/\ root1 <> root2) \/ root1 = root2  )) )-> 
table1 <> defaultPage -> 
table2 <> defaultPage -> 
(* stop > 0 ->  *)
getIndirection root1 va1 level1 stop s = Some table1-> 
getIndirection root2 va2 level1 stop s = Some table2 -> 
table1 <> table2 \/ StateLib.getIndexOfAddr va1 fstLevel <> StateLib.getIndexOfAddr va2 fstLevel.
Proof.
intros Hroot1 Hroot2 HNoDup1 HNoDup2 Hvas  Hlevel 
Hnotnull1 Hnotnull2  (* Hstop *) Htableroot1    Htableroot2.
assert (StateLib.Level.eqb level1 fstLevel = true \/ StateLib.Level.eqb level1 fstLevel = false).
{ unfold StateLib.Level.eqb.
        rewrite NPeano.Nat.eqb_eq.  rewrite NPeano.Nat.eqb_neq.
        omega. }
assert(StateLib.getIndexOfAddr va1 fstLevel <> StateLib.getIndexOfAddr va2 fstLevel \/ 
StateLib.getIndexOfAddr va1 fstLevel = StateLib.getIndexOfAddr va2 fstLevel).
{ destruct (StateLib.getIndexOfAddr va1 fstLevel), (StateLib.getIndexOfAddr va2 fstLevel ) .
  assert (i = i0 \/ i<> i0). omega.
  destruct H0. subst.
  assert(Hi = Hi0) by apply proof_irrelevance. subst.
  right. reflexivity. left. trivial.
  unfold not. intros. apply H0.
  clear H0. inversion H1. trivial. }
destruct H0; [right; assumption |].
destruct H.
+ destruct stop. simpl in *.
 now contradict Hvas.
  simpl in Hvas. right.
  rewrite H in Hvas.
  apply beq_nat_false in Hvas.
  apply levelEqBEqNatTrue in H. subst. unfold not.
  intros. contradict Hvas. rewrite H. reflexivity.
+ clear H H0.
assert(H0:True) by trivial.
left.
  revert HNoDup1 HNoDup2 Hvas Hlevel Hnotnull1 Hnotnull2 
  Htableroot1 (* Hstop *) Htableroot2  H0  Hroot1 Hroot2 .
  revert root1 root2 table1 table2 level1 va1 va2.
  assert (Hs :stop <= stop). omega. revert Hs.  
  generalize stop at 1 3 4 5 .
  intros.
  destruct stop0.
  simpl in *.
  now contradict Hvas.
    assert(Hzero: S stop0 < level1) by admit.
  assert (nbLevel <= nbLevel) as Hnbl by omega.
  revert Hnbl.
  revert HNoDup1 HNoDup2 Hvas Hlevel Hnotnull1 Hnotnull2 
  Htableroot1 (* Hstop *) Htableroot2 (* H0 *) Hs Hroot1 Hroot2 (* Hroot12 *) Hzero.
  revert root1 root2 table1 table2 level1 va1 va2 stop.
  unfold getIndirections.

  
  
  generalize nbLevel at 1 2 3 4 5 6 7 .

Qed. 



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
