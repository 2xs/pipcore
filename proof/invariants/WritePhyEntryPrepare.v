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
    Require Import Arith Lia Classical_Prop.


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
Lemma indirectionDescriptionInGetIndirections indirection pd partition vaToPrepare l s root:
(root=PDidx\/ root=sh1idx \/ root=sh2idx) ->
nextEntryIsPP partition root pd s ->
indirectionDescription s partition indirection root vaToPrepare l ->
In indirection (getIndirections pd s).
Proof.
intros Horroot Hpd Hind.
unfold indirectionDescription in *.
destruct Hind as (tableroot & Hpp & Hrootnotdef & Hor).
 assert(Hpdor: tableroot=pd).
 { destruct Horroot as [Horroot | [Horroot | Horroot]];subst.
  apply getPdNextEntryIsPPEq with partition s;trivial.
  apply nextEntryIsPPgetPd;trivial.
  apply getSh1NextEntryIsPPEq with partition s;trivial. 
  apply nextEntryIsPPgetFstShadow;trivial. 
  apply getSh2NextEntryIsPPEq with partition s;trivial. 
  apply nextEntryIsPPgetSndShadow;trivial. 
  }
  subst tableroot.
  destruct Hor as [Hor | Hor].
  + clear Horroot.
  intuition;subst.
  unfold getIndirections.
  pose proof nbLevelNotZero.
  destruct  nbLevel;simpl. omega.
  left;trivial.
  +
destruct Hor as (nbL & stop & Hnbl & Hstop & Hind & Hdef & Hl).
apply getIndirectionInGetIndirections with vaToPrepare nbL stop;trivial.
apply nbLevelNotZero.
  apply getNbLevelLe;trivial.
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


Lemma beq_nat_falseNot (tbl:page) :
(defaultPage =? tbl) = false -> tbl <> defaultPage.
Proof.
intros.
apply beq_nat_false in H.
unfold not;intros;subst.
now contradict H.
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
Lemma checkVAddrsEqualityWOOffsetTrueLe  :
forall stop stopi vaToPrepare vavalue nbL,
stopi <= stop ->
checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = true ->
checkVAddrsEqualityWOOffset stopi vaToPrepare vavalue nbL = true.
Proof.
induction stop;simpl.
* intros.
  assert(stopi =0) by omega.
  subst.
  simpl;trivial.
* intros.
 case_eq(StateLib.Level.eqb nbL fstLevel);intros * Hfst;rewrite Hfst in *.
  destruct stopi;simpl;trivial.
  rewrite Hfst;trivial.
  case_eq(StateLib.Level.pred nbL);intros * Hpred;rewrite Hpred in *.
  + destruct stopi;simpl;trivial.
    rewrite Hfst.
    rewrite Hpred.
    case_eq(StateLib.getIndexOfAddr vaToPrepare nbL =? StateLib.getIndexOfAddr vavalue nbL);
      intros * Hva;rewrite Hva in *;try now contradict H0.
  apply IHstop;trivial.
  omega.
 + apply levelPredNone  in Hfst.
  now contradict Hfst.
Qed.

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
forall (n : nat) (root1 root2 table1 table2 : page) (level1 : level) (va1 va2 : vaddr) (* (stop : nat) *) ,
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
(* S stop0 <= stop -> *)
root1 <> defaultPage -> root2 <> defaultPage -> S stop0 <= level1 -> n <= nbLevel ->
table1 <> table2 \/
StateLib.getIndexOfAddr va1 (CLevel (level1 -stop0)) <> StateLib.getIndexOfAddr va2 (CLevel (level1 -stop0)) .
Proof. intro H0.
intros * HNoDup1 HNoDup2 Hvas Hlevel Hnotnull1 Hnotnull2
  Htableroot1 (* Hstop *) Htableroot2 (* H0 *)  (* Hs *) Hroot1 Hroot2 (* Hroot12 *) Hzero Hnbl.  

assert(Hs: exists stop , S stop0 <= stop).
exists (S (S stop0)).
omega.
destruct Hs as (stop & Hs).
revert  HNoDup1 HNoDup2 Hvas Hlevel Hnotnull1 Hnotnull2
  Htableroot1 (* Hstop *) Htableroot2 (* H0 *)   Hs Hroot1 Hroot2 (* Hroot12 *) Hzero Hnbl.
revert n  root1 root2 table1 table2 level1 va1 va2 stop.
 induction stop0;
  intros *  HNoDup1 HNoDup2 Hvas Hlevel Hnotnull1 Hnotnull2
  Htableroot1 (* Hstop *) Htableroot2 (* H0 *)  Hs  Hroot1 Hroot2 (* Hroot12 *) Hzero Hnbl.
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
    * generalize (IHstop0  (n-1) p p0 table1 table2 pred va1 va2  stop); clear IHstop0; intros IHn.
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


Lemma checkVAddrsEqualityWOOffsetPermut' n va1 va2 level1 :
  StateLib.checkVAddrsEqualityWOOffset n va1 va2 level1 =
  StateLib.checkVAddrsEqualityWOOffset n va2 va1 level1.
Proof.
  revert va1 va2 level1.
  induction n.
  simpl. trivial.
  simpl. intros.
  case_eq (StateLib.Level.eqb level1 fstLevel); intros.
  apply NPeano.Nat.eqb_sym.
  case_eq(StateLib.Level.pred level1);
  intros; trivial.
  rewrite  NPeano.Nat.eqb_sym.
  case_eq (StateLib.getIndexOfAddr va2 level1 =? StateLib.getIndexOfAddr va1 level1); intros; trivial.
Qed.

Lemma getIndirectionInGetIndirections2n:
  forall stopn (stop : nat) (s : state) (va : vaddr) (level1 : level) (table root : page),
  stop + 1 <= nbLevel ->
  getIndirection root va level1 stop s = Some table ->
  NoDup (getIndirectionsAux root s (stop+1)) ->
  stopn <= stop ->
  table <> defaultPage -> root <> defaultPage -> stop <= level1 -> stop > 0 -> ~ In table (getIndirectionsAux root s stopn).
Proof.

intros.
apply indirectionNotInPreviousMMULevelAux in H0;trivial.
destruct H0 as ( prevtab & Hi1 & Hi2 & Hi3 ).
assert( Hnitin: ~ In table (getIndirectionsAux root s stop)).
apply getIndirectionInGetIndirections2  with prevtab va level1;trivial.
contradict Hnitin.
pose proof inclGetIndirectionsAuxLe as Hii.
unfold incl in *.
apply Hii with stopn;trivial.
omega.
rewrite  Nat.eqb_neq.
destruct defaultPage;simpl in *;destruct table;simpl in *;intuition.
subst.
apply H3.
f_equal.
apply proof_irrelevance.
Qed.  

Lemma getIndirectionStopLevelGe s va p (l: nat) (level : level)  (l0 : nat) p0:
 level <=l0 -> l = level ->  
getIndirection p va level l0 s = Some p0 ->  
getIndirection p va level l s = Some p0.
Proof.
intros.
revert p0 p level l H H0 H1.
induction l0;
intros.
subst.


apply NPeano.Nat.le_0_r in H.
rewrite H in *;trivial.
simpl.
destruct l; simpl in *.
assert (  StateLib.Level.eqb level fstLevel = true).
unfold MALInternal.Level.eqb.
apply NPeano.Nat.eqb_eq.
rewrite <- H0. unfold fstLevel. unfold CLevel.
assert ( 0 < nbLevel) by apply nbLevelNotZero.
case_eq (lt_dec 0 nbLevel ); intros.
simpl. trivial.
now contradict H2.
rewrite H2 in H1. assumption.
simpl in *.
case_eq (StateLib.Level.eqb level fstLevel); intros.
rewrite H2 in H1. destruct l0. simpl. assumption. assumption.  
+ simpl. rewrite H2 in H1.
  case_eq(StateLib.readPhyEntry p (StateLib.getIndexOfAddr va level) (memory s) ). intros.
  rewrite H3 in H1.
  case_eq (defaultPage =? p1); intros;
  rewrite H4 in H1. assumption.
  case_eq (StateLib.Level.pred level);
  intros; rewrite H5 in H1.
  apply levelPredMinus1 in H5; trivial.
  unfold CLevel in H5.  
  case_eq(lt_dec (level - 1) nbLevel ); intros; rewrite H6 in H5.
  destruct level. simpl in *. subst.
  simpl in *.
   
  apply IHl0 ; trivial. simpl. omega. simpl. omega.
  destruct level. simpl in *. omega. assumption.
  intros. rewrite H3 in H1. assumption.
Qed.

    Lemma CLevelIdentity' : forall l : level, CLevel (l -  0) = l.
Proof.
intros l.

simpl.
rewrite NPeano.Nat.sub_0_r.
apply CLevelIdentity1.
Qed.
 Lemma getIndirectionMapMMUPage11' s a (phyVaChild ptVaChildpd pd:page) e r w   entry nbL stop1 a1 (li : level):  
  (forall (stop : nat) (tbl : page) ,
        getIndirection pd a nbL stop s = Some tbl -> (defaultPage =? tbl) = false ->
        tbl <> ptVaChildpd \/  ( tbl = ptVaChildpd  /\ (StateLib.getIndexOfAddr a (CLevel (nbL-stop)) <>  StateLib.getIndexOfAddr a1 li))) ->
       lookup ptVaChildpd (StateLib.getIndexOfAddr a1 li) (memory s) beqPage beqIndex = Some (PE entry) ->
       pd <> defaultPage ->
       getIndirection pd a nbL stop1 s =
       getIndirection pd a nbL stop1
         {|
         currentPartition := currentPartition s;
         memory := add ptVaChildpd  (StateLib.getIndexOfAddr a1 li)
                     (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyVaChild |})
                     (memory s) beqPage beqIndex |}.
                     Proof.

                     
   revert pd nbL li ptVaChildpd entry.
   induction stop1.
   simpl;trivial.
   intros *  Hmykey  Hlookup Hpdnotnull.
   set(s':= {|
  currentPartition := _|}).
   simpl in *.

    case_eq( StateLib.Level.eqb nbL fstLevel);intros;trivial.
    assert(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a nbL)
    (add ptVaChildpd  (StateLib.getIndexOfAddr a1 li)
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex) =
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
    destruct defaultPage;destruct pd;simpl in *;subst.
    contradict Hpdnotnull.
    f_equal. apply  proof_irrelevance.
    destruct Hx.
    left;trivial.
    right.

rewrite CLevelIdentity'  in H0.
intuition.
    rewrite H0.
    case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a nbL) (memory s));intros;trivial.
    case_eq(defaultPage =? p);intros;trivial.
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
omega.
destruct nbL. simpl in *. omega.  apply beq_nat_false in H2.
     unfold not;intros.
     subst.
 now contradict H2.
Qed.


Lemma  readPhyEntryAddIndirectionSameTable indirection idx pg r w e p s:
StateLib.readPhyEntry indirection idx
(add indirection idx
(PE {| read := r; write := w; exec := e; present := p; user := true; pa := pg |})
(memory s) beqPage beqIndex) = Some pg.
Proof.
unfold  StateLib.readPhyEntry.
simpl.
assert(Hpairs: beqPairs (indirection, idx) (indirection, idx) beqPage beqIndex = true).
apply beqPairsTrue;split;trivial.
rewrite Hpairs;simpl;trivial.
Qed.

Lemma  isWellFormedMMUTablesAddIndirection nextIndirection indirection idx entry s:
lookup indirection idx
      (memory s) beqPage beqIndex = Some (PE entry) ->
nextIndirection <> indirection ->
isWellFormedMMUTables nextIndirection s ->
isWellFormedMMUTables nextIndirection {|
currentPartition := currentPartition s;
memory := add indirection idx
            (PE
               {|
               read := true;
               write := true;
               exec := true;
               present := true;
               user := true;
               pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
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
Lemma checkVAddrsEqualityWOOffsetFalseS:
forall stop vaToPrepare vavalue , forall (nbL:level),
StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop)) =
StateLib.getIndexOfAddr vavalue (CLevel (nbL - stop)) ->
checkVAddrsEqualityWOOffset (stop + 1) vaToPrepare vavalue nbL = false ->
checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = false.
Proof.
induction stop;simpl.
* intros.
  case_eq(StateLib.Level.eqb nbL fstLevel);intros * Hfst;rewrite Hfst in *.
  + rewrite CLevelIdentity' in H.
    rewrite H in H0.
    rewrite <- beq_nat_refl in H0.
    trivial.
  + case_eq(StateLib.Level.pred nbL );intros * Hpred;rewrite Hpred in *;try now contradict H0.
    rewrite CLevelIdentity' in H.
    rewrite H in H0.
    rewrite <- beq_nat_refl in H0.
    trivial.
* intros.
case_eq(StateLib.Level.eqb nbL fstLevel);intros * Hfst;rewrite Hfst in *;trivial.
case_eq(StateLib.Level.pred nbL );intros * Hpred;rewrite Hpred in *;try now contradict H0;
trivial.
case_eq( StateLib.getIndexOfAddr vaToPrepare nbL =? StateLib.getIndexOfAddr vavalue nbL); intros
* Hvas;rewrite Hvas in *;trivial.
apply IHstop;trivial.
 replace (nbL - S stop) with (l - stop) in *.
 trivial.
 assert(l = CLevel (nbL - 1)).
 apply levelPredMinus1;trivial.
 rewrite H1.
unfold CLevel .
case_eq( lt_dec (nbL - 1) nbLevel);intros * Hl;simpl.
omega.
destruct nbL. simpl in *. omega.
Qed.

Lemma getIndirectionAddIndirectionCheckVaddrsFalse  vapg l indirection vaToPrepare nextIndirection p pg indMMUToPrepare entry partition  s:
let s' := {|
      currentPartition := currentPartition s;
      memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
                  (PE
                     {|
                     read := true;
                     write := true;
                     exec := true;
                     present := true;
                     user := true;
                     pa := nextIndirection |}) (memory s) beqPage beqIndex |} in
 
 getIndirection indirection vapg l (nbLevel - 1) s' = Some p ->
 (defaultPage =? p) = false ->
 Some l = StateLib.getNbLevel ->
 false = StateLib.Level.eqb l fstLevel ->

lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex =
          Some (PE entry) ->
nextEntryIsPP partition PDidx indirection s ->
indirection <> defaultPage ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
(defaultPage =? nextIndirection) = false ->
 isWellFormedMMUTables nextIndirection s ->
 nextIndirection <> indirection ->
pg <> defaultPage ->
noDupConfigPagesList s ->
StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel) (memory s') = Some true ->
StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg fstLevel) (memory s') = Some pg  ->


partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
               
 getIndirection indirection vapg l (nbLevel - 1) s =
 getIndirection indirection vapg l (nbLevel - 1)  s'.
Proof.
intros s' Hindx' Hnotdefp Hl Hlevel  Hlookup Hpp Hrootnotdef Hdef Hdef'
Hnextnotdef Hinit Hnextnoteq HHkey Hnodupcons Hpres Hread .
intros.
rewrite Hindx'.
assert(Hnodup : NoDup (getIndirections indirection s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition PDidx ;trivial.
apply Hnodupcons;trivial.
left;trivial. }
assert(Hlvl: nbLevel - 1  = l).
{ apply getNbLevelEq in Hl.
  subst.
  rewrite <- nbLevelEq;trivial. }
assert(Hnotfstl: l > 0) by (apply levelEqBEqNatFalse0;symmetry;trivial).
assert(HnbLgt: (nbLevel-1) > 0) by omega.
assert(Htruenbl:  (nbLevel - 1) <= l) by omega.
destruct (nbLevel - 1);simpl in *;trivial.
rewrite <- Hlevel in *.
assert( (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vapg l) \/
(StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vapg l))as [Hvadsl|Hvadsl] by apply indexDecOrNot.
+ case_eq( StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel)
            (add indirection (StateLib.getIndexOfAddr vaToPrepare l)
               (PE
                  {|
                  read := true;
                  write := true;
                  exec := true;
                  present := true;
                  user := true;
                  pa := nextIndirection |}) (memory s) beqPage beqIndex));intros * Hxx;rewrite Hxx in *;try now contradict Hvapg.
        assert(Hreads:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vapg l)
               (memory s) = Some indMMUToPrepare).
        { apply isEntryPageReadPhyEntry1;trivial.
        rewrite <- Hvadsl.
        trivial. }
        rewrite Hreads in *.
        assert(Hreads': StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vapg l)
             (add indirection (StateLib.getIndexOfAddr vapg l)
                (PE
                   {|
                   read := true;
                   write := true;
                   exec := true;
                   present := true;
                   user := true;
                   pa := nextIndirection |}) (memory s) beqPage beqIndex) = Some nextIndirection).
        apply readPhyEntryAddIndirectionSameTable.
        rewrite Hvadsl in *.
        rewrite Hreads' in *.
        rewrite Hnextnotdef in *.
       (*  rewrite <- Hindx'. *)
        rewrite Hdef'  in *.        
        case_eq(StateLib.Level.pred l);intros * Hpred;rewrite Hpred in *.
       
       
       
       
         assert(Hs0: n=0 \/ n >0) by omega.
        destruct Hs0.
        subst;simpl in *.
        inversion Hindx'.
        subst p.
        case_eq(b);intros * Hb;rewrite Hb in *;try now contradict Hvapg. (*
       
        move Hvapg at bottom. *)
        assert(Hkey : StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vapg fstLevel)
            (add indirection (StateLib.getIndexOfAddr vapg l)
               (PE
                  {|
                  read := true;
                  write := true;
                  exec := true;
                  present := true;
                  user := true;
                  pa := nextIndirection |}) (memory s) beqPage beqIndex) = Some defaultPage).
          assert(Hwell':  isWellFormedMMUTables nextIndirection s').
          apply isWellFormedMMUTablesAddIndirection with entry;trivial.
          rewrite Hvadsl;trivial.
          unfold isWellFormedMMUTables in Hwell'.
          generalize (Hwell' (StateLib.getIndexOfAddr vapg fstLevel) ) ; clear Hwell'; intros (Hwell'1 & Hwell'2) .
          simpl in *.
          rewrite <- Hvadsl.
          trivial.
          rewrite Hkey in Hread.
          inversion Hread.
          subst.
          now contradict HHkey.
          now contradict Hpres.
         
          destruct n;simpl in *;try omega.
          case_eq(StateLib.Level.eqb l0 fstLevel);intros * Hpredl0;rewrite Hpredl0 in *.
           case_eq(b);intros * Hb;rewrite Hb in *;try now contradict Hvapg.
        inversion Hindx';subst p.
        assert(Hkey : StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vapg fstLevel)
            (add indirection (StateLib.getIndexOfAddr vapg l)
               (PE
                  {|
                  read := true;
                  write := true;
                  exec := true;
                  present := true;
                  user := true;
                  pa := nextIndirection |}) (memory s) beqPage beqIndex) = Some defaultPage).
          assert(Hwell':  isWellFormedMMUTables nextIndirection s').
          apply isWellFormedMMUTablesAddIndirection with entry;trivial.
          rewrite Hvadsl;trivial.
          unfold isWellFormedMMUTables in Hwell'.
          generalize (Hwell' (StateLib.getIndexOfAddr vapg fstLevel) ) ; clear Hwell'; intros (Hwell'1 & Hwell'2) .
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
                   read := true;
                   write := true;
                   exec := true;
                   present := true;
                   user := true;
                   pa := nextIndirection |}) (memory s) beqPage beqIndex) = Some defaultPage).
          assert(Hwell':  isWellFormedMMUTables nextIndirection s').
          apply isWellFormedMMUTablesAddIndirection with entry;trivial.
          rewrite Hvadsl;trivial.
          unfold isWellFormedMMUTables in Hwell'.
          generalize (Hwell' (StateLib.getIndexOfAddr vapg l0) ) ; clear Hwell'; intros (Hwell'1 & Hwell'2) .
          simpl in *.
          rewrite Hvadsl in *.
          trivial.
          rewrite Hkey in Hindx'.
          assert(Htruedef: (defaultPage =? defaultPage) = true).
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
                (PE {| read := true; write := true; exec := true; present := true; user := true; pa := nextIndirection |})
                (memory s) beqPage beqIndex)).
  {              apply readPhyEntryMapMMUPage with entry;trivial.
                right;intuition. }
                rewrite <- Hreads in *. clear Hreads.
   case_eq(StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vapg l) (memory s));intros * Hreadss;rewrite Hreadss in *
   ;try now contradict Hindx'.
   case_eq(defaultPage =? p0);intros * Hdef2;rewrite Hdef2 in *;trivial.
   case_eq(StateLib.Level.pred l );intros * Hpred;rewrite Hpred in *;try now contradict Hindx'.
   rewrite <- Hindx'.
 apply  getIndirectionMapMMUPage11 with entry;trivial.
      intros * Hi1 Hi2.
     
     assert(Horstop : S(stop+1) <= nbLevel \/ S(stop+1) > nbLevel) by omega.
      destruct Horstop as [Horstop|Horstop].
      -
        assert(Hin:  In indirection (getIndirectionsAux indirection s (stop+1) )).
      { replace (stop+1) with (S stop) by omega.
      simpl. left;trivial. }
      assert(~ In tbl (getIndirectionsAux indirection s (stop+1) )).
     
      { apply getIndirectionInGetIndirections2' with vapg l;trivial. omega.
      replace (stop+1) with (S stop) by omega.
      simpl.
      rewrite <- Hlevel
      .
      rewrite Hreadss.
      rewrite Hdef2.
      rewrite Hpred;trivial.
      apply noDupPreviousMMULevels with nbLevel;trivial.

     
      omega.
     
      apply beq_nat_falseNot;trivial.
           assert(Hlvlx: nbLevel - 1  = l).
       
      {
apply getNbLevelEq in Hl.
subst.
rewrite <- nbLevelEq;trivial. }
      omega.
      omega. }
     
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
omega.
omega.

      unfold CLevel in Hpred.
case_eq(lt_dec (l - 1) nbLevel);intros * Hll;rewrite Hll in *.
subst.
simpl in *.
omega.
omega.
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
subst;omega. left;trivial.  }

 assert(~ In tbl (getIndirectionsAux indirection s (nbLevel-1) )).
     
      { pose proof nbLevelNotZero.
       apply getIndirectionInGetIndirections2' with vapg l;trivial.
        omega.
     

destruct (nbLevel-1);simpl.
subst;omega.
rewrite <- Hlevel.
rewrite Hreadss.
rewrite Hdef2.
rewrite Hpred.
 
      replace (S n0 - 1) with n0 in * by omega.
      trivial.
     
unfold getIndirections in *.
replace  (nbLevel - 1 + 1) with nbLevel by omega.
trivial.
assert(Htruex:  (defaultPage =? tbl) = false) by trivial.
apply beq_nat_false in Htruex.
unfold not;intros;subst;try now contradict Htruex.
     
      omega. omega. }
      unfold not;intros ;subst;now contradict Hin.
            - apply beq_nat_false in Hdef2.
unfold not;intros;subst;try now contradict Hdef2.
Qed.



Lemma getMappedPageSomeAddIndirectionSamePartSSI1 s (indirection nextIndirection :page) vaToPrepare entry  vavalue pd pg partition l
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
 {
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
now contradict H4. }
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
apply checkVAddrsEqualityWOOffsetTrueLe with (stop+1);trivial.
  omega.
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
(* case_eq( getIndirection pd vavalue nbL (nbLevel - 1) s');intros * Hind'. *)

assert(Heq: getIndirection pd vavalue nbL (nbLevel - 1) s =
            getIndirection pd vavalue nbL (nbLevel - 1) s').
{  assert(Horlst: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vavalue l) \/  
(StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vavalue l) ) by apply indexDecOrNot.
destruct Horlst as [Horlst| Horlst].
+


 assert( Hnewvaddr: checkVAddrsEqualityWOOffset (stop ) vaToPrepare vavalue nbL = false ).
{ apply checkVAddrsEqualityWOOffsetFalseS;trivial.

 subst;trivial. }
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by omega.
destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
destruct nbL;simpl in *.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
subst;trivial.
-

subst.
assert(Hor: stop=0 \/ stop > 0) by omega.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
case_eq( StateLib.Level.eqb nbL fstLevel);intros * Hlvl;rewrite Hlvl in *.
rewrite CLevelIdentity' in Hfstl.
rewrite <- Hfstl in Hlvl.
now contradict Hlvl.
 now contradict Hvaddr.
* assert(Hrn: S (stop-1) = stop) by omega.
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

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by omega.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try omega.
apply getIndirectionStopLevelGe with stop0;trivial.
omega.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try omega.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
+ assert(checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = true \/
checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = false) .
{ destruct (checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL).
  left;trivial.
  right;trivial. }
destruct H.
**  assert(Hinstop1: getIndirection pd vaToPrepare nbL (stop+1) s = Some indMMUToPrepare).
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
}
assert(HindeqStop: getIndirection pd vaToPrepare nbL stop s=
getIndirection pd vavalue nbL stop  s).

apply getIndirectionEqStop;subst;trivial.
apply beq_nat_true in Hdefcurind.

apply getIndirectionMapMMUPage11' with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by omega.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
destruct nbL;simpl in *.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
{ assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
 }

pose proof inclGetIndirectionsAuxLe as Hproof.
left.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
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

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by omega.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try omega.
apply getIndirectionStopLevelGe with stop0;trivial.
omega.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }left.

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try omega.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }
left.

unfold not;intros;subst;now contradict Hnotinind.
 }
**
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by omega.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
destruct nbL;simpl in *.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
subst;trivial.
-

subst.
assert(Hor: stop=0 \/ stop > 0) by omega.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
inversion Hi1;subst.

inversion Hindi;subst.
now contradict H.
* assert(Hrn: S (stop-1) = stop) by omega.
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

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by omega.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try omega.
apply getIndirectionStopLevelGe with stop0;trivial.
omega.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try omega.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
 } }
 rewrite <- Heq.
 rewrite Hind.
 rewrite Hnotdef'.
 assert(Hkey: p <> indirection \/ StateLib.getIndexOfAddr vavalue fstLevel <> StateLib.getIndexOfAddr vaToPrepare l).
{    subst.
    assert(Horx: stop = nbL \/ stop <> nbL) by omega.
    destruct Horx as [Horx | Horx].
    subst.
    replace (nbL - nbL) with 0 in Hfstl.
    unfold fstLevel in Hfstl.
    unfold StateLib.Level.eqb in Hfstl.
    rewrite <- beq_nat_refl in Hfstl.
    now contradict Hfstl.
    omega.
    assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }
 assert(~In p (getIndirectionsAux pd s (stop+1))).
{
pose proof nbLevelNotZero as HnbL0.
 
apply getIndirectionInGetIndirections2n with (nbLevel - 1) vavalue nbL;trivial;try omega.
replace (nbLevel - 1 + 1) with nbLevel by omega.
unfold getIndirections in *.
trivial.
apply beq_nat_false in Hnotdef'.
unfold not;intros;subst;now contradict Hnotdef'. }
assert(In indirection (getIndirectionsAux pd s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
 left.
 unfold not;intros;subst;now contradict H0.
 }
 
 assert(Hpres: StateLib.readPresent p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s)=
 StateLib.readPresent p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s')).
 {  apply readPresentMapMMUPage with entry;trivial. }
 assert(Hread: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s)=
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s')).
 {  apply readPhyEntryMapMMUPage with entry;trivial. }
 

 rewrite <- Hread.
 rewrite <- Hpres.
 trivial.
 Qed.


Lemma getAccessibleMappedPageSomeAddIndirectionSamePartSSI1 s (indirection nextIndirection :page) vaToPrepare entry  vavalue pd pg partition l
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
getAccessibleMappedPage pd s vavalue = SomePage pg ->
false = StateLib.Level.eqb l fstLevel ->
 getAccessibleMappedPage pd  {|
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
unfold getAccessibleMappedPage, indirectionDescription in *.
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
 {
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
now contradict H4. }
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

assert(StateLib.readAccessible p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s') =
StateLib.readAccessible p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s)).
apply readAccessibleMapMMUPage ;trivial.
left;intuition.
rewrite H2.

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
apply checkVAddrsEqualityWOOffsetTrueLe with (stop+1);trivial.
  omega.
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
(* case_eq( getIndirection pd vavalue nbL (nbLevel - 1) s');intros * Hind'. *)

assert(Heq: getIndirection pd vavalue nbL (nbLevel - 1) s =
            getIndirection pd vavalue nbL (nbLevel - 1) s').
{ assert(Horlst: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vavalue l) \/  
(StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vavalue l) ) by apply indexDecOrNot.
destruct Horlst as [Horlst| Horlst].
+


 assert( Hnewvaddr: checkVAddrsEqualityWOOffset (stop ) vaToPrepare vavalue nbL = false ).
{ apply checkVAddrsEqualityWOOffsetFalseS;trivial.

 subst;trivial. }
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by omega.
destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
destruct nbL;simpl in *.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
subst;trivial.
-

subst.
assert(Hor: stop=0 \/ stop > 0) by omega.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
case_eq( StateLib.Level.eqb nbL fstLevel);intros * Hlvl;rewrite Hlvl in *.
rewrite CLevelIdentity' in Hfstl.
rewrite <- Hfstl in Hlvl.
now contradict Hlvl.
 now contradict Hvaddr.
* assert(Hrn: S (stop-1) = stop) by omega.
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

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by omega.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try omega.
apply getIndirectionStopLevelGe with stop0;trivial.
omega.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try omega.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
+ assert(checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = true \/
checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = false) .
{ destruct (checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL).
  left;trivial.
  right;trivial. }
destruct H.
**  assert(Hinstop1: getIndirection pd vaToPrepare nbL (stop+1) s = Some indMMUToPrepare).
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
}
assert(HindeqStop: getIndirection pd vaToPrepare nbL stop s=
getIndirection pd vavalue nbL stop  s).

apply getIndirectionEqStop;subst;trivial.
apply beq_nat_true in Hdefcurind.

apply getIndirectionMapMMUPage11' with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by omega.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
destruct nbL;simpl in *.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
{ assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
 }

pose proof inclGetIndirectionsAuxLe as Hproof.
left.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
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

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by omega.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try omega.
apply getIndirectionStopLevelGe with stop0;trivial.
omega.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }left.

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try omega.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }
left.

unfold not;intros;subst;now contradict Hnotinind.
 }
**
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by omega.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vavalue nbL;trivial.
destruct nbL;simpl in *.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
subst;trivial.
-

subst.
assert(Hor: stop=0 \/ stop > 0) by omega.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
inversion Hi1;subst.

inversion Hindi;subst.
now contradict H.
* assert(Hrn: S (stop-1) = stop) by omega.
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

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by omega.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vavalue nbL;trivial;try omega.
apply getIndirectionStopLevelGe with stop0;trivial.
omega.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vavalue nbL;trivial;try omega.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
 } }
 rewrite <- Heq.
 rewrite Hind.
 rewrite Hnotdef'.
 assert(Hkey: p <> indirection \/ StateLib.getIndexOfAddr vavalue fstLevel <> StateLib.getIndexOfAddr vaToPrepare l).
{    subst.
    assert(Horx: stop = nbL \/ stop <> nbL) by omega.
    destruct Horx as [Horx | Horx].
    subst.
    replace (nbL - nbL) with 0 in Hfstl.
    unfold fstLevel in Hfstl.
    unfold StateLib.Level.eqb in Hfstl.
    rewrite <- beq_nat_refl in Hfstl.
    now contradict Hfstl.
    omega.
    assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }
 assert(~In p (getIndirectionsAux pd s (stop+1))).
{
pose proof nbLevelNotZero as HnbL0.
 
apply getIndirectionInGetIndirections2n with (nbLevel - 1) vavalue nbL;trivial;try omega.
replace (nbLevel - 1 + 1) with nbLevel by omega.
unfold getIndirections in *.
trivial.
apply beq_nat_false in Hnotdef'.
unfold not;intros;subst;now contradict Hnotdef'. }
assert(In indirection (getIndirectionsAux pd s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
 left.
 unfold not;intros;subst;now contradict H0.
 }
 
 assert(Hpres: StateLib.readPresent p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s)=
 StateLib.readPresent p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s')).
 {  apply readPresentMapMMUPage with entry;trivial. }
 assert(Haccess: StateLib.readAccessible p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s') =
StateLib.readAccessible p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s)).
apply readAccessibleMapMMUPage ;trivial.

 assert(Hread: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s)=
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s')).
 {  apply readPhyEntryMapMMUPage with entry;trivial. }
 

 rewrite <- Hread.
 rewrite  Haccess.
 rewrite <- Hpres.
 trivial.
 Qed.



Lemma getMappedPagesAuxAddIndirectionSSI1 s indirection nextIndirection  entry nbLgen valist pd pg indMMUToPrepare vaToPrepare partition l:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
noDupConfigPagesList s ->
In pg (getMappedPagesAux pd valist s) ->

partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP partition PDidx pd s ->
nextIndirection <> indirection ->

 In pg  (getMappedPagesAux pd valist {|
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
intros Hlookup Hl Hroot Hdef Hdef' Hinit Hlevel Hnodupcons.
unfold getMappedPagesAux.
intros Hgoal.
intros.
assert(Hnodup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition PDidx ;trivial.
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
 assert(Hpdor: tableroot=pd).
 { apply getPdNextEntryIsPPEq with partition s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
  subst tableroot.
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
  *  apply getMappedPageSomeAddIndirectionSamePartSSI1 with entry partition indMMUToPrepare;trivial.
    unfold indirectionDescription in *.
    exists indirection.
    split;trivial.
     split;trivial.
     left;split;trivial.
     
 -  apply getMappedPageSomeAddIndirectionSamePartSSI1 with entry partition indMMUToPrepare;trivial.
     unfold indirectionDescription in *.
    exists pd.
    split;trivial.
     split;trivial.
     right;trivial. }
Qed.

 Lemma  isPresentNotDefaultIffMapMMUPage  s phyVaChild  ptVaChildpd idxvaChild r w e
     (* idxvaInCurPart ptVaInCurPartpd *)
entry
:
lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) ->
(* entryPresentFlag ptVaInCurPartpd idxvaInCurPart false s ->
isEntryPage ptVaInCurPartpd idxvaInCurPart phyVaChild s ->  *)
phyVaChild <> defaultPage ->
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
                     pa := phyVaChild |}) (memory s) beqPage beqIndex |}.
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
        pa := phyVaChild |}) (memory s) beqPage beqIndex)=
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
        pa := phyVaChild |}) (memory s) beqPage beqIndex)=
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
assert(Htrue: beqPairs (ptVaChildpd, idxvaChild) (ptVaChildpd, idxvaChild) beqPage
           beqIndex = true).
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
  getIndirection pd a level stop s = Some tbl -> (defaultPage =? tbl) = false -> stop1>  stop -> tbl <> ptVaChildpd) ->
 lookup ptVaChildpd idxvaChild (memory s) beqPage beqIndex = Some (PE entry) ->
 pd <> defaultPage ->
 getIndirection pd a level stop1 s =
 getIndirection pd a level stop1
   {|
   currentPartition := currentPartition s;
   memory := add ptVaChildpd idxvaChild
               (PE {| read := r; write := w; exec := e; present := true; user := true; pa := phyVaChild |})
               (memory s) beqPage beqIndex |}.
Proof.
   induction stop1.
   simpl;trivial.
   simpl in *.
   intros *  Hmykey Hlookup Hpdnotnull.
    case_eq( StateLib.Level.eqb level fstLevel);intros;trivial.
    assert(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a level)
    (add ptVaChildpd idxvaChild
       (PE
          {|
          read := r;
          write := w;
          exec := e;
          present := true;
          user := true;
          pa := phyVaChild |}) (memory s) beqPage beqIndex) =
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
    destruct defaultPage;destruct pd;simpl in *;subst.
    contradict Hpdnotnull.
    f_equal. apply  proof_irrelevance.
    omega.
    rewrite H0.
    case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr a level) (memory s));intros;trivial.
    case_eq(defaultPage =? p);intros;trivial.
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
     omega.
     
     apply beq_nat_false in H2.
     unfold not;intros.
     subst. now contradict H2.
Qed.

Lemma getMappedPageSomeAddIndirectionSSI2 s indirection nextIndirection vapg entry nbLgen  pd pg indMMUToPrepare vaToPrepare partition l:
isPresentNotDefaultIff s ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
noDupConfigPagesList s ->
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
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |} vapg = SomePage pg ->

partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP partition PDidx pd s ->
nextIndirection <> indirection ->
getMappedPage pd s vapg = SomePage pg.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hprecons Hlookup Hl Hroot Hdef Hdef' Hinit Hlevel Hnodupcons Hvapg.
intros.

unfold indirectionDescription,  initPEntryTablePreconditionToPropagatePrepareProperties in *.
destruct Hroot as (tableroot & Hpp & Hrootnotdef & Hor).
 assert(Hpdor: tableroot=pd).

 { apply getPdNextEntryIsPPEq with partition s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
  subst tableroot.
 assert(Hnodup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition PDidx ;trivial.
apply Hnodupcons;trivial.
left;trivial. }

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
        omega. }
      destruct (nbLevel - 1);
      simpl in Hind;try omega.
      rewrite Hlevel in Hind.
      simpl in Hind.
     
      assert(Hread:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l)
           (add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex) = Some nextIndirection).    
                apply readPhyEntryAddIndirectionSameTable.
      rewrite Hread in Hind.
      assert(Hnext: (defaultPage =? nextIndirection) = false) by trivial.
      rewrite Hnext in Hind.
      assert(Hwell':  isWellFormedMMUTables nextIndirection s').
      apply isWellFormedMMUTablesAddIndirection with entry;trivial.
      unfold isWellFormedMMUTables in Hwell'.
     
      case_eq( StateLib.Level.pred l );intros * Hpred;rewrite Hpred in *;try now contradict Hind.
      destruct n;simpl in Hind.
      +  generalize (Hwell'  (StateLib.getIndexOfAddr vaToPrepare fstLevel) ); clear Hwell'; intros (Hi1 & Hi2).
       inversion Hind. subst p.
      rewrite Hnext.                    
     
      rewrite Hi2.
       right;trivial.
      +  
        case_eq(StateLib.Level.eqb l0 fstLevel);intros * Hl0;rewrite Hl0 in *.
        - generalize (Hwell'  (StateLib.getIndexOfAddr vaToPrepare fstLevel) ); clear Hwell'; intros (Hi1 & Hi2).
          inversion Hind;subst p.
          rewrite Hnext.
          rewrite Hi2.
           right;trivial.
        - generalize (Hwell'  (StateLib.getIndexOfAddr vaToPrepare l0) ); clear Hwell'; intros (Hi1 & Hi2).
          simpl in *.
          rewrite   Hi1 in Hind.
       assert(Hdeftrue: (defaultPage =? defaultPage)=true). symmetry. apply beq_nat_refl.
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
  assert(Hor :checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = true \/
         checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = false).
  { destruct (checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l);intuition. }
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
 assert(HHkey: pg<> defaultPage) .
  {
   revert Hvapg Hlookup Hprecons.
    assert(Hnotdef: (defaultPage =? nextIndirection) = false) by trivial.
    revert Hnotdef.
    clear .
    unfold getMappedPage.
    intros.
    destruct (StateLib.getNbLevel);try now contradict Hvapg.
    destruct ( getIndirection indirection vapg l0 (nbLevel - 1) s');try now contradict Hvapg.
    destruct (defaultPage =? p);try now contradict Hvapg.
    case_eq( StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel) (memory s') );intros * Hpres;rewrite Hpres in *;try now contradict Hvapg.
    case_eq (b);intros * Hb ;rewrite Hb in *;try now contradict Hvapg.
    case_eq(StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg fstLevel) (memory s'));intros * Hread;
    rewrite Hread in *;try now contradict Hvapg.
   
    inversion Hvapg;subst.
    assert(Hcons':  isPresentNotDefaultIff s').
    { intros. eapply isPresentNotDefaultIffMapMMUPage with entry;trivial.
    apply beq_nat_falseNot;trivial.
   
   
    }
    unfold isPresentNotDefaultIff in Hcons'.
    generalize(Hcons' p (StateLib.getIndexOfAddr vapg fstLevel) );clear Hcons';
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
      case_eq(defaultPage =? p);intros * Hnotdefp;rewrite Hnotdefp in Hvapg;try now contradict Hnotdefp.
    case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel) (memory s'));intros * Hpres;rewrite Hpres in *;try now contradict Hvapg.
    case_eq(b);intros * Hb;rewrite Hb in *;subst;try now contradict Hvapg.
    case_eq(StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg fstLevel) (memory s'));intros * Hread;
    rewrite Hread in *;try now contradict Hvapg.
    inversion Hvapg;subst.
    assert(Hindeq: getIndirection indirection vapg l (nbLevel - 1) s =
    getIndirection indirection vapg l (nbLevel - 1) s').
    { apply getIndirectionAddIndirectionCheckVaddrsFalse with p pg indMMUToPrepare entry partition;trivial. }
    rewrite <- Hindeq in *.
    case_eq(getIndirection indirection vapg l (nbLevel - 1) s);intros * Hine;rewrite Hine in *; try now contradict Hvapg.
    case_eq(defaultPage =? p);intros * Hdefi;rewrite Hdefi in *; try now contradict Hvapg.
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
    omega.
    left;trivial. }
    assert(Ht2: ~In p (getIndirectionsAux indirection s (nbLevel-1))).
    { apply getIndirectionInGetIndirections2' with vapg l;trivial.
    omega.
    unfold noDupConfigPagesList in *.
    unfold getIndirections in *.
    replace (nbLevel -1 + 1) with nbLevel by omega.
    trivial.
    apply beq_nat_false in Hdefi.
    destruct defaultPage;simpl in *;destruct p;simpl in *.
    unfold not;intros xxx;simpl in *.
    inversion xxx.
    subst.
    now contradict Hdefi.
   
omega. }

unfold not;intros;subst;now contradict Ht2. }

assert(Hpreseq: StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel) (memory s')=
StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel) (memory s)).
symmetry.
apply readPresentMapMMUPage with entry;trivial.
left;trivial.
assert(Hreadeq: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg fstLevel) (memory s')=
StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg fstLevel) (memory s)).
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
omega.

omega. }

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
      omega.
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
    case_eq(defaultPage =? p);intros * Hdefs';rewrite Hdefs' in *;try now contradict Hvapg.
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
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
subst;trivial.
+ simpl. subst.
  rewrite <- Hlevel.
  rewrite readPhyEntryAddIndirectionSameTable.
  assert(Hnext: (defaultPage =? nextIndirection) = false) by trivial.
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
    assert(Hor: stop + 1+1 <= nbLevel-1 \/ stop + 1+1 > nbLevel-1 ) by omega.
    destruct Hor as [Hor | Hor].
    * rewrite HindeqStop in Hi.
     
    assert(Hii:  getIndirection pd vapg nbL (stop + 1 +1 ) s' = Some defaultPage).
    {  apply getIndirectionStopS1 with nextIndirection;trivial. omega.
        apply beq_nat_falseNot;trivial.
        simpl.
      case_eq(StateLib.Level.eqb (CLevel (nbL - (stop + 1))) fstLevel);intros * Hfst.
      apply levelEqBEqNatTrue0 in Hfst.
      rewrite <- Hnbleq in Hfst.
      unfold CLevel in Hfst.
      case_eq(lt_dec (nbLevel - 1 - (stop + 1)) nbLevel) ; intros * Hls;rewrite Hls in *;simpl in *.
      rewrite <- Hnbleq in Hstp.
      omega.
      omega.
      rewrite Hv.
      assert(Hread:  StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vapg (CLevel (nbL - (stop + 1))))
      (memory s') = Some defaultPage).
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
    assert(Hdefx: getIndirection pd vapg nbL (nbLevel - 1) s' = Some defaultPage).
    { apply getIndirectionNbLevelEq with (stop+1 +1);trivial.
      omega.
      rewrite <- Hnbleq.
      trivial. }
      rewrite Hinds' in Hdefx.
      inversion Hdefx.
      subst.
      rewrite <- beq_nat_refl in Hdefs'.
      now contradict Hdefx.
    *  assert(Htrueeq: stop+1 = nbL) by omega.
      rewrite Htrueeq in *.
      rewrite Hnbleq in *.
      rewrite HindeqStop in Hi.
      rewrite Hinds' in Hi.
      inversion Hi;subst.
      assert(Hconspres: StateLib.readPresent nextIndirection (StateLib.getIndexOfAddr vapg fstLevel)
       (memory s') = Some false).
             assert(Hwell':  isWellFormedMMUTables nextIndirection s').
          apply isWellFormedMMUTablesAddIndirection with entry;trivial.
          unfold isWellFormedMMUTables in Hwell'.
          generalize (Hwell' (StateLib.getIndexOfAddr vapg fstLevel) ) ; clear Hwell'; intros .
          intuition.
          rewrite Hconspres in *.
          now contradict Hvapg.
+ case_eq ( getIndirection pd vapg nbL (nbLevel - 1) s');intros * Hinds';rewrite Hinds' in *;try now contradict Hvapg.
  case_eq(defaultPage =? p) ; intros * Hps';rewrite Hps' in *;try now contradict Hvapg.
  assert(Heqs':  getIndirection pd vapg nbL (nbLevel - 1) s =
   getIndirection pd vapg nbL (nbLevel - 1) s').
  {  assert(Horlst: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vapg l) \/  
(StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vapg l) ) by apply indexDecOrNot.
destruct Horlst as [Horlst| Horlst].
+


 assert( Hnewvaddr: checkVAddrsEqualityWOOffset (stop ) vaToPrepare vapg nbL = false ).
{ apply checkVAddrsEqualityWOOffsetFalseS;trivial.

 subst;trivial. }
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by omega.
destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vapg nbL;trivial.
destruct nbL;simpl in *.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
subst;trivial.
- subst.
assert(Hor: stop=0 \/ stop > 0) by omega.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
case_eq( StateLib.Level.eqb nbL fstLevel);intros * Hlvl;rewrite Hlvl in *.
rewrite CLevelIdentity' in Hlevel.
rewrite <- Hlevel in Hlvl.
now contradict Hlvl.
 now contradict Hvaddr.
* assert(Hrn: S (stop-1) = stop) by omega.
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

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by omega.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vapg nbL;trivial;try omega.
apply getIndirectionStopLevelGe with stop0;trivial.
omega.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vapg nbL;trivial;try omega.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
+ assert(Horstop: checkVAddrsEqualityWOOffset stop vaToPrepare vapg nbL = true \/
checkVAddrsEqualityWOOffset stop vaToPrepare vapg nbL = false) .
{ destruct (checkVAddrsEqualityWOOffset stop vaToPrepare vapg nbL).
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
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by omega.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vapg nbL;trivial.
destruct nbL;simpl in *.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
{ assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
 }

pose proof inclGetIndirectionsAuxLe as Hproof.
left.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
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

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by omega.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{
 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vapg nbL;trivial;try omega.
apply getIndirectionStopLevelGe with stop0;trivial.
omega.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }left.

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vapg nbL;trivial;try omega.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }
left.

unfold not;intros;subst;now contradict Hnotinind.
 }
**
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by omega.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vapg nbL;trivial.
destruct nbL;simpl in *.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
subst;trivial.
-

subst.
assert(Hor: stop=0 \/ stop > 0) by omega.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
inversion Hi1;subst.

inversion Hind;subst.
now contradict H.
* assert(Hrn: S (stop-1) = stop) by omega.
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

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by omega.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vapg nbL;trivial;try omega.
apply getIndirectionStopLevelGe with stop0;trivial.
omega.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vapg nbL;trivial;try omega.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
 } }
rewrite  Heqs'.
 rewrite Hinds'.
 rewrite Hps'.
 assert(Hkey: p <> indirection \/ StateLib.getIndexOfAddr vapg fstLevel <> StateLib.getIndexOfAddr vaToPrepare l).
{    subst.
    assert(Horx: stop = nbL \/ stop <> nbL) by omega.
    destruct Horx as [Horx | Horx].
    subst.
    replace (nbL - nbL) with 0 in Hlevel.
    unfold fstLevel in Hlevel.
    unfold StateLib.Level.eqb in Hlevel.
    rewrite <- beq_nat_refl in Hlevel.
    now contradict Hlevel.
    omega.
    assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }
 assert(~In p (getIndirectionsAux pd s (stop+1))).
{
pose proof nbLevelNotZero as HnbL0.
 
apply getIndirectionInGetIndirections2n with (nbLevel - 1) vapg nbL;trivial;try omega.
rewrite Heqs';trivial.
replace (nbLevel - 1 + 1) with nbLevel by omega.
unfold getIndirections in *.
trivial.
apply beq_nat_false in Hps'.
unfold not;intros;subst;now contradict Hps'. }
assert(In indirection (getIndirectionsAux pd s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
 left.
 unfold not;intros;subst;now contradict H0.
 }
 
 assert(Hpres: StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel) (memory s)=
 StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel) (memory s')).
 {  apply readPresentMapMMUPage with entry;trivial. }
 assert(Hread: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg fstLevel) (memory s)=
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg fstLevel) (memory s')).
 {  apply readPhyEntryMapMMUPage with entry;trivial. }
 

 rewrite  Hread.
 rewrite  Hpres.
 trivial.

Qed.

Lemma getAccessibleMappedPageSomeAddIndirectionSSI2 s indirection nextIndirection vapg entry nbLgen  pd pg indMMUToPrepare vaToPrepare partition l:
isPresentNotDefaultIff s ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
noDupConfigPagesList s ->
getAccessibleMappedPage pd  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |} vapg = SomePage pg ->

partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP partition PDidx pd s ->
nextIndirection <> indirection ->
getAccessibleMappedPage pd s vapg = SomePage pg.
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hprecons Hlookup Hl Hroot Hdef Hdef' Hinit Hlevel Hnodupcons Hvapg.
intros.

unfold indirectionDescription,  initPEntryTablePreconditionToPropagatePrepareProperties in *.
destruct Hroot as (tableroot & Hpp & Hrootnotdef & Hor).
 assert(Hpdor: tableroot=pd).

 { apply getPdNextEntryIsPPEq with partition s;trivial.
  apply nextEntryIsPPgetPd;trivial. }
  subst tableroot.
 assert(Hnodup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition PDidx ;trivial.
apply Hnodupcons;trivial.
left;trivial. }

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
  assert(Hnone: getAccessibleMappedPage indirection s vaToPrepare = NonePage).
  { unfold getAccessibleMappedPage.
    rewrite <- HnbL.
    rewrite Hnoneind.
    assert(Heq: true=(defaultPage =? defaultPage)).
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
        omega. }
      destruct (nbLevel - 1);
      simpl in Hind;try omega.
      rewrite Hlevel in Hind.
      simpl in Hind.
     
      assert(Hread:  StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr vaToPrepare l)
           (add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex) = Some nextIndirection).    
                apply readPhyEntryAddIndirectionSameTable.
      rewrite Hread in Hind.
      assert(Hnext: (defaultPage =? nextIndirection) = false) by trivial.
      rewrite Hnext in Hind.
      assert(Hwell':  isWellFormedMMUTables nextIndirection s').
      apply isWellFormedMMUTablesAddIndirection with entry;trivial.
      unfold isWellFormedMMUTables in Hwell'.
     
      case_eq( StateLib.Level.pred l );intros * Hpred;rewrite Hpred in *;try now contradict Hind.
      destruct n;simpl in Hind.
      +  generalize (Hwell'  (StateLib.getIndexOfAddr vaToPrepare fstLevel) ); clear Hwell'; intros (Hi1 & Hi2).
       inversion Hind. subst p.
      rewrite Hnext.                    
     
      rewrite Hi2.
       left;trivial.
      +  
        case_eq(StateLib.Level.eqb l0 fstLevel);intros * Hl0;rewrite Hl0 in *.
        - generalize (Hwell'  (StateLib.getIndexOfAddr vaToPrepare fstLevel) ); clear Hwell'; intros (Hi1 & Hi2).
          inversion Hind;subst p.
          rewrite Hnext.
          rewrite Hi2.
           left;trivial.
        - generalize (Hwell'  (StateLib.getIndexOfAddr vaToPrepare l0) ); clear Hwell'; intros (Hi1 & Hi2).
          simpl in *.
          rewrite   Hi1 in Hind.
       assert(Hdeftrue: (defaultPage =? defaultPage)=true). symmetry. apply beq_nat_refl.
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
  assert(Hor :checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = true \/
         checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l = false).
  { destruct (checkVAddrsEqualityWOOffset nbLevel vaToPrepare vapg l);intuition. }
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
 assert(HHkey: pg<> defaultPage) .
  {
   revert Hvapg Hlookup Hprecons.
    assert(Hnotdef: (defaultPage =? nextIndirection) = false) by trivial.
    revert Hnotdef.
    clear .
    unfold getAccessibleMappedPage.
    intros.
    destruct (StateLib.getNbLevel);try now contradict Hvapg.
    destruct ( getIndirection indirection vapg l0 (nbLevel - 1) s');try now contradict Hvapg.
    destruct (defaultPage =? p);try now contradict Hvapg.
    case_eq( StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel) (memory s') );intros * Hpres;rewrite Hpres in *;try now contradict Hvapg.
    case_eq (b);intros * Hb ;rewrite Hb in *;try now contradict Hvapg.
    case_eq( StateLib.readAccessible p (StateLib.getIndexOfAddr vapg fstLevel) (memory s'));intros * Haccess;rewrite Haccess in *;try now contradict Hvapg.
    case_eq b0; intros * Hb0;rewrite Hb0 in *;try now contradict Hvapg.
    case_eq(StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg fstLevel) (memory s'));intros * Hread;
    rewrite Hread in *;try now contradict Hvapg.
   
    inversion Hvapg;subst.
    assert(Hcons':  isPresentNotDefaultIff s').
    { intros. eapply isPresentNotDefaultIffMapMMUPage with entry;trivial.
    apply beq_nat_falseNot;trivial.
   
   
    }
    unfold isPresentNotDefaultIff in Hcons'.
    generalize(Hcons' p (StateLib.getIndexOfAddr vapg fstLevel) );clear Hcons';
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
      case_eq(defaultPage =? p);intros * Hnotdefp;rewrite Hnotdefp in Hvapg;try now contradict Hnotdefp.
    case_eq(StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel) (memory s'));intros * Hpres;rewrite Hpres in *;try now contradict Hvapg.
    case_eq(b);intros * Hb;rewrite Hb in *;subst;try now contradict Hvapg.
    case_eq( StateLib.readAccessible p (StateLib.getIndexOfAddr vapg fstLevel) (memory s'));intros * Haccess;rewrite Haccess in *;try now contradict Hvapg.
    case_eq b; intros * Hb0;rewrite Hb0 in *;try now contradict Hvapg.
    case_eq(StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg fstLevel) (memory s'));intros * Hread;
    rewrite Hread in *;try now contradict Hvapg.
    inversion Hvapg;subst.
    assert(Hindeq: getIndirection indirection vapg l (nbLevel - 1) s =
    getIndirection indirection vapg l (nbLevel - 1) s').
    { apply getIndirectionAddIndirectionCheckVaddrsFalse with p pg indMMUToPrepare entry partition;trivial. }
    rewrite <- Hindeq in *.
    case_eq(getIndirection indirection vapg l (nbLevel - 1) s);intros * Hine;rewrite Hine in *; try now contradict Hvapg.
    case_eq(defaultPage =? p);intros * Hdefi;rewrite Hdefi in *; try now contradict Hvapg.
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
    omega.
    left;trivial. }
    assert(Ht2: ~In p (getIndirectionsAux indirection s (nbLevel-1))).
    { apply getIndirectionInGetIndirections2' with vapg l;trivial.
    omega.
    unfold noDupConfigPagesList in *.
    unfold getIndirections in *.
    replace (nbLevel -1 + 1) with nbLevel by omega.
    trivial.
    apply beq_nat_false in Hdefi.
    destruct defaultPage;simpl in *;destruct p;simpl in *.
    unfold not;intros xxx;simpl in *.
    inversion xxx.
    subst.
    now contradict Hdefi.
   
omega. }

unfold not;intros;subst;now contradict Ht2. }

assert(Hpreseq: StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel) (memory s')=
StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel) (memory s)).
symmetry.
apply readPresentMapMMUPage with entry;trivial.
left;trivial.
assert(Haccessx: StateLib.readAccessible p (StateLib.getIndexOfAddr vapg fstLevel) (memory s')=
StateLib.readAccessible p (StateLib.getIndexOfAddr vapg fstLevel) (memory s)).
apply readAccessibleMapMMUPage;trivial.
left;trivial.  
assert(Hreadeq: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg fstLevel) (memory s')=
StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg fstLevel) (memory s)).
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
omega.

omega. }

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
      omega.
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
    unfold getAccessibleMappedPage.
    (* rewrite HindeqStop in Hinstop1. *)
    case_eq(getIndirection pd vapg nbL (nbLevel - 1) s' );intros * Hinds'; rewrite Hinds' in *;
    try now contradict Hvapg.
    case_eq(defaultPage =? p);intros * Hdefs';rewrite Hdefs' in *;try now contradict Hvapg.
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
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
subst;trivial.
+ simpl. subst.
  rewrite <- Hlevel.
  rewrite readPhyEntryAddIndirectionSameTable.
  assert(Hnext: (defaultPage =? nextIndirection) = false) by trivial.
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
    assert(Hor: stop + 1+1 <= nbLevel-1 \/ stop + 1+1 > nbLevel-1 ) by omega.
    destruct Hor as [Hor | Hor].
    * rewrite HindeqStop in Hi.
     
    assert(Hii:  getIndirection pd vapg nbL (stop + 1 +1 ) s' = Some defaultPage).
    {  apply getIndirectionStopS1 with nextIndirection;trivial. omega.
        apply beq_nat_falseNot;trivial.
        simpl.
      case_eq(StateLib.Level.eqb (CLevel (nbL - (stop + 1))) fstLevel);intros * Hfst.
      apply levelEqBEqNatTrue0 in Hfst.
      rewrite <- Hnbleq in Hfst.
      unfold CLevel in Hfst.
      case_eq(lt_dec (nbLevel - 1 - (stop + 1)) nbLevel) ; intros * Hls;rewrite Hls in *;simpl in *.
      rewrite <- Hnbleq in Hstp.
      omega.
      omega.
      rewrite Hv.
      assert(Hread:  StateLib.readPhyEntry nextIndirection (StateLib.getIndexOfAddr vapg (CLevel (nbL - (stop + 1))))
      (memory s') = Some defaultPage).
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
    assert(Hdefx: getIndirection pd vapg nbL (nbLevel - 1) s' = Some defaultPage).
    { apply getIndirectionNbLevelEq with (stop+1 +1);trivial.
      omega.
      rewrite <- Hnbleq.
      trivial. }
      rewrite Hinds' in Hdefx.
      inversion Hdefx.
      subst.
      rewrite <- beq_nat_refl in Hdefs'.
      now contradict Hdefx.
    *  assert(Htrueeq: stop+1 = nbL) by omega.
      rewrite Htrueeq in *.
      rewrite Hnbleq in *.
      rewrite HindeqStop in Hi.
      rewrite Hinds' in Hi.
      inversion Hi;subst.
      assert(Hconspres: StateLib.readPresent nextIndirection (StateLib.getIndexOfAddr vapg fstLevel)
       (memory s') = Some false).
             assert(Hwell':  isWellFormedMMUTables nextIndirection s').
          apply isWellFormedMMUTablesAddIndirection with entry;trivial.
          unfold isWellFormedMMUTables in Hwell'.
          generalize (Hwell' (StateLib.getIndexOfAddr vapg fstLevel) ) ; clear Hwell'; intros .
          intuition.
          rewrite Hconspres in *.
          now contradict Hvapg.
+ case_eq ( getIndirection pd vapg nbL (nbLevel - 1) s');intros * Hinds';rewrite Hinds' in *;try now contradict Hvapg.
  case_eq(defaultPage =? p) ; intros * Hps';rewrite Hps' in *;try now contradict Hvapg.
  assert(Heqs':  getIndirection pd vapg nbL (nbLevel - 1) s =
   getIndirection pd vapg nbL (nbLevel - 1) s').
  {  assert(Horlst: (StateLib.getIndexOfAddr vaToPrepare l) = (StateLib.getIndexOfAddr vapg l) \/  
(StateLib.getIndexOfAddr vaToPrepare l) <> (StateLib.getIndexOfAddr vapg l) ) by apply indexDecOrNot.
destruct Horlst as [Horlst| Horlst].
+


 assert( Hnewvaddr: checkVAddrsEqualityWOOffset (stop ) vaToPrepare vapg nbL = false ).
{ apply checkVAddrsEqualityWOOffsetFalseS;trivial.

 subst;trivial. }
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by omega.
destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vapg nbL;trivial.
destruct nbL;simpl in *.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
subst;trivial.
- subst.
assert(Hor: stop=0 \/ stop > 0) by omega.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
case_eq( StateLib.Level.eqb nbL fstLevel);intros * Hlvl;rewrite Hlvl in *.
rewrite CLevelIdentity' in Hlevel.
rewrite <- Hlevel in Hlvl.
now contradict Hlvl.
 now contradict Hvaddr.
* assert(Hrn: S (stop-1) = stop) by omega.
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

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by omega.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vapg nbL;trivial;try omega.
apply getIndirectionStopLevelGe with stop0;trivial.
omega.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vapg nbL;trivial;try omega.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
+ assert(Horstop: checkVAddrsEqualityWOOffset stop vaToPrepare vapg nbL = true \/
checkVAddrsEqualityWOOffset stop vaToPrepare vapg nbL = false) .
{ destruct (checkVAddrsEqualityWOOffset stop vaToPrepare vapg nbL).
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
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by omega.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vapg nbL;trivial.
destruct nbL;simpl in *.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
{ assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
 }

pose proof inclGetIndirectionsAuxLe as Hproof.
left.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
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

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by omega.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{
 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vapg nbL;trivial;try omega.
apply getIndirectionStopLevelGe with stop0;trivial.
omega.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }left.

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vapg nbL;trivial;try omega.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }
left.

unfold not;intros;subst;now contradict Hnotinind.
 }
**
apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
assert(Hor : stop0 < stop \/ stop0=stop \/ stop0 > stop) by omega.
{ destruct Hor as [Hor | [Hor | Hor]].
- assert(Hinind: In tbl (getIndirectionsAux pd  s (stop0+1))).
{ apply getIndirectionInGetIndirections1 with vapg nbL;trivial.
destruct nbL;simpl in *.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2.
 }
assert(Hnotinind: ~ In indirection (getIndirectionsAux pd s (stop))).
assert(Hex: stop + 1 <= nbLevel).
destruct nbL;simpl in *.
omega.
   

apply getIndirectionInGetIndirections2' with vaToPrepare nbL;trivial.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
pose proof inclGetIndirectionsAuxLe as Hproof.
contradict Hnotinind.
unfold incl in Hproof.
apply Hproof with (stop0+1).
omega.
subst;trivial.
-

subst.
assert(Hor: stop=0 \/ stop > 0) by omega.
destruct Hor as [Hor | Hor].
* subst. simpl in *.
inversion Hi1;subst.

inversion Hind;subst.
now contradict H.
* assert(Hrn: S (stop-1) = stop) by omega.
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

assert(Hornbl: stop0>= nbLevel-1 \/ stop0 < nbLevel -1) by omega.
destruct Hornbl as [Hornbl | Hornbl].

*

  assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
 
apply getIndirectionInGetIndirections2n with (nbLevel -1) vapg nbL;trivial;try omega.
apply getIndirectionStopLevelGe with stop0;trivial.
omega.

unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
*   assert(Hinind: In indirection (getIndirectionsAux pd  s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
assert(Hex: stop + 1 <= nbLevel) by omega.

assert(Hnotinind: ~ In tbl (getIndirectionsAux pd s (stop+1))).
{

 
apply getIndirectionInGetIndirections2n with stop0 vapg nbL;trivial;try omega.
unfold getIndirections in *.
apply noDupPreviousMMULevels with nbLevel ;trivial.
omega.
apply beq_nat_false in Hi2.
unfold not;intros;subst;now contradict Hi2. }

unfold not;intros;subst;now contradict Hnotinind.
 } }
rewrite  Heqs'.
 rewrite Hinds'.
 rewrite Hps'.
 assert(Hkey: p <> indirection \/ StateLib.getIndexOfAddr vapg fstLevel <> StateLib.getIndexOfAddr vaToPrepare l).
{    subst.
    assert(Horx: stop = nbL \/ stop <> nbL) by omega.
    destruct Horx as [Horx | Horx].
    subst.
    replace (nbL - nbL) with 0 in Hlevel.
    unfold fstLevel in Hlevel.
    unfold StateLib.Level.eqb in Hlevel.
    rewrite <- beq_nat_refl in Hlevel.
    now contradict Hlevel.
    omega.
    assert(Hx: nbLevel - 1 = nbL).
{
apply getNbLevelEq in HnbL.
subst.
rewrite <- nbLevelEq;trivial. }
 assert(~In p (getIndirectionsAux pd s (stop+1))).
{
pose proof nbLevelNotZero as HnbL0.
 
apply getIndirectionInGetIndirections2n with (nbLevel - 1) vapg nbL;trivial;try omega.
rewrite Heqs';trivial.
replace (nbLevel - 1 + 1) with nbLevel by omega.
unfold getIndirections in *.
trivial.
apply beq_nat_false in Hps'.
unfold not;intros;subst;now contradict Hps'. }
assert(In indirection (getIndirectionsAux pd s (stop+1))).
{ apply getIndirectionInGetIndirections1 with vaToPrepare nbL;trivial.
omega.
 }
 left.
 unfold not;intros;subst;now contradict H0.
 }
 
 assert(Hpres: StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel) (memory s)=
 StateLib.readPresent p (StateLib.getIndexOfAddr vapg fstLevel) (memory s')).
 {  apply readPresentMapMMUPage with entry;trivial. }
  assert(Haccess: StateLib.readAccessible p (StateLib.getIndexOfAddr vapg fstLevel) (memory s)=
 StateLib.readAccessible p (StateLib.getIndexOfAddr vapg fstLevel) (memory s')).
 { symmetry.  apply readAccessibleMapMMUPage;trivial. }
 assert(Hread: StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg fstLevel) (memory s)=
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr vapg fstLevel) (memory s')).
 {  apply readPhyEntryMapMMUPage with entry;trivial. }
 

 rewrite  Hread.
 rewrite  Haccess.
 rewrite  Hpres.
 trivial.

Qed.

Lemma getMappedPagesAuxAddIndirectionSSI2 s indirection nextIndirection  entry nbLgen valist pd pg indMMUToPrepare vaToPrepare partition l:
isPresentNotDefaultIff s ->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
noDupConfigPagesList s ->
 In pg  (getMappedPagesAux pd valist {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}) ->

partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP partition PDidx pd s ->
nextIndirection <> indirection ->
                 
In pg (getMappedPagesAux pd valist s).
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hprecons Hlookup Hl Hroot Hdef Hdef' Hinit Hlevel Hnodupcons.
unfold getMappedPagesAux.
intros Hgoal.
intros.
rewrite filterOptionInIff in *.
unfold getMappedPagesOption in *.
rewrite in_map_iff in *.
destruct Hgoal as (vapg & Hvapg & Hinvalist).
exists vapg;split;trivial.
apply getMappedPageSomeAddIndirectionSSI2 with indirection nextIndirection entry
nbLgen indMMUToPrepare vaToPrepare partition l;trivial.
Qed.
     

Lemma getMappedPagesAuxAddIndirectionSamePart s indirection nextIndirection  entry nbLgen valist pd pg indMMUToPrepare vaToPrepare partition l:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
noDupConfigPagesList s ->


partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP partition PDidx pd s ->
nextIndirection <> indirection ->
In pg (getMappedPagesAux pd valist s) <->
 In pg  (getMappedPagesAux pd valist {|
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
intros Hlookup Hl Hroot Hdef Hdef' Hinit Hlevel Hnodupcons.
unfold getMappedPagesAux.
intros.
assert(Hnodup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition PDidx ;trivial.
unfold noDupConfigPagesList in *.
apply Hnodupcons;trivial.
left;trivial. }
split;intros Hgoal.
eapply getMappedPagesAuxAddIndirectionSSI1;try eassumption;trivial.
eapply getMappedPagesAuxAddIndirectionSSI2;try eassumption;trivial.
Qed.
Lemma getMappedPageEqAddIndirectionNotSamePart s  indirection nextIndirection  entry nbLgen a pd  indMMUToPrepare vaToPrepare partition l:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
noDupConfigPagesList s ->


partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP partition PDidx pd s ->
nextIndirection <> indirection ->

forall part pdpart,
part <> partition ->
In part (getPartitions multiplexer s) ->
nextEntryIsPP part PDidx pdpart s ->
getMappedPage pdpart s a = getMappedPage pdpart {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |} a.
Proof.
set(s':= {|
  currentPartition := _ |}).
intros.
unfold getMappedPage.
case_eq(StateLib.getNbLevel);intros;trivial.
assert(Hin2: In indirection (getConfigPages partition s)).
{ right.
apply inGetIndirectionsAuxInConfigPagesPD with pd;trivial.
apply indirectionDescriptionInGetIndirections with partition vaToPrepare l PDidx;trivial.
left;trivial.
apply nextEntryIsPPgetPd;trivial. }
assert(Hdisjoint: configTablesAreDifferent s) by trivial.
unfold configTablesAreDifferent in *.
assert(Hpartx : In part (getPartitions multiplexer s)) by trivial.
assert(Hpart:In partition (getPartitions multiplexer s)) by trivial.
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
case_eq(defaultPage =? p);intros * Hp;trivial.
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

 
assert(Hpres:  StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 apply readPresentMapMMUPage with entry;trivial. left. trivial.
 rewrite Hpres.
assert(Hread:  StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 apply readPhyEntryMapMMUPage with entry;trivial. left. trivial.
 rewrite Hread.
 trivial.
Qed.

Lemma getAccessibleMappedPageEqAddIndirectionNotSamePart s  indirection nextIndirection  entry nbLgen a pd  indMMUToPrepare vaToPrepare partition l:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
noDupConfigPagesList s ->


partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP partition PDidx pd s ->
nextIndirection <> indirection ->

forall part pdpart,
part <> partition ->
In part (getPartitions multiplexer s) ->
nextEntryIsPP part PDidx pdpart s ->
getAccessibleMappedPage pdpart s a = getAccessibleMappedPage pdpart {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |} a.
Proof.
set(s':= {|
  currentPartition := _ |}).
intros.
unfold getAccessibleMappedPage.
case_eq(StateLib.getNbLevel);intros;trivial.
assert(Hin2: In indirection (getConfigPages partition s)).
{ right.
apply inGetIndirectionsAuxInConfigPagesPD with pd;trivial.
apply indirectionDescriptionInGetIndirections with partition vaToPrepare l PDidx;trivial.
left;trivial.
apply nextEntryIsPPgetPd;trivial. }
assert(Hdisjoint: configTablesAreDifferent s) by trivial.
unfold configTablesAreDifferent in *.
assert(Hpartx : In part (getPartitions multiplexer s)) by trivial.
assert(Hpart:In partition (getPartitions multiplexer s)) by trivial.
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
case_eq(defaultPage =? p);intros * Hp;trivial.
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

 
assert(Hpres:  StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPresent p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 apply readPresentMapMMUPage with entry;trivial. left. trivial.
 rewrite Hpres.
assert(Haccess:  StateLib.readAccessible p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readAccessible p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 symmetry.
 apply readAccessibleMapMMUPage ;trivial. left. trivial.
 rewrite Haccess.
assert(Hread:  StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s) =
 StateLib.readPhyEntry p (StateLib.getIndexOfAddr a fstLevel) (memory s')).
 apply readPhyEntryMapMMUPage with entry;trivial. left. trivial.
 rewrite Hread.
 trivial.
Qed.
Lemma getMappedPagesAuxAddIndirectionNotSamePart s  indirection nextIndirection  entry nbLgen valist pd  indMMUToPrepare vaToPrepare partition l:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
noDupConfigPagesList s ->


partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP partition PDidx pd s ->
nextIndirection <> indirection ->

forall part pdpart,
part <> partition ->
In part (getPartitions multiplexer s) ->
nextEntryIsPP part PDidx pdpart s ->
getMappedPagesAux pdpart valist s = getMappedPagesAux pdpart valist {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
Proof.
intros.
set(s':=  {|
  currentPartition := _ |}).
unfold getMappedPagesAux.
f_equal.
unfold getMappedPagesOption.
induction valist;simpl;trivial.
f_equal;trivial.
apply getMappedPageEqAddIndirectionNotSamePart with entry nbLgen pd indMMUToPrepare partition part;trivial.
Qed.



Lemma getMappedPagesAuxAddIndirection s indirection nextIndirection  entry nbLgen valist pd pg indMMUToPrepare vaToPrepare partition l:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
noDupConfigPagesList s ->


partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP partition PDidx pd s ->
nextIndirection <> indirection ->

forall part pdpart,
In part (getPartitions multiplexer s) ->
nextEntryIsPP part PDidx pdpart s ->
In pg (getMappedPagesAux pdpart valist s) <->
 In pg  (getMappedPagesAux pdpart valist {|
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
intros Hlookup Hl Hroot Hdef Hdef' Hinit Hlevel Hnodupcons.

intros.
assert(Hnodup : NoDup (getIndirections pd s)).
{ apply noDupConfigPagesListNoDupGetIndirections with partition PDidx ;trivial.
unfold noDupConfigPagesList in *.
apply Hnodupcons;trivial.
left;trivial. }
assert(Hor: part = partition \/ part <> partition) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
+ subst.
unfold getMappedPagesAux.
split;intros Hgoal.
eapply getMappedPagesAuxAddIndirectionSSI1;try eassumption;trivial.
eapply getMappedPagesAuxAddIndirectionSSI2;try eassumption;trivial.
+ assert(Heq: getMappedPagesAux pdpart valist s = getMappedPagesAux pdpart valist s').
  apply  getMappedPagesAuxAddIndirectionNotSamePart with entry nbLgen pd
indMMUToPrepare partition part;trivial.
rewrite Heq.  split;intros Hgoal;trivial.
Qed.



Lemma checkChildAddIndirectionSamePart indirection idx  vavalue nextIndirection nbLgen part  e w r entry pd s:
lookup indirection idx (memory s) beqPage beqIndex = Some (PE entry) ->
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
nextEntryIsPP part PDidx pd s ->
In indirection (getIndirections pd s) ->
In part (getPartitions multiplexer s)  ->
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
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |} vavalue .
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hlookup Hpde Hconfdiff Hpd Hkey Hpart Hnbl.
unfold checkChild.
simpl.
assert(Hgetsh1 : forall part, getFstShadow part (memory s) =
 getFstShadow part
    (add indirection  idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex )).
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
assert(pd = pd1).
apply getPdNextEntryIsPPEq with part s;trivial.
subst pd1.
rewrite Hsh1.
assert(Hind : getIndirection sh1 vavalue nbLgen (nbLevel - 1) s  =
getIndirection sh1 vavalue nbLgen (nbLevel - 1) s' ).
{ apply getIndirectionMapMMUPage11 with entry
;trivial.
intros * Hi1 Hi2.
apply NoDupSplitInclIff in Hconfdiff.
destruct Hconfdiff as (_ & Hconfdiff).
unfold disjoint in *.
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
  }
  rewrite <- Hind.  
case_eq(getIndirection sh1 vavalue nbLgen (nbLevel - 1) s);intros * Hp;rewrite Hp in *.
 case_eq( p =? defaultPage);intros * Hdef;trivial.
assert(Hpdflag: StateLib.readPDflag p (StateLib.getIndexOfAddr vavalue fstLevel) (memory s) =
 StateLib.readPDflag p (StateLib.getIndexOfAddr vavalue fstLevel)
    (add indirection idx
       (PE
          {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
       (memory s) beqPage beqIndex)).
       symmetry.
       apply readPDflagMapMMUPage with entry;trivial.
     rewrite Hpdflag;trivial.
     trivial.
     trivial.
Qed.

Lemma checkChildAddIndirection indirection idx  vavalue nextIndirection nbLgen part  e w r entry pd s:
lookup indirection idx (memory s) beqPage beqIndex = Some (PE entry) ->
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
nextEntryIsPP part PDidx pd s ->
In indirection (getIndirections pd s) ->
In part (getPartitions multiplexer s)  ->
Some nbLgen = StateLib.getNbLevel ->
forall partx,
In partx (getPartitions multiplexer s) ->
 checkChild partx nbLgen s vavalue  =
checkChild partx nbLgen  {|
  currentPartition := currentPartition s;
  memory := add indirection  idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present :=true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |} vavalue .
Proof.
set(s':={|currentPartition:= _ |}) in *.
intros Hlookup Hpde Hconfdiff Hdisjoint Hpd Hkey Hpart Hnbl partx Hpartx.

assert(Hor: partx = part \/ partx <> part) by apply pageDecOrNot.
destruct Hor as [Hor|Hor];subst.
+ apply checkChildAddIndirectionSamePart with entry pd;trivial.
+ unfold checkChild.
  assert(Hgetsh1 : forall part, getFstShadow part (memory s) =
    getFstShadow part
    (add indirection  idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex )).
{ intros. symmetry.
  apply getFstShadowMapMMUPage with entry;trivial. }
rewrite <- Hgetsh1. clear Hgetsh1.
case_eq(getFstShadow partx (memory s));intros * Hsh1;
trivial.
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
unfold getConfigPages;simpl.
right.
apply inGetIndirectionsAuxInConfigPagesPD with pd;trivial.
apply nextEntryIsPPgetPd;trivial.
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



case_eq(getIndirection p vavalue nbLgen (nbLevel - 1) s);intros * Hp;rewrite Hp in *.
 case_eq( p0 =? defaultPage);intros * Hdef;trivial.
assert(Hpdflag: StateLib.readPDflag p0 (StateLib.getIndexOfAddr vavalue fstLevel) (memory s) =
 StateLib.readPDflag p0 (StateLib.getIndexOfAddr vavalue fstLevel)
    (add indirection idx
       (PE
          {| read := r; write := w; exec := e; present := true; user := true; pa := nextIndirection |})
       (memory s) beqPage beqIndex)).
       symmetry.
       apply readPDflagMapMMUPage with entry;trivial.
     rewrite Hpdflag;trivial.
     trivial.
Qed.


Lemma getPdsVAddrAddIndirection indirection idx   nextIndirection nbLgen partition part pd entry e w r s:
lookup indirection idx (memory s) beqPage beqIndex = Some (PE entry) ->
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
configTablesAreDifferent s ->
nextEntryIsPP part PDidx pd s ->
In indirection (getIndirections pd s) ->
In part (getPartitions multiplexer s)  ->
In partition (getPartitions multiplexer s)  ->
Some nbLgen = StateLib.getNbLevel ->
 getPdsVAddr partition nbLgen getAllVAddrWithOffset0 s =
getPdsVAddr partition nbLgen getAllVAddrWithOffset0  {|
  currentPartition := currentPartition s;
  memory := add indirection  idx
              (PE
                 {|
                 read := r;
                 write := w;
                 exec := e;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
Proof.
set (s':= {|
  currentPartition := _ |}).
unfold getPdsVAddr.
induction getAllVAddrWithOffset0;simpl;trivial.
intros.
assert(Hcheck :  checkChild partition nbLgen s'  a =
                   checkChild partition nbLgen s a).
                   symmetry. unfold s'.
apply checkChildAddIndirection with part entry pd;trivial.
case_eq(checkChild partition nbLgen s a);intros * Hi1.
rewrite Hcheck.
case_eq(checkChild partition nbLgen s a);intros * Hi2.
f_equal.
apply IHl;trivial.
rewrite Hi1 in *.
now contradict Hi2.
rewrite Hcheck;trivial.
rewrite Hi1.
apply IHl;trivial.
Qed.                

Lemma getChildrenAddIndirection s indirection nextIndirection  entry nbLgen  pd  indMMUToPrepare vaToPrepare partition l child:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
nextEntryIsPP partition PDidx pd s ->

nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
forall part,
In part (getPartitions multiplexer s) ->
In child (getChildren part s) <->
In child (getChildren part {|
  currentPartition := currentPartition s;
  memory := add indirection  (StateLib.getIndexOfAddr vaToPrepare l)
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
unfold getChildren.
intros Hlookup Hl Hroot Hdef Hdef' Hinit Hlevel Hpd.
intros.
assert(Hgetpd : forall partition, StateLib.getPd partition
  (add indirection  (StateLib.getIndexOfAddr vaToPrepare l) (PE
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
rewrite <- Hl in *.
rewrite nextEntryIsPPgetPd in *.
case_eq( StateLib.getPd part (memory s));intros * Hpd0;[|split;trivial].
assert(Hpds : getPdsVAddr part nbLgen getAllVAddrWithOffset0 s =
getPdsVAddr part nbLgen getAllVAddrWithOffset0 s') .
{ apply getPdsVAddrAddIndirection with partition pd entry;trivial.
apply nextEntryIsPPgetPd;trivial.
apply indirectionDescriptionInGetIndirections with partition vaToPrepare l PDidx;trivial.
left;trivial.
apply nextEntryIsPPgetPd;trivial. }
rewrite <-Hpds.
unfold s'.
eapply getMappedPagesAuxAddIndirection;try eassumption .
apply nextEntryIsPPgetPd;trivial.
eassumption.
apply nextEntryIsPPgetPd;trivial.
Qed.

Lemma getPartitionsAddIndirection
s indirection nextIndirection  entry nbLgen  pd  indMMUToPrepare vaToPrepare partition l  :
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
nextEntryIsPP partition PDidx pd s ->

noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
forall part,
In part (getPartitions multiplexer s) <->
In part (getPartitions multiplexer {|
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
intros Hlookup Hnewcons2 Hnewcons Hnoduptree Hi1 Hi2 Hi3 Hi4 Hlevel
 Ha1 Ha2 Ha3 Ha4 Ha5 .
unfold getPartitions.
assert(Hmult: In multiplexer (getPartitions multiplexer s)).
{ unfold getPartitions.
  destruct (nbPage);simpl; left;trivial. }
revert Hmult.
generalize multiplexer at 1 3 4.
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
rewrite <- getChildrenAddIndirection with (entry:=entry)   (nbLgen:= nbLgen) (indMMUToPrepare:= indMMUToPrepare)
(pd:=pd) (partition:= partition);trivial.
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
rewrite  getChildrenAddIndirection with (entry:=entry)   (nbLgen:= nbLgen) (indMMUToPrepare:= indMMUToPrepare)
(pd:=pd) (partition:= partition) (indirection:= indirection)(vaToPrepare:=vaToPrepare)(l:=l)
(nextIndirection:=nextIndirection);trivial.
*  apply IHn;trivial.

apply childrenPartitionInPartitionList with mult;trivial.
rewrite  getChildrenAddIndirection with (entry:=entry)   (nbLgen:= nbLgen) (indMMUToPrepare:= indMMUToPrepare)
(pd:=pd) (partition:= partition) (indirection:= indirection)(vaToPrepare:=vaToPrepare)(l:=l)
(nextIndirection:=nextIndirection);trivial.
Qed.

Lemma getAccessibleMappedPagesAuxAddIndirection s indirection nextIndirection  entry nbLgen valist pd pg indMMUToPrepare vaToPrepare partition l:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
noDupConfigPagesList s ->


partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP partition PDidx pd s ->
nextIndirection <> indirection ->

forall part pdpart,
In part (getPartitions multiplexer s) ->
nextEntryIsPP part PDidx pdpart s ->
In pg (getAccessibleMappedPagesAux pdpart valist s) <->
 In pg  (getAccessibleMappedPagesAux pdpart valist {|
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
  with entry partition indMMUToPrepare;trivial.
- rewrite filterOptionInIff in *.
 unfold getAccessibleMappedPagesOption in *.
 rewrite in_map_iff in *.
 destruct Hgoal as (x & Hx1 & Hx2).
 exists x;split;trivial.
 apply getAccessibleMappedPageSomeAddIndirectionSSI2 with indirection nextIndirection entry nbLgen
indMMUToPrepare vaToPrepare partition l;trivial.
+  unfold getAccessibleMappedPagesAux in *.
split; intros Hgoal;
 rewrite filterOptionInIff in *;
 unfold getAccessibleMappedPagesOption in *;
 rewrite in_map_iff in *;
 destruct Hgoal as (x & Hx1 & Hx2);
 exists x;split;trivial;
 rewrite <- Hx1;
 [symmetry|];
 apply getAccessibleMappedPageEqAddIndirectionNotSamePart
  with entry nbLgen pd indMMUToPrepare partition part;trivial.
Qed.


Lemma getAccessibleMappedPagesAddIndirection s indirection nextIndirection  entry nbLgen pd pg indMMUToPrepare vaToPrepare partition l:
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
noDupConfigPagesList s ->


partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP partition PDidx pd s ->
nextIndirection <> indirection ->

forall part,
In part (getPartitions multiplexer s) ->
In pg (getAccessibleMappedPages part  s) <->
 In pg  (getAccessibleMappedPages part  {|
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
  with entry partition indMMUToPrepare;trivial.
  apply nextEntryIsPPgetPd;trivial.
- rewrite filterOptionInIff in *.
 unfold getAccessibleMappedPagesOption in *.
 rewrite in_map_iff in *.
 destruct Hgoal as (x & Hx1 & Hx2).
 exists x;split;trivial.
 apply getAccessibleMappedPageSomeAddIndirectionSSI2 with indirection nextIndirection entry nbLgen
indMMUToPrepare vaToPrepare partition l;trivial.
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
  with entry nbLgen pd indMMUToPrepare partition part;trivial.
 apply nextEntryIsPPgetPd;trivial.
  apply nextEntryIsPPgetPd;trivial.
Qed.


 Lemma getConfigPagesAddIndirectionNotSamePage x nextIndirection partition s pdpart vaToPrepare l indirection entry :
(forall idx : index,
StateLib.readPhyEntry nextIndirection idx (memory s) = Some defaultPage)->
   consistency s ->
      x <> nextIndirection -> 
      indirection<> nextIndirection -> 
In x (getConfigPages partition {|
      currentPartition := currentPartition s;
      memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
                  (PE
                     {|
                     read := true;
                     write := true;
                     exec := true;
                     present := true;
                     user := true;
                     pa := nextIndirection |}) (memory s) beqPage beqIndex |})->
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
In partition (getPartitions multiplexer s) ->
nextEntryIsPP partition PDidx pdpart s ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->

In x (getConfigPages partition s).
Proof.
set(s':= {|
     currentPartition := _|}).
intros Hwell Hcons Hkey1 Hnotind Hkey2 Hlookup Hpart Hpdpart.
intros.
rewrite nextEntryIsPPgetPd in *.
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
rewrite Hpdpart in *.
assert(Hinmmu: In indirection (getIndirections pdpart s)). 
{ apply indirectionDescriptionInGetIndirections with partition vaToPrepare l PDidx;trivial.
left;trivial.
apply nextEntryIsPPgetPd;trivial. }

case_eq ( getFstShadow partition (memory s)) ; [intros sh1 Hsh1|intros Hsh1];rewrite Hsh1 in *;trivial.
case_eq ( getSndShadow partition (memory s) ) ; [intros sh2 Hsh2|intros Hsh2];rewrite Hsh2 in *;trivial.
case_eq ( getConfigTablesLinkedList partition (memory s) ) ; [intros ll Hll|intros Hll];rewrite Hll in *;trivial.
rewrite in_app_iff in *
. destruct Hkey2 as [Hkey2 | Hkey2].
+ left.
  move Hkey2 at bottom.
  unfold getIndirections in *.
  clear Hpdpart Hinmmu.
  revert dependent pdpart.
  induction nbLevel;simpl in *;trivial.
  intros;simpl in *.
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
      destruct H0 as (xx & Hxx & Hxx').
      contradict Hxx.
      revert Hnotind Hwell.
      clear.
      unfold isWellFormedMMUTables in *.
      
      induction tableSize;simpl in *;try auto.
      intros.
      case_eq(beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare l) (nextIndirection, CIndex n) beqPage beqIndex);intros * Heq.
      ++ simpl in *.
         apply beqPairsTrue in Heq.
         intuition.
      ++ case_eq(  lookup nextIndirection (CIndex n) (removeDup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex) beqPage
         beqIndex);intros;trivial;try apply IHn;trivial.
         destruct v;try apply IHn;trivial.
         case_eq(pa p =? defaultPage);intros * Hi;try apply IHn;trivial.
         rewrite in_app_iff.
         apply and_not_or.
         split;try apply IHn;trivial.
         simpl.
         apply and_not_or.
         split. 
         
         subst.
         rewrite removeDupIdentity in H.
         generalize(Hwell (CIndex n) );clear Hwell; intros Hwell(*  & _ *).
         unfold StateLib.readPhyEntry  in *.
         rewrite H in Hwell.
         apply beq_nat_false in Hi.
         inversion Hwell as (Hwelli).
         contradict Hi.
         rewrite Hwelli.
         trivial.
         intuition.
         auto.
    -- revert Hx0 Hor.
    clear.
    induction tableSize;simpl in *;try auto.
      intros.
     case_eq(beqPairs (indirection, StateLib.getIndexOfAddr vaToPrepare l) (pdpart, CIndex n) beqPage beqIndex);
     intros * Heq;rewrite Heq in *.
      ++ simpl in *.
         apply  beqPairsTrue in Heq.
         intuition.
         subst.
         case_eq( nextIndirection =? defaultPage);intros * Hdef;rewrite Hdef in *.
         ** case_eq ( lookup pdpart (CIndex n) (memory s) beqPage beqIndex);intros.
         destruct v;try apply IHn;trivial.
           case_eq(pa p =? defaultPage);intros;try apply IHn;trivial.
         rewrite in_app_iff.
         left. try apply IHn;trivial.
         apply IHn;trivial.
         **  case_eq ( lookup pdpart (CIndex n) (memory s) beqPage beqIndex);intros.
         rewrite in_app_iff in Hx0.
         simpl in *.
         intuition.
          destruct v;try apply IHn;trivial.
           case_eq(pa p =? defaultPage);intros;try apply IHn;trivial.
         rewrite in_app_iff.
         left. 
         try apply IHn;trivial.
         rewrite in_app_iff in Hx0.
         simpl in *.
         intuition.
     ++ rewrite removeDupIdentity in Hx0.
          case_eq ( lookup pdpart (CIndex n) (memory s) beqPage beqIndex);intros * Hlook;rewrite Hlook in *.
         destruct v;try apply IHn;trivial.
           case_eq(pa p =? defaultPage);intros * Hdef;rewrite Hdef in *;try apply IHn;trivial.
         rewrite in_app_iff in *.
         intuition. try apply IHn;trivial.
         apply beqPairsFalse in Heq.
         intuition.
    * apply IHn;trivial.
         
+ right.

assert(Hconfigdiff: noDupConfigPagesList s) by (unfold consistency in *;intuition).
 unfold noDupConfigPagesList in *.
  generalize(Hconfigdiff partition Hpart);clear Hconfigdiff;intros Hnodup.
  unfold getConfigPages in *.
apply NoDup_cons_iff in Hnodup as (Hnotin & Hnodup).
 unfold getConfigPagesAux in Hnodup.
 rewrite Hpdpart in Hnodup.
 rewrite Hsh1 in Hnodup.
 rewrite Hsh2 in Hnodup.
 rewrite Hll in Hnodup.
 rewrite NoDupSplitInclIff in Hnodup.
 destruct Hnodup as ((Hn1 & Hn2) & Hn3).
 unfold disjoint in *.
 apply Hn3 in Hinmmu.
 rewrite in_app_iff in Hinmmu.
assert(Hnotsh1:  ~In indirection (getIndirections sh1 s)) by intuition.
assert (Hsh1ind: getIndirections sh1 s =  getIndirections sh1 s')
 by (apply getIndirectionsMapMMUPage1 with entry;trivial).
 rewrite Hsh1ind in *.
  rewrite in_app_iff in Hinmmu.
assert(Hnotsh2:  ~In indirection (getIndirections sh2 s)) by intuition.
assert (Hsh2ind: getIndirections sh2 s =  getIndirections sh2 s')
 by (apply getIndirectionsMapMMUPage1 with entry;trivial).
 rewrite Hsh2ind in *.
assert(Hnotll:  ~In indirection (getLLPages ll s (nbPage + 1))) by intuition.
assert (Hllind: getLLPages ll s (nbPage + 1) =  getLLPages ll s' (nbPage + 1))
 by (apply getLLPagesMapMMUPage with entry;trivial).
 rewrite Hllind in *.
 trivial.
Qed.     
  
  
Lemma kernelDataIsolationAddIndirection
s indirection nextIndirection  entry nbLgen  pd  indMMUToPrepare 
(vaToPrepare vaNextInd : vaddr) partition l  
(currentPart currentPD ptMMUvaNextInd ptSh1VaNextInd: page) pdpart:
(forall parts, In parts (getPartitions multiplexer s) ->
   ~ In nextIndirection (getAccessibleMappedPages parts s)) -> 
kernelDataIsolation s ->   
lookup indirection (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry) ->
verticalSharing s ->
partitionsIsolation s ->
consistency s ->
Some nbLgen = StateLib.getNbLevel ->
indirectionDescription s partition indirection PDidx vaToPrepare l ->
isEntryPage indirection (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ->
(defaultPage =? indMMUToPrepare) = true ->
(forall idx : index,
StateLib.readPhyEntry nextIndirection idx (memory s) = Some defaultPage)->
   indirection<> nextIndirection ->   
   
isWellFormedMMUTables nextIndirection s ->
false = StateLib.Level.eqb l fstLevel ->
nextEntryIsPP partition PDidx pd s ->
writeAccessibleRecPreparePostcondition currentPart nextIndirection s ->
In currentPart (getPartitions multiplexer s) ->
getTableAddrRoot ptMMUvaNextInd PDidx currentPart vaNextInd s->
isPE ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) s->
entryUserFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) false s ->
entryPresentFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) true s ->
nextEntryIsPP currentPart PDidx currentPD s ->
(defaultPage =? ptMMUvaNextInd) = false ->
isEntryPage ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) nextIndirection s ->
(* (exists va : vaddr,
  isEntryVA ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) va s /\ beqVAddr defaultVAddr va = true)-> *)
(defaultPage =? ptSh1VaNextInd) = false ->
getTableAddrRoot ptSh1VaNextInd sh1idx currentPart vaNextInd s ->
isVE ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd fstLevel) s ->

noDupPartitionTree s ->
nextIndirection <> indirection ->
partitionDescriptorEntry s ->
In partition (getPartitions multiplexer s) ->
noDupConfigPagesList s ->
isPresentNotDefaultIff s ->
configTablesAreDifferent s ->
(defaultPage =? nextIndirection) = false ->
nextEntryIsPP partition PDidx pdpart s ->
In indirection(getConfigPages partition s)->

kernelDataIsolation
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |}.
Proof.
intros * Hnotacces Hkdi.
intros.
set(s':={|currentPartition:= _ |}) in *.
unfold kernelDataIsolation in *.
simpl in *;intros partition1 partition2 Hpart1 Hpart2.
assert(Hpart : forall part, In part (getPartitions multiplexer s) <-> In part (getPartitions multiplexer s')).
intros.
unfold s'.
apply  getPartitionsAddIndirection with entry nbLgen pd indMMUToPrepare partition;trivial.
rewrite <- Hpart in Hpart1.
rewrite <- Hpart in Hpart2.
clear Hpart.
unfold disjoint in *.
intros x Hx.
(*
unfold getAccessibleMappedPages in *.
case_eq(StateLib.getPd partition1 (memory s') );intros * Hpd;rewrite Hpd in *;try now contradict Hx.
unfold s' in *.
 *)
 assert(Hgoal: In x (getAccessibleMappedPages partition1 s)).
unfold s' in *.
rewrite  getAccessibleMappedPagesAddIndirection with (vaToPrepare:= vaToPrepare)
(l:=l) (entry:=entry)
(nbLgen:=nbLgen) (partition:=partition) (nextIndirection:=nextIndirection)
(indMMUToPrepare:=indMMUToPrepare) (indirection:=indirection) (part:=partition1)(pd:=pd) ;trivial.
(*    intros.
   apply nextIndirectionNotAccessibleInAnyPartition with currentPart currentPD ptMMUvaNextInd vaNextInd ptSh1VaNextInd;trivial.
 *)   
assert(Horpage: x=nextIndirection \/ x <> nextIndirection) by apply pageDecOrNot.
destruct Horpage as [Horpage|Horpage].
- (** same page : nextIndirection *)
  subst.
  generalize (Hnotacces partition1 Hpart1);clear Hnotacces;intros Hnotacces.
  now contradict Hnotacces.
- assert(Horparts1: partition1 = partition \/ partition1 <> partition) by apply pageDecOrNot.
  destruct Horparts1 as [Horparts1|Horparts1].
  + subst.
    assert(Hin: ~ In x (getConfigPages partition2 s)).
    apply Hkdi with partition;trivial.
    contradict Hin.
    assert(Horparts2: partition2 = partition \/ partition2 <> partition) by apply pageDecOrNot.
    destruct Horparts2 as [Horparts2|Horparts2].
    * subst.
    apply getConfigPagesAddIndirectionNotSamePage with nextIndirection pdpart vaToPrepare l indirection entry;
    trivial.
    (* Ok1 : In x (getConfigPages partition s') -> In x (getConfigPages partition s)*)
    * assert(Hconfig: getConfigPages partition2 s' = getConfigPages partition2 s).
     symmetry. apply getConfigPagesMapMMUPage with partition entry;trivial. (* Ok config Eq : getConfigPagesMapMMUPage*)
     assert(Hconfdiff: configTablesAreDifferent s ) by intuition.
     unfold configTablesAreDifferent in *.
     apply Hconfdiff;trivial.
     intuition.
     intuition.
      rewrite <- Hconfig;trivial.
  + assert(Horparts2: partition2 = partition \/ partition2 <> partition) by apply pageDecOrNot.
    destruct Horparts2 as [Horparts2|Horparts2].
    * subst.
      assert(Hin: ~ In x (getConfigPages partition s)).
      apply Hkdi with partition1;trivial.
      contradict Hin.
       apply getConfigPagesAddIndirectionNotSamePage with nextIndirection pdpart vaToPrepare l indirection entry;
    trivial.  (* Ok1 *)
    * assert(Hconfig: getConfigPages partition2 s' = getConfigPages partition2 s).
     symmetry. apply getConfigPagesMapMMUPage with partition entry;trivial. (* Ok config Eq : getConfigPagesMapMMUPage*)
     assert(Hconfdiff: configTablesAreDifferent s ) by intuition.
     unfold configTablesAreDifferent in *.
     apply Hconfdiff;trivial.
     intuition.
     intuition.
      rewrite  Hconfig;trivial.
      apply Hkdi with partition1;trivial.
Qed.
Definition nextIndirectionsOR (indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr: page):=
(indirection = phyPDChild /\ nextIndirection = phyMMUaddr ) \/ 
(indirection = phySh1Child/\ nextIndirection = phySh1addr ) \/ 
(indirection = phySh2Child/\ nextIndirection = phySh2addr).
 
Lemma insertEntryIntoLLPCAddIndirection  indirection nextIndirection ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
 phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (* idxToPrepare *):
nextIndirectionsOR indirection nextIndirection phyPDChild phyMMUaddr phySh1Child phySh1addr phySh2Child phySh2addr ->  
forall s : state,
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
  lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
  ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy
  lastLLTable (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) true  ->
insertEntryIntoLLPC
  {|
  currentPartition := currentPartition s;
  memory := add indirection (StateLib.getIndexOfAddr vaToPrepare l)
              (PE
                 {|
                 read := true;
                 write := true;
                 exec := true;
                 present := true;
                 user := true;
                 pa := nextIndirection |}) (memory s) beqPage beqIndex |} ptMMUTrdVA phySh2addr
  phySh1addr phyMMUaddr ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2
  phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
  descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l
  idxFstVA idxSndVA idxTrdVA zeroI lpred fstLL LLChildphy lastLLTable
  (CIndex (CIndex (CIndex (CIndex 3 - 1) - 1) - 1)) false.
Proof.
intros Hor.
intros.
unfold insertEntryIntoLLPC in *.
unfold propagatedPropertiesPrepare in *.
assert(Hlookup: exists entry, lookup phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex = Some (PE entry)). 
{ assert(Hep: isEntryPage phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s ) by intuition.
unfold isEntryPage in Hep.
  case_eq(lookup phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) (memory s) beqPage beqIndex);intros * Hlookup;
  rewrite Hlookup in *;try now contradict Hep.
  destruct v;try now contradict Hep.
  exists p;trivial. }
destruct Hlookup as (entry & Hlookup).
assert( exists pdchild, nextEntryIsPP descChildphy PDidx pdchild s) as(pdchild & Hpdchild).
{ assert(Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
  unfold partitionDescriptorEntry in *.
  assert(Hchildpart: In descChildphy (getPartitions multiplexer s) ) by intuition.
  generalize (Hpde descChildphy Hchildpart PDidx);clear Hpde;intros Hpde.
  destruct Hpde as (_ & _ & pdchild & Hppchild & Hnptdef). left;trivial.
  exists pdchild;trivial. }
(*  assert(Hindin: In indirection (getIndirections pdchild s)).
 { unfold consistency, indirectionDescriptionAll, isWellFormedTables, writeAccessibleRecPreparePostconditionAll in *.
   assert(Hroot: indirectionDescription s descChildphy indirection PDidx vaToPrepare l).
   { intuition subst;trivial.
   apply indirectionDescriptionInGetIndirections  with descChildphy vaToPrepare l;subst;trivial.
     } } *)
 assert(Hconfig: In indirection (getConfigPages descChildphy s)). 
  { 
 unfold consistency, indirectionDescriptionAll, isWellFormedTables, writeAccessibleRecPreparePostconditionAll in *.
(*     assert(Hroot: indirectionDescription s descChildphy phyPDChild PDidx vaToPrepare l) by trivial. *)
     unfold getConfigPages. 
     simpl. right.
     unfold getConfigPagesAux.
     apply nextEntryIsPPgetPd in Hpdchild.
     rewrite Hpdchild.
     pose proof pdSh1Sh2ListExistsNotNull as Hkey.
     destruct Hkey  with s descChildphy as ( (pd & Hpd & _) & (sh1 & Hsh1 & _) & (sh2 & Hsh2 & _) & (ll & Hll & _));trivial.
     intuition.
     intuition.     
     rewrite Hsh1.
     rewrite Hsh2.
     rewrite Hll.
     destruct Hor as[Hor |[Hor | Hor]].
     + intuition;subst.
     apply in_app_iff.
     left.
     trivial.
     apply indirectionDescriptionInGetIndirections with descChildphy vaToPrepare l PDidx;subst;trivial.
     left;trivial. 
     apply nextEntryIsPPgetPd;trivial. 
    + intuition;subst.
     apply in_app_iff.
     right.
     apply in_app_iff.
     left.
     apply indirectionDescriptionInGetIndirections  with descChildphy vaToPrepare l sh1idx;subst;trivial.
     right;left;trivial. 
     apply nextEntryIsPPgetFstShadow;trivial.
     + intuition;subst.
     apply in_app_iff.
     right.
     apply in_app_iff.
     right.
     apply in_app_iff.
     left.
     apply indirectionDescriptionInGetIndirections  with descChildphy vaToPrepare l sh2idx;subst;trivial.
     right;right;trivial. 
     apply nextEntryIsPPgetSndShadow;trivial.
       }     
  assert(Haccessnotconfig: forall part, In part (getPartitions multiplexer s) ->
   ~In nextIndirection (getConfigPages part s)). 
   { destruct Hor as[(Hi1&Hi2) |[(Hi1&Hi2) | (Hi1&Hi2)]];subst;
     assert(Hcons: initPEntryTablePreconditionToPropagatePreparePropertiesAll s phyMMUaddr phySh1addr phySh2addr ) by intuition;
     unfold initPEntryTablePreconditionToPropagatePreparePropertiesAll in *;
     unfold initPEntryTablePreconditionToPropagatePrepareProperties in *; 
   intuition. }
   assert(Hchildpart:  In descChildphy (getPartitions multiplexer s)) by intuition.
  apply Haccessnotconfig in Hchildpart.
  unfold consistency, indirectionDescriptionAll, isWellFormedTables, writeAccessibleRecPreparePostconditionAll in *;intuition;subst;trivial.
+ (** kernelDataIsolation **) 

  eapply kernelDataIsolationAddIndirection with 
   (partition:= descChildphy)(pd:=pdchild)(currentPart:= currentPartition s) (ptSh1VaNextInd:= ptSh1FstVA); trivial; try eassumption.
  assert(Hnotacces: newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr) by trivial.
  unfold newIndirectionsAreNotAccessible in *.
  intros.
  apply Hnotacces;trivial.
  unfold nextIndirectionsOR in *.
  intuition.
    unfold nextIndirectionsOR in *.
  intuition.
  left;trivial.
  unfold consistency in *;intuition.
  assert(Hwell: isWellFormedMMUTables phyMMUaddr s) by trivial.
  unfold isWellFormedMMUTables in *; intros.
  generalize (Hwell idx);intuition.  
  unfold not;intros;subst;now contradict Hchildpart.
  unfold not;intros;subst;now contradict Hchildpart.
  eapply phyPageNotDefault;try eassumption.
+ (** partitionsIsolation *)
    
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

