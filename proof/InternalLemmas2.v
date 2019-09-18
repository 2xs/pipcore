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
    This file contains several internal lemmas to help prove invariants *)
Require Import Model.ADT Isolation Consistency WeakestPreconditions List 
Core.Internal  Model.MAL StateLib Model.Hardware 
 DependentTypeLemmas Model.Lib Invariants Lib PropagatedProperties InternalLemmas.
Require Import Coq.Logic.ProofIrrelevance Omega Classical_Prop.

Import List.ListNotations.
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
StateLib.checkVAddrsEqualityWOOffset stop va1 va2 nbL = true ->
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

Definition or3 idxroot:=
(idxroot=PDidx \/ idxroot=sh1idx \/ idxroot = sh2idx).

Definition or2 idxroot:=
(idxroot=PDidx \/ idxroot = sh2idx).

Lemma indirectionNotInPreviousMMULevel' s (ptVaChildpd:page) idxvaChild (* phyVaChild *)  
  pdChildphy (* currentPart *)
(* presentvaChild *) vaChild phyDescChild level (* entry *) root:
or3 root ->
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
nextEntryIsPP phyDescChild root pdChildphy s ->
pdChildphy <> defaultPage ->
getIndirection pdChildphy vaChild level (nbLevel - 1) s =
            Some ptVaChildpd ->
            nbLevel -1 > 0 ->
~ In ptVaChildpd (getIndirectionsAux pdChildphy s (nbLevel - 1)).
Proof.
intros Hor3 Hpde Hpresdef Hnodupconf Hconfigdiff (* Hparts *) (* Haccess *) (* Hlookup *) Hlevel
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
  revert Hstooo Htpp Hnotdef Hor3.
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
      generalize(IHn p l ptVaChildpd Hii H3 Hi1 Hor3 Hindchild Hdefaut
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
apply noDupConfigPagesListNoDupGetIndirections with phyDescChild root;trivial.
apply Hdup;trivial.
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
Lemma levelDecOrNot :
forall p1 p2 : level, p1 = p2 \/ p1<>p2.
Proof.
destruct p1;simpl in *;subst;destruct p2;simpl in *;subst.
assert (Heq :l=l0 \/ l<> l0) by omega.
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
StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = true ->
StateLib.checkVAddrsEqualityWOOffset stopi vaToPrepare vavalue nbL = true.
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
StateLib.checkVAddrsEqualityWOOffset (S stop0) va1 va2 level1 = false ->
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
StateLib.checkVAddrsEqualityWOOffset (S stop0) va1 va2 level1 = false ->
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

Lemma checkVAddrsEqualityWOOffsetFalseS:
forall stop vaToPrepare vavalue , forall (nbL:level),
StateLib.getIndexOfAddr vaToPrepare (CLevel (nbL - stop)) =
StateLib.getIndexOfAddr vavalue (CLevel (nbL - stop)) ->
StateLib.checkVAddrsEqualityWOOffset (stop + 1) vaToPrepare vavalue nbL = false ->
StateLib.checkVAddrsEqualityWOOffset stop vaToPrepare vavalue nbL = false.
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

Lemma levelPredMinus1Nat:
  forall l0 l' : level,
  StateLib.Level.eqb l0 fstLevel = false -> StateLib.Level.pred l0 = Some l' -> l0 - 1 = l'.
Proof.
pose proof levelPredMinus1.
intros.
assert(l' = CLevel (l0 - 1)).
apply H;trivial.
unfold CLevel in H2.
case_eq(lt_dec (l0 - 1) nbLevel);intros * Hi; rewrite Hi in *;simpl in *;
subst;
destruct l0;simpl in *;trivial.
omega.
Qed.

Lemma CLevelIdentity2  :
forall x, x  < nbLevel -> x = CLevel (x).
Proof.
intros. 
unfold CLevel.
case_eq ( lt_dec x nbLevel);intros.
simpl;trivial.
omega.
Qed.

            
Lemma getIndirectionStopSRead :
forall  stop (s : state) (nbL : level)  nextind pd va indirection, 
stop + 1 <= nbL -> indirection <> defaultPage ->
StateLib.getIndirection pd va nbL stop s = Some indirection-> 
StateLib.getIndirection pd va nbL (stop + 1) s = Some ( nextind) ->
StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va (CLevel (nbL - stop))) (memory s) = Some ( nextind).

Proof.
induction stop.
- intros. simpl.
  cbn in *.
  inversion H1.
  subst.
  rewrite NPeano.Nat.sub_0_r.
  assert(HnbL: nbL = CLevel nbL).
  unfold CLevel.
  destruct (lt_dec nbL nbLevel ).
  simpl in *.
  destruct nbL.
  simpl in *.
  assert (Hl = ADT.CLevel_obligation_1 l0 l ).
  apply proof_irrelevance.
  f_equal.
  trivial.
  destruct nbL. simpl in *.
  contradict n.
  omega.
  rewrite <- HnbL in *.
   case_eq (StateLib.Level.eqb nbL fstLevel);intros * Hfst;rewrite Hfst in *.
   * apply levelEqBEqNatTrue0 in Hfst. 
     omega. 
   * case_eq ( StateLib.readPhyEntry indirection (StateLib.getIndexOfAddr va nbL) (memory s) );intros * Hread;
   rewrite Hread in *;try now contradict H2.
   case_eq( defaultPage =? p);intros * Hdef;rewrite Hdef in *;try now contradict H2.
   inversion H2.
   rewrite H4.
   apply beq_nat_true in Hdef.
   f_equal.
   rewrite <- H4.
   destruct p;destruct defaultPage;simpl in *;subst;f_equal;apply proof_irrelevance.
   case_eq (StateLib.Level.pred nbL );intros * Heq;rewrite Heq in *;try now contradict H2;trivial.
   inversion H2;subst.
   trivial.

- intros.
  simpl .
  simpl in *.
  case_eq (StateLib.Level.eqb nbL fstLevel) ; intros * Hfst;rewrite Hfst in *.
  + apply levelEqBEqNatTrue0 in Hfst. 
     omega. 
  + case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va nbL) (memory s));intros * Hread;
  rewrite Hread in *;try now contradict H1.
  case_eq(defaultPage =? p);intros * Hp;rewrite Hp in *.
  * inversion H2.
    inversion H1.
    subst.
    now contradict H0.
   * case_eq (StateLib.Level.pred nbL );intros * Heq;rewrite Heq in *;try now contradict H2;trivial.
    assert(Hkey: (CLevel (nbL - S stop)) = (CLevel (l -  stop))).
    pose proof levelPredMinus1Nat.
    assert(nbL - 1 = l).
    apply H3;trivial.
    subst.
    rewrite <- H4.
    replace (nbL - 1 - stop) with (nbL - S stop) by omega.
    trivial.
    
    rewrite Hkey.
    apply IHstop with p;trivial.
    
    pose proof levelPredMinus1Nat.
    assert(nbL - 1 = l).
    apply H3;trivial.
    subst.
    rewrite <- H4.
    omega.
    
    
 
  

Qed. 

Set Nested Proofs Allowed.

Lemma inGetChildren child part s (level:level) (currentPD ptDescChildpd ptDescChild currentShadow:page)(descChild:vaddr):
isPE ptDescChildpd (StateLib.getIndexOfAddr descChild fstLevel) s ->
getTableAddrRoot ptDescChildpd PDidx part descChild s ->
(defaultPage =? ptDescChildpd) = false -> 
isEntryPage ptDescChildpd (StateLib.getIndexOfAddr descChild fstLevel) child s ->
entryPresentFlag ptDescChildpd (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP part PDidx currentPD s ->
nextEntryIsPP part sh1idx currentShadow s ->
(defaultPage =? ptDescChild) = false ->
 entryPDFlag ptDescChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
  Some level = StateLib.getNbLevel ->
isVE ptDescChild (StateLib.getIndexOfAddr descChild fstLevel) s ->
getTableAddrRoot ptDescChild sh1idx part descChild s ->  
In child (getChildren part s).
Proof.
intros.
  unfold getChildren.
  assert(Hlevel : Some level = StateLib.getNbLevel) by trivial.
  rewrite <- Hlevel.
  assert(Hcurpd : StateLib.getPd part (memory s) = Some currentPD).
  { apply nextEntryIsPPgetPd.
    intuition. }
  rewrite Hcurpd.
  unfold getMappedPagesAux.
  rewrite filterOptionInIff.
  unfold getMappedPagesOption.
  rewrite in_map_iff.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel descChild va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1.  split;trivial. 
assert(Hnewgoal : getMappedPage currentPD s descChild = SomePage child). 
{  apply getMappedPageGetTableRoot with ptDescChildpd part; intuition;
  subst;trivial.
 }
  rewrite <- Hnewgoal.
  symmetry.
  apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
  apply getNbLevelEqOption.
  unfold getPdsVAddr.
  apply filter_In.
  split;trivial. 
  assert(Hnewgoal : checkChild part level s descChild = true).
  { unfold checkChild. 
  assert(Hcursh1 : StateLib.getFstShadow part (memory s) = Some currentShadow).
  { apply nextEntryIsPPgetFstShadow. intuition; subst;trivial. }
  rewrite Hcursh1.
  assert(Hpt :getIndirection currentShadow descChild level (nbLevel - 1) s  = Some ptDescChild). 
  { apply getIndirectionGetTableRoot with part;intuition.
    subst;trivial. }
  rewrite Hpt.
  assert(Htrue : (ptDescChild =? defaultPage) = false ). 
  { rewrite Nat.eqb_neq in *.
   intuition. }
  rewrite Htrue.
  assert(Hpdchild :  entryPDFlag ptDescChild (StateLib.getIndexOfAddr descChild fstLevel) true s) by intuition.
  assert(Hpdtrue : StateLib.readPDflag ptDescChild
    (StateLib.getIndexOfAddr descChild fstLevel) (memory s) = Some true).
  { unfold StateLib.readPDflag, entryPDFlag in *.
    intuition. subst.
    destruct (lookup ptDescChild (StateLib.getIndexOfAddr descChild fstLevel) (memory s) beqPage beqIndex );
    try now contradict Hpdchild.
    destruct v;try now contradict Hpdchild.
    f_equal. subst. intuition. }
    rewrite Hpdtrue;trivial. }
  rewrite <- Hnewgoal.
  apply checkChildEq.
  intuition.
  rewrite checkVAddrsEqualityWOOffsetPermut.
  rewrite <- Hva11.
  f_equal.
  assert(Hlvl : StateLib.getNbLevel = Some (CLevel (nbLevel - 1))) by apply getNbLevelEqOption. 
  rewrite  Hlvl in *.
  inversion Hlevel;trivial.
  Qed.
Set Nested Proofs Allowed.
    Lemma childIsNotParent (parent phyDescChild:page) s:
    isParent s ->
    noCycleInPartitionTree s ->
    noDupPartitionTree s ->
    In parent (getPartitions multiplexer s) ->
    In phyDescChild (getChildren parent s) ->
    parent <> phyDescChild.
    Proof.
    intros Hisparent Hnocycle.
    intros. 
    assert(Hparent : StateLib.getParent phyDescChild (memory s) = Some parent)by
      (apply Hisparent;trivial).
      assert (Hisances : In parent (getAncestors phyDescChild s)) by(
      unfold getAncestors;destruct nbPage;simpl;rewrite Hparent;simpl
      ;left;trivial).
      apply Hnocycle;trivial.
    apply childrenPartitionInPartitionList with parent;trivial.
   Qed.
