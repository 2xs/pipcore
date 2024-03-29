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
    This file contains several internal lemmas to help prove invariants *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.MAL Pip.Model.Lib Pip.Core.Internal.

Require Import Pip.Proof.Isolation Pip.Proof.Consistency Pip.Proof.WeakestPreconditions Pip.Proof.StateLib.
Require Import Pip.Proof.DependentTypeLemmas Pip.Proof.Lib.
Require Import PropagatedProperties Invariants.

Require Import List Coq.Logic.ProofIrrelevance Lia Classical_Prop Compare_dec EqNat Lt Minus.

Import List.ListNotations.
(* Require Import Model.ADT Model.Hardware Core.Services Isolation
Consistency Invariants WeakestPreconditions Model.Lib StateLib
Model.MAL UpdateShadow1Structure InternalLemmas DependentTypeLemmas Lib
WriteAccessible *)
Lemma inclGetIndirectionsAuxLe root s n m : 
n <= m ->     
incl (getIndirectionsAux root s n) (getIndirectionsAux root s m).
Proof.
revert  m n root.
unfold incl.
induction m;simpl;
intros.
destruct n.
simpl in *.
trivial.
lia.
assert(Hor : root = a \/ root <> a) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
left;trivial.
right.
rewrite in_flat_map.
destruct n. 
simpl in *.
intuition.
simpl in *. 
intuition.
rewrite in_flat_map in H1.
destruct H1 as (x & Hx1 & Hx2). 
exists x.
split;trivial.
apply IHm with (n);trivial.
lia.
Qed.

Lemma getIndirectionStop1 s indirection x idxind va l: 
levelEq l levelMin = false ->  indirection <> pageDefault ->
lookup indirection idxind (memory s) pageEq idxEq = Some (PE x) -> 
StateLib.getIndexOfAddr va l  =  idxind -> 
StateLib.getIndirection indirection va l 1 s = Some (pa x).
Proof.
intros Hlnotzero Hindnotnull Hlookup Hidx . 
unfold StateLib.getIndirection.
  case_eq (levelEq l levelMin).
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
      lia.
   * unfold runvalue in Hidx.
     intros.
     unfold StateLib.readPhyEntry.
     inversion Hidx.
     rewrite H0.
     rewrite Hlookup.
     case_eq(Nat.eqb pageDefault (pa x)).
     intros.
     apply beq_nat_true in H1.
     f_equal.
     unfold pageDefault in *.
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

Lemma inNotInList  :
forall (l : list page) (a : page), In a l \/ ~ In a l.
Proof.
intros.
induction l;simpl.
right;auto.
destruct IHl.
left. 
right.
trivial.
assert(a0= a \/ a0 <> a) by apply pageDecOrNot.
destruct H0.
left;left;trivial.
right.
intuition.
Qed. 

Lemma getIndirectionStopS :
forall  stop (s : state) (nbL : level)  nextind pd va indirection, 
stop + 1 <= nbL -> indirection <> pageDefault ->
StateLib.getIndirection pd va nbL stop s = Some indirection-> 
StateLib.getIndirection indirection va (CLevel (nbL - stop)) 1 s = Some (pa nextind) ->  
StateLib.getIndirection pd va nbL (stop + 1) s = Some (pa nextind).
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
  lia.
- intros.
  simpl .
  simpl in H1.
  case_eq (levelEq nbL levelMin).
  + intros. rewrite <- H2.
    inversion H1.
    subst. 
    symmetry.
    rewrite H3 in H5. inversion H5. subst.
    simpl. clear H1.
    apply levelEqBEqNatTrue in H3.
    case_eq (levelEq (CLevel (nbL - S stop)) levelMin).
    intros.
    reflexivity.
    intros.
    apply levelEqBEqNatFalse0 in H1.
    
    contradict H1.
    unfold CLevel.
    case_eq ( lt_dec (nbL - S stop) nbLevel ).
    intros. simpl . rewrite H3.
    unfold levelMin.
    unfold CLevel.
    case_eq(lt_dec 0 nbLevel ).
    intros.
    simpl. lia.
    intros.
    assert(0 < nbLevel).
    apply nbLevelNotZero.
    contradict H6. lia.
    intros.  
    Opaque StateLib.getIndirection.
    simpl in *.
    unfold levelMin in H3.
    unfold CLevel in H3.
    case_eq (lt_dec 0 nbLevel).
    intros.
    rewrite H4 in H3.
    simpl in *.
    destruct nbL.
    simpl in *.
    subst.
    inversion H3.
    subst. lia.
    intros.
    assert (0 < nbLevel).
    apply nbLevelNotZero.
    lia.
  + intros Hftlevel.  
    rewrite Hftlevel in H1.
    case_eq (StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va nbL) (memory s)).
    { intros. rewrite H3 in H1. 
      case_eq (Nat.eqb pageDefault p).
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
          lia. 
          assumption.
          assumption.
          clear IHstop.
          inversion H5.
          Opaque StateLib.getIndirection.
          simpl in *.
          subst. 
          replace (nbL - 1 - stop) with (nbL - S stop).
          assumption.
          lia.
          intros.
          apply levelEqBEqNatFalse0 in Hftlevel.
          contradict Hftlevel.
          lia.
          Transparent StateLib.getIndirection.
        + intros.  rewrite H5 in H1. inversion H1.  
    
     }
     { intros. rewrite H3 in H1.    inversion H1. }
Qed. 

Lemma getIndirectionProp :
forall stop s nextind idxind indirection pd va (nbL : level),
stop +1 <= nbL -> indirection <> pageDefault ->
levelEq (CLevel (nbL - stop)) levelMin = false -> 
StateLib.getIndexOfAddr va (CLevel (nbL - stop)) = idxind ->
lookup indirection idxind (memory s) pageEq idxEq = Some (PE nextind)-> 
StateLib.getIndirection pd va nbL stop s = Some indirection ->
StateLib.getIndirection pd va nbL (stop + 1) s = Some (pa nextind). 
Proof.
intros.
apply getIndirectionStopS with indirection;trivial.
apply getIndirectionStop1  with idxind;trivial.
Qed.

Lemma getIndirectionStopS1 :
forall  stop (s : state) (nbL : level)  nextind pd va indirection, 
stop + 1 <= nbL -> indirection <> pageDefault ->
StateLib.getIndirection pd va nbL stop s = Some indirection-> 
StateLib.getIndirection indirection va (CLevel (nbL - stop)) 1 s = Some (nextind) ->  
StateLib.getIndirection pd va nbL (stop + 1) s = Some (nextind).
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
  lia.
- intros.
  simpl .
  simpl in H1.
  case_eq (levelEq nbL levelMin).
  + intros. rewrite <- H2.
    inversion H1.
    subst. 
    symmetry.
    rewrite H3 in H5. inversion H5. subst.
    simpl. clear H1.
    apply levelEqBEqNatTrue in H3.
    case_eq (levelEq (CLevel (nbL - S stop)) levelMin).
    intros.
    reflexivity.
    intros.
    apply levelEqBEqNatFalse0 in H1.
    
    contradict H1.
    unfold CLevel.
    case_eq ( lt_dec (nbL - S stop) nbLevel ).
    intros. simpl . rewrite H3.
    unfold levelMin.
    unfold CLevel.
    case_eq(lt_dec 0 nbLevel ).
    intros.
    simpl. lia.
    intros.
    assert(0 < nbLevel).
    apply nbLevelNotZero.
    contradict H6. lia.
    intros.  
    Opaque StateLib.getIndirection.
    simpl in *.
    unfold levelMin in H3.
    unfold CLevel in H3.
    case_eq (lt_dec 0 nbLevel).
    intros.
    rewrite H4 in H3.
    simpl in *.
    destruct nbL.
    simpl in *.
    subst.
    inversion H3.
    subst. lia.
    intros.
    assert (0 < nbLevel).
    apply nbLevelNotZero.
    lia.
  + intros Hftlevel.  
    rewrite Hftlevel in H1.
    case_eq (StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va nbL) (memory s)).
    { intros. rewrite H3 in H1. 
      case_eq (Nat.eqb pageDefault p).
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
          lia. 
          assumption.
          assumption.
          clear IHstop.
          inversion H5.
          Opaque StateLib.getIndirection.
          simpl in *.
          subst. 
          replace (nbL - 1 - stop) with (nbL - S stop).
          assumption.
          lia.
          intros.
          apply levelEqBEqNatFalse0 in Hftlevel.
          contradict Hftlevel.
          lia.
          Transparent StateLib.getIndirection.
        + intros.  rewrite H5 in H1. inversion H1.  
    
     }
     { intros. rewrite H3 in H1.    inversion H1. }
Qed. 
 Lemma getIndirectionRetNotDefaultLtNbLevel:
 forall (stop2 stop1  : nat) (nbL : level)  (pd table1 table2 : page) (va : vaddr) (s : state),
 (Nat.eqb pageDefault pd) = false -> 
 stop1 <= stop2 -> 
 getIndirection pd va nbL stop1 s = Some table1 -> 
 getIndirection pd va nbL stop2 s = Some table2 ->
 (Nat.eqb pageDefault table2) = false  -> 
 (Nat.eqb pageDefault table1) = false.
 Proof.
 induction stop2;simpl; intros.
 assert(stop1 = 0) by lia.
 subst.
 simpl in *.
 inversion H1;inversion H2.
 subst.
 assumption.
 (* destruct table2; destruct table1; simpl in *.
 inversion H6.
 subst.
 assumption. *)
 case_eq(levelEq nbL levelMin);intros;
 rewrite H4 in *.
 + destruct stop1;simpl in *.
     inversion H1;inversion H2.
     subst.
    (*  destruct table2; destruct table1; simpl in *.
     inversion H7.
     subst. *)
     assumption.
   - rewrite H4 in H1.
      inversion H1;inversion H2.
     subst.
     (* 
     destruct table2; destruct table1; simpl in *.
     inversion H7.
     subst.
      *) assumption.
 + case_eq(StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va nbL) (memory s) );
 [intros next Hnext | intros Hnext];
 rewrite Hnext in *; try now contradict H1.
 case_eq(Nat.eqb pageDefault next) ;intros  Hb; rewrite Hb in *.
 - inversion H2.
 subst.
 apply beq_nat_false in H3.
 now contradict H3.
-  case_eq(StateLib.Level.pred nbL); intros; rewrite H5 in *; try now contradict H2.
 destruct stop1.
 simpl in *.
 inversion H1.
 subst.
 trivial.
 simpl in *.
 rewrite H4 in *.
 rewrite Hnext in *.
 rewrite Hb in *.
 rewrite H5 in *.     
   apply IHstop2 with stop1 l next  table2 va s;trivial.
   lia.
 Qed. 
Lemma fstIndirectionContainsValue_nbLevel_1  indirection idxroot s idx va l currentPart : 
(idxroot = idxPageDir \/ idxroot = idxShadow1 \/ idxroot = idxShadow2) ->
dataStructurePdSh1Sh2asRoot idxroot s -> In currentPart (getPartitions pageRootPartition s) -> 
levelEq l levelMin = true ->
nextEntryIsPP currentPart idxroot indirection s ->
StateLib.getIndexOfAddr va levelMin = idx -> indirection <> pageDefault -> 
Some l = StateLib.getNbLevel ->  
isVE indirection idx s /\ idxroot = idxShadow1 \/
isVA indirection idx s /\ idxroot = idxShadow2 \/
isPE indirection idx s /\ idxroot = idxPageDir.
Proof. 
intros Hisroot Hroot Hcprpl Hfstlevel Hcurpd  Hidxva  Hpdnotnull Hnblevel.
unfold dataStructurePdSh1Sh2asRoot in *.
unfold currentPartitionInPartitionsList in *.


generalize (Hroot currentPart Hcprpl); clear Hroot; intro Hroot.   
assert (True) as Hvarefchild.
trivial. (** va into the list of all Vaddr **)
subst.
intros.
generalize (Hroot indirection  Hcurpd va Hvarefchild l
          (nbLevel-1) Hnblevel indirection (StateLib.getIndexOfAddr va levelMin));clear Hroot.
intros Hroot.
destruct Hroot.
+ (** prove a condition into consistency **) subst.
 induction ((nbLevel - 1)).
 * simpl in *.
   trivial. 
 * simpl. 
   rewrite Hfstlevel.
   trivial.
+ contradict H.  assumption.
+ destruct H.
  destruct H as [(H & Hnotfstlevel) | H].
  unfold StateLib.getNbLevel in *.
  assert (nbLevel > 0).
  apply nbLevelNotZero.
  destruct (gt_dec nbLevel 0).
  { simpl in *.
    inversion Hnblevel. simpl in *.
    subst.
    contradict H. simpl.  lia. } 
  { contradict H. lia. }
 destruct H. assumption.
Qed.

Lemma  lastIndirectionContainsValueRec   idxroot s l rootind indirection va idx currentPart: 
levelEq l levelMin = true ->
In currentPart (getPartitions pageRootPartition s) ->
dataStructurePdSh1Sh2asRoot idxroot s -> 
 (idxroot = idxPageDir \/ idxroot = idxShadow1 \/ idxroot = idxShadow2 )-> 
 nextEntryIsPP currentPart idxroot rootind s ->
rootind <> pageDefault -> 
(exists (nbL : level) (stop : nat),
                 Some nbL = StateLib.getNbLevel /\ stop <= nbL /\
                 getIndirection rootind va nbL stop s = Some indirection /\
                 indirection <> pageDefault /\ l = CLevel (nbL - stop) ) -> 
StateLib.getIndexOfAddr va levelMin = idx -> 
isVE indirection idx s /\ idxroot = idxShadow1 \/
isVA indirection idx s /\ idxroot = idxShadow2 \/
isPE indirection idx s /\ idxroot = idxPageDir.
Proof. 
intros Hfstlevel Hcurpart Hroot Hisroot Hcurpd
        Hpdnotnull Hindirection Hidx.
destruct Hindirection. destruct H. destruct H.
unfold dataStructurePdSh1Sh2asRoot in *.
generalize (Hroot currentPart Hcurpart); clear Hroot; intro Hroot.
assert (True) as Hvarefchild;trivial. (** va into the list of all Vaddr **)
subst.
destruct H0. destruct H1.
generalize (Hroot rootind  Hcurpd va Hvarefchild x x0 H indirection (StateLib.getIndexOfAddr va levelMin) );clear Hroot;
intros Hroot.
destruct Hroot. assumption.
destruct H2. now contradict H2. 
destruct H3.
apply levelEqBEqNatTrue in Hfstlevel.
subst.
destruct H2.
unfold levelMin in H5.
apply levelEqNat in H5.
+ destruct H3 as [(Hfalse &H3) | H3].
  contradict Hfalse;lia.
  destruct H3. assumption.
+ apply nbLevelNotZero.
+ unfold StateLib.getNbLevel in H.
  assert (nbLevel > 0).
  apply nbLevelNotZero.
  destruct (gt_dec nbLevel 0).
  simpl in *.
  inversion H. 
  subst.
  simpl. lia.
  contradict H5.
  lia.
Qed. 

Lemma fstIndirectionContainsPENbLevelGT1 idxroot s l currentpd va idxind currentPart :
(idxroot = idxPageDir \/ idxroot = idxShadow1 \/ idxroot = idxShadow2) -> 
 levelEq l levelMin = false -> 
dataStructurePdSh1Sh2asRoot idxroot s -> 
In currentPart (getPartitions pageRootPartition s) ->
nextEntryIsPP currentPart idxroot currentpd s ->
 currentpd <> pageDefault -> 
 Some l = StateLib.getNbLevel -> 
 StateLib.getIndexOfAddr va l = idxind ->  (* isPE currentpd idxpd s. *)
isPE currentpd idxind s.
Proof.
  
intros Hroot Hnotfstlevel Hisroot Hcprpl  Hcurpd Hpdnotnull Hlevel Hidx .
 unfold  dataStructurePdSh1Sh2asRoot in Hroot.
          assert (True) as Hvarefchild.
          trivial. (** va into the list of all Vaddr **)
          assert (In currentPart ( getPartitions pageRootPartition s) ) as Hcurpart.
          { unfold currentPartitionInPartitionsList in Hcprpl.
            subst. intuition. }
          subst.
          assert ( StateLib.getIndirection currentpd va l levelMin s =
          Some currentpd ) as Hnextind.
          { unfold levelMin.
            unfold CLevel.
            assert (nbLevel > 0).
            apply nbLevelNotZero.
            case_eq (lt_dec 0 nbLevel).
            intros. simpl.
            cbn. reflexivity.
            intros. contradict H. lia. }
(*           destruct Hindirection as (Hcurind & Hlevel).
          subst.   *)
          unfold dataStructurePdSh1Sh2asRoot in Hisroot.
          generalize (Hisroot currentPart Hcurpart currentpd Hcurpd va 
          Hvarefchild  l levelMin Hlevel currentpd (StateLib.getIndexOfAddr va l) Hnextind);
          clear Hisroot; intro Hisroot.
          destruct Hisroot. subst. contradict Hpdnotnull. reflexivity.
          destruct H as (H & _). 
          subst. 
          apply levelEqBEqNatFalse0 in Hnotfstlevel.
          destruct H as [(Hl & H) | H].
          assumption.
          destruct H. unfold levelMin in H.
          unfold CLevel in H. destruct (lt_dec 0 nbLevel).
           simpl in *. contradict H. lia. 
           assert (0 < nbLevel).
           apply nbLevelNotZero. now contradict H1. 
Qed. 

Lemma middleIndirectionsContainsPE  idxroot s l rootind indirection va idxind currentPart: 
 (idxroot = idxPageDir \/ idxroot = idxShadow1 \/ idxroot = idxShadow2 )-> 
levelEq l levelMin = false ->
In currentPart (getPartitions pageRootPartition s) ->
dataStructurePdSh1Sh2asRoot idxroot s -> 

rootind <> pageDefault -> 
(exists (nbL : level) (stop : nat),
                 Some nbL = StateLib.getNbLevel /\ stop <= nbL /\
                 getIndirection rootind va nbL stop s = Some indirection /\
                 indirection <> pageDefault /\ l = CLevel (nbL - stop) ) -> 
nextEntryIsPP currentPart idxroot rootind s  -> 
isPE indirection idxind s.
Proof.
intros Hisroot Hnotfstlevel Hcurpart Hroot  Hpdnotnull Hindirection Hcurpd (* Hidx *).
destruct Hindirection. destruct H.
destruct H.
subst.
unfold dataStructurePdSh1Sh2asRoot in *.
unfold currentPartitionInPartitionsList in *.
generalize (Hroot currentPart Hcurpart); clear Hroot; intro Hroot.
assert (True) as Hvarefchild.
trivial. (** va into the list of all Vaddr **)
subst.
destruct H0.  
generalize (Hroot rootind  Hcurpd va Hvarefchild x
x0 H indirection idxind);clear Hroot.
intros Hroot.
destruct H1 as (Hind & Hnotnull & Hlevel).
destruct Hroot.
assumption. now contradict H1.
apply levelEqBEqNatFalse0 in Hnotfstlevel.
subst.
destruct H1. 
destruct H1 as [(Hx & Hpe)  | H1].
+ assumption.
+ destruct H1.
  destruct H1.  subst.  apply level_gt in Hnotfstlevel.  destruct x.
  simpl in *. contradict Hnotfstlevel. lia. assert (0 < nbLevel).
  apply nbLevelNotZero. lia.
  lia.
Qed.

Lemma getIndirectionStopLevelGT s va p (l: nat) (level : level)  (l0 : nat) p0: 
l0 > level -> l = level ->  
getIndirection p va level l s = Some p0 ->  
getIndirection p va level l0 s = Some p0.
Proof.
intros.
revert p0 p level l H H0 H1.
induction l0; 
intros. now contradict H.
simpl. 
destruct l; simpl in *.
assert (  levelEq level levelMin = true).
unfold levelEqM. 
apply NPeano.Nat.eqb_eq. 
rewrite <- H0. unfold levelMin. unfold CLevel.
assert ( 0 < nbLevel) by apply nbLevelNotZero.
case_eq (lt_dec 0 nbLevel ); intros.
simpl. trivial.
now contradict H2.
rewrite H2. assumption.
simpl in *.
case_eq (levelEq level levelMin); intros.
rewrite H2 in H1. destruct l0. simpl. assumption. assumption.   
+ simpl. rewrite H2 in H1.
  case_eq(StateLib.readPhyEntry p (StateLib.getIndexOfAddr va level) (memory s) ). intros.
  rewrite H3 in H1. 
  case_eq (Nat.eqb pageDefault p1); intros;
  rewrite H4 in H1. assumption.
  case_eq (StateLib.Level.pred level);
  intros; rewrite H5 in H1.
  apply levelPredMinus1 in H5; trivial. unfold CLevel in H5.  
  case_eq(lt_dec (level - 1) nbLevel ); intros; rewrite H6 in H5. destruct level. simpl in *. subst.
  simpl in *.      
  apply IHl0 with l; trivial. simpl. lia. simpl. lia.
  destruct level. simpl in *. lia. assumption.
  intros. rewrite H3 in H1. assumption.        
Qed.

Lemma getIndirectionStopLevelGT2 s va p (l: nat) (level : level)  (l0 : nat) p0: 
l0 > level -> l = level ->  
getIndirection p va level l0 s = Some p0 ->  
getIndirection p va level l s = Some p0.
Proof.
intros.
revert p0 p level l H H0 H1.
induction l0; 
intros. now contradict H.
simpl. 
destruct l; simpl in *.
assert (  levelEq level levelMin = true).
unfold levelEqM. 
apply NPeano.Nat.eqb_eq. 
rewrite <- H0. unfold levelMin. unfold CLevel.
assert ( 0 < nbLevel) by apply nbLevelNotZero.
case_eq (lt_dec 0 nbLevel ); intros.
simpl. trivial.
now contradict H2.
rewrite H2 in H1. assumption.
simpl in *.
case_eq (levelEq level levelMin); intros.
rewrite H2 in H1. destruct l0. simpl. assumption. assumption.   
+ simpl. rewrite H2 in H1.
  case_eq(StateLib.readPhyEntry p (StateLib.getIndexOfAddr va level) (memory s) ). intros.
  rewrite H3 in H1. 
  case_eq (Nat.eqb pageDefault p1); intros;
  rewrite H4 in H1. assumption.
  case_eq (StateLib.Level.pred level);
  intros; rewrite H5 in H1.
  apply levelPredMinus1 in H5; trivial.
  unfold CLevel in H5.  
  case_eq(lt_dec (level - 1) nbLevel ); intros; rewrite H6 in H5.
  destruct level. simpl in *. subst.
  simpl in *.
   
  apply IHl0 ; trivial. simpl. lia. simpl. lia.
  destruct level. simpl in *. lia. assumption.
  intros. rewrite H3 in H1. assumption.
Qed.

Lemma getIndirectionRetDefaultLtNbLevel l1 l0 (nbL :level) p va s:
l0 > 0 -> 
l0 < l1 ->
l0 < nbL ->
getIndirection p va nbL l0 s = Some pageDefault -> 
getIndirection p va nbL l1 s = Some pageDefault.
Proof.
revert l0 nbL p va.
induction l1; intros.
+ now contradict H0.
+ simpl in *.
  case_eq (levelEq nbL levelMin); intros.
  destruct l0.
  now contradict H.
  simpl in H2. 
  rewrite H3 in H2. assumption.
  case_eq (StateLib.readPhyEntry p (StateLib.getIndexOfAddr va nbL) (memory s)); intros.
  case_eq (Nat.eqb pageDefault p0); intros; trivial.
  case_eq (StateLib.Level.pred nbL); intros.
  destruct l0.
  now contradict H2.
  simpl in H2.
  rewrite H3 in H2.
  rewrite H4 in H2.
  rewrite H5 in H2.
  rewrite H6 in H2.    
  apply IHl1 with l0.
  destruct l0.
  simpl in H2. 
  inversion H2.
  subst.
  contradict H5. 
  apply Bool.not_false_iff_true.
  symmetry.
  apply beq_nat_refl.
  lia.
  lia.
  apply levelPredMinus1 with nbL l in H3; trivial.
  destruct nbL.
  simpl in *.
  unfold CLevel in H3.
  case_eq (lt_dec (l2 - 1) nbLevel); intros; rewrite H7 in H3.
  destruct l.
  simpl in *.
  inversion H3.
  subst.
  lia. lia.
  assumption.
  unfold StateLib.Level.pred in H6.
  apply levelEqBEqNatFalse0 in H3.
  case_eq (gt_dec nbL 0); intros; rewrite H7 in *.
  now contradict H6.
  lia. 
  destruct l0. now contradict H.
  simpl in H2.
  rewrite H3 in H2.
  rewrite H4 in H2.
  assumption.
Qed.

Lemma getIndirectionNbLevelEq (l1 l0 : nat) (nbL :level) p va s:
l0 > 0 -> 
l1 = nbL ->
l0 <= nbL ->
getIndirection p va nbL l0 s = Some pageDefault -> 
getIndirection p va nbL l1 s = Some pageDefault.
Proof.
revert l0 nbL p va.
induction l1; intros.
+ lia. 
+ simpl in *.
  case_eq (levelEq nbL levelMin); intros.
  destruct l0.
  now contradict H.
  simpl in H2.
  rewrite H3 in H2. assumption.
  case_eq (StateLib.readPhyEntry p (StateLib.getIndexOfAddr va nbL) (memory s)); intros.
  case_eq (Nat.eqb pageDefault p0); intros; trivial.
  case_eq (StateLib.Level.pred nbL); intros. 
  destruct l0.
  now contradict H.
   
  simpl in H2.
  rewrite H6 in H2.
  rewrite H3 in H2.
  rewrite H4 in H2.
  rewrite H5 in H2.    
  apply IHl1 with l0.
  destruct l0.
  simpl in H2. 
  inversion H2.
  subst.
  contradict H5. 
  apply Bool.not_false_iff_true.
  symmetry.
  apply beq_nat_refl.
  lia.
  apply levelPredMinus1 with nbL l in H3; trivial.
  destruct nbL.
  simpl in *.
  unfold CLevel in H3.
  case_eq (lt_dec (l2 - 1) nbLevel); intros; rewrite H7 in H3.
  destruct l.
  simpl in *.
  inversion H3.
  subst.
  lia. lia.
  unfold StateLib.Level.pred in H6.
  apply levelEqBEqNatFalse0 in H3.
  case_eq (gt_dec nbL 0); intros; rewrite H7 in *.
  inversion H6.
  destruct l.
  simpl in *.
  inversion H9.
  lia. now contradict H3.
  assumption.
    unfold StateLib.Level.pred in H6.
  apply levelEqBEqNatFalse0 in H3.
  case_eq (gt_dec nbL 0); intros; rewrite H7 in *.
  inversion H6.
  now contradict H3.
  
  destruct l0.
  now contradict H2.
  simpl in H2.
  rewrite H3 in H2.
  rewrite H4 in H2.
  assumption.
Qed.

Lemma checkVAddrsEqualityWOOffsetTrue' n va1 va2 (nbL predNbL : level) :
StateLib.checkVAddrsEqualityWOOffset n va1 va2 nbL = true -> 
predNbL <= nbL -> 
nbL < n ->   
StateLib.getIndexOfAddr va1 predNbL  = StateLib.getIndexOfAddr va2 predNbL .
Proof.
revert nbL predNbL.
induction n.
+ simpl in *.
intros.

lia.
+
intros.
simpl in H.
case_eq(levelEq nbL levelMin); intros; rewrite H2 in *.
 - apply levelEqBEqNatTrue in H2.
subst.
assert(predNbL = levelMin).
clear H IHn.
unfold levelMin in * .
unfold CLevel in *.
case_eq(lt_dec 0 nbLevel );intros.
rewrite H in *.

destruct predNbL.
simpl in *.
assert(l0 = 0) by lia.
subst.
f_equal;apply proof_irrelevance;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
subst.
apply beq_nat_true in H.
destruct (StateLib.getIndexOfAddr va1 levelMin);
destruct (StateLib.getIndexOfAddr va2 levelMin).
simpl in *.
subst.
f_equal;apply proof_irrelevance;trivial.
- 
case_eq(StateLib.Level.pred nbL); intros; rewrite H3 in *.
 * case_eq(Nat.eqb (StateLib.getIndexOfAddr va1 nbL) (StateLib.getIndexOfAddr va2 nbL));
intros; trivial; rewrite H4 in *;try now contradict H4.
apply NPeano.Nat.lt_eq_cases in H0.
destruct H0.
 apply IHn with l;trivial.
 apply levelPredMinus1 in H3;trivial.
 
  unfold CLevel in H3.
  case_eq (lt_dec (nbL - 1) nbLevel); intros.
  rewrite H5 in *.
  destruct l.
  inversion H3.
  subst.
  simpl.
  apply levelEqBEqNatFalse0  in H2.
  lia.
  apply levelEqBEqNatFalse0 in H2.
  rewrite H5 in *.
  destruct nbL.
  simpl in *.
  lia.
 apply levelPredLt in H3;trivial.
 lia.
 apply beq_nat_true in H4.
 destruct predNbL.
 destruct nbL.
 simpl in *.
 subst.
 assert(Hl = Hl0) by apply proof_irrelevance.
 subst.
  destruct (StateLib.getIndexOfAddr va1 {| l := l1; Hl := Hl0 |}).
  destruct (StateLib.getIndexOfAddr va2 {| l := l1; Hl := Hl0 |}).
  simpl in *.
  subst.
  f_equal.
  apply proof_irrelevance.

* 
apply levelPredNone in H2.
 destruct (StateLib.Level.pred nbL).
 now contradict H3.
 now contradict H2.
Qed.

Lemma checkVAddrsEqualityWOOffsetTrue2 : 
forall (n : nat) (va1 va2 : vaddr) (nbL predNbL : level),
n <= nbLevel ->
StateLib.checkVAddrsEqualityWOOffset n va1 va2 nbL = true ->
nbL < n ->
predNbL <= nbL ->
StateLib.checkVAddrsEqualityWOOffset n va1 va2 predNbL = true.
Proof.
induction n.
simpl in *.
trivial.
intros va1 va2 nbL predNbL Htrue.
intros.
simpl in *.
case_eq  (levelEq nbL levelMin); intros;rewrite H2 in *;trivial.
+ case_eq( levelEq predNbL levelMin); intros.
  - apply levelEqBEqNatTrue in H2;trivial.
    apply levelEqBEqNatTrue in H3;trivial.
    subst.
    assumption.
  - apply levelEqBEqNatTrue in H2;trivial.
    apply levelEqBEqNatFalse in H3;trivial.
    subst.
    lia.
+ case_eq (StateLib.Level.pred nbL); intros; rewrite H3 in *.
  * case_eq(Nat.eqb (StateLib.getIndexOfAddr va1 nbL) (StateLib.getIndexOfAddr va2 nbL)); intros;
        rewrite H4 in *; try now contradict H.
    case_eq(levelEq predNbL levelMin);intros.
    apply NPeano.Nat.eqb_eq.
    apply NPeano.Nat.lt_eq_cases in H1.
    destruct H1.
    rewrite checkVAddrsEqualityWOOffsetTrue' with n  va1 va2 l predNbL;trivial.
    apply levelPredMinus1 in H3; trivial.
    { unfold CLevel in H3.
  case_eq (lt_dec (nbL - 1) nbLevel); intros.
  rewrite H6 in *.
  destruct l.
  inversion H3.
  subst.
  simpl.
  lia.
  rewrite H6 in *.
  destruct nbL.
  simpl in *.
  lia. } 
 apply levelPredLt in H3;trivial.
 lia.
 apply beq_nat_true in H4.
 destruct predNbL.
 destruct nbL.
 simpl in *.
 subst.
 assert(Hl = Hl0) by apply proof_irrelevance.
 subst.
  destruct (StateLib.getIndexOfAddr va1 {| l := l1; Hl := Hl0 |}).
  destruct (StateLib.getIndexOfAddr va2 {| l := l1; Hl := Hl0 |}).
  simpl in *.
  subst.
  trivial.
  
   case_eq  (StateLib.Level.pred predNbL ); intros;trivial.
   case_eq (Nat.eqb (StateLib.getIndexOfAddr va1 predNbL)
                    (StateLib.getIndexOfAddr va2 predNbL)
           ); intros.
  apply IHn with l.
  lia.
  assumption.
  apply levelPredLt in H3;trivial.
  apply levelPredLt in H6;trivial.
  lia.
  apply levelPredMinus1 in H6;trivial.
  unfold CLevel in H6.
  case_eq (lt_dec (predNbL - 1) nbLevel ); intros.
  rewrite H8 in H6.
  inversion H6.
  
  simpl in *.
    apply levelPredMinus1 in H3;trivial.
  unfold CLevel in H3.
  case_eq (lt_dec (nbL - 1) nbLevel ); intros.
  rewrite H10 in H3.
  inversion H3.
  
  simpl in *.
  lia.
  destruct nbL.
  simpl in *.
  lia.
  
  destruct predNbL.
  simpl in *.
  
  
  lia.

   assert(StateLib.getIndexOfAddr va1 predNbL  = StateLib.getIndexOfAddr va2 predNbL ).
   
      apply NPeano.Nat.lt_eq_cases in H1.
    destruct H1.
    rewrite checkVAddrsEqualityWOOffsetTrue' with n  va1 va2 l predNbL;trivial.
    apply levelPredMinus1 in H3; trivial.
    { unfold CLevel in H3.
  case_eq (lt_dec (nbL - 1) nbLevel); intros.
  rewrite H8 in *.
  destruct l.
  inversion H3.
  subst.
  simpl.
  lia.
  rewrite H8 in *.
  destruct nbL.
  simpl in *.
  lia. } 
 apply levelPredLt in H3;trivial.
 lia.
 apply beq_nat_true in H4.
 destruct predNbL.
 destruct nbL.
 simpl in *.
 subst.
 assert(Hl = Hl0) by apply proof_irrelevance.
 subst.
  destruct (StateLib.getIndexOfAddr va1 {| l := l2; Hl := Hl0 |}).
  destruct (StateLib.getIndexOfAddr va2 {| l := l2; Hl := Hl0 |}).
  simpl in *.
  subst.
  apply beq_nat_false in H7.
  lia.
  apply beq_nat_false in H7.
    destruct (StateLib.getIndexOfAddr va1 predNbL);
    destruct (StateLib.getIndexOfAddr va2 predNbL).
    simpl in *.
    inversion H8.
    subst.
    now contradict H7.
  * apply levelPredNone in H3.
    contradict H3.
    destruct(StateLib.Level.pred nbL).
    assumption.
    trivial.
Qed.
Lemma checkVAddrsEqualityWOOffsetTrue va1 va2 (nbL predNbL : level):
StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 nbL = true -> 
nbL < nbLevel -> 
predNbL <= nbL -> 
StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 predNbL = true.
Proof.
assert (Htrue : nbLevel <= nbLevel) by lia.
revert va1 va2 nbL predNbL Htrue.
generalize nbLevel at 1 3 4 5.
apply checkVAddrsEqualityWOOffsetTrue2.
Qed.


Lemma getIndirectionEq (nbL : level) va1 va2 pd stop s:
nbL < nbLevel  -> 
StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 nbL = true -> 
getIndirection pd va1 nbL stop s =
getIndirection pd va2 nbL stop s .
Proof.
intros Hlevel Heq.
revert nbL va1 va2  pd Hlevel Heq.
induction stop.
simpl in *.
trivial.
simpl.
intros.
case_eq (levelEq nbL levelMin).
intros;trivial.
intros.
assert(StateLib.getIndexOfAddr va1 nbL  = StateLib.getIndexOfAddr va2 nbL ).
apply checkVAddrsEqualityWOOffsetTrue' with nbLevel nbL;trivial.
rewrite H0.
case_eq (StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va2 nbL) (memory s) );
intros; trivial.
case_eq(Nat.eqb pageDefault p);intros;trivial.
case_eq( StateLib.Level.pred nbL); intros;trivial.
apply IHstop.
apply levelPredMinus1 in H3.
subst.
unfold CLevel.
case_eq( lt_dec (nbL - 1) nbLevel); intros.
simpl.
assumption.
apply levelEqBEqNatFalse0 in H;trivial.
lia.
trivial.
apply checkVAddrsEqualityWOOffsetTrue with nbL;trivial.
apply levelPredMinus1 in H3.
subst.
unfold CLevel.
case_eq( lt_dec (nbL - 1) nbLevel); intros.
simpl.
apply levelEqBEqNatFalse0 in H;trivial.
lia.
destruct nbL.
simpl in *.
lia.
assumption.
Qed.

Lemma Index_eq_i (i1 i2 : index) : (ADT.i i1) = (ADT.i i2) -> i1 = i2.
Proof.
  revert i1 i2; intros (i1 & Hi1) (i2 & Hi2).
  simpl.
  intros Heqi; subst i1.
  assert (HeqHi : Hi1 = Hi2) by apply proof_irrelevance.
  now subst.
Qed.

Lemma AllIndicesAll : forall idx : index, In idx getAllIndices.
Proof.
  assert (Gen: forall n i j: nat, i <= j < n + i -> j < tableSize -> In (CIndex j) (getAllIndicesAux i n)).
  { intros n.
    induction n as [ | n IH ]; [ intros i j H; contradict H; lia | ].
     intros i j (Hlei & Hltn) Hltsize.
     simpl.
     destruct (lt_dec i tableSize) as [ Hltsize'' | Hgtsize ];
        [ | contradict Hgtsize; now apply le_lt_trans with j ].
     apply le_lt_or_eq in Hlei; destruct Hlei as [ Hlti | Heqi ].
     - right.
        apply IH; [ | assumption ].
        now lia.
     - left; subst i.
        unfold CIndex.
        destruct (lt_dec j tableSize); [ | now contradict Hltsize ].
        now apply Index_eq_i.
  }
  unfold getAllIndices.
  intros (i & Hi).
  assert (Heq : Build_index i Hi = CIndex i).
  { unfold CIndex.
    destruct (lt_dec i tableSize); [ | now contradict Hi ].
    now apply Index_eq_i. }
  rewrite Heq.
  apply Gen; lia.
Qed.

Lemma VAddrEqVA (v1 v2: vaddr) : ADT.va v1 = ADT.va v2 -> v1 = v2.
Proof.
  revert v1 v2; intros (v1 & Hv1) (v2 & Hv2).
  simpl; intros Heq; subst v1.
  assert (Heq: Hv1 = Hv2) by apply proof_irrelevance.
  now subst.
Qed.

Lemma AllVAddrAll : forall v : vaddr, In v getAllVAddr.
Proof.
  assert (Gen: forall levels (idxs: list index), length idxs = levels -> In idxs (getAllVAddrAux levels)).
  { intros levels.
    induction levels as [ | levels IH ].

    - intros idxs Hlen0; left; symmetry.
      now rewrite <- length_zero_iff_nil.
    - intros idxs Hlen.
      unfold getAllVAddrAux.
      apply in_flat_map.
      destruct idxs as [ | idx idxs ];
        [ now contradict Hlen | ].
      exists idx; split; [apply AllIndicesAll | ].
      apply in_map_iff.
      exists idxs; split; [ easy | ].
      apply IH.
      simpl in Hlen.
      now apply eq_add_S.
  }

  unfold getAllVAddr, CVaddr.
  intros (v & Hv).
  apply in_map_iff.
  exists v.
  split.

  - destruct (PeanoNat.Nat.eq_dec (length v) (nbLevel + 1));
    [ | now contradict Hv ].
    now apply VAddrEqVA.

  - apply Gen.
    rewrite Hv.
    now apply PeanoNat.Nat.add_1_r.
Qed.
 Lemma lengthRemoveLast(A :Type) :
     forall l : list A, forall n, length l = S n ->length (removelast l) = n.
     Proof.
     induction l;simpl;intros.
     lia.
     case_eq l;intros.
     inversion H.
     subst;trivial.
     Opaque removelast.
     simpl.
     assert(n=0 \/ n > 0) by lia.
     destruct H1 ;subst.
     simpl in H.
     lia.
     
     assert((length (removelast (a0 :: l0))) = (n-1)).
     apply IHl.
     simpl in *.
     inversion H.
     rewrite H2.
     
     lia.
     rewrite H0.
     lia.
     Transparent removelast. 
     Qed.
Lemma AllVAddrWithOffset0 : 
forall va, exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel va va1 ( CLevel (nbLevel -1) ) = true. 
Proof.
intros.
assert(Hinva : In va getAllVAddr) by apply AllVAddrAll.
unfold getAllVAddrWithOffset0.
eexists.
split.
+ destruct va.

  instantiate(1:= (CVaddr (removelast va ++ [CIndex 0]))).
  apply filter_In.
  split. 
  - apply AllVAddrAll.
  - unfold checkOffset0.
  simpl.
    case_eq(Nat.eqb (nth nbLevel (CVaddr (removelast va ++ [CIndex 0])) idxDefault) (CIndex 0));
    intros;trivial.
    unfold CVaddr in *.
     assert(Hmykey : length (removelast va) = nbLevel).
     { apply lengthRemoveLast;lia. }      
    case_eq(PeanoNat.Nat.eq_dec (length (removelast va ++ [CIndex 0])) (nbLevel + 1));
      intros; rewrite H0 in *;simpl in *.
    * rewrite <- H.
      clear H0 H.
      rewrite <- Hva in e.     
      rewrite app_nth2.      
      rewrite Hmykey.
      simpl.
      case_eq(nbLevel - nbLevel);intros;try lia.
      symmetry. apply beq_nat_refl.
      lia.
    * clear H0.
    contradict n.
    rewrite app_length.
    rewrite Hmykey.
    simpl;trivial.
+ assert(Hmykey : length (removelast va) = nbLevel).
     {  assert (length va = nbLevel +1).
       { destruct va. simpl. trivial. }  apply lengthRemoveLast;lia. }
       replace va with  (CVaddr (removelast va ++ [last va idxDefault]))
       at 1.
     {
     clear Hinva.
     assert(Hmykey1 : length (removelast va) >= nbLevel) by lia.
     clear Hmykey.
     revert va  Hmykey1.
     induction nbLevel;simpl;trivial.
     intros.
     case_eq (levelEq (CLevel (n - 0)) levelMin);intros.
     + assert(n=0).
       { replace (n - 0) with n in * by lia.
         { unfold levelEq in *.
           unfold levelMin in *.
           apply beq_nat_true in H.
           apply levelEqNat;subst;trivial.
           assert(Hmykey : length (removelast va) = nbLevel).
           { assert (length va = nbLevel +1).
             { destruct va. simpl. trivial. }
             apply lengthRemoveLast;lia. }
             rewrite <-Hmykey.
             lia.
             apply nbLevelNotZero.
            destruct (CLevel n);destruct (CLevel 0);simpl in *.
            subst;f_equal;apply proof_irrelevance.
        } }
       subst.
     simpl in *.
  rewrite NPeano.Nat.eqb_eq.
  clear H.
unfold StateLib.getIndexOfAddr.
assert(Htmp :CLevel 0 + 2 =2).
{ unfold CLevel.
assert(0<nbLevel) by apply nbLevelNotZero.
case_eq( lt_dec 0 nbLevel);intros; try now contradict H1.
simpl;lia. lia. }
rewrite Htmp in *;clear Htmp.
 assert(Hi :length (removelast va ++ [CIndex 0])  =
length (removelast va ++ [last va idxDefault]) ).
{  rewrite app_length.
rewrite app_length.
simpl.
trivial. }
assert (Hi1:length (CVaddr (removelast va ++ [CIndex 0])) - 2 =
 (length (CVaddr (removelast va ++ [last va idxDefault])) - 2)).
 { unfold CVaddr .
   case_eq( PeanoNat.Nat.eq_dec (length (removelast va ++ [CIndex 0])) (nbLevel + 1));intros;
   simpl.  
   + case_eq(PeanoNat.Nat.eq_dec (length (removelast va ++ [last va idxDefault]))
      (nbLevel + 1));intros;simpl. 
     - rewrite Hi.  trivial.
     - clear H H0.
     rewrite Hi in e.
     contradiction.
   +  case_eq(PeanoNat.Nat.eq_dec (length (removelast va ++ [last va idxDefault]))
      (nbLevel + 1));intros;simpl. 
     - rewrite e.
      rewrite repeat_length.  trivial.
     -trivial. }
rewrite Hi1.
set (pos := length (CVaddr (removelast va ++ [last va idxDefault])) - 2) in *.
unfold CVaddr.
case_eq(PeanoNat.Nat.eq_dec (length (removelast va ++ [last va idxDefault]))
      (nbLevel + 1));simpl;intros;trivial.
 - assert(Hmykey : pos < length (removelast va)). 
 {  unfold pos in *. clear pos.
     unfold CVaddr.
     rewrite H.
     simpl.
     rewrite app_length.
     simpl. lia. }
   case_eq( PeanoNat.Nat.eq_dec (length (removelast va ++ [CIndex 0])) (nbLevel + 1) );
    simpl;intros;trivial.
   * rewrite app_nth1;trivial.
  rewrite app_nth1;trivial.
 
   * clear H H0.  rewrite Hi in *. contradiction.
  -  case_eq( PeanoNat.Nat.eq_dec (length (removelast va ++ [CIndex 0])) (nbLevel + 1));
  simpl;intros;trivial.  clear H H0.  rewrite Hi in *. contradiction. 
  + case_eq(StateLib.Level.pred (CLevel (n - 0)));simpl; intros;trivial.
    case_eq(Nat.eqb (StateLib.getIndexOfAddr (CVaddr (removelast va ++ [last va idxDefault]))
    (CLevel (n - 0)))
  (StateLib.getIndexOfAddr (CVaddr (removelast va ++ [CIndex 0]))
    (CLevel (n - 0))));intros.
*   assert( StateLib.checkVAddrsEqualityWOOffset n
        (CVaddr (removelast va ++ [last va idxDefault]))
        (CVaddr (removelast va ++ [CIndex 0])) (CLevel (n - 1)) = true).
        apply IHn;trivial.
        lia.
         assert(Hmykey : length (removelast va) = nbLevel).
     {  assert (length va = nbLevel +1).
       { destruct va. simpl. trivial. }  apply lengthRemoveLast;lia. }
    apply checkVAddrsEqualityWOOffsetTrue2 with (CLevel (n - 1));trivial.
     rewrite Hmykey in *.
     lia.
     unfold CLevel.
     case_eq(lt_dec (n - 1) nbLevel );simpl;intros;trivial.
     assert(Hn : n=0 \/ n> 0) by lia.
     destruct Hn as [Hn | Hn];subst.
     simpl in *. 
    assert( Htrue : levelEq (CLevel ( 0)) levelMin = true).
    {  unfold levelEq. unfold levelMin.
      symmetry. apply beq_nat_refl. }
      rewrite Htrue in *.
      intuition.
      lia.
      lia.
      replace (n-0) with n in * by lia.
      simpl in *.
     apply levelPredMinus1 in H0;trivial.
     subst.
     unfold CLevel at 2.
     case_eq( lt_dec n nbLevel);intros;simpl.
     lia.
     clear H0.
     rewrite <-  Hmykey in n0.
     lia.
  * rewrite <- H1.
      rewrite NPeano.Nat.eqb_eq.
        replace (n-0) with n in * by lia.
        
        unfold StateLib.getIndexOfAddr.

 assert(Hi :length (removelast va ++ [CIndex 0])  =
length (removelast va ++ [last va idxDefault]) ).
        {  rewrite app_length.
        rewrite app_length.
        simpl.
        trivial. }
assert (Hi1:length (CVaddr (removelast va ++ [CIndex 0])) -  (CLevel n + 2) =
 (length (CVaddr (removelast va ++ [last va idxDefault])) -  (CLevel n + 2))).
 { unfold CVaddr .
   case_eq( PeanoNat.Nat.eq_dec (length (removelast va ++ [CIndex 0])) (nbLevel + 1));intros;
   simpl.  
   + case_eq(PeanoNat.Nat.eq_dec (length (removelast va ++ [last va idxDefault]))
      (nbLevel + 1));intros;simpl. 
     - rewrite Hi.  trivial.
     - clear H2 H3.
     rewrite Hi in e.
     contradiction.
   +  case_eq(PeanoNat.Nat.eq_dec (length (removelast va ++ [last va idxDefault]))
      (nbLevel + 1));intros;simpl. 
     - rewrite e.
      rewrite repeat_length.  trivial.
     -trivial. }
rewrite Hi1.
set (pos := length (CVaddr (removelast va ++ [last va idxDefault])) -  (CLevel n + 2)) in *.
unfold CVaddr.
case_eq(PeanoNat.Nat.eq_dec (length (removelast va ++ [last va idxDefault]))
      (nbLevel + 1));simpl;intros;trivial.
 - assert(Hmykey : pos < length (removelast va)). 
 {  unfold pos in *. clear pos.
     unfold CVaddr.
     rewrite H2.
     simpl.
     rewrite app_length.
     simpl. lia. }
   case_eq( PeanoNat.Nat.eq_dec (length (removelast va ++ [CIndex 0])) (nbLevel + 1) );
    simpl;intros;trivial.
    --
    
   rewrite app_nth1;trivial.
  rewrite app_nth1;trivial.
 
   -- clear H2 H3.  rewrite Hi in *. contradiction.
  -  case_eq( PeanoNat.Nat.eq_dec (length (removelast va ++ [CIndex 0])) (nbLevel + 1));
  simpl;intros;trivial.  clear H2 H3.  rewrite Hi in *. contradiction. }
  rewrite <- app_removelast_last .
  destruct va. unfold CVaddr.
  case_eq( PeanoNat.Nat.eq_dec (length  {| ADT.va := va; Hva := Hva |}) (nbLevel + 1));intros;simpl in *;trivial.
  f_equal.
  apply proof_irrelevance.
  clear H.
  rewrite Hva in *.
  now contradict n.
  destruct va.
  simpl. 
  intuition.
  subst.
  simpl in *.
  lia.
Qed.
 

Lemma noDupAllVaddr : NoDup getAllVAddr.
Proof.
  assert (Gen: forall levels (idxs: list index), In idxs (getAllVAddrAux levels) -> length idxs = levels) .
  { intros levels.
    induction levels as [ | levels IH ].

    - intros idxs Hlen0. simpl in *. intuition. rewrite <- H.
    apply length_zero_iff_nil;trivial.
    - intros idxs Hlen.
      simpl in *.
      rewrite  in_flat_map in Hlen.
      destruct Hlen as (x & Hx & Hxx).
      rewrite in_map_iff in Hxx.
      destruct Hxx as (xs & Hxs & Hgen).
      rewrite <- Hxs.
      simpl.
      f_equal.
      apply IH;trivial.
  }
  assert(Gen1 :  forall  (idxs : list index),
   In idxs (getAllVAddrAux (S nbLevel)) -> length idxs = (S nbLevel)).
    { intros.
      apply Gen;trivial. }
  clear Gen.     
  unfold getAllVAddr.
  assert(Hnodup : NoDup (getAllVAddrAux (S nbLevel))).
  { clear Gen1.
  
    induction (S nbLevel).
    simpl;constructor;intuition.
    constructor.
    simpl. unfold getAllIndices. simpl.
    
    assert(NoDup (getAllIndicesAux 0 tableSize)). 
    { clear IHn n.
       assert (Gen: forall n i j: nat, i <= j < n + i -> j < tableSize -> In (CIndex j) (getAllIndicesAux i n)).
  { intros n.
    induction n as [ | n IH ]; [ intros i j H; contradict H; lia | ].
     intros i j (Hlei & Hltn) Hltsize.
     simpl.
     destruct (lt_dec i tableSize) as [ Hltsize'' | Hgtsize ];
        [ | contradict Hgtsize; now apply le_lt_trans with j ].
     apply le_lt_or_eq in Hlei; destruct Hlei as [ Hlti | Heqi ].
     - right.
        apply IH; [ | assumption ].
        now lia.
     - left; subst i.
        unfold CIndex.
        destruct (lt_dec j tableSize); [ | now contradict Hltsize ].
        now apply Index_eq_i.
  } 
  
  clear Gen. 
  assert(tableSize <= tableSize) by lia.
  generalize 0. 
  revert H.
  generalize tableSize at 1 3 .
  induction n. simpl. constructor.
  intros.
  simpl.
  case_eq( lt_dec n0 tableSize);intros;constructor.
  simpl.
  assert (Gen: forall n i j: nat, j < i -> ~In (CIndex j) (getAllIndicesAux i n)).
  { clear.  intros n.
    induction n.
    simpl. intuition.
    simpl.
    intros.
    
  case_eq(lt_dec i tableSize);intros.
  simpl.
  apply Classical_Prop.and_not_or.
  split.
  unfold CIndex.
  case_eq (lt_dec j tableSize );intros.
  unfold not;intros.
  inversion H2.
  subst.
  lia.
  lia.
  apply IHn. lia. 
  intuition.
   }
  assert( ~ In (CIndex n0) (getAllIndicesAux (S n0) n)).
  apply Gen.
  lia.
  unfold CIndex in H1.
  rewrite H0 in *.
  assumption.
  simpl.
  apply IHn.
   lia.  }
   induction  (getAllIndicesAux 0 tableSize).
   +
   simpl.
   constructor.
   +
   simpl.
   apply NoDupSplitInclIff.
   split.
   -
   split.
   *
   clear IHl.
   induction (getAllVAddrAux n).
   simpl.
   constructor.
   simpl.
   apply NoDup_cons.
   rewrite in_map_iff.
   unfold not;intros.
   destruct H0 as (x & Hx & Hxx).
   inversion Hx.
   subst.
   apply NoDup_cons_iff in IHn.
   intuition.
   apply IHl0.
   apply NoDup_cons_iff in IHn.
   intuition.
   *
   apply IHl.
   apply NoDup_cons_iff in H.
   intuition.
   -
   unfold disjoint.
   intros.
   assert( NoDup (flat_map (fun idx : index => map (cons idx) (getAllVAddrAux n)) l)).
   apply IHl.
   apply NoDup_cons_iff in H.
   intuition. clear IHl.
   rewrite in_map_iff in H0.
   destruct H0 as (x0 & Hx0 &Hxx0).
   rewrite <- Hx0 in *.
   rewrite in_flat_map.
   unfold not;intros.
   destruct H0 as (b & Hb & Hbb).
   rewrite in_map_iff in Hbb.
   
   
   destruct Hbb as  (c & Hc & Hcc).
   
   inversion Hc.
   subst.
   clear Hc.
      apply NoDup_cons_iff in H.
      intuition.
  }
  induction (getAllVAddrAux (S nbLevel)).
  simpl in *.
  constructor.
  simpl.
  apply NoDup_cons_iff in Hnodup.
  constructor.
  simpl in *.
  destruct Hnodup.
  clear IHl.
  clear H0.
  rewrite in_map_iff.
  contradict H.
  destruct H as (x & Hx & Hxx)  .
  assert(length x = S nbLevel).
  apply Gen1.
  right.
  trivial.
  assert(length a = S nbLevel).
  apply Gen1.
  left;trivial.
  assert (x = a).
  unfold CVaddr in *.
  case_eq ( PeanoNat.Nat.eq_dec (length x) (nbLevel + 1) ); intros;
  rewrite H1 in *.  
  case_eq(PeanoNat.Nat.eq_dec (length a) (nbLevel + 1));intros;
  rewrite H2 in *.
  inversion Hx;trivial.
  clear H2 Hx.
  rewrite  H0 in n.
  lia.
  clear H1 Hx.
  rewrite H in n.
  lia.
  subst. trivial.
  apply IHl.
  intros.
  apply Gen1.
  simpl;right;trivial.
  intuition.    
Qed. (** noDupAllVaddr*)

Lemma filterOptionInIff l elt : 
List.In elt (filterOption l) <-> List.In (SomePage elt) l.
Proof.
split. 
+ revert l elt.
  induction l.
  simpl; trivial.  
  intros.
  simpl in *.
  case_eq a; intros .
  *
  rewrite H0 in H.
  simpl in H.
  destruct H;
  subst.
  left; trivial.
  right. 
  apply IHl; trivial.
  *
  rewrite H0 in H. 
  right. apply IHl; trivial.
  *
  rewrite H0 in H. 
  right. apply IHl; trivial.
+ revert l elt.
  induction l.
  simpl; trivial.  
  intros.
  simpl in *.
  case_eq a; intros .
  *
  rewrite H0 in H.
  simpl in H.
  destruct H;
  subst.
  left; trivial.
  inversion H; trivial.
  simpl.   
  right. 
  apply IHl; trivial.
  *
  apply IHl; trivial.
  destruct H. subst.
  now contradict H0.
  assumption.
  *
  apply IHl; trivial.
  destruct H. subst.
  now contradict H0.
  assumption.  
Qed.

Lemma checkVAddrsEqualityWOOffsetEqFalse  (nbL alevel : level): 
forall va1 va2, 
Some nbL = StateLib.getNbLevel -> 
alevel <= nbL -> 
false = StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 alevel ->
va1 <> va2.
Proof.
intros.
revert alevel H1 H0.
induction nbLevel;
simpl in *; intros.  
- now contradict H1.
- case_eq(levelEq alevel levelMin); intros; rewrite H2 in *.
  + unfold not; intros.
    subst.
    symmetry in H1.
    apply beq_nat_false in H1.
    apply H1. reflexivity.
  + case_eq (StateLib.Level.pred alevel); intros; rewrite H3 in *; try now contradict H1.
    case_eq (Nat.eqb (StateLib.getIndexOfAddr va1 alevel)
                     (StateLib.getIndexOfAddr va2 alevel)
            ); intros; rewrite H4 in *.
    apply IHn with l; trivial.
    apply levelPredMinus1 in H3; trivial.
    apply getNbLevelEq in H.
    assert(0<nbLevel) by apply nbLevelNotZero.
    unfold CLevel in *.
    case_eq(lt_dec (nbLevel - 1) nbLevel); intros; rewrite H6 in *; try lia.
    case_eq(lt_dec (alevel - 1) nbLevel); intros; rewrite H7 in *; simpl in *.
    destruct nbL; simpl in *.
    inversion H.
    subst.
    simpl.
    destruct alevel.
    simpl in *.
    lia.
    destruct alevel.
    simpl in *.
    lia.
    unfold not; intros.
    subst.
    apply beq_nat_false in H4.
    apply H4. reflexivity.
Qed.

(* Lemma twoMappedPagesAreDifferent' phy1 phy2 v1 v2 p s: 
getMappedPage p s v1 = Some phy1 ->
 In v1 getAllVAddr ->
 getMappedPage p s v2 = Some phy2-> 
In v2 getAllVAddr ->
NoDup (filterOption (map (getMappedPage p s) getAllVAddr)) -> 
v1 <> v2 -> 
phy1 <> phy2.
Proof.
revert phy1 phy2 v1 v2.
induction getAllVAddr.
intuition.
intros.
destruct H0; destruct H2.
subst.
(* rewrite H2 in H4. *)
now contradict H4.
subst.
simpl in *. 
rewrite H in H3.
apply NoDup_cons_iff in H3.
destruct H3.
assert(In phy2 (filterOption (map (getMappedPage p s) l))).
apply filterOptionInIff.
apply in_map_iff.
exists v2; split; trivial.
unfold not; intros.
subst.
now contradict H0.
subst.
simpl in *.
rewrite H1 in H3.
apply NoDup_cons_iff in H3.
destruct H3.
assert(In phy1 (filterOption (map (getMappedPage p s) l))).
apply filterOptionInIff.
apply in_map_iff.
exists v1; split; trivial.
unfold not; intros.
subst.
now contradict H0.
subst.
apply IHl with v1 v2; trivial.
simpl in H3.
destruct(getMappedPage p s a ).
apply NoDup_cons_iff in H3.
intuition.
assumption.
Qed.
 *)
Lemma getMappedPageEq pd va1 va2  nbL s : 
StateLib.getNbLevel = Some nbL -> 
StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 nbL = true -> 
getMappedPage pd s va1 = getMappedPage pd s va2.
Proof.
intros HnbL Heqva.
unfold getMappedPage.
rewrite HnbL.
assert(Heqind : getIndirection pd va1 nbL (nbLevel - 1) s =
getIndirection pd va2 nbL (nbLevel - 1) s).
apply getIndirectionEq;trivial.
apply getNbLevelLt;trivial.
rewrite Heqind.
destruct (getIndirection pd va2 nbL (nbLevel - 1) s);trivial.
assert(Heqidx : (StateLib.getIndexOfAddr va1 levelMin) = (StateLib.getIndexOfAddr va2 levelMin)).
apply checkVAddrsEqualityWOOffsetTrue'  with nbLevel nbL;trivial.
apply fstLevelLe.
apply getNbLevelLt;trivial.
rewrite Heqidx;trivial.
Qed.


Lemma checkChildEq partition va1 va2  nbL s : 
StateLib.getNbLevel = Some nbL -> 
StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 nbL = true -> 
checkChild partition nbL s va1 = checkChild partition nbL s va2.
Proof.
intros HnbL Heqva.
unfold checkChild.
destruct (StateLib.getFstShadow partition (memory s)) ;trivial.
assert(Heqind : getIndirection p va1 nbL (nbLevel - 1) s =
getIndirection p va2 nbL (nbLevel - 1) s).
apply getIndirectionEq;trivial.
apply getNbLevelLt;trivial.
rewrite Heqind.
destruct (getIndirection p va2 nbL (nbLevel - 1) s);trivial.
assert(Heqidx : (StateLib.getIndexOfAddr va1 levelMin) = (StateLib.getIndexOfAddr va2 levelMin)).
apply checkVAddrsEqualityWOOffsetTrue'  with nbLevel nbL;trivial.
apply fstLevelLe.
apply getNbLevelLt;trivial.
rewrite Heqidx;trivial.
Qed.

Lemma getPDFlagEq sh1 va1 va2  nbL s : 
StateLib.getNbLevel = Some nbL -> 
StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 nbL = true -> 
getPDFlag sh1 va1 s = getPDFlag sh1 va2 s.
Proof.
intros HnbL Heqva.
unfold getPDFlag.
rewrite HnbL.
assert(Heqind : getIndirection sh1 va1 nbL (nbLevel - 1) s =
getIndirection sh1 va2 nbL (nbLevel - 1) s).
apply getIndirectionEq;trivial.
apply getNbLevelLt;trivial.
rewrite Heqind.
destruct (getIndirection sh1 va2 nbL (nbLevel - 1) s);trivial.
assert(Heqidx : (StateLib.getIndexOfAddr va1 levelMin) = (StateLib.getIndexOfAddr va2 levelMin)).
apply checkVAddrsEqualityWOOffsetTrue'  with nbLevel nbL;trivial.
apply fstLevelLe.
apply getNbLevelLt;trivial.
rewrite Heqidx;trivial.
Qed.

Lemma getVirtualAddressSh1Eq sh1 va1 va2  nbL s : 
StateLib.getNbLevel = Some nbL -> 
StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 nbL = true -> 
getVirtualAddressSh1 sh1 s va1 = getVirtualAddressSh1 sh1 s va2.
Proof.
intros HnbL Heqva.
unfold getVirtualAddressSh1.
rewrite HnbL.
assert(Heqind : getIndirection sh1 va1 nbL (nbLevel - 1) s =
getIndirection sh1 va2 nbL (nbLevel - 1) s).
apply getIndirectionEq;trivial.
apply getNbLevelLt;trivial.
rewrite Heqind.
destruct (getIndirection sh1 va2 nbL (nbLevel - 1) s);trivial.
assert(Heqidx : (StateLib.getIndexOfAddr va1 levelMin) = (StateLib.getIndexOfAddr va2 levelMin)).
apply checkVAddrsEqualityWOOffsetTrue'  with nbLevel nbL;trivial.
apply fstLevelLe.
apply getNbLevelLt;trivial.
rewrite Heqidx;trivial.
Qed.

Lemma  checkVAddrsEqualityWOOffsetTrans :
forall vaChild va1 a level, 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va1
          level = true -> 
StateLib.checkVAddrsEqualityWOOffset nbLevel a va1 level =
      false ->
StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild a level = false.
Proof.

induction nbLevel;simpl;trivial.
intros. 
case_eq(levelEq level levelMin);intros;rewrite H1 in *.
+
apply beq_nat_true in H.
rewrite H.
apply NPeano.Nat.eqb_neq.
apply beq_nat_false in H0.
intuition.
+
case_eq(StateLib.Level.pred level);intros;rewrite H2 in *.
-
case_eq(Nat.eqb (StateLib.getIndexOfAddr vaChild level)
                (StateLib.getIndexOfAddr va1 level)
       );intros;rewrite H3 in *.
      * apply beq_nat_true in H3. trivial.
        rewrite H3;trivial. 
        rewrite PeanoNat.Nat.eqb_sym;trivial.
        case_eq(Nat.eqb (StateLib.getIndexOfAddr a level)
                        (StateLib.getIndexOfAddr va1 level)
               );intros H4;
        rewrite H4 in *;trivial.
        apply IHn  with va1;trivial;trivial.
    * now contradict H.
 - now contradict H0.
Qed.
Lemma checkVAddrsEqualityWOOffsetPermut va1 va2 level1 : 
  StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 level1 = 
  StateLib.checkVAddrsEqualityWOOffset nbLevel va2 va1 level1. 
Proof.
  revert va1 va2 level1.
  induction nbLevel.
  simpl. trivial.
  simpl. intros.
  case_eq (levelEq level1 levelMin); intros.
  apply NPeano.Nat.eqb_sym.
  case_eq(StateLib.Level.pred level1);
  intros; trivial. 
  rewrite  NPeano.Nat.eqb_sym.
  case_eq (Nat.eqb (StateLib.getIndexOfAddr va2 level1)
                   (StateLib.getIndexOfAddr va1 level1)
          ); intros; trivial.
Qed.

Lemma checkVAddrsEqualityWOOffsetEqTrue  descChild nbL : 
StateLib.checkVAddrsEqualityWOOffset nbLevel descChild descChild nbL = true.
Proof.
revert nbL.
induction nbLevel;intros.
simpl;trivial.
simpl.
destruct (levelEq nbL levelMin).
symmetry.
apply beq_nat_refl.
destruct(StateLib.Level.pred nbL);trivial.
rewrite <- beq_nat_refl.
apply IHn;trivial.
Qed.
Lemma twoMappedPagesAreDifferent phy1 phy2 v1 v2 p nbL s: 
getMappedPage p s v1 = SomePage phy1 ->
getMappedPage p s v2 = SomePage phy2-> 
NoDup (filterOption (map (getMappedPage p s) getAllVAddrWithOffset0)) -> 
StateLib.getNbLevel = Some nbL -> 
StateLib.checkVAddrsEqualityWOOffset nbLevel v1 v2 nbL = false -> 
phy1 <> phy2.
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
Qed.

Lemma eqMappedPagesEqVaddrs phy1 v1 v2 p s: 
getMappedPage p s v1 = SomePage phy1 ->
 In v1 getAllVAddrWithOffset0 ->
 getMappedPage p s v2 = SomePage phy1-> 
In v2 getAllVAddrWithOffset0 ->
NoDup (filterOption (map (getMappedPage p s) getAllVAddrWithOffset0)) -> 
v1 = v2.
Proof.
revert phy1  v1 v2.
induction getAllVAddrWithOffset0.
intuition.
intros.
destruct H0; destruct H2.
+
subst.
reflexivity.
+ subst.
(* rewrite H2 in H4.
now contradict H4.
subst.
 *)simpl in *. 
rewrite H in H3.
apply NoDup_cons_iff in H3.
destruct H3.
assert(In phy1 (filterOption (map (getMappedPage p s) l))).
apply filterOptionInIff.
apply in_map_iff.
exists v2; split; trivial.
now contradict H0.
+
subst.
simpl in *. 
rewrite H1 in H3.
apply NoDup_cons_iff in H3.
destruct H3.
assert(In phy1 (filterOption (map (getMappedPage p s) l))).
apply filterOptionInIff.
apply in_map_iff.
exists v1; split; trivial.
now contradict H0.
+ simpl in *.
  case_eq (getMappedPage p s a ); intros; rewrite H4 in *.
  apply NoDup_cons_iff in H3.
  destruct H3.
  apply IHl with phy1; trivial.
  apply IHl with phy1; trivial.
    apply IHl with phy1; trivial.
Qed.


Lemma getAccessibleMappedPageEq pd va1 va2  nbL s : 
StateLib.getNbLevel = Some nbL -> 
StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 nbL = true -> 
getAccessibleMappedPage pd s va1 = getAccessibleMappedPage pd s va2.
Proof.
intros HnbL Heqva.
unfold getAccessibleMappedPage.
rewrite HnbL.
assert(Heqind : getIndirection pd va1 nbL (nbLevel - 1) s =
getIndirection pd va2 nbL (nbLevel - 1) s).
apply getIndirectionEq;trivial.
apply getNbLevelLt;trivial.
rewrite Heqind.
destruct (getIndirection pd va2 nbL (nbLevel - 1) s);trivial.
assert(Heqidx : (StateLib.getIndexOfAddr va1 levelMin) = (StateLib.getIndexOfAddr va2 levelMin)).
apply checkVAddrsEqualityWOOffsetTrue'  with nbLevel nbL;trivial.
apply fstLevelLe.
apply getNbLevelLt;trivial.
rewrite Heqidx;trivial.
Qed.



Lemma physicalPageIsAccessible (currentPart : page) (ptPDChild : page)
phyPDChild pdChild idxPDChild accessiblePDChild  nbL presentPDChild 
currentPD  s: 
 (Nat.eqb pageDefault ptPDChild ) = false ->
accessiblePDChild = true -> 
presentPDChild = true -> 
StateLib.getIndexOfAddr pdChild levelMin = idxPDChild -> 
nextEntryIsPP currentPart idxPageDir currentPD s -> 
Some nbL = StateLib.getNbLevel ->
(forall idx : index,
        StateLib.getIndexOfAddr pdChild levelMin = idx ->
        isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s) -> 
entryPresentFlag ptPDChild idxPDChild presentPDChild s -> 
entryUserFlag ptPDChild idxPDChild accessiblePDChild s -> 
isEntryPage ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) phyPDChild s -> 
In currentPart (getPartitions pageRootPartition s) -> 
In phyPDChild (getAccessibleMappedPages currentPart s). 
Proof. 
intros Hnotnull Haccess Hpresentflag Hidx Hroot Hnbl
Histblroot Hpresent Haccessentry Hentry Hcons.
unfold getAccessibleMappedPages .
assert( Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD). 
{ 
unfold nextEntryIsPP in Hroot.
unfold StateLib.getPd. 
destruct (StateLib.Index.succ idxPageDir); [| now contradict Hroot].
unfold StateLib.readPhysical.
destruct (lookup currentPart i (memory s) pageEq idxEq) ; try now contradict Hroot.
destruct v ; try now contradict Hroot. subst; trivial. }
rewrite Hcurpd.
unfold getAccessibleMappedPagesAux.
apply filterOptionInIff.
unfold getAccessibleMappedPagesOption.
apply in_map_iff.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel pdChild va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1.
split; [| trivial].
assert(Hnewgoal : getAccessibleMappedPage currentPD s pdChild = SomePage phyPDChild). 
{ unfold getAccessibleMappedPage.
rewrite <- Hnbl.
assert (Hind : getIndirection currentPD pdChild nbL   (nbLevel - 1) s = Some ptPDChild).
{ simpl. 
  apply getIndirectionStopLevelGT2 with (nbL+1); auto.
  lia.
  unfold StateLib.getNbLevel in Hnbl.
  assert(0<nbLevel) by apply nbLevelNotZero.
  case_eq (gt_dec nbLevel 0); intros.
  rewrite H0 in Hnbl.
  inversion Hnbl.
  simpl. lia.
  now contradict H0.
  apply Histblroot in Hidx.
  destruct Hidx as (Hpe & Hgettbl).
  unfold getTableAddrRoot in Hgettbl.
  destruct Hgettbl as (_ &Hind).
  apply Hind in Hroot.
  clear Hind.
  destruct Hroot as (nbl & HnbL & stop & Hstop & Hind).
  subst. rewrite <- Hnbl in HnbL.
  inversion HnbL. subst. assumption. }
rewrite Hind.
assert(Hpresflag :  StateLib.readPresent ptPDChild 
(StateLib.getIndexOfAddr pdChild levelMin) (memory s) = Some true).
{ subst. unfold StateLib.readPresent.
  unfold  entryPresentFlag in Hpresent.
  destruct (lookup ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) (memory s) pageEq idxEq )
  ;[ | now contradict Hpresent].
  destruct v; try now contradict Hpresent.
  f_equal. subst.
  symmetry.
  assumption. }
rewrite Hpresflag.
assert(Haccessflag :  StateLib.readAccessible ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) (memory s) = Some true).
{ subst. unfold StateLib.readAccessible.
  unfold  entryUserFlag in Haccessentry.
  destruct (lookup ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) (memory s) pageEq idxEq )
  ;[ | now contradict Haccessentry].
  destruct v; try now contradict Haccessentry.
  f_equal. subst.
  symmetry.
  assumption. }
rewrite Haccessflag.
subst.
unfold isEntryPage in *.
unfold StateLib.readPhyEntry.
subst.
destruct(lookup ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) (memory s) pageEq idxEq);
[| now contradict Hentry].
destruct v; try now contradict Hentry.
rewrite Hnotnull.
f_equal. assumption. }
rewrite <- Hnewgoal.
apply getAccessibleMappedPageEq with (CLevel (nbLevel - 1));trivial.
apply getNbLevelEqOption.
rewrite <- Hva11.
apply checkVAddrsEqualityWOOffsetPermut.
Qed.

Lemma getIndirectionFstStep s root va (level1 : level) stop table : 
level1 > 0 -> stop > 0 -> root <> pageDefault ->  table <> pageDefault -> 
getIndirection root va level1 stop s = Some table -> 
exists pred page1,page1 <> pageDefault /\ Some pred = StateLib.Level.pred level1 /\ 
  StateLib.readPhyEntry root (StateLib.getIndexOfAddr va level1) (memory s) = Some page1 /\ 
 getIndirection page1 va pred (stop -1) s = Some table.
Proof.
intros Hl Hstop Hroot Hnull Hind .
destruct stop.
now contradict Hstop.
simpl in *.    
case_eq (levelEq level1 levelMin).
intros Hfst.
rewrite Hfst in Hind.
apply beq_nat_true in Hfst. unfold levelMin in Hfst.
unfold CLevel in Hfst.
case_eq (lt_dec 0 nbLevel).
intros. rewrite H in Hfst.
simpl in Hfst.
lia.
intros.
assert (0 < nbLevel) by apply nbLevelNotZero.
now contradict H0.
intros Hfst.
rewrite Hfst in Hind.
case_eq(StateLib.readPhyEntry root (StateLib.getIndexOfAddr va level1) (memory s)).
intros p Hread.
rewrite Hread in Hind.
case_eq(Nat.eqb pageDefault p);intros Hnullp; 
rewrite Hnullp in Hind.
inversion Hind. subst. now contradict Hnull.
destruct (StateLib.Level.pred level1 ).
exists l.
exists p.
repeat split; trivial.
apply beq_nat_false in Hnullp.
unfold not.
intros.
contradict Hnullp.
subst. trivial.
simpl. 
rewrite (NPeano.Nat.sub_0_r).
assumption.
inversion Hind.
intros. rewrite H in Hind.
inversion Hind.
Qed. 

Lemma readPhyEntryInGetTablePages s root: 
forall n : nat,
n <= tableSize ->
forall (idx : nat) (page1 : page),
idx < n ->
page1 <> pageDefault ->
StateLib.readPhyEntry root (CIndex idx) (memory s) = Some page1 ->
In page1 (getTablePages root n s).
Proof.
unfold StateLib.readPhyEntry in *. intros.
case_eq (lookup root (CIndex idx) (memory s) pageEq idxEq); 
[ intros v Hv| intros Hv] ; rewrite Hv in  H2; [ | now contradict H2 ].
destruct v; inversion H2.
subst. clear H2.
induction n.
 + intros.  now contradict H0.
 + destruct (PeanoNat.Nat.eq_dec n idx) as [ Heq | Hneq ]. 
    - simpl. subst.
      rewrite Hv.
      destruct pageDefault.
      destruct p. cbn in *. destruct pa.
      simpl in *. subst.
      case_eq (Nat.eqb p p0).
      * intros. apply beq_nat_true in H2.
        simpl in *.
        contradict H1.
        subst. 
        assert (Hp = Hp0) by apply proof_irrelevance. subst. reflexivity.
      * intros. apply in_app_iff. right.  simpl. left. reflexivity.
    - assert (idx < n). lia.
      assert (n <= tableSize). lia.
      simpl.
      case_eq (lookup root (CIndex n) (memory s) pageEq idxEq);
      [intros v Hlookup | intros Hlookup]; [ | apply IHn; trivial].
      destruct v; try apply IHn ; trivial.
      case_eq (Nat.eqb (pa p0) pageDefault); intros Hnull;
      [  | apply in_app_iff; left ] ; apply IHn ; trivial.
Qed.

Lemma getIndirectionInGetIndirections1 (stop : nat) s:
(stop+1) <= nbLevel ->
forall (va : vaddr) (level1 : level) (table root : page) ,
getIndirection root va level1 stop s = Some table ->
table <> pageDefault ->
root <> pageDefault -> In table (getIndirectionsAux root s (stop+1)).
Proof.
induction stop.
simpl.
intros. 
inversion H0;left;trivial.
intros. 
simpl in *. 
assert (root = table \/ root <> table) by apply pageDecOrNot.
destruct H3 ;subst. 
+ left;trivial.
+ right. 
case_eq(levelEq level1 levelMin);intros;rewrite H4 in *.
  * inversion H0;subst. now contradict H3. 
  * rewrite in_flat_map.
    case_eq(StateLib.readPhyEntry root (StateLib.getIndexOfAddr va level1)
         (memory s));intros; 
    rewrite H5 in *;try now contradict H0. 
    case_eq(Nat.eqb pageDefault p);intros; rewrite H6 in *; try now contradict H0.
    inversion H0.
    subst. now contradict H1. 
    case_eq (StateLib.Level.pred level1);intros;
    rewrite H7 in *;try now contradict H0. 
    exists p. 
    split.
    apply readPhyEntryInGetTablePages with (StateLib.getIndexOfAddr va level1);trivial.
     destruct (StateLib.getIndexOfAddr va level1 );trivial.
         apply beq_nat_false in H6.
    unfold not;intros;subst.
    now contradict H6.
    rewrite <- H5.
    f_equal.
    destruct (StateLib.getIndexOfAddr va level1).
    simpl. 
    unfold CIndex.
    case_eq(lt_dec i tableSize );intros.
    simpl.
    f_equal.
    apply proof_irrelevance.
    lia. 
    apply IHstop with va l. lia.
    trivial.
    trivial.
    apply beq_nat_false in H6.
    unfold not;intros;subst.
    now contradict H6.
Qed.


 



Lemma getIndirectionInGetIndirections (n : nat) s:
n > 0 ->
n <= nbLevel ->
forall (va : vaddr) (level1 : level) (table root : page) (stop : nat),
getIndirection root va level1 stop s = Some table ->
table <> pageDefault ->
level1 <= CLevel (n - 1) -> root <> pageDefault -> In table (getIndirectionsAux root s n).
Proof.
intros Hl Hi  va  level1  table root stop 
Hind  Hnotnull Hlevel Hrnotnull .
destruct n. now contradict Hl.
revert Hind Hnotnull Hlevel Hl  Hrnotnull  (* Hlevel *).
revert va level1 table root stop . 
induction (S n);  [ simpl; intros; now contradict Hl |].
intros. simpl.
destruct stop; [ simpl in *; left; inversion Hind; trivial| ].
assert (levelEq level1 levelMin = true \/ levelEq level1 levelMin = false).
{ unfold levelEq.
  destruct level1.
  simpl. unfold levelMin.
  unfold CLevel.
  case_eq(lt_dec 0 nbLevel); intros.
  simpl.
  destruct l. left.
  symmetry. apply beq_nat_refl.
  right.
  apply NPeano.Nat.eqb_neq. lia.
  assert (0 < nbLevel) by apply nbLevelNotZero.
  now contradict H0. }
   
destruct H; [subst;  left; simpl in Hind; rewrite H in Hind; inversion Hind; trivial| ].
right. 
apply getIndirectionFstStep  in Hind; trivial; 
  [ | apply levelEqBEqNatFalse0 in H; assumption | lia  ].
destruct Hind as (pred &page1 & Hpnotnull & Hpred & Hpage & Hind).
apply in_flat_map.
exists page1.
split.
+ apply readPhyEntryInGetTablePages with  (StateLib.getIndexOfAddr va level1); trivial.
  - destruct (StateLib.getIndexOfAddr va level1). simpl. assumption.
  - assert ((StateLib.getIndexOfAddr va level1) = (CIndex (StateLib.getIndexOfAddr va level1))).
    symmetry. 
    apply indexEqId.
    rewrite <- H0. assumption.
+ assert (Hnbl : n0 <= nbLevel). lia.
  apply IHn0   with va pred (S stop - 1); trivial.
  - assert (levelEq level1 levelMin = false); trivial.
    apply levelPredMinus1 with level1 pred in H; [ | symmetry; assumption].
    subst.
    unfold CLevel.
    case_eq(lt_dec (level1 - 1) nbLevel); intros ll Hll; [ | destruct level1; simpl in *;
    assert (l< nbLevel) by lia; contradict Hll; lia]. 
    case_eq (lt_dec (n0 - 1) nbLevel); intros ll' Hll'; [ | lia].
    simpl.
    destruct level1.
    simpl in *.
    unfold CLevel in Hlevel.
    case_eq (lt_dec (n0 -0) nbLevel); intros l' Hl'; [ rewrite Hl' in *;simpl in *|]; lia.
  - apply levelEqBEqNatFalse0 in H.
    destruct n0; [ | lia]. 
    simpl in Hlevel.
    unfold CLevel in Hlevel.
    assert (0 < nbLevel) as Hll by apply nbLevelNotZero.
    case_eq (lt_dec 0 nbLevel); intros l' Hl';[     rewrite Hl' in *; simpl in *|]; lia.
Qed.

Lemma AllPagesAll :
forall p : page, In p getAllPages.
Proof.
intros.
unfold getAllPages.
apply in_map_iff.
exists p.
split.
unfold CPage.
case_eq (lt_dec p nbPage); intros.
destruct p.
simpl in *.
f_equal.
apply proof_irrelevance.
destruct p.
simpl in *. lia.
apply in_seq.
simpl.
assert (0 < nbPage). apply nbPageNotZero.
destruct p.
simpl.
lia.
Qed.
 

Lemma lengthNoDupPartitions : 
forall listPartitions : list page, NoDup listPartitions -> 
length listPartitions <= nbPage.
Proof.
intros.
assert (forall p : page, In p getAllPages) by apply AllPagesAll.
assert (length getAllPages <= nbPage).
unfold getAllPages.
rewrite map_length.
rewrite seq_length. trivial.
apply NoDup_incl_length with page listPartitions getAllPages in H.
lia.
unfold incl.
intros.
apply AllPagesAll.
Qed.

Lemma nextEntryIsPPgetParent partition pd s :
nextEntryIsPP partition idxParentDesc pd s <-> 
StateLib.getParent partition (memory s) = Some pd.
Proof.
split.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getParent in *.
destruct(StateLib.Index.succ idxParentDesc); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getParent in *.
destruct(StateLib.Index.succ idxParentDesc); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
Qed. 



Lemma nbPartition s:
noDupPartitionTree s -> 
length (getPartitions pageRootPartition s) < (nbPage+1).
Proof.
intros.
rewrite NPeano.Nat.add_1_r.
apply le_lt_n_Sm.
apply lengthNoDupPartitions.
trivial.
Qed. 

Lemma childrenPartitionInPartitionList s phyVA parent: 
noDupPartitionTree s -> 
In parent (getPartitions pageRootPartition s ) ->
In phyVA (getChildren parent s) -> 
In phyVA (getPartitions pageRootPartition s).
Proof.
intro Hnodup. 
unfold getPartitions .
assert
(length (getPartitions pageRootPartition s) < (nbPage+1)).
apply nbPartition;trivial.
unfold getPartitions in H.
revert H.
generalize pageRootPartition. 
induction (nbPage+1); simpl.
+ intros. now contradict H.
+ intros.
  simpl in *.
  destruct H0.
  - rewrite H0 in *.
    clear H0.
    right.   
    induction ((getChildren parent s)).
    * simpl. auto.
    * simpl in *.
      apply in_app_iff.
      destruct H1.
      subst.
      left.
      destruct n. lia.
      simpl.
      left. trivial.
      right. apply IHl.
      intros.
      apply IHn.
      lia.
      assumption.
      right.
      assumption.
      apply lt_n_S.
      apply lt_S_n in H.
      rewrite app_length in H.  
      lia.
      assumption.
  - right. 
    induction (getChildren p s); simpl in *.
    * now contradict H.
    * simpl in *.
      apply in_app_iff in H0.
      apply in_app_iff .
      destruct H0.
      left.
      apply IHn ; trivial.
      apply lt_S_n in H.
      rewrite app_length in H.
      lia.
      right.
      apply IHl; trivial.
      apply lt_n_S.
      apply lt_S_n in H.
      rewrite app_length in H.  
      lia.
Qed.

Lemma nbPageLL fstLL s:
NoDup(getLLPages fstLL s (nbPage + 1))  -> 
length (getLLPages fstLL s (nbPage + 1)) <(nbPage + 1).
Proof.
intros.
rewrite NPeano.Nat.add_1_r.
apply le_lt_n_Sm.
apply lengthNoDupPartitions.
replace (S nbPage) with (nbPage + 1) by lia.
trivial.
Qed. 


Lemma inGetLLPages   s:
forall fstLL LLChildphy lastLLTable,
NoDup(getLLPages fstLL s (nbPage + 1)) ->
In LLChildphy (getLLPages fstLL s (nbPage + 1)) ->
In lastLLTable (getLLPages LLChildphy s (nbPage + 1)) ->
In lastLLTable (getLLPages fstLL s (nbPage + 1)).
Proof.
intros fstLL LLChildphy lastLLTable Hi0 Hi1 Hi2 .
assert(Hi: length (getLLPages fstLL s (nbPage + 1)) <(nbPage + 1)) by (
apply nbPageLL;trivial).
revert dependent LLChildphy.
revert dependent lastLLTable . 
revert dependent fstLL.
induction (nbPage+1); simpl.
+ intros. now contradict Hi.
+ intros.
  simpl in *.
  case_eq(StateLib.getMaxIndex);[intros i Hmaxidx|intros Hmaxidx];rewrite Hmaxidx in *; simpl in *;trivial.
  case_eq(StateLib.readPhysical fstLL i (memory s));[intros sndLL HLL|intros HLL];rewrite HLL in *.
  - case_eq (StateLib.readPhysical LLChildphy i (memory s));
  [intros nextLLChildphy HLLChildphy|intros HLLChildphy];rewrite HLLChildphy in *.
  * case_eq(Nat.eqb nextLLChildphy pageDefault);intros Hnotdef;rewrite Hnotdef in *;  trivial;simpl in *; destruct Hi2 as [Hi2 | Hi2];subst;trivial;try 
    now contradict Hi2.
   case_eq(Nat.eqb sndLL pageDefault);intros Hnotdef1; rewrite Hnotdef1 in *;trivial;simpl in *.
   -- destruct Hi1 as [Hi1 | Hi1];subst.
   ++
   rewrite  HLLChildphy in HLL.
   inversion HLL;subst.
   contradict Hnotdef.
   rewrite Bool.not_false_iff_true;trivial.
   ++
   now contradict Hi1. 
   -- destruct Hi1 as [Hi1 |Hi1];subst.
   ** 
   rewrite  HLLChildphy in HLL.
   inversion HLL;subst. 
   right. trivial.
   **
   right.
   apply IHn with nextLLChildphy;trivial.
   apply NoDup_cons_iff in Hi0.
   intuition.
   lia.
   apply IHn with LLChildphy;trivial.
   apply NoDup_cons_iff in Hi0.
   intuition.

      lia.
   destruct n;simpl in *.
   now contradict Hi2.
   
    rewrite Hmaxidx in *.
   rewrite HLLChildphy in *.
   rewrite Hnotdef.
   simpl.
   clear IHn.
   case_eq(StateLib.readPhysical nextLLChildphy i (memory s) );[intros x Hi3 |intros Hi3];
   rewrite Hi3 in *.
   ***
   simpl in *.
   case_eq(StateLib.readPhysical sndLL i (memory s));[intros p Htrd | intros Htrd];rewrite Htrd in *.
   +++
   case_eq(Nat.eqb p pageDefault);intros Hi4;rewrite Hi4 in *.
   ---
   simpl in *.   
   destruct Hi1;subst;try now contradict H.   
   rewrite Htrd in HLLChildphy.
   inversion HLLChildphy.
   subst.
   contradict Hnotdef.
   rewrite Bool.not_false_iff_true;trivial.
   ---
   simpl in *.
   destruct Hi1;subst;try now contradict Hi1.
   ++++
     rewrite Htrd in HLLChildphy.
   inversion HLLChildphy.
   subst.
   right.
   destruct n;simpl in *.
   lia.
   rewrite Hmaxidx in *.
    rewrite Hi3.
    simpl.
    case_eq(Nat.eqb x pageDefault);intros Hx;rewrite Hx in *;
    simpl;left;trivial.
    ++++
    right.
   destruct n;simpl in *.
   lia.
   rewrite Hmaxidx in *.
    rewrite Hi3.
    simpl.
     case_eq(Nat.eqb x pageDefault);intros Hx;rewrite Hx in *;
    simpl;left;trivial.
    +++
    simpl in *.
   destruct Hi1;subst;try now contradict H.
   rewrite Htrd in HLLChildphy.
   now contradict HLLChildphy.
   *** 
   simpl in *.
   destruct Hi2 as [Hi2 | Hi2];subst;trivial;try now contradict Hi2.
   case_eq(StateLib.readPhysical sndLL i (memory s));[intros p Htrd | intros Htrd];rewrite Htrd in *.
   +++
   case_eq(Nat.eqb p pageDefault);intros Hi4;rewrite Hi4 in *.
   ---
   simpl in *.   
   destruct Hi1;subst;try now contradict H.   
   rewrite Htrd in HLLChildphy.
   inversion HLLChildphy.
   subst.
   contradict Hnotdef.
   rewrite Bool.not_false_iff_true;trivial.
   ---
   simpl in *.
   destruct Hi1;subst;try now contradict Hi1.
   ++++
     rewrite Htrd in HLLChildphy.
   inversion HLLChildphy.
   subst.
   right.
   destruct n;simpl in *.
   lia.
   rewrite Hmaxidx in *.
    rewrite Hi3.
    simpl.
    left;trivial.
    ++++
    right.
   destruct n;simpl in *.
   lia.
   rewrite Hmaxidx in *.
    rewrite Hi3.
    simpl.
    left;trivial.
    +++
    simpl in *.
   destruct Hi1;subst;try now contradict H.
   rewrite Htrd in HLLChildphy.
   now contradict HLLChildphy.
   
   * simpl in *.
    intuition;subst.
    destruct(Nat.eqb sndLL pageDefault);trivial;simpl in *.
  -
  case_eq (StateLib.readPhysical LLChildphy i (memory s));
  [intros nextLLChildphy HLLChildphy|intros HLLChildphy];rewrite HLLChildphy in *.
  * 
  destruct(Nat.eqb nextLLChildphy pageDefault);trivial;simpl in *; destruct Hi1;subst;trivial;try 
  now contradict Hi0.
   destruct Hi2;[left;trivial|].
   rewrite  HLLChildphy in HLL.
   now contradict HLL.
  *
  simpl in *.
  intuition;subst;trivial.
  left;trivial.
Qed.

Lemma verticalSharingRec n s :
NoDup (getPartitions pageRootPartition s) -> 
noCycleInPartitionTree s -> 
isParent s -> 
verticalSharing s -> 
forall currentPart, 
In currentPart (getPartitions pageRootPartition s) ->
forall   partition, currentPart<> partition -> 
In partition (getPartitionAux currentPart s (n + 1)) -> 
incl (getMappedPages partition s) (getMappedPages currentPart s).
Proof.
intros Hnodup Hnocycle Hisparent Hvs.
unfold incl.
induction n ; simpl ; intuition.

contradict H2.
clear.
induction (getChildren currentPart s); simpl; intuition.
rewrite in_flat_map in H2.
destruct H2 as (x & Hx1 & Hx2).
assert(Hor : partition = x \/ partition <> x) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
+ subst x. 
unfold verticalSharing in *.
unfold incl in *.
apply Hvs with partition;trivial.
unfold getUsedPages.
simpl. right.
apply in_app_iff. right;trivial.
+
apply IHn with x; trivial.
-
unfold isParent in *.
unfold noCycleInPartitionTree in *.
unfold not in Hnocycle.
apply Hnocycle.
apply childrenPartitionInPartitionList with currentPart; trivial. 
intuition.
unfold getAncestors.

assert(Hparent : StateLib.getParent x (memory s)  = Some currentPart).
apply Hisparent;trivial.
destruct nbPage; simpl; rewrite Hparent; simpl;left;trivial. 
- destruct n;simpl in *.
  * intuition.
    contradict H2.
    clear.
    induction (getChildren x s); simpl; intuition.
  *  destruct  Hx2; subst.
     now contradict Hor.
      right.
      rewrite in_flat_map.
      exists x;simpl;split;trivial.
      destruct n;simpl; left;trivial.  
-
apply IHn with partition; trivial.
apply childrenPartitionInPartitionList with currentPart; trivial. 
intuition. 
Qed.



   Lemma verticalSharingRec2 :
forall (n : nat) (s : state), NoDup (getPartitions pageRootPartition s) ->  noCycleInPartitionTree s ->
isParent s ->
verticalSharing s ->
forall currentPart : page,
In currentPart (getPartitions pageRootPartition s) ->
forall partition : page,
currentPart <> partition ->
In partition (getPartitionAux currentPart s (n + 1)) ->
incl (getUsedPages partition s) (getMappedPages currentPart s).
Proof. 
intros n s Hnodup Hnocycle Hisparent Hvs.
unfold incl.
induction n ; simpl.
+ intros.
 clear H2.  intuition.    

contradict H2.
clear.
induction (getChildren currentPart s); simpl; intuition.
+ intros.
destruct H1 . intuition.
assert (In a (getUsedPages partition s) ).
unfold getUsedPages. unfold getConfigPages.
simpl. trivial. clear H2.
rewrite in_flat_map in H1.
destruct H1 as (x & Hx1 & Hx2).
assert(Hor : partition = x \/ partition <> x) by apply pageDecOrNot.
destruct Hor as [Hor | Hor]. 
* subst x. 
unfold verticalSharing in *.
unfold incl in *.
apply Hvs with partition;trivial.
* 
apply IHn with x; trivial. 
-
unfold isParent in *.
unfold noCycleInPartitionTree in *.
apply Hnocycle.
apply childrenPartitionInPartitionList with currentPart; trivial.
unfold getAncestors.

assert(Hparent : StateLib.getParent x (memory s)  = Some currentPart).
apply Hisparent;trivial.
destruct nbPage; simpl; rewrite Hparent; simpl;left;trivial.
- destruct n;simpl in *.
  ** destruct Hx2. subst. now contradict Hor.    contradict H1.
    induction (getChildren x s); simpl; intuition.
  **  destruct  Hx2; subst.
     now contradict Hor.
      right.
      rewrite in_flat_map.
      exists x;simpl;split;trivial.
      destruct n;simpl; left;trivial.  
- unfold getUsedPages. rewrite in_app_iff.
right. 
apply IHn with partition; trivial.
apply childrenPartitionInPartitionList with currentPart; trivial. 
intuition. 
Qed.
(*
 assert( incl (getMappedPages currentPart s) (getMappedPages child1 s)). *)
           Lemma toApplyVerticalSharingRec s:
           consistency s ->  
           verticalSharing s -> 
           forall currentPart child1 closestAnc,
           currentPart <> child1 -> 
            In child1 (getChildren closestAnc s) -> 
            In closestAnc (getPartitions pageRootPartition s) -> 
             In currentPart (getPartitionAux child1 s nbPage) -> 
            incl (getMappedPages currentPart s) (getMappedPages child1 s).
            Proof. intros Hcons Hvs. intros.
            unfold consistency in *. 
           apply verticalSharingRec with (nbPage-1); intuition.
           apply childrenPartitionInPartitionList with closestAnc; trivial.
           destruct nbPage.
           simpl in *. intuition.
           simpl.
           replace    (n - 0 + 1) with (S n) by lia.
           trivial.
           Qed.          

  Lemma verticalSharing2 child parent s :
  incl (getUsedPages child s) (getMappedPages parent s) -> 
  incl (getMappedPages child s) (getMappedPages parent s).
  Proof.
  unfold incl.
  intros.
  apply H.
  unfold getUsedPages.
  apply in_app_iff.
  right;trivial.
  Qed.
 
Lemma getPartitionAuxMinus1 s : 
NoDup (getPartitions pageRootPartition s) -> 
isParent s -> 
forall n child parent ancestor, 
In ancestor (getPartitions pageRootPartition s) ->
StateLib.getParent child (memory s) = Some parent ->  
In child (flat_map (fun p : page => getPartitionAux p s n) (getChildren ancestor s)) -> 
In parent (getPartitionAux ancestor s n).
Proof.
intros Hnodup Hparent .
induction n. simpl in *. intuition.
contradict H1.
clear. induction  (getChildren ancestor s);simpl in *;intuition.
simpl.
intros.
rewrite in_flat_map in H1.
destruct H1 as (x & Hx & Hxx).
simpl in Hxx.
assert(Hor : parent = ancestor \/ parent <> ancestor) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
left;intuition.
right.
destruct Hxx as [Hx1 | Hx1].
+ subst.
rewrite in_flat_map. 
assert(StateLib.getParent child (memory s) = Some ancestor).
unfold isParent in *.
apply Hparent;trivial.
rewrite H1 in H0.
inversion H0; subst. now contradict Hor.
+ rewrite  in_flat_map.
exists x;split;trivial.
simpl.
apply IHn with child;trivial.
apply childrenPartitionInPartitionList with ancestor;trivial.

Qed. 



Lemma isAncestorTrans2 ancestor descParent currentPart s:
noDupPartitionTree s ->
multiplexerWithoutParent s -> 
isParent s -> 
In currentPart (getPartitions pageRootPartition s)  -> 
StateLib.getParent descParent (memory s) = Some ancestor -> 
In descParent (getAncestors currentPart s) -> 
In ancestor (getAncestors currentPart s).
Proof.
intros Hnoduptree Hmultnone Hisparent.
revert descParent ancestor currentPart.
unfold getPartitions.
unfold getAncestors.
(* assert(Hge : nbPage >= nbPage) by lia.
revert Hge.
generalize nbPage at 1 3 4 . *)
induction nbPage ;intros descParent ancestor currentPart Hmult;intros;simpl in *.
destruct Hmult.
subst.
assert( StateLib.getParent pageRootPartition (memory s)  = None) by intuition.
rewrite H1 in H0. now contradict H0.
contradict H1.
clear.
induction   (getChildren pageRootPartition s);simpl in *; intuition.
destruct Hmult as [Hmult | Hmult].
+ subst. assert( StateLib.getParent pageRootPartition (memory s)  = None) by intuition.
rewrite H1 in *. now contradict H0.
+ 
case_eq(StateLib.getParent currentPart (memory s) );
[intros parent Hparent | intros Hparent ].
rewrite Hparent in H0.
simpl in *.
assert(Hi :parent = ancestor \/ parent <> ancestor ).
{ destruct parent;simpl in *;subst;destruct ancestor;simpl in *;subst.
  assert (Heq :p=p0 \/ p<> p0) by lia.
    destruct Heq as [Heq|Heq].
    subst.
    left;f_equal;apply proof_irrelevance.
    right. unfold not;intros.
    inversion H1.
    subst.
    now contradict Heq. }    
destruct Hi as [Hi | Hi].
left;trivial.
destruct H0;subst.
right.
destruct n.
simpl.
rewrite H.
simpl;left;trivial.
simpl.
rewrite H.
simpl;left;trivial.
right.
apply IHn with descParent;trivial.
apply getPartitionAuxMinus1 with currentPart;trivial.
unfold getPartitions. destruct nbPage;simpl;left;trivial.
rewrite Hparent in H0.
intuition. 
Qed.

Lemma getAncestorsProp1 s :
partitionDescriptorEntry s -> 
parentInPartitionList s -> 
forall ancestor parent child ,
In parent (getPartitions pageRootPartition s) -> 
In ancestor (getAncestors child s) -> 
parent <> ancestor -> 
StateLib.getParent child (memory s) = Some parent -> 
In ancestor (getAncestors parent s).
Proof.
intros Hpde Hparentpart. 
unfold getAncestors.
induction (nbPage + 1); intros ancestor parent child  Hin Hinanc Hnoteq Hparent;
simpl in *; trivial.
rewrite Hparent in Hinanc.
simpl in *.
destruct Hinanc.
intuition. 
case_eq (StateLib.getParent parent (memory s) ); intros.
simpl in *.
assert( Hor : p=ancestor \/ p<> ancestor) by apply pageDecOrNot.
destruct Hor. 
left;trivial.
right.
apply IHn with parent; trivial.
clear IHn.
unfold parentInPartitionList in *.
apply Hparentpart with parent; trivial.
apply nextEntryIsPPgetParent; trivial.
unfold partitionDescriptorEntry in *.
assert((exists entry : page, nextEntryIsPP parent idxParentDesc entry s /\ entry <> pageDefault)).
apply Hpde;trivial.
do 4 right; left;trivial.
destruct H1 as (parennt & H1 & H2).
rewrite nextEntryIsPPgetParent in *.
rewrite H1 in *.
now contradict H0.
Qed.

Lemma isAncestorTrans3 s :
noDupPartitionTree s ->
multiplexerWithoutParent s -> 
noCycleInPartitionTree s -> 
isParent s -> 
isChild s -> 
parentInPartitionList s -> 
forall ancestor child x,
In x (getPartitions pageRootPartition s) -> 
In child (getPartitions pageRootPartition s) -> 
In ancestor (getPartitions pageRootPartition s) -> 
In ancestor (getAncestors child s) ->
In x (getChildren child s) -> 

In ancestor (getAncestors x s).
Proof.
intros Ha1 Ha2 Hnocycle Hisparent Hischild Hparentintree.
unfold getPartitions at 1, getAncestors.
induction (nbPage+1);simpl; intros;trivial.
destruct H;subst.
assert(Hfalse :  StateLib.getParent pageRootPartition (memory s) = Some child).
unfold isParent in *.
apply Hisparent;trivial.
assert(Htrue :  StateLib.getParent pageRootPartition (memory s) = None) by intuition.
rewrite Htrue in Hfalse. now contradict Hfalse.
assert(Hparentx : StateLib.getParent x (memory s)  = Some child). 
unfold isParent in *.
apply Hisparent;trivial.
rewrite Hparentx;trivial.
case_eq(StateLib.getParent child (memory s));
[intros parent Hparentchild | intros Hparentchild];rewrite Hparentchild in *;
try now contradict H2.
simpl in *.
destruct H2;subst.
+ right.
  destruct n; simpl in *.
  contradict H.     
  induction ((getChildren pageRootPartition s));simpl in *;intuition.
  rewrite Hparentchild.
  simpl ;trivial;left;trivial.
+ 
  
simpl;right.
apply IHn with parent;trivial.
apply getPartitionAuxMinus1 with x;trivial.
unfold getPartitions.
destruct nbPage;simpl;left;trivial.
unfold parentInPartitionList in *.
apply Hparentintree with child;trivial.
apply nextEntryIsPPgetParent;trivial.
unfold isChild in *.
apply Hischild;trivial. 
Qed. (* isAncestorTrans3 : multiplexer without parent *)


Lemma noCycleInPartitionTree2 s :
noDupPartitionTree s -> 
multiplexerWithoutParent s -> 
isChild s ->
parentInPartitionList s ->
noCycleInPartitionTree s -> 
isParent s -> 
forall n parent child,
In parent (getPartitions pageRootPartition s) ->  
In child (getChildren parent s) -> 
~ In parent (getPartitionAux child s n).
Proof.
(* unfold noCycleInPartitionTree. *)
intros Hnoduptree Hmultnone Ha Ha2 Hnocycle Hisparent.
intros.
assert(In parent (getAncestors child s) ).
{ unfold getAncestors. 
  assert(Htrue: StateLib.getParent child (memory s) =Some parent).
  unfold isParent in *.
  apply Hisparent;trivial.
  destruct nbPage;simpl; rewrite Htrue;simpl;left;trivial. }
assert(Hchildintree : In child (getPartitions pageRootPartition s)).
apply childrenPartitionInPartitionList with parent;trivial.
clear H0. 
revert dependent parent.
revert dependent child.
induction n. simpl. intuition.
simpl.  
intros child Hchild parent Hparent  Hances.
apply Classical_Prop.and_not_or.
split.
+ unfold not;intros. subst. 
assert(Hfaalse : parent <> parent).
unfold noCycleInPartitionTree in *.
apply Hnocycle;trivial.
now contradict Hfaalse.
+ unfold not;intros Hcont.
rewrite in_flat_map in Hcont.
destruct Hcont as (x & Hx & Hx1).
contradict Hx1.
assert(Htrue : In x (getPartitions pageRootPartition s)). 
apply childrenPartitionInPartitionList with child;trivial.
 apply IHn;trivial.
 apply isAncestorTrans3 with child;trivial.
Qed.

Lemma accessiblePageIsNotPartitionDescriptor
phyPDChild pdChild idxPDChild accessiblePDChild currentPart nbL presentPDChild 
currentPD (ptPDChild : page) s:
partitionsIsolation s ->  
kernelDataIsolation s -> 
 (Nat.eqb pageDefault ptPDChild ) = false ->
accessiblePDChild = true -> 
presentPDChild = true -> 
StateLib.getIndexOfAddr pdChild levelMin = idxPDChild -> 
nextEntryIsPP currentPart idxPageDir currentPD s -> 
Some nbL = StateLib.getNbLevel -> 
(forall idx : index,
        StateLib.getIndexOfAddr pdChild levelMin = idx ->
        isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild idxPageDir currentPart pdChild s) -> 
entryPresentFlag ptPDChild idxPDChild presentPDChild s -> 
entryUserFlag ptPDChild idxPDChild accessiblePDChild s -> 
isEntryPage ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) phyPDChild s -> 
In currentPart (getPartitions pageRootPartition s) -> 
~ In phyPDChild (getPartitionAux pageRootPartition s (nbPage + 1)).
Proof.
intros Hiso Hanc Hnotnull Haccess Hpresentflag Hidx Hroot Hnbl
Histblroot Hpresent Haccessentry Hentry Hcons. 
assert (In phyPDChild (getAccessibleMappedPages currentPart s)) by
  now apply physicalPageIsAccessible with ptPDChild pdChild idxPDChild accessiblePDChild
          nbL presentPDChild currentPD.
  unfold kernelDataIsolation in Hanc.
unfold disjoint in Hanc.
unfold getConfigPages in Hanc.
unfold getConfigPagesAux in Hanc.
simpl in Hanc.
generalize (Hanc currentPart pageRootPartition) ;  intro Hanc1.
assert( Hp2 : In pageRootPartition (getPartitions pageRootPartition s)).
{ unfold getPartitions. destruct nbPage;
  simpl; left; trivial. }
assert( Hpcur : In currentPart (getPartitions pageRootPartition s) ) by trivial.
apply Hanc1  with phyPDChild in Hcons; trivial.
apply Classical_Prop.not_or_and in Hcons.
destruct Hcons as (Hp1 & _).
clear Hanc1 Hp2.
assert(Hanc' : forall partition2  : page,
In partition2 (getPartitions pageRootPartition s) ->
partition2 <> phyPDChild).
{ intros.
  apply Hanc with currentPart partition2 phyPDChild in H0;trivial.
  apply Classical_Prop.not_or_and in H0.
  intuition. }
clear Hanc .
unfold not in *.
intros.
apply Hanc' with phyPDChild; trivial. 
Qed.

Lemma getPdNextEntryIsPPEq partition pd1 pd2 s :
nextEntryIsPP partition idxPageDir pd1 s -> 
StateLib.getPd partition (memory s) = Some pd2 -> 
pd1 = pd2.
Proof.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getPd in *.
destruct(StateLib.Index.succ idxPageDir); [| now contradict H0].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H0].
destruct v ; try now contradict H0.
inversion H0; subst; trivial.
Qed. 

Lemma getSh1NextEntryIsPPEq partition pd1 pd2 s :
nextEntryIsPP partition idxShadow1 pd1 s -> 
StateLib.getFstShadow partition (memory s) = Some pd2 -> 
pd1 = pd2.
Proof.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getFstShadow in *.
destruct(StateLib.Index.succ idxShadow1); [| now contradict H0].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H0].
destruct v ; try now contradict H0.
inversion H0; subst; trivial.
Qed.
 
Lemma getSh2NextEntryIsPPEq partition pd1 pd2 s :
nextEntryIsPP partition idxShadow2 pd1 s -> 
StateLib.getSndShadow partition (memory s) = Some pd2 -> 
pd1 = pd2.
Proof.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getSndShadow in *.
destruct(StateLib.Index.succ idxShadow2); [| now contradict H0].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H0].
destruct v ; try now contradict H0.
inversion H0; subst; trivial.
Qed. 

Lemma getListNextEntryIsPPEq partition pd1 pd2 s :
nextEntryIsPP partition idxShadow3 pd1 s -> 
StateLib.getConfigTablesLinkedList partition (memory s) = Some pd2 -> 
pd1 = pd2.
Proof.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getConfigTablesLinkedList in *.
destruct(StateLib.Index.succ idxShadow3); [| now contradict H0].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H0].
destruct v ; try now contradict H0.
inversion H0; subst; trivial.
Qed.

Lemma getParentNextEntryIsPPEq partition pd1 pd2 s :
nextEntryIsPP partition idxParentDesc pd1 s -> 
StateLib.getParent partition (memory s) = Some pd2 -> 
pd1 = pd2.
Proof.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getParent in *.
destruct(StateLib.Index.succ idxParentDesc); [| now contradict H0].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H0].
destruct v ; try now contradict H0.
inversion H0; subst; trivial.
Qed.



Lemma nextEntryIsPPgetPd partition pd s :
nextEntryIsPP partition idxPageDir pd s <-> 
StateLib.getPd partition (memory s) = Some pd.
Proof.
split.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getPd in *.
destruct(StateLib.Index.succ idxPageDir); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getPd in *.
destruct(StateLib.Index.succ idxPageDir); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
Qed. 

Lemma nextEntryIsPPgetFstShadow partition sh1 s :
nextEntryIsPP partition idxShadow1 sh1 s <-> 
StateLib.getFstShadow partition (memory s) = Some sh1.
Proof.
split.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getFstShadow in *.
destruct(StateLib.Index.succ idxShadow1); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getFstShadow in *.
destruct(StateLib.Index.succ idxShadow1); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
Qed. 

Lemma nextEntryIsPPgetSndShadow partition sh2 s :
nextEntryIsPP partition idxShadow2 sh2 s <-> 
StateLib.getSndShadow partition (memory s) = Some sh2.
Proof.
split.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getSndShadow in *.
destruct(StateLib.Index.succ idxShadow2); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getSndShadow in *.
destruct(StateLib.Index.succ idxShadow2); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
Qed. 

Lemma nextEntryIsPPgetConfigList partition list s :
nextEntryIsPP partition idxShadow3 list s -> 
StateLib.getConfigTablesLinkedList partition (memory s) = Some list.
Proof.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getConfigTablesLinkedList in *.
destruct(StateLib.Index.succ idxShadow3); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
Qed. 


Lemma accessibleMappedPagesInMappedPages partition s : 
incl (getAccessibleMappedPages partition s) (getMappedPages partition s). 
Proof.
unfold incl.
intros apage Haccesible.
unfold getMappedPages.
unfold getAccessibleMappedPages in *.
destruct (StateLib.getPd partition (memory s)); trivial.
unfold getMappedPagesAux.
unfold getAccessibleMappedPagesAux in *. 
apply filterOptionInIff.
apply filterOptionInIff in Haccesible.
 unfold getAccessibleMappedPagesOption in *.
unfold getMappedPagesOption.
apply in_map_iff.
apply in_map_iff in Haccesible.
destruct Haccesible as (va & Haccesible & Hvas).
exists va.
split; trivial.
unfold  getAccessibleMappedPage in *.
unfold getMappedPage.
destruct (StateLib.getNbLevel); trivial.
destruct ( getIndirection p va l (nbLevel - 1) s);trivial.
destruct (StateLib.readPresent p0 
          (StateLib.getIndexOfAddr va levelMin) (memory s));trivial.
destruct b; trivial.
destruct (Nat.eqb pageDefault p0); try now contradict Haccesible.
destruct (StateLib.readAccessible p0 
(StateLib.getIndexOfAddr va levelMin) (memory s)); 
[|now contradict Haccesible].
destruct b; trivial.
now contradict Haccesible.
destruct (Nat.eqb pageDefault p0);intros;trivial.
now contradict Haccesible.
Qed.


Lemma inGetIndirectionsAuxLt pd s stop table bound: 
~ In table (getIndirectionsAux pd s bound) -> 
stop <= bound - 1 -> 
~ In table (getIndirectionsAux pd s  stop).
Proof.
revert stop pd.
induction bound.
simpl in *; auto.
intros.
destruct stop.
simpl. auto.
now contradict H0.
intros.
destruct stop.
simpl. auto.
simpl in *.
apply Classical_Prop.and_not_or .
apply Classical_Prop.not_or_and in H.
destruct H.
split; trivial.
auto.
simpl in *.

induction  (getTablePages pd tableSize s).
simpl. auto.
simpl in *.
rewrite in_app_iff in *.
apply Classical_Prop.and_not_or .
apply Classical_Prop.not_or_and in H1.
destruct H1.
split; trivial.
apply IHbound; trivial.
lia.
apply IHl; trivial.   
Qed.


Lemma notConfigTableNotPdconfigTableLt partition pd table s stop : 
stop < nbLevel - 1 -> 
partitionDescriptorEntry s -> 
In partition (getPartitions pageRootPartition s) -> 
~ In table (getConfigPagesAux partition s) -> 
StateLib.getPd partition (memory s) = Some pd -> 
~ In table (getIndirectionsAux pd s (S stop)).
Proof.
intros Hstop Hpde Hgetparts Hconfig Hpd .

unfold getConfigPagesAux in *.
rewrite Hpd in Hconfig.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow1 in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getFstShadow in *.
destruct (StateLib.Index.succ idxShadow1); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow2 in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getSndShadow in *.
destruct (StateLib.Index.succ idxShadow2); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition idxShadow3 in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ idxShadow3); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
simpl in Hconfig.
(* apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig. *)
rewrite in_app_iff in Hconfig.
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig.
unfold getIndirections in H.

apply inGetIndirectionsAuxLt with nbLevel; auto.
Qed.
Lemma inGetIndirectionsAuxInConfigPagesPD partition pd table s:
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
In table (getIndirectionsAux pd s nbLevel)->
StateLib.getPd partition (memory s) = Some pd -> 
In table (getConfigPagesAux partition s).
Proof. 
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow1 in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getFstShadow in *.
destruct (StateLib.Index.succ idxShadow1); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow2 in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getSndShadow in *.
destruct (StateLib.Index.succ idxShadow2); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition idxShadow3 in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ idxShadow3); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
unfold getIndirections.
simpl .
(* apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig. *)
rewrite in_app_iff .
left;trivial.
Qed.

Lemma notConfigTableNotPdconfigTable partition pd table s : 
partitionDescriptorEntry s -> 
In partition (getPartitions pageRootPartition s) -> 
~ In table (getConfigPagesAux partition s) -> 
StateLib.getPd partition (memory s) = Some pd -> 
~ In table (getIndirectionsAux pd s nbLevel).
Proof.
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd in Hconfig.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow1 in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getFstShadow in *.
destruct (StateLib.Index.succ idxShadow1); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow2 in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getSndShadow in *.
destruct (StateLib.Index.succ idxShadow2); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition idxShadow3 in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ idxShadow3); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
simpl in Hconfig.
(* apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig. *)
rewrite in_app_iff in Hconfig.
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig as (H0 & H).
unfold getIndirections in H0.
assumption.
Qed.

Lemma notConfigTableNotSh1configTableLt partition sh1 table s stop : 
stop < nbLevel - 1 -> 
partitionDescriptorEntry s -> 
In partition (getPartitions pageRootPartition s) -> 
~ In table (getConfigPagesAux partition s) -> 
StateLib.getFstShadow partition (memory s) = Some sh1 -> 
~ In table (getIndirectionsAux sh1 s (S stop)).
Proof.
intros Hstop Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd in Hconfig.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxPageDir in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ idxPageDir); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow2 in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getSndShadow in *.
destruct (StateLib.Index.succ idxShadow2); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition idxShadow3 in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ idxShadow3); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
simpl in Hconfig.
rewrite in_app_iff in Hconfig.
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig as (H & H0). (* 

apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig. *)
rewrite in_app_iff in H0. 
apply Classical_Prop.not_or_and in H0.
destruct H0.
unfold getIndirections in H0.
simpl in H1. (*  
apply Classical_Prop.not_or_and in H1.
destruct H1.
rewrite in_app_iff in H2.
apply Classical_Prop.not_or_and in H2.
destruct H2. *)
unfold getIndirections in H0.
apply inGetIndirectionsAuxLt with nbLevel; auto.
Qed.

Lemma inGetIndirectionsAuxInConfigPagesSh1 partition pd table s:
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
In table (getIndirectionsAux pd s nbLevel)->
StateLib.getFstShadow partition (memory s) = Some pd -> 
In table (getConfigPagesAux partition s).
Proof. 
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd .
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxPageDir in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ idxPageDir); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow2 in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getSndShadow in *.
destruct (StateLib.Index.succ idxShadow2); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition idxShadow3 in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ idxShadow3); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
simpl in Hconfig.
rewrite in_app_iff .
right.
rewrite in_app_iff .
left;trivial.
Qed. 
Lemma notConfigTableNotSh1configTable partition sh1 table s : 
partitionDescriptorEntry s -> 
In partition (getPartitions pageRootPartition s) -> 
~ In table (getConfigPagesAux partition s) -> 
StateLib.getFstShadow partition (memory s) = Some sh1 -> 
~ In table (getIndirectionsAux sh1 s nbLevel).
Proof.
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd in Hconfig.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxPageDir in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ idxPageDir); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow2 in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getSndShadow in *.
destruct (StateLib.Index.succ idxShadow2); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition idxShadow3 in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ idxShadow3); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
simpl in Hconfig.
rewrite in_app_iff in Hconfig.
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig.
simpl in H0. (* 
apply Classical_Prop.not_or_and in H1.
destruct H1. *)
rewrite in_app_iff in H0.
apply Classical_Prop.not_or_and in H0.
destruct H0.
rewrite in_app_iff in H1.
apply Classical_Prop.not_or_and in H1.
destruct H1.
unfold getIndirections in H2.
assumption.
Qed.

Lemma notConfigTableNotSh2configTableLt partition sh2 table s stop : 
stop < nbLevel - 1 -> 
partitionDescriptorEntry s -> 
In partition (getPartitions pageRootPartition s) -> 
~ In table (getConfigPagesAux partition s) -> 
StateLib.getSndShadow partition (memory s) = Some sh2 -> 
~ In table (getIndirectionsAux sh2 s (S stop)).
Proof.
intros Hstop Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd in Hconfig.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxPageDir in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ idxPageDir); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow1 in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getFstShadow in *.
destruct (StateLib.Index.succ idxShadow1); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition idxShadow3 in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ idxShadow3); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
simpl in Hconfig.
rename Hconfig into H0. (* 
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig. *)
rewrite in_app_iff in H0.
apply Classical_Prop.not_or_and in H0.
destruct H0.
unfold getIndirections in H0.
rewrite in_app_iff in H0.
apply Classical_Prop.not_or_and in H0.
destruct H0.
rewrite in_app_iff in H1.
simpl in H1. 
apply Classical_Prop.not_or_and in H1.
destruct H1. (* 
rewrite in_app_iff in H2.
apply Classical_Prop.not_or_and in H2.
destruct H2.
unfold getIndirections in H2.
simpl in H3.
apply Classical_Prop.not_or_and in H3.
destruct H3.
rewrite in_app_iff in H4.
apply Classical_Prop.not_or_and in H4.
destruct H4.
unfold getIndirections in H4.
simpl in H5. 
apply Classical_Prop.not_or_and in H5.
destruct H5. *)
apply inGetIndirectionsAuxLt with nbLevel; auto.
Qed.

Lemma inGetIndirectionsAuxInConfigPagesSh2 partition pd table s:
partitionDescriptorEntry s ->
In partition (getPartitions pageRootPartition s) ->
In table (getIndirectionsAux pd s nbLevel)->
StateLib.getSndShadow partition (memory s) = Some pd -> 
In table (getConfigPagesAux partition s).
Proof.
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxPageDir in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ idxPageDir); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow1 in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getFstShadow in *.
destruct (StateLib.Index.succ idxShadow1); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition idxShadow3 in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ idxShadow3); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
simpl in Hconfig.
rename Hconfig into H0. (* 
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig. *)
do 2 (rewrite in_app_iff;
right). 
rewrite in_app_iff.
left.
trivial.
Qed.

Lemma notConfigTableNotSh2configTable partition sh2 table s : 
partitionDescriptorEntry s -> 
In partition (getPartitions pageRootPartition s) -> 
~ In table (getConfigPagesAux partition s) -> 
StateLib.getSndShadow partition (memory s) = Some sh2 -> 
~ In table (getIndirectionsAux sh2 s nbLevel).
Proof.
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd in Hconfig.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxPageDir in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ idxPageDir); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow1 in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getFstShadow in *.
destruct (StateLib.Index.succ idxShadow1); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition idxShadow3 in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ idxShadow3); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) pageEq idxEq);auto.
destruct v; auto.
subst.
simpl in Hconfig.
rename Hconfig into H0. (* 
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig. *)
rewrite in_app_iff in H0.
apply Classical_Prop.not_or_and in H0.
destruct H0.
unfold getIndirections in H0.
rewrite in_app_iff in H0.
apply Classical_Prop.not_or_and in H0.
destruct H0.
rewrite in_app_iff in H1.
simpl in H1. 
apply Classical_Prop.not_or_and in H1.
destruct H1.
assumption.
Qed.



Lemma notConfigTableNotListconfigTable partition sh3 table s : 
partitionDescriptorEntry s -> 
In partition (getPartitions pageRootPartition s) -> 
~ In table (getConfigPagesAux partition s) -> 
StateLib.getConfigTablesLinkedList partition (memory s) = Some sh3 -> 
~ In table (getLLPages sh3 s (nbPage + 1)).
Proof.
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd in Hconfig.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxPageDir in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
rewrite nextEntryIsPPgetPd in *. 
rewrite Hpp in *.
clear Hrootidx Hisva  Hnotnull Hpp.
assert(Hgetpartslist :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow1 in Hgetpartslist;auto.
destruct Hgetpartslist as (Hrootidx & Hisva & sh1  & Hpp & Hnotnull).
rewrite nextEntryIsPPgetFstShadow in *. 
rewrite Hpp in *.
clear Hrootidx Hisva  Hnotnull Hpp.
assert(Hgetpartslist :In partition (getPartitions pageRootPartition s)) ; trivial.
apply Hpde with partition idxShadow2 in Hgetpartslist;auto.
destruct Hgetpartslist as (Hrootidx & Hisva & sh2  & Hpp & Hnotnull).
rewrite nextEntryIsPPgetSndShadow in *. 
rewrite Hpp in *.
simpl in Hconfig.
rename Hconfig into H0.
rewrite in_app_iff in H0.
apply Classical_Prop.not_or_and in H0.
destruct H0.
unfold getIndirections in H0.
rewrite in_app_iff in H0.
apply Classical_Prop.not_or_and in H0.
destruct H0.
rewrite in_app_iff in H1.
simpl in H1. 
apply Classical_Prop.not_or_and in H1.
destruct H1.
assumption.
Qed.

      
Lemma pdSh1Sh2ListExistsNotNull  (s: state): 
partitionDescriptorEntry s -> 
forall partition, In partition (getPartitions pageRootPartition s) -> 
(exists pd , StateLib.getPd partition (memory s) = Some pd /\ pd <> pageDefault) /\ 
(exists sh1, StateLib.getFstShadow partition (memory s) = Some sh1 /\ sh1 <> pageDefault) /\ 
(exists sh2, StateLib.getSndShadow partition (memory s) = Some sh2 /\ sh2 <> pageDefault) /\ 
(exists list, StateLib.getConfigTablesLinkedList partition (memory s) = Some list /\ list <> pageDefault).
Proof.
intros; unfold partitionDescriptorEntry in *.
repeat split.
+ apply H with partition idxPageDir in H0 .
  destruct H0 as (Hi & Hva & entry & Hentry & Hnotdef).
  exists entry.
  split; trivial.
  apply nextEntryIsPPgetPd; trivial.
  left. trivial.
+ apply H with partition idxShadow1 in H0 .
  destruct H0 as (Hi & Hva & entry & Hentry & Hnotdef).
  exists entry.
  split;trivial.
  apply nextEntryIsPPgetFstShadow; trivial.
  right;  left. trivial.
+ apply H with partition idxShadow2 in H0 .
  destruct H0 as (Hi & Hva & entry & Hentry & Hnotdef).
  exists entry.
  split; trivial.
  apply nextEntryIsPPgetSndShadow; trivial.
  right; right; left. trivial.
+ apply H with partition idxShadow3 in H0 .
  destruct H0 as (Hi & Hva & entry & Hentry & Hnotdef).
  exists entry.
  split;trivial.
  apply nextEntryIsPPgetConfigList ; trivial.
  right; right; right; left. trivial.
Qed.

Lemma isConfigTable descChild ptRefChild descParent s :
partitionDescriptorEntry s -> 
In descParent (getPartitions pageRootPartition s) -> 
(forall idx : index,
StateLib.getIndexOfAddr descChild levelMin = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild idxPageDir descParent descChild s) -> 
(Nat.eqb pageDefault ptRefChild) = false -> 
In ptRefChild (getConfigPages descParent s).
Proof.
intros Hpde Hpart Hget Hnotnull.
apply pdSh1Sh2ListExistsNotNull  with s descParent in Hpde.
destruct Hpde as ((pd & Hpd & Hpdnotnull) 
  & (sh1 & Hsh1 & Hsh1notnull) & (sh2 & Hsh2 & Hsh2notnull) & 
  (sh3 & Hsh3 & Hsh3notnull)).
unfold getConfigPages.
unfold getConfigPagesAux.
rewrite Hpd, Hsh1, Hsh2, Hsh3.
simpl.
do 1 right.
rewrite in_app_iff.
left.
unfold getIndirections.
destruct Hget with (StateLib.getIndexOfAddr descChild levelMin) ;trivial.
clear Hget.
unfold getTableAddrRoot in *.
destruct H0 as(_ & H0).
rewrite <- nextEntryIsPPgetPd in *.
apply H0 in Hpd.
clear H0.
destruct Hpd as (nbL & HnbL & stop & Hstop & Hind).
apply getIndirectionInGetIndirections with descChild nbL stop;trivial.
assert(0<nbLevel) by apply nbLevelNotZero;trivial.
apply beq_nat_false in Hnotnull.
unfold not;intros.
subst.
now contradict Hnotnull.
apply getNbLevelLe in HnbL;trivial.
assumption. 
Qed.

Lemma isConfigTableSh2WithVA descChild ptRefChild descParent s :
partitionDescriptorEntry s -> 
In descParent (getPartitions pageRootPartition s) -> 
(forall idx : index,
StateLib.getIndexOfAddr descChild levelMin = idx ->
isVA ptRefChild idx s /\ getTableAddrRoot ptRefChild idxShadow2 descParent descChild s) -> 
(Nat.eqb pageDefault ptRefChild) = false -> 
In ptRefChild (getConfigPages descParent s).
Proof.
intros Hpde Hpart Hget Hnotnull.
apply pdSh1Sh2ListExistsNotNull  with s descParent in Hpde.
destruct Hpde as ((pd & Hpd & Hpdnotnull) 
  & (sh1 & Hsh1 & Hsh1notnull) & (sh2 & Hsh2 & Hsh2notnull) & 
  (sh3 & Hsh3 & Hsh3notnull)).
unfold getConfigPages.
unfold getConfigPagesAux.
rewrite Hpd, Hsh1, Hsh2, Hsh3.
simpl.
right.
do 2 (rewrite in_app_iff;
right).
 rewrite in_app_iff.
left.
unfold getIndirections.
destruct Hget with (StateLib.getIndexOfAddr descChild levelMin) ;trivial.
clear Hget.
unfold getTableAddrRoot in *.
destruct H0 as(_ & H0).
rewrite <- nextEntryIsPPgetSndShadow in *.
apply H0 in Hsh2.
clear H0.
destruct Hsh2 as (nbL & HnbL & stop & Hstop & Hind).
apply getIndirectionInGetIndirections with descChild nbL stop;trivial.
assert(0<nbLevel) by apply nbLevelNotZero;trivial.
apply beq_nat_false in Hnotnull.
unfold not;intros.
subst.
now contradict Hnotnull.
apply getNbLevelLe in HnbL;trivial.
assumption. 
Qed.

Lemma isConfigTableSh2 descChild ptRefChild descParent s :
partitionDescriptorEntry s -> 
In descParent (getPartitions pageRootPartition s) -> 
getTableAddrRoot ptRefChild idxShadow2 descParent descChild s -> 
(Nat.eqb pageDefault ptRefChild) = false -> 
In ptRefChild (getConfigPages descParent s).
Proof.
intros Hpde Hpart Hget Hnotnull.
apply pdSh1Sh2ListExistsNotNull  with s descParent in Hpde;trivial.
destruct Hpde as ((pd & Hpd & Hpdnotnull) 
  & (sh1 & Hsh1 & Hsh1notnull) & (sh2 & Hsh2 & Hsh2notnull) & 
  (sh3 & Hsh3 & Hsh3notnull)).
unfold getConfigPages.
unfold getConfigPagesAux.
rewrite Hpd, Hsh1, Hsh2, Hsh3.
simpl.
right.
do 2 (rewrite in_app_iff;
right).
 rewrite in_app_iff.
left.
unfold getIndirections.
unfold getTableAddrRoot in *.
destruct Hget as(_ & H0).
rewrite <- nextEntryIsPPgetSndShadow in *.
apply H0 in Hsh2.
clear H0.
destruct Hsh2 as (nbL & HnbL & stop & Hstop & Hind).
apply getIndirectionInGetIndirections with descChild nbL stop;trivial.
assert(0<nbLevel) by apply nbLevelNotZero;trivial.
apply beq_nat_false in Hnotnull.
unfold not;intros.
subst.
now contradict Hnotnull.
apply getNbLevelLe in HnbL;trivial.
Qed.
Lemma isConfigTableSh1WithVE descChild ptRefChild descParent s :
partitionDescriptorEntry s -> 
In descParent (getPartitions pageRootPartition s) -> 
(forall idx : index,
StateLib.getIndexOfAddr descChild levelMin = idx ->
isVE ptRefChild idx s /\ getTableAddrRoot ptRefChild idxShadow1 descParent descChild s) -> 
(Nat.eqb pageDefault ptRefChild) = false -> 
In ptRefChild (getConfigPages descParent s).
Proof.
intros Hpde Hpart Hget Hnotnull.
apply pdSh1Sh2ListExistsNotNull  with s descParent in Hpde.
destruct Hpde as ((pd & Hpd & Hpdnotnull) 
  & (sh1 & Hsh1 & Hsh1notnull) & (sh2 & Hsh2 & Hsh2notnull) & 
  (sh3 & Hsh3 & Hsh3notnull)).
unfold getConfigPages.
unfold getConfigPagesAux.
rewrite Hpd, Hsh1, Hsh2, Hsh3.
simpl.
right.
do 1 (rewrite in_app_iff;
right).
 rewrite in_app_iff.
left.
unfold getIndirections.
destruct Hget with (StateLib.getIndexOfAddr descChild levelMin) ;trivial.
clear Hget.
unfold getTableAddrRoot in *.
destruct H0 as(_ & H0).
rewrite <- nextEntryIsPPgetFstShadow in *.
apply H0 in Hsh1.
clear H0.
destruct Hsh1 as (nbL & HnbL & stop & Hstop & Hind).
apply getIndirectionInGetIndirections with descChild nbL stop;trivial.
assert(0<nbLevel) by apply nbLevelNotZero;trivial.
apply beq_nat_false in Hnotnull.
unfold not;intros.
subst.
now contradict Hnotnull.
apply getNbLevelLe in HnbL;trivial.
assumption. 
Qed.



Lemma mappedPageIsNotPTable (table1 table2 currentPart root : page)
F  idxroot  va idx1 (s : state): 
 (idxroot = idxPageDir \/ idxroot = idxShadow1 \/ idxroot = idxShadow2) -> 
(forall partition : page,
          In partition (getPartitions pageRootPartition s) ->
          partition = table2 \/ In table2 (getConfigPagesAux partition s) -> False) ->
In currentPart (getPartitions pageRootPartition s) ->
partitionDescriptorEntry s -> 
nextEntryIsPP currentPart idxroot root s -> 
StateLib.getIndexOfAddr va levelMin = idx1 -> 
(forall idx : index,
        StateLib.getIndexOfAddr va levelMin = idx ->
       F table1 idx s /\ 
        getTableAddrRoot table1 idxroot currentPart va s) ->
(Nat.eqb pageDefault table1) = false -> 
table2 <> table1.
Proof.
intros Hor Hconfig Hcurpart Hpde Hpp Hidxref Hptref Hptrefnotnull.
assert(Hnotin: ~ In table2 (getConfigPagesAux currentPart s)).
 { generalize (Hconfig currentPart Hcurpart); clear Hconfig; intros Hconfig.
        apply Classical_Prop.not_or_and in Hconfig.
        destruct Hconfig; assumption. }
assert(Hin : In table1 (getConfigPagesAux currentPart s)).
{ unfold getConfigPagesAux.
  unfold consistency in *.
  assert (Hroots : 
   (exists pd , StateLib.getPd currentPart (memory s) = Some pd /\
    pd <> pageDefault) /\ 
   (exists sh1, StateLib.getFstShadow currentPart (memory s) = Some sh1 /\
    sh1 <> pageDefault) /\ 
   (exists sh2, StateLib.getSndShadow currentPart (memory s) = Some sh2 /\ 
    sh2 <> pageDefault) /\ 
   (exists list, StateLib.getConfigTablesLinkedList currentPart (memory s) = Some list /\ 
    list <> pageDefault)).
  apply pdSh1Sh2ListExistsNotNull; trivial.
  (* 
  assert (Hcurpd : StateLib.getPd currentPart (memory s) = Some root).
  apply nextEntryIsPPgetPd; trivial. *)
  destruct Hroots as ((pd & Hpd & Hpdnotnull) 
  & (sh1 & Hsh1 & Hsh1notnull) & (sh2 & Hsh2 & Hsh2notnull) & 
  (sh3 & Hsh3 & Hsh3notnull)).
  rewrite Hpd, Hsh1, Hsh2, Hsh3.
  destruct Hor as [Hpdroot | [Hsh1root | Hsh2root]].
  + rewrite Hpdroot in *.
    simpl.
    assert(Hroot : root = pd).
    apply getPdNextEntryIsPPEq with currentPart s;trivial.
    rewrite Hroot in *;clear Hroot. (* 
    right. *)
    apply in_app_iff.
    left.
    apply Hptref in Hidxref.
    destruct Hidxref as (Hperef & Htblrootref).
    unfold getTableAddrRoot in Htblrootref.
    assert (Hppref : nextEntryIsPP currentPart idxPageDir pd s) by trivial.
    destruct  Htblrootref as (_ & Htblrootref).
    generalize (Htblrootref pd  Hppref); clear Htblrootref; 
    intros Htblrootref.
    destruct Htblrootref as (nbL & HnbL & stop & Hstop & Hindref).
    apply getIndirectionInGetIndirections with va nbL stop; trivial.
    assert(0 < nbLevel) by apply nbLevelNotZero ; lia.
    apply beq_nat_false in Hptrefnotnull.
    unfold not; intros Hnot.
    subst. now contradict Hptrefnotnull.
    apply getNbLevelLe; trivial.
+  simpl.
    rewrite Hsh1root in *.
    assert(Hroot : root = sh1).
    apply getSh1NextEntryIsPPEq with currentPart s;trivial.
    rewrite Hroot in *;clear Hroot. (* 
    right. *)
    apply in_app_iff.
    right.
    simpl. (* right. *)
    apply in_app_iff.
    left.
    apply Hptref in Hidxref.
    destruct Hidxref as (Hperef & Htblrootref).
    unfold getTableAddrRoot in Htblrootref.
    assert (Hppref : nextEntryIsPP currentPart idxShadow1 sh1 s) by trivial.
    destruct  Htblrootref as (_ & Htblrootref).
    generalize (Htblrootref sh1  Hppref); clear Htblrootref; 
    intros Htblrootref.
    destruct Htblrootref as (nbL & HnbL & stop & Hstop & Hindref).
    apply getIndirectionInGetIndirections with va nbL stop; trivial.
    assert(0 < nbLevel) by apply nbLevelNotZero ; lia.
    apply beq_nat_false in Hptrefnotnull.
    unfold not; intros Hnot.
    subst. now contradict Hptrefnotnull.
    apply getNbLevelLe; trivial.
+ simpl.
    rewrite Hsh2root in *.
    assert(Hroot : root = sh2).
    apply getSh2NextEntryIsPPEq with currentPart s;trivial.
    rewrite Hroot in *;clear Hroot. (* 
    right. *)
    apply in_app_iff.
    right.
    simpl.
(*      right. *)
    apply in_app_iff.
    right.
    simpl.
(*      right. *)
    apply in_app_iff.
    left.
    apply Hptref in Hidxref.
    destruct Hidxref as (Hperef & Htblrootref).
    unfold getTableAddrRoot in Htblrootref.
    assert (Hppref : nextEntryIsPP currentPart idxShadow2 sh2 s) by trivial.
    destruct  Htblrootref as (_ & Htblrootref).
    generalize (Htblrootref sh2  Hppref); clear Htblrootref; 
    intros Htblrootref.
    destruct Htblrootref as (nbL & HnbL & stop & Hstop & Hindref).
    apply getIndirectionInGetIndirections with va nbL stop; trivial.
    assert(0 < nbLevel) by apply nbLevelNotZero ; lia.
    apply beq_nat_false in Hptrefnotnull.
    unfold not; intros Hnot.
    subst. now contradict Hptrefnotnull.
    apply getNbLevelLe; trivial. }
  unfold not; intros Hnot.
  subst; now contradict Hin.
Qed.


Lemma entryPresentFlagReadPresent s table idx flag: 
entryPresentFlag table idx flag s -> 
StateLib.readPresent table idx (memory s)  = Some flag.
Proof.
unfold entryPresentFlag , StateLib.readPresent .
intros.
destruct (lookup table idx (memory s) pageEq idxEq );intros;try now contradict H.
destruct v;intros; try now contradict H.
subst;trivial.
Qed.

Lemma entryPresentFlagReadPresent' s table idx flag: 
entryPresentFlag table idx flag s <-> 
StateLib.readPresent table idx (memory s)  = Some flag.
Proof.
unfold entryPresentFlag , StateLib.readPresent .
intros.
destruct (lookup table idx (memory s) pageEq idxEq );intros;[|split;intros Hi;try now contradict Hi]. 
destruct v;split;intros; try now contradict H.
subst;trivial.
inversion H;trivial.
Qed.

Lemma entryUserFlagReadAccessible s table idx flag: 
entryUserFlag table idx flag s <-> 
StateLib.readAccessible table idx (memory s)  = Some flag.
Proof.
unfold entryUserFlag , StateLib.readAccessible .
intros.
destruct (lookup table idx (memory s) pageEq idxEq );intros;[|split;intros Hi;try now contradict Hi]. 
destruct v;split;intros; try now contradict H.
subst;trivial.
inversion H;trivial.
Qed.

Lemma isEntryPageLookupEq table idx entry phy s:
lookup table idx (memory s) pageEq idxEq = Some (PE entry) -> 
isEntryPage table idx phy s -> 
pa entry = phy.
Proof.
intros Hlookup Hentrypage.
unfold isEntryPage in *.
rewrite Hlookup in *.
trivial.
Qed.

Lemma isEntryPageReadPhyEntry table idx entry s:
isEntryPage table idx (pa entry) s -> 
StateLib.readPhyEntry table idx (memory s) = Some (pa entry).
Proof.
intros Hentrypage.
unfold isEntryPage in *.
unfold StateLib.readPhyEntry.
destruct(lookup table idx (memory s) pageEq idxEq );
try now contradict Hentrypage.
destruct v; try now contradict Hentrypage.
f_equal;trivial.
Qed.

Lemma isEntryPageReadPhyEntry1 table idx p s:
isEntryPage table idx p s -> 
StateLib.readPhyEntry table idx (memory s) = Some p.
Proof.
intros Hentrypage.
unfold isEntryPage in *.
unfold StateLib.readPhyEntry.
destruct(lookup table idx (memory s) pageEq idxEq );
try now contradict Hentrypage.
destruct v; try now contradict Hentrypage.
f_equal;trivial.
Qed.
Lemma isAccessibleMappedPage pdChild currentPD (ptPDChild : page)  entry s : 
(Nat.eqb pageDefault ptPDChild ) = false -> 
entryPresentFlag ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) true s -> 
entryUserFlag ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) true s -> 
lookup ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) (memory s) pageEq idxEq =
    Some (PE entry) -> 
 nextEntryIsPP (currentPartition s) idxPageDir currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr pdChild levelMin = idx ->
isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild idxPageDir (currentPartition s) pdChild s ) -> 
getAccessibleMappedPage currentPD s pdChild = SomePage (pa entry).
Proof.
intros Hnotnull Hpe Hue Hlookup Hpp Hget .
assert ( isPE ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) s /\ 
        getTableAddrRoot ptPDChild idxPageDir (currentPartition s) pdChild s) as (_ & Hroot).
apply Hget; trivial.
clear Hget. 
unfold getAccessibleMappedPage.
unfold getTableAddrRoot in *.
destruct Hroot  as (_ & Hroot).
apply Hroot in Hpp; clear Hroot.
destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
rewrite <- HnbL.
subst.
assert (Hnewind : getIndirection currentPD pdChild nbL (nbLevel - 1) s= Some ptPDChild).
apply getIndirectionStopLevelGT2 with (nbL + 1);try lia;trivial.
apply getNbLevelEq in HnbL.
unfold CLevel in HnbL.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros; rewrite H in *.
destruct nbL.
simpl in *.
inversion HnbL; trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
rewrite Hnewind.
apply entryPresentFlagReadPresent in Hpe.
rewrite Hpe.
apply entryUserFlagReadAccessible in Hue.
rewrite Hue.
unfold StateLib.readPhyEntry.
rewrite Hnotnull.
rewrite Hlookup; trivial.
Qed.
Lemma isAccessibleMappedPage2 partition pdChild currentPD (ptPDChild : page)  phypage s : 
(Nat.eqb pageDefault ptPDChild ) = false -> 
entryPresentFlag ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) true s -> 
entryUserFlag ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) true s -> 
isEntryPage ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) phypage s -> 
 nextEntryIsPP partition idxPageDir currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr pdChild levelMin = idx ->
isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild idxPageDir partition pdChild s ) -> 
getAccessibleMappedPage currentPD s pdChild = SomePage phypage.
Proof.
intros Hnotnull Hpe Hue Hlookup Hpp Hget .
assert ( isPE ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) s /\ 
        getTableAddrRoot ptPDChild idxPageDir partition pdChild s) as (_ & Hroot).
apply Hget; trivial.
clear Hget. 
unfold getAccessibleMappedPage.
unfold getTableAddrRoot in *.
destruct Hroot  as (_ & Hroot).
apply Hroot in Hpp; clear Hroot.
destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
rewrite <- HnbL.
subst.
assert (Hnewind : getIndirection currentPD pdChild nbL (nbLevel - 1) s= Some ptPDChild).
apply getIndirectionStopLevelGT2 with (nbL + 1);try lia;trivial.
apply getNbLevelEq in HnbL.
unfold CLevel in HnbL.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros; rewrite H in *.
destruct nbL.
simpl in *.
inversion HnbL; trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
rewrite Hnewind.
apply entryPresentFlagReadPresent in Hpe.
rewrite Hpe.
apply entryUserFlagReadAccessible in Hue.
rewrite Hue.
unfold StateLib.readPhyEntry.
rewrite Hnotnull.
unfold isEntryPage in *.
destruct(lookup ptPDChild (StateLib.getIndexOfAddr pdChild levelMin)
              (memory s) pageEq idxEq);
              try now contradict Hlookup.
destruct v;            try now contradict Hlookup.
f_equal;

trivial.
Qed.

Lemma getPDFlagReadPDflag currentShadow1 pdChild (ptPDChildSh1 : page)
idxPDChild currentPart s:
(Nat.eqb ptPDChildSh1 pageDefault) = false ->
nextEntryIsPP currentPart idxShadow1 currentShadow1 s -> 
getPDFlag currentShadow1 pdChild s = false -> 
StateLib.getIndexOfAddr pdChild levelMin =  idxPDChild -> 
(forall idx : index,
   StateLib.getIndexOfAddr pdChild levelMin = idx ->
   isVE ptPDChildSh1 idx s /\ 
   getTableAddrRoot ptPDChildSh1 idxShadow1 currentPart pdChild s) ->
StateLib.readPDflag ptPDChildSh1 idxPDChild (memory s) = Some false \/ 
StateLib.readPDflag ptPDChildSh1 idxPDChild (memory s) = None .
Proof.
intros Hptnotnull Hsh1 Hgetflag Hidx Hind.
assert(isVE ptPDChildSh1 (StateLib.getIndexOfAddr pdChild levelMin) s /\ 
      getTableAddrRoot ptPDChildSh1 idxShadow1 currentPart pdChild s) as (Hve & Hget).
apply Hind;trivial.
clear Hind.
unfold getTableAddrRoot in *.
unfold getPDFlag in *.
destruct Hget as (_ & Hget).
apply Hget in Hsh1.
clear Hget.
destruct Hsh1 as (nbL & HnbL & stop & Hstop & Hget).
subst.
rewrite <- HnbL in *.
assert (Hind1 : getIndirection currentShadow1 pdChild nbL (nbLevel - 1) s  = Some ptPDChildSh1).
apply getIndirectionStopLevelGT2 with (nbL +1);try lia;trivial.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq ( lt_dec (nbLevel - 1) nbLevel);intros.
simpl;trivial.
assert(0 < nbLevel) by apply nbLevelNotZero.
lia.
rewrite Hind1 in *.
rewrite Hptnotnull in *.
case_eq(StateLib.readPDflag ptPDChildSh1 
        (StateLib.getIndexOfAddr pdChild levelMin) (memory s));intros.
rewrite H in *.
destruct b; try now contradict Hgetflag.
trivial.
left;trivial.
right;trivial.
Qed.

Lemma isVaInParent s va descParent (ptsh2 : page) vaInAncestor sh2 :
(Nat.eqb pageDefault ptsh2) = false -> 
(forall idx : index,
StateLib.getIndexOfAddr va levelMin = idx ->
isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s) -> 
isVA' ptsh2 (StateLib.getIndexOfAddr va levelMin) vaInAncestor s -> 
nextEntryIsPP descParent idxShadow2 sh2 s -> 
getVirtualAddressSh2 sh2 s va = Some vaInAncestor.
Proof.
intros Hnotnull Hroot Hva Hpp .
assert( isVA ptsh2 (StateLib.getIndexOfAddr va levelMin ) s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s) as (Hisva & Hget).
apply Hroot;trivial. clear Hroot.
unfold getTableAddrRoot in *.
destruct Hget as (_ & Hget).
apply Hget in Hpp.
clear Hget.
destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
unfold getVirtualAddressSh2.
rewrite <- HnbL.
subst.
assert (getIndirection sh2 va nbL (nbLevel - 1) s = Some ptsh2).
apply getIndirectionStopLevelGT2 with (nbL+1) ; trivial.
lia.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq( lt_dec (nbLevel - 1) nbLevel );intros.
simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
clear Hind.
rewrite H.
rewrite Hnotnull.
unfold isVA' in *.
unfold StateLib.readVirtual.
destruct( lookup ptsh2 (StateLib.getIndexOfAddr va levelMin) (memory s) pageEq idxEq );
try now contradict Hva.
destruct v; try now contradict Hva.
subst;trivial.
Qed.

Lemma disjointUsedPagesDisjointMappedPages partition1 partition2 s:
disjoint (getUsedPages partition1 s) (getUsedPages partition2 s) -> 
disjoint (getMappedPages partition1 s) (getMappedPages partition2 s).
Proof.
intros.
unfold disjoint in *.
intros.
unfold getUsedPages in *.
simpl in *.
assert(~
(partition2 = x \/
In x (getConfigPagesAux partition2 s ++ getMappedPages partition2 s))).
apply H.
right.
apply in_app_iff.
right;trivial.
apply Classical_Prop.not_or_and in H1.
destruct H1.
rewrite in_app_iff in H2.
apply Classical_Prop.not_or_and in H2.
intuition.
Qed.



Lemma inGetMappedPagesGetIndirection descParent entry vaInDescParent pdDesc (pt : page) nbL1  s:
entryPresentFlag pt (StateLib.getIndexOfAddr vaInDescParent levelMin) true s -> 
(Nat.eqb pageDefault pt) = false -> 
Some nbL1 = StateLib.getNbLevel -> 
nextEntryIsPP descParent idxPageDir pdDesc s -> 
getIndirection pdDesc vaInDescParent nbL1 (nbL1 + 1) s = Some pt -> 
isEntryPage pt (StateLib.getIndexOfAddr vaInDescParent levelMin) (pa entry) s ->
In (pa entry) (getMappedPages descParent s).
Proof.
intros Hpresent Hptnotnull HnbL Hpd Hind Hep.
unfold getMappedPages.
rewrite nextEntryIsPPgetPd in *.
rewrite Hpd.
unfold getMappedPagesAux.
apply filterOptionInIff.
unfold getMappedPagesOption.
rewrite in_map_iff.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaInDescParent va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1;split;trivial.
assert(Hnewgoal : getMappedPage pdDesc s vaInDescParent = SomePage (pa entry)). 
{
unfold getMappedPage.
rewrite <- HnbL.
assert(Hnewind : getIndirection pdDesc vaInDescParent nbL1 (nbLevel - 1) s  = Some pt).
apply getIndirectionStopLevelGT2 with (nbL1+1);trivial.
lia.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq(   lt_dec (nbLevel - 1) nbLevel);intros.
simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
rewrite Hnewind.
rewrite Hptnotnull.
rewrite entryPresentFlagReadPresent with s pt  (StateLib.getIndexOfAddr 
vaInDescParent levelMin) true;trivial.
apply isEntryPageReadPhyEntry in Hep.
rewrite Hep. trivial. }
rewrite <- Hnewgoal.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.
Qed.

Lemma getMappedPageGetIndirection ancestor phypage newVA pdAncestor
 (ptAncestor : page) L  s:
StateLib.readPresent ptAncestor (StateLib.getIndexOfAddr newVA levelMin)
 (memory s) = Some true -> 
(Nat.eqb pageDefault ptAncestor) = false -> 
 Some L = StateLib.getNbLevel -> 
nextEntryIsPP ancestor idxPageDir pdAncestor s -> 
getIndirection pdAncestor newVA L (nbLevel - 1) s = Some ptAncestor -> 
StateLib.readPhyEntry ptAncestor (StateLib.getIndexOfAddr newVA levelMin)
 (memory s) =  Some phypage -> 
getMappedPage pdAncestor s newVA = SomePage phypage.
Proof.
intros Hpresent Hptnotnull HnbL Hpd Hind Hep.
unfold getMappedPage.
rewrite nextEntryIsPPgetPd in *.
rewrite <- HnbL.
rewrite Hind.
rewrite Hptnotnull.
rewrite Hpresent;trivial.
rewrite Hep;trivial.
Qed.

Lemma getMappedPageGetTableRoot ptvaInAncestor ancestor phypage pdAncestor vaInAncestor s :
( forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor levelMin = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s) -> 
(Nat.eqb pageDefault ptvaInAncestor) = false ->
 isEntryPage ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) 
 phypage s ->
 entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) true s
  ->
nextEntryIsPP ancestor idxPageDir pdAncestor s -> 
getMappedPage pdAncestor s vaInAncestor = SomePage phypage.
Proof.
intros Hget Hnotnull Hep Hpresent Hpdparent.
destruct Hget with (StateLib.getIndexOfAddr vaInAncestor levelMin)
as (Hpe2 & Hroot2);trivial.
clear Hget.
unfold getTableAddrRoot in Hroot2.
destruct Hroot2 as (_ & Htableroot).
unfold getMappedPages.
assert(Hpd : StateLib.getPd ancestor (memory s) = Some pdAncestor).
apply nextEntryIsPPgetPd;trivial.
apply Htableroot in Hpdparent.
 clear Htableroot.
destruct Hpdparent as (nbL & HnbL & stop & Hstop & Hind ).
unfold getMappedPage.
rewrite <- HnbL.
subst.
assert(Hnewind :getIndirection pdAncestor vaInAncestor nbL  (nbLevel - 1) s
 = Some ptvaInAncestor).
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
lia.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel);
intros;simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
rewrite Hnewind.
rewrite Hnotnull.
apply entryPresentFlagReadPresent in Hpresent.
rewrite Hpresent.
unfold isEntryPage in *.
unfold StateLib.readPhyEntry.
destruct(lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) 
 (memory s) pageEq idxEq );
try now contradict Hep.
destruct v; try now contradict Hep.
f_equal;trivial.
Qed.
Lemma getVirtualAddressSh2GetTableRoot:
forall (ptsh2 descParent  sh2  : page) 
    (vaInAncestor va: vaddr) (s : state) L,
(forall idx : index,
  StateLib.getIndexOfAddr va levelMin = idx ->
   isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 idxShadow2 descParent va s) ->
(Nat.eqb pageDefault ptsh2) = false ->
isVA' ptsh2 (StateLib.getIndexOfAddr va levelMin) vaInAncestor s -> 
StateLib.getSndShadow descParent (memory s) = Some sh2 -> 
Some L = StateLib.getNbLevel ->
getVirtualAddressSh2 sh2 s va = Some vaInAncestor.
Proof. 
intros ptsh2 descParent sh2 vaInAncestor va  s L.
intros Hget Hnotnull Hisva Hsh2 HL.

unfold getVirtualAddressSh2.
rewrite <- HL.
destruct Hget with (StateLib.getIndexOfAddr va levelMin)
as (Hpe2 & Hroot2);trivial.
clear Hget.
unfold getTableAddrRoot in Hroot2.
destruct Hroot2 as (_ & Htableroot).
rewrite <- nextEntryIsPPgetSndShadow in *. 
apply Htableroot in Hsh2.
clear Htableroot.
destruct Hsh2 as (nbL & HnbL & stop & Hstop & Hind ).
subst.
rewrite <- HnbL in *.
inversion HL.
subst. 
assert(Hnewind :getIndirection sh2 va nbL (nbLevel - 1) s
= Some ptsh2).
apply getIndirectionStopLevelGT2 with (nbL +1);try lia;trivial.
apply getNbLevelEq in HnbL.
subst. apply nbLevelEq.
rewrite Hnewind.
rewrite Hnotnull.
unfold isVA' in *.
unfold StateLib.readVirtual.
destruct(lookup ptsh2 (StateLib.getIndexOfAddr va levelMin) 
(memory s) pageEq idxEq );
try now contradict Hisva.
destruct v; try now contradict Hisva.
f_equal;trivial.
Qed.



Lemma getMappedPageNotAccessible  
ptvaInAncestor ancestor phypage pdAncestor vaInAncestor s :
( forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor levelMin = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s) -> 
(Nat.eqb pageDefault ptvaInAncestor) = false ->
 isEntryPage ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) 
 phypage s ->
 entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) true s ->
entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) false s ->
nextEntryIsPP ancestor idxPageDir pdAncestor s -> 
getAccessibleMappedPage pdAncestor s vaInAncestor = NonePage.
Proof.
intros Hget Hnotnull Hep Hpresent Huser Hpdparent.
destruct Hget with (StateLib.getIndexOfAddr vaInAncestor levelMin)
as (Hpe2 & Hroot2);trivial.
clear Hget.
unfold getTableAddrRoot in Hroot2.
destruct Hroot2 as (_ & Htableroot).
unfold getMappedPages.
assert(Hpd : StateLib.getPd ancestor (memory s) = Some pdAncestor).
apply nextEntryIsPPgetPd;trivial.
apply Htableroot in Hpdparent.
 clear Htableroot.
destruct Hpdparent as (nbL & HnbL & stop & Hstop & Hind ).

unfold getAccessibleMappedPage.
rewrite <- HnbL.
subst.
assert(Hnewind :getIndirection pdAncestor vaInAncestor nbL  (nbLevel - 1) s
 = Some ptvaInAncestor).
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
lia.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel);
intros;simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
rewrite Hnewind.
rewrite Hnotnull.
apply entryPresentFlagReadPresent in Hpresent.
rewrite Hpresent.
unfold isEntryPage in *.
unfold StateLib.readPhyEntry.
destruct(lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) 
 (memory s) pageEq idxEq );
try now contradict Hep.
destruct v; try now contradict Hep.
unfold StateLib.readAccessible.
unfold entryUserFlag in *.
case_eq(lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) 
            (memory s) pageEq idxEq);[intros v Hv | intros Hv];
            rewrite Hv in *; trivial.
case_eq v; intros entry Hentry;
rewrite Hentry in *; trivial.
rewrite <- Huser;trivial.
Qed.

Lemma getAccessibleMappedPageNotPresent 
ptvaInAncestor ancestor  pdAncestor vaInAncestor s :
( forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor levelMin = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s) -> 
(Nat.eqb pageDefault ptvaInAncestor) = false ->
 entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) false s ->
nextEntryIsPP ancestor idxPageDir pdAncestor s -> 
getAccessibleMappedPage pdAncestor s vaInAncestor = NonePage.
Proof.
intros Hget Hnotnull  Hpresent  Hpdparent.
destruct Hget with (StateLib.getIndexOfAddr vaInAncestor levelMin)
as (Hpe2 & Hroot2);trivial.
clear Hget.
unfold getTableAddrRoot in Hroot2.
destruct Hroot2 as (_ & Htableroot).
unfold getMappedPages.
assert(Hpd : StateLib.getPd ancestor (memory s) = Some pdAncestor).
apply nextEntryIsPPgetPd;trivial.
apply Htableroot in Hpdparent.
 clear Htableroot.
destruct Hpdparent as (nbL & HnbL & stop & Hstop & Hind ).

unfold getAccessibleMappedPage.
rewrite <- HnbL.
subst.
assert(Hnewind :getIndirection pdAncestor vaInAncestor nbL  (nbLevel - 1) s
 = Some ptvaInAncestor).
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
lia.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel);
intros;simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
rewrite Hnewind.
rewrite Hnotnull.
apply entryPresentFlagReadPresent in Hpresent.
rewrite Hpresent.
trivial.
Qed.

Lemma getMappedPageNotPresent 
ptvaInAncestor ancestor  pdAncestor vaInAncestor s :
( forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor levelMin = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s) -> 
(Nat.eqb pageDefault ptvaInAncestor) = false ->
 entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) false s ->
nextEntryIsPP ancestor idxPageDir pdAncestor s -> 
getMappedPage pdAncestor s vaInAncestor = SomeDefault.
Proof.
intros Hget Hnotnull  Hpresent  Hpdparent.
destruct Hget with (StateLib.getIndexOfAddr vaInAncestor levelMin)
as (Hpe2 & Hroot2);trivial.
clear Hget.
unfold getTableAddrRoot in Hroot2.
destruct Hroot2 as (_ & Htableroot).
unfold getMappedPages.
assert(Hpd : StateLib.getPd ancestor (memory s) = Some pdAncestor).
apply nextEntryIsPPgetPd;trivial.
apply Htableroot in Hpdparent.
 clear Htableroot.
destruct Hpdparent as (nbL & HnbL & stop & Hstop & Hind ).
unfold getMappedPage.
rewrite <- HnbL.
subst.
assert(Hnewind :getIndirection pdAncestor vaInAncestor nbL  (nbLevel - 1) s
 = Some ptvaInAncestor).
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
lia.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel);
intros;simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
rewrite Hnewind.
rewrite Hnotnull.
apply entryPresentFlagReadPresent in Hpresent.
rewrite Hpresent.
trivial.
Qed.

Lemma inGetMappedPagesGetTableRoot va pt descParent phypage pdParent s :
(forall idx : index,
StateLib.getIndexOfAddr va levelMin = idx ->
isPE pt idx s /\ getTableAddrRoot pt idxPageDir descParent va s) -> 
(Nat.eqb pageDefault pt) = false ->
isEntryPage pt(StateLib.getIndexOfAddr va levelMin)  phypage s ->
entryPresentFlag pt (StateLib.getIndexOfAddr va levelMin)  true s ->
nextEntryIsPP descParent idxPageDir pdParent s -> 
In phypage (getMappedPages descParent s).
Proof.
intros Hget Hnotnull Hep Hpresent Hpdparent.
destruct Hget with (StateLib.getIndexOfAddr va levelMin)
as (Hpe2 & Hroot2);trivial.
clear Hget.
unfold getTableAddrRoot in Hroot2.
destruct Hroot2 as (_ & Htableroot).
unfold getMappedPages.
assert(Hpd : StateLib.getPd descParent (memory s) = Some pdParent).
apply nextEntryIsPPgetPd;trivial.
rewrite Hpd.
apply Htableroot in Hpdparent. clear Htableroot.
destruct Hpdparent as (nbL & HnbL & stop & Hstop & Hind ).
unfold getMappedPagesAux.
apply filterOptionInIff.
unfold getMappedPagesOption.
apply in_map_iff.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel va va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1;split;trivial.
assert(Hnewgoal : getMappedPage pdParent s va = SomePage phypage).
{ unfold getMappedPage.
rewrite <- HnbL.
subst.
assert(Hnewind :getIndirection  pdParent va nbL  (nbLevel - 1) s = Some pt).
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
lia.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel);
intros;simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
rewrite Hnewind.
rewrite Hnotnull.
apply entryPresentFlagReadPresent in Hpresent.
rewrite Hpresent.
unfold isEntryPage in *.
unfold StateLib.readPhyEntry.
destruct(lookup pt (StateLib.getIndexOfAddr va levelMin) (memory s) pageEq idxEq );
try now contradict Hep.
destruct v; try now contradict Hep.
f_equal;trivial. }
rewrite <- Hnewgoal.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.

(* apply AllVAddrAll.
Qed.
 *)
 Qed.


Lemma pageDecOrNot :
forall p1 p2 : page, p1 = p2 \/ p1<>p2.
Proof.
destruct p1;simpl in *;subst;destruct p2;simpl in *;subst.
assert (Heq :p=p0 \/ p<> p0) by lia.
destruct Heq as [Heq|Heq].
subst.
left;f_equal;apply proof_irrelevance.
right. unfold not;intros.
inversion H.
subst.
now contradict Heq.
Qed.

Lemma isAncestorTrans ancestor descParent currentPart s:
parentInPartitionList s ->
noCycleInPartitionTree s-> 
isParent s -> 
noDupPartitionTree s -> 
multiplexerWithoutParent s -> 
In currentPart (getPartitions pageRootPartition s) -> 
StateLib.getParent descParent (memory s) = Some ancestor -> 
isAncestor currentPart descParent s -> 
isAncestor currentPart ancestor s.
Proof.
unfold isAncestor.
intros Hparentinlist  Hnocycle.
intros Hisparent Hnoduptree Hmultnone Hcurpart.
intros.
assert(Hor :currentPart = ancestor  \/ currentPart <> ancestor ).
apply pageDecOrNot.
destruct Hor.
left;trivial.
right.
destruct H0.
+ subst.
  unfold getAncestors.    
  induction nbPage;
  simpl;
  rewrite H;
  simpl;left;trivial.
+ apply isAncestorTrans2 with descParent;trivial.
Qed.

Lemma parentIsAncestor partition ancestor s:
nextEntryIsPP partition idxParentDesc ancestor s -> 
In ancestor (getAncestors partition s).
Proof.
intros Hpd.
rewrite nextEntryIsPPgetParent in *.
unfold getAncestors.
destruct nbPage;
simpl;
rewrite Hpd;simpl;left;trivial.
Qed.

Lemma phyPageNotDefault table idx phyPage s : 
isPresentNotDefaultIff s -> 
entryPresentFlag table idx true s -> 
isEntryPage table idx phyPage s -> 
(Nat.eqb pageDefault phyPage) = false.
Proof.
intros.
unfold isPresentNotDefaultIff in *.
assert (StateLib.readPhyEntry table idx (memory s) = Some phyPage).
{ unfold StateLib.readPhyEntry.
 unfold isEntryPage in *.
 case_eq(lookup table idx (memory s) pageEq idxEq);intros * Hi;
 rewrite Hi in *;try now contradict H1.
 case_eq v;intros * Hii;
 rewrite Hii in *;try now contradict H1.
 subst;trivial. }
assert (StateLib.readPresent table idx (memory s) = Some true).
{ unfold StateLib.readPresent .
  unfold entryPresentFlag in *.
  case_eq(lookup table idx (memory s) pageEq idxEq);intros * Hi;
  rewrite Hi in *;try now contradict H1.
  case_eq v;intros * Hii;
  rewrite Hii in *;try now contradict H1.
  subst;f_equal;symmetry; trivial. }
clear H1 H0.
apply PeanoNat.Nat.eqb_neq.
unfold not;intros;subst.
destruct phyPage;destruct pageDefault.
simpl in *.
subst.
assert(Hp0 = Hp).
apply proof_irrelevance;trivial.
subst.
apply H in H2.
rewrite H2 in H3.
inversion H3.
Qed.

Lemma phyPageIsPresent table idx entry s : 
isPresentNotDefaultIff s -> 
 lookup table idx (memory s) pageEq idxEq = Some (PE entry) -> 
(Nat.eqb pageDefault (pa entry)) = false -> 
present entry = true.
Proof.
intros.
unfold isPresentNotDefaultIff in *.
assert (StateLib.readPhyEntry table idx (memory s) = Some (pa entry)).
{ unfold StateLib.readPhyEntry.
  rewrite H0. trivial. }
apply beq_nat_false in H1.
assert (~ (present entry = false) -> present entry = true ).
intros.
unfold not in *.
destruct ( present entry); trivial.
contradict H3;trivial.
apply H3.
unfold not.
intros.
clear H3.
generalize (H table idx);clear H; intros H.
destruct H as (Hii & Hi).
assert(StateLib.readPresent table idx (memory s) = Some false).
unfold StateLib.readPresent.
rewrite H0.
f_equal;trivial.
apply Hii in H.
clear Hi Hii.
apply H1.
rewrite  H in H2.
inversion H2;trivial.
Qed.

Lemma accessiblePAgeIsMapped pd s va accessiblePage :
getAccessibleMappedPage pd s va = SomePage accessiblePage -> 
getMappedPage pd s va = SomePage accessiblePage.
Proof.
intros.
unfold getMappedPage.
unfold getAccessibleMappedPage in *.
destruct( StateLib.getNbLevel);try now contradict H.
destruct ( getIndirection pd va l (nbLevel - 1) s );try now contradict H.
destruct(Nat.eqb pageDefault p);try now contradict H.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va levelMin) (memory s) );
try
 now contradict H.
 destruct b;try now contradict H.
destruct( StateLib.readAccessible p (StateLib.getIndexOfAddr va levelMin) (memory s));
try now contradict H.
destruct b;try now contradict H.

trivial.
Qed.
Import List.ListNotations.
Lemma getIndirectionsOnlyPD pd s: 
(forall idx : index,
        StateLib.readPhyEntry pd idx (memory s) = Some pageDefault /\
        StateLib.readPresent pd idx (memory s) = Some false) -> 
  getIndirections pd s = [pd].
Proof.
intros.      
unfold getIndirections.
assert(0<nbLevel) by apply nbLevelNotZero.
destruct nbLevel.
simpl.
lia.
simpl.
f_equal.
induction tableSize.
simpl;trivial.
simpl.
intros.
destruct H with (CIndex n0) as (Hphy & Hpres);trivial.
unfold StateLib.readPhyEntry in *.
case_eq(lookup pd (CIndex n0) (memory s) pageEq idxEq);
intros * Hread;rewrite Hread in *;trivial.
case_eq v;intros * Hv; rewrite Hv in *;trivial.
inversion Hphy.
subst.
case_eq(Nat.eqb (pa p) (pa p));intros Hfalse;trivial.
apply beq_nat_false in Hfalse.
now contradict Hfalse.
Qed.

Lemma getIndirectionsOnlySh1 sh1 level s: 
Some level =StateLib.getNbLevel -> 
 isWellFormedFstShadow level sh1 s -> 
  getIndirections sh1 s = [sh1].
Proof.
intros.
apply getNbLevelEq in H.      
unfold getIndirections.
unfold isWellFormedFstShadow in *.
assert(0<nbLevel) by apply nbLevelNotZero.
destruct nbLevel.
lia.
simpl.
induction tableSize.
simpl;trivial.
f_equal.
simpl.
inversion IHn0. 
destruct H0.
destruct H0 as (Hlevel & Hcontent).
destruct Hcontent with (CIndex n0) as (Hphy & Hpres);trivial.
unfold StateLib.readPhyEntry in *.
case_eq(lookup sh1 (CIndex n0) (memory s) pageEq idxEq);
intros * Hread;rewrite Hread in *;trivial.
case_eq v;intros * Hv; rewrite Hv in *;trivial.
inversion Hphy.
subst.
case_eq(Nat.eqb (pa p) (pa p));intros Hfalse;trivial.
apply beq_nat_false in Hfalse.
now contradict Hfalse.
inversion IHn0.
 (*  
destruct H0. *)
destruct H0 as (Hlevel & H2).
destruct H2 with (CIndex n0) as (Hphy & Hpres);trivial.
unfold StateLib.readVirEntry in *.
case_eq(lookup sh1 (CIndex n0) (memory s) pageEq idxEq);
intros * Hread;rewrite Hread in *;trivial.
case_eq v;intros * Hv; rewrite Hv in *;trivial.
now contradict Hphy.
Qed.

Lemma getIndirectionsOnlySh2 sh2 level s: 
Some level =StateLib.getNbLevel -> 
 isWellFormedSndShadow level sh2 s -> 
  getIndirections sh2 s = [sh2].
Proof.
intros.
apply getNbLevelEq in H.      
unfold getIndirections.
unfold isWellFormedSndShadow in *.
assert(0<nbLevel) by apply nbLevelNotZero.
destruct nbLevel.
lia.
simpl.
induction tableSize.
simpl;trivial.
f_equal.
simpl.
inversion IHn0. 
destruct H0.
destruct H0 as (Hlevel & Hcontent).
destruct Hcontent with (CIndex n0) as (Hphy & Hpres);trivial.
unfold StateLib.readPhyEntry in *.
case_eq(lookup sh2 (CIndex n0) (memory s) pageEq idxEq);
intros * Hread;rewrite Hread in *;trivial.
case_eq v;intros * Hv; rewrite Hv in *;trivial.
inversion Hphy.
subst.
case_eq(Nat.eqb (pa p) (pa p));intros Hfalse;trivial.
apply beq_nat_false in Hfalse.
now contradict Hfalse.
inversion IHn0. 
(* destruct H0. *)
destruct H0 as (Hlevel & H2).

unfold StateLib.readVirtual in *.

generalize (H2 (CIndex n0)) ; clear H2 ;intros H2.
case_eq(lookup sh2 (CIndex n0) (memory s) pageEq idxEq);
intros * Hread;rewrite Hread in *;trivial.
case_eq v;intros * Hv; rewrite Hv in *;trivial.
now contradict H2.
Qed.

Lemma getLLPagesOnlyRoot root s:
initConfigPagesListPostCondition root s -> (* 
StateLib.readPhysical root (CIndex (tableSize - 1)) (memory s) = Some defaultPage -> 
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual root idx (memory s) =
Some defaultVAddr) -> 
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex root idx (memory s) = Some idxValue) ->  
 *)
 getLLPages root s (nbPage+1) = 
[root].
Proof.
unfold initConfigPagesListPostCondition.
intros  (HphyListcontent1 & HphyListcontent2 & HphyListcontent3 & HphyListcontent4) .
assert(Hi : 0<nbPage+1) by lia.
destruct (nbPage+1).
simpl. 
lia.
simpl.
case_eq (StateLib.getMaxIndex);intros.
unfold StateLib.getMaxIndex in *.
case_eq (gt_dec tableSize 0 );intros;
rewrite H0 in *.
assert(i =  (CIndex (tableSize - 1))).
destruct i.
inversion H.
subst.
unfold CIndex.
case_eq (lt_dec (tableSize - 1) tableSize);
intros.
f_equal.
apply proof_irrelevance.
assert(tableSizeLowerBound<tableSize) by apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
now contradict H2.
subst.
rewrite HphyListcontent1.
assert((Nat.eqb pageDefault pageDefault) = true).
apply NPeano.Nat.eqb_refl.
rewrite H1;trivial.
now contradict H0.
unfold StateLib.getMaxIndex in *.
case_eq (gt_dec tableSize 0 );intros;
rewrite H0 in *.
now contradict H0.
 assert(tableSizeLowerBound<tableSize) by apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
lia.
Qed.

Require Import Coq.Sorting.Permutation.

Lemma getIndirectionGetTableRoot (s : state) currentShadow1 currentPart ptRefChildFromSh1 descChild 
nbL : 
StateLib.getFstShadow currentPart (memory s) = Some currentShadow1 -> 
StateLib.getNbLevel = Some nbL -> 
(forall idx : index,
  StateLib.getIndexOfAddr descChild levelMin = idx ->
  isVE ptRefChildFromSh1 idx s /\ 
  getTableAddrRoot ptRefChildFromSh1 idxShadow1 currentPart descChild s) 
  -> 
getIndirection currentShadow1 descChild nbL (nbLevel - 1) s = Some ptRefChildFromSh1. 
Proof.
intros.
destruct H1 with (StateLib.getIndexOfAddr descChild levelMin );
trivial.
clear H1.
unfold getTableAddrRoot in *.
destruct H3 as (_ & H3).
rewrite <- nextEntryIsPPgetFstShadow in *.
apply H3 in H.
clear H3.
destruct H as (nbl & HnbL & stop & Hstop & Hind).
subst.
rewrite H0 in HnbL.
inversion HnbL;subst.
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
lia.
symmetry in H0. 
apply getNbLevelEq in H0.
subst.
apply nbLevelEq.
Qed.

Lemma getIndirectionGetTableRoot1 (s : state) pd currentPart pt va 
nbL : 
StateLib.getPd currentPart (memory s) = Some pd -> 
StateLib.getNbLevel = Some nbL -> 
(forall idx : index,
  StateLib.getIndexOfAddr va levelMin = idx ->
  isPE pt idx s /\ 
  getTableAddrRoot pt idxPageDir currentPart va s) 
  -> 
getIndirection pd va nbL (nbLevel - 1) s = Some pt. 
Proof.
intros.
destruct H1 with (StateLib.getIndexOfAddr va levelMin );
trivial.
clear H1.
unfold getTableAddrRoot in *.
destruct H3 as (_ & H3).
rewrite <- nextEntryIsPPgetPd in *.
apply H3 in H.
clear H3.
destruct H as (nbl & HnbL & stop & Hstop & Hind).
subst.
rewrite H0 in HnbL.
inversion HnbL;subst.
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
lia.
symmetry in H0. 
apply getNbLevelEq in H0.
subst.
apply nbLevelEq.
Qed.

Lemma readPhyEntryInGetIndirectionsAux s root n: 
forall page1,page1 <> pageDefault -> 
In page1 (getTablePages root tableSize s) -> 
n> 1 -> 
In page1 (getIndirectionsAux root s n)  .
Proof.
intros. 
destruct n;
intros; simpl in *.  now contradict H1.
simpl in *. right.
apply in_flat_map.
exists page1.
split; trivial.
destruct n.  lia. simpl.
left. trivial.     
Qed.

Lemma nodupLevelMinus1 root s (n0 : nat) idx: 
forall p , p<> pageDefault -> 
StateLib.readPhyEntry root idx (memory s) = Some p -> 
NoDup (getIndirectionsAux root s n0 ) ->
 n0 <= nbLevel  -> 
NoDup (getIndirectionsAux p s (n0 - 1)).
Proof.
intros p Hnotnull Hread Hnodup Hnbl.
destruct n0;simpl in *; trivial.
(* constructor;auto.
constructor. *)
rewrite NPeano.Nat.sub_0_r.
apply NoDup_cons_iff in Hnodup.
destruct Hnodup as (_ & Hnodup).
assert (In p (getTablePages root tableSize s)) as HIn.
apply readPhyEntryInGetTablePages with idx; trivial.
destruct idx. simpl in *; trivial.
assert (idx = (CIndex idx)) as Hidx.
symmetry. 
apply indexEqId.
rewrite <- Hidx. assumption.
induction (getTablePages root tableSize s).
now contradict HIn.
simpl in *.
apply NoDupSplit in Hnodup.
destruct HIn;
destruct Hnodup;
subst; trivial.
apply IHl;trivial.
Qed.

Lemma inclGetIndirectionsAuxMinus1 n root idx p s: 
StateLib.readPhyEntry root idx (memory s) = Some p -> 
(Nat.eqb pageDefault p) = false -> 
n> 1 -> 
incl (getIndirectionsAux p s (n - 1)) (getIndirectionsAux root s n).
Proof.
intros Hread Hnotnull Hn. 
unfold incl.              
intros.
set(k := n -1) in *.
replace n with (S k); [ | unfold k; lia].
simpl.              
assert (In p (getTablePages root tableSize s)) as Htbl. 
apply readPhyEntryInGetTablePages with idx; trivial.
destruct idx; simpl in *; trivial.
apply beq_nat_false in Hnotnull. unfold not. intros.
contradict Hnotnull.
rewrite H0. trivial.
assert (idx = (CIndex idx)) as Hidx'.
symmetry. apply indexEqId. rewrite <- Hidx'.
assumption. right.
induction ((getTablePages root tableSize s)).
now contradict Htbl.
simpl in *.
destruct Htbl; subst;
apply in_app_iff. left;trivial.
right. 

apply IHl;trivial.
Qed.

Lemma notInFlatMapNotInGetIndirection k l ( p0: page) s x: 
In p0 l -> 
~ In x (flat_map (fun p : page => getIndirectionsAux p s k) l) -> 
~ In x (getIndirectionsAux p0 s k).
Proof.
revert  p0 x k.
induction l; simpl in *; intros; [ 
now contradict H |].
destruct H; subst.
+ unfold not. intros. apply H0.
  apply in_app_iff. left. assumption.
+ apply IHl; trivial.
  unfold not.
  intros. apply H0.
  apply in_app_iff. right. assumption. 
Qed.

Lemma disjointGetIndirectionsAuxMiddle n (p p0 : page) root (idx1 idx2 : index) s:
p0 <> p -> 
n > 1 -> 
(Nat.eqb pageDefault p) = false -> 
(Nat.eqb pageDefault p0) = false -> 
NoDup (getIndirectionsAux root s n) -> 
StateLib.readPhyEntry root idx1 (memory s) = Some p0 -> 
StateLib.readPhyEntry root idx2 (memory s) = Some p ->
disjoint (getIndirectionsAux p s (n - 1)) (getIndirectionsAux p0 s (n - 1)).
Proof. 
unfold disjoint.
intros Hp0p Hn Hnotnull1 Hnotnull2 Hnodup Hreadp0 Hreadp x Hxp.        
set(k := n -1) in *.
assert(n = S k) as Hk.
unfold k in *.  lia.          
rewrite Hk in Hnodup. simpl in *.
apply  NoDup_cons_iff in Hnodup.
destruct Hnodup as (Hnoduproot & Hnodup2).
assert ( In p0  (getTablePages root tableSize s)) as Hp0root.
apply readPhyEntryInGetTablePages with idx1; trivial.
destruct idx1. simpl in *. trivial.
apply beq_nat_false in Hnotnull2.
unfold not;intros; apply Hnotnull2; clear Hk; subst;trivial.
assert(CIndex idx1 =  idx1) as Hcidx.
apply indexEqId.
rewrite Hcidx; trivial. 
assert ( In p  (getTablePages root tableSize s)) as Hproot. 
apply readPhyEntryInGetTablePages with idx2; trivial.
destruct idx2. simpl in *. trivial.
apply beq_nat_false in Hnotnull1. 
unfold not;intros; apply Hnotnull1;
clear Hk; subst;trivial.
assert(CIndex idx2 =  idx2) as Hcidx.
apply indexEqId. rewrite Hcidx. trivial.
move Hnodup2 at bottom.
clear Hnoduproot Hk.
induction (getTablePages root tableSize s);  [ 
now contradict Hproot | ].
simpl in *.
destruct Hproot as [Hproot | Hproot];
destruct Hp0root as [Hp0root | Hp0root]; subst.
+ subst. now contradict Hp0p.
+ apply NoDupSplitInclIff in Hnodup2. 
  destruct Hnodup2 as ((Hnodup1 & Hnodup2) & Hdisjoint).
  unfold disjoint in Hdisjoint. subst. clear IHl.
  generalize (Hdisjoint x Hxp);clear Hdisjoint; intros Hdisjoint.
  apply notInFlatMapNotInGetIndirection with l; trivial.
+ apply NoDupSplitInclIff in Hnodup2. 
  destruct Hnodup2 as ((Hnodup1 & Hnodup2) & Hdisjoint).
  unfold disjoint in Hdisjoint. subst.
  unfold not. intros Hxp0. contradict Hxp.
  generalize (Hdisjoint x Hxp0);clear Hdisjoint; intros Hdisjoint.
  apply notInFlatMapNotInGetIndirection with l; trivial.
+ apply IHl; trivial. 
  apply NoDupSplit in Hnodup2.
  destruct Hnodup2. assumption.
Qed.

Lemma getIndirectionInGetIndirectionAuxMinus1 table (p: page) s n va1 pred n1 (level1 : level):
level1> 0 -> 
(Nat.eqb pageDefault p) = false ->  
level1 <= CLevel (n -1) -> 
StateLib.Level.pred level1 = Some pred -> 
table <> pageDefault -> 
n <= nbLevel -> 
n > 1 -> 
getIndirection p va1 pred n1 s = Some table -> 
In table (getIndirectionsAux p s (n - 1)). 
Proof.
intros Hfstlevel Hnotnull Hlevel Hpred Hnotnullt Hnbl Hn Hind.
apply getIndirectionInGetIndirections 
with va1 pred n1;trivial;  try lia.
  - apply levelPredMinus1 in Hpred; trivial.
    unfold CLevel in Hpred. 
    case_eq(lt_dec (level1 - 1) nbLevel ); intros l Hl0;  
    rewrite Hl0 in Hpred.
    simpl in *.
    inversion Hpred. subst.
    simpl in *.
    
    (* clear  Htableroot2 Htableroot1  
    Hread2  Hread1 HNoDup2 HNoDup1
    Hnull1 Hnull2 Hnotnull2 Hnotnull1 Hroot2 Hroot1. *)
    unfold CLevel in *.
    destruct level1.
    simpl in *. 
    
    case_eq (lt_dec (n - 1) nbLevel); 
    intros ii Hii;  rewrite Hii in *.
    simpl in *.
    case_eq (lt_dec (n - 1 - 1) nbLevel);
    intros.
    simpl in *. lia. lia.  
    case_eq (lt_dec (n - 1 - 1) nbLevel);
    intros.
    simpl in *. lia. lia.
    destruct level1. 
    simpl in *. lia. 
    unfold levelEq.
    unfold CLevel. 
    case_eq(lt_dec (n - 1) nbLevel ); intros;
    simpl in *.
    unfold levelMin. unfold CLevel.
    case_eq(lt_dec 0 nbLevel).
    intros. simpl.
    apply NPeano.Nat.eqb_neq. lia.
    intros. assert (0 < nbLevel) by apply nbLevelNotZero.
    lia. lia.
  - apply beq_nat_false in Hnotnull. unfold not. intros.
    apply Hnotnull. subst. trivial. 
Qed.
    
Lemma getTablePagesNoDup root (p p0 : page) idx1 idx2    s:
idx1 < tableSize -> idx2 < tableSize ->
NoDup (getTablePages root tableSize s) -> 
StateLib.readPhyEntry root (CIndex idx1) (memory s) = Some p0 -> 
StateLib.readPhyEntry root (CIndex idx2) (memory s) = Some p -> 
(Nat.eqb idx1 idx2) = false ->
(Nat.eqb p pageDefault) = false -> 
(Nat.eqb pageDefault p0) = false -> 
p0 <> p.
Proof.
assert (H: tableSize <= tableSize) by lia; revert H.
generalize tableSize at 1 3 4 5  .
induction n.
+ intros. now contradict H0.
+ intros. simpl in *.
  apply beq_nat_false in H5. 
  assert(Hdec : (idx1 = n /\ idx2 <> n) \/ 
          (idx2 = n /\ idx1 <> n) \/ 
          (idx1 <> n /\ idx2 <> n)). lia.
  destruct Hdec as [(Hdec1 & Hdec2) | [(Hdec1 & Hdec2) |(Hdec1 & Hdec2)]];
  subst.
  * unfold StateLib.readPhyEntry in H3. intros.
    case_eq (lookup root (CIndex n) (memory s) pageEq idxEq); 
    [ intros v Hv'| intros Hv'] ; rewrite Hv' in  *; [ | now contradict H3 ];
    destruct v; try now contradict H3. inversion H3. subst.
    subst.  clear IHn H3. rewrite PeanoNat.Nat.eqb_sym in H7.
    rewrite H7 in H2.
    apply NoDupSplitInclIff in H2.
    destruct H2 as ( (_ & _) & H2).
    unfold disjoint in H2.
    assert (In p (getTablePages root n s)).
    apply readPhyEntryInGetTablePages with idx2; trivial.
    lia. lia. 
    unfold not. intros. subst. apply beq_nat_false in H6.
    now contradict H6.
    apply H2 in H3. unfold not. intros.
    contradict H3. simpl in *. left. assumption.
  * unfold StateLib.readPhyEntry in H4. intros.
    case_eq (lookup root (CIndex n) (memory s) pageEq idxEq); 
    [ intros v Hv'| intros Hv'] ; rewrite Hv' in  *; [ | now contradict H4 ];
    destruct v; try now contradict H4. inversion H4. subst.
    subst.  clear IHn H4. rewrite H6 in H2.
    apply NoDupSplitInclIff in H2.
    destruct H2 as ( (_ & _) & H2).
    unfold disjoint in H2.
    assert (In p0 (getTablePages root n s)).
    apply readPhyEntryInGetTablePages with idx1; trivial.
    lia. lia. 
    unfold not. intros. subst. apply beq_nat_false in H7.
    now contradict H7.
    apply H2 in H4. unfold not. intros.
    contradict H4. simpl in *. left. rewrite H8. trivial.
  *  case_eq (lookup root (CIndex n) (memory s) pageEq idxEq); 
    [ intros v Hv'| intros Hv'] ; rewrite Hv' in  *;
    
    [ |
    apply IHn; trivial;try lia;
    apply PeanoNat.Nat.eqb_neq; trivial ].
    destruct v; apply IHn;
                try assumption;
                try apply PeanoNat.Nat.eqb_neq; try assumption;
                try lia.
    case_eq(Nat.eqb pageDefault (pa p1)); intros Hnull; rewrite PeanoNat.Nat.eqb_sym in Hnull ; rewrite Hnull in *; trivial.
    apply NoDupSplitInclIff in H2; intuition.
Qed.

Lemma getTablePagesNoDupFlatMap s n k root: 
n > 0 -> 
NoDup
(flat_map (fun p : page => getIndirectionsAux p s n)
(getTablePages root k s)) -> 
NoDup (getTablePages root k s).
Proof. 
induction (getTablePages root k s).
simpl in *. trivial.
simpl.
intros Hn H.
apply NoDup_cons_iff.
apply NoDupSplitInclIff in H.
destruct H as((H1 & H2) & H3).
split.
unfold disjoint in *.
generalize (H3 a ); clear H3; intros H3.
assert (~ In a (flat_map (fun p : page => getIndirectionsAux p s n) l)).
apply H3; trivial.
destruct n. simpl in *. lia.
simpl. left. trivial.
unfold not. contradict H.
apply in_flat_map. exists a.
split. assumption. destruct n; simpl. now contradict Hn.
left. trivial.  
apply IHl; trivial.
Qed. 

   Lemma getIndirectionGetTableRoot2 (s : state) sh2 currentPart pt va 
nbL : 
StateLib.getSndShadow currentPart (memory s) = Some sh2 -> 
StateLib.getNbLevel = Some nbL -> 
(forall idx : index,
  StateLib.getIndexOfAddr va levelMin = idx ->
  isVA pt idx s /\ 
  getTableAddrRoot pt idxShadow2 currentPart va s) 
  -> 
getIndirection sh2 va nbL (nbLevel - 1) s = Some pt. 
Proof.
intros.
destruct H1 with (StateLib.getIndexOfAddr va levelMin );
trivial.
clear H1.
unfold getTableAddrRoot in *.
destruct H3 as (_ & H3).
rewrite <- nextEntryIsPPgetSndShadow in *.
apply H3 in H.
clear H3.
destruct H as (nbl & HnbL & stop & Hstop & Hind).
subst.
rewrite H0 in HnbL.
inversion HnbL;subst.
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
lia.
symmetry in H0. 
apply getNbLevelEq in H0.
subst.
apply nbLevelEq.
Qed.

Lemma pageTablesOrIndicesAreDifferent (root1 root2 table1 table2 : page ) 
(va1 va2 : vaddr) (level1 : level)  (stop : nat)  s:
root1 <> pageDefault -> root2 <> pageDefault -> 
NoDup (getIndirections root1 s) ->
NoDup (getIndirections root2 s) -> 
StateLib.checkVAddrsEqualityWOOffset stop va1 va2 level1 = false -> 
( (level1 = CLevel (nbLevel -1) /\ root1 = root2) \/ (level1 < CLevel (nbLevel -1) /\(
(disjoint (getIndirections root1 s) (getIndirections root2 s)/\ root1 <> root2) \/ root1 = root2  )) )-> 
table1 <> pageDefault -> 
table2 <> pageDefault -> 
(* stop > 0 ->  *)
getIndirection root1 va1 level1 stop s = Some table1-> 
getIndirection root2 va2 level1 stop s = Some table2 -> 
table1 <> table2 \/ StateLib.getIndexOfAddr va1 levelMin <> StateLib.getIndexOfAddr va2 levelMin.
Proof.
intros Hroot1 Hroot2 HNoDup1 HNoDup2 Hvas  Hlevel 
Hnotnull1 Hnotnull2  (* Hstop *) Htableroot1    Htableroot2.
assert (levelEq level1 levelMin = true \/ levelEq level1 levelMin = false).
{ unfold levelEq.
        rewrite NPeano.Nat.eqb_eq.  rewrite NPeano.Nat.eqb_neq.
        lia. }
assert(StateLib.getIndexOfAddr va1 levelMin <> StateLib.getIndexOfAddr va2 levelMin \/ 
StateLib.getIndexOfAddr va1 levelMin = StateLib.getIndexOfAddr va2 levelMin).
{ destruct (StateLib.getIndexOfAddr va1 levelMin), (StateLib.getIndexOfAddr va2 levelMin ) .
  assert (i = i0 \/ i<> i0). lia.
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
+ clear H.
  revert HNoDup1 HNoDup2 Hvas Hlevel Hnotnull1 Hnotnull2 
  Htableroot1 (* Hstop *) Htableroot2 H0 Hroot1 Hroot2 .
  revert root1 root2 table1 table2 level1 va1 va2.
  assert (Hs :stop <= stop). lia. revert Hs.  
  generalize stop at 1 3 4 5 .
  intros.
  destruct stop0.
  simpl in *.
  now contradict Hvas.
  assert (nbLevel <= nbLevel) as Hnbl by lia.
  revert Hnbl.
  revert HNoDup1 HNoDup2 Hvas Hlevel Hnotnull1 Hnotnull2 
  Htableroot1 (* Hstop *) Htableroot2 H0 Hs Hroot1 Hroot2 (* Hroot12 *).
  revert root1 root2 table1 table2 level1 va1 va2 stop.
  unfold getIndirections.
  generalize nbLevel at 1 2 3 4 5 6 7. 
  induction (S stop0).
  intros. simpl in *. now contradict Hvas.
  intros.
  simpl in *.
  case_eq (levelEq level1 levelMin); intros . rewrite H in *.
  - contradict Hvas. 
    apply levelEqBEqNatTrue in H. subst.
    unfold not.
    intros. apply beq_nat_false in H.  contradict H. rewrite H0. reflexivity.
  - rewrite H in *.
    clear H. 
    case_eq (StateLib.readPhyEntry root1 (StateLib.getIndexOfAddr va1 level1) (memory s)) ;
    [intros p Hread1 | intros Hread1];
    rewrite Hread1 in *; [ | inversion Htableroot1].   
    case_eq (StateLib.readPhyEntry root2 (StateLib.getIndexOfAddr va2 level1) (memory s) );
    [intros p0 Hread2 | intros Hread2];
    rewrite Hread2 in *; [ | inversion Htableroot2].
    case_eq (Nat.eqb pageDefault p); intros Hnull1;
    rewrite Hnull1 in *.
    inversion Htableroot1.
    subst. now contradict Hnotnull1.
    case_eq (Nat.eqb pageDefault p0); intros Hnull2;
    rewrite Hnull2 in *.
    inversion Htableroot2.
    subst. now contradict Hnotnull2.
    case_eq(StateLib.Level.pred level1); [intros pred Hpred | intros Hpred];  rewrite Hpred in *; 
    [ | inversion Htableroot1].     
    case_eq (Nat.eqb (StateLib.getIndexOfAddr va1 level1)
                     (StateLib.getIndexOfAddr va2 level1)
            );intros Hidx;
            rewrite Hidx in Hvas; trivial. 
    * generalize (IHn (n0 -1) p p0 table1 table2 pred va1 va2 stop); clear IHn; intros IHn.
      assert (levelEq level1 levelMin = true \/ levelEq level1 levelMin = false).
      { unfold levelEq.
        rewrite NPeano.Nat.eqb_eq.  rewrite NPeano.Nat.eqb_neq.
        lia. }
      destruct H.
      { apply levelEqBEqNatTrue in H. subst.
        unfold StateLib.Level.pred in Hpred.
        unfold levelMin in Hpred.
        unfold CLevel in Hpred.
        case_eq (lt_dec 0 nbLevel ); intros;
        rewrite H in Hpred; [simpl in *;inversion Hpred |
        assert (0 < nbLevel) by apply nbLevelNotZero;
        now contradict H1]. }
      { apply IHn;trivial; try lia; clear IHn.
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
            simpl in *. lia. lia.
            destruct level1.
            simpl in *.
            lia.
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
                  
                  lia. lia.  
                case_eq (lt_dec (n0 - 1 - 1) nbLevel);
                intros.
                simpl in *. lia. lia.
                destruct level1. simpl in *. lia. }
              { assert (n0 <= 1 \/ n0 > 1) as Hn0. lia.
                destruct Hn0.
                apply levelEqBEqNatFalse0 in H.
                assert (CLevel
                (n0 - 1) > 1).
                lia.
                contradict H1.
                unfold CLevel in Hlevellt, H2.
                case_eq ( lt_dec (n0 - 1) nbLevel); intros;  rewrite H1 in *;
                simpl in *. lia.
                apply le_lt_or_eq in Hnbl.
                destruct Hnbl.
                lia.
                assert (n0 > 0).
                assert (0 < nbLevel) by apply nbLevelNotZero.
                lia.
                lia.
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
              simpl in *. lia. lia.  
              case_eq (lt_dec (n0 - 1 - 1) nbLevel);
              intros;
              simpl in *. contradict H0. lia. lia.
              destruct level1. simpl in *. lia.
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
          contradict Hnull2. subst. trivial. }
    * clear IHn. 
      left. clear stop0 stop (* Hstop *) Hs Hvas . 
      destruct Hlevel as [(Hlevel& Hroot) | (Hlevel& [(Hroot & Heq) | Hroot] ) ]; subst.
      { assert (n0 <= 1 \/ n0 > 1) as Hn0. lia.
        destruct Hn0 as [Hn0 | Hn0].
        + assert(n0 = 0 \/ n0 =1) as Hn01. lia.
          destruct Hn01;subst;  simpl in *;
          unfold StateLib.Level.pred in *; [
          case_eq(gt_dec (CLevel 0) 0 ); intros g Hnb0;rewrite Hnb0 in Hpred;
          [ | now contradict Hpred];
          unfold CLevel in g |]. 
          case_eq (lt_dec 0 nbLevel); intros nbl0 Hnbl0;
          [ |
          assert(0 < nbLevel) by apply nbLevelNotZero; lia].
          clear Hpred Hnb0. 
          rewrite Hnbl0 in *; simpl in *.  now contradict g.
          case_eq(gt_dec (CLevel 0) 0 ); intros g Hnb0;rewrite Hnb0 in Hpred;
          [ | 
          now contradict Hpred].
          unfold CLevel in g.
          case_eq (lt_dec 0 nbLevel); intros nbl0 Hnbl0; [ |
          assert(0 < nbLevel) by apply nbLevelNotZero; lia].
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
          apply getTablePagesNoDupFlatMap  with n0; trivial. lia.
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
          now contradict Hnull1. }
          
(*           apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *. *)
(*           apply beq_nat_false in Hnull2. now contradict Hnull2. } *)
        assert( disjoint (getIndirectionsAux p s (n0 -1)) 
       (getIndirectionsAux p0 s (n0 -1))) as Hdisjoint.
         apply disjointGetIndirectionsAuxMiddle with root2
         (StateLib.getIndexOfAddr va2 (CLevel (n0 - 1)))
         (StateLib.getIndexOfAddr va1 (CLevel (n0 - 1))) ; trivial. 
         assert (In table1 (getIndirectionsAux  p s (n0 -1))) as Htbl1p.
         apply getIndirectionInGetIndirectionAuxMinus1 with va1 pred n (CLevel (n0 - 1)); trivial.
         unfold CLevel.
         case_eq( lt_dec (n0 - 1) nbLevel). intros. simpl.
         lia.
         intros.
         contradict H1. lia.
         assert (In table2 (getIndirectionsAux  p0 s (n0 -1))) as Htb2p0.
         apply getIndirectionInGetIndirectionAuxMinus1 with va2 pred n (CLevel (n0 - 1)); trivial.
         unfold CLevel.
         case_eq( lt_dec (n0 - 1) nbLevel). intros. simpl.
         lia.
         intros.
         contradict H1. lia.
         unfold disjoint in *.
         apply Hdisjoint in Htbl1p.
         unfold not. intros.
         apply Htbl1p. subst.
         assumption. }
      { assert (n0 <= 1 \/ n0 > 1) as Hn0. lia.
        destruct Hn0 as [Hn0 | Hn0].
        + assert(n0 = 0 \/ n0 =1) as Hn01. lia.
          destruct Hn01;subst;  simpl in *;
          destruct level1; simpl in *;
          unfold CLevel in Hlevel; 
          case_eq ( lt_dec 0 nbLevel); intros; rewrite H in *;
          simpl in *; lia.
        +  assert (level1 > 0). 
             {unfold StateLib.Level.pred in *.
         case_eq (  gt_dec level1 0) ; intros;
         rewrite H in *.
         inversion Hpred.
         destruct pred.
         destruct level1. simpl in *.
         inversion H2. lia.
         inversion Hpred.
         }
        assert (In table1 (getIndirectionsAux  p s (n0 -1))) as Htbl1p.
         apply getIndirectionInGetIndirectionAuxMinus1 with va1 pred n level1; trivial.
         lia.
          assert (In table2 (getIndirectionsAux  p0 s (n0 -1))) as Htbl2p0.
         apply getIndirectionInGetIndirectionAuxMinus1 with va2 pred n level1; trivial.
          lia.

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
        { assert (n0 <= 1 \/ n0 > 1) as Hn0. lia.
        destruct Hn0 as [Hn0 | Hn0].
        + assert(n0 = 0 \/ n0 =1) as Hn01. lia.
        destruct Hn01;subst;  simpl in *;
          destruct level1; simpl in *;
          unfold CLevel in Hlevel; 
          case_eq ( lt_dec 0 nbLevel); intros; rewrite H in *;
          simpl in *; lia.
          
       + assert( p0 <> p).
         { apply getTablePagesNoDup with root2 (StateLib.getIndexOfAddr va2 level1)
          (StateLib.getIndexOfAddr va1 level1) s; trivial.  
          destruct (StateLib.getIndexOfAddr va2 level1). simpl in *; trivial.
          destruct (StateLib.getIndexOfAddr va1 level1). simpl in *; trivial.
          destruct n0; [now contradict Hn0 |].
          simpl in HNoDup2. apply NoDup_cons_iff in HNoDup2.
          destruct HNoDup2 as (_ & HNoDup2).
          apply getTablePagesNoDupFlatMap  with n0; trivial. lia.
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
          now contradict Hnull1. }
(*           apply NPeano.Nat.eqb_neq. unfold not. intros. rewrite H in *. *)
(*           apply beq_nat_false in Hnull2. now contradict Hnull2. } *)
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
         inversion H3. lia.
         inversion Hpred.
         lia.
         assert (In table2 (getIndirectionsAux  p0 s (n0 -1))) as Htb2p0.
         apply getIndirectionInGetIndirectionAuxMinus1 with va2 pred n level1; trivial.
         unfold StateLib.Level.pred in *.
         case_eq (  gt_dec level1 0) ; intros;
         rewrite H1 in *.
         inversion Hpred.
         destruct pred.
         destruct level1. simpl in *.
         inversion H3. lia.
         inversion Hpred.
         lia.
         unfold disjoint in *.
         apply Hdisjoint in Htbl1p.
         unfold not. intros.
         apply Htbl1p. subst.
         assumption. }
Qed. 
Lemma noDupConfigPagesListNoDupGetIndirections  s:
partitionDescriptorEntry s -> 
forall (partition : page),  
In partition (getPartitions pageRootPartition s) -> 
NoDup (getConfigPages partition s) -> 
forall root idxroot, (idxroot = idxPageDir \/ idxroot = idxShadow1 \/ idxroot = idxShadow2) -> 
nextEntryIsPP partition idxroot root s->
 NoDup (getIndirections root s).
 Proof.
 intros Hpde partition Hpart Hnodup root idx Hidx Hpp.
 unfold getConfigPages in *. 
 apply NoDup_cons_iff in Hnodup as (Hnotin & Hnodup).
 unfold getConfigPagesAux in Hnodup.
   unfold consistency in *.
  assert (Hroots : 
   (exists pd , StateLib.getPd partition (memory s) = Some pd /\
    pd <> pageDefault) /\ 
   (exists sh1, StateLib.getFstShadow partition (memory s) = Some sh1 /\
    sh1 <> pageDefault) /\ 
   (exists sh2, StateLib.getSndShadow partition (memory s) = Some sh2 /\ 
    sh2 <> pageDefault) /\ 
   (exists list, StateLib.getConfigTablesLinkedList partition (memory s) = Some list /\ 
    list <> pageDefault)).
  apply pdSh1Sh2ListExistsNotNull; trivial.
  destruct Hroots as ((pd & Hpd & Hpdnotnull) 
  & (sh1 & Hsh1 & Hsh1notnull) & (sh2 & Hsh2 & Hsh2notnull) & 
  (sh3 & Hsh3 & Hsh3notnull)).
  rewrite Hpd, Hsh1, Hsh2, Hsh3 in *.
  apply NoDupSplitInclIff in Hnodup as ((Hi1 & Hnodup) & _).
  apply NoDupSplitInclIff in Hnodup as ((Hi2 & Hnodup) & _).
  apply NoDupSplitInclIff in Hnodup as ((Hi3 & Hnodup) & _).
  destruct Hidx as [Hpdroot | [Hsh1root | Hsh2root]];subst.
  assert(root = pd).
  apply getPdNextEntryIsPPEq with partition s;trivial.
  subst;trivial.
  assert(root = sh1).
  apply getSh1NextEntryIsPPEq with partition s;trivial.
  subst;trivial.
  assert(root = sh2).
  apply getSh2NextEntryIsPPEq with partition s;trivial.
  subst;trivial. 
 Qed.

Lemma toApplyPageTablesOrIndicesAreDifferent idx1 idx2 va1 va2 (table1 table2 : page) 
currentPart root idxroot level1 F s: 
(idxroot = idxPageDir \/ idxroot = idxShadow1 \/ idxroot = idxShadow2) -> 
(Nat.eqb pageDefault table1) = false -> (Nat.eqb pageDefault table2) = false -> 
false = StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 level1 -> 
currentPart = currentPartition s -> 
consistency s -> 
StateLib.getIndexOfAddr va1 levelMin = idx1 -> 
StateLib.getIndexOfAddr va2 levelMin = idx2 -> 
(forall idx : index,
StateLib.getIndexOfAddr va1 levelMin = idx ->
F table1 idx s /\ getTableAddrRoot table1 idxroot currentPart va1 s) -> 
(forall idx : index,
StateLib.getIndexOfAddr va2 levelMin = idx ->
F table2 idx s /\ getTableAddrRoot table2 idxroot currentPart va2 s) -> 
nextEntryIsPP currentPart idxroot root s -> 
Some level1 = StateLib.getNbLevel -> 
table1 <> table2 \/ idx1 <> idx2. 
Proof. 
 intros Hor Hnotnull1 Hnotnull2 Hvas Hcurpart Hcons Hva1 Hva2 Htable1 Htable2 Hroot Hlevel.              
 rewrite <- Hva1.
  rewrite <- Hva2.
  apply Htable1 in Hva1.
  apply Htable2 in Hva2.
  unfold getTableAddrRoot in *.
  destruct Hva1 as (Hpe1 & Hor1 & Htableroot1). 
  destruct Hva2 as (Hpe2 & Hor2 & Htableroot2).
  generalize (Htableroot1 root Hroot); clear Htableroot1;intros Htableroot1.
  generalize (Htableroot2 root Hroot); clear Htableroot2;intros Htableroot2.
  destruct Htableroot1 as (nbl1 & Hnbl1 & stop1 & Hstop1 & Hind1). 
  destruct Htableroot2 as (nbl2 & Hnbl2 & stop2 & Hstop2 & Hind2).
  rewrite <- Hlevel in Hnbl1.
  inversion Hnbl1 as [Hi0]. 
  rewrite <- Hlevel in Hnbl2.
  inversion Hnbl2 as [Hi1 ].
  rewrite Hi1 in Hind2.
  rewrite Hi0 in Hind1.  
  rewrite Hi1 in Hstop2.
  rewrite Hi0 in Hstop1.
  rewrite <- Hstop2 in Hstop1.
  rewrite Hstop1 in Hind1.
  clear Hstop1 Hnbl2 Hnbl1 .
   apply  pageTablesOrIndicesAreDifferent with root root  
  level1 stop2 s; trivial.
  - unfold consistency in *.
    destruct Hcons.
    unfold partitionDescriptorEntry in *.
    assert (currentPartitionInPartitionsList s ) as Hpr by intuition.
    unfold currentPartitionInPartitionsList in *.
    subst.
    generalize (H  (currentPartition s)  Hpr); clear H; intros H.
    assert (idxroot = idxPageDir \/
      idxroot = idxShadow1 \/ idxroot = idxShadow2 \/ idxroot = idxShadow3 \/ idxroot = idxParentDesc 
      \/ idxroot = idxPartDesc) as Hpd .
    intuition.
    apply H in Hpd.
    destruct Hpd as (_ & _ & Hpd).
    destruct Hpd as (pd & Hrootpd & Hnotnul).
    move Hroot at bottom.
    move Hrootpd  at bottom.
    move Hnotnul at bottom.
    unfold nextEntryIsPP in Hroot , Hrootpd.
    destruct (StateLib.Index.succ idxroot); try now contradict Hrootpd.
    destruct (lookup (currentPartition s) i (memory s) pageEq idxEq); try now contradict Hroot.
    destruct v; try now contradict Hrootpd.
    subst. assumption.
  - unfold consistency in *.
    destruct Hcons.
    unfold partitionDescriptorEntry in *.
    assert (currentPartitionInPartitionsList s ) as Hpr by intuition.
    unfold currentPartitionInPartitionsList in *.
    subst.
    generalize (H  (currentPartition s)  Hpr); clear H; intros H.
    assert (idxroot = idxPageDir \/
      idxroot = idxShadow1 \/ idxroot = idxShadow2 \/ idxroot = idxShadow3 \/ idxroot = idxParentDesc 
      \/ idxroot = idxPartDesc) as Hpd .
    intuition.
    apply H in Hpd.
    destruct Hpd as (_ & _ & Hpd).
    destruct Hpd as (pd & Hrootpd & Hnotnul).
    move Hroot at bottom.
    move Hrootpd  at bottom.
    move Hnotnul at bottom.
    unfold nextEntryIsPP in Hroot , Hrootpd.
    destruct (StateLib.Index.succ idxroot); try now contradict Hrootpd.
    destruct (lookup (currentPartition s) i (memory s) pageEq idxEq); try now contradict Hroot.
    destruct v; try now contradict Hrootpd.
    subst. assumption.
  - unfold consistency in Hcons.
    assert(Hpde : partitionDescriptorEntry s) by intuition.
    assert(Hdup :   noDupConfigPagesList s) by intuition.
    assert(Hcurprt : currentPartitionInPartitionsList s ) by intuition.
    apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) idxroot;trivial.
    apply Hdup;trivial.
    subst. trivial.
  - unfold consistency in Hcons.
    assert(Hpde : partitionDescriptorEntry s) by intuition.
    assert(Hdup :   noDupConfigPagesList s) by intuition.
    assert(Hcurprt : currentPartitionInPartitionsList s ) by intuition.
    apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) idxroot;trivial.
    apply Hdup;trivial.
    subst. trivial.
  - move Hlevel at bottom.
    unfold StateLib.getNbLevel in Hlevel.
     case_eq (gt_dec nbLevel 0 ); intros;
    rewrite H in Hlevel.
    rewrite Hstop2.
    inversion Hlevel.
    rewrite H1 in *. simpl.
    symmetry. assert( (nbLevel - 1 + 1)  = nbLevel).
    lia. rewrite H0.
    assumption.
    now contradict H.
  - left. split.
    unfold StateLib.getNbLevel in *.
    move Hlevel at bottom.
    unfold CLevel.
    case_eq (gt_dec nbLevel 0); intros.
    rewrite H in Hlevel.
    inversion Hlevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel ); intros.
    subst.
    assert(MAL.getNbLevel_obligation_1 g  =  ADT.CLevel_obligation_1 (nbLevel - 1) l)
    by apply proof_irrelevance.
    rewrite H1. reflexivity. lia.
    assert (0 < nbLevel) by apply nbLevelNotZero. lia.
    trivial.
  - apply beq_nat_false in Hnotnull1.
    unfold not. intros.
    contradict Hnotnull1. subst. trivial.
  - apply beq_nat_false in Hnotnull2.
    unfold not. intros.
    contradict Hnotnull2. subst. trivial.
Qed.

Lemma getMappedPagesAuxConsSome :
forall pd va phyVa listva s, 
getMappedPage pd s va = SomePage phyVa ->  
 (getMappedPagesAux pd (va :: listva) s) =
 phyVa :: (getMappedPagesAux pd  listva) s. 
Proof.
 intros pd va phyVa listva.
 revert   pd va phyVa.
 induction listva;intros;
   unfold getMappedPagesAux;
   unfold getMappedPagesOption.
   simpl.
   rewrite H;trivial.
 + simpl. rewrite H.
   trivial.
Qed.

Lemma getMappedPagesAuxConsNone :
 forall pd va listva s, 
getMappedPage pd s va = NonePage ->   
 (getMappedPagesAux pd (va :: listva) s) =(getMappedPagesAux pd  listva) s.
Proof.
intros pd va phyVa listva.
revert   pd va phyVa.
induction listva;intros;
unfold getMappedPagesAux;
unfold getMappedPagesOption.
simpl.
rewrite H;trivial.
Qed.

Lemma getMappedPagesAuxConsDefault :
 forall pd va listva s, 
getMappedPage pd s va = SomeDefault ->   
 (getMappedPagesAux pd (va :: listva) s) =(getMappedPagesAux pd  listva) s.
Proof.
intros pd va phyVa listva.
revert   pd va phyVa.
induction listva;intros;
unfold getMappedPagesAux;
unfold getMappedPagesOption.
simpl.
rewrite H;trivial.
Qed.


Lemma childIsMappedPage partition child s :
In partition (getPartitions pageRootPartition s) -> 
In child (getChildren partition s) -> 
In child (getMappedPages partition s).
Proof.
intros Hpart Hchild.
unfold getChildren in *.
unfold getMappedPages.
case_eq (StateLib.getNbLevel );[intros nbL HnbL|intros HnbL];rewrite HnbL in *;
try now contradict Hchild.
case_eq (StateLib.getPd partition (memory s) );[intros pd Hpd | intros Hpd]; 
rewrite Hpd in *; try now contradict Hpd.
unfold getMappedPagesAux in *.
rewrite filterOptionInIff in *.
unfold getMappedPagesOption in *.
rewrite in_map_iff in *.
destruct Hchild as (va & Hva1 & Hva2).
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel va va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1i & Hva11).  
exists va1;split;trivial.
rewrite <- Hva1.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.
Qed.

Lemma ancestorInPartitionTree s:
parentInPartitionList s -> 
isChild s -> 
forall partition ancestor ,
In partition (getPartitions pageRootPartition s) -> 
In ancestor (getAncestors partition s) -> 
In ancestor (getPartitions pageRootPartition s).
Proof.
intros Hparent HisChild.
unfold getAncestors.
induction (nbPage + 1);simpl;trivial.
intuition.
intros  partition ancestor Hi1 Hi2.
case_eq(StateLib.getParent partition (memory s) );intros;
rewrite H in *;
simpl in *.
+ destruct Hi2 as [Hi2 | Hi2].
  - subst.
    unfold parentInPartitionList in *.
    apply Hparent with partition;trivial.
    apply nextEntryIsPPgetParent;trivial.
  - apply IHn with p;trivial.
    unfold parentInPartitionList in *.
    apply Hparent with partition;trivial.
    apply nextEntryIsPPgetParent;trivial.
+  now contradict Hi2.
Qed.

Lemma getPartitionAuxSn s : 
isChild s -> 
forall n child parent ancestor, 
In child (getPartitions pageRootPartition s) ->
StateLib.getParent child (memory s) = Some parent -> 
In parent (getPartitionAux ancestor s n) -> 
In child (flat_map (fun p : page => getPartitionAux p s n) (getChildren ancestor s)).
Proof.
intros Hchild .
induction n. simpl in *. intuition.
simpl.
intros.
destruct H1. subst.
rewrite  in_flat_map.
exists child.
split. unfold isChild in *.
apply Hchild;trivial.
simpl. left;trivial.
rewrite in_flat_map.
rewrite in_flat_map in H1.
destruct H1 as (x & Hx & Hxx).
exists x;split;trivial.
simpl.
right.
apply IHn with parent;trivial.
Qed.



Lemma getPartitionAuxSbound s bound : 
forall partition1 partition2, In partition1 (getPartitionAux partition2 s bound) ->
In partition1 (getPartitionAux partition2 s (bound+1)).
Proof.
induction bound;simpl; intros.
now contradict H.
destruct H. 
left ;trivial.
right.
rewrite in_flat_map in *.
destruct H as (x & Hx & Hxx).
exists x;split;trivial.
apply IHbound;trivial.  
Qed.

Lemma idxSh2idxSh1notEq : idxShadow2 <> idxShadow1. Proof.  
unfold idxShadow2. unfold idxShadow1.
apply indexEqFalse ;
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
lia.  apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
lia. apply tableSizeBigEnough. lia. Qed.

Lemma idxPDidxSh1notEq : 
idxPageDir <> idxShadow1.
Proof.
unfold idxPageDir. unfold idxShadow1.
apply indexEqFalse ;
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
lia.  apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
lia. apply tableSizeBigEnough. lia.
Qed. 

Lemma rootStructNotNull root part s idxroot: 
idxroot = idxPageDir \/
idxroot = idxShadow1 \/
idxroot = idxShadow2 \/ idxroot = idxShadow3 \/ idxroot = idxParentDesc \/ idxroot = idxPartDesc -> 
partitionDescriptorEntry s -> 
nextEntryIsPP part idxroot root s -> 
In part (getPartitions pageRootPartition s) -> 
root <> pageDefault.
Proof.
intros. 
unfold partitionDescriptorEntry in *.
assert((exists entry : page,
        nextEntryIsPP part idxroot entry s /\ entry <> pageDefault))
        as (entry & Hentry & Hdefault).
apply H0;trivial.
assert(entry = root).
unfold  nextEntryIsPP in *.
destruct (StateLib.Index.succ idxroot);try now contradict Hentry.
destruct(lookup part i (memory s) pageEq idxEq);try now contradict Hentry.
destruct v;try now contradict Hentry.
subst;trivial.
subst.
trivial.
Qed.
 Lemma checkVAddrsEqualityWOOffsetTrue1 s phyDescChild vaChild va level: 
      In va (getPdsVAddr phyDescChild level getAllVAddr s) ->
StateLib.checkVAddrsEqualityWOOffset nbLevel vaChild va level = true ->
StateLib.getNbLevel = Some level ->
In vaChild (getPdsVAddr phyDescChild level getAllVAddr s).
Proof.
      unfold getPdsVAddr.
      intros.
      rewrite filter_In in *.
      destruct H.
      split. 
      apply AllVAddrAll.
      unfold checkChild in *. 
      destruct (StateLib.getFstShadow phyDescChild (memory s) );trivial.
      assert(Hind : getIndirection p vaChild level (nbLevel - 1) s =
      getIndirection p va level (nbLevel - 1) s). 
      apply getIndirectionEq;trivial.
      apply getNbLevelLt;trivial.
      rewrite Hind.
      destruct (getIndirection p va level (nbLevel - 1) s);trivial.
      destruct (Nat.eqb p0 pageDefault);trivial.
      assert (idxeq :  (StateLib.getIndexOfAddr vaChild levelMin) = 
      (StateLib.getIndexOfAddr va levelMin)). 
     apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level;trivial .
    apply fstLevelLe.
    apply getNbLevelLt;trivial.
    rewrite idxeq;trivial.
Qed.





Lemma pdPartNotNull phyDescChild pdChildphy s:
In phyDescChild (getPartitions pageRootPartition s) -> 
nextEntryIsPP phyDescChild idxPageDir pdChildphy s -> 
partitionDescriptorEntry s -> 
pdChildphy <> pageDefault.
Proof.
intros. 
 unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP phyDescChild idxPageDir entry s /\ entry <> pageDefault)).
        apply H1;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pdChildphy).
apply getPdNextEntryIsPPEq  with phyDescChild s;trivial.
apply nextEntryIsPPgetPd;trivial.
subst;trivial.
Qed.
Lemma sh1PartNotNull phyDescChild pdChildphy s:
In phyDescChild (getPartitions pageRootPartition s) -> 
nextEntryIsPP phyDescChild idxShadow1 pdChildphy s -> 
partitionDescriptorEntry s -> 
pdChildphy <> pageDefault.
Proof.
intros. 
 unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP phyDescChild idxShadow1 entry s /\ entry <> pageDefault)).
        apply H1;trivial.
        right;left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pdChildphy).
apply getSh1NextEntryIsPPEq with phyDescChild s;trivial.
apply nextEntryIsPPgetFstShadow;trivial.
subst;trivial.
Qed.

Lemma sh2PartNotNull phyDescChild pdChildphy s:
In phyDescChild (getPartitions pageRootPartition s) -> 
nextEntryIsPP phyDescChild idxShadow2 pdChildphy s -> 
partitionDescriptorEntry s -> 
pdChildphy <> pageDefault.
Proof.
intros. 
 unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP phyDescChild idxShadow2 entry s /\ entry <> pageDefault)).
        apply H1;trivial.
        do 2 right;left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pdChildphy).
apply getSh2NextEntryIsPPEq with phyDescChild s;trivial.
apply nextEntryIsPPgetSndShadow;trivial.
subst;trivial.
Qed.

Lemma getConfigTablesRootNotNone phyDescChild s:
In phyDescChild (getPartitions pageRootPartition s) -> 
partitionDescriptorEntry s -> 
StateLib.getConfigTablesLinkedList phyDescChild (memory s) = None -> False.
Proof.
intros. 
unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP phyDescChild idxShadow3 entry s /\ entry <> pageDefault)).
        apply H0;trivial.
        do 3 right;left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
apply nextEntryIsPPgetConfigList in Hpp.
rewrite Hpp in *.
now contradict H1.
Qed.
  
 Lemma sh2PartNotNone phyDescChild s:
In phyDescChild (getPartitions pageRootPartition s) -> 
partitionDescriptorEntry s -> 
StateLib.getSndShadow phyDescChild (memory s) = None -> False.
Proof.
intros. 
unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP phyDescChild idxShadow2 entry s /\ entry <> pageDefault)).
        apply H0;trivial.
        do 2 right;left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
apply nextEntryIsPPgetSndShadow in Hpp.
rewrite Hpp in *.
now contradict H1.
Qed.

 Lemma sh1PartNotNone phyDescChild s:
In phyDescChild (getPartitions pageRootPartition s) -> 
partitionDescriptorEntry s -> 
StateLib.getFstShadow phyDescChild (memory s) = None -> False.
Proof.
intros. 
unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP phyDescChild idxShadow1 entry s /\ entry <> pageDefault)).
        apply H0;trivial.
        do 1 right;left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
apply nextEntryIsPPgetFstShadow in Hpp.
rewrite Hpp in *.
now contradict H1.
Qed.
 Lemma configNotDefault s stop: 
forall  pd ,
pd<> pageDefault -> 
(stop+1) <= nbLevel ->
  ~ In pageDefault (getIndirectionsAux pd s stop).
  Proof.
  induction stop;simpl.
  intuition.
  simpl;intros.
  apply and_not_or.
  split;trivial.
  rewrite in_flat_map.
  contradict H.
  destruct H as (x & Hx & Hx1).
  apply NNPP.
  unfold not at 1.
  intros.
  contradict Hx1.
  apply IHstop;try lia.
  induction tableSize;simpl in *.
  now contradict Hx.
  case_eq(lookup pd (CIndex n) (memory s) pageEq idxEq );intros;
  rewrite H1 in *;[|try apply IHn ;trivial].
  destruct v; try (apply IHn; assumption).
  case_eq(Nat.eqb (pa p) pageDefault ) ;intros ;rewrite H2 in *. 
  apply IHn;trivial.
  apply in_app_iff in Hx.
  destruct Hx. apply IHn; trivial.
  simpl in *.
  destruct H3.
  subst.
  unfold not;intros.
  apply beq_nat_false in H2.
  destruct pageDefault;destruct (pa p );simpl in *.
  inversion H3.
  subst.
  now contradict H2.
  now contradict H3.
Qed.

Lemma getIndirectionInGetIndirections2 (stop : nat) s prevtable
(va : vaddr) (level1 : level) (table root : page) :
(stop+1) <= nbLevel ->
getIndirection root va level1 (stop-1) s = Some prevtable ->
StateLib.readPhyEntry prevtable ( StateLib.getIndexOfAddr va (CLevel (level1 - (stop-1))))
         (memory  s) = Some table -> 
NoDup (getIndirectionsAux root s (stop+1)) -> 
table <> pageDefault -> 
root <> pageDefault -> 
stop <= level1 -> 
prevtable <> pageDefault -> 
~ In table (getIndirectionsAux root s stop).
Proof.

      intros. 
      
assert ( Hnotdef :  ~ In pageDefault (getIndirectionsAux root s stop)).
apply configNotDefault;trivial.
revert H H0 H1 H2 H3 H4 H5 H6.

revert Hnotdef.
revert va level1  table root.
revert prevtable.
induction stop;simpl.
intros.
lia.
intros.
apply Classical_Prop.and_not_or.
split.
simpl in *.
apply NoDup_cons_iff in H2.
destruct H2. 
clear IHstop.
{ assert(prevtable = table \/ prevtable <> table) by apply pageDecOrNot. 
  destruct H8;subst.
  
 + assert(Hstop : stop = 0 \/ stop <> 0) by lia.
   destruct Hstop.
   * subst. 
   simpl in *. 
   inversion H0. 
   subst. 
   assert(In table  (getTablePages table tableSize s)). 
   apply readPhyEntryInGetTablePages with 
   (StateLib.getIndexOfAddr va (CLevel (level1 - 0)));trivial.
   destruct (StateLib.getIndexOfAddr va (CLevel (level1 - 0)));trivial.
   rewrite <- H1.
   f_equal. apply indexEqId. 
   clear H6 H5 H3 H4 H7 H1 H0 H.
   revert H2 H8. 
   induction (getTablePages table tableSize s);simpl.
   intuition.
   intros. 
   apply Classical_Prop.not_or_and in H2. 
   destruct H2.
   rewrite in_app_iff in H0. 
   apply Classical_Prop.not_or_and in H0.
   destruct H0.
   destruct H8. 
   subst. 
   trivial.
   apply IHl;trivial.
   *  assert(In table  (getTablePages table tableSize s)). 
   apply readPhyEntryInGetTablePages with 
    (StateLib.getIndexOfAddr va (CLevel (level1 - (stop - 0))));trivial.
   destruct  (StateLib.getIndexOfAddr va (CLevel (level1 - (stop - 0))));trivial.
   rewrite <- H1.
   f_equal. apply indexEqId. 
   unfold not;intros ;subst. 
   revert H2 H9 H8.
   clear.
   induction(getTablePages table tableSize s) ;simpl.
   intuition.
   intros. 
   rewrite in_app_iff in H2. 
   apply Classical_Prop.not_or_and in H2.
   destruct H2.
   destruct H9.
   subst.
   replace (stop+1) with (S stop) in * by lia.
   simpl in H.
   apply not_or_and in H.
   intuition.
   apply IHl;trivial.
 +
  contradict H2. 
  rewrite in_flat_map.
  assert(exists x ,  StateLib.readPhyEntry root
       (StateLib.getIndexOfAddr va level1) (memory s) =
     Some x /\ x <> pageDefault).
  { subst.    destruct stop;simpl in *. 
    intros.
    inversion H0;subst.
    now contradict H8.
    (*  
   exists prevtable.
   rewrite <- H1.
   f_equal.
   f_equal.
   rewrite <- minus_n_O.
   symmetry.
   apply CLevelIdentity1. *)
   intros. 
destruct(levelEq level1 levelMin);intros.
inversion H0. 
subst.
now contradict H8. 
case_eq(StateLib.readPhyEntry table (StateLib.getIndexOfAddr va level1)
         (memory s));intros.
         rewrite H2 in *. 
   case_eq(Nat.eqb pageDefault p);intros. 
   rewrite H9 in *. 
   inversion H0. subst.
   now contradict H6.       exists p;split;trivial.
   apply beq_nat_false in H9.
   unfold not;intros;subst.
   now contradict H9.
         rewrite H2 in H0. 
         now contradict H0. }
        destruct H9 as (x & H9 & Hxnotnull). 
  exists x.
  split. 
  apply readPhyEntryInGetTablePages with  (StateLib.getIndexOfAddr va level1);trivial.
  destruct (StateLib.getIndexOfAddr va level1 );simpl;lia.
  rewrite <- H9.
  f_equal.
  apply indexEqId.
 
 assert (exists pred,  Some pred =  StateLib.Level.pred level1).
 { unfold StateLib.Level.pred.
  case_eq( gt_dec level1 0); intros.
  simpl. exists (CLevel(level1 - 1));f_equal;trivial.
  unfold CLevel.
  case_eq(lt_dec (level1 - 1) nbLevel);intros.
  f_equal.
  apply proof_irrelevance.
  destruct level1.
  simpl in *;lia.
  lia.
   } 
  destruct H10 as (pred & Hpred).  
  apply getIndirectionInGetIndirections1 with va pred;trivial.
  lia.
assert(stop = 0 \/ stop <> 0) by lia.
destruct H10.
subst. 
simpl in *. 
inversion H0.
subst.
now contradict H8.

  assert( getIndirection x va pred (( stop-1)+1) s = Some table).
  apply getIndirectionStopS1 with prevtable.
assert(pred = CLevel (level1 -1)).
apply levelPredMinus1;trivial.
assert(0 < level1) by lia.
apply notFstLevel;trivial.
  symmetry. trivial.
  rewrite H11.
  unfold CLevel.
  case_eq(lt_dec (level1 - 1) nbLevel);intros.
  simpl.
  lia.
  destruct level1.
  simpl in *. lia.
  unfold not;intros;subst.
  now contradict H6.
  assert(Hexist :  exists (pred : level) (page1 : page),
         page1 <> pageDefault /\
         Some pred = StateLib.Level.pred level1 /\
         StateLib.readPhyEntry root (StateLib.getIndexOfAddr va level1)
           (memory s) = Some page1 /\
         getIndirection page1 va pred (stop - 1) s = Some prevtable). 
  apply getIndirectionFstStep;trivial.
  lia. lia.
  rewrite <- H0.
  f_equal. lia.
  destruct Hexist as (pred1 & page1 & Hpred1 &
   Hnotnull1 & Hphy & Hind). 
   rewrite Hphy in H9.
   inversion H9;subst.
   rewrite <- Hnotnull1 in *.
   inversion Hpred.
   subst.
   trivial.
  simpl.
  assert(Htrue : levelEq
 (CLevel (pred - (stop - 1))) levelMin = false).
 { unfold levelEq.
  apply NPeano.Nat.eqb_neq.
  unfold CLevel.
  case_eq( lt_dec (pred - (stop - 1)) nbLevel );intros. 
  simpl. 
  unfold levelMin.
  unfold CLevel.
  case_eq(lt_dec 0 nbLevel );intros. 
  simpl.
  assert(pred = CLevel (level1 -1)).
apply levelPredMinus1;trivial.
apply notFstLevel;trivial.
lia.
symmetry; trivial.
subst.
unfold CLevel.
case_eq(lt_dec (level1 - 1) nbLevel);intros.
simpl.
  lia.
  assert(level1 < nbLevel).
  destruct level1.
  simpl in *.
  lia.
  lia.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia.
  destruct pred.
  simpl in *.
  lia.
}
rewrite Htrue
.
assert(Hi : StateLib.readPhyEntry prevtable
    (StateLib.getIndexOfAddr va (CLevel (pred - (stop - 1)))) (memory s) = Some table). 
    rewrite <- H1.
 do 3  f_equal.
 { 
symmetry in Hpred.
apply levelPredMinus1 in Hpred.
rewrite Hpred.
unfold CLevel.
case_eq(lt_dec (level1 - 1) nbLevel);intros. 
simpl. 
lia.
destruct level1. 
simpl in *.
lia.
trivial.
apply notFstLevel;lia.
 }
 rewrite Hi.
 assert((Nat.eqb pageDefault table) = false).
 { subst. apply NPeano.Nat.eqb_neq. unfold not;intros.
 destruct table ;destruct pageDefault;simpl in *;subst.
 contradict H4.
 f_equal. apply proof_irrelevance. }
 rewrite H11.
 case_eq ( StateLib.Level.pred (CLevel (pred - (stop - 1))));intros;trivial.
 assert(Hnotnote : StateLib.Level.pred (CLevel (pred - (stop - 1))) <> None).
 apply levelPredNone;trivial.
 now contradict Hnotnote.
 rewrite H2.
 rewrite <-H11.
 f_equal.
 lia.

}
 
rewrite in_flat_map.
unfold not;intros Hii.

destruct Hii as (x & Hx & Hfalse).
contradict Hfalse.
assert(Hor1 :stop = 0 \/ stop > 0) by lia.
destruct Hor1 as [Hor1 | Hor1].
{ subst.
  simpl in *. intuition. }   
assert(Hor2 : levelEq level1 levelMin = true \/ 
levelEq level1 levelMin = false).
{ destruct (levelEq level1 levelMin).
  left;trivial. right;trivial. }
destruct Hor2 as [Hor2 | Hor2].
+
destruct stop;try lia.
simpl in *.
rewrite Hor2 in *.
inversion H0;subst.
apply NoDup_cons_iff in H2.
destruct H2.
assert(level1 <= 0).
apply levelEqBEqNatTrue0;trivial.
lia.
+ 
assert(Htrue : exists (pred : level) (page1 : page),
         page1 <> pageDefault /\
         Some pred = StateLib.Level.pred level1 /\
         StateLib.readPhyEntry root (StateLib.getIndexOfAddr va level1)
           (memory s) = Some page1 /\
         getIndirection page1 va pred (stop - 1) s = Some prevtable).
apply getIndirectionFstStep;trivial. lia.
rewrite <- H0.
f_equal. lia.
rewrite <- minus_n_O in H0;trivial.
destruct Htrue as (pred & page1 & Hpage1notnull & Hpred & Hphyentry & Hind).
assert(Hor :page1 = x \/ page1 <> x) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].

subst.
 
apply IHstop with prevtable va pred;trivial.
move Hnotdef at bottom.
apply not_or_and in Hnotdef.
destruct Hnotdef.
contradict H8.
rewrite in_flat_map.
exists x;split;trivial.
lia.
rewrite <- H1.
f_equal.
f_equal.
f_equal.
symmetry in Hpred.
apply levelPredMinus1 in Hpred.
rewrite Hpred.
unfold CLevel.
case_eq(lt_dec (level1 - 1) nbLevel);intros. 
simpl.
lia.
destruct level1. 
simpl in *.
lia.
trivial.

apply NoDup_cons_iff in H2.
destruct H2.

revert Hx H7. 
clear.

induction (getTablePages root tableSize s);simpl.
intuition.
intros. 
destruct Hx;subst.
apply NoDupSplitInclIff in H7.
intuition.
apply IHl;trivial.
apply NoDupSplitInclIff in H7.

intuition.

assert(pred = CLevel (level1 -1)).
apply levelPredMinus1;trivial.
symmetry;trivial.
rewrite H7.
unfold CLevel.
case_eq(lt_dec (level1 - 1) nbLevel);intros;simpl.
lia.
destruct level1.
simpl in *.
lia.

assert(~ In table (getIndirectionsAux x s (stop+1))). 
{
assert(In table (getIndirectionsAux page1 s (stop+1))).
 {


apply getIndirectionInGetIndirections1  with va pred ;trivial.
lia.
assert(getIndirection page1 va pred ((stop-1) +1) s = Some table).
{ 

apply getIndirectionStopS1 with prevtable;trivial.
assert(Hhyp : stop <= pred). 
{ assert(pred = CLevel (level1 -1)). 
apply levelPredMinus1;trivial.
symmetry;trivial.
rewrite H7.
unfold CLevel.
case_eq(lt_dec (level1 - 1) nbLevel);intros;simpl.
lia.
destruct level1.
simpl in *.
lia. }
lia.

simpl.

assert(Hhyp : stop <= pred). 
{ assert(pred = CLevel (level1 -1)). 
apply levelPredMinus1;trivial.
symmetry;trivial.
rewrite H7.
unfold CLevel.
case_eq(lt_dec (level1 - 1) nbLevel);intros;simpl.
lia.
destruct level1.
simpl in *.
lia. }

assert(Htrue : levelEq
 (CLevel (pred - (stop - 1))) levelMin = false).
 { unfold levelEq.
  apply NPeano.Nat.eqb_neq.
  unfold CLevel.
  case_eq( lt_dec (pred - (stop - 1)) nbLevel );intros. 
  simpl. 
  unfold levelMin.
  unfold CLevel.
  case_eq(lt_dec 0 nbLevel );intros. 
  simpl.
  lia.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia.
  destruct pred.
  simpl in *.
  lia.
}
rewrite Htrue.
assert((CLevel (level1 - (stop - 0))) = 
(CLevel (pred - (stop - 1)))).
{
f_equal. 
symmetry in Hpred.
apply levelPredMinus1 in Hpred.
rewrite Hpred.
unfold CLevel.
case_eq(lt_dec (level1 - 1) nbLevel);intros. 
simpl. 
lia.
destruct level1. 
simpl in *.
lia.
trivial. }
rewrite <- H7.
rewrite H1.
assert((Nat.eqb pageDefault table) = true \/ (Nat.eqb pageDefault table) = false).
{ destruct (Nat.eqb pageDefault table). 
  left;trivial.
  right;trivial. } 

destruct H8.
rewrite  H8. 
apply beq_nat_true in H8;trivial.
f_equal.
destruct table.
simpl in *.
destruct pageDefault;simpl in *.
subst;f_equal;apply proof_irrelevance.
rewrite H8.
case_eq(StateLib.Level.pred (CLevel (level1 - (stop - 0))) );intros;trivial.
assert(StateLib.Level.pred (CLevel (level1 - (stop - 0))) 
<> None). 
apply levelPredNone.
rewrite <- Htrue.
f_equal.
f_equal. 
symmetry in Hpred.
apply levelPredMinus1 in Hpred.
rewrite Hpred.
unfold CLevel.
case_eq(lt_dec (level1 - 1) nbLevel);intros. 
simpl. 
lia.
destruct level1. 
simpl in *.
lia.
trivial. 
now contradict H9.   }
rewrite <-  H7.
f_equal.
lia.

}
assert(NoDup (getIndirectionsAux root s (S(stop + 1)))).
simpl;trivial. 
assert(disjoint (getIndirectionsAux page1 s (S(stop + 1) -1)) 
 (getIndirectionsAux x s  (S(stop + 1) -1))  ).
 assert(exists idx, StateLib.readPhyEntry root (CIndex idx) (memory s) = Some x ).
 { revert Hx. clear.
 revert x.
  induction tableSize.
  intros.
  simpl in *.
  intuition.
  simpl;intros.
  case_eq(lookup root (CIndex n) (memory s) pageEq idxEq);intros;
  rewrite H in *; try (apply IHn ; assumption).
  destruct v; try (apply IHn ; assumption).
  case_eq(Nat.eqb (pa p) pageDefault);intros;rewrite H0 in *.
  apply IHn;trivial.
  apply in_app_iff in Hx.
  destruct Hx; trivial.
  apply IHn;trivial.
  simpl in *. 
  destruct H1;subst.
  exists n;trivial.
  unfold StateLib.readPhyEntry. 
  rewrite H;trivial.
  intuition.
}

destruct H9 as (idx & Hidx).
{


apply disjointGetIndirectionsAuxMiddle with root
 (CIndex idx) (StateLib.getIndexOfAddr va level1);trivial.
 *
 intuition.
 *
 lia.
 *
 apply NPeano.Nat.eqb_neq.
 unfold not;intros Hfalse.
 contradict Hpage1notnull.
 destruct page1;destruct pageDefault;simpl in *. 
 subst;f_equal;apply proof_irrelevance.
 * move Hnotdef at bottom.
 apply not_or_and in Hnotdef.
 destruct Hnotdef.
 rewrite in_flat_map in H10.
 apply NNPP.
 unfold not at 1. intros.
 contradict H10.
 exists x.
 split. trivial.
 apply NNPP. 
 unfold not at 1.
 intros. 
 contradict H11.
 destruct stop;
 simpl in *.
 now contradict Hor1.
 apply not_or_and in H10.
 destruct H10 .
 apply NPeano.Nat.eqb_neq.
 unfold not;intros;subst.
 destruct x;destruct pageDefault;simpl in *;
 subst.
 contradict H10. f_equal.
 apply proof_irrelevance.
  }
assert(Htrue : S (stop + 1) - 1 = stop +1) by lia.
rewrite Htrue in *.
clear Htrue.
apply H9;trivial. }
apply inGetIndirectionsAuxLt with (stop + 1);trivial.
lia.

Qed.

Lemma indirectionNotInPreviousMMULevel s ptVaChildpd idxvaChild phyVaChild  
  pdChildphy currentPart 
presentvaChild vaChild phyDescChild level entry:
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
In currentPart (getPartitions pageRootPartition s) -> 
In phyVaChild (getAccessibleMappedPages currentPart s) -> 
lookup ptVaChildpd idxvaChild (memory s) pageEq idxEq = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
negb presentvaChild = true -> 
In phyDescChild (getPartitions pageRootPartition s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild levelMin) s -> 
 getTableAddrRoot ptVaChildpd idxPageDir phyDescChild vaChild s -> 
 (Nat.eqb pageDefault ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild levelMin = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild presentvaChild s ->  
nextEntryIsPP phyDescChild idxPageDir pdChildphy s -> 
pdChildphy <> pageDefault -> 
getIndirection pdChildphy vaChild level (nbLevel - 1) s =
            Some ptVaChildpd -> 
            nbLevel -1 > 0 -> 
~ In ptVaChildpd (getIndirectionsAux pdChildphy s (nbLevel - 1)).
Proof.
intros Hpde Hpresdef Hnodupconf Hconfigdiff Hparts Haccess Hlookup Hlevel 
Hnotpresent Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild Hpdchildnotnull Hindchild H0.
 {  assert(0<nbLevel) by apply nbLevelNotZero.
      assert(nbLevel - 1 + 1 = nbLevel) by lia. 
 assert(Hprevious : exists prevtab,
      getIndirection pdChildphy vaChild level (nbLevel - 2) s =
            Some prevtab /\prevtab <> pageDefault /\  StateLib.readPhyEntry prevtab
  (StateLib.getIndexOfAddr vaChild (CLevel (level- ((nbLevel - 1) - 1)))) (memory s) =
Some ptVaChildpd). 
{   revert Hindchild   Hdefaut  (*  H0 *).


  assert(Hstooo : level > (nbLevel - 1 -1)).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    lia. (* 
    unfold CLevel in H0.
    rewrite H0 in *.
    simpl in *.
     *)
    lia. } 

  
  assert(Htpp : 0 < nbLevel -1).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    lia.
    lia.
    
     } 
  assert(Hnotdef : pdChildphy <> pageDefault) by intuition. 
  revert Hstooo Htpp Hnotdef.
  clear. 
 
  replace (nbLevel -2) with (nbLevel -1 -1) by lia.  
  revert pdChildphy level ptVaChildpd.
  induction (nbLevel-1);simpl.
  intros.
  lia.
  intros. 
  case_eq(levelEq level levelMin);intros;
  rewrite H in *.
  apply levelEqBEqNatTrue0 in H. 
  lia.
   case_eq(StateLib.readPhyEntry pdChildphy
                (StateLib.getIndexOfAddr vaChild level) (memory s));intros;
    rewrite H0 in *;try now contradict Hindchild.
    case_eq(Nat.eqb pageDefault p);intros;rewrite H1 in *.
    apply beq_nat_false in Hdefaut.
    inversion Hindchild.
    subst.
    now contradict Hdefaut.
    case_eq(StateLib.Level.pred level );intros;rewrite H2 in *.
    + replace (n-0) with n by lia.
    assert(Hooo : n = 0 \/ 0 < n) by lia.
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
    lia.
    destruct level.
    simpl in *.
    lia.
    trivial.
    assert(Hi1 : p <> pageDefault).
    apply beq_nat_false in H1.
    intuition.
    subst.
    now contradict H1. 
      generalize(IHn p l ptVaChildpd Hii H3 Hi1 Hindchild Hdefaut
       );clear IHn ; intros iHn .
       destruct iHn as (prevtab & Hindprev & Hdef & Hread).
       exists prevtab;split;trivial.
       intros.
       assert(Hs :S(n-1) = n) by lia.
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
lia.
destruct level. 
simpl in *.
lia.
trivial.
+ assert(Hnotnone : StateLib.Level.pred level <> None).
apply levelPredNone;trivial. now contradict Hnotnone.  }
destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev). 
apply getIndirectionInGetIndirections2 with prevtab vaChild level;
simpl; subst;
trivial.
lia.
simpl.
rewrite <- Hprevtable.
f_equal.
lia.
rewrite H1.
assert(Hdup :   noDupConfigPagesList s) by intuition.
apply noDupConfigPagesListNoDupGetIndirections with phyDescChild idxPageDir;trivial.
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
lia.
lia.
}
Qed.
Lemma vaNotDerived currentPart shadow1 (ptSh1ChildFromSh1 : page) s : 
consistency s ->
In currentPart (getPartitions pageRootPartition s) -> 
(Nat.eqb pageDefault ptSh1ChildFromSh1) = false  -> 
(exists va : vaddr,
isEntryVA ptSh1ChildFromSh1 (StateLib.getIndexOfAddr shadow1 levelMin) va s /\
vaddrEq vaddrDefault va = true) -> 
(forall idx : index,
StateLib.getIndexOfAddr shadow1 levelMin = idx ->
isVE ptSh1ChildFromSh1 idx s /\ getTableAddrRoot ptSh1ChildFromSh1 idxShadow1 currentPart shadow1 s) -> 
~ isDerived currentPart shadow1 s .
Proof.
intros Hcons Hparts Hptfromsh1notnull Hii Hi. 

destruct Hi with (StateLib.getIndexOfAddr shadow1 levelMin) as 
(Hve & Hgetve);trivial.

clear Hi.
destruct Hii as (va0 & Hvae & Hveq).
unfold isDerived.
unfold getTableAddrRoot in *.
destruct Hgetve as (_ & Hgetve).
assert(Hcursh1 :(exists entry : page, nextEntryIsPP currentPart idxShadow1 entry s /\ entry <> pageDefault)).
assert(Hpde :  partitionDescriptorEntry s).
unfold consistency in *.
intuition.
unfold partitionDescriptorEntry in *.
apply Hpde;trivial.
right;left;trivial.
destruct Hcursh1 as (cursh1 & Hcursh1 & Hsh1notnull).
rewrite nextEntryIsPPgetFstShadow in *.
rewrite Hcursh1.
rewrite <- nextEntryIsPPgetFstShadow in *.        
apply Hgetve in Hcursh1.
destruct Hcursh1 as (l & Hl & stop & Hstop & Hgetva).
clear Hgetve.
unfold getVirtualAddressSh1.
rewrite <- Hl.
subst.
assert(Hgetind : getIndirection cursh1 shadow1 l (nbLevel - 1) s  = Some ptSh1ChildFromSh1).
apply getIndirectionStopLevelGT2 with (l+1);trivial.
abstract lia.
apply getNbLevelEq in Hl.
subst.
apply nbLevelEq.
rewrite Hgetind.
rewrite Hptfromsh1notnull.
unfold  isEntryVA in *.
unfold isVE in *.
unfold StateLib.readVirEntry.
case_eq(lookup ptSh1ChildFromSh1 (StateLib.getIndexOfAddr shadow1 levelMin) 
(memory s) pageEq idxEq);intros * Hlookupsh1;rewrite Hlookupsh1 in *; 
try now contradict Hve.
case_eq v;intros * Hvsh1;rewrite Hvsh1 in *; 
try now contradict Hve.
subst.
unfold not;intros.
rewrite H in Hveq.
now contradict Hveq.
Qed.
Lemma phyNotDerived currentPart phySh1Child currentPD shadow1 (ptSh1Child : page)s :  
(Nat.eqb pageDefault ptSh1Child) = false -> 
~ isDerived currentPart shadow1 s -> 
consistency s -> 
In currentPart (getPartitions pageRootPartition s) -> 
nextEntryIsPP currentPart idxPageDir currentPD s  -> 
(forall idx : index,
StateLib.getIndexOfAddr shadow1 levelMin = idx ->
isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child idxPageDir currentPart shadow1 s) -> 
isEntryPage ptSh1Child (StateLib.getIndexOfAddr shadow1 levelMin) phySh1Child s -> 
entryPresentFlag ptSh1Child (StateLib.getIndexOfAddr shadow1 levelMin) true s -> 
forall child : page,
In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s).
Proof.
intros Hptnotnull HderivShadow1 Hcons Hcurparts Hcurpd Hget Hep Hpres child Hchild. 
assert(H1 : physicalPageNotDerived s).
{ unfold consistency in *.
intuition. }
unfold physicalPageNotDerived in *.
rewrite nextEntryIsPPgetPd in *.
generalize (H1 currentPart shadow1 currentPD 
phySh1Child Hcurparts Hcurpd HderivShadow1);clear H1;intros H1.
unfold getMappedPages.
case_eq (StateLib.getPd child (memory s) );intros;trivial.
unfold getMappedPagesAux.
rewrite filterOptionInIff.
unfold getMappedPagesOption.
rewrite in_map_iff.
unfold not in *.
intros.
destruct H0 as (x & Hx1 & Hx2).

apply H1 with child p x phySh1Child;trivial.
apply getMappedPageGetTableRoot
with ptSh1Child currentPart;intuition.
subst.
trivial.
subst.
trivial.
apply nextEntryIsPPgetPd;trivial.
unfold not;intros Hfalse;now contradict Hfalse. 
Qed. 


Lemma noDupAllVAddrWithOffset0 :
 NoDup getAllVAddrWithOffset0.
 Proof.
unfold getAllVAddrWithOffset0.
assert (Hnodupallvaddr : NoDup getAllVAddr) by apply noDupAllVaddr.
revert Hnodupallvaddr.
clear.
induction getAllVAddr;simpl;intros;trivial.
apply NoDup_cons_iff in Hnodupallvaddr.
case_eq(checkOffset0 a);intros.
constructor.
rewrite filter_In.
intuition.
apply IHl;intuition.
apply IHl;intuition.
Qed.

Lemma  checkVAddrsEqualityWOOffsetFalseEqOffset nbL a descChild: 
StateLib.getNbLevel = Some nbL -> 
a <> descChild -> 
checkOffset0 descChild = true  -> 
checkOffset0 a = true ->
StateLib.checkVAddrsEqualityWOOffset nbLevel a descChild nbL = false.
Proof.
intros.
unfold checkOffset0 in *.
   assert( nth nbLevel descChild idxDefault =  nth nbLevel a idxDefault). 
 { case_eq (Nat.eqb (nth nbLevel a idxDefault) (CIndex 0));intros Heq;rewrite Heq in *; 
    try now contradict H1.
   case_eq(Nat.eqb (nth nbLevel descChild idxDefault) (CIndex 0));intros Heq1;rewrite Heq1 in *;
   try now contradict H2.
   apply beq_nat_true in Heq.
   apply beq_nat_true in Heq1.
   destruct (nth nbLevel a idxDefault);simpl in *;destruct (nth nbLevel descChild idxDefault);simpl in *.
  subst. f_equal. apply proof_irrelevance. }
 rewrite H3 in *. 
 clear H1 H2.
  assert(last a idxDefault = last descChild idxDefault).
 {  revert H0.
   intros. 
   assert(forall l ,  nth ((length l)-1)  l idxDefault = last l idxDefault ).
   { clear.
    induction l.
    simpl;trivial.
    simpl.
    replace ( length l - 0 ) with (length l) by lia.
    case_eq(length l );intros.
    apply length_zero_iff_nil in H.
    subst;trivial.
    case_eq l.
    intros;subst.
    simpl in *.
    lia.
    intros.
    rewrite <- H0.
    rewrite H in IHl.
    rewrite  <- IHl.
    f_equal.
    lia. }
    rewrite <- H1.   
   destruct a;simpl in *.
   destruct descChild;simpl in *.
   rewrite Hva.
   rewrite <- H1.
   rewrite NPeano.Nat.add_sub.
   rewrite Hva0.
   simpl.
   rewrite <- H3.
   f_equal.
   lia. }
   clear H1.
  (*  assert (Heql : nbLevel <= nbLevel) by lia. *)

assert(HnbLlt :nbL < nbLevel).
apply getNbLevelLt;trivial.
 assert(length a <= nbL +2).
{ destruct a;simpl. simpl in *.
rewrite Hva.
symmetry in H.
apply getNbLevelEq in H.
subst.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
simpl.
lia.
lia.
}
apply NNPP.
unfold not at 1; intros Hfalse.
 apply Bool.not_false_is_true in Hfalse.
 contradict H0.
  assert(forall predNbL : level, predNbL <= nbL ->
  StateLib.getIndexOfAddr a predNbL = StateLib.getIndexOfAddr descChild predNbL ).
  intros.
  apply checkVAddrsEqualityWOOffsetTrue' with  nbLevel nbL;trivial.
  clear Hfalse.
   
assert(Hmykey: forall pos, pos > nbL ->   nth pos descChild idxDefault = nth pos a idxDefault).
{ intros.
symmetry in H.

apply getNbLevelEq in H.
subst. 
clear HnbLlt.
assert(length a = nbLevel +1).
destruct a. 
simpl in *. lia.
assert (pos > nbLevel -1).
         unfold CLevel.
         case_eq( lt_dec (nbLevel - 1) nbLevel);intros.
         simpl.
         trivial.
         lia.
         lia.
clear H2.
assert (pos = nbLevel \/ pos > nbLevel) by lia.
destruct H2.
subst;trivial.
rewrite nth_overflow.
rewrite nth_overflow;trivial.
lia.
destruct descChild;simpl in *.
lia. }

unfold StateLib.getIndexOfAddr in *.
destruct a;destruct descChild;simpl in *.
assert(va = va0).
{ rewrite Hva in *.
  rewrite Hva0 in *.
  symmetry in H.
  apply getNbLevelEq in H.
  subst.
  assert(va = firstn (nbLevel-1) va ++ skipn (nbLevel-1) va).
  symmetry.
  apply firstn_skipn.
  rewrite H. 
  
  assert(va0 = firstn (nbLevel-1) va0 ++ skipn (nbLevel-1) va0).
  symmetry.
  apply firstn_skipn.
  rewrite H2.
  f_equal.
  +     
 clear Hmykey.
  assert(forall predNbL : level,
     predNbL <= nbLevel - 1 ->
     nth ((nbLevel - 1)  - predNbL ) va idxDefault =
     nth ((nbLevel - 1) - predNbL ) va0 idxDefault).
     { intros. generalize (H0 predNbL) ; clear H0;intros H0.
     assert((nbLevel - 1 - predNbL) = (nbLevel + 1 - (predNbL + 2))). 
     lia.
     rewrite H5.
     apply H0.
     unfold CLevel.
     case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
     simpl.
     trivial.
     lia. } 
     assert(length va = length va0) by lia.
      assert(Hlenva : length va > 0) by lia.
     clear H2 H HnbLlt H0 H3 Hva0 Hva H1.
     assert(Hx : forall pos : level,
     pos <= nbLevel - 1 -> 
     nth pos va idxDefault =
     nth pos va0 idxDefault).
     {  intros. 

     generalize(H4 (CLevel ((nbLevel - 1 ) - pos )));clear H4;
     intros H4.
     unfold
      CLevel in *.
      case_eq(lt_dec (nbLevel - 1 - pos) nbLevel );intros;
      rewrite H0 in *;simpl in *.
      assert (0 < nbLevel) by apply nbLevelNotZero.
      destruct pos.
      simpl in *.
      replace ((nbLevel - 1 - (nbLevel - 1 - l0))) with l0
      in *. 
      apply H4. clear H4.
      lia.
      clear H0.
      clear H4 l .
      lia.
      assert(0 < nbLevel) by apply nbLevelNotZero.
      lia. }
      
     clear H4.
     

     
     
     revert dependent va; revert dependent va0.
     assert(0 < nbLevel) by apply nbLevelNotZero.
     
     assert(Hlevel : nbLevel -1 < nbLevel ) by lia.
     
     clear H.
     induction (nbLevel-1);intros.
     simpl;trivial.
     assert(firstn (S n) va =
     nth 0 va idxDefault::  firstn n (tl va) ).
     revert Hlenva.
      clear .
     destruct va;simpl; intros;try lia.
     f_equal.
     rewrite H.
     assert(firstn (S n) va0 =
     nth 0 va0 idxDefault::  firstn n (tl va0) ).
     {revert Hlenva.
     rewrite H5. clear .
     destruct va0;simpl; intros;try lia.
     f_equal. }
     rewrite H0.
     f_equal.
     generalize(Hx levelMin );clear Hx;intros Hx.
     
     assert (levelMin <= S n).
     unfold levelMin.
     unfold CLevel.
     assert(0<nbLevel) by apply nbLevelNotZero.
     case_eq( lt_dec 0 nbLevel);intros;
     simpl; lia.
     apply Hx in H1. clear Hx.
     unfold levelMin in H1.
     unfold CLevel in H1.
     assert(0<nbLevel) by apply nbLevelNotZero.
     case_eq( lt_dec 0 nbLevel);intros; rewrite H3 in *.
     simpl in  *;trivial. lia.
     assert(forall va: list index, (length va) -1 = length (tl va) ).
     { clear.
       induction va;intros.
       simpl;trivial.
       simpl.
       lia. }
     assert (Hor :  length  (tl va) = 0 \/ length (tl va) > 0) by lia.
     destruct
      Hor as [Hor | Hor].
      * subst.
      assert(length (tl va0) = 0).
      rewrite <- H1.
      rewrite <- H5.
      rewrite  H1;trivial.
      assert((tl va) = []).
      apply length_zero_iff_nil;trivial.
      rewrite H3.
      
      assert((tl va0) = []).
      apply length_zero_iff_nil;trivial.
      rewrite H4.
      trivial.
      * 
     apply IHn.
     lia.
     
     
     rewrite <- H1.
     rewrite <- H1.
     f_equal.
     lia.
     trivial.
     intros.
     revert Hx H2 Hlevel.
     clear.
     intros.
     assert(forall va, nth pos (tl va) idxDefault =
     nth (S pos) va idxDefault).
     { clear .
     intros.
     revert pos.
     induction va.
     intros.
     simpl.
     destruct (l pos);trivial.
     simpl.
     intros;trivial. }
     rewrite H.
     rewrite H.
     generalize (Hx (CLevel (S pos)));clear Hx ; intros Hx.
     unfold CLevel in *.
     case_eq(lt_dec (S pos) nbLevel );intros;
     rewrite H0 in *;
     simpl in *.
         
     
     apply Hx.
     lia.
     lia. 
     
     
     +  
     generalize(H0 levelMin );clear H0;intros Hx.
 assert (levelMin <= CLevel (nbLevel - 1) ).
     unfold levelMin.
     unfold CLevel.
     assert(0<nbLevel) by apply nbLevelNotZero.
     case_eq( lt_dec 0 nbLevel);intros;
     simpl; lia.
     apply Hx in H0. clear Hx.
     
     simpl in *.
     unfold levelMin in H0.
     unfold CLevel in H0.
     assert(0<nbLevel) by apply nbLevelNotZero.
     case_eq( lt_dec 0 nbLevel);intros; rewrite H5 in *;
      intuition.
     simpl in  *;trivial.
     replace (nbLevel + 1 - 2) with (nbLevel -1) 
     in * by lia.
     
    
     assert(forall pos : nat,
         pos > nbLevel - 1 ->
         nth pos va0 idxDefault = nth pos va idxDefault).
         intros. 
         apply Hmykey.
         unfold CLevel.
         case_eq( lt_dec (nbLevel - 1) nbLevel);intros.
         simpl.
         trivial.
         lia.
         assert(Hx : length va = length va0) by lia.
         assert(Hii : length va <= (nbLevel -1) +2) by lia.
         clear Hmykey H1 H2 H HnbLlt.
         clear H3.
         clear Hva Hva0 H5. 
         clear l H4.
         assert(forall pos, pos >= nbLevel -1 -> nth pos va0 idxDefault = nth pos va idxDefault). 
         intros .
         assert(pos =  nbLevel - 1 \/ pos >  nbLevel - 1) by lia.
         clear H.
         destruct H1.
         subst;trivial.
         symmetry;trivial.        
         apply H6;trivial.
         clear H6 H0.
         
 
         revert dependent va0.
         revert dependent va.
         induction (nbLevel-1);intros;trivial.
         simpl in *.
         revert dependent va.
         induction va0;simpl;intros;subst.
         apply length_zero_iff_nil;trivial.
         simpl in *.
         case_eq va;simpl;intros.
         subst.
         simpl in *. 
         lia.
         f_equal.
         generalize(H 0);clear H;intros H.
         simpl in *.
         subst.
         simpl in *.
         symmetry.
         apply H; lia.
         apply IHva0.
         subst.
         simpl in *. lia.
         intros.
         subst. simpl in *;lia.
         intros.
         generalize (H (S pos));clear H;intros H.
         subst.
         simpl in *.
         apply H.
         lia.
         subst.
         simpl in *. (* 
         lia.
         simpl. *)
         case_eq va;simpl;intros.
         subst.
         
         inversion Hx.
         symmetry in H1.
         apply length_zero_iff_nil in H1.
         subst.
         trivial.
         case_eq va0;intros.
         subst.
         simpl in *.
         now contradict Hx.
         apply IHn;trivial.
         intros.
         subst.
         simpl in *.
         lia.
         intros.
         subst.
         simpl in *.
         lia.
         intros.
         subst.
         
         generalize (H (S pos));clear H ; intros H.
         
         apply H;lia. }
         subst;f_equal;apply proof_irrelevance.
Qed.

Lemma getPDFlagGetPdsVAddr' sh1Childphy vaChild phyDescChild level s:
 nextEntryIsPP phyDescChild idxShadow1 sh1Childphy s -> 
  getPDFlag sh1Childphy vaChild s = false -> 
  StateLib.getNbLevel = Some level -> 
  StateLib.getFstShadow phyDescChild (memory s) = Some sh1Childphy -> 
  ~ In vaChild (getPdsVAddr phyDescChild level getAllVAddr s).
Proof.
unfold getPDFlag.
unfold getPdsVAddr.
rewrite filter_In.
intros Hpp Hpdflag Hlevel Hsh1 .
apply or_not_and.
right.
unfold not;intros.
unfold checkChild in *.
rewrite Hlevel in *.
rewrite Hsh1 in *.
rewrite Hpdflag in *.
now contradict H. 
Qed.

Lemma isEntryPageReadPhyEntry2 table idx entry s:
StateLib.readPhyEntry table idx (memory s) = Some (pa entry) -> 
isEntryPage table idx (pa entry) s.
Proof.
intros Hentrypage.
unfold isEntryPage in *.
unfold StateLib.readPhyEntry in *.
destruct(lookup table idx (memory s) pageEq idxEq );
try now contradict Hentrypage.
destruct v; try now contradict Hentrypage.
inversion Hentrypage;trivial.
Qed.

   Lemma isPresentNotDefaultIffTrue (s :state):
   forall (table : page) (idx : index) ,
   isPresentNotDefaultIff s -> 
StateLib.readPresent table idx (memory s) = Some true ->
StateLib.readPhyEntry table idx (memory s) <> Some pageDefault.
Proof.
intros table idx Hi1. intros.
apply NNPP.
unfold not at 1;intros Hfalse.
contradict H. 
assert(StateLib.readPresent table idx (memory s) = Some false). 
generalize (Hi1 table idx); 
clear Hi1; intros Hconspresent.
      apply Hconspresent.
       apply NNPP.
      unfold not at 1;intros Hfalse1.
      contradict Hfalse.
      trivial.
      rewrite H.
      unfold not;intros. now contradict H0.
Qed.
(** moins d'hypothèses *)
Lemma indirectionNotInPreviousMMULevel1 s ptVaChildpd idxvaChild (* phyVaChild *)  
  pdChildphy (* currentPart *) 
(* presentvaChild *) vaChild phyDescChild level entry:
 partitionDescriptorEntry s -> 
 isPresentNotDefaultIff s -> 
 noDupConfigPagesList s -> 
configTablesAreDifferent s -> 
(* In currentPart (getPartitions multiplexer s) ->  *)
True -> 
(* In phyVaChild (getAccessibleMappedPages currentPart s) ->  *)
True -> 
lookup ptVaChildpd idxvaChild (memory s) pageEq idxEq = Some (PE entry) -> 
StateLib.getNbLevel = Some level -> 
(* negb presentvaChild = true ->  *)
True -> 
In phyDescChild (getPartitions pageRootPartition s) -> 
 isPE ptVaChildpd (StateLib.getIndexOfAddr vaChild levelMin) s -> 
 getTableAddrRoot ptVaChildpd idxPageDir phyDescChild vaChild s -> 
 (Nat.eqb pageDefault ptVaChildpd) = false ->
 StateLib.getIndexOfAddr vaChild levelMin = idxvaChild -> 
 entryPresentFlag ptVaChildpd idxvaChild true s ->  
nextEntryIsPP phyDescChild idxPageDir pdChildphy s -> 
pdChildphy <> pageDefault -> 
getIndirection pdChildphy vaChild level (nbLevel - 1) s =
            Some ptVaChildpd -> 
            nbLevel -1 > 0 -> 
~ In ptVaChildpd (getIndirectionsAux pdChildphy s (nbLevel - 1)).
Proof.
intros Hpde Hpresdef Hnodupconf Hconfigdiff Hparts Haccess Hlookup Hlevel 
 Hnotpresent Hchildpart Hpe Htblroot Hdefaut Hidx Hentrypresent
Hpdchild Hpdchildnotnull Hindchild H0.
 {  assert(0<nbLevel) by apply nbLevelNotZero.
      assert(nbLevel - 1 + 1 = nbLevel) by lia. 
 assert(Hprevious : exists prevtab,
      getIndirection pdChildphy vaChild level (nbLevel - 2) s =
            Some prevtab /\prevtab <> pageDefault /\  StateLib.readPhyEntry prevtab
  (StateLib.getIndexOfAddr vaChild (CLevel (level- ((nbLevel - 1) - 1)))) (memory s) =
Some ptVaChildpd). 
{   revert Hindchild   Hdefaut  (*  H0 *).


  assert(Hstooo : level > (nbLevel - 1 -1)).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    lia. (* 
    unfold CLevel in H0.
    rewrite H0 in *.
    simpl in *.
     *)
    lia. } 

  
  assert(Htpp : 0 < nbLevel -1).
  { symmetry in Hlevel. apply getNbLevelEq in Hlevel.
    subst. 
    unfold CLevel.
    case_eq(lt_dec (nbLevel - 1) nbLevel );intros.
    simpl.
    lia.
    lia.
    
     } 
  assert(Hnotdef : pdChildphy <> pageDefault) by intuition. 
  revert Hstooo Htpp Hnotdef.
  clear. 
  replace (nbLevel -2) with (nbLevel -1 -1) by lia.  
  revert pdChildphy level ptVaChildpd.
  induction (nbLevel-1);simpl.
  intros.
  lia.
  intros. 
  case_eq(levelEq level levelMin);intros;
  rewrite H in *.
  apply levelEqBEqNatTrue0 in H. 
  lia.
   case_eq(StateLib.readPhyEntry pdChildphy
                (StateLib.getIndexOfAddr vaChild level) (memory s));intros;
    rewrite H0 in *;try now contradict Hindchild.
    case_eq(Nat.eqb pageDefault p);intros;rewrite H1 in *.
    apply beq_nat_false in Hdefaut.
    inversion Hindchild.
    subst.
    now contradict Hdefaut.
    case_eq(StateLib.Level.pred level );intros;rewrite H2 in *.
    + replace (n-0) with n by lia.
    assert(Hooo : n = 0 \/ 0 < n) by lia.
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
    lia.
    destruct level.
    simpl in *.
    lia.
    trivial.
    assert(Hi1 : p <> pageDefault).
    apply beq_nat_false in H1.
    intuition.
    subst.
    now contradict H1. 
      generalize(IHn p l ptVaChildpd Hii H3 Hi1 Hindchild Hdefaut
       );clear IHn ; intros iHn .
       destruct iHn as (prevtab & Hindprev & Hdef & Hread).
       exists prevtab;split;trivial.
       intros.
       assert(Hs :S(n-1) = n) by lia.
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
lia.
destruct level. 
simpl in *.
lia.
trivial.
+ assert(Hnotnone : StateLib.Level.pred level <> None).
apply levelPredNone;trivial. now contradict Hnotnone.  }
destruct Hprevious as (prevtab & Hprevtable & Hprevnotnull & Hreadprev). 
apply getIndirectionInGetIndirections2 with prevtab vaChild level;
simpl; subst;
trivial.
lia.
simpl.
rewrite <- Hprevtable.
f_equal.
lia.
rewrite H1.
assert(Hdup :   noDupConfigPagesList s) by intuition.
apply noDupConfigPagesListNoDupGetIndirections with phyDescChild idxPageDir;trivial.
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
lia.
lia.
}
Qed.

Lemma beqVAddrTrue a :
vaddrEq a a= true.
Proof.
unfold vaddrEq.
destruct a;simpl.
assert(length va <= nbLevel + 1) by lia.
clear Hva.
revert dependent va.
induction va;simpl in *;trivial.
intros.
case_eq( idxEq a a);intros.
apply IHva.
lia.
unfold idxEq in *.
rewrite <- H0.
symmetry.
apply beq_nat_refl.
Qed.

Lemma eqListTrueEq  :
forall a b,
eqList a b idxEq= true -> a=b.
Proof.
induction a; simpl;intros.
case_eq b;intros;trivial.
rewrite H0 in *.
now contradict H.
case_eq b;intros;subst.
now contradict H.
case_eq( idxEq a i);intros;rewrite H0 in *.
f_equal.
unfold idxEq in H0.
apply beq_nat_true in H0;trivial.
destruct a. destruct i. simpl in *.

subst;trivial.
f_equal.
apply proof_irrelevance.
apply IHa;trivial.
now contradict H.
Qed.

Lemma beqVAddrTrueEq :
forall a b,
vaddrEq a b = true -> a=b.
Proof.
intros.
destruct a. 
destruct b. 
assert (va = va0). 
apply eqListTrueEq.
simpl in *.
trivial.
subst.
f_equal.
apply proof_irrelevance.
Qed.
Lemma isAccessibleMappedPageGetTableRoot (phypage :page) entry sh2 descParent ptsh2 va pdAncestor ancestor  (vaInAncestor :vaddr) ptvaInAncestor s:
 nextEntryIsPP descParent idxShadow2 sh2 s -> 
 isVA ptsh2 (StateLib.getIndexOfAddr va levelMin) s -> 
getTableAddrRoot ptsh2 idxShadow2 descParent va s -> 
nextEntryIsPP descParent idxParentDesc ancestor s -> 
nextEntryIsPP ancestor idxPageDir pdAncestor s -> 
isPE ptvaInAncestor  (StateLib.getIndexOfAddr vaInAncestor levelMin) s -> 
getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s -> 
(Nat.eqb pageDefault ptvaInAncestor) = false -> 
 isAccessibleMappedPageInParent descParent va phypage s = true -> 
  lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) (memory s) pageEq idxEq =
          Some (PE entry) -> 
(Nat.eqb pageDefault ptsh2) = false -> 

isVA' ptsh2 (StateLib.getIndexOfAddr va levelMin) vaInAncestor s -> 
phypage = pa entry.
Proof. 
intros Hppsh2 Hva Hx Hppparent Hpppd Hve Hroot Hdef Hfalse Hlookup.
intros.
symmetry.
 assert (HgetVirt : getVirtualAddressSh2 sh2 s va  = Some vaInAncestor).
{ apply isVaInParent with descParent ptsh2;trivial.
  intros;subst.
  intuition. }
unfold isAccessibleMappedPageInParent in *.
apply nextEntryIsPPgetSndShadow in Hppsh2.
rewrite Hppsh2 in *.
rewrite HgetVirt in *.
rewrite nextEntryIsPPgetParent in * .
rewrite Hppparent in *. 
apply nextEntryIsPPgetPd in Hpppd .
rewrite Hpppd in *.
case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor);
intros * Hacce;
rewrite Hacce in *;try now contradict Hfalse.
unfold getAccessibleMappedPage in Hacce.
unfold getTableAddrRoot in *.
destruct Hroot as (_ & Hroot).
rewrite <- nextEntryIsPPgetPd in *.
apply Hroot in  Hpppd.
clear Hroot.
destruct Hpppd as (nbL & HnbL & stop & Hstop & Hind).
subst.
rewrite <- HnbL in *.
assert(Hgetind : getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s  
= Some ptvaInAncestor).
{ apply getIndirectionStopLevelGT2 with (nbL+1);trivial.
  lia.
  apply getNbLevelEq in HnbL.
  rewrite HnbL.
  unfold CLevel.
  case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
  simpl;trivial.
  assert(0<nbLevel) by apply nbLevelNotZero.
  lia. }
  rewrite Hgetind in *.

rewrite Hdef in *.
destruct ( StateLib.readPresent ptvaInAncestor
(StateLib.getIndexOfAddr vaInAncestor levelMin) 
(memory s));try now contradict Hacce.
destruct b;try now contradict Hacce.
destruct ( StateLib.readAccessible ptvaInAncestor
(StateLib.getIndexOfAddr vaInAncestor levelMin) 
(memory s)); try now contradict Hacce.
destruct b; try now contradict Hacce.
unfold StateLib.readPhyEntry in *.
 
rewrite Hlookup in *.
apply beq_nat_true in Hfalse.
inversion Hacce.
subst.
destruct phypage; destruct (pa entry).
simpl in *.
subst.
f_equal; apply proof_irrelevance.
Qed.

Lemma isAccessibleMappedPage' part pdChild currentPD (ptPDChild : page)  entry s : 
(Nat.eqb pageDefault ptPDChild ) = false -> 
entryPresentFlag ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) true s -> 
entryUserFlag ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) true s -> 
lookup ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) (memory s) pageEq idxEq =
    Some (PE entry) -> 
 nextEntryIsPP part idxPageDir currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr pdChild levelMin = idx ->
isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild idxPageDir part pdChild s ) -> 
getAccessibleMappedPage currentPD s pdChild = SomePage (pa entry).
Proof.
intros Hnotnull Hpe Hue Hlookup Hpp Hget .
assert ( isPE ptPDChild (StateLib.getIndexOfAddr pdChild levelMin) s /\ 
        getTableAddrRoot ptPDChild idxPageDir part pdChild s) as (_ & Hroot).
apply Hget; trivial.
clear Hget. 
unfold getAccessibleMappedPage.
unfold getTableAddrRoot in *.
destruct Hroot  as (_ & Hroot).
apply Hroot in Hpp; clear Hroot.
destruct Hpp as (nbL & HnbL & stop & Hstop & Hind).
rewrite <- HnbL.
subst.
assert (Hnewind : getIndirection currentPD pdChild nbL (nbLevel - 1) s= Some ptPDChild).
apply getIndirectionStopLevelGT2 with (nbL + 1);try lia;trivial.
apply getNbLevelEq in HnbL.
unfold CLevel in HnbL.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros; rewrite H in *.
destruct nbL.
simpl in *.
inversion HnbL; trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
rewrite Hnewind.
apply entryPresentFlagReadPresent in Hpe.
rewrite Hpe.
apply entryUserFlagReadAccessible in Hue.
rewrite Hue.
unfold StateLib.readPhyEntry.
rewrite Hnotnull.
rewrite Hlookup; trivial.
Qed.



Lemma isAccessibleMappedPageInParentTruePresentAccessible s (va vaInAncestor:vaddr) 
ptvaInAncestor entry descParent L sh2 (ptsh2 ancestor pdAncestor: page):
isAccessibleMappedPageInParent descParent va (pa entry) s = true -> 
nextEntryIsPP descParent idxShadow2 sh2 s-> 
isPE ptvaInAncestor ( StateLib.getIndexOfAddr vaInAncestor levelMin) s -> 
getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s ->
(Nat.eqb pageDefault ptvaInAncestor) = false -> 
Some L = StateLib.getNbLevel -> 
(Nat.eqb pageDefault ptsh2) = false -> 
isVA' ptsh2 (StateLib.getIndexOfAddr va levelMin) vaInAncestor s -> 
isVA ptsh2 (StateLib.getIndexOfAddr va levelMin) s -> 
getTableAddrRoot ptsh2 idxShadow2 descParent va s -> 
nextEntryIsPP descParent idxParentDesc ancestor s -> 
nextEntryIsPP ancestor idxPageDir pdAncestor s -> 
entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) true s
/\ entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) true s.
Proof.
intros HaccessInParent Hcursh2 Hva Hget Hnotnull.
intros.
unfold isAccessibleMappedPageInParent in HaccessInParent.
apply nextEntryIsPPgetSndShadow in Hcursh2.
rewrite Hcursh2 in HaccessInParent.
assert(Hvainparent : getVirtualAddressSh2 sh2 s va = Some vaInAncestor). 
apply getVirtualAddressSh2GetTableRoot with ptsh2 descParent L;trivial.
intros;split;subst;trivial. 
rewrite Hvainparent in *.
assert(Hgetparent : StateLib.getParent descParent (memory s) = Some ancestor).
{ apply nextEntryIsPPgetParent;trivial. }
rewrite Hgetparent in *.
assert(Hgetpdparent : StateLib.getPd ancestor (memory s) = Some pdAncestor).
{ apply nextEntryIsPPgetPd;trivial. }
rewrite Hgetpdparent in *.
case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor ); intros * Hi ;
rewrite Hi in *;try now contradict Hi.
unfold getAccessibleMappedPage in Hi.
assert(HnbL: Some L = StateLib.getNbLevel) by trivial.
rewrite <- HnbL in *.
unfold getTableAddrRoot in Hget.
destruct Hget as (_ & Hget).
apply nextEntryIsPPgetPd in Hgetpdparent.
apply Hget in Hgetpdparent.
destruct Hgetpdparent as (nbL & HnbL' & stop & Hstop & Hgettable).
clear Hget.
rewrite <- HnbL' in *.
inversion HnbL.
subst.
assert(Hind :getIndirection pdAncestor vaInAncestor nbL (nbLevel - 1) s = Some ptvaInAncestor).
apply getIndirectionStopLevelGT2 with (nbL+1);trivial.
lia.
apply getNbLevelEq in HnbL'.
rewrite HnbL'.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
rewrite Hind in *.
rewrite Hnotnull in *.
case_eq (StateLib.readPresent ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin)
(memory s));[intros pres Hpres|intros Hpres];rewrite Hpres in *; try now contradict Hi.
case_eq pres;intros;subst; try now contradict Hi.
rewrite entryPresentFlagReadPresent';split;trivial.
    case_eq (StateLib.readAccessible ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin)
(memory s));[intros pres Hacc|intros Hacc];rewrite Hacc in *; try now contradict Hi.
case_eq pres;intros;subst; try now contradict Hi.
rewrite entryUserFlagReadAccessible;trivial.
Qed.
 Lemma pdPartNotNull' phyDescChild pdChildphy s:
In phyDescChild (getPartitions pageRootPartition s) -> 
nextEntryIsPP phyDescChild idxPageDir pdChildphy s -> 
partitionDescriptorEntry s -> 
(Nat.eqb pageDefault pdChildphy) = false.
Proof.
intros. 
 unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP phyDescChild idxPageDir entry s /\ entry <> pageDefault)).
        apply H1;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
assert(entryPd = pdChildphy).
apply getPdNextEntryIsPPEq  with phyDescChild s;trivial.
apply nextEntryIsPPgetPd;trivial.
subst;trivial.
apply PeanoNat.Nat.eqb_neq.
symmetrynot.
unfold not;intros.
apply Hnotnull.
destruct pdChildphy;simpl in *.
destruct pageDefault;simpl in *.
subst.

f_equal.
trivial.
apply proof_irrelevance.
Qed.

Lemma getAccessibleMappedPageInAncestor  descParent va entry pdAncestor s vaInAncestor sh2 ptsh2 ancestor:
isAccessibleMappedPageInParent descParent va (pa entry) s = true -> 
 nextEntryIsPP descParent idxShadow2 sh2 s -> 
  isVA ptsh2 (StateLib.getIndexOfAddr va levelMin) s ->  
        getTableAddrRoot ptsh2 idxShadow2 descParent va s -> 
        isVA' ptsh2 (StateLib.getIndexOfAddr va levelMin) vaInAncestor s -> 
        (Nat.eqb pageDefault ptsh2) = false -> 
         nextEntryIsPP descParent idxParentDesc ancestor s -> 
         nextEntryIsPP ancestor idxPageDir pdAncestor s -> 
 getAccessibleMappedPage pdAncestor s vaInAncestor = SomePage (pa entry)      .
 Proof.
 intros HaccessInParent Hcursh2 Hva Hgetva Hisva Hptnotnull.
 intros.
unfold isAccessibleMappedPageInParent in HaccessInParent.
(** Here we use the property already present into the precondition : 
    *)
apply nextEntryIsPPgetSndShadow in Hcursh2.
rewrite Hcursh2 in HaccessInParent.
assert(Hvainparent : getVirtualAddressSh2 sh2 s va = Some vaInAncestor).
{ 

unfold getVirtualAddressSh2.
unfold getTableAddrRoot in Hgetva.
destruct Hgetva as (_ & Hgetva).
assert(HcurSh2 : nextEntryIsPP descParent idxShadow2 sh2 s).
rewrite  nextEntryIsPPgetSndShadow ;trivial.
apply Hgetva in HcurSh2.
destruct HcurSh2 as (nbL & HnbL & stop & Hstop & Hind).
rewrite <- HnbL.
subst.
assert(Hgetind : getIndirection sh2 va nbL (nbLevel - 1) s = Some ptsh2).
apply getIndirectionStopLevelGT2 with (nbL + 1);trivial.
lia.
apply getNbLevelEq in HnbL.
rewrite HnbL.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel);intros.
simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
lia.
rewrite Hgetind.
rewrite Hptnotnull.
unfold  isVA' in *. 
unfold StateLib.readVirtual. 
destruct(lookup ptsh2 (StateLib.getIndexOfAddr va levelMin) (memory s) pageEq idxEq ); 
try now contradict Hisva.
destruct v;try now contradict Hisva.
subst. trivial. }
rewrite Hvainparent in *.
assert(Hgetparent : StateLib.getParent descParent (memory s) = Some ancestor).
{ apply nextEntryIsPPgetParent;trivial. }
rewrite Hgetparent in *.
assert(Hgetpdparent : StateLib.getPd ancestor (memory s) = Some pdAncestor).
{ apply nextEntryIsPPgetPd;trivial. }
rewrite Hgetpdparent in *.
case_eq(getAccessibleMappedPage pdAncestor s vaInAncestor ); intros * Hi ;
rewrite Hi in *;try now contradict HaccessInParent.
f_equal.
apply beq_nat_true in HaccessInParent.
symmetry;trivial.
destruct p;simpl in *.
destruct (pa entry);simpl in *.
subst.
f_equal.
apply proof_irrelevance.
Qed.

Lemma parentMultNone descParent s:
true = pageEq descParent pageRootPartition ->
consistency s -> 
StateLib.getParent descParent (memory s) = None.
Proof.
intros Hmult Hcons.
unfold pageEq in *.
assert(Hismult : true = (Nat.eqb descParent pageRootPartition)) by trivial.
symmetry in Hismult.
apply  beq_nat_true in Hismult.

unfold consistency in *.

assert(Hmultcons : multiplexerWithoutParent s) by intuition.
revert Hismult Hmultcons.
clear.
intros.
unfold multiplexerWithoutParent in *.
rewrite <- Hmultcons.
f_equal.
destruct  descParent; destruct pageRootPartition.
simpl in *.
subst.
f_equal.
apply proof_irrelevance. 
Qed.

Lemma childAncestorConfigTablesAreDifferent s (child parent ancestor :page)(ptchild ptAncestor: page)
(vaInchild vaInAncestor: vaddr):
isAncestor  child parent s -> 
consistency s -> 
In child (getPartitions pageRootPartition s) -> 
nextEntryIsPP parent idxParentDesc ancestor s ->
isPE ptchild (StateLib.getIndexOfAddr vaInchild levelMin) s -> 
getTableAddrRoot ptchild idxPageDir child vaInchild s-> 
(Nat.eqb pageDefault ptchild) = false -> 
In ancestor (getPartitions pageRootPartition s) -> 
isPE ptAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) s -> 
getTableAddrRoot ptAncestor idxPageDir ancestor vaInAncestor s ->
(Nat.eqb pageDefault ptAncestor) = false -> 
ptchild <> ptAncestor.
Proof.
intros   Hisancestor.
intros.  
unfold isAncestor in *.
destruct Hisancestor as [Hisancestor | Hisancestor].
- subst.
(*             rewrite Hisancestor in *. *)
unfold consistency in *.
assert(parent <> ancestor).
{ assert(Hdiff : noCycleInPartitionTree s) by
  intuition.
  unfold noCycleInPartitionTree in *.
  unfold not;intros Hii;symmetry in Hii;contradict Hii.
  apply Hdiff;trivial.
  apply parentIsAncestor;trivial. }
assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
unfold configTablesAreDifferent in *.
assert(Hdisjoint : disjoint (getConfigPages parent  s) (getConfigPages ancestor s)).
apply Hconfigdiff;trivial.
(*             assert(Hparet : parentInPartitionList s) by intuition.
unfold parentInPartitionList in *.
apply Hparet with (currentPartition s) ;trivial. *)
assert(Hin1 : In ptchild (getConfigPages parent  s)).
apply isConfigTable with vaInchild;trivial.
intuition.
 intros;subst;split;trivial.
assert(Hin2: In ptAncestor (getConfigPages ancestor s)).
apply isConfigTable with vaInAncestor;trivial.
intuition.
intros;subst;split;trivial.
unfold disjoint in *.
apply Hdisjoint in Hin1.
unfold not;intros; subst.
now contradict Hin2.
- unfold consistency in *.
subst.            
assert(In child (getPartitions pageRootPartition s)).
unfold currentPartitionInPartitionsList in *.
intuition.
assert(child <> ancestor).
{  unfold not;intros Hii;symmetry in Hii;contradict Hii.
assert (Hnocycle : noCycleInPartitionTree s) by intuition.
unfold noCycleInPartitionTree in *.
apply Hnocycle;trivial.
unfold consistency in *.
apply isAncestorTrans2 with parent;trivial.
intuition. intuition.
unfold consistency in *. intuition.
apply nextEntryIsPPgetParent;trivial. }
assert(Hconfigdiff :configTablesAreDifferent s) by intuition.
unfold configTablesAreDifferent in *. 
assert(Hdisjoint : disjoint (getConfigPages child s) (getConfigPages ancestor s)).
apply Hconfigdiff;trivial.
assert(Hin1 : In ptchild (getConfigPages child s)).
apply isConfigTable with vaInchild;trivial.
intuition.
intros;subst;split;trivial.

assert(Hin2: In ptAncestor (getConfigPages ancestor s)).
apply isConfigTable with vaInAncestor;trivial.
intuition.
intros;subst;split;trivial.
assert(Hparet : parentInPartitionList s) by intuition.
unfold parentInPartitionList in *.

unfold disjoint in *.
apply Hdisjoint in Hin1.
unfold not;intros; subst.
now contradict Hin2.
Qed.


Lemma structIndirectionIsnotnull (indSh2ToPrepare indMMUToPrepare phySh2Child descChildphy phyPDChild : page)
(vaToPrepare: vaddr) (l levelpred: level) idxroot s: 
(idxroot = idxShadow1 \/ idxroot = idxShadow2) -> 
consistency s -> 
(Nat.eqb pageDefault indMMUToPrepare) = false -> 
indirectionDescription s descChildphy phyPDChild idxPageDir vaToPrepare l -> 
indirectionDescription s descChildphy phySh2Child idxroot vaToPrepare l -> 
   false = levelEq l levelMin -> 
isEntryPage phyPDChild (StateLib.getIndexOfAddr vaToPrepare l) indMMUToPrepare s -> 
StateLib.Level.pred l = Some levelpred ->
isEntryPage phySh2Child (StateLib.getIndexOfAddr vaToPrepare l) indSh2ToPrepare s -> 
Some l = StateLib.getNbLevel -> 
   In descChildphy (getPartitions pageRootPartition s) -> 
(Nat.eqb pageDefault indSh2ToPrepare) = false.

Proof.
intros Hor Hconsistency Hmmunotnull Hmmu Hstruct Hnotfstlevel Hpemmu Hlvlpred Hpestruct Hlvl.
intros.
assert(Hcons : wellFormedShadows idxroot s ).
{ destruct Hor;subst;(unfold consistency in *;intuition). }
unfold indirectionDescription in Hmmu.
destruct Hmmu as ( mmuroot  & idxmmuroot & ( Hnotnullmm & 
                    [(Hroot & Hlvlmmu) | (nbL & stop & Hnbl &Hstople &Hind & Hindnotnull & Hstop)])).
+ (* root *) 
  subst.
  unfold indirectionDescription in Hstruct.
  destruct Hstruct as ( root  & idxrootstruct & ( Hnotnullstruct & 
                  [(Hroot & Hlvlstruct) | (nbL & stop & Hnbl &Hstople &Hind & Hindnotnull & Hstop)])).
  - subst.
    unfold  wellFormedShadows in Hcons.
    assert(Hconsinst: exists indirection2 : page,
    getIndirection phySh2Child vaToPrepare l 1 s = Some indirection2 /\
    (Nat.eqb pageDefault indirection2) = false).
    apply Hcons with descChildphy phyPDChild indMMUToPrepare;trivial.
    apply nextEntryIsPPgetPd;trivial.
    simpl.
    rewrite <- Hnotfstlevel.
    apply isEntryPageReadPhyEntry1 in Hpemmu.
    rewrite Hpemmu.
    rewrite Hmmunotnull.
    
    rewrite Hlvlpred.
    trivial.
    destruct Hconsinst as (x & Hconsind & Hconsindnotnull).
    clear Hcons.
    simpl in *.
    rewrite <- Hnotfstlevel in Hconsind.
    apply isEntryPageReadPhyEntry1 in Hpestruct.
    rewrite Hpestruct in Hconsind.
    case_eq(Nat.eqb pageDefault indSh2ToPrepare) ; intros Hisdefaut; 
    rewrite Hisdefaut in Hconsind.
    inversion Hconsind as (Hx).
    subst.
    rewrite <- Hconsindnotnull.
    symmetry.
    apply PeanoNat.Nat.eqb_refl.
    trivial.
  - subst. rewrite <- Hlvl in Hnbl.
    inversion Hnbl as (Hstop).
    assert(stop = 0). 
    { apply ClevelMinus0Eq with nbL;trivial. }
    subst.
    simpl in *.
    inversion Hind.
    subst.
    unfold  wellFormedShadows in Hcons.
    assert(Hconsinst: exists indirection2 : page,
    getIndirection phySh2Child vaToPrepare (CLevel (nbL - 0)) 1 s = Some indirection2 /\
    (Nat.eqb pageDefault indirection2) = false).
    apply Hcons with descChildphy phyPDChild indMMUToPrepare;trivial.
    apply nextEntryIsPPgetPd;trivial.
     simpl.
    rewrite <- Hnotfstlevel.
    apply isEntryPageReadPhyEntry1 in Hpemmu.
    rewrite Hpemmu.
    rewrite Hmmunotnull.
    rewrite Hlvlpred.
    trivial.
    destruct Hconsinst as (x & Hconsind & Hconsindnotnull).
    clear Hcons.
    simpl in *.
    rewrite <- Hnotfstlevel in Hconsind.
    apply isEntryPageReadPhyEntry1 in Hpestruct.
    rewrite Hpestruct in Hconsind.
    case_eq(Nat.eqb pageDefault indSh2ToPrepare) ; intros Hisdefaut; 
    rewrite Hisdefaut in Hconsind.
    inversion Hconsind as (Hx).
    subst.
    rewrite <- Hconsindnotnull.
    symmetry.
    apply PeanoNat.Nat.eqb_refl.
    trivial.
+ (* middle *) 
  subst.
  unfold wellFormedShadows in Hcons.
  unfold indirectionDescription in Hstruct.
  destruct Hstruct as ( structroot  & idxrootstruct & ( Hnotnullstruct & 
                  [(Hroot & Hlvlstruct) | (nbL1 & stop1 & Hnbl1 &Hstople1 &Hind1 & Hindnotnull1 & Hstop1)])).
  - subst phySh2Child.
    subst. rewrite <- Hlvl in Hnbl.
    inversion Hnbl as (Hstop).
    assert(stop = 0). 
    { apply ClevelMinus0Eq with nbL;trivial. }
    subst.
    simpl in *.
    inversion Hind.
    subst phyPDChild.
    assert(Hconsinst: exists indirection2 : page,
    getIndirection structroot vaToPrepare (CLevel (nbL - 0)) 1 s = Some indirection2 /\
    (Nat.eqb pageDefault indirection2) = false).
    apply Hcons with descChildphy mmuroot indMMUToPrepare;trivial.
    apply nextEntryIsPPgetPd;trivial.
     simpl.
    rewrite <- Hnotfstlevel.
    apply isEntryPageReadPhyEntry1 in Hpemmu.
    rewrite Hpemmu.
    rewrite Hmmunotnull.
    rewrite Hlvlpred.
    trivial.
    destruct Hconsinst as (x & Hconsind & Hconsindnotnull).
    clear Hcons.
    simpl in *.
    rewrite <- Hnotfstlevel in Hconsind.
    apply isEntryPageReadPhyEntry1 in Hpestruct.
    rewrite Hpestruct in Hconsind.
    case_eq(Nat.eqb pageDefault indSh2ToPrepare) ; intros Hisdefaut; 
    rewrite Hisdefaut in Hconsind.
    inversion Hconsind as (Hx).
    subst.
    rewrite <- Hconsindnotnull.
    symmetry.
    apply PeanoNat.Nat.eqb_refl.
    trivial.
  - rewrite <- Hnbl1 in Hnbl.
    inversion Hnbl.
    subst nbL1.
    assert(stop = stop1).
    { assert(nbL - stop = nbL -stop1).
      apply levelEqNat.
      clear.
      destruct stop. destruct nbL.
      simpl in *.
      lia.
      destruct nbL.
      simpl.
      lia.
      destruct stop1. destruct nbL.
      simpl in *.
      lia.
      destruct nbL.
      simpl.
      lia. trivial.
      lia. }
    subst stop1.
    assert(Hconsinst: exists indirection2 : page,
    getIndirection structroot vaToPrepare nbL (stop+1) s = Some indirection2 /\
    (Nat.eqb pageDefault indirection2) = false).
    { apply Hcons with descChildphy mmuroot indMMUToPrepare;trivial.
      apply nextEntryIsPPgetPd;trivial.
      apply getIndirectionStopS1 with phyPDChild;trivial.
      assert(stop < nbL).
      symmetry in Hnotfstlevel. apply levelEqBEqNatFalse0 in Hnotfstlevel.
      apply level_gt in Hnotfstlevel.
      lia.
      clear.
      destruct stop. destruct nbL.
      simpl in *.
      lia.
      destruct nbL.
      simpl.
      lia.
      lia.
      simpl.
      simpl.
      rewrite <- Hnotfstlevel.
      apply isEntryPageReadPhyEntry1 in Hpemmu.
      rewrite Hpemmu.
      rewrite Hmmunotnull.
      rewrite Hlvlpred.
      trivial. }
      destruct Hconsinst as (x & Hconsind & Hconsindnotnull).
      clear Hcons.
      assert(Hsamelevel: Some x = Some indSh2ToPrepare).
      {
      rewrite <- Hconsind.
      clear Hconsind.
      apply getIndirectionStopS1 with phySh2Child;trivial.
      assert(stop < nbL).
      symmetry in Hnotfstlevel. apply levelEqBEqNatFalse0 in Hnotfstlevel.
      apply level_gt in Hnotfstlevel.
      lia.
      clear.
      destruct stop. destruct nbL.
      simpl in *.
      lia.
      destruct nbL.
      simpl.
      lia.
      lia.
      simpl.
      simpl.
      rewrite <- Hnotfstlevel.
      apply isEntryPageReadPhyEntry1 in Hpestruct.
      rewrite Hpestruct.
      case_eq(Nat.eqb pageDefault indSh2ToPrepare);intros Hnull.
      apply beq_nat_true in Hnull.
      f_equal. revert Hnull.
      clear. intros.
      destruct pageDefault;simpl in *.
      destruct indSh2ToPrepare;simpl in *.
      subst.
      f_equal.
      apply proof_irrelevance.
      rewrite Hlvlpred.
      trivial. }
      inversion Hsamelevel.
      subst;trivial.
Qed.
Lemma structIndirectionIsnotnullMiddle (indSh2ToPrepare indMMUToPrepare phySh2Child descChildphy phyPDChild : page)
(vaToPrepare: vaddr) (l levelpred: level) (stopl : nat) idxroot s: 
(idxroot = idxShadow1 \/ idxroot = idxShadow2) -> 
consistency s -> 
(Nat.eqb pageDefault indMMUToPrepare) = false -> 
indirectionDescription s descChildphy phyPDChild idxPageDir vaToPrepare (CLevel (l - stopl)) -> 
indirectionDescription s descChildphy phySh2Child idxroot vaToPrepare (CLevel (l - stopl)) -> 
   false = levelEq (CLevel (l - stopl)) levelMin -> 
isEntryPage phyPDChild (StateLib.getIndexOfAddr vaToPrepare (CLevel (l - stopl))) indMMUToPrepare s -> 
StateLib.Level.pred (CLevel (l - stopl)) = Some levelpred ->
isEntryPage phySh2Child (StateLib.getIndexOfAddr vaToPrepare (CLevel (l - stopl))) indSh2ToPrepare s -> 
Some l = StateLib.getNbLevel -> 
stopl <= l -> 
   In descChildphy (getPartitions pageRootPartition s) -> 
(Nat.eqb pageDefault indSh2ToPrepare) = false.
Proof.
intros Hor Hconsistency Hmmunotnull Hmmu Hstruct Hnotfstlevel Hpemmu Hlvlpred Hpestruct Hlvl.
intros.
assert(Hcons : wellFormedShadows idxroot s ).
{ destruct Hor;subst;(unfold consistency in *;intuition). }
unfold indirectionDescription in Hmmu.
destruct Hmmu as ( mmuroot  & idxmmuroot & ( Hnotnullmm & 
                    [(Hroot & Hlvlmmu) | (nbL & stop & Hnbl &Hstople &Hind & Hindnotnull & Hstop)])).
+ (* root *) 
  subst.
  unfold indirectionDescription in Hstruct.
  destruct Hstruct as ( root  & idxrootstruct & ( Hnotnullstruct & 
                  [(Hroot & Hlvlstruct) | (nbL & stop & Hnbl &Hstople &Hind & Hindnotnull & Hstop)])).
  - subst.
    unfold  wellFormedShadows in Hcons.
    assert(Hconsinst: exists indirection2 : page,
    getIndirection phySh2Child vaToPrepare (CLevel (l - stopl)) 1 s = Some indirection2 /\
    (Nat.eqb pageDefault indirection2) = false).
    apply Hcons with descChildphy phyPDChild indMMUToPrepare;trivial.
    apply nextEntryIsPPgetPd;trivial.
    simpl.
    rewrite <- Hnotfstlevel.
    apply isEntryPageReadPhyEntry1 in Hpemmu.
    rewrite Hpemmu.
    rewrite Hmmunotnull.    
    rewrite Hlvlpred.
    trivial.
    destruct Hconsinst as (x & Hconsind & Hconsindnotnull).
    clear Hcons.
    simpl in *.
    rewrite <- Hnotfstlevel in Hconsind.
    apply isEntryPageReadPhyEntry1 in Hpestruct.
    rewrite Hpestruct in Hconsind.
    case_eq(Nat.eqb pageDefault indSh2ToPrepare) ; intros Hisdefaut; 
    rewrite Hisdefaut in Hconsind.
    inversion Hconsind as (Hx).
    subst.
    rewrite <- Hconsindnotnull.
    symmetry.
    apply PeanoNat.Nat.eqb_refl.
    trivial.
  - rewrite <- Hnbl in Hlvl.
    inversion Hlvl.
    subst. 
    assert(stop = stopl).
    { assert(nbL - stop = nbL -stopl).
      apply levelEqNat.
      clear.
      destruct stop. destruct nbL.
      simpl in *.
      lia.
      destruct nbL.
      simpl.
      lia.
      destruct nbL.
      simpl in *.
      lia.
      symmetry;trivial.
      lia. }
    subst stopl.
    assert(stop = 0). 
    { apply ClevelMinus0Eq with nbL;trivial.
    rewrite <- Hlvlmmu in  Hnbl.
    clear Hor.
    intuition.
     inversion Hnbl as (Hi).
     f_equal.
     rewrite <- Hi.
     lia. }
    subst.
    simpl in *.
    inversion Hind.
    subst.
    unfold  wellFormedShadows in Hcons.
    assert(Hconsinst: exists indirection2 : page,
    getIndirection phySh2Child vaToPrepare (CLevel (nbL - 0)) 1 s = Some indirection2 /\
    (Nat.eqb pageDefault indirection2) = false).
    apply Hcons with descChildphy phyPDChild indMMUToPrepare;trivial.
    apply nextEntryIsPPgetPd;trivial.
     simpl.
    rewrite <- Hnotfstlevel.
    apply isEntryPageReadPhyEntry1 in Hpemmu.
    rewrite Hpemmu.
    rewrite Hmmunotnull.
    rewrite Hlvlpred.
    trivial.
    destruct Hconsinst as (x & Hconsind & Hconsindnotnull).
    clear Hcons.
    simpl in *.
    rewrite <- Hnotfstlevel in Hconsind.
    apply isEntryPageReadPhyEntry1 in Hpestruct.
    rewrite Hpestruct in Hconsind.
    case_eq(Nat.eqb pageDefault indSh2ToPrepare) ; intros Hisdefaut; 
    rewrite Hisdefaut in Hconsind.
    inversion Hconsind as (Hx).
    subst.
    rewrite <- Hconsindnotnull.
    symmetry.
    apply PeanoNat.Nat.eqb_refl.
    trivial.
+ (* middle *) 
  subst.
  unfold wellFormedShadows in Hcons.
  unfold indirectionDescription in Hstruct.
  destruct Hstruct as ( structroot  & idxrootstruct & ( Hnotnullstruct & 
                  [(Hroot & Hlvlstruct) | (nbL1 & stop1 & Hnbl1 &Hstople1 &Hind1 & Hindnotnull1 & Hstop1)])).
  - subst phySh2Child.
    subst. rewrite <- Hlvl in Hnbl.
    inversion Hnbl as (Hstopl).
    subst.
    assert(stop = stopl).
    { assert(l - stop = l -stopl).
      apply levelEqNat.
      clear.
      destruct stop. destruct l.
      simpl in *.
      lia.
      destruct l.
      simpl.
      lia.
      destruct l.
      simpl in *.
      lia.
      symmetry;trivial.
      lia. }
    subst stopl.
    assert(stop = 0). 
    { apply ClevelMinus0Eq with l;trivial.
    rewrite <- Hlvlstruct in  Hlvl.
    clear Hor.
    intuition.
     inversion Hlvl as (Hi).
     f_equal.
     rewrite <- Hi.
     lia. }
    subst.
    simpl in *.
    inversion Hind.
    subst phyPDChild.
    assert(Hconsinst: exists indirection2 : page,
    getIndirection structroot vaToPrepare (CLevel (l - 0)) 1 s = Some indirection2 /\
    (Nat.eqb pageDefault indirection2) = false).
    apply Hcons with descChildphy mmuroot indMMUToPrepare;trivial.
    apply nextEntryIsPPgetPd;trivial.
     simpl.
    rewrite <- Hnotfstlevel.
    apply isEntryPageReadPhyEntry1 in Hpemmu.
    rewrite Hpemmu.
    rewrite Hmmunotnull.
    rewrite Hlvlpred.
    trivial.
    destruct Hconsinst as (x & Hconsind & Hconsindnotnull).
    clear Hcons.
    simpl in *.
    rewrite <- Hnotfstlevel in Hconsind.
    apply isEntryPageReadPhyEntry1 in Hpestruct.
    rewrite Hpestruct in Hconsind.
    case_eq(Nat.eqb pageDefault indSh2ToPrepare) ; intros Hisdefaut; 
    rewrite Hisdefaut in Hconsind.
    inversion Hconsind as (Hx).
    subst.
    rewrite <- Hconsindnotnull.
    symmetry.
    apply PeanoNat.Nat.eqb_refl.
    trivial.
  - rewrite <- Hnbl1 in Hnbl.
    inversion Hnbl.
    subst nbL1.
    rewrite <- Hnbl1 in Hlvl.
    inversion Hlvl.
    subst.
    rewrite Hstop1 in Hstop.
    symmetry in Hstop.
    assert(stop = stop1).
    { assert(nbL - stop = nbL -stop1).
      apply levelEqNat.
      clear.
      destruct nbL.
      simpl in *.
      lia.
      destruct nbL.
      simpl.
      lia.
      trivial. destruct nbL.
      simpl in *.
      lia. }
    subst stop1.
    assert(stop = stopl).
    { assert(nbL - stop = nbL -stopl).
      apply levelEqNat.
      clear.
      destruct nbL.
      simpl in *.
      lia.
      destruct nbL.
      simpl.
      lia.
      symmetry.
      trivial. destruct nbL.
      simpl in *.
      lia. }
    subst stopl.    
    assert(Hconsinst: exists indirection2 : page,
    getIndirection structroot vaToPrepare nbL (stop+1) s = Some indirection2 /\
    (Nat.eqb pageDefault indirection2) = false).
    { apply Hcons with descChildphy mmuroot indMMUToPrepare;trivial.
      apply nextEntryIsPPgetPd;trivial.
      apply getIndirectionStopS1 with phyPDChild;trivial.
      assert(stop < nbL).
      symmetry in Hnotfstlevel. apply levelEqBEqNatFalse0 in Hnotfstlevel.
      apply level_gt in Hnotfstlevel.
      lia.
      clear.
      destruct stop. destruct nbL.
      simpl in *.
      lia.
      destruct nbL.
      simpl.
      lia.
      lia.
      simpl.
      simpl.
      rewrite <- Hnotfstlevel.
      apply isEntryPageReadPhyEntry1 in Hpemmu.
      rewrite Hpemmu.
      rewrite Hmmunotnull.
      rewrite Hlvlpred.
      trivial. }
      destruct Hconsinst as (x & Hconsind & Hconsindnotnull).
      clear Hcons.
      assert(Hsamelevel: Some x = Some indSh2ToPrepare).
      {
      rewrite <- Hconsind.
      clear Hconsind.
      apply getIndirectionStopS1 with phySh2Child;trivial.
      assert(stop < nbL).
      symmetry in Hnotfstlevel. apply levelEqBEqNatFalse0 in Hnotfstlevel.
      apply level_gt in Hnotfstlevel.
      lia.
      clear.
      destruct stop. destruct nbL.
      simpl in *.
      lia.
      destruct nbL.
      simpl.
      lia.
      lia.
      simpl.
      simpl.
      rewrite <- Hnotfstlevel.
      apply isEntryPageReadPhyEntry1 in Hpestruct.
      rewrite Hpestruct.
      case_eq(Nat.eqb pageDefault indSh2ToPrepare);intros Hnull.
      apply beq_nat_true in Hnull.
      f_equal. revert Hnull.
      clear. intros.
      destruct pageDefault;simpl in *.
      destruct indSh2ToPrepare;simpl in *.
      subst.
      f_equal.
      apply proof_irrelevance.
      rewrite Hlvlpred.
      trivial. }
      inversion Hsamelevel.
      subst;trivial.
Qed.
Lemma proveInitPEntryTablePreconditionToPropagatePrepareProperties s userPage (pt:page) vaValue part nbL pdPart  :
consistency s -> 
kernelDataIsolation s ->
In part (getPartitions pageRootPartition s) ->
(Nat.eqb pageDefault pt) = false -> 
nextEntryIsPP part idxPageDir pdPart s -> 
Some nbL = StateLib.getNbLevel -> 
isPE pt (StateLib.getIndexOfAddr vaValue levelMin) s /\ getTableAddrRoot pt idxPageDir part vaValue s -> 
entryPresentFlag pt (StateLib.getIndexOfAddr vaValue levelMin) true s -> 
entryUserFlag pt (StateLib.getIndexOfAddr vaValue levelMin) true s -> 
isEntryPage pt (StateLib.getIndexOfAddr vaValue levelMin) userPage s ->  
initPEntryTablePreconditionToPropagatePrepareProperties s userPage.
Proof.
intros Hcons Hkdi.
unfold initPEntryTablePreconditionToPropagatePrepareProperties.
split. 
+ intros.
unfold  consistency in *.
assert (Hcurpart : currentPartitionInPartitionsList s) by intuition.
unfold currentPartitionInPartitionsList in *; trivial. 
assert (Hkernel : kernelDataIsolation s) by intuition.
unfold kernelDataIsolation in Hkernel.
unfold Lib.disjoint in Hkernel.
apply Hkernel with part; trivial.
intuition.
eapply physicalPageIsAccessible with pt vaValue (StateLib.getIndexOfAddr vaValue levelMin)  
true nbL true pdPart;intuition;subst;trivial.
+ apply phyPageNotDefault with pt(StateLib.getIndexOfAddr vaValue levelMin) s;trivial.
unfold consistency in *;intuition.
Qed.
    

Lemma isPartitionFalseProof  idxRefChild 
(currentShadow1 currentPart currentPD phyDescChild ptRefChild ptRefChildFromSh1:page) (descChild :vaddr) idx s :
consistency s ->
In currentPart (getPartitions pageRootPartition s) ->
nextEntryIsPP currentPart idxPageDir currentPD s ->
nextEntryIsPP currentPart idxShadow1 currentShadow1 s ->
(Nat.eqb pageDefault ptRefChild) = false ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild levelMin) true s ->
entryUserFlag ptRefChild (StateLib.getIndexOfAddr descChild levelMin) true s ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild levelMin) phyDescChild s ->
nextEntryIsPP (currentPartition s) idxPageDir currentPD s ->
StateLib.getIndexOfAddr descChild levelMin = idx ->
isPE ptRefChild idx s ->
getTableAddrRoot ptRefChild idxPageDir (currentPartition s) descChild s ->
(Nat.eqb ptRefChildFromSh1 pageDefault) = false ->
StateLib.getIndexOfAddr descChild levelMin = idxRefChild ->
isVE ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild levelMin) s ->
getTableAddrRoot ptRefChildFromSh1 idxShadow1 currentPart descChild s ->
isPartitionFalse ptRefChildFromSh1 idxRefChild s.
Proof.
intros.
unfold isPartitionFalse.
unfold consistency in *. 
assert(Haccessva : accessibleVAIsNotPartitionDescriptor s) by intuition.
unfold accessibleVAIsNotPartitionDescriptor in *.
assert (Hflag : getPDFlag currentShadow1 descChild s = false).
{ apply Haccessva with currentPart currentPD phyDescChild.
unfold consistency in *.
unfold currentPartitionInPartitionsList in *.
intuition.
apply nextEntryIsPPgetPd; intuition.
apply nextEntryIsPPgetFstShadow;intuition.  
apply isAccessibleMappedPage2 with (currentPartition s) ptRefChild;intuition;subst;trivial. }
apply getPDFlagReadPDflag with currentShadow1 descChild currentPart;trivial.
intuition;subst;trivial.
Qed.

Lemma getMaxIndexNotNone :
StateLib.getMaxIndex <> None.
Proof.
unfold StateLib.getMaxIndex.
pose proof tableSizeBigEnough.
case_eq(gt_dec tableSize 0);intros;simpl.
unfold not;intros.
now contradict H1.
lia.
Qed. 

Lemma readPhysicalIsPP' LLtable idx nextLLtable s:
isPP' LLtable idx nextLLtable s <->
StateLib.readPhysical LLtable idx (memory s) = Some nextLLtable.
Proof.
intros;
unfold isPP' in *;
unfold StateLib.readPhysical;
case_eq(lookup LLtable idx (memory s) pageEq idxEq);[intros v Hv|intros Hv].
destruct v;split;intros Hx;try now contradict Hx.
 f_equal; trivial.
inversion Hx;subst;trivial.
split;intros;trivial;try now contradict H.
Qed.
 Lemma pdPartNotNone phyDescChild s:
In phyDescChild (getPartitions pageRootPartition s) -> 
partitionDescriptorEntry s -> 
StateLib.getPd phyDescChild (memory s) = None -> False.
Proof.
intros. 
unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP phyDescChild idxPageDir entry s /\ entry <> pageDefault)).
        apply H0;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
apply nextEntryIsPPgetPd in Hpp.
rewrite Hpp in *.
now contradict H1.
Qed.

Lemma disjointSh2LLstruct tbl newLastLLable sh2 LL partition s: 
StateLib.getSndShadow partition (memory s) = Some sh2 ->
StateLib.getConfigTablesLinkedList partition (memory s) = Some LL -> 
consistency s ->
In partition (getPartitions pageRootPartition s) ->
In tbl (getIndirections sh2 s) ->
In newLastLLable (getLLPages LL s (nbPage + 1)) -> 
NoDup (getConfigPagesAux partition s) -> tbl <> newLastLLable.
Proof.
intros Hsh2 HLL Hcons Hpart Hi1 Hi2 Hnodup. 
unfold getConfigPagesAux in Hnodup.
case_eq(StateLib.getPd partition (memory s));intros pd Hpd.
2:{ assert False. apply pdPartNotNone with partition s;trivial. 
    unfold consistency in *;intuition. auto. }
rewrite Hpd in Hnodup.    
case_eq(StateLib.getFstShadow  partition (memory s));intros sh1 Hsh1.
2:{ assert False. apply sh1PartNotNone with partition s;trivial. 
    unfold consistency in *;intuition. auto. }
rewrite Hsh1 in Hnodup.
rewrite Hsh2 in Hnodup.
rewrite HLL in Hnodup.
apply Lib.NoDupSplit in Hnodup.
destruct Hnodup as (_ & Hnodup).
apply Lib.NoDupSplit in Hnodup.
destruct Hnodup as (_ & Hnodup).
apply Lib.NoDupSplitInclIff in Hnodup.
destruct Hnodup as (_ &  Hdisjoint).
unfold Lib.disjoint in *.
contradict Hi2.
apply Hdisjoint;subst;trivial.
Qed.

Lemma index0Ltfalse (idx:index):
idx < CIndex 0 -> False.
Proof.
intros.
unfold CIndex in H.
case_eq (lt_dec 0 tableSize).
intros.
rewrite H0 in H.
simpl in *. lia.
intros.
contradict H0.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
lia.
Qed.

  Lemma InDecOrNot (A:Type) (l:list A ) (elt: A) (P: forall p1 p2 : A, p1 = p2 \/ p1 <> p2):  
  In elt l \/ ~In elt l.
  Proof.
  revert elt.
  induction l;simpl.
    right;intuition.
    simpl.
    intros.
    subst.
    assert( a = elt \/ a <> elt )  by apply P.
    destruct H.
    do 2 left;trivial.
    generalize (IHl elt);clear IHl;intros IHl.
    destruct IHl.
    left.
    right;trivial.     
    right.
    intuition.
 Qed. 
Lemma isEntryPageReadPhyEntry2' table idx phy s:
isEntryPage table idx phy s -> 
StateLib.readPhyEntry table idx (memory s) = Some phy.
Proof.
intros Hentrypage.
unfold isEntryPage in *.
unfold StateLib.readPhyEntry.
destruct(lookup table idx (memory s) pageEq idxEq );
try now contradict Hentrypage.
destruct v; try now contradict Hentrypage.
f_equal;trivial.
Qed. 
   
  Lemma notInGetAccessibleMappedPage ptvaInAncestor ancestor phypage pdAncestor vaInAncestor s  : 
    noDupMappedPagesList s -> 
    In ancestor (getPartitions pageRootPartition s) -> 
  (forall idx : index,
   StateLib.getIndexOfAddr vaInAncestor levelMin = idx ->
   isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor idxPageDir ancestor vaInAncestor s) ->
  (Nat.eqb pageDefault ptvaInAncestor) = false ->
  isEntryPage ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) phypage s ->
  entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) true s ->
  entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor levelMin) false s ->
  nextEntryIsPP ancestor idxPageDir pdAncestor s ->
    ~In phypage (getAccessibleMappedPages ancestor s).
    Proof. 
  intros Hnodupmap Hpart Hget Hnotnull Hep Hpresent Huser Hpdparent.
destruct Hget with (StateLib.getIndexOfAddr vaInAncestor levelMin)
as (Hpe2 & Hroot2);trivial.
clear Hget.
unfold getTableAddrRoot in Hroot2.
destruct Hroot2 as (_ & Htableroot).
unfold getMappedPages.
assert(Hpd : StateLib.getPd ancestor (memory s) = Some pdAncestor).
apply nextEntryIsPPgetPd;trivial.
apply Htableroot in Hpdparent.
 clear Htableroot.
destruct Hpdparent as (nbL & HnbL & stop & Hstop & Hind ).
unfold getAccessibleMappedPages.
rewrite Hpd.
unfold getAccessibleMappedPagesAux.
rewrite filterOptionInIff.
unfold getAccessibleMappedPagesOption.
rewrite in_map_iff.
unfold not;intros Hfalse.
destruct Hfalse as (x & Hx1 & Hx2).
assert( getMappedPage pdAncestor s vaInAncestor = SomePage phypage).
apply getMappedPageGetIndirection with ancestor ptvaInAncestor nbL;trivial.
apply entryPresentFlagReadPresent;trivial.
apply nextEntryIsPPgetPd;trivial.
subst.
assert(Hnewind :getIndirection pdAncestor vaInAncestor nbL  (nbLevel - 1) s
 = Some ptvaInAncestor).
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
lia.
apply getNbLevelEq in HnbL.
subst.
apply nbLevelEq.
rewrite Hnewind.
trivial.

apply isEntryPageReadPhyEntry2';trivial.
assert(getMappedPage pdAncestor s x = SomePage phypage).
apply accessiblePAgeIsMapped;trivial.

assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaInAncestor va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).


assert(x = va1).
{ apply eqMappedPagesEqVaddrs with phypage pdAncestor s;trivial.
  rewrite <- H.
  symmetry.
  apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
      apply getNbLevelEqOption.
  unfold noDupMappedPagesList in *.
  unfold getMappedPages in *.
  apply Hnodupmap in Hpart.
  rewrite Hpd in *.  
  unfold getMappedPagesAux in *.
  trivial. }
subst x.
 
assert (  getAccessibleMappedPage pdAncestor s vaInAncestor = NonePage).
unfold getAccessibleMappedPage.
rewrite <- HnbL.
subst. 
assert(Hnewind :getIndirection pdAncestor vaInAncestor nbL  (nbLevel - 1) s
 = Some ptvaInAncestor).
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
lia.
apply getNbLevelEq in HnbL.
subst.
apply nbLevelEq.
rewrite Hnewind.
rewrite Hnotnull.
apply entryPresentFlagReadPresent in Hpresent.
rewrite Hpresent.
apply entryUserFlagReadAccessible in Huser.
rewrite Huser;trivial.
assert(getAccessibleMappedPage pdAncestor s va1 = getAccessibleMappedPage pdAncestor s vaInAncestor).
symmetry.
apply getAccessibleMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.
rewrite  H2 in *.
rewrite H1 in Hx1.
now contradict Hx1.  
Qed.
Lemma multiplexerIsAncestor s : 
 noDupPartitionTree s -> 
 forall partition, parentInPartitionList s ->  partitionDescriptorEntry s ->  isParent s ->  In partition (getPartitions pageRootPartition s)
-> In partition (getPartitions pageRootPartition s) -> 
    partition <> pageRootPartition -> 
    In pageRootPartition (getAncestors partition s).
Proof.
intro Hnoduptree.
intro. 
unfold getAncestors.
unfold getPartitions at 2.
intros Hparentintree Hpde Hisparent .
revert partition. 
induction (nbPage+1);simpl;intuition. 
case_eq(StateLib.getParent partition (memory s));[ intros parent Hparent | intros Hparent].
simpl. 
assert(Hor : parent = pageRootPartition \/ parent <> pageRootPartition) by apply pageDecOrNot.
destruct Hor as [Hor | Hor].
left;trivial.
right. 
apply IHn;trivial.
unfold parentInPartitionList in *.
apply Hparentintree with partition;trivial.
apply nextEntryIsPPgetParent;trivial.
apply getPartitionAuxMinus1 with partition;trivial.
unfold getPartitions.
destruct nbPage;left;trivial.
unfold partitionDescriptorEntry in *.
assert((exists entry : page,
nextEntryIsPP partition idxParentDesc entry s /\ entry <> pageDefault)).
apply Hpde;trivial.
do 4 right;left;trivial.
destruct H0 as (entry & Hi & _).
rewrite nextEntryIsPPgetParent in *.
rewrite Hi in Hparent. now contradict Hparent.
Qed.    
Lemma nextIndirectionNotAccessibleInAnyPartition s nextIndirection 
(currentPart currentPD: page) ptMMUvaNextInd (vaNextInd : vaddr) ptSh1VaNextInd:
writeAccessibleRecPreparePostcondition currentPart nextIndirection s ->
verticalSharing s -> 
partitionsIsolation s ->
consistency s -> 
(* noCycleInPartitionTree s ->
noDupMappedPagesList s ->  *)
In currentPart (getPartitions pageRootPartition s) -> 
getTableAddrRoot ptMMUvaNextInd idxPageDir currentPart vaNextInd s ->
isPE ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) s  ->
entryUserFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) false s ->
entryPresentFlag ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) true s ->
nextEntryIsPP currentPart idxPageDir currentPD s ->
(Nat.eqb pageDefault ptMMUvaNextInd) = false -> 
isEntryPage ptMMUvaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) nextIndirection s -> 
(exists va : vaddr,
   isEntryVA ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) va s /\
   vaddrEq vaddrDefault va = true) ->
(Nat.eqb pageDefault ptSh1VaNextInd) = false ->
getTableAddrRoot ptSh1VaNextInd idxShadow1 currentPart vaNextInd s ->
isVE ptSh1VaNextInd (StateLib.getIndexOfAddr vaNextInd levelMin) s ->


forall partition1, In partition1 (getPartitions pageRootPartition s) ->
   ~ In nextIndirection (getAccessibleMappedPages partition1 s).
Proof.
intros * Hancesnotaccecc Hvs Hiso Hcons  Hcurpart Htbl Hpe Huser Hpres Hcurpd Hnotdef Hispage
Hshare Hshdef Htblsh1 Hve * Hpart.
assert( noCycleInPartitionTree s /\ noDupMappedPagesList s ) as (Hcycle & Hnodupmap) by (unfold consistency in *;intuition).
(* check if partition1 is an ancestor of currentPart **)    
assert (Hances : In partition1 (getAncestors currentPart s) \/
  ~ In partition1 (getAncestors currentPart s)).
{ apply InDecOrNot.
  apply pageDecOrNot. }
destruct  Hances as [ Hances | Hances].
+ (** partition1 is ancestor of currentPart *)
  assert(Hor : partition1 <> currentPart).
  { unfold consistency in *. 
    unfold noCycleInPartitionTree in *.
    apply Hcycle;trivial. }
  unfold writeAccessibleRecPreparePostcondition in *.
  apply Hancesnotaccecc;trivial.
+ (** partition1 is not ancestor of currentPart *)
  (* check if partition1 is the current part or not *)  
  assert(Hor : currentPart = partition1 \/ currentPart <> partition1) by apply pageDecOrNot. 
  destruct Hor as [Hor | Hor].
  - (** partition1 is the currentPart *)
    subst partition1.
    apply notInGetAccessibleMappedPage with  ptMMUvaNextInd currentPD vaNextInd;trivial.
    intros;subst;split;trivial.
  - (** partition1 is not the currentPart, is not an ancestor **)
    (** partition1 could be a descendent *)
    assert(Hin : In partition1 (getPartitionAux currentPart s (nbPage+1)) \/ 
            ~ In partition1 (getPartitionAux currentPart s (nbPage+1))).
    { apply InDecOrNot.
      apply pageDecOrNot. }
    destruct Hin as [Hin | Hin].
    * (** partition1 is a descendent *)
       destruct nbPage. simpl in *.
        revert Hin Hor. clear.
        intros.
        intuition. contradict H.
        induction (getChildren currentPart s);simpl; intuition.
        simpl in *.
        destruct Hin as [Hin | Hin]. intuition.
        rewrite in_flat_map in Hin.
        destruct Hin as (x & Hx1 & Hx2).
        assert (Hincl : incl (getAccessibleMappedPages partition1 s) 
        (getMappedPages partition1 s)) by apply accessibleMappedPagesInMappedPages.
        unfold incl in *.
        assert(Hderivlist : ~ isDerived currentPart vaNextInd s ).
        { unfold not;intros Hgoal.
          intuition. subst.
          contradict Hgoal.
          eapply vaNotDerived with ptSh1VaNextInd ;trivial.
          intros;split;subst;trivial. }
        assert(Hlist : forall child, In child (getChildren currentPart s) ->
             ~ In nextIndirection (getMappedPages child s)).
        { intros.
          unfold not;intros Hgoal.
          intuition. subst. 
          contradict Hgoal.
          apply phyNotDerived  with currentPart currentPD vaNextInd ptMMUvaNextInd ; trivial.
          intros;split;subst;trivial.  }
        unfold incl in *.
        unfold not;intros Hpg.
        apply Hincl in Hpg;clear Hincl.
        simpl .
        assert(Horx : x=partition1 \/ x<> partition1) by apply pageDecOrNot.
        destruct Horx as [Horx | Horx].
        ++ subst.
           apply Hlist in Hx1.
           now contradict Hx1.
        ++ unfold consistency in *.
           unfold noDupPartitionTree in *.
           assert( Hincl2 : incl (getMappedPages partition1 s) (getMappedPages x s)).
           apply verticalSharingRec with n;intuition.
           apply childrenPartitionInPartitionList with currentPart;trivial.
           unfold incl in Hincl2.
           apply Hincl2 in Hpg.
           apply Hlist in Hx1.
           now contradict Hx1.
      * (** partition1 is not a descendent, not the currentPart and not an ancestor *)
          (** continuer sur le fichier UpdatePDFlagTrue : ligne 5030 *) 
        (* clear.
        Lemma pageNotAccessibleInCousins s (currentPart : page):
        forall nextIndirection partition1,
        ~ In partition1 (getPartitionAux multiplexer s (nbPage + 1)) ->
        consistency s ->
        In currentPart (getPartitions multiplexer s) ->
        ~ In nextIndirection (getAccessibleMappedPages partition1 s).
        Proof. 
        intros * Hin.
        intros.   *)      
        assert (Hok:  forall partition, parentInPartitionList s ->  partitionDescriptorEntry s ->  isParent s ->  In partition (getPartitions pageRootPartition s)
         -> In partition (getPartitions pageRootPartition s) -> 
              partition <> pageRootPartition -> 
              In pageRootPartition (getAncestors partition s)).  
        apply multiplexerIsAncestor;trivial.
        unfold consistency in *. intuition.
        assert(Hnotanc : partition1 <> pageRootPartition). 
        { assert(In pageRootPartition (getAncestors currentPart s)) . 
          { unfold consistency in *; intuition.  
            apply Hok;trivial.
            unfold not;intros Hfalse;subst.
            contradict Hin. unfold getPartitions in *;trivial.  }
            unfold not;intros Hfalse;subst.
           now contradict Hances.  }
        assert(Hmulteq :currentPart = pageRootPartition \/ currentPart <> pageRootPartition ) by apply pageDecOrNot.
        destruct Hmulteq as [Hmulteq | Hmulteq].
        ++ subst currentPart.           
           unfold getPartitions in Hpart.
           now contradict Hin.     
        ++ move Hcurpart at bottom.
         unfold consistency in *.
           assert(Hisparent : isParent s) by intuition. 
           assert(Hmultnone : multiplexerWithoutParent s) by intuition.
           assert(Hnoduptree : noDupPartitionTree s) by intuition.   
         assert( match  closestAncestor currentPart partition1 s with 
                  | Some closestAnc =>  True
                  | None => False
         end
         ).
         { case_eq (closestAncestor currentPart partition1 s ); [intros  closestAnc Hclose| 
           intros Hclose];trivial.       
           revert Hmultnone Hnoduptree Hcurpart Hclose Hisparent  .           
           clear.
           { unfold closestAncestor, getPartitions.
             intro. intro.
             revert currentPart partition1.
             assert(Hmult : StateLib.getParent pageRootPartition (memory s) = None) .
             intuition.
             induction nbPage.
             simpl.
            intros.            
            destruct Hcurpart.
            subst. 
            rewrite Hmult in *.
            now contradict Hclose.
            contradict H. clear.
            induction (getChildren pageRootPartition s); simpl; intuition.
            simpl .
            intros. 
            destruct Hcurpart.
            subst.
            rewrite Hmult in *.
            now contradict Hclose.
            case_eq(StateLib.getParent currentPart (memory s) ); [intros parent Hparent | intros Hparent];
            rewrite Hparent in *; try now contradict Hclose.
            case_eq ( in_dec pageDec partition1 (getPartitionAux parent s (nbPage + 1))); 
            intros i Hi; rewrite Hi in *.
            now contradict Hclose.
            apply IHn with parent partition1;trivial.
            assert (In currentPart (getPartitionAux pageRootPartition s (n + 2))).
            replace (n + 2) with (S n +1) by lia.
            simpl;right;trivial.
            apply getPartitionAuxMinus1 with currentPart;trivial.
            unfold getPartitions. destruct nbPage;simpl;left;trivial.
          } }
         case_eq(closestAncestor currentPart partition1 s); [intros  closestAnc Hclose| 
          intros Hclose];
          rewrite Hclose in *; try now contradict H. 
         assert(Hcloseintree : In closestAnc (getPartitions pageRootPartition s)). 
          { revert Hclose Hcurpart.
            unfold consistency in *. 
            assert(Hchild : isChild s) by intuition.
            assert(Hparent: isParent s) by intuition.
             assert(Hparenintreet: parentInPartitionList s) by intuition.
            revert Hchild Hparent Hparenintreet.
           clear. intro . intros Hisparent Hparentintree.
           revert currentPart partition1 closestAnc.
           unfold closestAncestor.
           induction (nbPage+1);simpl;intros. now contradict Hclose.
           case_eq( StateLib.getParent currentPart (memory s));[intros parent Hparent | intros Hparent];
           rewrite Hparent in *.
           - case_eq(in_dec pageDec partition1 (getPartitionAux parent s (nbPage + 1)));
           intros i Hi; rewrite Hi in *.
           * inversion Hclose;subst.
             unfold parentInPartitionList in *.
             apply Hparentintree with currentPart;trivial.
             apply nextEntryIsPPgetParent;trivial.
          * apply IHn with parent partition1;trivial. 
           unfold parentInPartitionList in *.
           apply Hparentintree with currentPart;trivial.
           apply nextEntryIsPPgetParent;trivial.
        - inversion Hclose; subst. unfold getPartitions.
          destruct nbPage;simpl;left;trivial.
          }
         assert (Hinsubtree1 : In currentPart  (getPartitionAux closestAnc s (nbPage +1))).
          { assert (Hcurpart1 :In currentPart (getPartitions pageRootPartition s)) by trivial.   
          revert Hnoduptree Hmultnone Hclose Hcurpart Hcurpart1.
          
            unfold consistency in *. 
            assert(Hchild : isChild s) by intuition.
            assert(Hparent: isParent s) by intuition.
             assert(Hparenintreet: parentInPartitionList s) by intuition.
            revert Hchild Hparent Hparenintreet. 
           clear. intro . intros Hisparent Hparentintree Hnoduptree.
           intro.
           revert currentPart partition1 closestAnc.
           unfold closestAncestor.
           unfold getPartitions  at 1.
           induction (nbPage+1);simpl;intros.
           trivial.
           assert(Hor : closestAnc = currentPart \/ closestAnc <> currentPart) by apply pageDecOrNot.
           destruct Hor as [Hor | Hor].
           left;trivial.
           destruct Hcurpart as [Hcurpart | Hcurpart].
           + subst. assert (Hmult :  StateLib.getParent pageRootPartition (memory s) = None) by intuition.
           rewrite Hmult in *.
           inversion Hclose. intuition.
           +
           right.
           case_eq( StateLib.getParent currentPart (memory s));[intros parent Hparent | intros Hparent];
           rewrite Hparent in *.
           - case_eq(in_dec pageDec partition1 (getPartitionAux parent s (nbPage + 1)));
           intros i Hi; rewrite Hi in *.
           * inversion Hclose;subst.
           rewrite in_flat_map.
           exists currentPart;split;trivial.
           unfold isChild in *.
           apply Hchild;trivial. destruct n;simpl in *.
           contradict Hcurpart.
           clear. induction   (getChildren pageRootPartition s) ;simpl;intuition.
           left;trivial.
           * assert(In parent  (getPartitionAux closestAnc s n)).
           apply IHn with partition1;trivial.
           apply getPartitionAuxMinus1 with currentPart;trivial.
           unfold getPartitions. destruct nbPage;simpl;left;trivial. 
           unfold parentInPartitionList in *.
           apply Hparentintree with currentPart;trivial.
           apply nextEntryIsPPgetParent;trivial.
             apply getPartitionAuxSn with parent;trivial.
           - inversion Hclose; subst. trivial. }
                   assert (Hinsubtree2 : In partition1  (getPartitionAux closestAnc s (nbPage +1))).
         { assert (Hcurpart1 :In partition1 (getPartitions pageRootPartition s)) by trivial.   
          revert Hclose Hcurpart Hcurpart1.
            unfold consistency in *. 
            assert(Hchild : isChild s) by intuition.
            assert(Hparent: isParent s) by intuition.
             assert(Hparenintreet: parentInPartitionList s) by intuition.
            revert Hchild Hparent Hparenintreet.
           clear. intro . intros Hisparent Hparentintree.
           revert currentPart partition1 closestAnc.
           unfold closestAncestor.
(*            unfold getPartitions  at 1. *)
          assert(Hnbpage : nbPage <= nbPage) by lia.
          revert Hnbpage.
          generalize nbPage at 1 3.
           induction n;simpl;intros.
           trivial.  
           + case_eq(StateLib.getParent currentPart (memory s));[intros parent Hparent | intros Hparent];
              rewrite Hparent in *.
              - case_eq(in_dec pageDec partition1 (getPartitionAux parent s (nbPage + 1)));
                intros i Hi; rewrite Hi in *.
               * inversion Hclose;subst. trivial.
               *  now contradict Hclose.
              -  inversion Hclose. subst. unfold getPartitions in *;trivial.
         + case_eq( StateLib.getParent currentPart (memory s));[intros parent Hparent | intros Hparent];
            rewrite Hparent in *.
            - case_eq(in_dec pageDec partition1 (getPartitionAux parent s (nbPage + 1)));
              intros i Hi; rewrite Hi in *.
              * inversion Hclose;subst. trivial.
              * apply IHn with parent;trivial. lia.           
                unfold parentInPartitionList in *.
                apply Hparentintree with currentPart;trivial.
                apply nextEntryIsPPgetParent;trivial.
          - inversion Hclose; subst. trivial.  }  
        assert(Heqclose : partition1 = closestAnc \/ partition1 <> closestAnc) by apply pageDecOrNot.
         destruct Heqclose as [Heqclose | Heqclose].
         **  subst closestAnc.
          assert( partitionDescriptorEntry s /\ parentInPartitionList s) as (Hpde & Hparent).
          { unfold consistency in *. intuition. } 
           assert(Hfalse : In partition1 (getAncestors currentPart s)).
           { revert Hclose Hcurpart Hpde Hparent. clear .
           unfold  closestAncestor.
           unfold  getAncestors.
           revert currentPart partition1.
           induction (nbPage + 1).
           simpl in *. intros.
           now contradict Hclose.
           simpl.
           intros.    
           case_eq(StateLib.getParent currentPart (memory s) );intros.
           rewrite H in *.
           case_eq ( in_dec pageDec partition1 (getPartitionAux p s (nbPage + 1)));intros;
           rewrite H0 in *.
           inversion Hclose.
           simpl;left;trivial.
           simpl.
           right.
           apply IHn;trivial.
           unfold parentInPartitionList in *.
           apply Hparent with currentPart;trivial.
           apply nextEntryIsPPgetParent;trivial.
            unfold partitionDescriptorEntry in *.
           assert((exists entry : page,
          nextEntryIsPP currentPart idxParentDesc entry s /\ entry <> pageDefault)).
          apply Hpde;trivial.
          do 4 right;left;trivial.
          destruct H0 as (entry & H1 & _).
          rewrite nextEntryIsPPgetParent in *.
          rewrite H1 in H. now contradict H1. }
        now contradict Hfalse.
        ** assert(Hsub1 : In currentPart
          (flat_map (fun p : page => getPartitionAux p s nbPage) (getChildren closestAnc s))).
         {  replace (nbPage +1) with (1 + nbPage) in * by lia.
             simpl in *.
             apply Classical_Prop.not_or_and in Hin as (_ & Hin).  
               destruct  Hinsubtree1 as [Hsub1 | Hsub1]; subst.
      destruct  Hinsubtree2 as [Hsub2 | Hsub2]; subst.
             now contradict Heqclose.  now contradict Hsub2.
         destruct  Hinsubtree2 as [Hsub2 | Hsub2]; subst.
             now contradict Heqclose. trivial. }
      assert(Hsub2 : In partition1
          (flat_map (fun p : page => getPartitionAux p s nbPage) (getChildren closestAnc s))).
          {  replace (nbPage +1) with (1 + nbPage) in * by lia.
            simpl in *.
            apply Classical_Prop.not_or_and in Hin as (_ & Hin).  
            destruct  Hinsubtree2 as [Hsub2 | Hsub2]; subst.
            destruct  Hinsubtree1 as [Hsub11 | Hsub11]; subst.
            now contradict Heqclose.  now contradict Heqclose.
            destruct  Hinsubtree1 as [Hsub11 | Hsub11]; subst.
            now contradict Heqclose. trivial. }               

             rewrite in_flat_map in Hsub1 , Hsub2.
             destruct Hsub1 as (child1 & Hchild1 &  Hchild11).
             destruct Hsub2 as (child2 & Hchild2 &  Hchild22).
         assert(Horcurpart : child1 = currentPart \/ child1 <> currentPart ) by apply pageDecOrNot.
         destruct Horcurpart as [Horcurpart | Horcurpart].
          --- subst. 
          assert (Htrue : currentPart <> child2 ). 
          { unfold not;intros Hfasle;subst child2.
            contradict Hin. 
            apply getPartitionAuxSbound;trivial. 
            }
          assert(Hdisjoint : disjoint (getUsedPages currentPart s) (getUsedPages child2 s)).
          { unfold partitionsIsolation in *. 
            apply Hiso with closestAnc;trivial. }
         assert (Hor1 : partition1 = child2 \/ partition1 <> child2) by apply pageDecOrNot.
         destruct Hor1 as [Hor1 |Hor1].
        {  subst child2.
        unfold not;intros Hfalse. 
         assert(Hx : In nextIndirection (getMappedPages partition1 s)).
         apply accessibleMappedPagesInMappedPages; trivial. simpl. 
        assert(Hincurpart: In nextIndirection (getMappedPages currentPart s)). 
        { apply inGetMappedPagesGetTableRoot with vaNextInd ptMMUvaNextInd currentPD;
          trivial. intros ;split;subst;trivial. }
       unfold disjoint in Hdisjoint.
       contradict Hx.
       assert(Hgen : ~ In nextIndirection (getUsedPages partition1 s)).
        
       apply Hdisjoint. unfold getUsedPages. apply in_app_iff.
       right;trivial.
       contradict Hgen.
       unfold getUsedPages.
       apply in_app_iff.
       right;trivial. }
      { assert(Hincl2:  incl (getMappedPages partition1 s) (getMappedPages child2 s)).
        apply verticalSharingRec with (nbPage-1);trivial.
        unfold consistency in *.
        intuition.
        apply childrenPartitionInPartitionList with closestAnc; trivial.
        intuition.
        destruct nbPage.
        simpl in *. intuition.
        simpl.
        replace    (n - 0 + 1) with (S n) by lia.
        trivial.
        destruct nbPage.
        simpl in *. intuition.
        simpl.
        replace    (n - 0 + 1) with (S n) by lia.
        trivial.
        unfold disjoint in *.
       intros.
       unfold not;intros Hfalse.
       assert(Hx : In nextIndirection (getMappedPages partition1 s)).
       apply accessibleMappedPagesInMappedPages; trivial. simpl.
       unfold incl in *.
       apply Hincl2 in Hx.
       assert(Hincurpart: In nextIndirection (getMappedPages currentPart s)). 
        { apply inGetMappedPagesGetTableRoot with vaNextInd ptMMUvaNextInd currentPD;
          trivial. intros ;split;subst;trivial. }
          assert(Hgen : ~ In nextIndirection (getUsedPages child2 s)).
        apply Hdisjoint. unfold getUsedPages. apply in_app_iff.
       right;trivial.
       contradict Hgen.
       unfold getUsedPages.
       apply in_app_iff.
       right;trivial. } 
      --- assert(Horpart1 : child2 = partition1 \/ child2 <> partition1 ) by apply pageDecOrNot.
            destruct Horpart1 as [Horpart1 | Horpart1].
            +++ subst. 
              assert (Htrue : partition1 <> child1 ). 
               { unfold not;intros Hfasle;subst child1.
                contradict Hances.
                revert Hchild11 Horcurpart  Hpart Hcurpart .

                 assert( partitionDescriptorEntry s /\ parentInPartitionList s) as (Hpde & Hparentintree).
          { unfold consistency in *. intuition. } 
                revert Hnoduptree Hisparent Hparentintree Hpde. 
                clear.
                revert currentPart partition1.
                unfold getAncestors.
                induction nbPage;simpl. intuition.
                intros.               
                destruct Hchild11. intuition.
              case_eq(StateLib.getParent currentPart (memory s) ); [intros parent Hparent | intros Hparent].
              simpl.
              assert(Hor : parent = partition1 \/ parent <> partition1) by apply pageDecOrNot.
              destruct Hor as [Hor | or].
              left;trivial.
              right.
              apply IHn;trivial.
              apply getPartitionAuxMinus1 with currentPart;trivial.
              intuition.
              unfold parentInPartitionList in *.
              apply Hparentintree with currentPart;trivial.
              apply nextEntryIsPPgetParent;trivial.
                 unfold partitionDescriptorEntry in *.
           assert((exists entry : page,
          nextEntryIsPP currentPart idxParentDesc entry s /\ entry <> pageDefault)).
          apply Hpde;trivial.
          do 4 right;left;trivial.
          destruct H0 as (entry & H1 & _).
          rewrite nextEntryIsPPgetParent in *.
          rewrite H1 in Hparent. now contradict H1. }
       assert(Hdisjoint : disjoint (getUsedPages partition1 s) (getUsedPages child1 s)).
          { unfold partitionsIsolation in *. 
            apply Hiso with closestAnc;trivial. }
        { assert(Hincl2:  incl (getMappedPages currentPart s) (getMappedPages child1 s)).
           apply verticalSharingRec with (nbPage-1);trivial.
           unfold consistency in *.
           intuition.
           apply childrenPartitionInPartitionList with closestAnc; trivial.
           
           intuition.
           destruct nbPage.
           simpl in *. intuition.
           simpl.
           replace    (n - 0 + 1) with (S n) by lia.
           trivial.
           destruct nbPage.
           simpl in *. intuition.
           simpl.
           replace    (n - 0 + 1) with (S n) by lia.
           trivial.
          unfold disjoint in *.
         intros.
         unfold not;intros Hfalse.
         assert(Hx : In nextIndirection (getMappedPages partition1 s)).
         apply accessibleMappedPagesInMappedPages; trivial.
         
         assert(Hgen : ~ In nextIndirection (getUsedPages child1 s)).
        apply Hdisjoint. unfold getUsedPages. apply in_app_iff.
       right;trivial.
        assert(Hincurpart: In nextIndirection (getMappedPages currentPart s)). 
        { apply inGetMappedPagesGetTableRoot with vaNextInd ptMMUvaNextInd currentPD;
          trivial. intros ;split;subst;trivial. }
        unfold incl in *.
        apply Hincl2 in Hincurpart.
      contradict Hgen.
       unfold getUsedPages.
       apply in_app_iff.
       right;trivial. }
       +++ 
          
            assert(Horc : child1 = child2 \/ child1 <> child2) by apply pageDecOrNot.
           destruct Horc as [Horc | Horc]. 
            subst. 
          { contradict Hclose.
          assert( partitionDescriptorEntry s /\ parentInPartitionList s) as (Hpde & Hparentintree).
          { unfold consistency in *. intuition. } 
           clear Hinsubtree1 Hinsubtree2 .
           assert(Hnocycle : noCycleInPartitionTree s).
            { unfold consistency in *. intuition. }
           assert(Hchild2intree : In child2 (getPartitions pageRootPartition s)).
           { apply childrenPartitionInPartitionList with closestAnc;trivial. } 
           revert dependent child2. 
(*            revert dependent child1.  *)
           revert dependent partition1.
           assert( partitionsIsolation s /\ isChild s /\ verticalSharing s) as (His & Hischild ).
           { unfold consistency in *. intuition. }
           intros partition1 Htmp Htmp1. 
           revert Hparentintree Hischild Hmultnone Hnoduptree Hisparent Hcurpart (* Hmulteq *).
           revert dependent closestAnc.
           revert Hpde  Hnocycle His  Hvs Htmp1.
           clear .
           revert currentPart  partition1.
           unfold closestAncestor.
           unfold getAncestors.
           assert(Hnbpage : nbPage <= nbPage) by lia.
           revert Hnbpage.
           generalize nbPage at 1 (* 3 4 5 *) 5    7. 
           induction n.
           intros. simpl in *.
           intuition.
           simpl.
           intros.
           case_eq (StateLib.getParent currentPart (memory s));[intros parent Hparent| intros Hparent]. 
           +  destruct Hchild11 as [Hchild11 | Hchild11];subst.
             now contradict Horcurpart.
           (*  destruct Hchild22 as [Hchild22 | Hchild22];subst.
             now contradict Horpart1.  
             apply Classical_Prop.not_or_and in Hin as (_ & Hin). *)
            case_eq (in_dec pageDec partition1 
                  (getPartitionAux parent s (nbPage + 1)));intros i Hi.
            unfold not; intros; subst.
            inversion H.
            subst.         
           - revert  Hparentintree Hischild Hmultnone Hnoduptree Hparent Hchild11 Hchild1 Horcurpart  His Hischild Hvs Hcurpart Hnocycle Hisparent Hcloseintree. 
            clear .
            intros.
           assert(Hchild : In currentPart (getChildren closestAnc s) ).
           unfold isChild in *.
           intuition.  (* isChild *)
           clear Hparent.
         assert(Hii :  incl (getUsedPages currentPart s) (getMappedPages child2 s)). 
          apply verticalSharingRec2 with n; trivial.
          apply childrenPartitionInPartitionList with closestAnc;trivial.
          replace (n+1) with (1+n) by lia.
          simpl.
          right;trivial.
           assert(Hmap : In currentPart (getMappedPages child2 s)).
           unfold getUsedPages in *.
           unfold getConfigPages in *.
           intuition.   
           assert( disjoint (getUsedPages currentPart s) (getUsedPages child2 s)).
           unfold partitionsIsolation in *.
           apply His with closestAnc;trivial.
           unfold not;intros; subst.
           rewrite in_flat_map in Hchild11.
           destruct Hchild11 as (x & Hx1 & Hx11).
           contradict Hx11.
              
           apply noCycleInPartitionTree2;trivial.
           intuition.
            unfold disjoint in *.
            unfold getUsedPages in *.
            
            assert( ~ In currentPart (getConfigPages child2 s ++ getMappedPages child2 s) ).
            apply H.  
           unfold getConfigPages.
           simpl;left;trivial.
           rewrite in_app_iff in H0.
           intuition.
           (** contradict Hparent, Hchild11 and Hchild1*)      
           - apply IHn with  child2; trivial.
(*            * lia. *)
           * lia. 
 
          * revert  Htmp1 Hparent Hpde Hisparent Hcurpart Hparentintree Hnoduptree Hmultnone.
             clear.
            revert currentPart partition1 parent.
            intros.
            contradict Htmp1.
            assert(Hmult : In pageRootPartition (getAncestors currentPart s)).
            { apply multiplexerIsAncestor;trivial. 
              unfold not;intros; subst.
               assert(Hmult :   StateLib.getParent pageRootPartition (memory s) = None) by intuition.
              rewrite Hmult in *. now contradict Hparent. }  
            unfold getAncestors in *.
            revert dependent currentPart.
            revert dependent partition1.
            revert parent.
            induction (nbPage+1); simpl. intuition.
            intros parent partition1 Hances.
            intros.
            rewrite Hparent in *. 
            case_eq(StateLib.getParent parent (memory s) );[intros ances Hances1 | intros Hances1];
            rewrite Hances1 in *; try now contradict Hances.
            simpl in *.
            destruct Hmult as [Hmult | Hmult ].
            subst.
            assert(Hmultnoparent : StateLib.getParent pageRootPartition (memory s) = None) by intuition.
            rewrite Hances1 in *. 
            now contradict Hmultnoparent.
            destruct Hances as [Hances | Hances].
            subst.
            right.
            destruct n;simpl in *; trivial.
            rewrite Hances1 in *.
            simpl;left;trivial.
            right.
            apply IHn with ances;trivial.
            unfold parentInPartitionList in *.
            apply Hparentintree with currentPart;trivial.
            apply nextEntryIsPPgetParent;trivial. 
                       * unfold parentInPartitionList in *. 
             apply Hparentintree with currentPart;trivial.
             apply nextEntryIsPPgetParent;trivial.  
          * unfold not;intros.
            subst. clear Hi. contradict i.
            destruct nbPage;simpl;left;trivial.
            * revert Hchild11.
              
              revert Hparent Horcurpart Hisparent Hchild2intree Hcurpart 
              Hnocycle Hnoduptree Hmultnone Hischild Hparentintree.
              clear.
              intros.
              destruct Hischild as (Hischild & Hvs).
              assert(In currentPart (getPartitionAux child2 s (1+n))).
              simpl.
              right;trivial.
              clear Hchild11.
              revert dependent currentPart.
              revert dependent child2.
              revert parent.
              induction n;
              simpl in * ;intros.
              intuition.
              contradict H0.
              clear.
              induction (getChildren child2 s);simpl in *;intuition.
              assert(child2 = parent \/ child2 <> parent) by apply pageDecOrNot.
              destruct H0.
              left;trivial.
              destruct H.
              intuition.
              right.
              rewrite in_flat_map in H.
              destruct H as (x & Hx & Hxx).
              simpl in *.
              destruct Hxx.
              subst.
              assert(StateLib.getParent currentPart (memory s) = Some child2).
              unfold isParent in Hisparent.
              apply Hisparent;trivial.
              rewrite H in Hparent.
              inversion Hparent. subst. now contradict H0.
              rewrite in_flat_map.
              exists x;split;trivial.
              apply IHn with currentPart;trivial.
              apply childrenPartitionInPartitionList with child2;trivial.
              unfold not;intros;subst.
              rewrite in_flat_map in H.
              destruct H as (x2 & Hx2 & Hx22).
              contradict Hx22.
              apply noCycleInPartitionTree2;trivial.
              right;trivial.
           * unfold not;intros. subst.    
            contradict Hchild22.
            clear Hi.
            contradict i.
            revert i.
            clear.
            revert parent partition1.
            induction nbPage.
            simpl;intuition.
            simpl.
            intros.
            intuition.
            right.
            rewrite in_flat_map in *.
            destruct H as (x2 & Hx2 & Hx22).
            exists x2;split;trivial.
            apply IHn;trivial.
           +        unfold partitionDescriptorEntry in *.
           assert((exists entry : page,
          nextEntryIsPP currentPart idxParentDesc entry s /\ entry <> pageDefault)).
          apply Hpde;trivial.
          do 4 right;left;trivial.
          destruct H as (entry & H1 & _).
          rewrite nextEntryIsPPgetParent in *.
          rewrite H1 in Hparent. now contradict H1.  }
         assert(Hintree : In  closestAnc (getPartitions pageRootPartition s)) by trivial.
         assert(Horc1 : partition1 = child2 \/ partition1 <> child2) by apply pageDecOrNot.
         { destruct Horc1 as [Horc1 | Horc1].
           subst child2.  
           **
           assert(Horc1 : currentPart = child1 \/ currentPart <> child1) by apply pageDecOrNot.
           destruct Horc1 as [Horc1 | Horc1].
           --- subst child1. now contradict Horpart1.
           --- now contradict Horpart1.
           
            ** assert(Horc2 : currentPart = child1 \/ currentPart <> child1) by apply pageDecOrNot.
           destruct Horc2 as [Horc2 | Horc2].
           --- subst child1. now contradict Horcurpart.
           ---   assert(Hincl1 :  incl (getMappedPages currentPart s) (getMappedPages child1 s)).
           apply verticalSharingRec with (nbPage-1);trivial.
           unfold consistency in *.
           intuition.
           apply childrenPartitionInPartitionList with closestAnc; trivial.
           intuition.
           destruct nbPage.
           simpl in *. intuition.
           simpl.
           replace    (n - 0 + 1) with (S n) by lia.
           trivial.
            assert(Hincl2:  incl (getMappedPages partition1 s) (getMappedPages child2 s)).
           apply verticalSharingRec with (nbPage-1);trivial.
           unfold consistency in *.
           intuition.
           apply childrenPartitionInPartitionList with closestAnc; trivial.
           intuition.
           destruct nbPage.
           simpl in *. intuition.
           simpl.
           replace    (n - 0 + 1) with (S n) by lia.
           trivial.
           destruct nbPage.
           simpl in *. intuition.
           simpl.
           replace    (n - 0 + 1) with (S n) by lia.
           trivial.
            assert(Hincurpart: In nextIndirection (getMappedPages currentPart s)). 
        { apply inGetMappedPagesGetTableRoot with vaNextInd ptMMUvaNextInd currentPD;
          trivial. intros ;split;subst;trivial. }
           assert(Hdisjoint : disjoint (getUsedPages child1 s) (getUsedPages child2 s)).
           unfold partitionsIsolation in *.
           apply Hiso with closestAnc; trivial.
           unfold disjoint in *.
           intros.
           unfold not;intros Hx.
           assert(mapped1 : In nextIndirection (getMappedPages partition1 s)).
           apply accessibleMappedPagesInMappedPages; trivial.
           unfold incl in *.
           apply Hincl2 in mapped1.
           simpl. 
           assert(Hmap: In nextIndirection (getUsedPages child1 s)).
           unfold getUsedPages.
           apply in_app_iff.
           right.
           apply Hincl1; trivial.
           apply Hdisjoint in Hmap.
           contradict Hmap.
           
           
           unfold getUsedPages.
           
           apply in_app_iff.
           right. trivial. }
Qed.           
 
