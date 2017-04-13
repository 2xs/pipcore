(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2016)                 *)
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
 DependentTypeLemmas Model.Lib Invariants Lib.
Require Import Coq.Logic.ProofIrrelevance Omega.

(* Require Import Model.ADT Model.Hardware Core.Services Isolation
Consistency Invariants WeakestPreconditions Model.Lib StateLib
Model.MAL UpdateShadow1Structure InternalLemmas DependentTypeLemmas Lib
WriteAccessible *)

Lemma getIndirectionStop1 s indirection x idxind va l: 
StateLib.Level.eqb l fstLevel = false ->  indirection <> defaultPage ->
lookup indirection idxind (memory s) beqPage beqIndex = Some (PE x) -> 
StateLib.getIndexOfAddr va l  =  idxind -> 
StateLib.getIndirection indirection va l 1 s = Some (pa x).
Proof.
intros Hlnotzero Hindnotnull Hlookup Hidx . 
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
   * unfold run in Hidx.
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

Lemma getIndirectionStopS :
forall  stop (s : state) (nbL : level)  nextind pd va indirection, 
stop + 1 <= nbL -> indirection <> defaultPage ->
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

Lemma getIndirectionProp :
forall stop s nextind idxind indirection pd va (nbL : level),
stop +1 <= nbL -> indirection <> defaultPage ->
StateLib.Level.eqb (CLevel (nbL - stop)) fstLevel = false -> 
StateLib.getIndexOfAddr va (CLevel (nbL - stop)) = idxind ->
lookup indirection idxind (memory s) beqPage beqIndex = Some (PE nextind)-> 
StateLib.getIndirection pd va nbL stop s = Some indirection ->
StateLib.getIndirection pd va nbL (stop + 1) s = Some (pa nextind). 
Proof.
intros.
apply getIndirectionStopS with indirection;trivial.
apply getIndirectionStop1  with idxind;trivial.
Qed.

Lemma fstIndirectionContainsValue_nbLevel_1  indirection idxroot s idx va l currentPart : 
(idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx) ->
dataStructurePdSh1Sh2asRoot idxroot s -> In currentPart (getPartitions multiplexer s) -> 
StateLib.Level.eqb l fstLevel = true ->
nextEntryIsPP currentPart idxroot indirection s ->
StateLib.getIndexOfAddr va fstLevel = idx -> indirection <> defaultPage -> 
Some l = StateLib.getNbLevel ->  
isVE indirection idx s /\ idxroot = sh1idx \/
isVA indirection idx s /\ idxroot = sh2idx \/
isPE indirection idx s /\ idxroot = PDidx.
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
          (nbLevel-1) Hnblevel indirection (StateLib.getIndexOfAddr va fstLevel));clear Hroot.
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
    contradict H. simpl.  omega. } 
  { contradict H. omega. }
 destruct H. assumption.
Qed.

Lemma  lastIndirectionContainsValueRec   idxroot s l rootind indirection va idx currentPart: 
StateLib.Level.eqb l fstLevel = true ->
In currentPart (getPartitions multiplexer s) ->
dataStructurePdSh1Sh2asRoot idxroot s -> 
 (idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx )-> 
 nextEntryIsPP currentPart idxroot rootind s ->
rootind <> defaultPage -> 
(exists (nbL : level) (stop : nat),
                 Some nbL = StateLib.getNbLevel /\ stop <= nbL /\
                 getIndirection rootind va nbL stop s = Some indirection /\
                 indirection <> defaultPage /\ l = CLevel (nbL - stop) ) -> 
StateLib.getIndexOfAddr va fstLevel = idx -> 
isVE indirection idx s /\ idxroot = sh1idx \/
isVA indirection idx s /\ idxroot = sh2idx \/
isPE indirection idx s /\ idxroot = PDidx.
Proof. 
intros Hfstlevel Hcurpart Hroot Hisroot Hcurpd
        Hpdnotnull Hindirection Hidx.
destruct Hindirection. destruct H. destruct H.
unfold dataStructurePdSh1Sh2asRoot in *.
generalize (Hroot currentPart Hcurpart); clear Hroot; intro Hroot.
assert (True) as Hvarefchild;trivial. (** va into the list of all Vaddr **)
subst.
destruct H0. destruct H1.
generalize (Hroot rootind  Hcurpd va Hvarefchild x x0 H indirection (StateLib.getIndexOfAddr va fstLevel) );clear Hroot;
intros Hroot.
destruct Hroot. assumption.
destruct H2. now contradict H2. 
destruct H3.
apply levelEqBEqNatTrue in Hfstlevel.
subst.
destruct H2.
unfold fstLevel in H5.
apply levelEqNat in H5.
+ destruct H3 as [(Hfalse &H3) | H3].
  contradict Hfalse;omega.
  destruct H3. assumption.
+ apply nbLevelNotZero.
+ unfold StateLib.getNbLevel in H.
  assert (nbLevel > 0).
  apply nbLevelNotZero.
  destruct (gt_dec nbLevel 0).
  simpl in *.
  inversion H. 
  subst.
  simpl. omega.
  contradict H5.
  omega.
Qed. 

Lemma fstIndirectionContainsPENbLevelGT1 idxroot s l currentpd va idxind currentPart :
(idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx) -> 
 StateLib.Level.eqb l fstLevel = false -> 
dataStructurePdSh1Sh2asRoot idxroot s -> 
In currentPart (getPartitions multiplexer s) ->
nextEntryIsPP currentPart idxroot currentpd s ->
 currentpd <> defaultPage -> 
 Some l = StateLib.getNbLevel -> 
 StateLib.getIndexOfAddr va l = idxind ->  (* isPE currentpd idxpd s. *)
isPE currentpd idxind s.
Proof.
  
intros Hroot Hnotfstlevel Hisroot Hcprpl  Hcurpd Hpdnotnull Hlevel Hidx .
 unfold  dataStructurePdSh1Sh2asRoot in Hroot.
          assert (True) as Hvarefchild.
          trivial. (** va into the list of all Vaddr **)
          assert (In currentPart ( getPartitions multiplexer s) ) as Hcurpart.
          { unfold currentPartitionInPartitionsList in Hcprpl.
            subst. intuition. }
          subst.
          assert ( StateLib.getIndirection currentpd va l fstLevel s =
          Some currentpd ) as Hnextind.
          { unfold fstLevel.
            unfold CLevel.
            assert (nbLevel > 0).
            apply nbLevelNotZero.
            case_eq (lt_dec 0 nbLevel).
            intros. simpl.
            cbn. reflexivity.
            intros. contradict H. omega. }
(*           destruct Hindirection as (Hcurind & Hlevel).
          subst.   *)
          unfold dataStructurePdSh1Sh2asRoot in Hisroot.
          generalize (Hisroot currentPart Hcurpart currentpd Hcurpd va 
          Hvarefchild  l fstLevel Hlevel currentpd (StateLib.getIndexOfAddr va l) Hnextind);
          clear Hisroot; intro Hisroot.
          destruct Hisroot. subst. contradict Hpdnotnull. reflexivity.
          destruct H as (H & _). 
          subst. 
          apply levelEqBEqNatFalse0 in Hnotfstlevel.
          destruct H as [(Hl & H) | H].
          assumption.
          destruct H. unfold fstLevel in H.
          unfold CLevel in H. destruct (lt_dec 0 nbLevel).
           simpl in *. contradict H. omega. 
           assert (0 < nbLevel).
           apply nbLevelNotZero. now contradict H1. 
Qed. 

Lemma middleIndirectionsContainsPE  idxroot s l rootind indirection va idxind currentPart: 
 (idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx )-> 
StateLib.Level.eqb l fstLevel = false ->
In currentPart (getPartitions multiplexer s) ->
dataStructurePdSh1Sh2asRoot idxroot s -> 

rootind <> defaultPage -> 
(exists (nbL : level) (stop : nat),
                 Some nbL = StateLib.getNbLevel /\ stop <= nbL /\
                 getIndirection rootind va nbL stop s = Some indirection /\
                 indirection <> defaultPage /\ l = CLevel (nbL - stop) ) -> 
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
  simpl in *. contradict Hnotfstlevel. omega. assert (0 < nbLevel).
  apply nbLevelNotZero. omega.
  intuition.
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
assert (  StateLib.Level.eqb level fstLevel = true).
unfold MALInternal.Level.eqb. 
apply NPeano.Nat.eqb_eq. 
rewrite <- H0. unfold fstLevel. unfold CLevel.
assert ( 0 < nbLevel) by apply nbLevelNotZero.
case_eq (lt_dec 0 nbLevel ); intros.
simpl. trivial.
now contradict H2.
rewrite H2. assumption.
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
  apply levelPredMinus1 in H5; trivial. unfold CLevel in H5.  
  case_eq(lt_dec (level - 1) nbLevel ); intros; rewrite H6 in H5. destruct level. simpl in *. subst.
  simpl in *.      
  apply IHl0 with l; trivial. simpl. omega. simpl. omega.
  destruct level. simpl in *. omega. assumption.
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

Lemma getIndirectionRetDefaultLtNbLevel l1 l0 (nbL :level) p va s:
l0 > 0 -> 
l0 < l1 ->
l0 < nbL ->
getIndirection p va nbL l0 s = Some defaultPage -> 
getIndirection p va nbL l1 s = Some defaultPage.
Proof.
revert l0 nbL p va.
induction l1; intros.
+ now contradict H0.
+ simpl in *.
  case_eq (StateLib.Level.eqb nbL fstLevel); intros.
  destruct l0.
  now contradict H.
  simpl in H2. 
  rewrite H3 in H2. assumption.
  case_eq (StateLib.readPhyEntry p (StateLib.getIndexOfAddr va nbL) (memory s)); intros.
  case_eq (defaultPage =? p0); intros; trivial.
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
  omega.
  omega.
  apply levelPredMinus1 with nbL l in H3; trivial.
  destruct nbL.
  simpl in *.
  unfold CLevel in H3.
  case_eq (lt_dec (l2 - 1) nbLevel); intros; rewrite H7 in H3.
  destruct l.
  simpl in *.
  inversion H3.
  subst.
  omega. omega.
  assumption.
  unfold StateLib.Level.pred in H6.
  apply levelEqBEqNatFalse0 in H3.
  case_eq (gt_dec nbL 0); intros; rewrite H7 in *.
  now contradict H6.
  omega. 
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
getIndirection p va nbL l0 s = Some defaultPage -> 
getIndirection p va nbL l1 s = Some defaultPage.
Proof.
revert l0 nbL p va.
induction l1; intros.
+ omega. 
+ simpl in *.
  case_eq (StateLib.Level.eqb nbL fstLevel); intros.
  destruct l0.
  now contradict H.
  simpl in H2.
  rewrite H3 in H2. assumption.
  case_eq (StateLib.readPhyEntry p (StateLib.getIndexOfAddr va nbL) (memory s)); intros.
  case_eq (defaultPage =? p0); intros; trivial.
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
  omega.
  apply levelPredMinus1 with nbL l in H3; trivial.
  destruct nbL.
  simpl in *.
  unfold CLevel in H3.
  case_eq (lt_dec (l2 - 1) nbLevel); intros; rewrite H7 in H3.
  destruct l.
  simpl in *.
  inversion H3.
  subst.
  omega. omega.
  unfold StateLib.Level.pred in H6.
  apply levelEqBEqNatFalse0 in H3.
  case_eq (gt_dec nbL 0); intros; rewrite H7 in *.
  inversion H6.
  destruct l.
  simpl in *.
  inversion H9.
  omega. now contradict H3.
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

omega.
+
intros.
simpl in H.
case_eq(StateLib.Level.eqb nbL fstLevel); intros; rewrite H2 in *.
 - apply levelEqBEqNatTrue in H2.
subst.
assert(predNbL = fstLevel).
clear H IHn.
unfold fstLevel in * .
unfold CLevel in *.
case_eq(lt_dec 0 nbLevel );intros.
rewrite H in *.

destruct predNbL.
simpl in *.
assert(l0 = 0) by omega.
subst.
f_equal;apply proof_irrelevance;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.
subst.
apply beq_nat_true in H.
destruct (StateLib.getIndexOfAddr va1 fstLevel);
destruct (StateLib.getIndexOfAddr va2 fstLevel).
simpl in *.
subst.
f_equal;apply proof_irrelevance;trivial.
- 
case_eq(StateLib.Level.pred nbL); intros; rewrite H3 in *.
 * case_eq(StateLib.getIndexOfAddr va1 nbL =? StateLib.getIndexOfAddr va2 nbL);
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
  omega.
  apply levelEqBEqNatFalse0 in H2.
  rewrite H5 in *.
  destruct nbL.
  simpl in *.
  omega.
 apply levelPredLt in H3;trivial.
 omega.
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


Lemma checkVAddrsEqualityWOOffsetTrue va1 va2 (nbL predNbL : level):
StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 nbL = true -> 
nbL < nbLevel -> 
predNbL <= nbL -> 
StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 predNbL = true.
Proof.
assert (Htrue : nbLevel <= nbLevel) by omega.
revert va1 va2 nbL predNbL Htrue.
generalize nbLevel at 1 3 4 5.
induction n.
simpl in *.
trivial.
intros.
simpl in *.
case_eq  (StateLib.Level.eqb nbL fstLevel); intros;rewrite H2 in *;trivial.
+ case_eq( StateLib.Level.eqb predNbL fstLevel); intros.
  - apply levelEqBEqNatTrue in H2;trivial.
    apply levelEqBEqNatTrue in H3;trivial.
    subst.
    assumption.
  - apply levelEqBEqNatTrue in H2;trivial.
    apply levelEqBEqNatFalse in H3;trivial.
    subst.
    omega.
+ case_eq (StateLib.Level.pred nbL); intros; rewrite H3 in *.
  * case_eq(StateLib.getIndexOfAddr va1 nbL =? StateLib.getIndexOfAddr va2 nbL); intros;
        rewrite H4 in *; try now contradict H.
    case_eq(StateLib.Level.eqb predNbL fstLevel);intros.
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
  omega.
  rewrite H6 in *.
  destruct nbL.
  simpl in *.
  omega. } 
 apply levelPredLt in H3;trivial.
 omega.
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
   case_eq (StateLib.getIndexOfAddr va1 predNbL =? 
            StateLib.getIndexOfAddr va2 predNbL); intros.
  apply IHn with l.
  omega.
  assumption.
  apply levelPredLt in H3;trivial.
  apply levelPredLt in H6;trivial.
  omega.
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
  omega.
  destruct nbL.
  simpl in *.
  omega.
  
  destruct predNbL.
  simpl in *.
  
  
  omega.

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
  omega.
  rewrite H8 in *.
  destruct nbL.
  simpl in *.
  omega. } 
 apply levelPredLt in H3;trivial.
 omega.
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
  omega.
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
case_eq (StateLib.Level.eqb nbL fstLevel).
intros;trivial.
intros.
assert(StateLib.getIndexOfAddr va1 nbL  = StateLib.getIndexOfAddr va2 nbL ).
apply checkVAddrsEqualityWOOffsetTrue' with nbLevel nbL;trivial.
rewrite H0.
case_eq (StateLib.readPhyEntry pd (StateLib.getIndexOfAddr va2 nbL) (memory s) );
intros; trivial.
case_eq(defaultPage =? p);intros;trivial.
case_eq( StateLib.Level.pred nbL); intros;trivial.
apply IHstop.
apply levelPredMinus1 in H3.
subst.
unfold CLevel.
case_eq( lt_dec (nbL - 1) nbLevel); intros.
simpl.
assumption.
apply levelEqBEqNatFalse0 in H;trivial.
omega.
trivial.
apply checkVAddrsEqualityWOOffsetTrue with nbL;trivial.
apply levelPredMinus1 in H3.
subst.
unfold CLevel.
case_eq( lt_dec (nbL - 1) nbLevel); intros.
simpl.
apply levelEqBEqNatFalse0 in H;trivial.
omega.
destruct nbL.
simpl in *.
omega.
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
    induction n as [ | n IH ]; [ intros i j H; contradict H; omega | ].
     intros i j (Hlei & Hltn) Hltsize.
     simpl.
     destruct (lt_dec i tableSize) as [ Hltsize'' | Hgtsize ];
        [ | contradict Hgtsize; now apply Nat.le_lt_trans with j ].
     apply le_lt_or_eq in Hlei; destruct Hlei as [ Hlti | Heqi ].
     - right.
        apply IH; [ | assumption ].
        now omega.
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
  apply Gen; omega.
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

  - destruct (Nat.eq_dec (length v) (nbLevel + 1));
    [ | now contradict Hv ].
    now apply VAddrEqVA.

  - apply Gen.
    rewrite Hv.
    now apply Nat.add_1_r.
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
    induction n as [ | n IH ]; [ intros i j H; contradict H; omega | ].
     intros i j (Hlei & Hltn) Hltsize.
     simpl.
     destruct (lt_dec i tableSize) as [ Hltsize'' | Hgtsize ];
        [ | contradict Hgtsize; now apply Nat.le_lt_trans with j ].
     apply le_lt_or_eq in Hlei; destruct Hlei as [ Hlti | Heqi ].
     - right.
        apply IH; [ | assumption ].
        now omega.
     - left; subst i.
        unfold CIndex.
        destruct (lt_dec j tableSize); [ | now contradict Hltsize ].
        now apply Index_eq_i.
  } 
  
  clear Gen. 
  assert(tableSize <= tableSize) by omega.
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
  omega.
  omega.
  apply IHn. omega. 
  intuition.
   }
  assert( ~ In (CIndex n0) (getAllIndicesAux (S n0) n)).
  apply Gen.
  omega.
  unfold CIndex in H1.
  rewrite H0 in *.
  assumption.
  simpl.
  apply IHn.
   omega.  }
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
  case_eq ( Nat.eq_dec (length x) (nbLevel + 1) ); intros;
  rewrite H1 in *.  
  case_eq(Nat.eq_dec (length a) (nbLevel + 1));intros;
  rewrite H2 in *.
  inversion Hx;trivial.
  clear H2 Hx.
  rewrite  H0 in n.
  omega.
  clear H1 Hx.
  rewrite H in n.
  omega.
  subst. trivial.
  apply IHl.
  intros.
  apply Gen1.
  simpl;right;trivial.
  intuition.    
Qed. (** noDupAllVaddr*)

Lemma filterOptionInIff l elt : 
List.In elt (filterOption l) <-> List.In (Some elt) l.
Proof.
split. 
+ revert l elt.
  induction l.
  simpl; trivial.  
  intros.
  simpl in *.
  case_eq a; intros .
  rewrite H0 in H.
  simpl in H.
  destruct H;
  subst.
  left; trivial.
  right. 
  apply IHl; trivial.
  rewrite H0 in H. 
  right. apply IHl; trivial.
+ revert l elt.
  induction l.
  simpl; trivial.  
  intros.
  simpl in *.
  case_eq a; intros .
  rewrite H0 in H.
  simpl in H.
  destruct H;
  subst.
  left; trivial.
  inversion H; trivial.
  simpl.   
  right. 
  apply IHl; trivial.
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
- case_eq(StateLib.Level.eqb alevel fstLevel); intros; rewrite H2 in *.
  + unfold not; intros.
    subst.
    symmetry in H1.
    apply beq_nat_false in H1.
    apply H1. reflexivity.
  + case_eq (StateLib.Level.pred alevel); intros; rewrite H3 in *; try now contradict H1.
    case_eq (StateLib.getIndexOfAddr va1 alevel =?
    StateLib.getIndexOfAddr va2 alevel); intros; rewrite H4 in *.
    apply IHn with l; trivial.
    apply levelPredMinus1 in H3; trivial.
    apply getNbLevelEq in H.
    assert(0<nbLevel) by apply nbLevelNotZero.
    unfold CLevel in *.
    case_eq(lt_dec (nbLevel - 1) nbLevel); intros; rewrite H6 in *; try omega.
    case_eq(lt_dec (alevel - 1) nbLevel); intros; rewrite H7 in *; simpl in *.
    destruct nbL; simpl in *.
    inversion H.
    subst.
    simpl.
    destruct alevel.
    simpl in *.
    omega.
    destruct alevel.
    simpl in *.
    omega.
    unfold not; intros.
    subst.
    apply beq_nat_false in H4.
    apply H4. reflexivity.
Qed.

Lemma twoMappedPagesAreDifferent phy1 phy2 v1 v2 p s: 
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
rewrite H2 in H4.
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

Lemma eqMappedPagesEqVaddrs phy1 v1 v2 p s: 
getMappedPage p s v1 = Some phy1 ->
 In v1 getAllVAddr ->
 getMappedPage p s v2 = Some phy1-> 
In v2 getAllVAddr ->
NoDup (filterOption (map (getMappedPage p s) getAllVAddr)) -> 
v1 = v2.
Proof.
revert phy1  v1 v2.
induction getAllVAddr.
intuition.
intros.
destruct H0; destruct H2.
+
subst.
assumption.
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
Qed.



Lemma physicalPageIsAccessible (currentPart : page) (ptPDChild : page)
phyPDChild pdChild idxPDChild accessiblePDChild  nbL presentPDChild 
currentPD  s: 
 (defaultPage =? ptPDChild ) = false ->
accessiblePDChild = true -> 
presentPDChild = true -> 
StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild -> 
nextEntryIsPP currentPart PDidx currentPD s -> 
Some nbL = StateLib.getNbLevel ->
(forall idx : index,
        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
        isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) -> 
entryPresentFlag ptPDChild idxPDChild presentPDChild s -> 
entryUserFlag ptPDChild idxPDChild accessiblePDChild s -> 
isEntryPage ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) phyPDChild s -> 
In currentPart (getPartitions multiplexer s) -> 
In phyPDChild (getAccessibleMappedPages currentPart s). 
Proof. 
intros Hnotnull Haccess Hpresentflag Hidx Hroot Hnbl
Histblroot Hpresent Haccessentry Hentry Hcons.
unfold getAccessibleMappedPages .
assert( Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD). 
{ 
unfold nextEntryIsPP in Hroot.
unfold StateLib.getPd. 
destruct (StateLib.Index.succ PDidx); [| now contradict Hroot].
unfold StateLib.readPhysical.
destruct (lookup currentPart i (memory s) beqPage beqIndex) ; [| now contradict Hroot].
destruct v ; [now contradict Hroot |now contradict Hroot |
subst; trivial | now contradict Hroot |now contradict Hroot ]. }
rewrite Hcurpd.
unfold getAccessibleMappedPagesAux.
apply filterOptionInIff.
unfold getAccessibleMappedPagesOption.
apply in_map_iff.
exists pdChild.
split; [| apply AllVAddrAll].
unfold getAccessibleMappedPage.
rewrite <- Hnbl.
assert (Hind : getIndirection currentPD pdChild nbL   (nbLevel - 1) s = Some ptPDChild).
{ simpl. 
  apply getIndirectionStopLevelGT2 with (nbL+1); auto.
  omega.
  unfold StateLib.getNbLevel in Hnbl.
  assert(0<nbLevel) by apply nbLevelNotZero.
  case_eq (gt_dec nbLevel 0); intros.
  rewrite H0 in Hnbl.
  inversion Hnbl.
  simpl. omega.
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
(StateLib.getIndexOfAddr pdChild fstLevel) (memory s) = Some true).
{ subst. unfold StateLib.readPresent.
  unfold  entryPresentFlag in Hpresent.
  destruct (lookup ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) (memory s) beqPage beqIndex )
  ;[ | now contradict Hpresent].
  destruct v; try now contradict Hpresent.
  f_equal. subst.
  symmetry.
  assumption. }
rewrite Hpresflag.
assert(Haccessflag :  StateLib.readAccessible ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) (memory s) = Some true).
{ subst. unfold StateLib.readAccessible.
  unfold  entryUserFlag in Haccessentry.
  destruct (lookup ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) (memory s) beqPage beqIndex )
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
destruct(lookup ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) (memory s) beqPage beqIndex);
[| now contradict Hentry].
destruct v; try now contradict Hentry.
rewrite Hnotnull.
f_equal. assumption.
Qed.

Lemma getIndirectionFstStep s root va (level1 : level) stop table : 
level1 > 0 -> stop > 0 -> root <> defaultPage ->  table <> defaultPage -> 
getIndirection root va level1 stop s = Some table -> 
exists pred page1,page1 <> defaultPage /\ Some pred = StateLib.Level.pred level1 /\ 
  StateLib.readPhyEntry root (StateLib.getIndexOfAddr va level1) (memory s) = Some page1 /\ 
 getIndirection page1 va pred (stop -1) s = Some table.
Proof.
intros Hl Hstop Hroot Hnull Hind .
destruct stop.
now contradict Hstop.
simpl in *.    
case_eq (StateLib.Level.eqb level1 fstLevel).
intros Hfst.
rewrite Hfst in Hind.
apply beq_nat_true in Hfst. unfold fstLevel in Hfst.
unfold CLevel in Hfst.
case_eq (lt_dec 0 nbLevel).
intros. rewrite H in Hfst.
simpl in Hfst.
omega.
intros.
assert (0 < nbLevel) by apply nbLevelNotZero.
now contradict H0.
intros Hfst.
rewrite Hfst in Hind.
case_eq(StateLib.readPhyEntry root (StateLib.getIndexOfAddr va level1) (memory s)).
intros p Hread.
rewrite Hread in Hind.
case_eq( defaultPage =? p);intros Hnullp; 
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
page1 <> defaultPage ->
StateLib.readPhyEntry root (CIndex idx) (memory s) = Some page1 ->
In page1 (getTablePages root n s).
Proof.
unfold StateLib.readPhyEntry in *. intros.
case_eq (lookup root (CIndex idx) (memory s) beqPage beqIndex); 
[ intros v Hv| intros Hv] ; rewrite Hv in  H2; [ | now contradict H2 ].
destruct v; inversion H2.
subst. clear H2.
induction n.
 + intros.  now contradict H0.
 + destruct (eq_nat_dec n idx) as [ Heq | Hneq ]. 
    - simpl. subst.
      rewrite Hv.
      destruct defaultPage.
      destruct p. cbn in *. destruct pa.
      simpl in *. subst.
      case_eq ( p =? p0).
      * intros. apply beq_nat_true in H2.
        simpl in *.
        contradict H1.
        subst. 
        assert (Hp = Hp0) by apply proof_irrelevance. subst. reflexivity.
      * intros. apply in_app_iff. right.  simpl. left. reflexivity.
    - assert (idx < n). omega.
      assert (n <= tableSize). omega.
      simpl.
      case_eq (lookup root (CIndex n) (memory s) beqPage beqIndex);
      [intros v Hlookup | intros Hlookup]; [ | apply IHn; trivial].
      destruct v; [ 
                  case_eq (pa p0 =? defaultPage); intros Hnull;
                   [  | apply in_app_iff; left ] | |  | | ]; apply IHn ; trivial.
Qed.

Lemma getIndirectionInGetIndirections (n : nat) s:
n > 0 ->
n <= nbLevel ->
forall (va : vaddr) (level1 : level) (table root : page) (stop : nat),
getIndirection root va level1 stop s = Some table ->
table <> defaultPage ->
level1 <= CLevel (n - 1) -> root <> defaultPage -> In table (getIndirectionsAux root s n).
Proof.
intros Hl Hi  va  level1  table root stop 
Hind  Hnotnull Hlevel Hrnotnull .
destruct n. now contradict Hl.
revert Hind Hnotnull Hlevel Hl  Hrnotnull  (* Hlevel *).
revert va level1 table root stop . 
induction (S n);  [ simpl; intros; now contradict Hl |].
intros. simpl.
destruct stop; [ simpl in *; left; inversion Hind; trivial| ].
assert (StateLib.Level.eqb level1 fstLevel = true \/ StateLib.Level.eqb level1 fstLevel = false).
{ unfold StateLib.Level.eqb.
  destruct level1.
  simpl. unfold fstLevel.
  unfold CLevel.
  case_eq(lt_dec 0 nbLevel); intros.
  simpl.
  destruct l. left.
  symmetry. apply beq_nat_refl.
  right.
  apply NPeano.Nat.eqb_neq. omega.
  assert (0 < nbLevel) by apply nbLevelNotZero.
  now contradict H0. }
   
destruct H; [subst;  left; simpl in Hind; rewrite H in Hind; inversion Hind; trivial| ].
right. 
apply getIndirectionFstStep  in Hind; trivial; 
  [ | apply levelEqBEqNatFalse0 in H; assumption | omega  ].
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
+ assert (Hnbl : n0 <= nbLevel). omega.
  apply IHn0   with va pred (S stop - 1); trivial.
  - assert (StateLib.Level.eqb level1 fstLevel = false); trivial.
    apply levelPredMinus1 with level1 pred in H; [ | symmetry; assumption].
    subst.
    unfold CLevel.
    case_eq(lt_dec (level1 - 1) nbLevel); intros ll Hll; [ | destruct level1; simpl in *;
    assert (l< nbLevel) by omega; contradict Hll; omega]. 
    case_eq (lt_dec (n0 - 1) nbLevel); intros ll' Hll'; [ | omega].
    simpl.
    destruct level1.
    simpl in *.
    unfold CLevel in Hlevel.
    case_eq (lt_dec (n0 -0) nbLevel); intros l' Hl'; [ rewrite Hl' in *;simpl in *|]; omega.
  - apply levelEqBEqNatFalse0 in H.
    destruct n0; [ | omega]. 
    simpl in Hlevel.
    unfold CLevel in Hlevel.
    assert (0 < nbLevel) as Hll by apply nbLevelNotZero.
    case_eq (lt_dec 0 nbLevel); intros l' Hl';[     rewrite Hl' in *; simpl in *|]; omega.
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
simpl in *. omega.
apply in_seq.
simpl.
assert (0 < nbPage). apply nbPageNotZero.
destruct p.
simpl.
omega.
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
omega.
unfold incl.
intros.
apply AllPagesAll.
Qed.

Lemma nextEntryIsPPgetParent partition pd s :
nextEntryIsPP partition PPRidx pd s <-> 
StateLib.getParent partition (memory s) = Some pd.
Proof.
split.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getParent in *.
destruct(StateLib.Index.succ PPRidx); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getParent in *.
destruct(StateLib.Index.succ PPRidx); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
Qed. 



Lemma nbPartition s:
noDupPartitionTree s -> 
length (getPartitions multiplexer s) < (nbPage+1).
Proof.
intros.
rewrite NPeano.Nat.add_1_r.
apply le_lt_n_Sm.
apply lengthNoDupPartitions.
trivial.
Qed. 

Lemma childrenPartitionInPartitionList s phyVA parent: 
noDupPartitionTree s -> 
In parent (getPartitions multiplexer s ) ->
In phyVA (getChildren parent s) -> 
In phyVA (getPartitions multiplexer s).
Proof.
intro Hnodup. 
unfold getPartitions .
assert
(length (getPartitions multiplexer s) < (nbPage+1)).
apply nbPartition;trivial.
unfold getPartitions in H.
revert H.
generalize multiplexer. 
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
      destruct n. omega.
      simpl.
      left. trivial.
      right. apply IHl.
      intros.
      apply IHn.
      omega.
      assumption.
      right.
      assumption.
      apply lt_n_S.
      apply lt_S_n in H.
      rewrite app_length in H.  
      omega.
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
      omega.
      right.
      apply IHl; trivial.
      apply lt_n_S.
      apply lt_S_n in H.
      rewrite app_length in H.  
      omega.
Qed.

Lemma verticalSharingRec n s :
NoDup (getPartitions multiplexer s) -> 
noCycleInPartitionTree s -> 
isParent s -> 
verticalSharing s -> 
forall currentPart, 
In currentPart (getPartitions multiplexer s) ->
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
forall (n : nat) (s : state), NoDup (getPartitions multiplexer s) ->  noCycleInPartitionTree s ->
isParent s ->
verticalSharing s ->
forall currentPart : page,
In currentPart (getPartitions multiplexer s) ->
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
            In closestAnc (getPartitions multiplexer s) -> 
             In currentPart (getPartitionAux child1 s nbPage) -> 
            incl (getMappedPages currentPart s) (getMappedPages child1 s).
            Proof. intros Hcons Hvs. intros.
            unfold consistency in *. 
           apply verticalSharingRec with (nbPage-1); intuition.
           apply childrenPartitionInPartitionList with closestAnc; trivial.
           destruct nbPage.
           simpl in *. intuition.
           simpl.
           replace    (n - 0 + 1) with (S n) by omega.
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
NoDup (getPartitions multiplexer s) -> 
isParent s -> 
forall n child parent ancestor, 
In ancestor (getPartitions multiplexer s) ->
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
In currentPart (getPartitions multiplexer s)  -> 
StateLib.getParent descParent (memory s) = Some ancestor -> 
In descParent (getAncestors currentPart s) -> 
In ancestor (getAncestors currentPart s).
Proof.
intros Hnoduptree Hmultnone Hisparent.
revert descParent ancestor currentPart.
unfold getPartitions.
unfold getAncestors.
(* assert(Hge : nbPage >= nbPage) by omega.
revert Hge.
generalize nbPage at 1 3 4 . *)
induction nbPage ;intros descParent ancestor currentPart Hmult;intros;simpl in *.
destruct Hmult.
subst.
assert( StateLib.getParent multiplexer (memory s)  = None) by intuition.
rewrite H1 in H0. now contradict H0.
contradict H1.
clear.
induction   (getChildren multiplexer s);simpl in *; intuition.
destruct Hmult as [Hmult | Hmult].
+ subst. assert( StateLib.getParent multiplexer (memory s)  = None) by intuition.
rewrite H1 in *. now contradict H0.
+ 
case_eq(StateLib.getParent currentPart (memory s) );
[intros parent Hparent | intros Hparent ].
rewrite Hparent in H0.
simpl in *.
assert(Hi :parent = ancestor \/ parent <> ancestor ).
{ destruct parent;simpl in *;subst;destruct ancestor;simpl in *;subst.
  assert (Heq :p=p0 \/ p<> p0) by omega.
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
In parent (getPartitions multiplexer s) -> 
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
assert((exists entry : page, nextEntryIsPP parent PPRidx entry s /\ entry <> defaultPage)).
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
In x (getPartitions multiplexer s) -> 
In child (getPartitions multiplexer s) -> 
In ancestor (getPartitions multiplexer s) -> 
In ancestor (getAncestors child s) ->
In x (getChildren child s) -> 

In ancestor (getAncestors x s).
Proof.
intros Ha1 Ha2 Hnocycle Hisparent Hischild Hparentintree.
unfold getPartitions at 1, getAncestors.
induction (nbPage+1);simpl; intros;trivial.
destruct H;subst.
assert(Hfalse :  StateLib.getParent multiplexer (memory s) = Some child).
unfold isParent in *.
apply Hisparent;trivial.
assert(Htrue :  StateLib.getParent multiplexer (memory s) = None) by intuition.
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
  induction ((getChildren multiplexer s));simpl in *;intuition.
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
In parent (getPartitions multiplexer s) ->  
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
assert(Hchildintree : In child (getPartitions multiplexer s)).
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
assert(Htrue : In x (getPartitions multiplexer s)). 
apply childrenPartitionInPartitionList with child;trivial.
 apply IHn;trivial.
 apply isAncestorTrans3 with child;trivial.
Qed.

Lemma accessiblePageIsNotPartitionDescriptor
phyPDChild pdChild idxPDChild accessiblePDChild currentPart nbL presentPDChild 
currentPD (ptPDChild : page) s:
partitionsIsolation s ->  
kernelDataIsolation s -> 
 (defaultPage =? ptPDChild ) = false ->
accessiblePDChild = true -> 
presentPDChild = true -> 
StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild -> 
nextEntryIsPP currentPart PDidx currentPD s -> 
Some nbL = StateLib.getNbLevel -> 
(forall idx : index,
        StateLib.getIndexOfAddr pdChild fstLevel = idx ->
        isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) -> 
entryPresentFlag ptPDChild idxPDChild presentPDChild s -> 
entryUserFlag ptPDChild idxPDChild accessiblePDChild s -> 
isEntryPage ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) phyPDChild s -> 
In currentPart (getPartitions multiplexer s) -> 
~ In phyPDChild (getPartitionAux multiplexer s (nbPage + 1)).
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
generalize (Hanc currentPart multiplexer) ;  intro Hanc1.
assert( Hp2 : In multiplexer (getPartitions multiplexer s)).
{ unfold getPartitions. destruct nbPage;
  simpl; left; trivial. }
assert( Hpcur : In currentPart (getPartitions multiplexer s) ) by trivial.
apply Hanc1  with phyPDChild in Hcons; trivial.
apply Classical_Prop.not_or_and in Hcons.
destruct Hcons as (Hp1 & _).
clear Hanc1 Hp2.
assert(Hanc' : forall partition2  : page,
In partition2 (getPartitions multiplexer s) ->
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
nextEntryIsPP partition PDidx pd1 s -> 
StateLib.getPd partition (memory s) = Some pd2 -> 
pd1 = pd2.
Proof.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getPd in *.
destruct(StateLib.Index.succ PDidx); [| now contradict H0].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H0].
destruct v ; try now contradict H0.
inversion H0; subst; trivial.
Qed. 

Lemma getSh1NextEntryIsPPEq partition pd1 pd2 s :
nextEntryIsPP partition sh1idx pd1 s -> 
StateLib.getFstShadow partition (memory s) = Some pd2 -> 
pd1 = pd2.
Proof.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getFstShadow in *.
destruct(StateLib.Index.succ sh1idx); [| now contradict H0].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H0].
destruct v ; try now contradict H0.
inversion H0; subst; trivial.
Qed.
 
Lemma getSh2NextEntryIsPPEq partition pd1 pd2 s :
nextEntryIsPP partition sh2idx pd1 s -> 
StateLib.getSndShadow partition (memory s) = Some pd2 -> 
pd1 = pd2.
Proof.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getSndShadow in *.
destruct(StateLib.Index.succ sh2idx); [| now contradict H0].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H0].
destruct v ; try now contradict H0.
inversion H0; subst; trivial.
Qed. 

Lemma getListNextEntryIsPPEq partition pd1 pd2 s :
nextEntryIsPP partition sh3idx pd1 s -> 
StateLib.getConfigTablesLinkedList partition (memory s) = Some pd2 -> 
pd1 = pd2.
Proof.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getConfigTablesLinkedList in *.
destruct(StateLib.Index.succ sh3idx); [| now contradict H0].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H0].
destruct v ; try now contradict H0.
inversion H0; subst; trivial.
Qed.

Lemma getParentNextEntryIsPPEq partition pd1 pd2 s :
nextEntryIsPP partition PPRidx pd1 s -> 
StateLib.getParent partition (memory s) = Some pd2 -> 
pd1 = pd2.
Proof.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getParent in *.
destruct(StateLib.Index.succ PPRidx); [| now contradict H0].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H0].
destruct v ; try now contradict H0.
inversion H0; subst; trivial.
Qed.



Lemma nextEntryIsPPgetPd partition pd s :
nextEntryIsPP partition PDidx pd s <-> 
StateLib.getPd partition (memory s) = Some pd.
Proof.
split.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getPd in *.
destruct(StateLib.Index.succ PDidx); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getPd in *.
destruct(StateLib.Index.succ PDidx); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
Qed. 

Lemma nextEntryIsPPgetFstShadow partition sh1 s :
nextEntryIsPP partition sh1idx sh1 s <-> 
StateLib.getFstShadow partition (memory s) = Some sh1.
Proof.
split.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getFstShadow in *.
destruct(StateLib.Index.succ sh1idx); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getFstShadow in *.
destruct(StateLib.Index.succ sh1idx); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
Qed. 

Lemma nextEntryIsPPgetSndShadow partition sh2 s :
nextEntryIsPP partition sh2idx sh2 s <-> 
StateLib.getSndShadow partition (memory s) = Some sh2.
Proof.
split.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getSndShadow in *.
destruct(StateLib.Index.succ sh2idx); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getSndShadow in *.
destruct(StateLib.Index.succ sh2idx); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H].
destruct v ; try now contradict H.
inversion H; subst; trivial.
Qed. 

Lemma nextEntryIsPPgetConfigList partition list s :
nextEntryIsPP partition sh3idx list s -> 
StateLib.getConfigTablesLinkedList partition (memory s) = Some list.
Proof.
intros.
unfold nextEntryIsPP in *.
unfold  StateLib.getConfigTablesLinkedList in *.
destruct(StateLib.Index.succ sh3idx); [| now contradict H].
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex); [| now contradict H].
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
          (StateLib.getIndexOfAddr va fstLevel) (memory s));trivial.
destruct b; trivial.
destruct (defaultPage =? p0); try now contradict Haccesible.
destruct (StateLib.readAccessible p0 
(StateLib.getIndexOfAddr va fstLevel) (memory s)); 
[|now contradict Haccesible].
destruct b; trivial.
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
omega.
apply IHl; trivial.   
Qed.


Lemma notConfigTableNotPdconfigTableLt partition pd table s stop : 
stop < nbLevel - 1 -> 
partitionDescriptorEntry s -> 
In partition (getPartitions multiplexer s) -> 
~ In table (getConfigPagesAux partition s) -> 
StateLib.getPd partition (memory s) = Some pd -> 
~ In table (getIndirectionsAux pd s (S stop)).
Proof.
intros Hstop Hpde Hgetparts Hconfig Hpd .

unfold getConfigPagesAux in *.
rewrite Hpd in Hconfig.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition sh1idx in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getFstShadow in *.
destruct (StateLib.Index.succ sh1idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition sh2idx in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getSndShadow in *.
destruct (StateLib.Index.succ sh2idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition sh3idx in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ sh3idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) beqPage beqIndex);auto.
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
In partition (getPartitions multiplexer s) ->
In table (getIndirectionsAux pd s nbLevel)->
StateLib.getPd partition (memory s) = Some pd -> 
In table (getConfigPagesAux partition s).
Proof. 
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition sh1idx in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getFstShadow in *.
destruct (StateLib.Index.succ sh1idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition sh2idx in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getSndShadow in *.
destruct (StateLib.Index.succ sh2idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition sh3idx in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ sh3idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) beqPage beqIndex);auto.
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
In partition (getPartitions multiplexer s) -> 
~ In table (getConfigPagesAux partition s) -> 
StateLib.getPd partition (memory s) = Some pd -> 
~ In table (getIndirectionsAux pd s nbLevel).
Proof.
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd in Hconfig.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition sh1idx in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getFstShadow in *.
destruct (StateLib.Index.succ sh1idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition sh2idx in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getSndShadow in *.
destruct (StateLib.Index.succ sh2idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition sh3idx in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ sh3idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) beqPage beqIndex);auto.
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
In partition (getPartitions multiplexer s) -> 
~ In table (getConfigPagesAux partition s) -> 
StateLib.getFstShadow partition (memory s) = Some sh1 -> 
~ In table (getIndirectionsAux sh1 s (S stop)).
Proof.
intros Hstop Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd in Hconfig.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition PDidx in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ PDidx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition sh2idx in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getSndShadow in *.
destruct (StateLib.Index.succ sh2idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition sh3idx in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ sh3idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) beqPage beqIndex);auto.
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
In partition (getPartitions multiplexer s) ->
In table (getIndirectionsAux pd s nbLevel)->
StateLib.getFstShadow partition (memory s) = Some pd -> 
In table (getConfigPagesAux partition s).
Proof. 
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd .
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition PDidx in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ PDidx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition sh2idx in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getSndShadow in *.
destruct (StateLib.Index.succ sh2idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition sh3idx in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ sh3idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) beqPage beqIndex);auto.
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
In partition (getPartitions multiplexer s) -> 
~ In table (getConfigPagesAux partition s) -> 
StateLib.getFstShadow partition (memory s) = Some sh1 -> 
~ In table (getIndirectionsAux sh1 s nbLevel).
Proof.
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd in Hconfig.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition PDidx in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ PDidx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition sh2idx in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getSndShadow in *.
destruct (StateLib.Index.succ sh2idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition sh3idx in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ sh3idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) beqPage beqIndex);auto.
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
In partition (getPartitions multiplexer s) -> 
~ In table (getConfigPagesAux partition s) -> 
StateLib.getSndShadow partition (memory s) = Some sh2 -> 
~ In table (getIndirectionsAux sh2 s (S stop)).
Proof.
intros Hstop Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd in Hconfig.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition PDidx in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ PDidx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition sh1idx in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getFstShadow in *.
destruct (StateLib.Index.succ sh1idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition sh3idx in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ sh3idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) beqPage beqIndex);auto.
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
In partition (getPartitions multiplexer s) ->
In table (getIndirectionsAux pd s nbLevel)->
StateLib.getSndShadow partition (memory s) = Some pd -> 
In table (getConfigPagesAux partition s).
Proof.
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition PDidx in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ PDidx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition sh1idx in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getFstShadow in *.
destruct (StateLib.Index.succ sh1idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition sh3idx in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ sh3idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) beqPage beqIndex);auto.
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
In partition (getPartitions multiplexer s) -> 
~ In table (getConfigPagesAux partition s) -> 
StateLib.getSndShadow partition (memory s) = Some sh2 -> 
~ In table (getIndirectionsAux sh2 s nbLevel).
Proof.
intros Hpde Hgetparts Hconfig Hpd .
unfold getConfigPagesAux in *.
rewrite Hpd in Hconfig.
unfold partitionDescriptorEntry in *.
assert(Hgetpartssh2 :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition PDidx in Hgetparts;auto.
destruct Hgetparts as (Hrootidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getPd in *.
destruct (StateLib.Index.succ PDidx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear Hrootidx Hisva  Hnotnull.
assert(Hgetpartslist :In partition (getPartitions multiplexer s)) ; trivial.
apply Hpde with partition sh1idx in Hgetpartssh2;auto.
destruct Hgetpartssh2 as (Hrootsh2idx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold StateLib.getFstShadow in *.
destruct (StateLib.Index.succ sh1idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i0 (memory s) beqPage beqIndex);auto.
destruct v; auto.
subst.
clear  Hisva  Hnotnull.
apply Hpde with partition sh3idx in Hgetpartslist; auto.
destruct Hgetpartslist as (Hrootlistidx & Hisva & Hroot  & Hpp & Hnotnull).
unfold nextEntryIsPP in *.
unfold getConfigTablesLinkedList in *.
destruct (StateLib.Index.succ sh3idx); auto.
unfold  StateLib.readPhysical in *.
destruct (lookup partition i1 (memory s) beqPage beqIndex);auto.
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

      
Lemma pdSh1Sh2ListExistsNotNull  (s: state): 
partitionDescriptorEntry s -> 
forall partition, In partition (getPartitions multiplexer s) -> 
(exists pd , StateLib.getPd partition (memory s) = Some pd /\ pd <> defaultPage) /\ 
(exists sh1, StateLib.getFstShadow partition (memory s) = Some sh1 /\ sh1 <> defaultPage) /\ 
(exists sh2, StateLib.getSndShadow partition (memory s) = Some sh2 /\ sh2 <> defaultPage) /\ 
(exists list, getConfigTablesLinkedList partition (memory s) = Some list /\ list <> defaultPage).
Proof.
intros; unfold partitionDescriptorEntry in *.
repeat split.
+ apply H with partition PDidx in H0 .
  destruct H0 as (Hi & Hva & entry & Hentry & Hnotdef).
  exists entry.
  split; trivial.
  apply nextEntryIsPPgetPd; trivial.
  left. trivial.
+ apply H with partition sh1idx in H0 .
  destruct H0 as (Hi & Hva & entry & Hentry & Hnotdef).
  exists entry.
  split;trivial.
  apply nextEntryIsPPgetFstShadow; trivial.
  right;  left. trivial.
+ apply H with partition sh2idx in H0 .
  destruct H0 as (Hi & Hva & entry & Hentry & Hnotdef).
  exists entry.
  split; trivial.
  apply nextEntryIsPPgetSndShadow; trivial.
  right; right; left. trivial.
+ apply H with partition sh3idx in H0 .
  destruct H0 as (Hi & Hva & entry & Hentry & Hnotdef).
  exists entry.
  split;trivial.
  apply nextEntryIsPPgetConfigList ; trivial.
  right; right; right; left. trivial.
Qed.

Lemma isConfigTable descChild ptRefChild descParent s :
partitionDescriptorEntry s -> 
In descParent (getPartitions multiplexer s) -> 
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx descParent descChild s) -> 
(defaultPage =? ptRefChild) = false -> 
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
destruct Hget with (StateLib.getIndexOfAddr descChild fstLevel) ;trivial.
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

Lemma mappedPageIsNotPTable (table1 table2 currentPart root : page)
F  idxroot  va idx1 (s : state): 
 (idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx) -> 
(forall partition : page,
          In partition (getPartitions multiplexer s) ->
          partition = table2 \/ In table2 (getConfigPagesAux partition s) -> False) ->
In currentPart (getPartitions multiplexer s) ->
partitionDescriptorEntry s -> 
nextEntryIsPP currentPart idxroot root s -> 
StateLib.getIndexOfAddr va fstLevel = idx1 -> 
(forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx ->
       F table1 idx s /\ 
        getTableAddrRoot table1 idxroot currentPart va s) ->
(defaultPage =? table1) = false -> 
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
    pd <> defaultPage) /\ 
   (exists sh1, StateLib.getFstShadow currentPart (memory s) = Some sh1 /\
    sh1 <> defaultPage) /\ 
   (exists sh2, StateLib.getSndShadow currentPart (memory s) = Some sh2 /\ 
    sh2 <> defaultPage) /\ 
   (exists list, getConfigTablesLinkedList currentPart (memory s) = Some list /\ 
    list <> defaultPage)).
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
    assert (Hppref : nextEntryIsPP currentPart PDidx pd s) by trivial.
    destruct  Htblrootref as (_ & Htblrootref).
    generalize (Htblrootref pd  Hppref); clear Htblrootref; 
    intros Htblrootref.
    destruct Htblrootref as (nbL & HnbL & stop & Hstop & Hindref).
    apply getIndirectionInGetIndirections with va nbL stop; trivial.
    assert(0 < nbLevel) by apply nbLevelNotZero ; omega.
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
    assert (Hppref : nextEntryIsPP currentPart sh1idx sh1 s) by trivial.
    destruct  Htblrootref as (_ & Htblrootref).
    generalize (Htblrootref sh1  Hppref); clear Htblrootref; 
    intros Htblrootref.
    destruct Htblrootref as (nbL & HnbL & stop & Hstop & Hindref).
    apply getIndirectionInGetIndirections with va nbL stop; trivial.
    assert(0 < nbLevel) by apply nbLevelNotZero ; omega.
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
    assert (Hppref : nextEntryIsPP currentPart sh2idx sh2 s) by trivial.
    destruct  Htblrootref as (_ & Htblrootref).
    generalize (Htblrootref sh2  Hppref); clear Htblrootref; 
    intros Htblrootref.
    destruct Htblrootref as (nbL & HnbL & stop & Hstop & Hindref).
    apply getIndirectionInGetIndirections with va nbL stop; trivial.
    assert(0 < nbLevel) by apply nbLevelNotZero ; omega.
    apply beq_nat_false in Hptrefnotnull.
    unfold not; intros Hnot.
    subst. now contradict Hptrefnotnull.
    apply getNbLevelLe; trivial. }
  unfold not; intros Hnot.
  subst; now contradict Hin.
Qed.

Lemma checkVAddrsEqualityWOOffsetPermut va1 va2 level1 : 
  StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 level1 = 
  StateLib.checkVAddrsEqualityWOOffset nbLevel va2 va1 level1. 
Proof.
  revert va1 va2 level1.
  induction nbLevel.
  simpl. trivial.
  simpl. intros.
  case_eq (StateLib.Level.eqb level1 fstLevel); intros.
  apply NPeano.Nat.eqb_sym.
  case_eq(StateLib.Level.pred level1);
  intros; trivial. 
  rewrite  NPeano.Nat.eqb_sym.
  case_eq (StateLib.getIndexOfAddr va2 level1 =? StateLib.getIndexOfAddr va1 level1); intros; trivial.
Qed.

Lemma entryPresentFlagReadPresent s table idx flag: 
entryPresentFlag table idx flag s -> 
StateLib.readPresent table idx (memory s)  = Some flag.
Proof.
unfold entryPresentFlag , StateLib.readPresent .
intros.
destruct (lookup table idx (memory s) beqPage beqIndex );try now contradict H.
destruct v; try now contradict H.
subst;trivial.
Qed.

Lemma entryUserFlagReadAccessible s table idx flag: 
entryUserFlag table idx flag s -> 
StateLib.readAccessible table idx (memory s)  = Some flag.
Proof.
unfold entryUserFlag , StateLib.readAccessible .
intros.
destruct (lookup table idx (memory s) beqPage beqIndex );try now contradict H.
destruct v; try now contradict H.
subst;trivial.
Qed.

Lemma isEntryPageLookupEq table idx entry phy s:
lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
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
destruct(lookup table idx (memory s) beqPage beqIndex );
try now contradict Hentrypage.
destruct v; try now contradict Hentrypage.
f_equal;trivial.
Qed.

Lemma isAccessibleMappedPage pdChild currentPD (ptPDChild : page)  entry s : 
(defaultPage =? ptPDChild ) = false -> 
entryPresentFlag ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) true s -> 
entryUserFlag ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) true s -> 
lookup ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) (memory s) beqPage beqIndex =
    Some (PE entry) -> 
 nextEntryIsPP (currentPartition s) PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx (currentPartition s) pdChild s ) -> 
getAccessibleMappedPage currentPD s pdChild = Some (pa entry).
Proof.
intros Hnotnull Hpe Hue Hlookup Hpp Hget .
assert ( isPE ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) s /\ 
        getTableAddrRoot ptPDChild PDidx (currentPartition s) pdChild s) as (_ & Hroot).
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
apply getIndirectionStopLevelGT2 with (nbL + 1);try omega;trivial.
apply getNbLevelEq in HnbL.
unfold CLevel in HnbL.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros; rewrite H in *.
destruct nbL.
simpl in *.
inversion HnbL; trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.
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
(defaultPage =? ptPDChild ) = false -> 
entryPresentFlag ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) true s -> 
entryUserFlag ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) true s -> 
isEntryPage ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) phypage s -> 
 nextEntryIsPP partition PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx partition pdChild s ) -> 
getAccessibleMappedPage currentPD s pdChild = Some phypage.
Proof.
intros Hnotnull Hpe Hue Hlookup Hpp Hget .
assert ( isPE ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel) s /\ 
        getTableAddrRoot ptPDChild PDidx partition pdChild s) as (_ & Hroot).
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
apply getIndirectionStopLevelGT2 with (nbL + 1);try omega;trivial.
apply getNbLevelEq in HnbL.
unfold CLevel in HnbL.
case_eq (lt_dec (nbLevel - 1) nbLevel); intros; rewrite H in *.
destruct nbL.
simpl in *.
inversion HnbL; trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.
rewrite Hnewind.
apply entryPresentFlagReadPresent in Hpe.
rewrite Hpe.
apply entryUserFlagReadAccessible in Hue.
rewrite Hue.
unfold StateLib.readPhyEntry.
rewrite Hnotnull.
unfold isEntryPage in *.
destruct(lookup ptPDChild (StateLib.getIndexOfAddr pdChild fstLevel)
              (memory s) beqPage beqIndex);
              try now contradict Hlookup.
destruct v;            try now contradict Hlookup.
f_equal;

trivial.
Qed.

Lemma getPDFlagReadPDflag currentShadow1 pdChild (ptPDChildSh1 : page)
idxPDChild currentPart s:
(ptPDChildSh1 =? defaultPage) = false ->
nextEntryIsPP currentPart sh1idx currentShadow1 s -> 
getPDFlag currentShadow1 pdChild s = false -> 
StateLib.getIndexOfAddr pdChild fstLevel =  idxPDChild -> 
(forall idx : index,
   StateLib.getIndexOfAddr pdChild fstLevel = idx ->
   isVE ptPDChildSh1 idx s /\ 
   getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) ->
StateLib.readPDflag ptPDChildSh1 idxPDChild (memory s) = Some false \/ 
StateLib.readPDflag ptPDChildSh1 idxPDChild (memory s) = None .
Proof.
intros Hptnotnull Hsh1 Hgetflag Hidx Hind.
assert(isVE ptPDChildSh1 (StateLib.getIndexOfAddr pdChild fstLevel) s /\ 
      getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) as (Hve & Hget).
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
apply getIndirectionStopLevelGT2 with (nbL +1);try omega;trivial.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq ( lt_dec (nbLevel - 1) nbLevel);intros.
simpl;trivial.
assert(0 < nbLevel) by apply nbLevelNotZero.
omega.
rewrite Hind1 in *.
rewrite Hptnotnull in *.
case_eq(StateLib.readPDflag ptPDChildSh1 
        (StateLib.getIndexOfAddr pdChild fstLevel) (memory s));intros.
rewrite H in *.
destruct b; try now contradict Hgetflag.
trivial.
left;trivial.
right;trivial.
Qed.

Lemma isVaInParent s va descParent (ptsh2 : page) vaInAncestor sh2 :
(defaultPage =? ptsh2) = false -> 
(forall idx : index,
StateLib.getIndexOfAddr va fstLevel = idx ->
isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) -> 
isVA' ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s -> 
nextEntryIsPP descParent sh2idx sh2 s -> 
getVirtualAddressSh2 sh2 s va = Some vaInAncestor.
Proof.
intros Hnotnull Hroot Hva Hpp .
assert( isVA ptsh2 (StateLib.getIndexOfAddr va fstLevel ) s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) as (Hisva & Hget).
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
omega.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq( lt_dec (nbLevel - 1) nbLevel );intros.
simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.
clear Hind.
rewrite H.
rewrite Hnotnull.
unfold isVA' in *.
unfold StateLib.readVirtual.
destruct( lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex );
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
entryPresentFlag pt (StateLib.getIndexOfAddr vaInDescParent fstLevel) true s -> 
(defaultPage =? pt) = false -> 
Some nbL1 = StateLib.getNbLevel -> 
nextEntryIsPP descParent PDidx pdDesc s -> 
getIndirection pdDesc vaInDescParent nbL1 (nbL1 + 1) s = Some pt -> 
isEntryPage pt (StateLib.getIndexOfAddr vaInDescParent fstLevel) (pa entry) s ->
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
exists vaInDescParent;split.
unfold getMappedPage.
rewrite <- HnbL.
assert(Hnewind : getIndirection pdDesc vaInDescParent nbL1 (nbLevel - 1) s  = Some pt).
apply getIndirectionStopLevelGT2 with (nbL1+1);trivial.
omega.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq(   lt_dec (nbLevel - 1) nbLevel);intros.
simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.
rewrite Hnewind.
rewrite Hptnotnull.
rewrite entryPresentFlagReadPresent with s pt  (StateLib.getIndexOfAddr 
vaInDescParent fstLevel) true;trivial.
apply isEntryPageReadPhyEntry;trivial.
apply AllVAddrAll.
Qed.

Lemma getMappedPageGetIndirection ancestor phypage newVA pdAncestor
 (ptAncestor : page) L  s:
StateLib.readPresent ptAncestor (StateLib.getIndexOfAddr newVA fstLevel)
 (memory s) = Some true -> 
(defaultPage =? ptAncestor) = false -> 
 Some L = StateLib.getNbLevel -> 
nextEntryIsPP ancestor PDidx pdAncestor s -> 
getIndirection pdAncestor newVA L (nbLevel - 1) s = Some ptAncestor -> 
StateLib.readPhyEntry ptAncestor (StateLib.getIndexOfAddr newVA fstLevel)
 (memory s) =  Some phypage -> 
getMappedPage pdAncestor s newVA = Some phypage.
Proof.
intros Hpresent Hptnotnull HnbL Hpd Hind Hep.
unfold getMappedPage.
rewrite nextEntryIsPPgetPd in *.
rewrite <- HnbL.
rewrite Hind.
rewrite Hptnotnull.
rewrite Hpresent;trivial.
Qed.

Lemma getMappedPageGetTableRoot ptvaInAncestor ancestor phypage pdAncestor vaInAncestor s :
( forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) -> 
(defaultPage =? ptvaInAncestor) = false ->
 isEntryPage ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
 phypage s ->
 entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) true s
  ->
nextEntryIsPP ancestor PDidx pdAncestor s -> 
getMappedPage pdAncestor s vaInAncestor = Some phypage.
Proof.
intros Hget Hnotnull Hep Hpresent Hpdparent.
destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
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
omega.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel);
intros;simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.
rewrite Hnewind.
rewrite Hnotnull.
apply entryPresentFlagReadPresent in Hpresent.
rewrite Hpresent.
unfold isEntryPage in *.
unfold StateLib.readPhyEntry.
destruct(lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
 (memory s) beqPage beqIndex );
try now contradict Hep.
destruct v; try now contradict Hep.
f_equal;trivial.
Qed.
Lemma getVirtualAddressSh2GetTableRoot:
forall (ptsh2 descParent  sh2  : page) 
    (vaInAncestor va: vaddr) (s : state) L,
(forall idx : index,
  StateLib.getIndexOfAddr va fstLevel = idx ->
   isVA ptsh2 idx s /\ getTableAddrRoot ptsh2 sh2idx descParent va s) ->
(defaultPage =? ptsh2) = false ->
isVA' ptsh2 (StateLib.getIndexOfAddr va fstLevel) vaInAncestor s -> 
StateLib.getSndShadow descParent (memory s) = Some sh2 -> 
Some L = StateLib.getNbLevel ->
getVirtualAddressSh2 sh2 s va = Some vaInAncestor.
Proof. 
intros ptsh2 descParent sh2 vaInAncestor va  s L.
intros Hget Hnotnull Hisva Hsh2 HL.

unfold getVirtualAddressSh2.
rewrite <- HL.
destruct Hget with (StateLib.getIndexOfAddr va fstLevel)
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
apply getIndirectionStopLevelGT2 with (nbL +1);try omega;trivial.
apply getNbLevelEq in HnbL.
subst. apply nbLevelEq.
rewrite Hnewind.
rewrite Hnotnull.
unfold isVA' in *.
unfold StateLib.readVirtual.
destruct(lookup ptsh2 (StateLib.getIndexOfAddr va fstLevel) 
(memory s) beqPage beqIndex );
try now contradict Hisva.
destruct v; try now contradict Hisva.
f_equal;trivial.
Qed.
Lemma getMappedPageNotAccessible  
ptvaInAncestor ancestor phypage pdAncestor vaInAncestor s :
( forall idx : index,
      StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
      isPE ptvaInAncestor idx s /\ 
      getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) -> 
(defaultPage =? ptvaInAncestor) = false ->
 isEntryPage ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
 phypage s ->
 entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) true s ->
entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) false s ->
nextEntryIsPP ancestor PDidx pdAncestor s -> 
getAccessibleMappedPage pdAncestor s vaInAncestor = None.
Proof.
intros Hget Hnotnull Hep Hpresent Huser Hpdparent.
destruct Hget with (StateLib.getIndexOfAddr vaInAncestor fstLevel)
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
omega.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel);
intros;simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.
rewrite Hnewind.
rewrite Hnotnull.
apply entryPresentFlagReadPresent in Hpresent.
rewrite Hpresent.
unfold isEntryPage in *.
unfold StateLib.readPhyEntry.
destruct(lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
 (memory s) beqPage beqIndex );
try now contradict Hep.
destruct v; try now contradict Hep.
unfold StateLib.readAccessible.
unfold entryUserFlag in *.
case_eq(lookup ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) 
            (memory s) beqPage beqIndex);[intros v Hv | intros Hv];
            rewrite Hv in *; trivial.
case_eq v; intros entry Hentry;
rewrite Hentry in *; trivial.
rewrite <- Huser;trivial.
Qed.

Lemma inGetMappedPagesGetTableRoot va pt descParent phypage pdParent s :
(forall idx : index,
StateLib.getIndexOfAddr va fstLevel = idx ->
isPE pt idx s /\ getTableAddrRoot pt PDidx descParent va s) -> 
(defaultPage =? pt) = false ->
isEntryPage pt(StateLib.getIndexOfAddr va fstLevel)  phypage s ->
entryPresentFlag pt (StateLib.getIndexOfAddr va fstLevel)  true s ->
nextEntryIsPP descParent PDidx pdParent s -> 
In phypage (getMappedPages descParent s).
Proof.
intros Hget Hnotnull Hep Hpresent Hpdparent.
destruct Hget with (StateLib.getIndexOfAddr va fstLevel)
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
exists va;split.
unfold getMappedPage.
rewrite <- HnbL.
subst.
assert(Hnewind :getIndirection  pdParent va nbL  (nbLevel - 1) s = Some pt).
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
omega.
apply getNbLevelEq in HnbL.
subst.
unfold CLevel.
case_eq(lt_dec (nbLevel - 1) nbLevel);
intros;simpl;trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega.
rewrite Hnewind.
rewrite Hnotnull.
apply entryPresentFlagReadPresent in Hpresent.
rewrite Hpresent.
unfold isEntryPage in *.
unfold StateLib.readPhyEntry.
destruct(lookup pt (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex );
try now contradict Hep.
destruct v; try now contradict Hep.
f_equal;trivial.
apply AllVAddrAll.
Qed.



Lemma pageDecOrNot :
forall p1 p2 : page, p1 = p2 \/ p1<>p2.
Proof.
destruct p1;simpl in *;subst;destruct p2;simpl in *;subst.
assert (Heq :p=p0 \/ p<> p0) by omega.
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
In currentPart (getPartitions multiplexer s) -> 
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
nextEntryIsPP partition PPRidx ancestor s -> 
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
(defaultPage =? phyPage) = false.
Proof.
intros.
unfold isPresentNotDefaultIff in *.
assert (StateLib.readPhyEntry table idx (memory s) = Some phyPage).
{ unfold StateLib.readPhyEntry.
 unfold isEntryPage in *.
 case_eq(lookup table idx (memory s) beqPage beqIndex);intros * Hi;
 rewrite Hi in *;try now contradict H1.
 case_eq v;intros * Hii;
 rewrite Hii in *;try now contradict H1.
 subst;trivial. }
assert (StateLib.readPresent table idx (memory s) = Some true).
{ unfold StateLib.readPresent .
  unfold entryPresentFlag in *.
  case_eq(lookup table idx (memory s) beqPage beqIndex);intros * Hi;
  rewrite Hi in *;try now contradict H1.
  case_eq v;intros * Hii;
  rewrite Hii in *;try now contradict H1.
  subst;f_equal;symmetry; trivial. }
clear H1 H0.
apply Nat.eqb_neq.
unfold not;intros;subst.
destruct phyPage;destruct defaultPage.
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
 lookup table idx (memory s) beqPage beqIndex = Some (PE entry) -> 
(defaultPage =? pa entry) = false -> 
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
getAccessibleMappedPage pd s va = Some accessiblePage -> 
getMappedPage pd s va = Some accessiblePage.
Proof.
intros.
unfold getMappedPage.
unfold getAccessibleMappedPage in *.
destruct( StateLib.getNbLevel);try now contradict H.
destruct ( getIndirection pd va l (nbLevel - 1) s );try now contradict H.
destruct(defaultPage =? p);try now contradict H.
destruct(StateLib.readPresent p (StateLib.getIndexOfAddr va fstLevel) (memory s) );
try
 now contradict H.
 destruct b;try now contradict H.
destruct( StateLib.readAccessible p (StateLib.getIndexOfAddr va fstLevel) (memory s));
try now contradict H.
destruct b;try now contradict H.

trivial.
Qed.
Import List.ListNotations.
Lemma getIndirectionsOnlyPD pd s: 
(forall idx : index,
        StateLib.readPhyEntry pd idx (memory s) = Some defaultPage /\
        StateLib.readPresent pd idx (memory s) = Some false) -> 
  getIndirections pd s = [pd].
Proof.
intros.      
unfold getIndirections.
assert(0<nbLevel) by apply nbLevelNotZero.
destruct nbLevel.
simpl.
omega.
simpl.
f_equal.
induction tableSize.
simpl;trivial.
simpl.
intros.
destruct H with (CIndex n0) as (Hphy & Hpres);trivial.
unfold StateLib.readPhyEntry in *.
case_eq(lookup pd (CIndex n0) (memory s) beqPage beqIndex);
intros * Hread;rewrite Hread in *;trivial.
case_eq v;intros * Hv; rewrite Hv in *;trivial.
inversion Hphy.
subst.
case_eq( pa p =? pa p);intros Hfalse;trivial.
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
omega.
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
case_eq(lookup sh1 (CIndex n0) (memory s) beqPage beqIndex);
intros * Hread;rewrite Hread in *;trivial.
case_eq v;intros * Hv; rewrite Hv in *;trivial.
inversion Hphy.
subst.
case_eq( pa p =? pa p);intros Hfalse;trivial.
apply beq_nat_false in Hfalse.
now contradict Hfalse.
inversion IHn0. 
destruct H0.
destruct H0 as (Hlevel & Hcontent).
destruct H2 with (CIndex n0) as (Hphy & Hpres);trivial.
unfold StateLib.readVirEntry in *.
case_eq(lookup sh1 (CIndex n0) (memory s) beqPage beqIndex);
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
omega.
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
case_eq(lookup sh2 (CIndex n0) (memory s) beqPage beqIndex);
intros * Hread;rewrite Hread in *;trivial.
case_eq v;intros * Hv; rewrite Hv in *;trivial.
inversion Hphy.
subst.
case_eq( pa p =? pa p);intros Hfalse;trivial.
apply beq_nat_false in Hfalse.
now contradict Hfalse.
inversion IHn0. 
destruct H0.
destruct H0 as (Hlevel & Hcontent).

unfold StateLib.readVirtual in *.

generalize (H2 (CIndex n0)) ; clear H2 ;intros H2.
case_eq(lookup sh2 (CIndex n0) (memory s) beqPage beqIndex);
intros * Hread;rewrite Hread in *;trivial.
case_eq v;intros * Hv; rewrite Hv in *;trivial.
now contradict H2.
Qed.

Lemma getTrdShadowsOnlyRoot root s:
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
getTrdShadows root s (nbPage+1) = 
[root].
Proof.
intros  HphyListcontent1 HphyListcontent2 HphyListcontent3 .

 assert(Hi : 0<nbPage+1) by omega.

destruct (nbPage+1).
simpl. 
omega.
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
assert((defaultPage =? defaultPage ) = true).
apply NPeano.Nat.eqb_refl.
rewrite H1;trivial.
now contradict H0.
unfold StateLib.getMaxIndex in *.
case_eq (gt_dec tableSize 0 );intros;
rewrite H0 in *.
now contradict H0.
 assert(tableSizeLowerBound<tableSize) by apply tableSizeBigEnough.
unfold tableSizeLowerBound in *.
omega.
Qed.

Require Import Coq.Sorting.Permutation.

Lemma getIndirectionGetTableRoot (s : state) currentShadow1 currentPart ptRefChildFromSh1 descChild 
nbL : 
StateLib.getFstShadow currentPart (memory s) = Some currentShadow1 -> 
StateLib.getNbLevel = Some nbL -> 
(forall idx : index,
  StateLib.getIndexOfAddr descChild fstLevel = idx ->
  isVE ptRefChildFromSh1 idx s /\ 
  getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) 
  -> 
getIndirection currentShadow1 descChild nbL (nbLevel - 1) s = Some ptRefChildFromSh1. 
Proof.
intros.
destruct H1 with (StateLib.getIndexOfAddr descChild fstLevel );
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
omega.
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
  StateLib.getIndexOfAddr va fstLevel = idx ->
  isPE pt idx s /\ 
  getTableAddrRoot pt PDidx currentPart va s) 
  -> 
getIndirection pd va nbL (nbLevel - 1) s = Some pt. 
Proof.
intros.
destruct H1 with (StateLib.getIndexOfAddr va fstLevel );
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
omega.
symmetry in H0. 
apply getNbLevelEq in H0.
subst.
apply nbLevelEq.
Qed.

Lemma readPhyEntryInGetIndirectionsAux s root n: 
forall page1,page1 <> defaultPage -> 
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
destruct n.  omega. simpl.
left. trivial.     
Qed.

Lemma nodupLevelMinus1 root s (n0 : nat) idx: 
forall p , p<> defaultPage -> 
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
(defaultPage =? p) = false -> 
n> 1 -> 
incl (getIndirectionsAux p s (n - 1)) (getIndirectionsAux root s n).
Proof.
intros Hread Hnotnull Hn. 
unfold incl.              
intros.
set(k := n -1) in *.
replace n with (S k); [ | unfold k; omega].
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
(defaultPage =? p) = false -> 
(defaultPage =? p0) = false -> 
NoDup (getIndirectionsAux root s n) -> 
StateLib.readPhyEntry root idx1 (memory s) = Some p0 -> 
StateLib.readPhyEntry root idx2 (memory s) = Some p ->
disjoint (getIndirectionsAux p s (n - 1)) (getIndirectionsAux p0 s (n - 1)).
Proof. 
unfold disjoint.
intros Hp0p Hn Hnotnull1 Hnotnull2 Hnodup Hreadp0 Hreadp x Hxp.        
set(k := n -1) in *.
assert(n = S k) as Hk.
unfold k in *.  omega.          
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
(defaultPage =? p) = false ->  
level1 <= CLevel (n -1) -> 
StateLib.Level.pred level1 = Some pred -> 
table <> defaultPage -> 
n <= nbLevel -> 
n > 1 -> 
getIndirection p va1 pred n1 s = Some table -> 
In table (getIndirectionsAux p s (n - 1)). 
Proof.
intros Hfstlevel Hnotnull Hlevel Hpred Hnotnullt Hnbl Hn Hind.
apply getIndirectionInGetIndirections 
with va1 pred n1;trivial;  try omega.
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
    simpl in *. omega. omega.  
    case_eq (lt_dec (n - 1 - 1) nbLevel);
    intros.
    simpl in *. omega. omega.
    destruct level1. 
    simpl in *. omega. 
    unfold StateLib.Level.eqb.
    unfold CLevel. 
    case_eq(lt_dec (n - 1) nbLevel ); intros;
    simpl in *.
    unfold fstLevel. unfold CLevel.
    case_eq(lt_dec 0 nbLevel).
    intros. simpl.
    apply NPeano.Nat.eqb_neq. omega.
    intros. assert (0 < nbLevel) by apply nbLevelNotZero.
    omega. omega.
  - apply beq_nat_false in Hnotnull. unfold not. intros.
    apply Hnotnull. subst. trivial. 
Qed.
    
Lemma getTablePagesNoDup root (p p0 : page) idx1 idx2    s:
idx1 < tableSize -> idx2 < tableSize ->
NoDup (getTablePages root tableSize s) -> 
StateLib.readPhyEntry root (CIndex idx1) (memory s) = Some p0 -> 
StateLib.readPhyEntry root (CIndex idx2) (memory s) = Some p -> 
(idx1 =? idx2) = false ->
(p =? defaultPage) = false -> 
(p0 =? defaultPage) = false -> 
p0 <> p.
Proof.
assert (H: tableSize <= tableSize) by omega; revert H.
generalize tableSize at 1 3 4 5  .
induction n.
+ intros. now contradict H0.
+ intros. simpl in *.
  apply beq_nat_false in H5. 
  assert(Hdec : (idx1 = n /\ idx2 <> n) \/ 
          (idx2 = n /\ idx1 <> n) \/ 
          (idx1 <> n /\ idx2 <> n)). omega.
  destruct Hdec as [(Hdec1 & Hdec2) | [(Hdec1 & Hdec2) |(Hdec1 & Hdec2)]];
  subst.
  * unfold StateLib.readPhyEntry in H3. intros.
    case_eq (lookup root (CIndex n) (memory s) beqPage beqIndex); 
    [ intros v Hv'| intros Hv'] ; rewrite Hv' in  *; [ | now contradict H3 ];
    destruct v; try now contradict H3. inversion H3. subst.
    subst.  clear IHn H3. rewrite H7 in H2.
    apply NoDupSplitInclIff in H2.
    destruct H2 as ( (_ & _) & H2).
    unfold disjoint in H2.
    assert (In p (getTablePages root n s)).
    apply readPhyEntryInGetTablePages with idx2; trivial.
    omega. omega. 
    unfold not. intros. subst. apply beq_nat_false in H6.
    now contradict H6.
    apply H2 in H3. unfold not. intros.
    contradict H3. simpl in *. left. assumption.
  * unfold StateLib.readPhyEntry in H4. intros.
    case_eq (lookup root (CIndex n) (memory s) beqPage beqIndex); 
    [ intros v Hv'| intros Hv'] ; rewrite Hv' in  *; [ | now contradict H4 ];
    destruct v; try now contradict H4. inversion H4. subst.
    subst.  clear IHn H4. rewrite H6 in H2.
    apply NoDupSplitInclIff in H2.
    destruct H2 as ( (_ & _) & H2).
    unfold disjoint in H2.
    assert (In p0 (getTablePages root n s)).
    apply readPhyEntryInGetTablePages with idx1; trivial.
    omega. omega. 
    unfold not. intros. subst. apply beq_nat_false in H7.
    now contradict H7.
    apply H2 in H4. unfold not. intros.
    contradict H4. simpl in *. left. rewrite H8. trivial.
  *  case_eq (lookup root (CIndex n) (memory s) beqPage beqIndex); 
    [ intros v Hv'| intros Hv'] ; rewrite Hv' in  *;
    
    [ |
    apply IHn; trivial;try omega;
    apply Nat.eqb_neq; trivial ].
    destruct v; [ | apply IHn;  trivial;try omega;
    apply Nat.eqb_neq; trivial |
    apply IHn;  trivial;try omega;
    apply Nat.eqb_neq; trivial | apply IHn;  trivial;try omega;
    apply Nat.eqb_neq; trivial | apply IHn;  trivial;try omega;
    apply Nat.eqb_neq; trivial].
    case_eq(pa p1 =? defaultPage); intros Hnull; rewrite Hnull in *.
    { apply IHn; trivial; try omega. apply Nat.eqb_neq; trivial. }
    {
    apply NoDupSplitInclIff in H2.
    destruct H2 as ( (H2 & _) &  _).
    apply IHn; trivial; try omega. apply Nat.eqb_neq; trivial. }
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
destruct n. simpl in *. omega.
simpl. left. trivial.
unfold not. contradict H.
apply in_flat_map. exists a.
split. assumption. destruct n; simpl. now contradict Hn.
left. trivial.  
apply IHl; trivial.
Qed. 
                  

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
+ clear H.
  revert HNoDup1 HNoDup2 Hvas Hlevel Hnotnull1 Hnotnull2 
  Htableroot1 (* Hstop *) Htableroot2 H0 Hroot1 Hroot2 .
  revert root1 root2 table1 table2 level1 va1 va2.
  assert (Hs :stop <= stop). omega. revert Hs.  
  generalize stop at 1 3 4 5 .
  intros.
  destruct stop0.
  simpl in *.
  now contradict Hvas.
  assert (nbLevel <= nbLevel) as Hnbl by omega.
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
  case_eq (StateLib.Level.eqb level1 fstLevel); intros . rewrite H in *.
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
          contradict Hnull2. subst. trivial. }
    * clear IHn. 
      left. clear stop0 stop (* Hstop *) Hs Hvas . 
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
Lemma toApplyPageTablesOrIndicesAreDifferent idx1 idx2 va1 va2 (table1 table2 : page) 
currentPart root idxroot level1 F s: 
(idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx) -> 
(defaultPage =? table1) = false -> (defaultPage =? table2) = false -> 
false = StateLib.checkVAddrsEqualityWOOffset nbLevel va1 va2 level1 -> 
currentPart = currentPartition s -> 
consistency s -> 
StateLib.getIndexOfAddr va1 fstLevel = idx1 -> 
StateLib.getIndexOfAddr va2 fstLevel = idx2 -> 
(forall idx : index,
StateLib.getIndexOfAddr va1 fstLevel = idx ->
F table1 idx s /\ getTableAddrRoot table1 idxroot currentPart va1 s) -> 
(forall idx : index,
StateLib.getIndexOfAddr va2 fstLevel = idx ->
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
  unfold consistency in *.
  destruct Hcons.
  unfold partitionDescriptorEntry in *.
  assert (currentPartitionInPartitionsList s ) as Hpr by intuition.
  unfold currentPartitionInPartitionsList in *.
  subst.
  generalize (H  (currentPartition s)  Hpr); clear H; intros H.
  assert (idxroot = PDidx \/
    idxroot = sh1idx \/ idxroot = sh2idx \/ idxroot = sh3idx \/ idxroot = PPRidx 
    \/ idxroot = PRidx) as Hpd .
    intuition.

  apply H in Hpd.
  destruct Hpd as (_ & _ & Hpd).
  destruct Hpd as (pd & Hrootpd & Hnotnul).
  move Hroot at bottom.
  move Hrootpd  at bottom.
  move Hnotnul at bottom.
  unfold nextEntryIsPP in Hroot , Hrootpd.
  destruct (StateLib.Index.succ idxroot).
  subst. 
  destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex); [
  | now contradict Hroot].
  destruct v; [  
  now contradict Hroot| now contradict Hroot | | now contradict Hroot | now contradict Hroot].
  subst. assumption. now contradict Hroot.
  unfold consistency in *.
  destruct Hcons.
  unfold partitionDescriptorEntry in *.
  assert (currentPartitionInPartitionsList s ) as Hpr by intuition.
  unfold currentPartitionInPartitionsList in *.
  subst.
  generalize (H  (currentPartition s)  Hpr); clear H; intros H.
  assert (idxroot = PDidx \/
    idxroot = sh1idx \/ idxroot = sh2idx \/ idxroot = sh3idx \/ idxroot = PPRidx \/ idxroot = PRidx)  as Hpd 
  by intuition.
  apply H in Hpd.
  destruct Hpd as (_ & _ & Hpd).
  destruct Hpd as (pd & Hrootpd & Hnotnul).
  move Hroot at bottom.
  move Hrootpd  at bottom.
  move Hnotnul at bottom.
  unfold nextEntryIsPP in Hroot , Hrootpd.
  destruct (StateLib.Index.succ idxroot).
  subst.
  destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex); [
  | now contradict Hroot].
  destruct v; [  
   now contradict Hroot| now contradict Hroot | | now contradict Hroot |
    now contradict Hroot].
  subst. assumption.
  now contradict Hroot.
  unfold consistency in Hcons.
  unfold noDupConfigPagesList in Hcons.
  unfold currentPartitionInPartitionsList in Hcons.
  destruct Hcons as (_ & _& _& _& Hcurprt & _ & Hdup). subst.
  apply Hdup with idxroot (currentPartition s); trivial.
  unfold consistency in Hcons.
  unfold noDupConfigPagesList in Hcons.
  unfold currentPartitionInPartitionsList in Hcons.
  destruct Hcons as (_ & _& _& _& Hcurprt & _ & Hdup). subst.
  apply Hdup with idxroot (currentPartition s); trivial.

  move Hlevel at bottom.
  unfold StateLib.getNbLevel in Hlevel.
   case_eq (gt_dec nbLevel 0 ); intros;
  rewrite H in Hlevel.
  rewrite Hstop2.
  inversion Hlevel.
  rewrite H1 in *. simpl.
  symmetry. assert( (nbLevel - 1 + 1)  = nbLevel).
  omega. rewrite H0.
  assumption.
  now contradict H. 
  left. split.
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
  rewrite H1. reflexivity. omega.
  assert (0 < nbLevel) by apply nbLevelNotZero. omega.
  trivial. 
  apply beq_nat_false in Hnotnull1.
  unfold not. intros.
  contradict Hnotnull1. subst. trivial.
  apply beq_nat_false in Hnotnull2.
  unfold not. intros.
  contradict Hnotnull2. subst. trivial.
Qed.

Lemma getMappedPagesAuxConsSome :
forall pd va phyVa listva s, 
getMappedPage pd s va = Some phyVa ->  
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
getMappedPage pd s va = None ->   
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
assert(Heqidx : (StateLib.getIndexOfAddr va1 fstLevel) = (StateLib.getIndexOfAddr va2 fstLevel)).
apply checkVAddrsEqualityWOOffsetTrue'  with nbLevel nbL;trivial.
apply fstLevelLe.
apply getNbLevelLt;trivial.
rewrite Heqidx;trivial.
Qed.

Lemma checkVAddrsEqualityWOOffsetEqTrue  descChild nbL : 
StateLib.checkVAddrsEqualityWOOffset nbLevel descChild descChild nbL = true.
Proof.
revert nbL.
induction nbLevel;intros.
simpl;trivial.
simpl.
destruct (StateLib.Level.eqb nbL fstLevel).
symmetry.
apply beq_nat_refl.
destruct(StateLib.Level.pred nbL);trivial.
rewrite <- beq_nat_refl.
apply IHn;trivial.
Qed.
Lemma childIsMappedPage partition child s :
In partition (getPartitions multiplexer s) -> 
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
exists va;split;trivial.
apply AllVAddrAll.
Qed.

Lemma ancestorInPartitionTree s:
parentInPartitionList s -> 
isChild s -> 
forall partition ancestor ,
In partition (getPartitions multiplexer s) -> 
In ancestor (getAncestors partition s) -> 
In ancestor (getPartitions multiplexer s).
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
In child (getPartitions multiplexer s) ->
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
