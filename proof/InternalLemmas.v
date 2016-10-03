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
Require Import Isolation Consistency WeakestPreconditions List 
Core.Internal  Model.MAL StateLib Model.Hardware 
Model.ADT DependentTypeLemmas Model.Lib Invariants Lib.
Require Import Coq.Logic.ProofIrrelevance Omega.

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



Lemma physicalPageIsAccessible (currentPart : page) ptPDChild 
phyPDChild pdChild idxPDChild accessiblePDChild  nbL presentPDChild 
currentPD  s: 
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
intros Haccess Hpresentflag Hidx Hroot Hnbl
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
    apply CIndexEq.
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

Lemma getPartitionsNoDup s :
NoDup (getPartitions multiplexer s).
Proof.
(*
intros.
(* unfold prop1, prop2, prop3 in *.  *)
unfold getPartitions.
assert(Hmult : In multiplexer (getPartitions multiplexer s)).
{ unfold getPartitions;
  destruct nbPage;simpl; left; trivial. }
  revert Hmult.
  generalize multiplexer at 1 3.  
induction (nbPage + 1).
+ simpl in *. constructor.
+ simpl; intros.
(*  constructor.
  - rewrite in_flat_map.  
  unfold not; intros.
  destruct H3 as (partition & Hp1& Hp2).
  assert(Hances : In partition (getAncestors p s)) by admit.
  unfold prop4 in *. 
  unfold disjoint in *.
  unfold not in *.
  apply H2 with p partition p; trivial.
  unfold getConfigPages.  
  contradict Hp2.
  revert Hp1 Hmult.
  revert p partition.
  induction n.
  simpl.
  auto.
  intros.
  simpl.
  apply and_not_or.
  split.
  admit.
  rewrite in_flat_map.
  unfold not; intros.
  destruct H2 as (child & Hchildren & Hin).
  contradict Hin.
  apply IHn0; trivial.
  intros.
  admit.        
  
  
  unfold getChildren in *.
  apply nodup_In in Hp1.
  assert ( exists nbL, StateLib.getNbLevel = Some nbL) by admit.
  destruct H2 as (nbL & HnbLevel).
  rewrite HnbLevel in Hp1.
  assert(exists pd, StateLib.getPd p (memory s) = Some pd) by admit.
  destruct H2 as (pd & Hpd).
  rewrite Hpd in Hp1.
  unfold getMappedPagesAux in Hp1.
  apply filterOptionInIff in Hp1.
  unfold getMappedPagesOption in Hp1.
  apply in_map_iff in Hp1.
  destruct Hp1 as (va & Hmap & Hin).
  unfold getMappedPage in *.
  rewrite HnbLevel in Hmap.
  case_eq (getIndirection pd va nbL (nbLevel - 1) s ); intros;
  rewrite H2 in Hmap ; [| now contradict Hmap].
  case_eq(StateLib.readPresent p0 (StateLib.getIndexOfAddr va fstLevel) (memory s));
  intros; rewrite H3 in Hmap; [| now contradict Hmap].
  case_eq b; intros; subst; [| now contradict Hmap].
  clear H3.   
  destr
  SearchAbout nodup.
  assert(Hchildren : forall 
  
  
  
  admit.
  assert( Hchildren : forall child, In child (getChildren p s) ->
               In child (getPartitions multiplexer s)) by admit. 
  
  induction (getChildren p s).
  simpl. constructor.
  simpl.
  apply NoDupSplitInclIff; intuition.
  
  unfold disjoint.
  intros.
  apply IHn
  SearchAbout NoDup.
  contradict Hp2.
induction n. simpl.
auto.
simpl.   
apply Classical_Prop.and_not_or.
split.
simpl in *.
apply NoDup_cons_iff in IHn.
destruct IHn.
 induction (getChildren multiplexer s). simpl in *.
 now contradict Hp1.
 simpl in *.
 destruct Hp1.
 subst.
 apply IHl; trivial.
         rewrite in_app_iff in H2.
         apply Classical_Prop.not_or_and in  H2.
         destruct H2.
         trivial.
apply NoDupSplitIncl in H3.
intuition.
SearchAbout NoDup.
admit.
  rewrite in_flat_map.
  unfold not; intros.
destruct H2 as (partition & Hp1 & Hp2).
contradict Hp2.
SearchAbout not or.
simpl. *)
  *) 
(** TODO : To be proved *)
Admitted.
 

Lemma nbPartition s:
length (getPartitions multiplexer s) < (nbPage+1).
Proof.
rewrite NPeano.Nat.add_1_r.
apply le_lt_n_Sm.
apply lengthNoDupPartitions.
apply getPartitionsNoDup; admit.
(*
unfold getPartitions.
induction (nbPage + 1).
simpl. apply NoDup_nil.
simpl.
induction (getChildren multiplexer s).
simpl. constructor. auto. constructor.
simpl.
constructor.
 auto. trivial.
apply NoDup_cons.
destruct n. simpl in *. 
unfold getChildren.
unfold not.
intros.
apply in_flat_map in H.
destruct H as (x & H1 & H2).
now contradict H2. simpl in *.
unfold not.
intros.
 apply in_flat_map in H.
 destruct H as (x & H1 & H2).
 simpl in *.
 destruct H2.
 subst.
 unfold getChildren in H1.
 admit.
 admit.
 destruct n. simpl in *.
 induction (getChildren multiplexer s).
 simpl. trivial.
 simpl. assumption.
 simpl in *. 
 induction  (getChildren multiplexer s).
 simpl in *.
 constructor.
 simpl in *.
 constructor.
   trivial. 
  *)
 
Admitted.

Lemma childrenPartitionInPartitionList s phyVA parent: 
In parent (getPartitions multiplexer s ) ->
In phyVA (getChildren parent s) -> 
In phyVA (getPartitions multiplexer s).
Proof.
unfold getPartitions.
assert
(length (getPartitions multiplexer s) < (nbPage+1)) by apply nbPartition.
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

Lemma accessiblePageIsNotPartitionDescriptor
phyPDChild pdChild idxPDChild accessiblePDChild currentPart nbL presentPDChild 
currentPD ptPDChild s:
partitionsIsolation s ->  
kernelDataIsolation s -> 
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
intros Hiso Hanc Haccess Hpresentflag Hidx Hroot Hnbl
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
 
Lemma nextEntryIsPPgetPd partition pd s :
nextEntryIsPP partition PDidx pd s -> 
StateLib.getPd partition (memory s) = Some pd.
Proof.
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
nextEntryIsPP partition sh1idx sh1 s -> 
StateLib.getFstShadow partition (memory s) = Some sh1.
Proof.
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
nextEntryIsPP partition sh2idx sh2 s -> 
StateLib.getSndShadow partition (memory s) = Some sh2.
Proof.
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
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig.
rewrite in_app_iff in H0.
apply Classical_Prop.not_or_and in H0.
destruct H0.
unfold getIndirections in H0.

apply inGetIndirectionsAuxLt with nbLevel; auto.
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
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig.
rewrite in_app_iff in H0.
apply Classical_Prop.not_or_and in H0.
destruct H0.
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
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig.
rewrite in_app_iff in H0.
apply Classical_Prop.not_or_and in H0.
destruct H0.
unfold getIndirections in H0.
simpl in H1. 
apply Classical_Prop.not_or_and in H1.
destruct H1.
rewrite in_app_iff in H2.
apply Classical_Prop.not_or_and in H2.
destruct H2.
unfold getIndirections in H2.
apply inGetIndirectionsAuxLt with nbLevel; auto.
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
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig.
rewrite in_app_iff in H0.
apply Classical_Prop.not_or_and in H0.
destruct H0.
simpl in H1. 
apply Classical_Prop.not_or_and in H1.
destruct H1.
rewrite in_app_iff in H2.
apply Classical_Prop.not_or_and in H2.
destruct H2.
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
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig.
rewrite in_app_iff in H0.
apply Classical_Prop.not_or_and in H0.
destruct H0.
unfold getIndirections in H0.
simpl in H1. 
apply Classical_Prop.not_or_and in H1.
destruct H1.
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
destruct H5.
apply inGetIndirectionsAuxLt with nbLevel; auto.
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
apply Classical_Prop.not_or_and in Hconfig.
destruct Hconfig.
rewrite in_app_iff in H0.
apply Classical_Prop.not_or_and in H0.
destruct H0.
simpl in H1. 
apply Classical_Prop.not_or_and in H1.
destruct H1.
rewrite in_app_iff in H2.
apply Classical_Prop.not_or_and in H2.
destruct H2.
simpl in H3.
apply Classical_Prop.not_or_and in H3.
destruct H3.
rewrite in_app_iff in H4.
apply Classical_Prop.not_or_and in H4.
destruct H4.
unfold getIndirections in H4.
simpl in H5. 
apply Classical_Prop.not_or_and in H5.
destruct H5.
unfold getIndirections in H2.
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


Lemma mappedPageIsNotShadow1Table (table1 table2 currentPart currentPD currentShadow1: page)
 va idx1 (s : state): 
(forall partition : page,
          In partition (getPartitions multiplexer s) ->
          partition = table2 \/ In table2 (getConfigPagesAux partition s) -> False) ->
In currentPart (getPartitions multiplexer s) ->
partitionDescriptorEntry s -> 
nextEntryIsPP currentPart PDidx currentPD s -> 
StateLib.getIndexOfAddr va fstLevel = idx1 -> 
(forall idx : index,
         StateLib.getIndexOfAddr va fstLevel = idx ->
         isVE table1 idx s /\
         getTableAddrRoot table1 sh1idx currentPart va s) ->
nextEntryIsPP currentPart sh1idx currentShadow1 s -> 
(defaultPage =? table1) = false -> 
table2 <> table1.
Proof.
intros Hconfig Hcurpart Hpde Hpp Hidxref Hptref Hppref Hptrefnotnull.
unfold getConfigPagesAux. 
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
  assert (Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
  apply nextEntryIsPPgetPd; trivial.
  destruct Hroots as ((pd & Hpd & Hpdnotnull) 
  & (sh1 & Hsh1 & Hsh1notnull) & (sh2 & Hsh2 & Hsh2notnull) & 
  (sh3 & Hsh3 & Hsh3notnull)).
  rewrite Hcurpd, Hsh1, Hsh2, Hsh3.
  simpl.
  right.
  apply in_app_iff.
  right.
  simpl.
  right.
  apply in_app_iff.
  left.
  apply Hptref in Hidxref.
  destruct Hidxref as (Hperef & Htblrootref).
  unfold getTableAddrRoot in Htblrootref.
  destruct  Htblrootref as (_ & Htblrootref).
  generalize (Htblrootref currentShadow1  Hppref); clear Htblrootref; 
  intros Htblrootref.
  destruct Htblrootref as (nbL & HnbL & stop & Hstop & Hindref).
  apply getIndirectionInGetIndirections with va nbL stop; trivial.
  assert(0 < nbLevel) by apply nbLevelNotZero ; omega.
  assert(currentShadow1 = sh1).
  apply getSh1NextEntryIsPPEq with currentPart s; trivial.
  subst. assumption.
  apply beq_nat_false in Hptrefnotnull.
   unfold not; intros Hnot.
  subst. now contradict Hptrefnotnull.
  apply getNbLevelLe; trivial.  }
  unfold not; intros Hnot.
  subst; now contradict Hin.
Qed.

Lemma mappedPageIsNotPTable (table1 table2 currentPart currentPD : page)
 va idx1 (s : state): 
(forall partition : page,
          In partition (getPartitions multiplexer s) ->
          partition = table2 \/ In table2 (getConfigPagesAux partition s) -> False) ->
In currentPart (getPartitions multiplexer s) ->
partitionDescriptorEntry s -> 
nextEntryIsPP currentPart PDidx currentPD s -> 
StateLib.getIndexOfAddr va fstLevel = idx1 -> 
(forall idx : index,
        StateLib.getIndexOfAddr va fstLevel = idx ->
        isPE table1 idx s /\ 
        getTableAddrRoot table1 PDidx currentPart va s) ->
(defaultPage =? table1) = false -> 
table2 <> table1.
Proof.
intros Hconfig Hcurpart Hpde Hpp Hidxref Hptref Hptrefnotnull.
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
  assert (Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
  apply nextEntryIsPPgetPd; trivial.
  destruct Hroots as ((pd & Hpd & Hpdnotnull) 
  & (sh1 & Hsh1 & Hsh1notnull) & (sh2 & Hsh2 & Hsh2notnull) & 
  (sh3 & Hsh3 & Hsh3notnull)).
  rewrite Hcurpd, Hsh1, Hsh2, Hsh3.
  simpl.
  right.
  apply in_app_iff.
  left.
  apply Hptref in Hidxref.
  destruct Hidxref as (Hperef & Htblrootref).
  unfold getTableAddrRoot in Htblrootref.
  assert (Hppref : nextEntryIsPP currentPart PDidx currentPD s) by trivial.
  destruct  Htblrootref as (_ & Htblrootref).
  generalize (Htblrootref currentPD  Hppref); clear Htblrootref; 
  intros Htblrootref.
  destruct Htblrootref as (nbL & HnbL & stop & Hstop & Hindref).
  apply getIndirectionInGetIndirections with va nbL stop; trivial.
  assert(0 < nbLevel) by apply nbLevelNotZero ; omega.
  apply beq_nat_false in Hptrefnotnull.
  unfold not; intros Hnot.
  subst. now contradict Hptrefnotnull.
  apply getNbLevelLe; trivial.
  assert(currentPD = pd).
  apply getPdNextEntryIsPPEq with currentPart s; trivial.
  subst. assumption. }
  unfold not; intros Hnot.
  subst; now contradict Hin.
Qed.
