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
Require Import Model.ADT Model.Hardware Core.Services Isolation
Consistency Invariants WeakestPreconditions Model.Lib StateLib
Model.MAL UpdateShadow1Structure InternalLemmas DependentTypeLemmas Lib
WriteAccessible
  InitConfigPagesList InitPEntryTable DependentTypeLemmas  GetTableAddr
 WriteAccessibleRec UpdateMappedPageContent InternalLemmas 
UpdatePartitionDescriptor PropagatedProperties UpdateShadow1Structure .
 Require Import Omega Bool  Coq.Logic.ProofIrrelevance List.
 Import List.ListNotations.
 Require Import Coq.Sorting.Permutation.
Lemma readPDflagRightValue table idx entry s flag:
StateLib.readPDflag table idx
  (add table idx
     (VE {| pd := flag; va := va entry |}) (memory s) beqPage beqIndex) = Some flag.
Proof.
unfold StateLib.readPDflag.
simpl.
assert(beqPairs (table, idx) (table, idx) beqPage beqIndex = true).
apply beqPairsTrue;split;trivial.
rewrite H.
simpl;trivial.
Qed.



Lemma getPdsVAddrCheckChild partition descChild nbL s: 
true = checkChild partition nbL s descChild -> 
In descChild getAllVAddrWithOffset0 -> 
List.In descChild  (getPdsVAddr partition nbL getAllVAddrWithOffset0 s).
Proof.
intros.
unfold getPdsVAddr.
apply filter_In.
split;trivial.
symmetry;trivial.
Qed. 



Lemma addNewChild currentPart ptRefChild  phyDescChild ptRefChildFromSh1 
descChild entry level currentPD s  currentShadow1:
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
(forall idx : index,
      StateLib.getIndexOfAddr descChild fstLevel = idx ->
      isPE ptRefChild idx s /\
      getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
( forall idx : index,
      StateLib.getIndexOfAddr descChild fstLevel = idx ->
      isVE ptRefChildFromSh1 idx s /\
      getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s )->
      (defaultPage =? ptRefChildFromSh1) = false ->
In phyDescChild (getChildren currentPart {|
  currentPartition := currentPartition s;
  memory := add ptRefChildFromSh1
  (StateLib.getIndexOfAddr descChild fstLevel)
   (VE {| pd := true; va := va entry |})
              (memory s) beqPage beqIndex |}).
Proof.
intros Hlookup Hlevel Hpd Hroot.
intros Hptnotnull Hep Hpresent Hfstsh1 Hsh1 Hptsh1notnull.
unfold getChildren.
rewrite <- Hlevel.
simpl.
rewrite getPdAddDerivation with
 currentPart  (va entry) ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
  s entry true ;trivial.
rewrite nextEntryIsPPgetPd in *.
rewrite Hpd.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel descChild va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).
assert(HdescChild : In va1 (getPdsVAddr currentPart level getAllVAddrWithOffset0
        {|
        currentPartition := currentPartition s;
        memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                    (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |})).

{ unfold getPdsVAddr.
  apply filter_In.
  split;trivial.
  unfold checkChild.
  simpl. 
  rewrite getFstShadowAddDerivation with currentPart  (va entry) ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
  s entry true ;trivial.
  rewrite nextEntryIsPPgetFstShadow in *.
  rewrite Hfstsh1.
  rewrite getIndirectionAddDerivation with  currentShadow1 ptRefChildFromSh1
  (StateLib.getIndexOfAddr descChild fstLevel) (va entry) s entry va1 level (nbLevel - 1)
  true ;trivial.
 
  destruct Hsh1 with (StateLib.getIndexOfAddr descChild fstLevel) as (Hve & Hvee)  ;trivial.
  clear Hsh1.
  unfold getTableAddrRoot in Hvee.
 
  destruct Hvee as (_ & Hvee).
  rewrite <- nextEntryIsPPgetFstShadow in *.
  apply Hvee in Hfstsh1.
  clear Hvee.
  destruct Hfstsh1 as (nbL & HnbL & stop & Hstop & Hsh1root).
  assert(Hind : getIndirection currentShadow1 descChild level (nbLevel - 1) s  = Some
  ptRefChildFromSh1).
  subst.
    rewrite <- HnbL in Hlevel.
  inversion Hlevel.
  subst.
  apply getIndirectionStopLevelGT2 with (nbL + 1);trivial.
  omega.
  apply getNbLevelEq in HnbL.
  subst.
  apply nbLevelEq.
  assert(Haux : getIndirection currentShadow1 descChild level (nbLevel - 1) s  =
  getIndirection currentShadow1 va1 level (nbLevel - 1) s ).
  { apply getIndirectionEq;trivial. apply getNbLevelLt;symmetry;trivial.
     assert(StateLib.getNbLevel = Some (CLevel (nbLevel - 1))). 
    apply getNbLevelEqOption.
    rewrite <- Hlevel in *.
    inversion H;trivial. }
  rewrite <- Haux. 
  rewrite Hind.
  assert(Htmp : (ptRefChildFromSh1 =? defaultPage) = false).
  apply Nat.eqb_neq.
  unfold not;intros.
  apply beq_nat_false in Hptsh1notnull.
  subst.
  rewrite H in *.
  now contradict Hptsh1notnull.
  rewrite Htmp.
  assert(Haux1 : (StateLib.getIndexOfAddr descChild fstLevel) =
  (StateLib.getIndexOfAddr va1 fstLevel)).
  { apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level;trivial.
    rewrite <- Hva11.
    f_equal.
    assert(StateLib.getNbLevel = Some (CLevel (nbLevel - 1))). 
    apply getNbLevelEqOption.
    rewrite <- Hlevel in *.
    inversion H;trivial.
    apply fstLevelLe;trivial.
    apply getNbLevelLt;trivial.
    symmetry;trivial. }
  rewrite <- Haux1.  
  rewrite readPDflagRightValue;trivial. }
unfold getMappedPagesAux.
rewrite filterOptionInIff.
unfold getMappedPagesOption.
apply in_map_iff.

exists va1.
split;trivial.
rewrite getMappedPageAddDerivation with (va entry) ptRefChildFromSh1
(StateLib.getIndexOfAddr descChild fstLevel) s va1 currentPD
 entry true;trivial.
 assert(Haux2 :getMappedPage currentPD s descChild = SomePage phyDescChild ).
 apply getMappedPageGetTableRoot with ptRefChild currentPart;trivial.
 apply nextEntryIsPPgetPd;trivial.
rewrite <- Haux2.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.
Qed.

Lemma getMappedPagesOptionNil phyPDChild s:
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
filterOption (getMappedPagesOption phyPDChild getAllVAddrWithOffset0 s) = [] .
Proof.
intros Htrue.
unfold getMappedPagesOption.
induction getAllVAddrWithOffset0.
simpl;trivial.
simpl.
intros.
case_eq(getMappedPage phyPDChild s a);intros.
+ contradict H.
  unfold getMappedPage.
  case_eq(StateLib.getNbLevel);intros; [|
  unfold not;intros Hi;
  now contradict Hi]. 
  case_eq(getIndirection phyPDChild a l0 (nbLevel - 1) s  );
  intros;[|   unfold not;intros Hi;
  now contradict Hi].
    simpl in *.
 case_eq( defaultPage =? p0);intros.
 unfold not;intros Hi;
  now contradict Hi.
  clear IHl.
  revert phyPDChild p0 l0 H1 H0 Htrue H.
  destruct (nbLevel - 1).
  - simpl in *.
  intros.
  inversion H0;subst.
  destruct Htrue with (StateLib.getIndexOfAddr a fstLevel) as (Hphy & Hpresent).
  rewrite Hpresent.
   unfold not;intros Hi;
  now contradict Hi.
  - intros.
    simpl in H0.
    case_eq(StateLib.Level.eqb l0 fstLevel);intros.
    rewrite H2 in *.
    inversion H0;subst.
    destruct Htrue with (StateLib.getIndexOfAddr a fstLevel) as (Hphy & Hpresent).
    rewrite Hpresent.
    unfold not;intros Hi;
    now contradict Hi.
    rewrite H2 in *.
    destruct Htrue with (StateLib.getIndexOfAddr a l0) as (Hphy & Hpresent).
    rewrite Hphy in H0.
    assert((defaultPage =? defaultPage ) = true).
    apply NPeano.Nat.eqb_refl.
    rewrite H3 in H0.
    inversion H0.
    subst.
    apply beq_nat_false in H1.
    now contradict H1.
+ apply IHl.
+ apply IHl.
Qed.


Lemma partitionInPreviousState (phyDescChild ptRefChild currentShadow1 currentPD child2
currentPart : page) (s s' :state) (entry : Ventry) (descChild : vaddr)
(ptRefChildFromSh1 : page) :
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
noDupMappedPagesList s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
In currentPart (getPartitions multiplexer s)  ->
    nextEntryIsPP currentPart PDidx currentPD s ->
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\
getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s
->

nextEntryIsPP currentPart sh1idx currentShadow1 s ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isVE ptRefChildFromSh1 idx s /\
getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s )->
(defaultPage =? ptRefChildFromSh1) = false ->
In descChild getAllVAddrWithOffset0 -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) (memory s) beqPage beqIndex =
Some (VE entry) ->
s' =  {|
      currentPartition := currentPartition s;
      memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                  (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}  ->
phyDescChild <> child2 ->
In child2 (getChildren currentPart s') ->
In phyDescChild (getChildren currentPart s') ->
~ In phyDescChild (getChildren currentPart s) ->

In child2 (getChildren currentPart s).
Proof.
intros Hpde Hnoduppd Hnodupsh1 Hnotpart Hpresent Hpart Hpppd HgetA Hnotnull Hentry Hsh1 Hpp Hpp1
 Hnewprop.
intros.
unfold getChildren in *.
case_eq (StateLib.getNbLevel);
[intros nbL Hnbl | intros Hnbl];rewrite Hnbl in *;try now contradict H3.
subst.
simpl in *.
rewrite getPdAddDerivation with currentPart  (va entry) ptRefChildFromSh1
(StateLib.getIndexOfAddr descChild fstLevel)
s entry true in *;trivial.
set (s' :=  {|
    currentPartition := currentPartition s;
    memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}
                ) in *.
                rewrite nextEntryIsPPgetPd in *.
                rewrite Hpppd in *.
assert(Hi : exists va, getMappedPage currentPD s va = SomePage child2).
{ unfold getMappedPagesAux in H2.
rewrite filterOptionInIff in H2.
unfold  getMappedPagesOption in *.
apply in_map_iff in H2.
destruct H2 as (x & Hx & Hxx).
exists x.
rewrite <- Hx.
symmetry.
apply getMappedPageAddDerivation with entry;trivial.  
}
destruct Hi as (vachild & Hvachild).
unfold getMappedPagesAux.
rewrite filterOptionInIff.
unfold getMappedPagesOption.
apply in_map_iff.



  
   
   
unfold getMappedPagesAux in H2.
rewrite filterOptionInIff in H2.
unfold getMappedPagesOption in H2.
apply in_map_iff in H2.
destruct H2 as (vachild' & Hvachild' & Hpds).
assert(HgetMap :getMappedPage currentPD s' vachild' =
getMappedPage currentPD s vachild').
apply getMappedPageAddDerivation with entry;trivial.
rewrite HgetMap in *.
exists vachild';split;trivial.
assert(Hmapaux : getMappedPage currentPD s descChild = SomePage phyDescChild).
{ apply getMappedPageGetTableRoot with ptRefChild currentPart;trivial.
  apply nextEntryIsPPgetPd;trivial. }
assert(getMappedPage currentPD s descChild = SomePage phyDescChild /\
~ In descChild (getPdsVAddr currentPart nbL getAllVAddrWithOffset0 s)) as ( Hvaphy' & Hpds1).
{ split.
+ trivial.
+
unfold isPartitionFalse in *.
move Hnotpart at bottom.
unfold getPdsVAddr.
rewrite filter_In.
apply Classical_Prop.or_not_and.
right.
unfold checkChild. (**)
rewrite nextEntryIsPPgetFstShadow in *.
rewrite Hsh1.
assert(Hind : getIndirection currentShadow1 descChild nbL (nbLevel - 1) s = Some ptRefChildFromSh1).

apply getIndirectionGetTableRoot with currentPart;trivial.

rewrite Hind.
destruct  (ptRefChildFromSh1 =? defaultPage);trivial.
auto.

destruct Hnotpart as [Hnotpart | Hnotpart];rewrite Hnotpart;auto. }

assert(Hnewgoal : checkChild currentPart nbL s' descChild = true). 
 { unfold checkChild.

rewrite nextEntryIsPPgetFstShadow in *.

assert(Hsh1S : getFstShadow currentPart (memory s') =
getFstShadow currentPart (memory s)).
unfold s';simpl.
apply getFstShadowAddDerivation with entry;trivial.
rewrite Hsh1S.


rewrite Hsh1.
assert(getIndirection currentShadow1 descChild nbL (nbLevel - 1) s' =
getIndirection currentShadow1 descChild nbL (nbLevel - 1) s).
apply getIndirectionAddDerivation with entry;trivial.
rewrite H0;clear H0.
assert(     getIndirection currentShadow1 descChild nbL (nbLevel - 1) s =
Some ptRefChildFromSh1).
apply getIndirectionGetTableRoot with currentPart;trivial.
rewrite H0.
case_eq (   ptRefChildFromSh1 =? defaultPage);intros.
apply beq_nat_true in H2.
subst.
apply beq_nat_false in Hpp1.
rewrite H2 in *.
now contradict Hpp1.
unfold s';simpl.
rewrite readPDflagRightValue;trivial. }




assert(In descChild (getPdsVAddr currentPart nbL getAllVAddrWithOffset0 s')) .
{ unfold getPdsVAddr.
rewrite filter_In.
split;trivial.
 } 

unfold getPdsVAddr in *.
rewrite filter_In in *.
apply Classical_Prop.not_and_or in Hpds1.
destruct Hpds.
split;trivial.     
assert(Hshad :getFstShadow currentPart (memory s) =
getFstShadow currentPart (memory s')).
symmetry.
apply getFstShadowAddDerivation with entry;trivial.

unfold checkChild in *.

rewrite <- Hshad in *.
rewrite nextEntryIsPPgetFstShadow in *.
rewrite Hsh1 in *.

destruct Hpp with ( StateLib.getIndexOfAddr descChild fstLevel);
trivial.

clear Hpp.
assert(getIndirection currentShadow1 descChild nbL (nbLevel - 1) s'
= getIndirection currentShadow1 descChild nbL (nbLevel - 1) s).
apply getIndirectionAddDerivation with entry;trivial.
rewrite <- H8 in *.
assert(getIndirection currentShadow1 descChild nbL (nbLevel - 1) s =
Some ptRefChildFromSh1).
{
unfold getTableAddrRoot in *.
destruct H7 as (_ & Hget).
rewrite <- nextEntryIsPPgetFstShadow in *.
apply  Hget in   Hsh1. clear Hget.
destruct Hsh1 as (l & HnbL & stop & Hstop & Hget).

subst.
rewrite <-  HnbL in *.
inversion Hnbl.
subst.
apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
omega.
apply getNbLevelEq in HnbL.
subst.
apply nbLevelEq. }

rewrite H9 in *.
rewrite H8 in *.
(* assert(Hindaux' : getIndirection currentShadow1 descChild1 nbL (nbLevel - 1) s' =
getIndirection currentShadow1 descChild nbL (nbLevel - 1) s' ).
{ symmetry.
  apply getIndirectionEq;trivial.
  apply getNbLevelLt;trivial.
  rewrite <- HdescChild11.
  f_equal.
  assert(Htmp : StateLib.getNbLevel = Some (CLevel (nbLevel - 1))). 
  apply getNbLevelEqOption. 
  rewrite  Hnbl in *.
  inversion Htmp;trivial. }
  
rewrite Hindaux' in *.
rewrite H8 in *.  *)

case_eq (ptRefChildFromSh1 =? defaultPage);intros H14; rewrite H14 in *.
now contradict H8.
 
assert(getIndirection currentShadow1 vachild' nbL (nbLevel - 1) s'
= getIndirection currentShadow1 vachild' nbL (nbLevel - 1) s).
apply getIndirectionAddDerivation with entry;trivial. 

  
rewrite H10 in *. 
case_eq (getIndirection currentShadow1 vachild' nbL (nbLevel - 1) s);
[intros tbl1 Hind1 | intros Hind1];rewrite Hind1 in *;try now contradict H4.
case_eq (tbl1 =? defaultPage);intros;
rewrite H11 in *.
intuition.
 assert (vachild' <> descChild).
unfold not;intros; subst.
rewrite  Hvachild' in Hmapaux.
inversion Hmapaux.
subst.

now contradict H1.
 
assert(Hvas : checkVAddrsEqualityWOOffset nbLevel vachild' descChild nbL = true \/
checkVAddrsEqualityWOOffset nbLevel vachild' descChild nbL = false).
{ destruct (checkVAddrsEqualityWOOffset nbLevel vachild' descChild nbL);intuition. }
destruct Hvas as  [Hvaseq | Hvasnoteq];subst.
- assert(Hvasx : checkVAddrsEqualityWOOffset nbLevel vachild' descChild nbL = true) by trivial.
apply getIndirectionEq with nbL vachild' descChild currentPD (nbLevel -1) s in Hvaseq.
unfold getMappedPage in Hvachild'.
rewrite Hnbl in *.

unfold getMappedPage in Hvaphy'.
rewrite Hnbl in *.
rewrite Hvaseq in *.
clear H4 H3.
case_eq(getIndirection currentPD descChild nbL (nbLevel - 1) s);
[intros pt Hpt | intros Hpt]; rewrite Hpt in *;try now contradict Hvachild.
destruct (defaultPage =? pt);try now contradict Hvachild.
destruct(StateLib.readPresent pt (StateLib.getIndexOfAddr vachild' fstLevel) (memory s));
try now contradict Hvachild.
destruct (StateLib.readPresent pt (StateLib.getIndexOfAddr descChild fstLevel) (memory s));
try now contradict Hvaphy'.
destruct b;destruct b0; try now contradict Hvaphy' ; try now contradict Hvachild.
assert((StateLib.getIndexOfAddr vachild' fstLevel) <>
(StateLib.getIndexOfAddr descChild fstLevel)).

unfold not;intros;subst.
rewrite H3 in *.
rewrite Hvaphy' in Hvachild'.
inversion Hvachild'.
subst.
now contradict H1.
assert(   StateLib.readPDflag tbl1 (StateLib.getIndexOfAddr vachild' fstLevel) (memory s)  =
StateLib.readPDflag tbl1 (StateLib.getIndexOfAddr vachild' fstLevel) (memory s')).
unfold s';simpl.
symmetry.
apply readPDflagAddDerivation.
right;trivial.
rewrite H4;trivial.
symmetry in Hnbl.
apply getNbLevelEq in Hnbl.
subst.
unfold CLevel.
assert(0<nbLevel) by apply nbLevelNotZero.

case_eq (lt_dec (nbLevel - 1) nbLevel);intros;
simpl;
omega.

- assert(currentShadow1 <> defaultPage).
{ unfold partitionDescriptorEntry in *.
assert(exists entry : page, nextEntryIsPP currentPart sh1idx entry s /\ entry <> defaultPage).
apply Hpde;trivial.
right;left;trivial.
destruct H13 as (ii & Hii & Hiii).
assert(ii = currentShadow1).
apply getSh1NextEntryIsPPEq with currentPart s;trivial.
subst;trivial. }
assert(tbl1 <> ptRefChildFromSh1 \/ (StateLib.getIndexOfAddr vachild' fstLevel)  <>
(StateLib.getIndexOfAddr descChild fstLevel)).
{ apply pageTablesOrIndicesAreDifferent
with currentShadow1 currentShadow1 nbL nbLevel s;trivial.
(** NoDup (getIndirections currentShadow1 s) **)
apply noDupConfigPagesListNoDupGetIndirections with currentPart sh1idx;trivial.
unfold noDupConfigPagesList in *.
apply Hnoduppd ;trivial.
right;left;trivial.
apply nextEntryIsPPgetFstShadow;trivial.
(** NoDup (getIndirections currentShadow1 s) **)
apply noDupConfigPagesListNoDupGetIndirections with currentPart sh1idx;trivial.
unfold noDupConfigPagesList in *.
apply Hnoduppd ;trivial.
right;left;trivial.
apply nextEntryIsPPgetFstShadow;trivial.
left;split;trivial.
symmetry in Hnbl.
apply getNbLevelEq in Hnbl.
subst.

trivial.
apply beq_nat_false in H11.
unfold not;intros;subst;now contradict H11.
apply beq_nat_false in Hpp1.
unfold not;intros;subst;now contradict Hpp1.
apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
symmetry in Hnbl.
apply getNbLevelEq in Hnbl.
subst.
unfold CLevel.
assert(0<nbLevel) by apply nbLevelNotZero.

case_eq (lt_dec (nbLevel - 1) nbLevel);intros;
simpl;
omega.
symmetry in Hnbl.

apply getNbLevelEq in Hnbl.
subst.
apply nbLevelEq.

apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
symmetry in Hnbl.
apply getNbLevelEq in Hnbl.
subst.
unfold CLevel.
assert(0<nbLevel) by apply nbLevelNotZero.

case_eq (lt_dec (nbLevel - 1) nbLevel);intros;
simpl;
omega.
symmetry in Hnbl.

apply getNbLevelEq in Hnbl.
subst.
apply nbLevelEq. }


assert(   StateLib.readPDflag tbl1 (StateLib.getIndexOfAddr vachild' fstLevel) (memory s)  =
StateLib.readPDflag tbl1 (StateLib.getIndexOfAddr vachild' fstLevel) (memory s')).
unfold s';simpl.
symmetry.
apply readPDflagAddDerivation.
trivial.
rewrite H16;trivial.

Qed.
 
 Lemma notInPreviousMappedPages s' nbL phyVa a s entry idx table pd partition l:
noDupMappedPagesList s ->
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
s' = {|
currentPartition := currentPartition s;
memory := add table idx (VE {| pd := true; va := va entry |})
      (memory s) beqPage beqIndex |} ->
      StateLib.getNbLevel = Some nbL  ->
       In partition (getPartitions multiplexer s) ->
       StateLib.getPd partition (memory s) = Some pd ->
~ In phyVa (getMappedPagesAux pd (filter (checkChild partition nbL s) l) s) ->
getMappedPage pd s a = SomePage phyVa ->
checkChild partition nbL s' a = checkChild partition nbL s a ->
~ In phyVa (getMappedPagesAux pd (filter (checkChild partition nbL s') l) s').
Proof.
intros  Hnodumap Hlookup Hs HnbL.

revert l phyVa a  pd partition .
induction l.
simpl. auto.
simpl;intros.
subst.
set(s':= {|
   currentPartition := currentPartition s;
   memory := add table idx (VE {| pd := true; va := va entry |})
               (memory s) beqPage beqIndex |}) in *.
assert(Ha : getMappedPage pd s a = NonePage \/ 
getMappedPage pd s a = SomeDefault \/ 
(exists phy , getMappedPage pd s a = SomePage phy)).
{ destruct (getMappedPage pd s a). 
  do 2 right;exists p;trivial.
  right;left;trivial.
  left;trivial.  }
assert(H5 :getMappedPage pd s a = getMappedPage pd s' a). 
symmetry.
apply getMappedPageAddDerivation with entry;trivial.
case_eq(checkChild partition nbL s' a);intros;
case_eq(checkChild partition nbL s a);intros;
rewrite H6 in *.
+          

destruct Ha as [H7 | [H7 | H7]].



{ rewrite getMappedPagesAuxConsNone ; [ | rewrite H5 in *;trivial].

rewrite getMappedPagesAuxConsNone in *;trivial.
apply IHl with a0 ;trivial.  }

{ rewrite getMappedPagesAuxConsDefault ; [ | rewrite H5 in *;trivial].

rewrite getMappedPagesAuxConsDefault in *;trivial.
apply IHl with a0 ;trivial.  }
{ destruct H7 as (phy & H7).
rewrite getMappedPagesAuxConsSome with pd a phy
(filter (checkChild partition nbL s') l) s';[ | rewrite H5 in *;trivial].

rewrite getMappedPagesAuxConsSome with pd a phy
(filter (checkChild partition nbL s) l) s in *; trivial.
simpl in *.
apply Classical_Prop.not_or_and in H1.
destruct H1.
apply  Classical_Prop.and_not_or .
split;trivial.
apply IHl with a0;trivial. }
+ destruct Ha as [H7 | [H7 | H7]].
{ rewrite getMappedPagesAuxConsNone ; [ | rewrite H5 in *;trivial].
apply IHl with a0;trivial. }
{ rewrite getMappedPagesAuxConsDefault ; [ | rewrite H5 in *;trivial].
apply IHl with a0;trivial. }
{ destruct H7 as (phy & H7).
rewrite getMappedPagesAuxConsSome with pd a phy
(filter (checkChild partition nbL s') l) s';[ | rewrite H5 in *;trivial].

simpl in *.
apply  Classical_Prop.and_not_or .
split;trivial.
(* assert(Hor:a=a0 \/ a <> a0). *)
assert(Hor : checkVAddrsEqualityWOOffset nbLevel a a0 nbL = true \/ 
checkVAddrsEqualityWOOffset nbLevel a a0 nbL = false).
{ destruct (checkVAddrsEqualityWOOffset nbLevel a a0 nbL).
  left;trivial.
  right;trivial.
(* destruct a0.
  assert (va = va0 \/ va <> va0).
  clear.
  tauto.
  destruct H8.
  subst.
  left;trivial.
  f_equal.
  apply proof_irrelevance.
  right.
  unfold not;intros.
  inversion H9.
  subst.
  now contradict H8. *) }
destruct Hor as [Hor | Hor].
subst.
assert(Haux1 :checkChild partition nbL s' a = checkChild partition nbL s' a0).
apply checkChildEq;trivial.
assert(Haux2 :checkChild partition nbL s a = checkChild partition nbL s a0).
apply checkChildEq;trivial.
rewrite Haux1 in *.
rewrite Haux2 in *.
rewrite H3 in *.
rewrite H6 in H4.
now contradict H4.

apply twoMappedPagesAreDifferent with a a0 pd nbL s;trivial.
unfold noDupMappedPagesList in *.
apply Hnodumap in H.
unfold getMappedPages in H.
rewrite H0 in *.
unfold getMappedPagesAux in *.
unfold getMappedPagesOption in *.
assumption.
apply IHl with a0;trivial. }
+ destruct Ha as [H7 | [H7 | H7]].
{ rewrite getMappedPagesAuxConsNone in *; [ | rewrite H5 in *;trivial].
apply IHl with a0;trivial. }
{ rewrite getMappedPagesAuxConsDefault in *; [ | rewrite H5 in *;trivial].
apply IHl with a0;trivial. }
{ destruct H7 as (phy & H7).
rewrite getMappedPagesAuxConsSome with pd a phy
(filter (checkChild partition nbL s) l) s in *;[ | rewrite H5 in *;trivial].
simpl in *.
apply Classical_Prop.not_or_and in H1.
destruct H1.
apply IHl with a0;trivial. }
+apply IHl with a0;trivial.
Qed.


Lemma getChildrenSplitList (newPartition ptRefChild currentShadow1 currentPD 
currentPart : page) (s :state) (entry : Ventry) (descChild : vaddr)
(ptRefChildFromSh1 : page) :
let s' := {|
   currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) (VE {| pd := true; va := va entry |})
               (memory s) beqPage beqIndex |} in
partitionDescriptorEntry s ->
noDupMappedPagesList s -> 
noDupConfigPagesList s ->
In currentPart (getPartitions multiplexer s) -> 
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
    nextEntryIsPP currentPart PDidx currentPD s ->
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\
getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) newPartition s
->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isVE ptRefChildFromSh1 idx s /\
getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s )->
(defaultPage =? ptRefChildFromSh1) = false ->
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) (memory s) beqPage beqIndex =
Some (VE entry) ->
~ In newPartition (getChildren currentPart s) ->
In newPartition (getChildren currentPart s') ->
In descChild getAllVAddrWithOffset0 -> 
exists l1 l2,
getChildren currentPart s' = l1 ++ [newPartition] ++ l2 /\
getChildren currentPart s = l1 ++l2.
Proof.
intros s' Hpde Hnodupmap Hnodupconfig Hpart  Hnotpart Hpresent (* Hpart *) Hpppd HgetA Hnotnull Hentry Hsh1 Hpp Hpp1  Hlookup.
intros Hnotin Hin Hnewhyp. 
unfold getChildren in *.
case_eq (StateLib.getNbLevel );  [ intros nbL  HnbL | intros HnbL ;rewrite HnbL in *; tauto]  .
simpl in *.
rewrite HnbL in *.
assert(HgetPd :   StateLib.getPd currentPart
      (add  ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
      (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex) =
      StateLib.getPd currentPart (memory s)).
apply getPdAddDerivation with entry;trivial.
rewrite HgetPd in *;clear HgetPd.
case_eq (StateLib.getPd currentPart (memory s) );  
[ intros pd Hpd | intros Hpd ; rewrite Hpd in *;tauto]  .
rewrite Hpd in *.
assert(getMappedPage currentPD s descChild = SomePage newPartition /\
~ In descChild (getPdsVAddr currentPart nbL getAllVAddrWithOffset0 s)) as ( Hvaphy' & Hpds1).
{ split.
  + apply getMappedPageGetTableRoot with ptRefChild currentPart;trivial.
  + unfold isPartitionFalse in *.
    move Hnotpart at bottom.
    unfold getPdsVAddr.
    rewrite filter_In.
    apply Classical_Prop.or_not_and.
    right.
    unfold checkChild.
    rewrite nextEntryIsPPgetFstShadow in *.
    rewrite Hsh1.
    assert(Hind : getIndirection currentShadow1 descChild nbL (nbLevel - 1) s = Some ptRefChildFromSh1).
    apply getIndirectionGetTableRoot with currentPart;trivial.
    rewrite Hind.
    destruct  (ptRefChildFromSh1 =? defaultPage);trivial.
    auto.
    destruct Hnotpart as [Hnotpart | Hnotpart];rewrite Hnotpart;auto. }
assert(In descChild (getPdsVAddr currentPart nbL getAllVAddrWithOffset0 s')).
{ unfold getPdsVAddr.
  rewrite filter_In;trivial.
  unfold checkChild.
  rewrite nextEntryIsPPgetFstShadow in *.
  assert(Hsh1S : getFstShadow currentPart (memory s') =
  getFstShadow currentPart (memory s)).
  unfold s';simpl.
  apply getFstShadowAddDerivation with entry;trivial.
  rewrite Hsh1S.
  rewrite Hsh1.
  assert(Hind : getIndirection currentShadow1 descChild nbL (nbLevel - 1) s' =
  getIndirection currentShadow1 descChild nbL (nbLevel - 1) s).
  apply getIndirectionAddDerivation with entry;trivial.
  rewrite Hind;clear Hind.
  assert(  Hind :   getIndirection currentShadow1 descChild nbL (nbLevel - 1) s =
  Some ptRefChildFromSh1).
  apply getIndirectionGetTableRoot with currentPart;trivial.
  rewrite Hind.
  case_eq ( ptRefChildFromSh1 =? defaultPage);intros Htrue.
  apply beq_nat_true in Htrue.
  subst.
  apply beq_nat_false in Hpp1.
  rewrite Htrue in *.
  now contradict Hpp1.
  unfold s';simpl.
  rewrite readPDflagRightValue;trivial.
  split;trivial. }
unfold getPdsVAddr in *.
rewrite filter_In in *.
destruct H as (Hvapart & Hcheck).
apply Classical_Prop.not_and_or in Hpds1.
assert(  In descChild getAllVAddr).
apply AllVAddrAll.
destruct Hpds1. tauto.
clear H.
assert(Hnodupva : NoDup getAllVAddrWithOffset0).
{ unfold getAllVAddrWithOffset0.
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
apply IHl;intuition. }

assert(HnewHyp1 : checkOffset0 descChild = true).
{ unfold getAllVAddrWithOffset0 in *. 
  apply filter_In in Hvapart.
  intuition. }
unfold getAllVAddrWithOffset0 in *. 
induction getAllVAddr; try tauto.
simpl in Hvapart.
simpl in *. 
 case_eq(checkOffset0 a);intros Hax;rewrite Hax in *.
destruct Hvapart as [Hvapart | Hvapart].
+ subst;simpl.
  rewrite Hcheck.
  apply not_true_is_false in H0.
  rewrite H0.
  assert(currentPD = pd).
  apply getPdNextEntryIsPPEq with currentPart s;trivial.
  subst.
  assert(HmapS : getMappedPage pd s' descChild = SomePage newPartition).
  rewrite <- Hvaphy'.
  apply getMappedPageAddDerivation with entry;trivial. 
  rewrite getMappedPagesAuxConsSome with 
  pd descChild newPartition (filter (checkChild currentPart nbL s')  (filter checkOffset0 l))
  s';trivial.
   (* 
  do 2 eexists. *)  
  exists [].
  exists (getMappedPagesAux pd (filter (checkChild currentPart nbL s)  (filter checkOffset0 l)) s).
  simpl.
  split;f_equal.
  apply NoDup_cons_iff in Hnodupva.
  destruct   Hnodupva.
  clear IHl.

  clear Hnotin Hin Hnewhyp.
  
  induction l.
  simpl; try tauto.
  simpl in *.
  case_eq(checkOffset0 a);intros Hxa;rewrite Hxa in *. 
  assert(Ha : getMappedPage pd s a = NonePage \/ 
  getMappedPage pd s a = SomeDefault \/ (exists phy , getMappedPage pd s a = SomePage phy)).
{ destruct (getMappedPage pd s a). 
  do 2 right;exists p;trivial.
  right;left;trivial.
  left;trivial.  }
  assert(Hmapeq :getMappedPage pd s' a = getMappedPage pd s a).
 {  apply getMappedPageAddDerivation with entry;trivial. }
  simpl in H.
  apply Classical_Prop.not_or_and in H as (Hnot1 & Hnot2);trivial.
  apply NoDup_cons_iff in H1 as (Hdup1 & Hdup2);trivial.
  simpl in *. 
  case_eq(checkChild currentPart nbL s a);intros Hii. 
  - case_eq(checkChild currentPart nbL s' a);intros Hi.
    * destruct Ha as [Ha | [Ha | Ha]].
      { rewrite getMappedPagesAuxConsNone ; [ | rewrite Hmapeq in *;trivial].
        rewrite getMappedPagesAuxConsNone in *;trivial.
        apply IHl ;trivial. }
        { rewrite getMappedPagesAuxConsDefault ; [ | rewrite Hmapeq in *;trivial].
        rewrite getMappedPagesAuxConsDefault in *;trivial.
        apply IHl ;trivial. }
      { destruct Ha as (phy & Ha).
        rewrite getMappedPagesAuxConsSome with pd a phy
        (filter (checkChild currentPart nbL s')  (filter checkOffset0 l)) s';[ | rewrite Hmapeq in *;trivial].
        rewrite getMappedPagesAuxConsSome with pd a phy
        (filter (checkChild currentPart nbL s) (filter checkOffset0 l)) s in *; trivial.
        f_equal.
        apply IHl ;trivial. }
    * destruct Ha as [Ha | [Ha | Ha]].
      { rewrite getMappedPagesAuxConsNone ; [ | trivial].
        apply IHl ;trivial. }
       { rewrite getMappedPagesAuxConsDefault ; [ | trivial].
        apply IHl ;trivial. }
      { destruct Ha as (phy & Ha).
      assert (checkChild currentPart nbL s' a = true).
      { unfold checkChild in *.
        assert(Hsh1S : StateLib.getFstShadow currentPart (memory s') =
                StateLib.getFstShadow currentPart (memory s))by (
          apply getFstShadowAddDerivation with entry;trivial). 
        rewrite Hsh1S in *. clear Hsh1S.
        destruct (StateLib.getFstShadow currentPart (memory s));
        try now contradict H0.
        assert(Hind :  getIndirection p a nbL (nbLevel - 1) s' =
           getIndirection p a nbL (nbLevel - 1) s) by (
           apply getIndirectionAddDerivation with entry;trivial). 
        rewrite Hind in *; clear Hind.
        case_eq ( getIndirection p a nbL (nbLevel - 1) s);
         [intros ind Hind1 |intros Hind1]; 
        rewrite Hind1 in *;try now contradict Hii.
        destruct (ind =? defaultPage);
        try now contradict H0.
        unfold s' in *.
        simpl in *.
        unfold StateLib.readPDflag in *.
        cbn in *.
        case_eq( beqPairs (ptRefChildFromSh1, StateLib.getIndexOfAddr descChild fstLevel)
         (ind, StateLib.getIndexOfAddr a fstLevel) beqPage beqIndex);
        intros Hpairs ;rewrite Hpairs in *.
        simpl;trivial.
        apply beqPairsFalse in Hpairs.
        assert(lookup ind (StateLib.getIndexOfAddr a fstLevel)
         (removeDup  ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) 
         (memory s) beqPage beqIndex) beqPage beqIndex =
        lookup ind (StateLib.getIndexOfAddr a fstLevel) (memory s) beqPage beqIndex).        
        apply removeDupIdentity;intuition.        
        rewrite H in *. clear H.
        case_eq (lookup ind (StateLib.getIndexOfAddr a fstLevel) (memory s) beqPage beqIndex)
        ; [ intros v Hv | intros Hv]; rewrite Hv in *; try now contradict Hi.
        trivial. }
        rewrite H in *.
        now contradict Hi. }
  - case_eq (checkChild currentPart nbL s' a); intros Hk.
    * simpl in *.
      destruct Ha as [Ha | [Ha|Ha]].
      ++  rewrite <- Hmapeq in *;clear Hmapeq.
          rewrite getMappedPagesAuxConsNone;trivial.
          apply IHl;trivial.
     ++    rewrite <- Hmapeq in *;clear Hmapeq.
          rewrite getMappedPagesAuxConsDefault;trivial.
          apply IHl;trivial.
      ++ destruct Ha as (phyVa & Hphy).
          (* assert(newPartition <> phyVa).
          { apply 
          twoMappedPagesAreDifferent with  descChild a pd nbL s;
          trivial.
          unfold noDupMappedPagesList in *.
          apply Hnodupmap in Hpart.
          unfold getMappedPages in *.
          rewrite Hpd in *.
          unfold getMappedPagesAux in *;tauto.
          unfold not;intros;subst;tauto. } *)
          assert( Hor :
                        StateLib.checkVAddrsEqualityWOOffset nbLevel a descChild nbL = false). 
         
           apply checkVAddrsEqualityWOOffsetFalseEqOffset;trivial.  
         assert(checkChild currentPart nbL s' a = false).
         { clear IHl.
          unfold checkChild in *.
           assert(Hsh1S : StateLib.getFstShadow currentPart (memory s') =
                StateLib.getFstShadow currentPart (memory s))by (
          apply getFstShadowAddDerivation with entry;trivial). 
        rewrite Hsh1S in *. clear Hsh1S.
        rewrite nextEntryIsPPgetFstShadow in *.
        rewrite Hsh1 in *. 

        assert(Hind :  getIndirection currentShadow1 a nbL (nbLevel - 1) s' =
           getIndirection currentShadow1 a nbL (nbLevel - 1) s) by (
           apply getIndirectionAddDerivation with entry;trivial). 
        rewrite Hind in *; clear Hind.
        case_eq ( getIndirection currentShadow1 a nbL (nbLevel - 1) s);
         [intros ind Hind1 |intros Hind1]; 
        rewrite Hind1 in *;try now contradict Hii.
        case_eq (ind =? defaultPage);intros Hindnotnil;
        try now contradict H0;trivial.
        trivial.
        assert(Hind :  getIndirection currentShadow1 descChild nbL (nbLevel - 1) s' =
           getIndirection currentShadow1 descChild nbL (nbLevel - 1) s) by (
           apply getIndirectionAddDerivation with entry;trivial). 
        rewrite Hind in *; clear Hind.
        case_eq ( getIndirection currentShadow1 descChild nbL (nbLevel - 1) s);
         [intros ind2 Hind2 |intros Hind2]; 
        rewrite Hind2 in *;try now contradict Hcheck.
        destruct (ind2 =? defaultPage);
        try now contradict H0.
        assert(Some ind2 = Some ptRefChildFromSh1).
        { destruct Hpp with  (StateLib.getIndexOfAddr descChild fstLevel)
          as (Hve & Hroot) ;trivial.
          unfold getTableAddrRoot in Hroot.
          destruct Hroot as (_ & Hroot).
          rewrite <- nextEntryIsPPgetFstShadow in *.
          apply Hroot in Hsh1.
          clear Hroot.
          move Hsh1 at bottom.
          destruct Hsh1 as (ll & Hll & stop & Hstop& Hroot).
          subst.
          rewrite <- Hll in *.
          inversion HnbL;subst.         
          assert(getIndirection currentShadow1 descChild nbL (nbLevel - 1) s = 
          Some ptRefChildFromSh1 ).
          apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
          omega.
          apply getNbLevelEq in Hll.
          subst.
          apply nbLevelEq.
          rewrite <- Hind2.
(*           rewrite <- H1. *)
          trivial.  }
        inversion H;subst.
        clear H.
        assert(currentShadow1 <> defaultPage).
        { unfold partitionDescriptorEntry in *.
          assert(Hexist : exists entry : page, nextEntryIsPP currentPart sh1idx entry s /\ entry <> defaultPage).
          apply Hpde;trivial.
          right;left;trivial.
          destruct Hexist as (ii & Hi1 & Hi2).
          assert(ii = currentShadow1).
          apply getSh1NextEntryIsPPEq with currentPart s;trivial.
          subst;trivial. }
        assert(ind <> ptRefChildFromSh1 \/ 
         (StateLib.getIndexOfAddr a fstLevel) <> 
         (StateLib.getIndexOfAddr descChild fstLevel)).
        { apply pageTablesOrIndicesAreDifferent with currentShadow1 
          currentShadow1 nbL  nbLevel s;trivial.
          apply noDupConfigPagesListNoDupGetIndirections with currentPart sh1idx;trivial.
          unfold noDupConfigPagesList in *.
          apply Hnodupconfig ;trivial.
          right;left;trivial.
          apply nextEntryIsPPgetFstShadow;trivial.
          apply noDupConfigPagesListNoDupGetIndirections with currentPart sh1idx;trivial.
          unfold noDupConfigPagesList in *.
          apply Hnodupconfig ;trivial.
          right;left;trivial.
          apply nextEntryIsPPgetFstShadow;trivial.
          left;split;trivial.
          symmetry in HnbL.
          apply getNbLevelEq in HnbL.
          subst;trivial.
          apply beq_nat_false in Hindnotnil;trivial.
          unfold not;intros;subst.
          now contradict Hindnotnil.
          apply beq_nat_false in Hpp1.
          unfold not;intros;subst;now contradict Hpp1.
          apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
          symmetry in HnbL.
          apply getNbLevelEq in HnbL.
          subst.
          unfold CLevel.
          assert(0<nbLevel) by apply nbLevelNotZero.
          case_eq (lt_dec (nbLevel - 1) nbLevel);intros;
          simpl;
          omega.
          symmetry in HnbL.
          apply getNbLevelEq in HnbL.
          subst.
          apply nbLevelEq.
          apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
          symmetry in HnbL.
          apply getNbLevelEq in HnbL.
          subst.
          unfold CLevel.
          assert(0<nbLevel) by apply nbLevelNotZero.
          case_eq (lt_dec (nbLevel - 1) nbLevel);intros;
          simpl;
          omega.
          symmetry in HnbL.
          apply getNbLevelEq in HnbL.
          subst.
          apply nbLevelEq. }
        rewrite Hindnotnil in *. 
        assert(Heq : StateLib.readPDflag ind (StateLib.getIndexOfAddr a fstLevel) (memory s) 
            =   StateLib.readPDflag ind (StateLib.getIndexOfAddr a fstLevel) (memory s')).
         { unfold s'.
          simpl.
          symmetry.
          apply readPDflagAddDerivation;trivial.
         }
          rewrite Heq in *.
          trivial. }
          rewrite H in *.
          now contradict Hk. 
    * apply IHl;trivial.
    - apply IHl;trivial.
  + simpl.
    assert(currentPD = pd).
    apply getPdNextEntryIsPPEq with currentPart s;trivial.
    subst.
    assert(Hnotchild : a <> descChild).
    { apply NoDup_cons_iff in Hnodupva.
      destruct Hnodupva as (Hnodup1 & Hnodup2).
      unfold not;intros;subst.
      contradiction. }  
    assert(Hmapeq :getMappedPage pd s' a = getMappedPage pd s a).
    apply getMappedPageAddDerivation with entry;trivial.
    case_eq(checkChild currentPart nbL s a);intros Hii. 
  - case_eq(checkChild currentPart nbL s' a);intros Hi.
    *   assert(Ha : getMappedPage pd s a = NonePage \/ 
  getMappedPage pd s a = SomeDefault \/ (exists phy , getMappedPage pd s a = SomePage phy)).
  { destruct (getMappedPage pd s a). 
  do 2 right;exists p;trivial.
  right;left;trivial.
  left;trivial.  }
        destruct Ha as [Ha | [Ha|Ha]].
      ++ rewrite getMappedPagesAuxConsNone ; [ | rewrite Hmapeq in *;trivial].
        rewrite getMappedPagesAuxConsNone in *;trivial.
        apply IHl ;trivial.
        simpl in Hnotin.
        rewrite Hii in *.
        rewrite getMappedPagesAuxConsNone in *;trivial.
        simpl in Hin.
        rewrite Hi in *.
        rewrite getMappedPagesAuxConsNone in *;trivial.
        rewrite Hmapeq in *;trivial.
        apply NoDup_cons_iff in Hnodupva.
        intuition.
      ++ rewrite getMappedPagesAuxConsDefault ; [ | rewrite Hmapeq in *;trivial].
        rewrite getMappedPagesAuxConsDefault in *;trivial.
        apply IHl ;trivial.
        simpl in Hnotin.
        rewrite Hii in *.
        rewrite getMappedPagesAuxConsDefault in *;trivial.
        simpl in Hin.
        rewrite Hi in *.
        rewrite getMappedPagesAuxConsDefault in *;trivial.
        rewrite Hmapeq in *;trivial.
        apply NoDup_cons_iff in Hnodupva.
        intuition.
      ++ destruct Ha as (phyVa & Hphy).
         assert(HmapaS : getMappedPage pd s' a = SomePage phyVa).
         rewrite Hmapeq in *;trivial. 
         rewrite getMappedPagesAuxConsSome with pd a phyVa
         (filter (checkChild currentPart nbL s') (filter checkOffset0 l))  s';trivial.
         rewrite getMappedPagesAuxConsSome with pd a phyVa
         (filter (checkChild currentPart nbL s) (filter checkOffset0 l))  s;trivial.
         assert(exists l1 l2 : list page,
        getMappedPagesAux pd (filter (checkChild currentPart nbL s') (filter checkOffset0 l)) s' = l1 ++ newPartition :: l2 /\
        getMappedPagesAux pd (filter (checkChild currentPart nbL s) (filter checkOffset0 l)) s = l1 ++ l2).
        apply IHl;trivial.
         simpl in Hnotin.
        rewrite Hii in *.
        rewrite getMappedPagesAuxConsSome with pd a phyVa
         (filter (checkChild currentPart nbL s) (filter checkOffset0 l))  s in Hnotin ;trivial.
        simpl in Hnotin.
        tauto.
        simpl in Hin.
        rewrite Hi in *.
        rewrite getMappedPagesAuxConsSome with pd a phyVa
         (filter (checkChild currentPart nbL s') (filter checkOffset0 l))  s' in Hin ;trivial.
        simpl in Hin.
        assert(Hphynoteq : newPartition <> phyVa).
        { apply twoMappedPagesAreDifferent with  descChild a pd nbL s;
          trivial.
(*           apply AllVAddrAll. *)
(*           apply AllVAddrAll. *)
          unfold noDupMappedPagesList in *.
          apply Hnodupmap in Hpart.
          unfold getMappedPages in *.
          rewrite Hpd in *.
          unfold getMappedPagesAux in *;tauto.
          assert(Horkey : checkVAddrsEqualityWOOffset nbLevel descChild a nbL = false \/
          checkVAddrsEqualityWOOffset nbLevel descChild a nbL = true).
          { destruct (checkVAddrsEqualityWOOffset nbLevel descChild a nbL).
          right;trivial.
          left;trivial. }
          destruct Horkey as [Horkey | Horkey];trivial.
          assert(Hfalse1 : checkChild currentPart nbL s descChild = 
          checkChild currentPart nbL s a).
          apply checkChildEq;trivial.
          rewrite Hfalse1 in *.
           assert(Hfalse2 : checkChild currentPart nbL s' descChild = 
           checkChild currentPart nbL s' a).
          apply checkChildEq;trivial.
          rewrite Hfalse2 in *.
          rewrite Hii in H0. 
          now contradict H0. }
        destruct Hin;subst;try now contradict Hphynoteq.
        trivial.
        apply NoDup_cons_iff in Hnodupva.
        intuition.
        destruct H as (l1 & l2 & H).
        
        exists (phyVa ::l1), l2.
        simpl.
        destruct H.
        split;
        f_equal;
        trivial.
    * assert (Hi' : checkChild currentPart nbL s' a = true).
      {
   apply checkChildTrueSameValue;trivial. }
   rewrite Hi' in *.
   now contradict Hi.  
 - case_eq (checkChild currentPart nbL s' a); intros Hi.
    * assert(Ha : getMappedPage pd s a = NonePage \/ 
  getMappedPage pd s a = SomeDefault \/ (exists phy , getMappedPage pd s a = SomePage phy)).
  { destruct (getMappedPage pd s a). 
  do 2 right;exists p;trivial.
  right;left;trivial.
  left;trivial.  }
        destruct Ha as [Ha | [Ha|Ha]].
      ++ rewrite getMappedPagesAuxConsNone ; [ | rewrite Hmapeq in *;trivial].
        simpl in *.
        rewrite Hii in *.
        rewrite Hi in *. 
          rewrite getMappedPagesAuxConsNone in *;trivial.
        apply IHl ;trivial.
        apply NoDup_cons_iff in Hnodupva.
        intuition.
        rewrite Hmapeq in *;trivial. 
          ++ rewrite getMappedPagesAuxConsDefault ; [ | rewrite Hmapeq in *;trivial].
        simpl in *.
        rewrite Hii in *.
        rewrite Hi in *. 
          rewrite getMappedPagesAuxConsDefault in *;trivial.
        apply IHl ;trivial.
        apply NoDup_cons_iff in Hnodupva.
        intuition.
        rewrite Hmapeq in *;trivial. 
      ++   destruct Ha as (phyVa & Hphy).
         assert( Hor :
                        StateLib.checkVAddrsEqualityWOOffset nbLevel a descChild nbL = false). 
         
           apply checkVAddrsEqualityWOOffsetFalseEqOffset;trivial. 
         assert(checkChild currentPart nbL s' a = false).
         { clear IHl.
          unfold checkChild in *.
           assert(Hsh1S : StateLib.getFstShadow currentPart (memory s') =
                StateLib.getFstShadow currentPart (memory s))by (
          apply getFstShadowAddDerivation with entry;trivial). 
        rewrite Hsh1S in *. clear Hsh1S.
        rewrite nextEntryIsPPgetFstShadow in *.
        rewrite Hsh1 in *. 

        assert(Hind :  getIndirection currentShadow1 a nbL (nbLevel - 1) s' =
           getIndirection currentShadow1 a nbL (nbLevel - 1) s) by (
           apply getIndirectionAddDerivation with entry;trivial). 
        rewrite Hind in *; clear Hind.
        case_eq ( getIndirection currentShadow1 a nbL (nbLevel - 1) s);
         [intros ind Hind1 |intros Hind1]; 
        rewrite Hind1 in *;try now contradict Hii.
        case_eq (ind =? defaultPage);intros Hindnotnil;
        try now contradict H0;trivial.
        trivial.
        assert(Hind :  getIndirection currentShadow1 descChild nbL (nbLevel - 1) s' =
           getIndirection currentShadow1 descChild nbL (nbLevel - 1) s) by (
           apply getIndirectionAddDerivation with entry;trivial). 
        rewrite Hind in *; clear Hind.
        case_eq ( getIndirection currentShadow1 descChild nbL (nbLevel - 1) s);
         [intros ind2 Hind2 |intros Hind2]; 
        rewrite Hind2 in *;try now contradict Hcheck.
        destruct (ind2 =? defaultPage);
        try now contradict H0.
        assert(Some ind2 = Some ptRefChildFromSh1).
        { destruct Hpp with  (StateLib.getIndexOfAddr descChild fstLevel)
          as (Hve & Hroot) ;trivial.
          unfold getTableAddrRoot in Hroot.
          destruct Hroot as (_ & Hroot).
          rewrite <- nextEntryIsPPgetFstShadow in *.
          apply Hroot in Hsh1.
          clear Hroot.
          move Hsh1 at bottom.
          destruct Hsh1 as (ll & Hll & stop & Hstop& Hroot).
          subst.
          rewrite <- Hll in *.
          inversion HnbL;subst.         
          assert(getIndirection currentShadow1 descChild nbL (nbLevel - 1) s = 
          Some ptRefChildFromSh1 ).
          apply getIndirectionStopLevelGT2 with (nbL +1);trivial.
          omega.
          apply getNbLevelEq in Hll.
          subst.
          apply nbLevelEq.
          rewrite <- Hind2.
(*           rewrite <- H1. *)
          trivial.  }
        inversion H;subst.
        clear H.
        assert(currentShadow1 <> defaultPage).
        { unfold partitionDescriptorEntry in *.
          assert(Hexist : exists entry : page, nextEntryIsPP currentPart sh1idx entry s /\ entry <> defaultPage).
          apply Hpde;trivial.
          right;left;trivial.
          destruct Hexist as (ii & Hi1 & Hi2).
          assert(ii = currentShadow1).
          apply getSh1NextEntryIsPPEq with currentPart s;trivial.
          subst;trivial. }
        assert(ind <> ptRefChildFromSh1 \/ 
         (StateLib.getIndexOfAddr a fstLevel) <> 
         (StateLib.getIndexOfAddr descChild fstLevel)).

        { apply pageTablesOrIndicesAreDifferent with currentShadow1 
          currentShadow1 nbL  nbLevel s;trivial.
          apply noDupConfigPagesListNoDupGetIndirections with currentPart sh1idx;trivial.
          apply Hnodupconfig ;trivial.
          right;left;trivial.
          apply nextEntryIsPPgetFstShadow;trivial.
          apply noDupConfigPagesListNoDupGetIndirections with currentPart sh1idx;trivial.
          apply Hnodupconfig ;trivial.
          right;left;trivial.
          apply nextEntryIsPPgetFstShadow;trivial.
          left;split;trivial.
          symmetry in HnbL.
          apply getNbLevelEq in HnbL.
          subst;trivial.
          apply beq_nat_false in Hindnotnil;trivial.
          unfold not;intros;subst.
          now contradict Hindnotnil.
          apply beq_nat_false in Hpp1.
          unfold not;intros;subst;now contradict Hpp1.
          apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
          symmetry in HnbL.
          apply getNbLevelEq in HnbL.
          subst.
          unfold CLevel.
          assert(0<nbLevel) by apply nbLevelNotZero.
          case_eq (lt_dec (nbLevel - 1) nbLevel);intros;
          simpl;
          omega.
          symmetry in HnbL.
          apply getNbLevelEq in HnbL.
          subst.
          apply nbLevelEq.
          apply getIndirectionStopLevelGT with (nbLevel - 1);trivial.
          symmetry in HnbL.
          apply getNbLevelEq in HnbL.
          subst.
          unfold CLevel.
          assert(0<nbLevel) by apply nbLevelNotZero.
          case_eq (lt_dec (nbLevel - 1) nbLevel);intros;
          simpl;
          omega.
          symmetry in HnbL.
          apply getNbLevelEq in HnbL.
          subst.
          apply nbLevelEq. }
        rewrite Hindnotnil in *. 
        assert(Heq : StateLib.readPDflag ind (StateLib.getIndexOfAddr a fstLevel) (memory s) 
            =   StateLib.readPDflag ind (StateLib.getIndexOfAddr a fstLevel) (memory s')).
         { unfold s'.
          simpl.
          symmetry.
          apply readPDflagAddDerivation;trivial.
         }
          rewrite Heq in *.
          trivial. }
          rewrite H in *.
          
          now contradict Hi.
  * apply IHl;trivial.
    simpl in Hnotin.
    rewrite Hii in *;trivial.
    simpl in Hnotin.
    rewrite Hii in *.
    simpl in Hin.
    rewrite Hi in *.
    trivial. 
    apply NoDup_cons_iff in Hnodupva.
    intuition.
    + apply IHl;trivial.
Qed.

Lemma getPartitionAuxSplitList   s:
 noDupPartitionTree s-> 
forall parent , In parent (getPartitions multiplexer s) ->
exists nbPagesParent l1 l2,
getPartitionAux multiplexer s (nbPage +1) = l1 ++ [parent] ++
flat_map (fun p => getPartitionAux p s (nbPagesParent-1) )
(getChildren parent s)++ l2.
Proof.
 intros Hnoduptree. 
assert(Hmult : In multiplexer (getPartitions multiplexer s)).
{ unfold getPartitions.
destruct nbPage;
simpl;
left;trivial. }
revert Hmult.
generalize multiplexer at 1 3 4.
unfold getPartitions at 2.
induction (nbPage+1);intros.
simpl in H;tauto.
simpl.
simpl in H.
destruct H;subst. 
+ exists (S n), nil, nil.
  simpl.
  rewrite app_nil_r.
  rewrite <- minus_n_O.
  reflexivity.
+ apply in_flat_map in H.
destruct H as (ancestor & Hi & Hii).

assert(In ancestor (getPartitions multiplexer s)) by
(apply childrenPartitionInPartitionList with p;trivial).  
apply in_split in Hi.
destruct Hi as (l11 & l22 & Hi).
apply IHn with (parent:= parent) in H;trivial.
destruct H as (nbPP & l12 & l21 & H).
exists nbPP.
do 2 eexists.
rewrite Hi.
rewrite flat_map_app_cons.
simpl.
rewrite app_nil_r.
rewrite H.
instantiate (1:= l21 ++ flat_map (fun p0 : page => getPartitionAux p0 s n) l22 ).
instantiate (1:= p :: flat_map (fun p0 : page => getPartitionAux p0 s n) l11 ++ l12).
simpl.
f_equal.
do 2 (symmetry;
rewrite app_assoc_reverse;
f_equal).
simpl.
f_equal.
rewrite app_assoc_reverse.
reflexivity.
Qed.

Lemma addPartitionKeepsAllChildren 
part table idx entry nbL v s :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
StateLib.getNbLevel = Some nbL -> 
checkChild part nbL s v = true -> 
checkChild part nbL {|
currentPartition := currentPartition s;
memory := add table idx (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}
 v = true. 
Proof. 
set(s' :=  {|
currentPartition := currentPartition s;
memory := add table idx (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |})
in *.
intros Hlookup HnbL Hchild.
unfold checkChild in *.
assert(Hsh1S : StateLib.getFstShadow part (memory s') =
      StateLib.getFstShadow part (memory s))by (
apply getFstShadowAddDerivation with entry;trivial). 
rewrite Hsh1S in *. clear Hsh1S.
destruct (StateLib.getFstShadow part (memory s));
try now contradict H0.
assert(Hind :  getIndirection p v nbL (nbLevel - 1) s' =
 getIndirection p v nbL (nbLevel - 1) s) by (
 apply getIndirectionAddDerivation with entry;trivial). 
rewrite Hind in *; clear Hind.
case_eq ( getIndirection p v nbL (nbLevel - 1) s);
[intros ind Hind1 |intros Hind1]; 
rewrite Hind1 in *;trivial.
destruct (ind =? defaultPage);trivial.
unfold s' in *.
simpl in *.
unfold StateLib.readPDflag in *.
cbn in *.
case_eq(beqPairs (table, idx) (ind, StateLib.getIndexOfAddr v fstLevel) beqPage beqIndex);
intros Hpairs . 
simpl;trivial.
apply beqPairsFalse in Hpairs.
assert(lookup ind (StateLib.getIndexOfAddr v fstLevel)
(removeDup  table idx  
(memory s) beqPage beqIndex) beqPage beqIndex =
lookup ind (StateLib.getIndexOfAddr v fstLevel) (memory s) beqPage beqIndex).        
apply removeDupIdentity;intuition.        
rewrite H in *. clear H.
case_eq (lookup ind (StateLib.getIndexOfAddr v fstLevel) (memory s) beqPage beqIndex)
; [ intros a Hv | intros Hv]; rewrite Hv in *; try now contradict Hi.
trivial. trivial. trivial.
Qed.

Lemma addPartitionGetChildrenNoDup s parent entry table idx nbL pdParent: 
let s' := {|
currentPartition := currentPartition s;
memory := add table idx (VE {| pd := true; va := va entry |})
        (memory s) beqPage beqIndex |} in 
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->
NoDup (getMappedPagesAux pdParent getAllVAddrWithOffset0 s') -> 
StateLib.getNbLevel = Some nbL -> 
NoDup (getMappedPagesAux pdParent (getPdsVAddr parent nbL getAllVAddrWithOffset0 s') s'). 
Proof.
intros s' Hlookup HnodupmapS HnbL.
unfold getPdsVAddr in *.
induction getAllVAddrWithOffset0;simpl in *.
+ unfold getMappedPagesAux.
simpl. constructor.
+ assert(Ha : getMappedPage pdParent s a = NonePage \/ 
  getMappedPage pdParent s a = SomeDefault \/ (exists phy , getMappedPage pdParent s a = SomePage phy)).
  { destruct (getMappedPage pdParent s a). 
  do 2 right;exists p;trivial.
  right;left;trivial.
  left;trivial.  }
 case_eq (checkChild parent nbL s' a);intros.
  * destruct Ha as [Ha | [Ha|Ha]].
    - rewrite getMappedPagesAuxConsNone in HnodupmapS.
      rewrite getMappedPagesAuxConsNone.
      apply IHl;trivial.
      rewrite <- Ha.
      apply getMappedPageAddDerivation with entry;trivial.
      rewrite <- Ha.
      apply getMappedPageAddDerivation with entry;trivial.
    - rewrite getMappedPagesAuxConsDefault in HnodupmapS.
      rewrite getMappedPagesAuxConsDefault.
      apply IHl;trivial.
      rewrite <- Ha.
      apply getMappedPageAddDerivation with entry;trivial.
      rewrite <- Ha.
      apply getMappedPageAddDerivation with entry;trivial.
    - destruct Ha as (phy & Ha).
      rewrite getMappedPagesAuxConsSome with pdParent a phy l s' in HnodupmapS.
      rewrite getMappedPagesAuxConsSome with pdParent a phy 
      (filter (checkChild parent nbL s') l) s'.
      rewrite NoDup_cons_iff in *.
      destruct HnodupmapS as (Hin1 & Hin2).
      split.
      unfold getMappedPagesAux in Hin1.
      unfold getMappedPagesAux.
      rewrite filterOptionInIff in *. 
      unfold getMappedPagesOption in *.
      rewrite in_map_iff in *.
      unfold not;intros;contradict Hin1.
      destruct H0 as (x & Hx1 & Hx2).
      exists x;split;trivial.
      apply filter_In in Hx2.
      intuition.
      apply IHl;trivial.
      rewrite <- Ha.
      apply getMappedPageAddDerivation with entry;trivial.
      rewrite <- Ha.
      apply getMappedPageAddDerivation with entry;trivial.
  * apply IHl.
    simpl in *.
    destruct Ha as [Ha | [Ha|Ha]].
    - rewrite getMappedPagesAuxConsNone in HnodupmapS.
      trivial.
      rewrite <- Ha.
      apply getMappedPageAddDerivation with entry;trivial.
  - rewrite getMappedPagesAuxConsDefault in HnodupmapS.
      trivial.
      rewrite <- Ha.
      apply getMappedPageAddDerivation with entry;trivial.
    - destruct Ha as (phy & Ha).
      rewrite getMappedPagesAuxConsSome with pdParent a phy 
      l s' in HnodupmapS.
      rewrite NoDup_cons_iff in HnodupmapS.
      intuition.
      rewrite <- Ha.
      apply getMappedPageAddDerivation with entry;trivial.
Qed.

Lemma premierLemmePoseAvecSam s n :
noDupPartitionTree s -> 
verticalSharing s ->  
forall partition, In partition (getPartitions multiplexer s) -> 
forall subPartition, subPartition <> partition -> 
In subPartition (getPartitionAux partition s n ) -> 
In subPartition (getMappedPages partition s). 
Proof.    
intros Hnoduptree Hvs. 
induction  n;
simpl;intros partition Hpart subPartition Hnoteq Hsubpart;try now contradict Hsubpart.
destruct Hsubpart as [Hsubpart | Hsubpart]; [subst;now contradict Hnoteq|].
apply in_flat_map in Hsubpart.
destruct Hsubpart as (child & Hchild1 & Hchild2).
unfold verticalSharing in *.
unfold incl in *.
unfold incl in *.
assert(child = subPartition \/ child <> subPartition) by apply pageDecOrNot.
destruct H.
+ subst.
  apply Hvs with subPartition;trivial.
  unfold getUsedPages.
  rewrite in_app_iff.
  left.
  unfold getConfigPages.
  simpl;left;trivial.
+ apply Hvs with child;trivial.
  unfold getUsedPages.
  apply in_app_iff.
  right.   
  apply IHn;trivial.
  apply childrenPartitionInPartitionList with partition;trivial.
  intuition.
Qed. (** premierLemmePoseAvecSam *)

Lemma addPartitionAddSingleChild table idx entry nbL s :
let s' := {|
currentPartition := currentPartition s;
memory := add table idx
          (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in
partitionDescriptorEntry s ->
configTablesAreDifferent s -> 
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
StateLib.getNbLevel = Some nbL -> 
forall part parent va a, 
part <> parent -> 
In part (getPartitions multiplexer s) -> 
In parent (getPartitions multiplexer s) -> 
checkChild parent nbL s' va = true -> 
checkChild parent nbL s va = false ->
checkChild part nbL s a = false -> 
checkChild part nbL s' a = false.
Proof.
intros s' Hpde Hconfigs Hlookup HnbL part parent va a Hnoteq  Hi1 Hpart Htrue  Hfalse H. 
unfold checkChild in *.
assert(Hsh1 : forall part, getFstShadow part (memory s') =
getFstShadow part (memory s)).
unfold s';simpl.
intros. 
apply getFstShadowAddDerivation with entry;trivial.
rewrite  Hsh1 in *;clear Hsh1.  
case_eq ( getFstShadow part (memory s)); [ intros sh1 Hsh1 | 
intros Hsh1];rewrite Hsh1 in *;trivial.
move Hpde at bottom.
unfold partitionDescriptorEntry in *.
assert(  sh1idx < tableSize - 1 /\
isVA part sh1idx s /\ 
(exists entry : page, nextEntryIsPP part sh1idx entry s /\ entry <> defaultPage))
as (_ & _ & Hsh1prop).
apply Hpde;trivial.
right;left;trivial.   
assert(  sh1idx < tableSize - 1 /\
isVA parent sh1idx s /\ 
(exists entry : page, nextEntryIsPP parent sh1idx entry s /\ entry <> defaultPage))
as (_ & _ & Hsh1propparent).
apply Hpde;trivial.
right;left;trivial.
case_eq ( getFstShadow parent (memory s)); [ intros sh1parent Hsh1parent | 
intros Hsh1parent];rewrite Hsh1parent in *;trivial.
2: {
destruct Hsh1propparent as (xx & Hsh1parentprop & Hnotnull).
rewrite nextEntryIsPPgetFstShadow in *. 
rewrite Hsh1parentprop in Hsh1parent.
now contradict Hsh1parent. }
assert(Hind :  forall va root ,  
getIndirection root va nbL (nbLevel - 1) s' =
getIndirection root va nbL (nbLevel - 1) s).
intros.
apply getIndirectionAddDerivation with entry;trivial.
rewrite Hind in *.
clear Hind.
case_eq (getIndirection sh1 a nbL (nbLevel - 1) s); [intros indpart Hindpart |
intros Hindpart];trivial;rewrite Hindpart in *.
case_eq (getIndirection sh1parent va nbL (nbLevel - 1) s);
[intros indparent Hindparent |
intros Hindparent];trivial;rewrite Hindparent in *.
case_eq (indparent =? defaultPage); intros Hnul; rewrite Hnul in *.
now contradict Htrue.
case_eq (indpart =? defaultPage); intros Hnul1; rewrite Hnul1 in *;trivial.
assert(indparent = table).
{ unfold  StateLib.readPDflag in *.
unfold s' in *. 
simpl in *.
case_eq(  beqPairs (table, idx) (indparent, StateLib.getIndexOfAddr va fstLevel)
      beqPage beqIndex);intros Hpairs;
      rewrite Hpairs in *;
      simpl in *.
      apply beqPairsTrue in Hpairs.
      destruct Hpairs;subst;trivial.
assert(lookup indparent (StateLib.getIndexOfAddr va fstLevel)
    (removeDup table idx 
    (memory s) beqPage beqIndex) beqPage beqIndex
    =  
lookup indparent (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ).
apply removeDupIdentity;trivial.
apply beqPairsFalse in Hpairs.
intuition.
rewrite H0 in *.
rewrite Htrue in Hfalse.
now contradict Hfalse. } 
assert(indpart <> indparent).
{ unfold configTablesAreDifferent  in *. 
move Hconfigs at bottom.
unfold disjoint in *.
assert(In indpart (getConfigPages part s)).
{ assert(In indpart (getIndirectionsAux sh1 s nbLevel )).
  { apply getIndirectionInGetIndirections with a nbL (nbLevel - 1) ;trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    omega.
    apply beq_nat_false in Hnul1.
    unfold not;intros;subst;now contradict Hnul1.
    symmetry in HnbL.
    apply getNbLevelEq in HnbL.
    subst.
    omega.
    trivial.
    destruct Hsh1prop as (sh1' & Hsh1prop & Hnotnull).
    assert (sh1' = sh1).
    apply getSh1NextEntryIsPPEq with part s;trivial.
    subst.
    unfold not;intros;subst;now contradict Hnotnull. }
  unfold getConfigPages.
  simpl;right. 
  apply inGetIndirectionsAuxInConfigPagesSh1 with sh1;trivial. }
  assert(In indparent (getConfigPages parent s)).
  { assert(In indparent (getIndirectionsAux sh1parent s nbLevel )).
    { apply getIndirectionInGetIndirections with va nbL (nbLevel - 1) ;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      apply beq_nat_false in Hnul.
      unfold not;intros;
      subst;
      subst;  now contradict Hnul.
      symmetry in HnbL.
      apply getNbLevelEq in HnbL.
      subst.
      omega.
      trivial.
      destruct Hsh1propparent as (sh1' & Hsh1parentprop & Hnotnull).
      assert (sh1' = sh1parent).
      apply getSh1NextEntryIsPPEq with parent s;trivial.
      subst.
      unfold not;intros;subst;now contradict Hnotnull. }
    unfold getConfigPages.
    simpl;right. 
    apply inGetIndirectionsAuxInConfigPagesSh1 with sh1parent;trivial. }
    assert( ~ In indparent (getConfigPages part s)).
    apply Hconfigs with parent;trivial.
    unfold not;intros Hii;subst;now contradict Hnoteq.
    unfold not;intros;subst.
    now contradict H3. }  
assert ( StateLib.readPDflag indpart (StateLib.getIndexOfAddr a fstLevel)
(memory s')  = 
StateLib.readPDflag indpart (StateLib.getIndexOfAddr a fstLevel) (memory s) ).  
unfold s';simpl.
apply readPDflagAddDerivation ; trivial.
subst;left;trivial.
rewrite H2.
trivial.
now contradict Htrue.
Qed.

(* Lemma addPartitionAddSingleChildIntoTheSamePart table idx entry nbL s :
let s' := {|
currentPartition := currentPartition s;
memory := add table idx
          (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in
partitionDescriptorEntry s ->
configTablesAreDifferent s -> 
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
StateLib.getNbLevel = Some nbL -> 
forall  parent va a, 
a <> va -> 
In parent (getPartitions multiplexer s) -> 
checkChild parent nbL s' va = true -> 
checkChild parent nbL s va = false ->
checkChild parent nbL s a = false -> 
checkChild parent nbL s' a = false.
Proof.
intros s' Hpde Hconfigs Hlookup HnbL  parent va a  Hnoteq Hpart Htrue  Hfalse H. 
unfold checkChild in *.
assert(Hsh1 : forall part, getFstShadow part (memory s') =
getFstShadow part (memory s)).
unfold s';simpl.
intros. 
apply getFstShadowAddDerivation with entry;trivial.
rewrite  Hsh1 in *;clear Hsh1.  
case_eq ( getFstShadow parent (memory s)); [ intros sh1 Hsh1 | 
intros Hsh1];rewrite Hsh1 in *;trivial.
move Hpde at bottom.
unfold partitionDescriptorEntry in *.
assert(  sh1idx < tableSize - 1 /\
isVA parent sh1idx s /\ 
(exists entry : page, nextEntryIsPP parent sh1idx entry s /\ entry <> defaultPage))
as (_ & _ & Hsh1prop).
apply Hpde;trivial.
right;left;trivial.   
case_eq ( getFstShadow parent (memory s)); [ intros sh1parent Hsh1parent | 
intros Hsh1parent];rewrite Hsh1parent in *;trivial.
Focus 2 .
destruct Hsh1prop as (xx & Hsh1parentprop & Hnotnull).
rewrite nextEntryIsPPgetFstShadow in *. 
rewrite Hsh1parentprop in Hsh1parent.
now contradict Hsh1parent.   
assert(Hind :  forall va root ,  
getIndirection root va nbL (nbLevel - 1) s' =
getIndirection root va nbL (nbLevel - 1) s).
intros.
apply getIndirectionAddDerivation with entry;trivial.
rewrite Hind in *.
clear Hind.
case_eq (getIndirection sh1 a nbL (nbLevel - 1) s); [intros indpart Hindpart |
intros Hindpart];trivial;rewrite Hindpart in *.
case_eq (indpart =? defaultPage); intros Hnul; rewrite Hnul in *.
trivial.
case_eq (getIndirection sh1 va nbL (nbLevel - 1) s); [intros indpart2 Hindpart2 |
intros Hindpart2];trivial;rewrite Hindpart2 in *.
case_eq (indpart2 =? defaultPage); intros Hnul1; rewrite Hnul1 in *.
now contradict Htrue.
assert (indpart <> indpart2 \/ (StateLib.getIndexOfAddr a fstLevel) <> 
(StateLib.getIndexOfAddr a fstLevel)).
apply tablesOr 

trivial.

case_eq (indpart =? defaultPage); intros Hnul1; rewrite Hnul1 in *;trivial.

assert(indparent = table).
{ unfold  StateLib.readPDflag in *.
unfold s' in *. 
simpl in *.
case_eq(  beqPairs (table, idx) (indparent, StateLib.getIndexOfAddr va fstLevel)
      beqPage beqIndex);intros Hpairs;
      rewrite Hpairs in *;
      simpl in *.
      apply beqPairsTrue in Hpairs.
      destruct Hpairs;subst;trivial.
assert(lookup indparent (StateLib.getIndexOfAddr va fstLevel)
    (removeDup table idx 
    (memory s) beqPage beqIndex) beqPage beqIndex
    =  
lookup indparent (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ).
apply removeDupIdentity;trivial.
apply beqPairsFalse in Hpairs.
intuition.
rewrite H0 in *.
rewrite Htrue in Hfalse.
now contradict Hfalse. } 
assert(indpart <> indparent).
{ unfold configTablesAreDifferent  in *. 
move Hconfigs at bottom.
unfold disjoint in *.
assert(In indpart (getConfigPages part s)).
{ assert(In indpart (getIndirectionsAux sh1 s nbLevel )).
  { apply getIndirectionInGetIndirections with a nbL (nbLevel - 1) ;trivial.
    assert(0<nbLevel) by apply nbLevelNotZero.
    omega.
    apply beq_nat_false in Hnul1.
    unfold not;intros;subst;now contradict Hnul1.
    symmetry in HnbL.
    apply getNbLevelEq in HnbL.
    subst.
    omega.
    trivial.
    destruct Hsh1prop as (sh1' & Hsh1prop & Hnotnull).
    assert (sh1' = sh1).
    apply getSh1NextEntryIsPPEq with part s;trivial.
    subst.
    unfold not;intros;subst;now contradict Hnotnull. }
  unfold getConfigPages.
  simpl;right. 
  apply inGetIndirectionsAuxInConfigPagesSh1 with sh1;trivial. }
  assert(In indparent (getConfigPages parent s)).
  { assert(In indparent (getIndirectionsAux sh1parent s nbLevel )).
    { apply getIndirectionInGetIndirections with va nbL (nbLevel - 1) ;trivial.
      assert(0<nbLevel) by apply nbLevelNotZero.
      omega.
      apply beq_nat_false in Hnul.
      unfold not;intros;
      subst;
      subst;  now contradict Hnul.
      symmetry in HnbL.
      apply getNbLevelEq in HnbL.
      subst.
      omega.
      trivial.
      destruct Hsh1propparent as (sh1' & Hsh1parentprop & Hnotnull).
      assert (sh1' = sh1parent).
      apply getSh1NextEntryIsPPEq with parent s;trivial.
      subst.
      unfold not;intros;subst;now contradict Hnotnull. }
    unfold getConfigPages.
    simpl;right. 
    apply inGetIndirectionsAuxInConfigPagesSh1 with sh1parent;trivial. }
    assert( ~ In indparent (getConfigPages part s)).
    apply Hconfigs with parent;trivial.
    unfold not;intros Hii;subst;now contradict Hnoteq.
    unfold not;intros;subst.
    now contradict H3. }  
assert ( StateLib.readPDflag indpart (StateLib.getIndexOfAddr a fstLevel)
(memory s')  = 
StateLib.readPDflag indpart (StateLib.getIndexOfAddr a fstLevel) (memory s) ).  
unfold s';simpl.
apply readPDflagAddDerivation ; trivial.
subst;left;trivial.
rewrite H2.
trivial.
now contradict Htrue.
Qed.
 *)
Lemma deuxiemeLemmePoseAvecSam entry table descChild 
(newPartition ptRefChild currentShadow1 currentPD : page)  parent s:
noDupPartitionTree s -> 
configTablesAreDifferent s  -> 
partitionDescriptorEntry s -> 
noDupMappedPagesList s -> 
noDupConfigPagesList s -> 
In parent (getPartitions multiplexer s) -> 
isPartitionFalse table (StateLib.getIndexOfAddr descChild fstLevel) s -> 
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s -> 
nextEntryIsPP parent PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx parent descChild s )-> 
(defaultPage =? ptRefChild) = false -> 
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) newPartition s ->
nextEntryIsPP parent sh1idx currentShadow1 s ->
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isVE table idx s /\ getTableAddrRoot table sh1idx parent descChild s ) -> 
(defaultPage =? table) = false -> 
lookup table (StateLib.getIndexOfAddr descChild fstLevel) (memory s) beqPage beqIndex =
Some (VE entry) -> 
~ In newPartition (getChildren parent s) -> 
In newPartition
  (getChildren parent
     {|
     currentPartition := currentPartition s;
     memory := add table (StateLib.getIndexOfAddr descChild fstLevel)
                 (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}) -> 
let s' := {|
   currentPartition := currentPartition s;
   memory := add table (StateLib.getIndexOfAddr descChild fstLevel) (VE {| pd := true; va := va entry |})
               (memory s) beqPage beqIndex |} in
In descChild getAllVAddrWithOffset0 -> 
forall part n, (* n> nbPage ->   *)
In part (getPartitions multiplexer s) ->
~In parent (getPartitionAux part s n) -> 
 (getPartitionAux part s (* (n+1) *) n = getPartitionAux part s' n (* (n+1) *)).
Proof. 
intros Hnoduptree Hconfigs Hpde Hnodupmap Hnodupconfig Hpart  Hnotpart Hpresent (* Hpart *) 
Hpppd HgetA Hnotnull Hentry Hsh1 Hpp Hpp1  Hlookup Hnotin Hin.
intros s' Hnewhyp(* HparentS *).
assert(Hchildren : exists  l1 l2,
getChildren parent s' = l1 ++ [newPartition] ++ l2 /\
getChildren parent s = l1 ++l2).
unfold s'.
apply getChildrenSplitList with ptRefChild currentShadow1 currentPD; trivial.
clear  (* Hnodupmap *) Hnodupconfig   Hnotpart Hpresent (* Hpart *) 
Hpppd HgetA Hnotnull Hentry Hsh1 Hpp Hpp1   Hnotin Hin. 
destruct Hchildren as (li1 & li2 & HchildS & Hchild).
simpl.
intros part n Hi1 Hi2.
unfold getPartitions.
unfold getPartitions in Hi2.
revert Hi1 Hi2.
revert part. 
induction n in *.
-
simpl in *.
intros. 
move Hi1 at top.
f_equal. (* 
clear.
induction (getChildren part s');simpl;trivial.
induction (getChildren part s);simpl;trivial. *)
-
intros. 
simpl in *.
f_equal.
apply Classical_Prop.not_or_and in Hi2 as (Hnoteq & Hin).
assert( (getChildren part s) =  (getChildren part s') ) .
{  clear Hin IHn .
  unfold getChildren in *.
  case_eq  StateLib.getNbLevel; [ intros nbL HnbL | intros HnbL]; 
  rewrite HnbL in *;trivial.
  unfold s' in *; simpl in *.
  assert(Hpd : forall part, StateLib.getPd part (memory s) = 
   StateLib.getPd part
    (add table (StateLib.getIndexOfAddr descChild fstLevel) (VE {| pd := true; va := va entry |}) 
       (memory s) beqPage beqIndex)).
       intros.
       symmetry.
  apply getPdAddDerivation with entry ;trivial.
  rewrite <- Hpd in *;clear Hpd.
  case_eq (StateLib.getPd part (memory s));  [ intros pdPart Hpdpart
   | intros HpdPart];trivial.
  case_eq(  StateLib.getPd parent (memory s) ); [ intros pdParent HpdParent
   | intros HpdParent]; rewrite HpdParent in *; [ |
   apply app_cons_not_nil in HchildS;
   tauto].
  fold s'.
  fold s' in HchildS.
  assert( (getPdsVAddr part nbL getAllVAddrWithOffset0 s) = 
  (getPdsVAddr part nbL getAllVAddrWithOffset0 s')).
  {
  unfold getPdsVAddr.
  assert(exists va , In va  (getPdsVAddr parent nbL getAllVAddrWithOffset0 s') /\ 
  getMappedPage pdParent s va = SomePage newPartition).
  { clear Hchild.
    revert li1 li2 HchildS. 
    clear Hnewhyp.
    induction getAllVAddrWithOffset0.
    simpl in *.  
    unfold getMappedPagesAux in *.
    unfold getMappedPagesOption in *. 
    simpl in *.
    intros. 
    apply app_cons_not_nil in HchildS.
    now contradict HchildS.
    simpl in *.
    intros.    
    case_eq (checkChild parent nbL s' a);intros.
    rewrite H in *.
    simpl in *.
assert(Ha : getMappedPage pdParent s a = NonePage \/ 
  getMappedPage pdParent s a = SomeDefault \/ (exists phy , getMappedPage pdParent s a = SomePage phy)).
  { destruct (getMappedPage pdParent s a). 
  do 2 right;exists p;trivial.
  right;left;trivial.
  left;trivial.  }
    destruct Ha as [Ha | [Ha|Ha]].
    rewrite getMappedPagesAuxConsNone in HchildS.
    apply IHl in HchildS.
    destruct HchildS as (va & Hva & Hmap).
    exists va.
    split;trivial.
    right;trivial.
    rewrite <-Ha.
    apply getMappedPageAddDerivation with entry;trivial.
    rewrite getMappedPagesAuxConsDefault in HchildS.
    apply IHl in HchildS.
    destruct HchildS as (va & Hva & Hmap).
    exists va.
    split;trivial.
    right;trivial.
    rewrite <-Ha.
    apply getMappedPageAddDerivation with entry;trivial.
    destruct Ha as (phy & Ha).
    rewrite getMappedPagesAuxConsSome with pdParent a phy 
    (getPdsVAddr parent nbL l s') s' in HchildS.
    assert((phy = hd page_d li1 /\  li1<>[]) \/ phy = newPartition).
    induction li1.
    simpl in *.
    inversion HchildS.
    right;trivial.
    simpl in *. 
    inversion HchildS.
    left;split;trivial.
    unfold not;intros Hi;symmetry in  Hi;contradict Hi;
    apply nil_cons.
    destruct H0 as [(Hi22 & Hi2) | Hi2].
    generalize (IHl (tl li1) li2);clear IHl ; intros IHl.
    assert( exists va : vaddr, In va (getPdsVAddr parent nbL l s') /\ getMappedPage pdParent s va = SomePage newPartition).
    apply IHl.
    subst.
    clear IHl Ha.
    induction li1.
    simpl in *.
    now contradict Hi2.
    simpl in *.
    inversion HchildS;trivial.
    destruct H0 as (va & Hva1 & Hva2).
    exists va.
    split;trivial.
    right;trivial.
    subst.
    exists a.
    split;trivial.
    left;trivial.
    rewrite <- Ha.
    apply getMappedPageAddDerivation with entry;trivial.
    rewrite H in *.
    apply IHl with li1 li2;trivial. }
  destruct H as (va & Hva & Hmap).
  assert (Htrue : checkChild parent nbL s' va = true).
  { clear HchildS Hchild. 
    unfold getPdsVAddr in *.
    rewrite filter_In in *.
    intuition.
  }
  assert (Hfalse :  checkChild parent nbL s va = false).
  { assert(HnodupmapS :NoDup (getMappedPages parent s')).
    { assert(HmapS : getMappedPages parent s' = getMappedPages parent s).      
      apply getMappedPagesAddDerivation with entry;trivial.
      rewrite HmapS.
      unfold noDupMappedPagesList in *.
      apply Hnodupmap;trivial. }
      unfold getMappedPages in HnodupmapS.
      assert(HpdS : StateLib.getPd parent (memory s') =
      StateLib.getPd parent (memory s)).
      { apply getPdAddDerivation with entry;trivial. }
      rewrite HpdS in *. clear HpdS. 
      rewrite HpdParent in HnodupmapS.
      assert(Hnodupchild : NoDup (li1 ++ newPartition :: li2)).
      rewrite <- HchildS.
      apply addPartitionGetChildrenNoDup;trivial.
      apply NoDup_remove_2 in Hnodupchild.
      rewrite <- Hchild in Hnodupchild.
      assert (Hnotin3 : ~ In newPartition (getMappedPagesAux pdParent 
                                            (getPdsVAddr parent nbL getAllVAddrWithOffset0 s) s)) by trivial.
      unfold getMappedPagesAux in Hnotin3.
      rewrite filterOptionInIff in *.
      unfold getMappedPagesOption in *.
      rewrite in_map_iff in *.
      apply Classical_Prop.NNPP.
      unfold not at 1.
      intros.
      contradict Hnotin3.
      exists va;split;trivial.
      unfold getPdsVAddr.
      apply filter_In.
      split.
      unfold getPdsVAddr in Hva.
      apply filter_In in Hva.
      intuition.
      rewrite not_false_iff_true in H;trivial. }
    clear Hva HchildS Hchild. 
    clear Hnewhyp. 
    induction getAllVAddrWithOffset0.
    simpl;trivial.
    simpl.
    rewrite <- IHl;trivial.
    case_eq (checkChild part nbL s a );intros;trivial. 
    + case_eq (checkChild part nbL s' a );intros;trivial.
      assert ( checkChild part nbL s' a = true).
      { unfold checkChild in *.
        assert(Hsh1S : StateLib.getFstShadow part (memory s') =
            StateLib.getFstShadow part (memory s))by (
        apply getFstShadowAddDerivation with entry;trivial). 
        rewrite Hsh1S in *. clear Hsh1S.
        destruct (StateLib.getFstShadow part (memory s));
        try now contradict H0.
        assert(Hind :  getIndirection p a nbL (nbLevel - 1) s' =
         getIndirection p a nbL (nbLevel - 1) s) by (
         apply getIndirectionAddDerivation with entry;trivial). 
        rewrite Hind in *; clear Hind.
        case_eq ( getIndirection p a nbL (nbLevel - 1) s);
        [intros ind Hind1 |intros Hind1]; 
        rewrite Hind1 in *;trivial.
        destruct (ind =? defaultPage);trivial.
        unfold s' in *.
        simpl in *.
        unfold StateLib.readPDflag in *.
        cbn in *.
        case_eq( beqPairs (table, StateLib.getIndexOfAddr descChild fstLevel)
        (ind, StateLib.getIndexOfAddr a fstLevel) beqPage beqIndex);
        intros Hpairs ;rewrite Hpairs in *.
        simpl;trivial.
        apply beqPairsFalse in Hpairs.
        assert(lookup ind (StateLib.getIndexOfAddr a fstLevel)
        (removeDup  table (StateLib.getIndexOfAddr descChild fstLevel) 
        (memory s) beqPage beqIndex) beqPage beqIndex =
        lookup ind (StateLib.getIndexOfAddr a fstLevel) (memory s) beqPage beqIndex).        
        apply removeDupIdentity;intuition.        
        rewrite H1 in *. clear H1.
        case_eq (lookup ind (StateLib.getIndexOfAddr a fstLevel) (memory s) beqPage beqIndex)
        ; [ intros v Hv | intros Hv]; rewrite Hv in *; try now contradict Hi.
        trivial. trivial. }
      rewrite H1 in H0.
      now contradict H0.
    + case_eq (checkChild part nbL s' a );intros;trivial.
      assert ( checkChild part nbL s' a = false).
      { clear IHl H0.

     apply addPartitionAddSingleChild with parent va;trivial.  }
    rewrite H1 in H0.
    now contradict H0. }     
  rewrite <- H.
  unfold s'.
  symmetry. 
  apply getMappedPagesAuxAddDerivation with entry;trivial. }
  
rewrite <- H;clear H.
assert(forall a, In a (getChildren part s) -> In a  (getPartitions multiplexer s)).
intros.
apply childrenPartitionInPartitionList with part;trivial.  
induction (getChildren part s).
simpl;trivial.
simpl.
rewrite IHn;trivial.
f_equal.
apply IHl.
simpl in Hin .
rewrite in_app_iff in Hin .
tauto.
intros.
apply H.
simpl.
right;trivial.
simpl in *.  
apply H.
simpl;left;trivial.
simpl in *.
rewrite in_app_iff in Hin. 
tauto.
Qed. (** deuxiemeLemmePoseAvecSam *)


Lemma addPartitionKeepsAllPartitionsInTree currentPart table idx entry s :
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
In currentPart (getPartitions multiplexer s) -> 
In currentPart
  (getPartitions multiplexer
     {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := true; va := va entry |}) 
                 (memory s) beqPage beqIndex |}).
Proof.
set(s' :=  {|
   currentPartition := currentPartition s;
   memory := add table idx (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |})
   in *.
intros Hlookup.
unfold getPartitions.
generalize multiplexer as mult.
induction (nbPage+1);trivial.
intros mult Hmult.
simpl in *.
destruct Hmult as [Hmult | Hmult].
left;trivial.
right.
rewrite in_flat_map in *.
destruct Hmult as (child & H1child & H2child).
exists child;split; [| apply IHn;trivial].
clear IHn.
unfold getChildren in *.
case_eq (StateLib.getNbLevel);[intros nbL HnbL | intros HnbL];
rewrite HnbL in *; try now contradict H1child.
simpl in *.
assert(Hpd : StateLib.getPd mult (memory s) =
StateLib.getPd mult (add table idx 
(VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex)).
 { symmetry. apply getPdAddDerivation with entry;trivial. }
rewrite <- Hpd in *;clear Hpd.
case_eq (StateLib.getPd mult (memory s));[intros pd Hpd | intros Hpd];
rewrite Hpd in *;try now contradict H1child.
unfold getMappedPagesAux in *.
rewrite filterOptionInIff in *.
unfold getMappedPagesOption in *.
rewrite in_map_iff in *.
destruct H1child as (va & Hva1 & Hva2).
exists va;split.
+ rewrite <- Hva1.
  apply getMappedPageAddDerivation with entry;trivial. 
+ unfold getPdsVAddr in *.
  rewrite filter_In in *.
  intuition.
  apply addPartitionKeepsAllChildren;trivial.
Qed.

Lemma addPartitionGetChildrenEq table idx entry s :
let s':= {|
currentPartition := currentPartition s;
memory := add table idx
          (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in
lookup table idx (memory s) beqPage beqIndex = Some (VE entry) -> 
partitionDescriptorEntry s -> 
configTablesAreDifferent s -> 
forall partition1 partition2, 
In partition1 (getPartitions multiplexer s) -> 
In partition2 (getPartitions multiplexer s) -> 
partition1 <> partition2 -> 
getChildren partition1 s' <> getChildren partition1 s -> 
getChildren partition2 s' = getChildren partition2 s.
Proof.
intros s' Hlookup Hpde Hconfigs.
unfold getChildren.
intros partition1 partition2 Hin1 Hin2 .
intros.
case_eq (StateLib.getNbLevel );[intros nbL HnbL | intros HnbL];
          [|constructor].
          rewrite HnbL in *. 
assert( Hpds :forall parts, StateLib.getPd parts (memory s') =
StateLib.getPd parts (memory s)).
intros.
apply getPdAddDerivation with entry;trivial.
rewrite Hpds in *;clear Hpds. 
case_eq (StateLib.getPd partition2 (memory s) );[intros pd2 Hpd2 | intros Hpd2];
[|trivial].
case_eq (StateLib.getPd partition1 (memory s) );[intros pd1 Hpd1 | intros Hpd1];
rewrite Hpd1 in *; [| contradict H0;trivial].
unfold getMappedPagesAux in *.
assert( (getPdsVAddr partition1 nbL getAllVAddrWithOffset0 s') <> 
(getPdsVAddr partition1 nbL getAllVAddrWithOffset0 s)).
{ unfold not;intros.
  rewrite H1 in *. 
  apply H0.
  clear H1 H0.
  induction  (getPdsVAddr partition1 nbL getAllVAddrWithOffset0 s).
  simpl;intuition.
  simpl.
  assert(HmapS : getMappedPage pd1 s' a = 
  getMappedPage pd1 s a).
  apply getMappedPageAddDerivation with entry;trivial.
  rewrite HmapS in *.
  case_eq ( getMappedPage pd1 s a );intros;
  rewrite H0 in *;trivial.
  f_equal;trivial.
  }     
assert( (getPdsVAddr partition2 nbL getAllVAddrWithOffset0 s) =
(getPdsVAddr partition2 nbL getAllVAddrWithOffset0 s')).
{ unfold getPdsVAddr in *.
  assert(exists vaChild, (* In vaChild getAllVAddr -> *)  
  checkChild partition1 nbL s' vaChild = true /\
  checkChild partition1 nbL s vaChild= false).
  { clear H0.
    revert H1.
    induction getAllVAddrWithOffset0.
    simpl.
    intros. now contradict H1.
    simpl.
    intros.
    case_eq (checkChild partition1 nbL s' a); intros;
    rewrite H0 in *. 
    + case_eq(checkChild partition1 nbL s a);intros; rewrite H2 in *.
      - apply IHl. 
        unfold not;intros.
        apply H1;trivial.
        f_equal;trivial.
      - exists a;split;trivial.
    + case_eq(checkChild partition1 nbL s a);intros; rewrite H2 in *.
      - assert(checkChild partition1 nbL s' a = true).
        apply addPartitionKeepsAllChildren;trivial.
        rewrite H3 in *.
        now contradict H0.
      - apply IHl;trivial. } 
  clear H1. 
  clear H0.
  induction getAllVAddrWithOffset0.
  simpl;trivial.
  simpl.
  intros.
  case_eq(checkChild partition2 nbL s a);intros.
  + case_eq (checkChild partition2 nbL s' a);intros.
    - f_equal;trivial.
    - destruct H2 as (vaChild & Hvatrue & Hvafalse).
      assert( checkChild partition2 nbL s' a = true).
      apply addPartitionKeepsAllChildren;trivial.
      rewrite H2 in H1.
      now contradict H1.
  + case_eq (checkChild partition2 nbL s' a);intros;trivial.
    destruct H2 as (vaChild & Hvatrue & Hvafalse).
    assert(checkChild partition2 nbL s' a = false).
    { apply addPartitionAddSingleChild with partition1 vaChild;trivial.
    unfold not;intros;subst; now contradict H. }
    rewrite H2 in *.
    now contradict H1. }    
rewrite <- H2.
unfold getMappedPagesOption.
f_equal.
clear H0 H1 H2.
induction (getPdsVAddr partition2 nbL getAllVAddrWithOffset0 s).
simpl;trivial.
simpl.
f_equal;trivial.
apply getMappedPageAddDerivation with entry;trivial.
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
Lemma getPartitionAuxSplitListNewSate' entry table descChild 
(newPartition ptRefChild currentShadow1 currentPD : page)  parent s:
parentInPartitionList s -> 
multiplexerWithoutParent s -> 
noDupPartitionTree s -> 
isParent s -> 
isChild s -> 
noCycleInPartitionTree s -> 
verticalSharing s -> 
partitionsIsolation s -> 
In parent (getPartitions multiplexer s) -> 
configTablesAreDifferent s -> 
partitionDescriptorEntry s -> 
noDupMappedPagesList s -> 
noDupConfigPagesList s -> 
In parent (getPartitions multiplexer s) -> 
isPartitionFalse table (StateLib.getIndexOfAddr descChild fstLevel) s -> 
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s -> 
nextEntryIsPP parent PDidx currentPD s -> 
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx parent descChild s )-> 
(defaultPage =? ptRefChild) = false -> 
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) newPartition s ->
nextEntryIsPP parent sh1idx currentShadow1 s ->
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isVE table idx s /\ getTableAddrRoot table sh1idx parent descChild s ) -> 
(defaultPage =? table) = false -> 
lookup table (StateLib.getIndexOfAddr descChild fstLevel) (memory s) beqPage beqIndex =
Some (VE entry) -> 
In descChild getAllVAddrWithOffset0 -> 
~ In newPartition (getChildren parent s) -> 
In newPartition
  (getChildren parent
     {|
     currentPartition := currentPartition s;
     memory := add table (StateLib.getIndexOfAddr descChild fstLevel)
                 (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}) -> 
let s' := {|
   currentPartition := currentPartition s;
   memory := add table (StateLib.getIndexOfAddr descChild fstLevel) (VE {| pd := true; va := va entry |})
               (memory s) beqPage beqIndex |} in
In parent (getPartitions multiplexer s') -> 
exists size l1 l2,
getPartitionAux multiplexer s (nbPage +1) = l1 ++ [parent] ++
flat_map (fun p => getPartitionAux p s  size )
(getChildren parent s)++ l2
/\
getPartitionAux multiplexer s' (nbPage +1)  = l1 ++ [parent] ++
flat_map (fun p => getPartitionAux p s' size  )
(getChildren parent s')++ l2 .
Proof.
intros Hparentintree Hmultnone Hnoduptree Hisparent HisChild Hnocycle Hvs Hiso Hparentpart Hconfigsdiff Hpde Hnodupmap Hnodupconfig Hpart  Hnotpart Hpresent (* Hpart *) 
Hpppd HgetA Hnotnull Hentry Hsh1 Hpp Hpp1  Hlookup Hnewhyp Hnotinp Hinp s' HparentS.
assert(Hchildren : exists  l1 l2,
getChildren parent s' = l1 ++ [newPartition] ++ l2 /\
getChildren parent s = l1 ++l2).
unfold s'.
apply getChildrenSplitList with ptRefChild currentShadow1 currentPD; trivial.
(* clear Hpde Hnodupmap Hnodupconfig   Hnotpart Hpresent (* Hpart *) 
Hpppd HgetA Hnotnull Hentry Hsh1 Hpp Hpp1   Hnotin Hin.  *)
destruct Hchildren as (li1 & li2 & HchildS & Hchild).
simpl.
unfold getPartitions in Hpart.
revert Hpart.
assert(Hmult : In multiplexer (getPartitions multiplexer s)).
{ unfold getPartitions.
  replace (nbPage+1) with (1+nbPage) by omega.
  simpl;left;trivial. } 
revert Hmult.
generalize multiplexer at 1 3 4 5 as mult.
(* intros mult Hmult. *)
(*assert(HnbPage : nbPage+1 >= nbPage+1) by omega.
revert HnbPage.
generalize nbPage at 1 3 4 5 as nbpage.
intros nbpage.  *) 
induction (nbPage+1) as [ | n IH ].
contradiction.
intros (* Hnbpage *) mult Hmult  [Heq | Hin].
- subst mult.
  exists  n, [], [].
  do 2 rewrite app_nil_l, app_nil_r.
  simpl.
 replace (n - 0) with n; [ | rewrite Nat.sub_0_r; trivial ].
  split; trivial.
- apply in_flat_map in Hin; destruct Hin as (multichld & Hin & IH').
destruct IH with multichld as (nbPPc & l1c & l2c & eqlc & eqrc);trivial.

apply childrenPartitionInPartitionList with mult;trivial. 
  apply in_split in Hin as (l11 & l22 & eqchld).
  set (l1 := mult :: flat_map (fun p : page => getPartitionAux p s n) l11 ++ l1c).
  set (l2 := l2c ++ flat_map (fun p : page => getPartitionAux p s n) l22).
  exists nbPPc, l1, l2.
  simpl.
  split.
  + f_equal.
    rewrite eqchld.
    rewrite <- app_assoc.
    rewrite flat_map_app_cons.
    f_equal.
    simpl.
    rewrite app_nil_r.
    rewrite eqlc.
    rewrite <- app_assoc; f_equal.
    rewrite <- app_comm_cons.
    f_equal.
    rewrite <- app_assoc.
    trivial.
  + f_equal.
    assert (Hmultparent : mult <> multichld ).
    { unfold noCycleInPartitionTree in *.
      apply Hnocycle;trivial.
      apply childrenPartitionInPartitionList with mult;trivial.
      rewrite eqchld.
      rewrite in_app_iff;right;simpl;left;trivial.
      unfold getAncestors.
      unfold isParent in *.
      assert (Hparent : getParent multichld (memory s) = Some mult ).
      apply Hisparent;trivial.
      rewrite eqchld.
      rewrite in_app_iff;simpl;right;simpl;left;trivial.     
      destruct nbPage;simpl;rewrite Hparent;simpl;left;trivial. }    
    assert (eqp: getChildren mult s' = getChildren mult s).
    {  
      fold s' in Hinp.
      assert(Hor : parent = multichld \/ parent <> multichld) by apply pageDecOrNot.
      destruct Hor as [Hor | Hor].
      - subst.  clear IH eqlc eqrc IH'.
        apply addPartitionGetChildrenEq with multichld;trivial.  intuition.
        fold s'.
        rewrite HchildS.
        rewrite Hchild.  
        clear.
        simpl.
        apply app_cons_not.
      -  apply addPartitionGetChildrenEq with parent;trivial.

assert(mult = parent \/ mult <> parent) by apply pageDecOrNot.
destruct H;subst.
assert(In multichld ( getChildren parent s)).
rewrite eqchld.
rewrite in_app_iff.
right;simpl;left;trivial.
assert(Hfalse :  StateLib.getParent multichld (memory s)= Some parent). 
{ unfold isParent in *.
  apply Hisparent;trivial. }
unfold not; intros.
assert(Htrue : ~ In parent (getPartitionAux multichld s n)).
 
 apply noCycleInPartitionTree2;trivial.
 now contradict Htrue.
 intuition. 
        fold s'.
        rewrite HchildS.
        rewrite Hchild.
        simpl.
        clear.
        apply app_cons_not. }
(*       assert (In parent (getMappedPages multichld s)).
      { apply premierLemmePoseAvecSam with n;trivial.
        apply childrenPartitionInPartitionList with mult;trivial.
        rewrite eqchld.
        rewrite in_app_iff;right;simpl;left;trivial. 
      
    } *)
    rewrite eqp, eqchld.
    rewrite flat_map_app_cons.
    simpl.
    replace (getPartitionAux multichld s' n ++ []) with 
     (getPartitionAux multichld s' n) ; [|intuition].
    rewrite eqrc.
    replace ((flat_map (fun p : page => getPartitionAux p s n) l11 ++ l1c) ++
      parent :: flat_map (fun p : page => getPartitionAux p s' (nbPPc )) (getChildren parent s') ++ l2
      ) with (flat_map (fun p : page => getPartitionAux p s n) l11 ++ l1c ++
      parent :: flat_map (fun p : page => getPartitionAux p s' (nbPPc)) (getChildren parent s') ++ l2
      ); [| intuition].
      assert (Hchildintree : forall child , In child (getChildren mult s) -> 
      In child (getPartitions multiplexer s)).
      intros.
      apply childrenPartitionInPartitionList with mult;trivial.
    f_equal.
    * assert(Hiso2 : ~In parent (flat_map (fun p : page => getPartitionAux p s n) l11)). (**Isolation**) 
      {
      assert(Hor : parent = multichld \/ parent <> multichld) by apply pageDecOrNot. 
      destruct Hor as [Hor | Hor].
      + (* clear Hor.  *) subst. clear IH HgetA Hinp Hpp l1 l2. 
        assert(Hnodupchild : NoDup (getChildren mult s)).
        { rewrite <- eqp.
          unfold getChildren.
          case_eq (StateLib.getNbLevel );[intros nbL HnbL | intros HnbL];
          [|constructor]. 
          case_eq (StateLib.getPd mult (memory s') );[intros pd Hpd | intros Hpd];
          [|constructor].
          apply addPartitionGetChildrenNoDup;trivial.
          fold s'.
          assert(Hmappedaux : getMappedPagesAux pd getAllVAddrWithOffset0 s' =
          getMappedPagesAux pd getAllVAddrWithOffset0 s).
          apply getMappedPagesAuxAddDerivation with entry;trivial.
          rewrite Hmappedaux. clear Hmappedaux.
          unfold noDupMappedPagesList in Hnodupmap.
          move Hnodupmap at bottom.
          unfold getMappedPages in Hnodupmap.
          apply Hnodupmap in Hmult. clear Hnodupmap.
          assert ( HpdS : StateLib.getPd mult (memory s') =
          StateLib.getPd mult (memory s)).
          apply getPdAddDerivation with entry;trivial.
          rewrite HpdS in *. clear HpdS.
          rewrite Hpd in *;trivial. }
        rewrite eqchld in Hnodupchild.
        clear Hchildintree    Hpde Hnodupmap Hnodupconfig   Hnotpart Hpresent (* Hpart *) 
            Hpppd  Hnotnull Hentry Hsh1  Hpp1 eqlc eqrc.
        clear IH'.
        rewrite in_flat_map .
        unfold not;intros Hfalse.
        destruct Hfalse as (sister & Hsister1 & Hsister2).
        assert(In multichld (getMappedPages sister s)).
        apply premierLemmePoseAvecSam with n;trivial.
        apply childrenPartitionInPartitionList with mult;trivial.
        rewrite eqchld. 
        rewrite in_app_iff.
        left;trivial.
        apply NoDup_remove_2 in Hnodupchild.
        rewrite in_app_iff in *.
        apply Classical_Prop.not_or_and in Hnodupchild.
        intuition.
        subst.
        apply H0;trivial.
        unfold partitionsIsolation in *.
        unfold disjoint in *.
        unfold not in Hiso.
        apply Hiso with mult multichld sister multichld;trivial.
        rewrite eqchld.
        rewrite in_app_iff;right;simpl;left;trivial.
        rewrite eqchld.
        rewrite in_app_iff;simpl;left;trivial.
        apply NoDup_remove_2 in Hnodupchild.
        rewrite in_app_iff in *.
        apply Classical_Prop.not_or_and in Hnodupchild.
        intuition.
        subst.
        apply H1;trivial.
        unfold getUsedPages.
        rewrite in_app_iff.
        left.
        unfold getConfigPages.
        simpl;left;trivial.
        unfold getUsedPages.
        rewrite in_app_iff; right;trivial.
      + assert(Hinparent : In parent (getPartitionAux multichld s n) ).
       { rewrite eqlc. rewrite in_app_iff. right. simpl;left;trivial. }
       assert (In parent (getMappedPages multichld s)).
       {  apply premierLemmePoseAvecSam with n; trivial.
          apply childrenPartitionInPartitionList with mult;trivial.
          rewrite eqchld. 
          rewrite in_app_iff.
          right;simpl;left;trivial.
            }
        clear l1 l2.             
        rewrite in_flat_map.
        unfold not;intros.
        destruct H0 as (sister & Hsister1 & Hsister2). 
        contradict Hsister2.
        unfold not;intros.  
        assert(In parent (getMappedPages sister s)). 
        { apply premierLemmePoseAvecSam with n; trivial.
          apply childrenPartitionInPartitionList with mult;trivial.
          rewrite eqchld. rewrite in_app_iff;left;trivial.
          unfold not. intros.
          unfold partitionsIsolation in *. 
          unfold disjoint in *.
          unfold not in Hiso.     
          subst.
          apply Hiso with mult multichld sister sister;trivial.
          clear IH.
          rewrite eqchld.
          rewrite in_app_iff;right;simpl; left;trivial.
          rewrite eqchld.
          rewrite in_app_iff; left;trivial.
          intuition.
          unfold getUsedPages.
          rewrite in_app_iff.
          right;trivial.
          unfold getUsedPages.
          rewrite in_app_iff;left.
          unfold getConfigPages.
          simpl;left;trivial. }
        move Hiso at bottom.
        unfold partitionsIsolation in *. 
        unfold disjoint in *.
        unfold not in Hiso.     
        apply Hiso with mult multichld sister parent;trivial. 
        rewrite eqchld.
        rewrite in_app_iff. right;simpl;left;trivial.
        rewrite eqchld.
        rewrite in_app_iff. left;trivial.
        assert (Hnodupchild : NoDup (l11 ++ multichld :: l22)).
        rewrite <- eqchld.
        { rewrite <- eqp.
          unfold getChildren.
          case_eq (StateLib.getNbLevel );[intros nbL HnbL | intros HnbL];
          [|constructor]. 
          case_eq (StateLib.getPd mult (memory s') );[intros pd Hpd | intros Hpd];
          [|constructor].
          apply addPartitionGetChildrenNoDup;trivial.
          fold s'.
          assert(Hmappedaux : getMappedPagesAux pd getAllVAddrWithOffset0 s' =
          getMappedPagesAux pd getAllVAddrWithOffset0 s).
          apply getMappedPagesAuxAddDerivation with entry;trivial.
          rewrite Hmappedaux. clear Hmappedaux.
          unfold noDupMappedPagesList in Hnodupmap.
          move Hnodupmap at bottom.
          unfold getMappedPages in Hnodupmap.
          apply Hnodupmap in Hmult. clear Hnodupmap.
          assert ( HpdS : StateLib.getPd mult (memory s') =
          StateLib.getPd mult (memory s)).
          apply getPdAddDerivation with entry;trivial.
          rewrite HpdS in *. clear HpdS.
          rewrite Hpd in *;trivial. }
        apply NoDup_remove_2 in Hnodupchild.
        rewrite in_app_iff in *.
        apply Classical_Prop.not_or_and in Hnodupchild.
        intuition.
        subst.
        apply H3;trivial.
        unfold getUsedPages.
        rewrite in_app_iff.
        right;trivial.
        unfold getUsedPages.
        rewrite in_app_iff.
        right;trivial. }
      assert(Hl11intree : forall child, In child l11 -> In child (getPartitions multiplexer s)).
      { intros.
        apply Hchildintree;trivial.
        rewrite eqchld .
        rewrite in_app_iff.
        left;trivial. }
      clear Hchildintree eqchld l1.
      induction l11.
      simpl;trivial.
       
      simpl in *.
      f_equal. 
      symmetry.
      apply deuxiemeLemmePoseAvecSam with newPartition ptRefChild currentShadow1 
        currentPD parent;
      trivial.
      apply  Hl11intree.
      left;trivial.
      rewrite in_app_iff in Hiso2.
      intuition.
      apply IHl11.
      simpl in *.
      rewrite in_app_iff in Hiso2.
      intuition.
      intros.
      apply Hl11intree.
      right;trivial.
    * assert(Hiso2 : ~In parent (flat_map (fun p : page => getPartitionAux p s n) l22)). (**Isolation**) 
      {
      assert(Hor : parent = multichld \/ parent <> multichld) by apply pageDecOrNot. 
      destruct Hor as [Hor | Hor].
      + subst. clear IH HgetA Hinp Hpp l1 l2. 
        assert(Hnodupchild : NoDup (getChildren mult s)).
        { rewrite <- eqp.
          unfold getChildren.
          case_eq (StateLib.getNbLevel );[intros nbL HnbL | intros HnbL];
          [|constructor]. 
          case_eq (StateLib.getPd mult (memory s') );[intros pd Hpd | intros Hpd];
          [|constructor].
          apply addPartitionGetChildrenNoDup;trivial.
          fold s'.
          assert(Hmappedaux : getMappedPagesAux pd getAllVAddrWithOffset0 s' =
          getMappedPagesAux pd getAllVAddrWithOffset0 s).
          apply getMappedPagesAuxAddDerivation with entry;trivial.
          rewrite Hmappedaux. clear Hmappedaux.
          unfold noDupMappedPagesList in Hnodupmap.
          move Hnodupmap at bottom.
          unfold getMappedPages in Hnodupmap.
          apply Hnodupmap in Hmult. clear Hnodupmap.
          assert ( HpdS : StateLib.getPd mult (memory s') =
          StateLib.getPd mult (memory s)).
          apply getPdAddDerivation with entry;trivial.
          rewrite HpdS in *. clear HpdS.
          rewrite Hpd in *;trivial. }
        rewrite eqchld in Hnodupchild.
        clear Hchildintree    Hpde Hnodupmap Hnodupconfig   Hnotpart Hpresent (* Hpart *) 
            Hpppd  Hnotnull Hentry Hsh1  Hpp1 eqlc eqrc.
        clear IH'.
        rewrite in_flat_map .
        unfold not;intros Hfalse.
        destruct Hfalse as (sister & Hsister1 & Hsister2).
        assert(In multichld (getMappedPages sister s)).
        apply premierLemmePoseAvecSam with n;trivial.
        apply childrenPartitionInPartitionList with mult;trivial.
        rewrite eqchld. 
        rewrite in_app_iff.
        right;simpl;right;trivial.
        apply NoDup_remove_2 in Hnodupchild.
        rewrite in_app_iff in *.
        apply Classical_Prop.not_or_and in Hnodupchild.
        intuition.
        subst.
        apply H1;trivial.
        unfold partitionsIsolation in *.
        unfold disjoint in *.
        unfold not in Hiso.
        apply Hiso with mult multichld sister multichld;trivial.
        rewrite eqchld.
        rewrite in_app_iff;right;simpl;left;trivial.
        rewrite eqchld.
        rewrite in_app_iff;simpl;right;simpl;right;trivial.
        apply NoDup_remove_2 in Hnodupchild.
        rewrite in_app_iff in *.
        apply Classical_Prop.not_or_and in Hnodupchild.
        intuition.
        subst.
        apply H2;trivial.
        unfold getUsedPages.
        rewrite in_app_iff.
        left.
        unfold getConfigPages.
        simpl;left;trivial.
        unfold getUsedPages.
        rewrite in_app_iff; right;trivial.
      + assert(Hinparent : In parent (getPartitionAux multichld s n) ).
       { rewrite eqlc. rewrite in_app_iff. right. simpl;left;trivial. }
       assert (In parent (getMappedPages multichld s)).
       {  apply premierLemmePoseAvecSam with n; trivial.
          apply childrenPartitionInPartitionList with mult;trivial.
          rewrite eqchld. 
          rewrite in_app_iff.
          right;simpl;left;trivial.
            }
        clear l1 l2.             
        rewrite in_flat_map.
        unfold not;intros.
        destruct H0 as (sister & Hsister1 & Hsister2). 
        contradict Hsister2.
        unfold not;intros.  
        assert(In parent (getMappedPages sister s)). 
        { apply premierLemmePoseAvecSam with n; trivial.
          apply childrenPartitionInPartitionList with mult;trivial.
          rewrite eqchld.
          rewrite in_app_iff;right;simpl;right;trivial.
          unfold not. intros.
          unfold partitionsIsolation in *. 
          unfold disjoint in *.
          unfold not in Hiso.     
          subst.
          apply Hiso with mult multichld sister sister;trivial.
          clear IH.
          rewrite eqchld.
          rewrite in_app_iff;right;simpl; left;trivial.
          rewrite eqchld.
          rewrite in_app_iff;right;simpl;right;trivial.
          intuition.
          unfold getUsedPages.
          rewrite in_app_iff.
          right;trivial.
          unfold getUsedPages.
          rewrite in_app_iff;left.
          unfold getConfigPages.
          simpl;left;trivial. }
        move Hiso at bottom.
        unfold partitionsIsolation in *. 
        unfold disjoint in *.
        unfold not in Hiso.     
        apply Hiso with mult multichld sister parent;trivial. 
        rewrite eqchld.
        rewrite in_app_iff. right;simpl;left;trivial.
        rewrite eqchld.
        rewrite in_app_iff;right;simpl;right;trivial.
        assert (Hnodupchild : NoDup (l11 ++ multichld :: l22)).
        rewrite <- eqchld.
        { rewrite <- eqp.
          unfold getChildren.
          case_eq (StateLib.getNbLevel );[intros nbL HnbL | intros HnbL];
          [|constructor]. 
          case_eq (StateLib.getPd mult (memory s') );[intros pd Hpd | intros Hpd];
          [|constructor].
          apply addPartitionGetChildrenNoDup;trivial.
          fold s'.
          assert(Hmappedaux : getMappedPagesAux pd getAllVAddrWithOffset0 s' =
          getMappedPagesAux pd getAllVAddrWithOffset0 s).
          apply getMappedPagesAuxAddDerivation with entry;trivial.
          rewrite Hmappedaux. clear Hmappedaux.
          unfold noDupMappedPagesList in Hnodupmap.
          move Hnodupmap at bottom.
          unfold getMappedPages in Hnodupmap.
          apply Hnodupmap in Hmult. clear Hnodupmap.
          assert ( HpdS : StateLib.getPd mult (memory s') =
          StateLib.getPd mult (memory s)).
          apply getPdAddDerivation with entry;trivial.
          rewrite HpdS in *. clear HpdS.
          rewrite Hpd in *;trivial. }
        apply NoDup_remove_2 in Hnodupchild.
        rewrite in_app_iff in *.
        apply Classical_Prop.not_or_and in Hnodupchild.
        intuition.
        subst.
        apply H4;trivial.
        unfold getUsedPages.
        rewrite in_app_iff.
        right;trivial.
        unfold getUsedPages.
        rewrite in_app_iff.
        right;trivial. }
        unfold l2.
      rewrite <- app_assoc;f_equal.
      symmetry.
      rewrite <- app_comm_cons.
      f_equal.
      rewrite <- app_assoc_reverse;f_equal.
      assert(Hl11intree : forall child, In child l22 -> In child (getPartitions multiplexer s)).
      { intros.
        apply Hchildintree;trivial.
       rewrite eqchld .
       rewrite in_app_iff.
       right;simpl;right;trivial. }
      clear Hchildintree eqchld l2.
      induction l22.
      simpl;trivial.
      simpl.
      f_equal.
      symmetry.
      unfold s'.
      symmetry.
      apply deuxiemeLemmePoseAvecSam with 
            newPartition ptRefChild currentShadow1 currentPD parent;
      trivial.   
      apply  Hl11intree.
      left;trivial.
      simpl in *.
      rewrite in_app_iff in Hiso2.
      intuition. 
      apply IHl22.
      simpl in *. (* 
      rewrite in_app_iff in Hiso1.
      intuition.
      simpl in *. *)
      rewrite in_app_iff in Hiso2.
      intuition. 
      intros.
      apply Hl11intree.
      right;trivial.
Qed.

Lemma addPartitionAddsSinglePartition  parent
entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
noDupMappedPagesList s ->
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             {|
             currentPartition := currentPartition s;
             memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                         (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}) ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s  -> 
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *)
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   

parent <> currentPart ->
parent <> phyDescChild -> 
In parent(getPartitions multiplexer s') -> 

(* 
parent currentPD currentPart ptRefChild ptRefChildFromSh1 phyDescChild descChild
entry  level s: 
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isPartitionFalse ptRefChildFromSh1
             (StateLib.getIndexOfAddr descChild fstLevel) s -> 
(forall idx : index,
        StateLib.getIndexOfAddr descChild fstLevel = idx ->
        isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s )-> 
(defaultPage =? ptRefChild) = false -> 
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s -> 
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s -> 

Some level = StateLib.getNbLevel -> 
nextEntryIsPP currentPart PDidx currentPD s ->  *)
In descChild getAllVAddrWithOffset0 -> 
In parent (getPartitions multiplexer s).
Proof.
intros s' HisParent Hcons Hiso Hvs Hpde Hnodupconf Hnodupmap Hlookup Hppsh3 Hppsh2 Hppsh1 Hpppd Hcurpart Hlevel HcurrentPD Hpost
Hnewpd Hnewsh1 Hnewsh2 Hnewsh31 (* Hnewsh32 Hnewsh33 *) HmappedDesc
HmappedPD Hmappedsh1 HmappedSh2 Hmappedsh3 Hnotconfig Hroot Hptnotnull Hep
Hpresent Hfstsh1 Hnotpart Hsh1 Hptsh1notnull
HphyPDcontent HphySh1content HphySh2content (*HphyListcontent1 HphyListcontent2 HphyListcontent3  *)
HnotConfig HnotConfig1 HnotConfig2 HnotConfig3 HnotConfig4
Ha1 Ha2 Ha3 Ha4 Ha5 .
intros Hparteq Hparentnotchild Hvs1 Hnewphy. 
assert(Hphynotchild : ~ In phyDescChild (getChildren currentPart s)).
    { assert(getMappedPage currentPD s descChild = SomePage phyDescChild /\
      ~ In descChild (getPdsVAddr currentPart level getAllVAddrWithOffset0 s)) as ( Hvaphy' & Hpds1).
      { split.
        + apply getMappedPageGetTableRoot with ptRefChild currentPart;trivial.
        + unfold isPartitionFalse in *.
          move Hnotpart at bottom.
          unfold getPdsVAddr.
          rewrite filter_In.
          apply Classical_Prop.or_not_and.
          right.
          unfold checkChild.
          rewrite nextEntryIsPPgetFstShadow in *.
          rewrite Hfstsh1.
          assert(getIndirection currentShadow1 descChild level (nbLevel - 1) s = Some ptRefChildFromSh1).
          apply getIndirectionGetTableRoot with currentPart;trivial.
          symmetry;trivial.
          rewrite H.
          destruct  (ptRefChildFromSh1 =? defaultPage);trivial.
          auto.
          destruct Hnotpart; rewrite H0;auto. }
     
      unfold getChildren.
      rewrite <- Hlevel.
      rewrite nextEntryIsPPgetPd in *.
      rewrite HcurrentPD.
      unfold getMappedPagesAux.
      rewrite filterOptionInIff.
      unfold getMappedPagesOption.
      rewrite in_map_iff.
      unfold not.
      intros.
      destruct H as (samev & Hi & Hii).
      assert(descChild = samev).
      apply eqMappedPagesEqVaddrs with phyDescChild currentPD s;trivial.
      unfold getPdsVAddr in *. 
      apply filter_In in Hii.
      intuition.
      unfold consistency in *.
      assert(noDupMappedPagesList s) by intuition.
      unfold noDupMappedPagesList in *.
      apply H in Hcurpart. clear H.
      move Hcurpart at bottom.
      unfold getMappedPages in Hcurpart.
      rewrite HcurrentPD in *.
      unfold getMappedPagesAux  in *.
      unfold getMappedPagesOption in Hcurpart;trivial.
      subst.
      now contradict Hpds1. }
 assert(Hkey : In parent (getPartitions multiplexer s)). 
 {  assert (Hsplitlist : exists size l1 l2,
          getPartitionAux multiplexer s (nbPage +1) = l1 ++ [currentPart] ++
          flat_map (fun p => getPartitionAux p s size)
          (getChildren currentPart s)++ l2
          /\
          getPartitionAux multiplexer s' (nbPage +1)  = l1 ++ [currentPart] ++
          flat_map (fun p => getPartitionAux p s' size  )
          (getChildren currentPart s')++ l2 ).
  { unfold consistency in *.
    apply getPartitionAuxSplitListNewSate' with phyDescChild ptRefChild currentShadow1
     currentPD;intuition.

    apply addPartitionKeepsAllPartitionsInTree;trivial. }
  destruct Hsplitlist as (nbPagesParent & l11 & l22 & Hsplitlist).
  destruct Hsplitlist.
  unfold getPartitions in *.
  rewrite H;clear H.
  rewrite H0 in *;clear H0. 
  simpl in *.
  rewrite in_app_iff in *.
  destruct Hvs1 as [Hparent | Hparent]; [left;trivial|].
  right.
  simpl in *.
  destruct Hparent as [Hparent | Hparent];[left;trivial|].
  right.
  rewrite in_app_iff in *.
  destruct Hparent as [Hparent | Hparent];[ | right;trivial].
  left.
  unfold consistency in *.
  assert(HchildrenS : exists l1 l2,
  getChildren currentPart s' = l1 ++ [phyDescChild] ++ l2 /\
  getChildren currentPart s = l1 ++l2).
  apply getChildrenSplitList with ptRefChild currentShadow1 currentPD; intuition.
  destruct HchildrenS as (l1 & l2 & HchildrenS & Hchildrenprev).
  assert(Hl1 : incl l1 (getChildren currentPart s)).
  { unfold incl.
    intros.
    rewrite Hchildrenprev.
    rewrite in_app_iff;left;trivial. }
   assert(Hl22 : incl l2 (getChildren currentPart s)).
  { unfold incl.
    intros.
    rewrite Hchildrenprev.
    rewrite in_app_iff;right;trivial. }  
  rewrite  HchildrenS in Hparent.
  rewrite  Hchildrenprev . 
  simpl in Hparent.
  rewrite flat_map_app_cons in Hparent.
  rewrite flat_map_app.
  rewrite in_app_iff in *.
  simpl in *.
  assert(Hzero : getPartitionAux phyDescChild s' nbPagesParent = [phyDescChild] \/
  getPartitionAux phyDescChild s' nbPagesParent  = [] ).
  {clear Hparent.
  induction (nbPagesParent ).
  simpl.
  right;trivial.
  simpl. left.
   assert (Hchildrennil : getChildren phyDescChild s' = nil).
   { assert(forall partition s, (* In partition (getPartitions multiplexer s)
              ->  *) incl (getChildren partition s) (getMappedPages partition s)).
      { intros.
        unfold incl.
        unfold getChildren.
        unfold getMappedPages.
        intros.
        destruct (StateLib.getNbLevel ); try now contradict H0.
        destruct  (StateLib.getPd partition (memory s0)); try now contradict H0.
        unfold getMappedPagesAux in *.
        rewrite filterOptionInIff in *.
        unfold getMappedPagesOption in *.
        rewrite in_map_iff in *.
        destruct H as (x & H & Hx).
        clear IHn.
        exists x;split;trivial.
        unfold getPdsVAddr in Hx.
        apply filter_In in Hx.
        intuition. intuition. intuition. }
     assert(Hmappednull : getMappedPages phyDescChild s' = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        (** we have an hypothesis **)
        rewrite getPdAddDerivation with phyDescChild  (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel)
        s entry true ;trivial.
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial.
        split;simpl.
        rewrite readPhyEntryAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        rewrite readPresentAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        (** PropagatedProperties : forall idx : index,
            StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
            StateLib.readPresent phyPDChild idx (memory s) = Some false **) }
            assert(Hbb1 :  forall (partition : page) (s : state) (a : page),
      In a (getChildren partition s) -> In a (getMappedPages partition s)) by trivial.
     generalize (Hbb1  phyDescChild s'); clear Hbb1; intros Hbb1.
     rewrite Hmappednull in *.
     destruct (getChildren phyDescChild s') .
     trivial. 
     assert(In p []).
     apply Hbb1.
     simpl;left;trivial. contradiction.
      }
  rewrite Hchildrennil;simpl;trivial.   
  }
  assert( In parent (flat_map (fun p : page => getPartitionAux p s' (nbPagesParent )) l1) \/
          In parent
            (
             flat_map (fun p : page => getPartitionAux p s' (nbPagesParent )) l2)).
  { destruct Hzero as [Hzero | Hzero]; rewrite Hzero in *; simpl in *.
    +
    destruct Hparent as [Hparent | [ Hparent | Hparent]] .
    left;trivial.
    subst parent;now contradict Hparentnotchild.
    right;trivial.
    + trivial.
    }
clear Hparent Hzero.
  rename H into Hparent.
  destruct Hparent as [Hparent | Hparent] .
  ++ left.
     rewrite in_flat_map in *.
     destruct Hparent as (childx & Hancestor1 & Hancestor2).
     exists childx;split;trivial.
     assert( getPartitionAux childx s (nbPagesParent ) = 
     getPartitionAux childx s' (nbPagesParent )).
     { unfold consistency in *.
       intuition.
        apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
        apply childrenPartitionInPartitionList with currentPart;trivial.
        rewrite Hchildrenprev.
        rewrite in_app_iff.
        left;trivial.
        apply noCycleInPartitionTree2;trivial.
        unfold incl in Hl1.
        rewrite Hchildrenprev in *.
        apply in_app_iff.
        left;trivial. }
      trivial.
   rewrite H;trivial.
  ++ right.
     rewrite in_flat_map in *.
     destruct Hparent as (childx & Hancestor1 & Hancestor2).
     exists childx;split;trivial.
     assert( getPartitionAux childx s (nbPagesParent ) = 
     getPartitionAux childx s' (nbPagesParent )).
     { unfold consistency in *.
       intuition.
        apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
        apply childrenPartitionInPartitionList with currentPart;trivial.
        rewrite Hchildrenprev.
        rewrite in_app_iff.
        right;trivial.
        apply noCycleInPartitionTree2;trivial.
        unfold incl in Hl1.
        rewrite Hchildrenprev in *.
        apply in_app_iff.
        right;trivial. }
   rewrite H;trivial.
     }
     trivial.
Qed.

Lemma partitionsIsolationAddChild currentPart ptRefChild  phyDescChild ptRefChildFromSh1 
descChild entry level currentPD s  currentShadow1 phyPDChild phySh1Child phySh2Child phyConfigPagesList :
isParent s -> 
verticalSharing s -> 
consistency s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
(forall idx : index,
      StateLib.getIndexOfAddr descChild fstLevel = idx ->
      isPE ptRefChild idx s /\
      getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
( forall idx : index,
      StateLib.getIndexOfAddr descChild fstLevel = idx ->
      isVE ptRefChildFromSh1 idx s /\
      getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s )->
      (defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
initConfigPagesListPostCondition phyConfigPagesList s -> 
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
In phyDescChild (getChildren currentPart{|
  currentPartition := currentPartition s;
  memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
   (VE {| pd := true; va := va entry |})
              (memory s) beqPage beqIndex |}) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
partitionsIsolation s ->
In descChild getAllVAddrWithOffset0 -> 
partitionsIsolation {|
  currentPartition := currentPartition s;
  memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros HisParent Hvs Hcons Hnotpart Hppsh3 Hppsh2 Hppsh1 Hpppd.
intros Hcurpart Hlookup Hlevel Hpd Hroot.
intros Hptnotnull Hep Hpresent Hfstsh1 Hsh1 Hptsh1notnull HphyPDcontent
HphySh1content HphySh2content HphyListcontent(* 1 HphyListcontent2 HphyListcontent3  *)
HnotConfig HnotConfig1 HnotConfig2 HnotConfig3 HnotConfig4
Hpost 
Ha1 Ha2 Ha3 Ha4 Ha5 
 Hiso Hnewphy.
set (s' := {| currentPartition := _|}).
unfold partitionsIsolation in *.
intros parent child1 child2 Hparent Hchild1 Hchild2 Hchildren.
assert(Hparteq : parent = currentPart \/ parent <> currentPart) by apply pageDecOrNot.
destruct Hparteq as [Hparteq | Hparteq].
(* parent = currentPart *)
  + subst.
    assert(Hchildeq : child1 = phyDescChild \/ child2 = phyDescChild \/
  ( child1 <> phyDescChild /\ child2 <> phyDescChild) ).
  { destruct child1; destruct child2; destruct phyDescChild.
    assert (p = p1 \/ p0 = p1 \/
    (p <> p1 /\ p0 <> p1)) by omega.
    destruct H as [Hi | [Hi |(Hi1 & Hi2) ]].
    + left. subst. f_equal. apply proof_irrelevance.
    + right;left.
      subst. f_equal. apply proof_irrelevance.
    + right;right.
      split;
      unfold not; intros Hfalse;inversion Hfalse; subst; 
      try now contradict Hi1;try now contradict Hi2. }   
    destruct Hchildeq as [Hchild1eq | [Hchild1eq | (Hchild1eq & Hchild2eq)]].
    - (*child1 = phyDescChild*)
      subst.
      unfold s'.
      rewrite getUsedPagesAddDerivation  with phyDescChild (va entry) ptRefChildFromSh1
      (StateLib.getIndexOfAddr descChild fstLevel) entry s true  ;trivial.
      rewrite getUsedPagesAddDerivation  with child2 (va entry) ptRefChildFromSh1
      (StateLib.getIndexOfAddr descChild fstLevel) entry s true  ;trivial.
      unfold getUsedPages at 1.
     (** phyDescChild is the new partition, consequently it mapped pages list is empty **) 
      assert(Hmappednull : getMappedPages phyDescChild s = nil).
      { unfold getMappedPages.
        (** we have an hypothesis **)
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial.
        (** PropagatedProperties : forall idx : index,
            StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
            StateLib.readPresent phyPDChild idx (memory s) = Some false **)
       }  
      rewrite Hmappednull.
      rewrite app_nil_r.
      unfold getConfigPages.
      unfold getConfigPagesAux.
      simpl.
      (** we have an hypothesis **)
      assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
      apply nextEntryIsPPgetPd;trivial.
      rewrite Hpdnewchild.
      simpl.
      (** we have an hypothesis **)
      assert(Hsh1newchild :StateLib.getFstShadow phyDescChild (memory s) = Some phySh1Child).
      apply nextEntryIsPPgetFstShadow;trivial.
      rewrite Hsh1newchild.
      simpl.
      (** we have an hypothesis **)
      assert(Hsh2newchild :StateLib.getSndShadow phyDescChild (memory s) = Some phySh2Child).
      apply nextEntryIsPPgetSndShadow;trivial.
      rewrite Hsh2newchild.
      simpl.
      (** we have an hypothesis **)
      assert(Hlistnewchild :StateLib.getConfigTablesLinkedList phyDescChild (memory s) = Some phyConfigPagesList ).
      apply nextEntryIsPPgetConfigList;trivial.
      rewrite Hlistnewchild.
      (** new partition configuration : replace  *)
      rewrite getIndirectionsOnlyPD;trivial.
      rewrite getIndirectionsOnlySh1 with phySh1Child level s;trivial.
      rewrite getIndirectionsOnlySh2 with phySh2Child level s;trivial.
      rewrite getLLPagesOnlyRoot;trivial.
      unfold s'.
      unfold getUsedPages.
     (** the new partition is phyDescChild and
         it is different from child2 so child2 was into getPartitions of
         the previous state **)
      assert(Htmp : In child2 (getChildren currentPart s)).
      { (** Have to prove this property using
      (forall partition : page,
        In partition (getPartitions multiplexer s) ->
        ~(partition = phyDescChild \/In phyDescChild (getConfigPagesAux partition s))) :
        not a partition implies not a child  **)
        assert(HnewChild : ~ In phyDescChild (getChildren currentPart s)).
        { assert (~ In phyDescChild (getPartitions multiplexer s)).
          { unfold not. intros.
            apply HnotConfig in H.
            contradict H;left;trivial. }         
        unfold not;intros Hfalse; contradict H.
        apply childrenPartitionInPartitionList with currentPart;trivial. 
        unfold consistency in *. intuition. }
        unfold consistency in *.

        apply partitionInPreviousState with
        phyDescChild ptRefChild currentShadow1 currentPD
        s' entry descChild ptRefChildFromSh1;intuition. }
      assert( Hchild2part : In child2 (getPartitions multiplexer s)).
      apply childrenPartitionInPartitionList with currentPart;trivial. 
      unfold consistency in *. intuition. 
      (** * all physical pages are not config pages (already into hypothesis)
          * all physical pages are not mapped into any child 
            (have to prove this before writeVirEntry) @_@ *)
      unfold Lib.disjoint.
      intros apage Hpage.
      simpl in Hpage.
      rewrite in_app_iff.
      apply Classical_Prop.and_not_or.
      split.
      (** * all physical pages are not config pages (already into hypothesis) *)
      unfold getConfigPages.
      simpl.
      destruct Hpage as [H1 |[H1 | [ H1 | [H1 | [ H1 | H1]]]]];
      subst.
      apply HnotConfig;trivial.
      apply HnotConfig1;trivial.
      apply HnotConfig2;trivial.
      apply HnotConfig3;trivial.
      apply HnotConfig4;trivial.
      now contradict H1.
      destruct Hpage as [H1 |[H1 | [ H1 | [H1 | [ H1 | H1]]]]];
      subst.
      apply Ha1;trivial.
      apply Ha2;trivial.
      apply Ha3;trivial.
      apply Ha4;trivial.
      apply Ha5;trivial.
      now contradict H1.
      
    - (** the same as in the previous case **)
      unfold s'.
     (*child2 = phyDescChild*)
      subst.
      apply disjointPermut.
      rewrite getUsedPagesAddDerivation  with child1 (va entry) ptRefChildFromSh1
      (StateLib.getIndexOfAddr descChild fstLevel) entry s true  ;trivial.
      rewrite getUsedPagesAddDerivation  with phyDescChild (va entry) ptRefChildFromSh1
      (StateLib.getIndexOfAddr descChild fstLevel) entry s true  ;trivial. 
      unfold getUsedPages at 1.
     (** phyDescChild is the new partition, consequently it mapped pages list is empty **) 
      assert(Hmappednull : getMappedPages phyDescChild s = nil).
      { unfold getMappedPages.
        (** we have an hypothesis **)
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial. }  
      rewrite Hmappednull.
      rewrite app_nil_r.
      unfold getConfigPages.
      unfold getConfigPagesAux.
      simpl.
      (** we have an hypothesis **)
      assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
      apply nextEntryIsPPgetPd;trivial.
      rewrite Hpdnewchild.
      simpl.
      (** we have an hypothesis **)
      assert(Hsh1newchild :StateLib.getFstShadow phyDescChild (memory s) = Some phySh1Child).
      apply nextEntryIsPPgetFstShadow;trivial.
      rewrite Hsh1newchild.
      simpl.
      (** we have an hypothesis **)
      assert(Hsh2newchild :StateLib.getSndShadow phyDescChild (memory s) = Some phySh2Child).
      apply nextEntryIsPPgetSndShadow;trivial.
      rewrite Hsh2newchild.
      simpl.
      (** we have an hypothesis **)
      assert(Hlistnewchild :StateLib.getConfigTablesLinkedList phyDescChild (memory s) = Some phyConfigPagesList ).
      apply nextEntryIsPPgetConfigList;trivial.
      rewrite Hlistnewchild.
      (** new partition configuration : replace  *)
      rewrite getIndirectionsOnlyPD;trivial.
      rewrite getIndirectionsOnlySh1 with phySh1Child level s;trivial.
      rewrite getIndirectionsOnlySh2 with phySh2Child level s;trivial.
      rewrite getLLPagesOnlyRoot;trivial.
      unfold getUsedPages.
     (** the new partition is phyDescChild and
         it is different from child2 so child2 was into getPartitions of
         the previous state **)
      assert(Htmp : In child1 (getChildren currentPart s)).
      { (** Have to prove this property using
      (forall partition : page,
        In partition (getPartitions multiplexer s) ->
        ~(partition = phyDescChild \/In phyDescChild (getConfigPagesAux partition s))) :
        not a partition implies not a child  **)
        assert(HnewChild : ~ In phyDescChild (getChildren currentPart s)).
        { assert (~ In phyDescChild (getPartitions multiplexer s)).
          { unfold not. intros.
            apply HnotConfig in H.
            contradict H;left;trivial. }         
        unfold not;intros Hfalse; contradict H.
        apply childrenPartitionInPartitionList with currentPart;trivial.
        unfold consistency in *. intuition.  }
        unfold consistency in *.
        apply partitionInPreviousState with
         phyDescChild ptRefChild currentShadow1 currentPD
        s' entry descChild ptRefChildFromSh1;intuition. }
        assert( Hchild2part : In child1 (getPartitions multiplexer s)).
      apply childrenPartitionInPartitionList with currentPart;trivial.
      unfold consistency in *. intuition. 
      (** * all physical pages are not config pages (already into hypothesis)
          * all physical pages are not mapped into any child 
            (have to prove this before writeVirEntry) @_@ *)
      unfold Lib.disjoint.
      intros apage Hpage.
      simpl in Hpage.
      rewrite in_app_iff.
      apply Classical_Prop.and_not_or.
      split.
      (** * all physical pages are not config pages (already into hypothesis) *)
      unfold getConfigPages.
      simpl.
      destruct Hpage as [H1 |[H1 | [ H1 | [H1 | [ H1 | H1]]]]];
      subst.
      apply HnotConfig;trivial.
      apply HnotConfig1;trivial.
      apply HnotConfig2;trivial.
      apply HnotConfig3;trivial.
      apply HnotConfig4;trivial.
      now contradict H1.
      destruct Hpage as [H1 |[H1 | [ H1 | [H1 | [ H1 | H1]]]]];
      subst.
      apply Ha1;trivial.
      apply Ha2;trivial.
      apply Ha3;trivial.
      apply Ha4;trivial.
      apply Ha5;trivial.
      now contradict H1.     
      (* * all physical pages are not mapped into any child 
            (have to prove this before writeVirEntry) @_@
            forall child, In child (getChildren currentPart s), ~ In apage (getMappedPages child s) *) 
    - unfold s'.
     rewrite getUsedPagesAddDerivation  with child2 (va entry) ptRefChildFromSh1
      (StateLib.getIndexOfAddr descChild fstLevel) entry s true  ;trivial.
      rewrite getUsedPagesAddDerivation  with child1 (va entry) ptRefChildFromSh1
      (StateLib.getIndexOfAddr descChild fstLevel) entry s true  ;trivial.
      (** child1 is different from phyDescChild
            so it was into the children list of currentPart in previous state **)
      assert(Hchild1part : In child1  (getChildren currentPart s )).
      { (** Have to prove this property using
      (forall partition : page,
        In partition (getPartitions multiplexer s) ->
        ~(partition = phyDescChild \/In phyDescChild (getConfigPagesAux partition s))) :
        not a partition implies not a child  **)
        assert(HnewChild : ~ In phyDescChild (getChildren currentPart s)).
        { assert (~ In phyDescChild (getPartitions multiplexer s)).
          { unfold not. intros.
            apply HnotConfig in H.
            contradict H;left;trivial. }         
        unfold not;intros Hfalse; contradict H.
        apply childrenPartitionInPartitionList with currentPart;trivial.
        unfold consistency in *. intuition.  }
                unfold consistency in *.
        apply partitionInPreviousState with
         phyDescChild ptRefChild currentShadow1 currentPD
         s' entry descChild ptRefChildFromSh1;intuition. }
       
        (** child2 is different from phyDescChild
            so it was into the children list of currentPart in previous state **)
      assert(Hchild2part : In child2 (getChildren currentPart s )).
      {  (** Have to prove this property using
      (forall partition : page,
        In partition (getPartitions multiplexer s) ->
        ~(partition = phyDescChild \/In phyDescChild (getConfigPagesAux partition s))) :
        not a partition implies not a child  **)
        assert(HnewChild : ~ In phyDescChild (getChildren currentPart s)).
        { assert (~ In phyDescChild (getPartitions multiplexer s)).
          { unfold not. intros.
            apply HnotConfig in H.
            contradict H;left;trivial. }         
        unfold not;intros Hfalse; contradict H.
        apply childrenPartitionInPartitionList with currentPart;trivial.
        unfold consistency in *. intuition.  }
        unfold consistency in *.
        apply partitionInPreviousState with
          phyDescChild ptRefChild currentShadow1 currentPD
          s' entry descChild ptRefChildFromSh1;intuition.  }
        apply Hiso with currentPart;trivial.
+ assert(Hparentnotchild : parent = phyDescChild \/ parent <> phyDescChild ).
{ destruct parent; destruct phyDescChild.
  simpl in *.
  assert(p=p0 \/ p<> p0) by omega.
  destruct H as [Hi | Hi].
  subst.
  left;simpl;f_equal;apply proof_irrelevance.
  right.
  unfold not;intros Hii.
  inversion Hii.
  subst.
  now contradict Hi. }
  destruct Hparentnotchild as [Hparentnotchild | Hparentnotchild].
  - subst.
    assert (Hchildrennil : getChildren phyDescChild
               {|
               currentPartition := currentPartition s;
               memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                           (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} =
                           nil).
   { assert(forall partition s, In partition (getPartitions multiplexer s)
              ->  incl (getChildren partition s) (getMappedPages partition s)).
      { intros.
        unfold incl.
        unfold getChildren.
        unfold getMappedPages.
        intros.
        destruct (StateLib.getNbLevel ); try now contradict H0.
        destruct  (StateLib.getPd partition (memory s0)); try now contradict H0.
        unfold getMappedPagesAux in *.
        rewrite filterOptionInIff in *.
        unfold getMappedPagesOption in *.
        rewrite in_map_iff in *.
        destruct H0 as (x & Hi & Hx).
        exists x;split;intuition.
        unfold getPdsVAddr in *. 
        apply filter_In in Hx; intuition.
        }
     assert(Hmappednull : getMappedPages phyDescChild s' = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        (** we have an hypothesis **)
        rewrite getPdAddDerivation with phyDescChild  (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel)
        s entry true ;trivial.
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial.
        split;simpl.
        rewrite readPhyEntryAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        rewrite readPresentAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        (** PropagatedProperties : forall idx : index,
            StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
            StateLib.readPresent phyPDChild idx (memory s) = Some false **) }
     apply H in Hparent.
     unfold incl in *.
     rewrite Hmappednull in *.
fold s'.
     destruct (getChildren phyDescChild s') .
     trivial.
     assert(In p []).
     apply Hparent.
     simpl;left;trivial.
     now contradict H0. }
     unfold s' in *.
     clear s'.
     set(s' := {|currentPartition := _|}) in *. 
   rewrite Hchildrennil in *.
   now contradict Hchild1.
 - unfold s'.  rewrite getUsedPagesAddDerivation  with child1 (va entry) ptRefChildFromSh1
    (StateLib.getIndexOfAddr descChild fstLevel) entry s true  ;trivial.
   rewrite getUsedPagesAddDerivation  with child2 (va entry) ptRefChildFromSh1
    (StateLib.getIndexOfAddr descChild fstLevel) entry s true  ;trivial.
assert(Hphynotchild : ~ In phyDescChild (getChildren currentPart s)).
    { assert(getMappedPage currentPD s descChild = SomePage phyDescChild /\
      ~ In descChild (getPdsVAddr currentPart level getAllVAddrWithOffset0 s)) as ( Hvaphy' & Hpds1).
      { split.
        + apply getMappedPageGetTableRoot with ptRefChild currentPart;trivial.
        + unfold isPartitionFalse in *.
          move Hnotpart at bottom.
          unfold getPdsVAddr.
          rewrite filter_In.
          apply Classical_Prop.or_not_and.
          right.
          unfold checkChild.
          rewrite nextEntryIsPPgetFstShadow in *.
          rewrite Hfstsh1.
          assert(getIndirection currentShadow1 descChild level (nbLevel - 1) s = Some ptRefChildFromSh1).
          apply getIndirectionGetTableRoot with currentPart;trivial.
          symmetry;trivial.
          rewrite H.
          destruct  (ptRefChildFromSh1 =? defaultPage);trivial.
          auto.
          destruct Hnotpart; rewrite H0;auto. }
     
      unfold getChildren.
      rewrite <- Hlevel.
      rewrite nextEntryIsPPgetPd in *.
      rewrite Hpd.
      unfold getMappedPagesAux.
      rewrite filterOptionInIff.
      unfold getMappedPagesOption.
      rewrite in_map_iff.
      unfold not.
      intros.
      destruct H as (samev & Hi & Hii).
      assert(descChild = samev).
      apply eqMappedPagesEqVaddrs with phyDescChild currentPD s;trivial.

        unfold getPdsVAddr in *. 
        apply filter_In in Hii; intuition.
      unfold consistency in *.
      assert(noDupMappedPagesList s) by intuition.
      unfold noDupMappedPagesList in *.
      apply H in Hcurpart. clear H.
      move Hcurpart at bottom.
      unfold getMappedPages in Hcurpart.
      rewrite Hpd in *.
      unfold getMappedPagesAux  in *.
      unfold getMappedPagesOption in Hcurpart;trivial.
      subst.
      now contradict Hpds1. }
   assert(In parent (getPartitions multiplexer s)). 
 {  assert (Hsplitlist : exists nbPagesParent l1 l2,
          getPartitionAux multiplexer s (nbPage +1) = l1 ++ [currentPart] ++
          flat_map (fun p => getPartitionAux p s nbPagesParent )
          (getChildren currentPart s)++ l2
          /\
          getPartitionAux multiplexer s' (nbPage +1)  = l1 ++ [currentPart] ++
          flat_map (fun p => getPartitionAux p s' nbPagesParent )
          (getChildren currentPart s')++ l2 ).
  { unfold consistency in *.
    apply getPartitionAuxSplitListNewSate' with phyDescChild ptRefChild currentShadow1
     currentPD;intuition.
    apply addPartitionKeepsAllPartitionsInTree;trivial. }
  destruct Hsplitlist as (nbPagesParent & l11 & l22 & Hsplitlist).
  destruct Hsplitlist.
  unfold getPartitions in *.
  rewrite H;clear H.
  rewrite H0 in *;clear H0. 
  simpl in *.
  rewrite in_app_iff in *.
  destruct Hparent as [Hparent | Hparent]; [left;trivial|].
  right.
  simpl in *.
  destruct Hparent as [Hparent | Hparent];[left;trivial|].
  right.
  rewrite in_app_iff in *.
  destruct Hparent as [Hparent | Hparent];[ | right;trivial].
  left.
  unfold consistency in *.
  assert(HchildrenS : exists l1 l2,
  getChildren currentPart s' = l1 ++ [phyDescChild] ++ l2 /\
  getChildren currentPart s = l1 ++l2).
  apply getChildrenSplitList with ptRefChild currentShadow1 currentPD; intuition.
  destruct HchildrenS as (l1 & l2 & HchildrenS & Hchildrenprev).
  assert(Hl1 : incl l1 (getChildren currentPart s)).
  { unfold incl.
    intros.
    rewrite Hchildrenprev.
    rewrite in_app_iff;left;trivial. }
   assert(Hl22 : incl l2 (getChildren currentPart s)).
  { unfold incl.
    intros.
    rewrite Hchildrenprev.
    rewrite in_app_iff;right;trivial. }  
  rewrite  HchildrenS in Hparent.
  rewrite  Hchildrenprev . 
  simpl in Hparent.
  rewrite flat_map_app_cons in Hparent.
  rewrite flat_map_app.
  rewrite in_app_iff in *.
  simpl in *.
  assert(Hzero : getPartitionAux phyDescChild s' nbPagesParent  = [phyDescChild] \/
  getPartitionAux phyDescChild s' nbPagesParent  = [] ).
  {clear Hparent.
  induction (nbPagesParent ).
  simpl.
  right;trivial.
  simpl. left.
   assert (Hchildrennil : getChildren phyDescChild s' = nil).
   { assert(forall partition s, (* In partition (getPartitions multiplexer s)
              ->  *) incl (getChildren partition s) (getMappedPages partition s)).
      { intros.
        unfold incl.
        unfold getChildren.
        unfold getMappedPages.
        intros.
        destruct (StateLib.getNbLevel ); try now contradict H0.
        destruct  (StateLib.getPd partition (memory s0)); try now contradict H0.
        unfold getMappedPagesAux in *.
        rewrite filterOptionInIff in *.
        unfold getMappedPagesOption in *.
        rewrite in_map_iff in *.
        destruct H as (x & Hi & Hx).
        clear IHn.
        unfold getPdsVAddr in *.
        apply filter_In in Hx.
        
        exists x;split;intuition.
        trivial. now contradict H. }
     assert(Hmappednull : getMappedPages phyDescChild s' = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        (** we have an hypothesis **)
        rewrite getPdAddDerivation with phyDescChild  (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel)
        s entry true ;trivial.
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial.
        split;simpl.
        rewrite readPhyEntryAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        rewrite readPresentAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        (** PropagatedProperties : forall idx : index,
            StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
            StateLib.readPresent phyPDChild idx (memory s) = Some false **) }
             assert(Hbb1 :  forall (partition : page) (s : state) (a : page),
      In a (getChildren partition s) -> In a (getMappedPages partition s)) by trivial.
     generalize (Hbb1  phyDescChild s'); clear Hbb1; intros Hbb1.
     rewrite Hmappednull in *.
     destruct (getChildren phyDescChild s') .
     trivial. 
     assert(In p []).
     apply Hbb1.
     simpl;left;trivial. contradiction.
 }
  rewrite Hchildrennil;simpl;trivial.   
  }
  assert( In parent (flat_map (fun p : page => getPartitionAux p s' (nbPagesParent )) l1) \/
          In parent
            (
             flat_map (fun p : page => getPartitionAux p s' (nbPagesParent )) l2)).
  { destruct Hzero as [Hzero | Hzero]; rewrite Hzero in *; simpl in *.
    +
    destruct Hparent as [Hparent | [ Hparent | Hparent]] .
    left;trivial.
    subst parent;now contradict Hparentnotchild.
    right;trivial.
    + trivial.
    }
  clear Hparent Hzero.
  rename H into Hparent.
  destruct Hparent as [Hparent | Hparent] .
  ++ left.
     rewrite in_flat_map in *.
     destruct Hparent as (child & Hancestor1 & Hancestor2).
     exists child;split;trivial.
     assert( getPartitionAux child s (nbPagesParent ) = 
     getPartitionAux child s' (nbPagesParent )).
     { unfold consistency in *.
       intuition.
        apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
        apply childrenPartitionInPartitionList with currentPart;trivial.
        rewrite Hchildrenprev.
        rewrite in_app_iff.
        left;trivial.
         apply noCycleInPartitionTree2;trivial.
        unfold incl in Hl1.
        rewrite Hchildrenprev in *.
        apply in_app_iff.
        left;trivial. }
      trivial.
   rewrite H;trivial.
  ++ right.
     rewrite in_flat_map in *.
     destruct Hparent as (child & Hancestor1 & Hancestor2).
     exists child;split;trivial.
     assert( getPartitionAux child s (nbPagesParent ) = 
     getPartitionAux child s' (nbPagesParent )).
     { unfold consistency in *.
       intuition.
        apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
        apply childrenPartitionInPartitionList with currentPart;trivial.
        rewrite Hchildrenprev.
        rewrite in_app_iff.
        right;trivial.
        apply noCycleInPartitionTree2;trivial.
        unfold incl in Hl1.
        rewrite Hchildrenprev in *.
        apply in_app_iff.
        right;trivial. }
   rewrite H;trivial.
     }
  assert(Hchildeq : child1 = phyDescChild \/ child2 = phyDescChild \/
    (child1 <> phyDescChild /\ child2 <> phyDescChild) ). 
  { destruct child1; destruct child2; destruct phyDescChild.
    assert (p = p1 \/ p0 = p1 \/
    (p <> p1 /\ p0 <> p1)) by omega.
    destruct H0 as [Hi | [Hi |(Hi1 & Hi2) ]].
    + left. subst. f_equal. apply proof_irrelevance.
    + right;left.
      subst. f_equal. apply proof_irrelevance.
    + right;right.
      split;
      unfold not; intros Hfalse;inversion Hfalse; subst; 
      try now contradict Hi1;try now contradict Hi2. }
  destruct Hchildeq as [Hchild1eq | [Hchild1eq | (Hchild1eq & Hchild2eq)]];
  subst.
  * fold s' in Hpost.
    assert(Hchildeq : getChildren parent s' = getChildren parent s).
    { unfold consistency in *. 
      apply addPartitionGetChildrenEq with currentPart;intuition.
      fold s' in H0.
      rewrite H0 in *. 
      apply Hphynotchild;trivial. }  
    rewrite Hchildeq in Hchild1.
    assert (In  phyDescChild (getPartitions multiplexer s)).
    apply childrenPartitionInPartitionList with parent; trivial.
    unfold consistency in *. intuition. 
    apply HnotConfig in H0.
    apply Classical_Prop.not_or_and in H0.
    intuition.
  * fold s' in Hpost.
    assert(Hchildeq : getChildren parent s' = getChildren parent s).
    { unfold consistency in *. 
      apply addPartitionGetChildrenEq with currentPart;intuition.
      fold s' in H0.
      rewrite H0 in *. 
      apply Hphynotchild;trivial. }  
    rewrite Hchildeq in Hchild2.
    assert (In  phyDescChild (getPartitions multiplexer s)).
    apply childrenPartitionInPartitionList with parent; trivial.
    unfold consistency in *. intuition. 
    apply HnotConfig in H0.
    apply Classical_Prop.not_or_and in H0.
    intuition.
  * unfold consistency in *. 
    assert (getChildren parent s' = getChildren parent s).
    { apply addPartitionGetChildrenEq with currentPart;intuition.
      fold s' in H0, Hpost.
      rewrite H0 in *. 
      apply Hphynotchild;trivial. }
    rewrite H0 in *.
    apply Hiso with parent; trivial.
Qed. (** noDupPartitionTree s' : partitionsIsolationAddChild*)

Lemma isEntryPageReadPhyEntry2 table idx phy s:
isEntryPage table idx phy s -> 
StateLib.readPhyEntry table idx (memory s) = Some phy.
Proof.
intros Hentrypage.
unfold isEntryPage in *.
unfold StateLib.readPhyEntry.
destruct(lookup table idx (memory s) beqPage beqIndex );
try now contradict Hentrypage.
destruct v; try now contradict Hentrypage.
f_equal;trivial.
Qed.
    Lemma notInGetAccessibleMappedPage ptvaInAncestor ancestor phypage pdAncestor vaInAncestor s  : 
    noDupMappedPagesList s -> 
    In ancestor (getPartitions multiplexer s) -> 
  (forall idx : index,
   StateLib.getIndexOfAddr vaInAncestor fstLevel = idx ->
   isPE ptvaInAncestor idx s /\ getTableAddrRoot ptvaInAncestor PDidx ancestor vaInAncestor s) ->
  (defaultPage =? ptvaInAncestor) = false ->
  isEntryPage ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) phypage s ->
  entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) true s ->
  entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) false s ->
  nextEntryIsPP ancestor PDidx pdAncestor s ->
    ~In phypage (getAccessibleMappedPages ancestor s).
    Proof. 
  intros Hnodupmap Hpart Hget Hnotnull Hep Hpresent Huser Hpdparent.
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
omega.
apply getNbLevelEq in HnbL.
subst.
apply nbLevelEq.
rewrite Hnewind.
trivial.

apply isEntryPageReadPhyEntry2;trivial.
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
omega.
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

Lemma verticalSharingAddChild entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1:
isParent s -> 
consistency s -> 
partitionsIsolation s -> 
(* partitionDescriptorEntry s ->
noDupConfigPagesList s ->
noDupMappedPagesList s -> *)
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             {|
             currentPartition := currentPartition s;
             memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                         (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}) ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
verticalSharing s ->
In descChild getAllVAddrWithOffset0 -> 
verticalSharing  {|
             currentPartition := currentPartition s;
             memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                         (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros HisParent Hcons Hiso (* Hpde Hnodupconf Hnodupmap *) Hlookup Hppsh3 Hppsh2 Hppsh1 Hpppd Hcurpart Hlevel HcurrentPD Hpost
Hnewpd Hnewsh1 Hnewsh2 (* Hnewsh31 Hnewsh32 Hnewsh33 *) HmappedDesc
HmappedPD Hmappedsh1 HmappedSh2 Hmappedsh3 Hnotconfig Hroot Hptnotnull Hep
Hpresent Hfstsh1 Hnotpart Hsh1 Hptsh1notnull
HphyPDcontent HphySh1content HphySh2content HphyListcontent(* 1 HphyListcontent2 HphyListcontent3  *)
HnotConfig HnotConfig1 HnotConfig2 HnotConfig3 HnotConfig4
Ha1 Ha2 Ha3 Ha4 Ha5 HVS Hnewphy.
unfold verticalSharing in *.
intros parent child Hvs1 Hvs2.
assert(Hparteq : parent = currentPart \/ parent <> currentPart) by apply pageDecOrNot.
destruct Hparteq as [Hparteq | Hparteq].
(* parent = currentPart *)
  + subst.
    assert(Hchildeq : child = phyDescChild  \/ child <> phyDescChild ) by apply pageDecOrNot.
    destruct Hchildeq as [Hchild1eq |Hchild1eq ].
    - subst.
      rewrite getUsedPagesAddDerivation  with phyDescChild (va entry) ptRefChildFromSh1
      (StateLib.getIndexOfAddr descChild fstLevel) entry s true  ;trivial.
      rewrite getMappedPagesAddDerivation with currentPart (va entry)
      ptRefChildFromSh1  (StateLib.getIndexOfAddr descChild fstLevel) s entry true
        ;trivial.
      unfold getUsedPages at 1.
      assert(Hmappednull : getMappedPages phyDescChild s = nil).
      { unfold getMappedPages.
        (** we have an hypothesis **)
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial.
        (** PropagatedProperties : forall idx : index,
            StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
            StateLib.readPresent phyPDChild idx (memory s) = Some false **)
       }
      rewrite Hmappednull.
      rewrite app_nil_r.
      unfold getConfigPages.
      unfold getConfigPagesAux.
      simpl.   
      (** we have an hypothesis **)
      assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
      apply nextEntryIsPPgetPd;trivial.
      rewrite Hpdnewchild.
      simpl.
      (** we have an hypothesis **)
      assert(Hsh1newchild :StateLib.getFstShadow phyDescChild (memory s) = Some phySh1Child).
      apply nextEntryIsPPgetFstShadow;trivial.
      rewrite Hsh1newchild.
      simpl.
      (** we have an hypothesis **)
      assert(Hsh2newchild :StateLib.getSndShadow phyDescChild (memory s) = Some phySh2Child).
      apply nextEntryIsPPgetSndShadow;trivial.
      rewrite Hsh2newchild.
      simpl.
      (** we have an hypothesis **)
      assert(Hlistnewchild :StateLib.getConfigTablesLinkedList phyDescChild (memory s) = Some phyConfigPagesList ).
      apply nextEntryIsPPgetConfigList;trivial.
      rewrite Hlistnewchild.
      set(s' := {|
            currentPartition := currentPartition s;
            memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                        (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} )
                        in *.
      (** new partition configuration : replace  *)
      rewrite getIndirectionsOnlyPD;trivial.
      rewrite getIndirectionsOnlySh1 with phySh1Child level s;trivial.
      rewrite getIndirectionsOnlySh2 with phySh2Child level s;trivial.
      rewrite getLLPagesOnlyRoot;trivial.
      unfold incl.
      simpl.
      intros.
      repeat destruct H;
      subst;trivial.
    - rewrite getUsedPagesAddDerivation  with child (va entry) ptRefChildFromSh1
      (StateLib.getIndexOfAddr descChild fstLevel) entry s true  ;trivial.
      rewrite getMappedPagesAddDerivation with currentPart (va entry)
      ptRefChildFromSh1  (StateLib.getIndexOfAddr descChild fstLevel) s entry true ;trivial.
      apply HVS;trivial.
      { (** Have to prove this property using
      (forall partition : page,
        In partition (getPartitions multiplexer s) ->
        ~(partition = phyDescChild \/In phyDescChild (getConfigPagesAux partition s))) :
        not a partition implies not a child  **)
        assert(HnewChild : ~ In phyDescChild (getChildren currentPart s)).
        { assert (~ In phyDescChild (getPartitions multiplexer s)).
          { unfold not. intros.
            apply Hnotconfig in H.
            contradict H;left;trivial. }         
        unfold not;intros Hfalse; contradict H.
        apply childrenPartitionInPartitionList with currentPart;trivial.
        unfold consistency in *. intuition. }
        unfold consistency in *.
        apply partitionInPreviousState with
         phyDescChild ptRefChild currentShadow1 currentPD
         {|
            currentPartition := currentPartition s;
            memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                        (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}
                         entry descChild ptRefChildFromSh1;intuition.
                          }
 +  assert(Hparentnotchild : parent = phyDescChild \/ parent <> phyDescChild ).
{ destruct parent; destruct phyDescChild.
  simpl in *.
  assert(p=p0 \/ p<> p0) by omega.
  destruct H as [Hi | Hi].
  subst.
  left;simpl;f_equal;apply proof_irrelevance.
  right.
  unfold not;intros Hii.
  inversion Hii.
  subst.
  now contradict Hi. }
  destruct Hparentnotchild as [Hparentnotchild | Hparentnotchild].
  -  set(s':=  {|
  currentPartition := _ |}) in *.  
    subst.
    assert (Hchildrennil : getChildren phyDescChild
              s' =
                           nil).
   { assert(forall partition s, (* In partition (getPartitions multiplexer s)
              ->  *) incl (getChildren partition s) (getMappedPages partition s)).
      { intros.
        unfold incl.
        unfold getChildren.
        unfold getMappedPages.
        intros.
        destruct (StateLib.getNbLevel ); try now contradict H0.
        destruct  (StateLib.getPd partition (memory s0)); try now contradict H0.
        unfold getMappedPagesAux in *.
        rewrite filterOptionInIff in *.
        unfold getMappedPagesOption in *.
        rewrite in_map_iff in *.
          destruct H as (x & Hi & Hx).
        unfold getPdsVAddr in *.
        apply filter_In in Hx.
        
        exists x;split;intuition. intuition. intuition. }
        
    
     assert(Hmappednull : getMappedPages phyDescChild s' = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        (** we have an hypothesis **)
        rewrite getPdAddDerivation with phyDescChild  (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel)
        s entry true ;trivial.
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial.
        split;simpl.
        rewrite readPhyEntryAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        rewrite readPresentAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        (** PropagatedProperties : forall idx : index,
            StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
            StateLib.readPresent phyPDChild idx (memory s) = Some false **) }
            assert(Hbb1 :  forall (partition : page) (s : state) (a : page),
      In a (getChildren partition s) -> In a (getMappedPages partition s)) by trivial.
     generalize (Hbb1  phyDescChild s'); clear Hbb1; intros Hbb1.
     rewrite Hmappednull in *.
     destruct (getChildren phyDescChild s') .
     trivial. 
     assert(In p []).
     apply Hbb1.
     simpl;left;trivial. contradiction.
 }
     unfold s' in *.
     clear s'.
     set(s' := {|currentPartition := _|}) in *. 
   rewrite Hchildrennil in *.
   now contradict Hvs2.
   - rewrite getUsedPagesAddDerivation  with child (va entry) ptRefChildFromSh1
    (StateLib.getIndexOfAddr descChild fstLevel) entry s true  ;trivial.
    rewrite getMappedPagesAddDerivation with parent (va entry)
    ptRefChildFromSh1  (StateLib.getIndexOfAddr descChild fstLevel) s entry true
    ;trivial.
    assert(Hphynotchild : ~ In phyDescChild (getChildren currentPart s)).
    { assert(getMappedPage currentPD s descChild = SomePage phyDescChild /\
      ~ In descChild (getPdsVAddr currentPart level getAllVAddrWithOffset0 s)) as ( Hvaphy' & Hpds1).
      { split.
        + apply getMappedPageGetTableRoot with ptRefChild currentPart;trivial.
        + unfold isPartitionFalse in *.
          move Hnotpart at bottom.
          unfold getPdsVAddr.
          rewrite filter_In.
          apply Classical_Prop.or_not_and.
          right.
          unfold checkChild.
          rewrite nextEntryIsPPgetFstShadow in *.
          rewrite Hfstsh1.
          assert(getIndirection currentShadow1 descChild level (nbLevel - 1) s = Some ptRefChildFromSh1).
          apply getIndirectionGetTableRoot with currentPart;trivial.
          symmetry;trivial.
          rewrite H.
          destruct  (ptRefChildFromSh1 =? defaultPage);trivial.
          auto.
          destruct Hnotpart; rewrite H0;auto. }
     
      unfold getChildren.
      rewrite <- Hlevel.
      rewrite nextEntryIsPPgetPd in *.
      rewrite HcurrentPD.
      unfold getMappedPagesAux.
      rewrite filterOptionInIff.
      unfold getMappedPagesOption.
      rewrite in_map_iff.
      unfold not.
      intros.
      destruct H as (samev & Hi & Hii).
      assert(descChild = samev).
      apply eqMappedPagesEqVaddrs with phyDescChild currentPD s;trivial.
              unfold getPdsVAddr in *.
        apply filter_In in Hii. intuition.
      unfold consistency in *.
      assert(noDupMappedPagesList s) by intuition.
      unfold noDupMappedPagesList in *.
      apply H in Hcurpart. clear H.
      move Hcurpart at bottom.
      unfold getMappedPages in Hcurpart.
      rewrite HcurrentPD in *.
      unfold getMappedPagesAux  in *.
      unfold getMappedPagesOption in Hcurpart;trivial.
      subst.
      now contradict Hpds1. }
      unfold consistency in *.
 assert(Hkey : In parent (getPartitions multiplexer s)).
   apply addPartitionAddsSinglePartition with 
   entry descChild ptRefChildFromSh1
currentPart phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1;trivial.
 intuition. 
 intuition.
 intuition. 
  
      apply HVS;trivial.
  assert(Hchildeq : child = phyDescChild \/  child <> phyDescChild ) by apply pageDecOrNot. 
  set (s':= {|
            currentPartition := currentPartition s;
            memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                        (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} ) in *. 
  destruct Hchildeq as [Hchild1eq | Hchild2eq];
  subst.
  * assert(Hchildeq : getChildren parent s' = getChildren parent s).
    { unfold consistency in *. 
      apply addPartitionGetChildrenEq with currentPart; intuition.
      fold s' in H.
      rewrite H in *. 
      apply Hphynotchild;trivial. }  
    rewrite Hchildeq in Hvs2.
    assert (In  phyDescChild (getPartitions multiplexer s)).
    apply childrenPartitionInPartitionList with parent; trivial.
    unfold consistency in *. intuition. 
    apply HnotConfig in H.
    apply Classical_Prop.not_or_and in H.
    intuition.
  * fold s' in Hpost.
    assert(Hchildeq : getChildren parent s' = getChildren parent s).
    { unfold consistency in *. 
      apply addPartitionGetChildrenEq with currentPart;intuition.
      fold s' in H.
      rewrite H in *. 
      apply Hphynotchild;trivial. }  
    rewrite Hchildeq in Hvs2.
    trivial.
Qed.
 (** verticalSharing *)
           Lemma multiplexerIsAncestor s : 
           noDupPartitionTree s -> 
           forall partition, parentInPartitionList s ->  partitionDescriptorEntry s ->  isParent s ->  In partition (getPartitions multiplexer s)
         -> In partition (getPartitions multiplexer s) -> 
              partition <> multiplexer -> 
              In multiplexer (getAncestors partition s).
        Proof.
         intro Hnoduptree.
         intro. 
          unfold getAncestors.
          unfold getPartitions at 2.
          intros Hparentintree Hpde Hisparent .
          revert partition. 
          induction (nbPage+1);simpl;intuition. 
          case_eq(getParent partition (memory s));[ intros parent Hparent | intros Hparent].
          simpl. 
          assert(Hor : parent = multiplexer \/ parent <> multiplexer) by apply pageDecOrNot.
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
          nextEntryIsPP partition PPRidx entry s /\ entry <> defaultPage)).
          apply Hpde;trivial.
          do 4 right;left;trivial.
          destruct H0 as (entry & Hi & _).
          rewrite nextEntryIsPPgetParent in *.
          rewrite Hi in Hparent. now contradict Hparent.
          Qed.

           
Lemma kernelDataIsolationAddChild entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxConfigPagesList ptConfigPagesList idxSh2
ptSh2Child shadow2 idxSh1 ptSh1Child shadow1 idxPDChild ptPDChild pdChild idxRefChild list
:
isParent s -> 
verticalSharing s ->
partitionsIsolation s -> 
consistency s -> 
(* partitionDescriptorEntry s ->
noDupConfigPagesList s ->
noDupMappedPagesList s -> *)
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
nextEntryIsPP phyDescChild PPRidx currentPart s -> 
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             {|
             currentPartition := currentPartition s;
             memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                         (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}) ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s -> 
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->

In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) -> 
 *) initConfigPagesListPostCondition phyConfigPagesList s ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyPDChild (getAccessibleMappedPages partition s)) -> 
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phySh1Child (getAccessibleMappedPages partition s)) ->
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phySh2Child (getAccessibleMappedPages partition s)) ->
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyConfigPagesList (getAccessibleMappedPages partition s)) ->
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyDescChild (getAccessibleMappedPages partition s)) ->

kernelDataIsolation s ->
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
StateLib.getIndexOfAddr descChild fstLevel = idxRefChild ->
entryPresentFlag ptRefChild idxRefChild true s ->
entryUserFlag ptRefChild idxRefChild false s ->
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) ->
(defaultPage =? ptPDChild) = false ->
StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild ->
entryPresentFlag ptPDChild idxPDChild true s ->
entryUserFlag ptPDChild idxPDChild false s ->
(forall idx : index,
StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) ->
(defaultPage =? ptSh1Child) = false ->
StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1 ->
entryPresentFlag ptSh1Child idxSh1 true s ->
entryUserFlag ptSh1Child idxSh1 false s ->
(forall idx : index,
StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) ->
(defaultPage =? ptSh2Child) = false ->
StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2 ->
entryPresentFlag ptSh2Child idxSh2 true s ->
entryUserFlag ptSh2Child idxSh2 false s->
(forall idx : index,
StateLib.getIndexOfAddr list fstLevel = idx ->
isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s) ->
(defaultPage =? ptConfigPagesList) = false ->
StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList ->
entryPresentFlag ptConfigPagesList idxConfigPagesList true s ->
entryUserFlag ptConfigPagesList idxConfigPagesList false s ->


isEntryPage ptPDChild idxPDChild phyPDChild s ->
isEntryPage ptSh1Child idxSh1 phySh1Child s ->
isEntryPage ptSh2Child idxSh2 phySh2Child s ->
isEntryPage ptConfigPagesList idxConfigPagesList phyConfigPagesList s ->

In descChild getAllVAddrWithOffset0 -> 
kernelDataIsolation {|
  currentPartition := currentPartition s;
  memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}. 
Proof.
intros HisParent Hvs Hiso Hcons (* Hpde Hnodupconf Hnodupmap *) Hlookup Hppsh3 Hppsh2 Hppsh1 Hpppd Hppparent Hcurpart Hlevel HcurrentPD Hpost
Hnewpd Hnewsh1 Hnewsh2 Hnewsh31 (* Hnewsh32 Hnewsh33 *) HmappedDesc
HmappedPD Hmappedsh1 HmappedSh2 Hmappedsh3 Hnotconfig Hroot Hptnotnull Hep
Hpresent Hfstsh1 Hnotpart Hsh1 Hptsh1notnull.
intros HphyPDcontent
HphySh1content HphySh2content HphyListcontent(* 1 HphyListcontent2 HphyListcontent3  *)
HnotConfig HnotConfig1 HnotConfig2 HnotConfig3 HnotConfig4

Ha1 Ha2 Ha3 Ha4 Ha5.
intros  Hb1 Hb2 Hb3 Hb4 Hb5.

unfold kernelDataIsolation.
intros HKDI.
intros .
assert(Hmultnone : multiplexerWithoutParent s ) .
unfold consistency in *. intuition.
assert(Hnoduptree : noDupPartitionTree s).
unfold consistency in *. intuition.
assert(Heqparts : partition1 = phyDescChild \/ partition2 = phyDescChild \/
(partition1 <> phyDescChild /\ partition2 <> phyDescChild) ).
{ destruct partition1; destruct partition2; destruct phyDescChild.
    assert (Hor1 : p = p1 \/ p0 = p1 \/
    (p <> p1 /\ p0 <> p1)) by omega.
    destruct Hor1 as [Hi | [Hi |(Hi1 & Hi2) ]].
    + left. subst. f_equal. apply proof_irrelevance.
    + right;left.
      subst. f_equal. apply proof_irrelevance.
    + right;right.
      split;
      unfold not; intros Hfalse;inversion Hfalse; subst; 
      try now contradict Hi1;try now contradict Hi2. }
set(s' := {|
          currentPartition := currentPartition s;
          memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                      (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}) in *.    

 assert(Hmappednull : getMappedPages phyDescChild s' = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        (** we have an hypothesis **)
        rewrite getPdAddDerivation with phyDescChild  (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel)
        s entry true ;trivial.
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial.
        split;simpl.
        rewrite readPhyEntryAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        rewrite readPresentAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        (** PropagatedProperties : forall idx : index,
            StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
            StateLib.readPresent phyPDChild idx (memory s) = Some false **) }
assert(Hnil : getAccessibleMappedPages phyDescChild
     s' = nil).
{ 
assert (Hincl : incl (getAccessibleMappedPages phyDescChild s') 
          (getMappedPages phyDescChild s'))
by apply accessibleMappedPagesInMappedPages.
unfold incl in *.
rewrite Hmappednull in *.
induction (getAccessibleMappedPages phyDescChild s') ;trivial.
simpl in *.
destruct Hincl with a; left;trivial.
}
 destruct Heqparts as [Heqparts | [Heqparts | (Hnoteqpart1 & Hnoteqpart2)]].
- subst.
  
  rewrite Hnil.
  unfold disjoint.
  intros.
  tauto.
- subst.
unfold s'.
  rewrite getAccessibleMappedPagesAddDerivation with partition1 (va entry)
  ptRefChildFromSh1  (StateLib.getIndexOfAddr descChild fstLevel) entry s true;
  trivial.
  rewrite getConfigPagesAddDerivation with phyDescChild (va entry)
  ptRefChildFromSh1  (StateLib.getIndexOfAddr descChild fstLevel) entry s true;
  trivial.
  assert(Hiseq : partition1 = phyDescChild \/ partition1 <> phyDescChild) by 
  apply pageDecOrNot. 
 destruct Hiseq as [Hiseq | Hiseq].
  + subst.
    assert(Haccess : getAccessibleMappedPages phyDescChild
     s = getAccessibleMappedPages phyDescChild
     s').
     symmetry.
     apply getAccessibleMappedPagesAddDerivation with entry;trivial.
     rewrite Haccess.
    rewrite Hnil.
    unfold disjoint.
    intros.
    tauto.
  +
  unfold getConfigPages.
  unfold getConfigPagesAux.
  simpl.   
  (** we have an hypothesis **)
  assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
  apply nextEntryIsPPgetPd;trivial.
  rewrite Hpdnewchild.
  simpl.
  (** we have an hypothesis **)
  assert(Hsh1newchild :StateLib.getFstShadow phyDescChild (memory s) = Some phySh1Child).
  apply nextEntryIsPPgetFstShadow;trivial.
  rewrite Hsh1newchild.
  simpl.
  (** we have an hypothesis **)
  assert(Hsh2newchild :StateLib.getSndShadow phyDescChild (memory s) = Some phySh2Child).
  apply nextEntryIsPPgetSndShadow;trivial.
  rewrite Hsh2newchild.
  simpl.
  (** we have an hypothesis **)
  assert(Hlistnewchild :StateLib.getConfigTablesLinkedList phyDescChild (memory s) = Some phyConfigPagesList ).
  apply nextEntryIsPPgetConfigList;trivial.
  rewrite Hlistnewchild.
  (** new partition configuration : replace  *)
  rewrite getIndirectionsOnlyPD;trivial.
  rewrite getIndirectionsOnlySh1 with phySh1Child level s;trivial.
  rewrite getIndirectionsOnlySh2 with phySh2Child level s;trivial.
  rewrite getLLPagesOnlyRoot;trivial.
  unfold incl.
  
  assert (Hances : In partition1 (getAncestors currentPart s) \/
  ~ In partition1 (getAncestors currentPart s)).
  { clear. 
    revert partition1. 
    induction (getAncestors currentPart s).
    right;intuition.
    simpl.
    intros.
    assert( a = partition1 \/ a <> partition1 ) by apply pageDecOrNot.
    destruct H.
    do 2 left;trivial.
    generalize (IHl partition1);clear IHl;intros IHl.
    destruct IHl.
    left.
    right;trivial.
     
    right.
    intuition. }
  destruct  Hances as [ Hances | Hances].
  * assert(Hor : partition1 <> currentPart).
  { unfold consistency in *. 
     assert(Hcycle : noCycleInPartitionTree s) by intuition.
     unfold noCycleInPartitionTree in *.
     apply Hcycle;trivial. }
    unfold disjoint.
    intros.
    subst. 
    simpl.
    intuition;
    subst x.
    ++ unfold consistency in *. 
        apply Hb5 with partition1; trivial.
    ++  unfold consistency in *. 
        apply Hb1 with partition1; trivial.
    ++ unfold consistency in *. 
        apply Hb2 with partition1; trivial.
    ++  unfold consistency in *. 
        apply Hb3 with partition1; trivial.
    ++  unfold consistency in *. 
        apply Hb4 with partition1; trivial.
  
   (** child config pages are not accessible into its ancestors **)
   (** partition not an ancestor*)
  * assert(Hor : currentPart = partition1 \/ currentPart <> partition1) by apply pageDecOrNot. 
    destruct Hor as [Hor | Hor].
  -- subst partition1.
      unfold disjoint.
      intros.
      subst. 
      simpl.
      assert(Hnodupmap : noDupMappedPagesList s).
      unfold consistency in *.
      intuition. 
      intuition;
      subst x.
      assert(Htrue : ~ In phyDescChild (getAccessibleMappedPages currentPart s)). 
      apply notInGetAccessibleMappedPage with ptRefChild currentPD descChild;trivial.
      now contradict Htrue.
      assert(Htrue : ~ In phyPDChild (getAccessibleMappedPages currentPart s)). 
      apply notInGetAccessibleMappedPage with ptPDChild currentPD pdChild;trivial.
      now contradict Htrue.
      assert(Htrue : ~ In phySh1Child (getAccessibleMappedPages currentPart s)). 
      apply notInGetAccessibleMappedPage with ptSh1Child currentPD shadow1;trivial.
      now contradict Htrue.
      assert(Htrue : ~ In phySh2Child (getAccessibleMappedPages currentPart s)). 
      apply notInGetAccessibleMappedPage with ptSh2Child currentPD shadow2;trivial.
      now contradict Htrue.
      assert(Htrue : ~ In phyConfigPagesList (getAccessibleMappedPages currentPart s)). 
      apply notInGetAccessibleMappedPage with ptConfigPagesList currentPD list;trivial.
      now contradict Htrue.
 (** all phy pages are not accessible into the current partition **)
  -- assert(Hin : In partition1 (getPartitionAux currentPart s (nbPage+1)) \/ 
             ~ In partition1 (getPartitionAux currentPart s (nbPage+1))).
     { clear. 
        revert partition1. 
        induction (getPartitionAux currentPart s (nbPage + 1)).
        right;intuition.
        simpl.
        intros.
        assert( a = partition1 \/ a <> partition1 ) by apply pageDecOrNot.
        destruct H.
        do 2 left;trivial.
        generalize (IHl partition1);clear IHl;intros IHl.
        destruct IHl.
        left.
        right;trivial.         
        right.
        intuition. }
     destruct Hin as [Hin | Hin].
     ++ destruct nbPage. simpl in *.
        revert Hin Hor. clear.
        intros.
        intuition. contradict H.
        induction (getChildren currentPart s);simpl; intuition.
        simpl in *.
        destruct Hin as [Hin | Hin]. intuition.
        rewrite in_flat_map in Hin.
        destruct Hin as (x & Hx1 & Hx2).
        unfold disjoint.
        intros pgmap Hpg.  
        assert (Hincl : incl (getAccessibleMappedPages partition1 s) 
        (getMappedPages partition1 s))
          by apply accessibleMappedPagesInMappedPages.
        unfold incl in *.
        apply Hincl in Hpg;clear Hincl.
        simpl .
        assert(Horx : x=partition1 \/ x<> partition1) by apply pageDecOrNot.
        destruct Horx as [Horx | Horx].
        ** subst.         
            intuition subst pgmap.
            apply Ha1 with partition1;trivial.
            apply Ha2 with partition1;trivial.
            apply Ha3 with partition1;trivial.
            apply Ha4 with partition1;trivial.
            apply Ha5 with partition1;trivial.
        ** assert( Hincl2 : incl (getMappedPages partition1 s) (getMappedPages x s)).
            apply verticalSharingRec with n;trivial.
            unfold consistency in *.
            intuition.
            unfold consistency in *. intuition.
            apply childrenPartitionInPartitionList with currentPart;trivial.
   
            unfold incl in Hincl2.
            apply Hincl2 in Hpg.
            intuition subst pgmap.
            apply Ha1 with x;trivial.
            apply Ha2 with x;trivial.
            apply Ha3 with x;trivial.
            apply Ha4 with x;trivial.
            apply Ha5 with x;trivial.       
     ++ assert(Hin1: In partition1 (getPartitions multiplexer s)).
         { unfold consistency in *.
           apply addPartitionAddsSinglePartition with 
            entry descChild ptRefChildFromSh1
            currentPart phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
            phyConfigPagesList ptRefChild currentShadow1;trivial.
           intuition. 
           intuition.
           intuition.
           intuition. }

        assert (Hok:  forall partition, parentInPartitionList s ->  partitionDescriptorEntry s ->  isParent s ->  In partition (getPartitions multiplexer s)
         -> In partition (getPartitions multiplexer s) -> 
              partition <> multiplexer -> 
              In multiplexer (getAncestors partition s)).  
         apply multiplexerIsAncestor;trivial.
         unfold consistency in *. intuition.
         assert(Hnotanc : partition1 <> multiplexer). 
         { assert(In multiplexer (getAncestors currentPart s)) . 
            { unfold consistency in *.  
           apply Hok;trivial.
           unfold not;intros Hfalse;subst.
           contradict Hin. unfold getPartitions in *;trivial.  }
           unfold not;intros Hfalse;subst.
           now contradict Hances.  } 
         assert(Hmulteq :currentPart = multiplexer \/ currentPart <> multiplexer ) by apply pageDecOrNot.
         destruct Hmulteq as [Hmulteq | Hmulteq].
         subst currentPart.           
         unfold getPartitions in Hin1.
         now contradict Hin.
         move Hcurpart at bottom.
         assert( match  closestAncestor currentPart partition1 s with 
                  | Some closestAnc =>  True
                  | None => False
         end
         ).
         { case_eq (closestAncestor currentPart partition1 s ); [intros  closestAnc Hclose| 
          intros Hclose];trivial.
          unfold consistency in *.
             assert(Hisparent : isParent s) by intuition. 
           revert Hmultnone Hnoduptree Hcurpart Hclose Hisparent  .
           
            clear.
            unfold closestAncestor, getPartitions.
            intro. intro.
            revert currentPart partition1.
            
            
            assert(Hmult : getParent multiplexer (memory s) = None) .
            intuition.
            induction nbPage.
            simpl.
            intros.            
            destruct Hcurpart.
            subst. 
            rewrite Hmult in *.
            now contradict Hclose.
            contradict H. clear.
            induction (getChildren multiplexer s); simpl; intuition.
            simpl .
            intros. 
            destruct Hcurpart.
            subst.
            rewrite Hmult in *.
            now contradict Hclose.
            case_eq(getParent currentPart (memory s) ); [intros parent Hparent | intros Hparent];
            rewrite Hparent in *; try now contradict Hclose.
            case_eq ( in_dec pageDec partition1 (getPartitionAux parent s (nbPage + 1))); 
            intros i Hi; rewrite Hi in *.
            now contradict Hclose.
            apply IHn with parent partition1;trivial.
            assert (In currentPart (getPartitionAux multiplexer s (n + 2))).
            replace (n + 2) with (S n +1) by omega.
            simpl;right;trivial.
            apply getPartitionAuxMinus1 with currentPart;trivial.
            unfold getPartitions. destruct nbPage;simpl;left;trivial.
          } 
          case_eq(closestAncestor currentPart partition1 s); [intros  closestAnc Hclose| 
          intros Hclose];
          rewrite Hclose in *; try now contradict H1.
          assert(Hcloseintree : In closestAnc (getPartitions multiplexer s)). 
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
           case_eq( getParent currentPart (memory s));[intros parent Hparent | intros Hparent];
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
          { assert (Hcurpart1 :In currentPart (getPartitions multiplexer s)) by trivial.   
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
           + subst. assert (Hmult :  getParent multiplexer (memory s) = None) by intuition.
           rewrite Hmult in *.
           inversion Hclose. intuition.
           +
           right.
           case_eq( getParent currentPart (memory s));[intros parent Hparent | intros Hparent];
           rewrite Hparent in *.
           - case_eq(in_dec pageDec partition1 (getPartitionAux parent s (nbPage + 1)));
           intros i Hi; rewrite Hi in *.
           * inversion Hclose;subst.
           rewrite in_flat_map.
           exists currentPart;split;trivial.
           unfold isChild in *.
           apply Hchild;trivial. destruct n;simpl in *.
           contradict Hcurpart.
           clear. induction   (getChildren multiplexer s) ;simpl;intuition.
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
         { assert (Hcurpart1 :In partition1 (getPartitions multiplexer s)) by trivial.   
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
          assert(Hnbpage : nbPage <= nbPage) by omega.
          revert Hnbpage.
          generalize nbPage at 1 3.
           induction n;simpl;intros.
           trivial.  
           + case_eq( getParent currentPart (memory s));[intros parent Hparent | intros Hparent];
              rewrite Hparent in *.
              - case_eq(in_dec pageDec partition1 (getPartitionAux parent s (nbPage + 1)));
                intros i Hi; rewrite Hi in *.
               * inversion Hclose;subst. trivial.
               *  now contradict Hclose.
              -  inversion Hclose. subst. unfold getPartitions in *;trivial.
         + case_eq( getParent currentPart (memory s));[intros parent Hparent | intros Hparent];
            rewrite Hparent in *.
            - case_eq(in_dec pageDec partition1 (getPartitionAux parent s (nbPage + 1)));
              intros i Hi; rewrite Hi in *.
              * inversion Hclose;subst. trivial.
              * apply IHn with parent;trivial. omega.           
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
           case_eq(getParent currentPart (memory s) );intros.
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
          nextEntryIsPP currentPart PPRidx entry s /\ entry <> defaultPage)).
          apply Hpde;trivial.
          do 4 right;left;trivial.
          destruct H0 as (entry & H1 & _).
          rewrite nextEntryIsPPgetParent in *.
          rewrite H1 in H. now contradict H1. }
        now contradict Hfalse.
      ** assert(Hsub1 : In currentPart
          (flat_map (fun p : page => getPartitionAux p s nbPage) (getChildren closestAnc s))).
         {  replace (nbPage +1) with (1 + nbPage) in * by omega.
             simpl in *.
             apply Classical_Prop.not_or_and in Hin as (_ & Hin).  
               destruct  Hinsubtree1 as [Hsub1 | Hsub1]; subst.
      destruct  Hinsubtree2 as [Hsub2 | Hsub2]; subst.
             now contradict Heqclose.  now contradict Hsub2.
         destruct  Hinsubtree2 as [Hsub2 | Hsub2]; subst.
             now contradict Heqclose. trivial. }
      assert(Hsub2 : In partition1
          (flat_map (fun p : page => getPartitionAux p s nbPage) (getChildren closestAnc s))).
          {  replace (nbPage +1) with (1 + nbPage) in * by omega.
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
         unfold disjoint in *.
         intros.
         assert(Hx : In x (getMappedPages partition1 s)).
         apply accessibleMappedPagesInMappedPages; trivial. simpl. 
         intuition subst x.
          * apply Hdisjoint with phyDescChild;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial. trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
           * 
           apply Hdisjoint with phyPDChild ;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial. trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
          * 
           apply Hdisjoint with phySh1Child;trivial.
          unfold getUsedPages.
           apply in_app_iff.
           right. trivial. trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
            * 
           apply Hdisjoint with phySh2Child;trivial.
          unfold getUsedPages.
           apply in_app_iff.
           right. trivial. trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
            * 
           apply Hdisjoint with phyConfigPagesList;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial. trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
            }      
        { assert(Hincl2:  incl (getMappedPages partition1 s) (getMappedPages child2 s)).
           apply verticalSharingRec with (nbPage-1);trivial.
           unfold consistency in *.
           intuition.
           apply childrenPartitionInPartitionList with closestAnc; trivial.
           
           intuition.
           destruct nbPage.
           simpl in *. intuition.
           simpl.
           replace    (n - 0 + 1) with (S n) by omega.
           trivial.
           destruct nbPage.
           simpl in *. intuition.
           simpl.
           replace    (n - 0 + 1) with (S n) by omega.
           trivial.
          unfold disjoint in *.
         intros.
         assert(Hx : In x (getMappedPages partition1 s)).
         apply accessibleMappedPagesInMappedPages; trivial. simpl.
         unfold incl in *.
         apply Hincl2 in Hx.   
         intuition subst x.
          * apply Hdisjoint with phyDescChild;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
           * 
           apply Hdisjoint with phyPDChild ;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial. trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
          * 
           apply Hdisjoint with phySh1Child;trivial.
          unfold getUsedPages.
           apply in_app_iff.
           right. trivial. trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
            * 
           apply Hdisjoint with phySh2Child;trivial.
          unfold getUsedPages.
           apply in_app_iff.
           right. trivial. trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
            * 
           apply Hdisjoint with phyConfigPagesList;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial. trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial. }
     --- assert(Horpart1 : child2 = partition1 \/ child2 <> partition1 ) by apply pageDecOrNot.
            destruct Horpart1 as [Horpart1 | Horpart1].
            +++ subst. 
              assert (Htrue : partition1 <> child1 ). 
              { unfold not;intros Hfasle;subst child1.
                contradict Hances.
                revert Hchild11 Horcurpart  Hin1 Hcurpart .
                assert(Hisparent : isParent s ). 
                { unfold consistency in *. intuition. }
                 assert( partitionDescriptorEntry s /\ parentInPartitionList s) as (Hpde & Hparentintree).
          { unfold consistency in *. intuition. } 
                revert Hnoduptree Hisparent Hparentintree Hpde. 
                clear.
                revert currentPart partition1.
                unfold getAncestors.
                induction nbPage;simpl. intuition.
                intros.               
                destruct Hchild11. intuition.
              case_eq(getParent currentPart (memory s) ); [intros parent Hparent | intros Hparent].
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
          nextEntryIsPP currentPart PPRidx entry s /\ entry <> defaultPage)).
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
           replace    (n - 0 + 1) with (S n) by omega.
           trivial.
           destruct nbPage.
           simpl in *. intuition.
           simpl.
           replace    (n - 0 + 1) with (S n) by omega.
           trivial.
          unfold disjoint in *.
         intros.
         assert(Hx : In x (getMappedPages partition1 s)).
         apply accessibleMappedPagesInMappedPages; trivial. simpl.
         unfold incl in *.   
         intuition subst x.
          * apply Hdisjoint with phyDescChild;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. apply Hincl2; trivial.
           * 
           apply Hdisjoint with phyPDChild ;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial. trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. apply Hincl2; trivial.
          * 
           apply Hdisjoint with phySh1Child;trivial.
          unfold getUsedPages.
           apply in_app_iff.
           right. trivial. trivial.
           unfold getUsedPages.
           apply in_app_iff.
            right. apply Hincl2; trivial.
            * 
           apply Hdisjoint with phySh2Child;trivial.
          unfold getUsedPages.
           apply in_app_iff.
           right. trivial. trivial.
           unfold getUsedPages.
           apply in_app_iff.
            right. apply Hincl2; trivial.
          * 
           apply Hdisjoint with phyConfigPagesList;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial. trivial.
           unfold getUsedPages.
           apply in_app_iff.
          right. apply Hincl2; trivial. }
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
           assert(Hchild2intree : In child2 (getPartitions multiplexer s)).
           { apply childrenPartitionInPartitionList with closestAnc;trivial. } 
           revert dependent child2. 
(*            revert dependent child1.  *)
           revert dependent partition1.
           assert(Hisparent : isParent s).
           { unfold consistency in *. intuition. }
           assert( partitionsIsolation s /\ isChild s /\ verticalSharing s) as (His & Hischild ).
           { unfold consistency in *. intuition. }
           intros partition1 Htmp Htmp1. 
           revert Hparentintree Hischild Hmultnone Hnoduptree Hisparent Hcurpart (* Hmulteq *).
           revert dependent closestAnc.
           revert Hpde  Hnocycle His  Hvs.
           clear .
           revert currentPart  partition1.
           unfold closestAncestor.
           unfold getAncestors.
           assert(Hnbpage : nbPage <= nbPage) by omega.
           revert Hnbpage.
           generalize nbPage at 1 (* 3 4 5 *) 5    7. 
           induction n.
           intros. simpl in *.
           intuition.
           simpl.
           intros.
           case_eq (getParent currentPart (memory s));[intros parent Hparent| intros Hparent]. 
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
          replace (n+1) with (1+n) by omega.
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
(*            * omega. *)
           * omega. 
           * unfold parentInPartitionList in *. 
             apply Hparentintree with currentPart;trivial.
             apply nextEntryIsPPgetParent;trivial.   
          * revert  Hances Hparent Hpde Hisparent Hcurpart Hparentintree Hnoduptree Hmultnone.
             clear.
            revert currentPart partition1 parent.
            intros.
            contradict Hances.
            assert(Hmult : In multiplexer (getAncestors currentPart s)).
            { apply multiplexerIsAncestor;trivial. 
              unfold not;intros; subst.
               assert(Hmult :   getParent multiplexer (memory s) = None) by intuition.
              rewrite Hmult in *. now contradict Hparent. }  
            unfold getAncestors in *.
            revert dependent currentPart.
            revert dependent partition1.
            revert parent.
            induction (nbPage+1); simpl. intuition.
            intros parent partition1 Hances.
            intros.
            rewrite Hparent in *. 
            case_eq(getParent parent (memory s) );[intros ances Hances1 | intros Hances1];
            rewrite Hances1 in *; try now contradict Hances.
            simpl in *.
            destruct Hmult as [Hmult | Hmult ].
            subst.
            assert(Hmultnoparent : getParent multiplexer (memory s) = None) by intuition.
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
              assert(getParent currentPart (memory s) = Some child2).
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
          nextEntryIsPP currentPart PPRidx entry s /\ entry <> defaultPage)).
          apply Hpde;trivial.
          do 4 right;left;trivial.
          destruct H as (entry & H1 & _).
          rewrite nextEntryIsPPgetParent in *.
          rewrite H1 in Hparent. now contradict H1.  }
         assert(Hintree : In  closestAnc (getPartitions multiplexer s)) by trivial.
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
           replace    (n - 0 + 1) with (S n) by omega.
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
           replace    (n - 0 + 1) with (S n) by omega.
           trivial.
           destruct nbPage.
           simpl in *. intuition.
           simpl.
           replace    (n - 0 + 1) with (S n) by omega.
           trivial.
           assert(Hdisjoint : disjoint (getUsedPages child1 s) (getUsedPages child2 s)).
           unfold partitionsIsolation in *.
           apply Hiso with closestAnc; trivial.
           unfold disjoint in *.
           intros.
           assert(mapped1 : In x (getMappedPages partition1 s)).
           apply accessibleMappedPagesInMappedPages; trivial.
           unfold incl in *.
           apply Hincl2 in mapped1.
           simpl. 
           intuition subst x.
           * apply Hdisjoint with phyDescChild;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right.
           apply Hincl1; trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
           * 
           apply Hdisjoint with phyPDChild ;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right.
           apply Hincl1; trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
           * 
           apply Hdisjoint with phySh1Child;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right.
           apply Hincl1; trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
           * 
           apply Hdisjoint with phySh2Child;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right.
           apply Hincl1; trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
           * 
           apply Hdisjoint with phyConfigPagesList;trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right.
           apply Hincl1; trivial.
           unfold getUsedPages.
           apply in_app_iff.
           right. trivial.
            }
 
- unfold s'.
  rewrite getAccessibleMappedPagesAddDerivation with partition1 (va entry)
  ptRefChildFromSh1  (StateLib.getIndexOfAddr descChild fstLevel) entry s true;
  trivial.
  rewrite getConfigPagesAddDerivation with partition2 (va entry)
  ptRefChildFromSh1  (StateLib.getIndexOfAddr descChild fstLevel) entry s true;
  trivial.
  assert(Hphynotchild : ~ In phyDescChild (getChildren currentPart s)).
    { assert(getMappedPage currentPD s descChild = SomePage phyDescChild /\
      ~ In descChild (getPdsVAddr currentPart level getAllVAddrWithOffset0 s)) as ( Hvaphy' & Hpds1).
      { split.
        + apply getMappedPageGetTableRoot with ptRefChild currentPart;trivial.
        + unfold isPartitionFalse in *.
          move Hnotpart at bottom.
          unfold getPdsVAddr.
          rewrite filter_In.
          apply Classical_Prop.or_not_and.
          right.
          unfold checkChild.
          rewrite nextEntryIsPPgetFstShadow in *.
          rewrite Hfstsh1.
          assert(Hind : getIndirection currentShadow1 descChild level (nbLevel - 1) s = Some ptRefChildFromSh1).
          apply getIndirectionGetTableRoot with currentPart;trivial.
          symmetry;trivial.
          rewrite Hind.
          destruct  (ptRefChildFromSh1 =? defaultPage);trivial.
          auto.
          destruct Hnotpart as [Hnotpart|Hnotpart]; rewrite Hnotpart;auto. }
     
      unfold getChildren.
      rewrite <- Hlevel.
      rewrite nextEntryIsPPgetPd in *.
      rewrite HcurrentPD.
      unfold getMappedPagesAux.
      rewrite filterOptionInIff.
      unfold getMappedPagesOption.
      rewrite in_map_iff.
      unfold not.
      intros Hfalse.
      destruct Hfalse as (samev & Hi & Hii).
      assert(descChild = samev).
      apply eqMappedPagesEqVaddrs with phyDescChild currentPD s;trivial.
        unfold getPdsVAddr in *.
        apply filter_In in Hii. intuition.
      unfold consistency in *.
      assert(Hnodup : noDupMappedPagesList s) by intuition.
      unfold noDupMappedPagesList in *.
      apply Hnodup in Hcurpart.
       move Hcurpart at bottom.
      unfold getMappedPages in Hcurpart.
      rewrite HcurrentPD in *.
      unfold getMappedPagesAux  in *.
      unfold getMappedPagesOption in Hcurpart;trivial.
      subst.
      now contradict Hpds1. } 
  assert (Hsplitlist : exists 
   nbPagesParent  l1 l2,
          getPartitionAux multiplexer s (nbPage +1) = l1 ++ [currentPart] ++
          flat_map (fun p => getPartitionAux p s nbPagesParent  )
          (getChildren currentPart s)++ l2
          /\
          getPartitionAux multiplexer s' (nbPage +1)  = l1 ++ [currentPart] ++
          flat_map (fun p => getPartitionAux p s' nbPagesParent  )
          (getChildren currentPart s')++ l2 ).
  { unfold consistency in *.
    apply getPartitionAuxSplitListNewSate' with phyDescChild ptRefChild currentShadow1
     currentPD;intuition.
    apply addPartitionKeepsAllPartitionsInTree;trivial. }
  destruct Hsplitlist as ( nbPagesParent &  l11 & l22 & Hsplitlist).

  destruct Hsplitlist as (Hsplitlist1 & Hsplitlist2).
  unfold getPartitions in *.
  apply HKDI;trivial.
  + assert (Hii1 : In partition1 (getPartitionAux multiplexer s' (nbPage + 1))) by trivial.
    assert(Hii2: In partition2 (getPartitionAux multiplexer s' (nbPage + 1))) by trivial. 
  rewrite Hsplitlist1;clear Hsplitlist1.
  rewrite Hsplitlist2 in *;clear Hsplitlist2. 
  simpl in *.
  rewrite in_app_iff in *.
  destruct Hii1 as [Hparent | Hparent]; [left;trivial|].
  right.
  simpl in *.
  destruct Hparent as [Hparent | Hparent];[left;trivial|].
  right.
  rewrite in_app_iff in *.
  destruct Hparent as [Hparent | Hparent];[ | right;trivial].
  left.
  unfold consistency in *.
  assert(HchildrenS : exists l1 l2,
  getChildren currentPart s' = l1 ++ [phyDescChild] ++ l2 /\
  getChildren currentPart s = l1 ++l2).
  apply getChildrenSplitList with ptRefChild currentShadow1 currentPD; intuition.
  destruct HchildrenS as (l1 & l2 & HchildrenS & Hchildrenprev).
  assert(Hl1 : incl l1 (getChildren currentPart s)).
  { unfold incl.
    intros.
    rewrite Hchildrenprev.
    rewrite in_app_iff;left;trivial. }
   assert(Hl22 : incl l2 (getChildren currentPart s)).
  { unfold incl.
    intros.
    rewrite Hchildrenprev.
    rewrite in_app_iff;right;trivial. }  
  rewrite  HchildrenS in Hparent.
  rewrite  Hchildrenprev . 
  simpl in Hparent.
  rewrite flat_map_app_cons in Hparent.
  rewrite flat_map_app.
  rewrite in_app_iff in *.
  simpl in *.
  assert(Hzero : getPartitionAux phyDescChild s' nbPagesParent = [phyDescChild] \/
  getPartitionAux phyDescChild s' nbPagesParent = [] ).
  {clear Hparent.
  induction nbPagesParent.
  simpl.
  right;trivial.
  simpl. left.
   assert (Hchildrennil : getChildren phyDescChild s' = nil).
   { assert(forall partition s, (* In partition (getPartitions multiplexer s)
              ->  *) incl (getChildren partition s) (getMappedPages partition s)).
      { intros.
        unfold incl.
        unfold getChildren.
        unfold getMappedPages.
        intros aa Haaa.
        destruct (StateLib.getNbLevel ); try now contradict Haaa.
        destruct  (StateLib.getPd partition (memory s0)); try now contradict Haaa.
        unfold getMappedPagesAux in *.
        rewrite filterOptionInIff in *.
        unfold getMappedPagesOption in *.
        rewrite in_map_iff in *.
        destruct Haaa as (x & Hx1 & Hx2).
        exists x;split;trivial.
        unfold getPdsVAddr in Hx2.
        apply filter_In in Hx2.
        destruct Hx2;trivial. }
   (*   assert(Hparent : In phyDescChild (getPartitions multiplexer s')).
     apply childrenPartitionInPartitionList with currentPart;trivial.
     apply addPartitionKeepsAllPartitionsInTree;trivial. 
     apply H in Hparent. *)
     unfold incl in *.
(*      clear IHn. 
     
     fold s'. *)
     assert(Hbb1 :  forall (partition : page) (s : state) (a : page),
      In a (getChildren partition s) -> In a (getMappedPages partition s)) by trivial.
     generalize (Hbb1  phyDescChild s'); clear Hbb1; intros Hbb1.
     rewrite Hmappednull in *.
     destruct (getChildren phyDescChild s') .
     trivial. 
     assert(In p []).
     apply Hbb1.
     simpl;left;trivial. contradiction. }
  rewrite Hchildrennil;simpl;trivial.   
  }
  assert(Hor: In partition1 (flat_map (fun p : page => getPartitionAux p s' nbPagesParent) l1) \/
          In partition1
            (
             flat_map (fun p : page => getPartitionAux p s' nbPagesParent) l2)).
  { destruct Hzero as [Hzero | Hzero]; rewrite Hzero in *; simpl in *.
    +
    destruct Hparent as [Hparent | [ Hparent | Hparent]] .
    left;trivial.
    subst partition1; now contradict Hnoteqpart1.
    right;trivial.
    + trivial.
    }
  clear Hparent Hzero.
  rename Hor into Hparent.
  destruct Hparent as [Hparent | Hparent] .
  ++ left.
     rewrite in_flat_map in *.
     destruct Hparent as (child & Hancestor1 & Hancestor2).
     exists child;split;trivial.
     assert(Hget : getPartitionAux child s nbPagesParent = 
     getPartitionAux child s' nbPagesParent).
     { unfold consistency in *. clear H0.
         
        apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
        intuition. intuition. intuition. intuition. 
        
        
        apply childrenPartitionInPartitionList with currentPart;trivial.
        rewrite Hchildrenprev.
        rewrite in_app_iff.
        left;trivial.
        
        apply noCycleInPartitionTree2;trivial.
        intuition. intuition. intuition.
        intuition. }
      trivial.
    rewrite Hget;trivial.
  ++ right.
     rewrite in_flat_map in *.
     destruct Hparent as (child & Hancestor1 & Hancestor2).
     exists child;split;trivial.
     assert(Hget : getPartitionAux child s nbPagesParent = 
     getPartitionAux child s' nbPagesParent).
     { unfold consistency in *. clear H0.
      (*  intuition. *)
        apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial. intuition. intuition. intuition. intuition.
        apply childrenPartitionInPartitionList with currentPart;trivial.
        rewrite Hchildrenprev.
        rewrite in_app_iff.
        right;trivial.
        apply noCycleInPartitionTree2;trivial.
        intuition. intuition. intuition. intuition. 
         }
      trivial.
   rewrite Hget;trivial.
 +  
  rewrite Hsplitlist1;clear Hsplitlist1.
  rewrite Hsplitlist2 in *;clear Hsplitlist2. 
  simpl in *.
  rewrite in_app_iff in *.  
  assert(Htmp :  In partition2 l11 \/
      In partition2
        (currentPart
         :: flat_map (fun p : page => getPartitionAux p s' nbPagesParent)
              (getChildren currentPart s') ++ l22)) by trivial.
  destruct Htmp as [Hparent | Hparent]; [left;trivial|].
  right.
  simpl in *.
  destruct Hparent as [Hparent | Hparent];[left;trivial|].
  right.
  rewrite in_app_iff in *.
  destruct Hparent as [Hparent | Hparent];[ | right;trivial].
  left.
  unfold consistency in *.
  assert(HchildrenS : exists l1 l2,
  getChildren currentPart s' = l1 ++ [phyDescChild] ++ l2 /\
  getChildren currentPart s = l1 ++l2).
  apply getChildrenSplitList with ptRefChild currentShadow1 currentPD; intuition.
  destruct HchildrenS as (l1 & l2 & HchildrenS & Hchildrenprev).
  assert(Hl1 : incl l1 (getChildren currentPart s)).
  { unfold incl.
    intros.
    rewrite Hchildrenprev.
    rewrite in_app_iff;left;trivial. }
   assert(Hl22 : incl l2 (getChildren currentPart s)).
  { unfold incl.
    intros.
    rewrite Hchildrenprev.
    rewrite in_app_iff;right;trivial. }  
  rewrite  HchildrenS in Hparent.
  rewrite  Hchildrenprev . 
  simpl in Hparent.
  rewrite flat_map_app_cons in Hparent.
  rewrite flat_map_app.
  rewrite in_app_iff in *.
  simpl in *.
  assert(Hzero : getPartitionAux phyDescChild s' nbPagesParent = [phyDescChild] \/
  getPartitionAux phyDescChild s' nbPagesParent = [] ).
  {clear Hparent.
  induction nbPagesParent.
  simpl.
  right;trivial.
  simpl. left.
   assert (Hchildrennil : getChildren phyDescChild s' = nil).
   { assert(Htrue : forall partition s, (* In partition (getPartitions multiplexer s)
              ->  *) incl (getChildren partition s) (getMappedPages partition s)).
      { intros.
        unfold incl.
        unfold getChildren.
        unfold getMappedPages.
        intros a Ha.
        destruct (StateLib.getNbLevel ); try now contradict H.
        destruct  (StateLib.getPd partition (memory s0)); try now contradict H.
        unfold getMappedPagesAux in *.
        rewrite filterOptionInIff in *.
        unfold getMappedPagesOption in *.
        rewrite in_map_iff in *.
        destruct Ha as (x & Hx1 & Hx11).
        
        exists x;split;trivial.
        unfold getPdsVAddr in *.
        apply filter_In in Hx11.
        destruct Hx11;trivial. } (* 
     assert(Hparent : In phyDescChild (getPartitions multiplexer s')).
     apply childrenPartitionInPartitionList with currentPart;trivial.
     apply addPartitionKeepsAllPartitionsInTree;trivial. *) 
     
     unfold incl in *.
     generalize (Htrue  phyDescChild s'); clear H; intros H.
     rewrite Hmappednull in *.
     destruct (getChildren phyDescChild s') .
     trivial. 
     assert(In p []).
     apply H.
     simpl;left;trivial.
     now contradict H0. }
  rewrite Hchildrennil;simpl;trivial.   
  }
  assert( Htrue : In partition2 (flat_map (fun p : page => getPartitionAux p s'  nbPagesParent) l1) \/
          In partition2
            (
             flat_map (fun p : page => getPartitionAux p s'  nbPagesParent) l2)).
  { destruct Hzero as [Hzero | Hzero]; rewrite Hzero in *; simpl in *.
    + destruct Hparent as [Hparent | [ Hparent | Hparent]] .
    left;trivial.
    subst partition2; now contradict Hnoteqpart2.
    right;trivial.
    + trivial.
    }
  clear Hparent Hzero.
  rename Htrue into Hparent.
  destruct Hparent as [Hparent | Hparent] .
  ++ left.
     rewrite in_flat_map in *.
     destruct Hparent as (child & Hancestor1 & Hancestor2).
     exists child;split;trivial.
     assert(Hget :  getPartitionAux child s  nbPagesParent = 
     getPartitionAux child s'  nbPagesParent).
     { unfold consistency in *.
       
        apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial. intuition. intuition. intuition. intuition. 
        apply childrenPartitionInPartitionList with currentPart;trivial.
        rewrite Hchildrenprev.
        rewrite in_app_iff.
        left;trivial.
        apply noCycleInPartitionTree2;trivial. intuition.
        intuition. intuition. intuition. }
      trivial.
   rewrite Hget;trivial.
  ++ right.
     rewrite in_flat_map in *.
     destruct Hparent as (child & Hancestor1 & Hancestor2).
     exists child;split;trivial.
     assert(Hget : getPartitionAux child s  nbPagesParent = 
     getPartitionAux child s'  nbPagesParent).
     { unfold consistency in *.
        apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial. intuition. intuition. intuition. intuition. 
        apply childrenPartitionInPartitionList with currentPart;trivial.
        rewrite Hchildrenprev.
        rewrite in_app_iff.
        right;trivial.
        apply noCycleInPartitionTree2;trivial. intuition.
        intuition. intuition. intuition.  }
   rewrite Hget;trivial.
Qed. (** kernel data isolation *)

Lemma partitionDescriptorEntryAddPartition 
entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
(* partitionDescriptorEntry s ->
noDupConfigPagesList s ->
noDupMappedPagesList s -> *)
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild (getAllVAddrWithOffset0) -> 
 partitionDescriptorEntry s' .
Proof.
intros s' HisParent Hcons Hiso Hvs (* Hpde Hnodupconf Hnodupmap *) Hlookup Hppsh3 Hppsh2 Hppsh1 Hpppd Hcurpart Hlevel HcurrentPD Hpost
Hnewpd Hnewsh1 Hnewsh2 Hnewsh31 Hnewsh32 Hnewsh33 HmappedDesc
HmappedPD Hmappedsh1 HmappedSh2 Hmappedsh3 Hnotconfig Hroot Hptnotnull Hep
Hpresent Hfstsh1 Hnotpart Hsh1 Hptsh1notnull
HphyPDcontent HphySh1content (*HphySh2content HphyListcontent 1 HphyListcontent2 HphyListcontent3  *)
HnotConfig HnotConfig1 HnotConfig2 HnotConfig3 HnotConfig4
Ha1 Ha2 Ha3 Ha4 Ha5 .
 intros (* Hiso Hkdi Hvs Hcons Hlookup Hlevel*) HcurpartS
Hvapr Hpppr Hva3 Hpp3 Hva2 Hpp2  Hva1 Hpp1 Hvapd Hpppd' Hva0 Hpp0
Hnot1 Hnot2 Hnot3 Hnot4 Hnot5
intros ;subst.
intros;subst.
unfold partitionDescriptorEntry in *.
(* set (s' := {|
     currentPartition := currentPartition s;
     memory := add table idx (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}). *)
intros.
assert(Hidx : idxroot < tableSize - 1 ).
{  assert(tableSizeLowerBound < tableSize).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    intuition subst.
    unfold PDidx.
    unfold CIndex.
    case_eq( lt_dec 2 tableSize );intros;
    simpl;omega.
    unfold sh1idx.
    unfold CIndex.
    case_eq( lt_dec 4 tableSize );intros;
    simpl;omega.
     unfold sh2idx.
    unfold CIndex.
    case_eq( lt_dec 6 tableSize );intros;
    simpl;omega.
     unfold sh3idx.
    unfold CIndex.
    case_eq( lt_dec 8 tableSize );intros;
    simpl;omega.
    unfold PPRidx.
    unfold CIndex.
    
    case_eq( lt_dec 10 tableSize );intros;
    simpl;omega.    
    unfold PRidx.
    unfold CIndex.
    case_eq( lt_dec 0 tableSize );intros;
    simpl;omega. }
assert (HVA : forall p idx, isVA p idx s -> isVA p idx s').
    { intros.
      apply  isVAAddDerivation with entry;trivial. }
assert (HPE : forall p idx x, nextEntryIsPP p idx x s -> 
                  nextEntryIsPP p idx x s').
    { intros. apply nextEntryIsPPAddDerivation with entry;trivial. }
assert(Hparteq : partition = phyDescChild  \/ partition <> phyDescChild ) by apply pageDecOrNot.

destruct Hparteq as [Hparteq |Hparteq ].
- subst.
  try repeat split;trivial.
  + intuition subst; apply HVA;trivial.
  + apply beq_nat_false in Hnot1.
    apply beq_nat_false in Hnot2.
    apply beq_nat_false in Hnot3.
    apply beq_nat_false in Hnot4.
    apply beq_nat_false in Hnot5.
    intuition subst;eexists;split; [ try apply HPE;try eassumption|
    intros Hfalse;subst;intuition
    ].
    contradict Hfalse.
    unfold consistency in *.
    unfold currentPartitionIsNotDefaultPage in *. 
      intuition.
 - assert(Hpde : partitionDescriptorEntry s).
      { unfold consistency in *. intuition. } 
   assert(HcurEq : partition = (currentPartition s) \/ partition <> (currentPartition s)) by apply pageDecOrNot.
   destruct HcurEq as [HcurEq | HcurEq].
    * assert(Hpde' : idxroot < tableSize - 1 /\
                          isVA (currentPartition s) idxroot s /\
                          (exists entry0 : page, nextEntryIsPP (currentPartition s)  idxroot entry0 s/\ entry0 <> defaultPage)).
      
      apply Hpde;trivial. 
      subst. split;trivial.  
      destruct Hpde' as (Hi1 & Hi2 & Hi3).
      try repeat split;trivial.
      + intuition subst; apply HVA;trivial.
      + destruct Hi3 as (entry0 & Hentry & Htrue).
         exists entry0;split;trivial.
         apply HPE;trivial.
         * assert( Hpde' : idxroot < tableSize - 1 /\ isVA partition idxroot s /\
             (exists entry : page, nextEntryIsPP partition idxroot entry s /\ 
             entry <> defaultPage)).
          { apply Hpde;trivial.
            unfold consistency in *. 
            apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
            (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
            phyConfigPagesList ptRefChild currentShadow1;trivial.
            intuition. intuition. }
            destruct Hpde' as (Hi1 & Hi2 & Hi3).
            try repeat split;trivial.
            + intuition subst; apply HVA;trivial.
            + destruct Hi3 as (entry0 & Hentry & Htrue).
               exists entry0;split;trivial.
               apply HPE;trivial.
Qed.

Lemma readPhyEntryOrReadPresentIsPE table idx s :
(StateLib.readPhyEntry table idx (memory s) = Some defaultPage \/
StateLib.readPresent table idx (memory s) = Some false) ->
isPE table idx s.
Proof.
intros [H | H].
unfold StateLib.readPhyEntry in *.
case_eq (lookup table idx (memory s) beqPage beqIndex );[ intros v Hlookup | intros Hlookup];
rewrite Hlookup in *; try now contradict H. 
destruct v; try now contradict H.  
unfold isPE.
rewrite Hlookup. trivial.
unfold StateLib.readPresent in *.
case_eq (lookup table idx (memory s) beqPage beqIndex );[ intros v Hlookup | intros Hlookup];
rewrite Hlookup in *; try now contradict H.
destruct v; try now contradict H. 
unfold isPE.
rewrite Hlookup. trivial.
Qed.
Lemma readVirEntryOrReadPDFlagIsVE table idx s :
(StateLib.readVirEntry table idx (memory s) = Some defaultVAddr \/
StateLib.readPDflag table idx (memory s) = Some false) ->
isVE table idx s.
Proof.
intros [H | H].
+ unfold StateLib.readVirEntry in *.
case_eq (lookup table idx (memory s) beqPage beqIndex );[ intros v Hlookup | intros Hlookup]; 
rewrite Hlookup in *;    try now contradict H.
destruct v; try now contradict H.
unfold isVE. rewrite Hlookup. trivial.
+
unfold StateLib.readPDflag in *.
case_eq (lookup table idx (memory s) beqPage beqIndex );[ intros v Hlookup | intros Hlookup];
rewrite Hlookup in *; try now contradict H.
destruct v; try now contradict H. 
unfold isVE.
rewrite Hlookup. trivial.
Qed.

Lemma readVirtualIsVA table idx s :
StateLib.readVirtual table idx (memory s) = Some defaultVAddr ->
isVA table idx s.
Proof.

unfold StateLib.readVirtual in *.
intros.
case_eq (lookup table idx (memory s) beqPage beqIndex );[ intros v Hlookup | intros Hlookup]; 
rewrite Hlookup in *;    try now contradict H.
destruct v; try now contradict H.
unfold isVA. rewrite Hlookup. trivial.
Qed.

Lemma dataStructurePdAsRootAddPartition 
entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
noDupMappedPagesList s ->
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *)
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 -> 
dataStructurePdSh1Sh2asRoot PDidx s'.
Proof.
intros s' HisParent Hcons Hiso Hvs Hpde Hnodupconf Hnodupmap Hlookup Hppsh3 Hppsh2 Hppsh1 Hpppd Hcurpart Hlevel HcurrentPD Hpost
Hnewpd Hnewsh1 Hnewsh2 Hnewsh31 (* Hnewsh32 Hnewsh33 *) HmappedDesc
HmappedPD Hmappedsh1 HmappedSh2 Hmappedsh3 Hnotconfig Hroot Hptnotnull Hep
Hpresent Hfstsh1 Hnotpart Hsh1 Hptsh1notnull
HphyPDcontent HphySh1content HphySh2content (*HphyListcontent 1 HphyListcontent2 HphyListcontent3  *)
HnotConfig HnotConfig1 HnotConfig2 HnotConfig3 HnotConfig4
Ha1 Ha2 Ha3 Ha4 Ha5 .
 intros (* Hiso Hkdi Hvs Hcons Hlookup Hlevel*) HcurpartS
Hvapr Hpppr Hva3 Hpp3 Hva2 Hpp2  Hva1 Hpp1 Hvapd Hpppd' Hva0 Hpp0
Hnot1 Hnot2 Hnot3 Hnot4 Hnot5.  
intros ;subst.
intros;subst.
unfold consistency in *.
unfold dataStructurePdSh1Sh2asRoot.
intros partition HinTreeS structRoot HstructRoot va.
intro.
intros nbL stop HnbLS table idx Hind. 
  assert (HVA : forall p idx, isVA p idx s -> isVA p idx s').
    { intros.
      apply  isVAAddDerivation with entry;trivial. }
     assert (HPE : forall p idx, isPE p idx s -> isPE p idx s').
    { intros.
      apply  isPEAddDerivation with entry;trivial. }
      assert (HVE : forall p idx, isVE p idx s -> isVE p idx s').
    { intros.
      apply  isVEAddDerivation with entry;trivial. }
assert (HPP : forall p idx x, nextEntryIsPP p idx x s -> 
                  nextEntryIsPP p idx x s').
    { intros. apply nextEntryIsPPAddDerivation with entry;trivial. }
assert(HindS : getIndirection structRoot va nbL stop s'  =
  getIndirection structRoot va nbL stop s ).
 { apply getIndirectionAddDerivation with entry;trivial. }
 rewrite HindS in *. clear HindS.
 assert(HppS :nextEntryIsPP partition PDidx structRoot s') ; trivial.
 assert(Hpps : nextEntryIsPP partition PDidx structRoot s).
 { rewrite nextEntryIsPPAddDerivation with entry;trivial.
 unfold s' in HppS.
 eassumption.
 trivial.  }
assert(Hparteq : partition = phyDescChild  \/ partition <> phyDescChild ) by apply pageDecOrNot.
destruct Hparteq as [Hparteq |Hparteq ].
- subst. 
  assert(Heq : structRoot = phyPDChild).
  { rewrite nextEntryIsPPgetPd in Hpps.
  symmetry.
  apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
  subst.
  rewrite <- HnbLS in *.
  inversion Hlevel.
  subst.
  revert HPE HphyPDcontent HnbLS Hind Hnot1.
  clear.
  revert nbL table.
  induction stop; simpl in *.
  + right.
    inversion Hind;subst. 
    split.
    * assert( Hor : 0 < nbL \/ 0 = nbL) by omega.
      destruct Hor as [Hor | Hor].
      { left;split;trivial.
        apply HPE;trivial.
        destruct HphyPDcontent with idx as ( Hpe1 & Hpe2).
        apply readPhyEntryOrReadPresentIsPE;left;trivial. }
      { right.
        split;trivial.
        omega.
        right;right;split;trivial.
        apply HPE;trivial. 
        destruct HphyPDcontent with idx as ( Hpe1 & Hpe2).
        apply readPhyEntryOrReadPresentIsPE;left;trivial. }
    * apply beq_nat_false in Hnot1.
      unfold not;intros Hfalse;subst.
      now contradict Hnot1.
  + intros.
    case_eq(StateLib.Level.eqb nbL fstLevel); intros Hlevel;
    rewrite Hlevel in *.
    inversion Hind;subst.
    right.  
    split.
    * assert( Hor :S stop < nbL \/ S stop >= nbL) by omega.
      destruct Hor as [Hor | Hor].
      { left. split;trivial. apply HPE;trivial.  
        destruct HphyPDcontent with idx as ( Hpe1 & Hpe2).
        apply readPhyEntryOrReadPresentIsPE;left;trivial. }
      { right.
        split;trivial.
        right;right;split;trivial.
        apply HPE;trivial. 
        destruct HphyPDcontent with idx as ( Hpe1 & Hpe2).
        apply readPhyEntryOrReadPresentIsPE;left;trivial. }
    * apply beq_nat_false in Hnot1.
      unfold not;intros Hfalse;subst.
      now contradict Hnot1.
    * destruct HphyPDcontent with (StateLib.getIndexOfAddr va nbL)  as ( Hpe1 & Hpe2).
      rewrite Hpe1 in *.
      assert (Htrue : (defaultPage =? defaultPage) = true).      
      rewrite beq_nat_refl with defaultPage. reflexivity.
      rewrite Htrue in *.
      inversion Hind. 
      left;trivial.
  - assert(Hcurparteq : (currentPartition s) = partition  \/
                (currentPartition s) <> partition ) by apply pageDecOrNot.
    destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
    subst.
    + assert(HdsS : table = defaultPage \/
              (stop < nbL /\ isPE table idx s \/
               stop >= nbL /\
               (isVE table idx s /\ PDidx = sh1idx \/
                isVA table idx s /\ PDidx = sh2idx \/ isPE table idx s /\ PDidx = PDidx)) /\
              table <> defaultPage).
      { assert(Hdss : dataStructurePdSh1Sh2asRoot PDidx s ) by intuition.
        unfold  dataStructurePdSh1Sh2asRoot in Hdss.
        apply Hdss with (currentPartition s) structRoot va;trivial. }
      destruct HdsS as [HdsS | HdsS];[left;trivial|right].
      destruct HdsS as (HdsS & Hnotnull).
      split;trivial. 
      destruct HdsS as [(Hstop &HdsS) |(Hstop& HdsS)];[left|right].
      * split;trivial. apply HPE;trivial.
      * split;trivial.
        destruct HdsS as [(HdsS & Hidxrot) |[(HdsS & Hidxrot)|(HdsS& Hidxrot)]].
        left;split;trivial. apply HVE;trivial.
        right;left;split;trivial. apply HVA;trivial.
        right;right;split;trivial. apply HPE;trivial.
    + assert(HdsS : table = defaultPage \/
            (stop < nbL /\ isPE table idx s \/
             stop >= nbL /\
             (isVE table idx s /\ PDidx = sh1idx \/
              isVA table idx s /\ PDidx = sh2idx \/ isPE table idx s /\ PDidx = PDidx)) /\
            table <> defaultPage).
      { assert(Hdss : dataStructurePdSh1Sh2asRoot PDidx s ) by intuition.
        unfold  dataStructurePdSh1Sh2asRoot in Hdss.
        apply Hdss with partition structRoot va;trivial.
        apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
        (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
        phyConfigPagesList ptRefChild currentShadow1;trivial. unfold not;intros Hfalse.
        subst. now contradict Hcurparteq. }
      destruct HdsS as [HdsS | HdsS];[left;trivial|right].
      destruct HdsS as (HdsS & Hnotnull).
      split;trivial. 
      destruct HdsS as [(Hstop &HdsS) |(Hstop& HdsS)];[left|right].
      * split;trivial. apply HPE;trivial.
      * split;trivial.
        destruct HdsS as [(HdsS & Hidxrot) |[(HdsS & Hidxrot)|(HdsS& Hidxrot)]].
        left;split;trivial. apply HVE;trivial.
        right;left;split;trivial. apply HVA;trivial.
        right;right;split;trivial. apply HPE;trivial.
Qed.

Lemma fstLevelEq0 (nbL : level): 
 nbL <> fstLevel -> 0 <> nbL.
Proof.
intros.
unfold not;intros.   
unfold fstLevel in *.
unfold CLevel in *.
case_eq( lt_dec 0 nbLevel );intros;rewrite H1 in *.
simpl in *.
destruct nbL.
simpl in *.
subst.
contradict H.
f_equal. apply proof_irrelevance.
assert(0 < nbLevel) by apply nbLevelNotZero.
omega.
Qed. 

        Lemma fstLevelSFalse stop: 
        S stop < fstLevel -> False.
        Proof.
        unfold fstLevel.
        unfold CLevel.
        case_eq( lt_dec 0 nbLevel );intros. 
simpl in *.
omega.
assert(0 < nbLevel) by apply nbLevelNotZero.
omega.
Qed.
 
         Lemma fstLevelGt0False : 
        0 < fstLevel -> False.
        Proof.

        unfold fstLevel in *. intros Hor. unfold CLevel in Hor.
        case_eq( lt_dec 0 nbLevel );intros;rewrite H in *.
        simpl in *.
        omega.
        assert(0 < nbLevel) by apply nbLevelNotZero.
        omega.
        Qed.
Lemma dataStructureSh1AsRootAddPartition 
entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
noDupMappedPagesList s ->
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 -> 
dataStructurePdSh1Sh2asRoot sh1idx s'.
Proof.
intros s' HisParent Hcons Hiso Hvs Hpde Hnodupconf Hnodupmap Hlookup Hppsh3 Hppsh2 Hppsh1 Hpppd Hcurpart Hlevel HcurrentPD Hpost
Hnewpd Hnewsh1 Hnewsh2 Hnewsh31(*  Hnewsh32 Hnewsh33 *) HmappedDesc
HmappedPD Hmappedsh1 HmappedSh2 Hmappedsh3 Hnotconfig Hroot Hptnotnull Hep
Hpresent Hfstsh1 Hnotpart Hsh1 Hptsh1notnull
HphyPDcontent HphySh1content HphySh2content HphyListcontent(*1 HphyListcontent2 HphyListcontent3  *)
HnotConfig HnotConfig1 HnotConfig2 HnotConfig3 HnotConfig4
Ha1 Ha2 Ha3 Ha4 Ha5 .
 intros (* Hiso Hkdi Hvs Hcons Hlookup Hlevel*) HcurpartS
Hvapr Hpppr Hva3 Hpp3 Hva2 Hpp2  Hva1 Hpp1 Hvapd Hpppd' Hva0 Hpp0
Hnot1 Hnot2 Hnot3 Hnot4 Hnot5  
intros ;subst.
intros;subst.
unfold consistency in *.
unfold dataStructurePdSh1Sh2asRoot.
intros partition HinTreeS structRoot HstructRoot va.
intro.
intros nbL stop HnbLS table idx Hind. 
  assert (HVA : forall p idx, isVA p idx s -> isVA p idx s').
    { intros.
      apply  isVAAddDerivation with entry;trivial. }
     assert (HPE : forall p idx, isPE p idx s -> isPE p idx s').
    { intros.
      apply  isPEAddDerivation with entry;trivial. }
      assert (HVE : forall p idx, isVE p idx s -> isVE p idx s').
    { intros.
      apply  isVEAddDerivation with entry;trivial. }
assert (HPP : forall p idx x, nextEntryIsPP p idx x s -> 
                  nextEntryIsPP p idx x s').
    { intros. apply nextEntryIsPPAddDerivation with entry;trivial. }
assert(HindS : getIndirection structRoot va nbL stop s'  =
  getIndirection structRoot va nbL stop s ).
 { apply getIndirectionAddDerivation with entry;trivial. }
 rewrite HindS in *. clear HindS.
 assert(HppS :nextEntryIsPP partition sh1idx structRoot s') ; trivial.
 assert(Hpps : nextEntryIsPP partition sh1idx structRoot s).
 { rewrite nextEntryIsPPAddDerivation with entry;trivial.
 unfold s' in HppS.
 eassumption.
 trivial.  }
assert(Hparteq : partition = phyDescChild  \/ partition <> phyDescChild ) by apply pageDecOrNot.
destruct Hparteq as [Hparteq |Hparteq ].
- subst. 
  assert(Heq : structRoot = phySh1Child).
  { rewrite nextEntryIsPPgetFstShadow in Hpps.
    symmetry.
    apply getSh1NextEntryIsPPEq with phyDescChild s;trivial. }
  subst.
  rewrite <- HnbLS in *.
  inversion Hlevel.
  subst.
  revert HPE HVE HphySh2content HnbLS Hind Hnot2.
  clear.
  revert nbL table.
  induction stop; simpl in *.
  + right.
    inversion Hind;subst. 
    split.
    * assert( Hor : 0 < nbL \/ 0 = nbL) by omega.
      destruct Hor as [Hor | Hor].
      { left;split;trivial.
        apply HPE;trivial.
        unfold isWellFormedFstShadow in *.
        destruct HphySh2content as [(Hl & HphySh1content) | (Hl & HphySh1content)]. 
        destruct HphySh1content with idx as ( Hpe1 & Hpe2).
        apply readPhyEntryOrReadPresentIsPE;left;trivial.
        subst.
        apply fstLevelGt0False in Hor.
        now contradict Hor.  }
      { right.
        split;trivial.
        omega. left;split;trivial.
        apply HVE;trivial. 
        unfold isWellFormedFstShadow in *.
        destruct HphySh2content as [(Hl & HphySh1content) | (Hl & HphySh1content)].
        contradict Hor.
        apply fstLevelEq0;trivial.
        destruct HphySh1content with idx as ( Hpe1 & Hpe2).
        apply readVirEntryOrReadPDFlagIsVE;left;trivial. }
    * apply beq_nat_false in Hnot2.
      unfold not;intros Hfalse;subst.
      now contradict Hnot2.
  + intros.
    case_eq(StateLib.Level.eqb nbL fstLevel); intros Hlevel;
    rewrite Hlevel in *.
    inversion Hind;subst.
    right.  
    split.
    * assert( Hor :S stop < nbL \/ S stop >= nbL) by omega.
      destruct Hor as [Hor | Hor].
      { left. split;trivial. apply HPE;trivial.
        unfold isWellFormedFstShadow in *.
        destruct HphySh2content as [(Hl & HphySh1content) | (Hl & HphySh1content)].
        destruct HphySh1content with idx as ( Hpe1 & Hpe2).
        apply readPhyEntryOrReadPresentIsPE;left;trivial.
        subst.
        apply fstLevelSFalse in Hor.
        now contradict Hor. }
      { right.
        split;trivial.
        left;split;trivial.
        apply HVE;trivial.
         unfold isWellFormedFstShadow in *.
        destruct HphySh2content as [(Hl & HphySh1content) | (Hl & HphySh1content)].
        apply levelEqBEqNatTrue in Hlevel.
        subst.
        now contradict Hl.
        destruct HphySh1content with idx as ( Hpe1 & Hpe2).
        apply readVirEntryOrReadPDFlagIsVE;left;trivial. }
    * apply beq_nat_false in Hnot2.
      unfold not;intros Hfalse;subst.
      now contradict Hnot2.
    * unfold isWellFormedFstShadow in *.
      destruct HphySh2content as [(Hl & HphySh1content) | (Hl & HphySh1content)].
     ++ destruct HphySh1content with (StateLib.getIndexOfAddr va nbL)  as ( Hpe1 & Hpe2).
        rewrite Hpe1 in *.
        assert (Htrue : (defaultPage =? defaultPage) = true).      
        rewrite beq_nat_refl with defaultPage. reflexivity.
        rewrite Htrue in *.
        inversion Hind. 
        left;trivial.
     ++ destruct HphySh1content with (StateLib.getIndexOfAddr va nbL)  as ( Hpe1 & Hpe2).
        clear IHstop HphySh1content.
        unfold StateLib.readVirEntry in *.
        unfold StateLib.readPhyEntry in *.
        case_eq(lookup phySh1Child (StateLib.getIndexOfAddr va nbL) (memory s) beqPage beqIndex);
        [intros v Hlookup| intros Hlookup];rewrite Hlookup in *; try now contradict Hpe1.
        case_eq(v);intros p H; rewrite H in *; try now contradict Hpe1.
- assert(Hcurparteq : (currentPartition s) = partition  \/
                (currentPartition s) <> partition ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  subst.
  + assert(HdsS : table = defaultPage \/
              (stop < nbL /\ isPE table idx s \/
               stop >= nbL /\
               (isVE table idx s /\ sh1idx = sh1idx \/
                isVA table idx s /\ sh1idx = sh2idx \/ isPE table idx s /\ sh1idx = PDidx)) /\
              table <> defaultPage).
    { assert(Hdss : dataStructurePdSh1Sh2asRoot sh1idx s ) by intuition.
      unfold  dataStructurePdSh1Sh2asRoot in Hdss.
      apply Hdss with (currentPartition s) structRoot va;trivial. }
      destruct HdsS as [HdsS | HdsS];[left;trivial|right].
      destruct HdsS as (HdsS & Hnotnull).
      split;trivial. 
      destruct HdsS as [(Hstop &HdsS) |(Hstop& HdsS)];[left|right].
      * split;trivial. apply HPE;trivial.
      * split;trivial.
        destruct HdsS as [(HdsS & Hidxrot) |[(HdsS & Hidxrot)|(HdsS& Hidxrot)]].
        left;split;trivial. apply HVE;trivial.
        right;left;split;trivial. apply HVA;trivial.
        right;right;split;trivial. apply HPE;trivial.
  + assert(HdsS : table = defaultPage \/
            (stop < nbL /\ isPE table idx s \/
             stop >= nbL /\
             (isVE table idx s /\ sh1idx = sh1idx \/
              isVA table idx s /\ sh1idx = sh2idx \/ isPE table idx s /\ sh1idx = PDidx)) /\
            table <> defaultPage).
    { assert(Hdss : dataStructurePdSh1Sh2asRoot sh1idx s ) by intuition.
      unfold  dataStructurePdSh1Sh2asRoot in Hdss.
      apply Hdss with partition structRoot va;trivial.
      apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial. unfold not;intros Hfalse.
      subst. now contradict Hcurparteq. }
      destruct HdsS as [HdsS | HdsS];[left;trivial|right].
      destruct HdsS as (HdsS & Hnotnull).
      split;trivial. 
      destruct HdsS as [(Hstop &HdsS) |(Hstop& HdsS)];[left|right].
      * split;trivial. apply HPE;trivial.
      * split;trivial.
        destruct HdsS as [(HdsS & Hidxrot) |[(HdsS & Hidxrot)|(HdsS& Hidxrot)]].
        left;split;trivial. apply HVE;trivial.
        right;left;split;trivial. apply HVA;trivial.
        right;right;split;trivial. apply HPE;trivial.
Qed.

Lemma dataStructureSh2AsRootAddPartition 
entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
partitionDescriptorEntry s ->
noDupConfigPagesList s ->
noDupMappedPagesList s ->
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 -> 
dataStructurePdSh1Sh2asRoot sh2idx s'.
Proof.
intros s' HisParent Hcons Hiso Hvs Hpde Hnodupconf Hnodupmap Hlookup Hppsh3 Hppsh2 Hppsh1 Hpppd Hcurpart Hlevel HcurrentPD Hpost
Hnewpd Hnewsh1 Hnewsh2 Hnewsh31 (* Hnewsh32 Hnewsh33 *) HmappedDesc
HmappedPD Hmappedsh1 HmappedSh2 Hmappedsh3 Hnotconfig Hroot Hptnotnull Hep
Hpresent Hfstsh1 Hnotpart Hsh1 Hptsh1notnull
HphyPDcontent HphySh1content HphySh2content HphyListcontent(* 1 HphyListcontent2 HphyListcontent3  *)
HnotConfig HnotConfig1 HnotConfig2 HnotConfig3 HnotConfig4
Ha1 Ha2 Ha3 Ha4 Ha5 .
 intros (* Hiso Hkdi Hvs Hcons Hlookup Hlevel*) HcurpartS
Hvapr Hpppr Hva3 Hpp3 Hva2 Hpp2  Hva1 Hpp1 Hvapd Hpppd' Hva0 Hpp0
Hnot1 Hnot2 Hnot3 Hnot4 Hnot5  
intros ;subst.
intros;subst.
unfold consistency in *.
unfold dataStructurePdSh1Sh2asRoot.
intros partition HinTreeS structRoot HstructRoot va.
intro.
intros nbL stop HnbLS table idx Hind. 
  assert (HVA : forall p idx, isVA p idx s -> isVA p idx s').
    { intros.
      apply  isVAAddDerivation with entry;trivial. }
     assert (HPE : forall p idx, isPE p idx s -> isPE p idx s').
    { intros.
      apply  isPEAddDerivation with entry;trivial. }
      assert (HVE : forall p idx, isVE p idx s -> isVE p idx s').
    { intros.
      apply  isVEAddDerivation with entry;trivial. }
assert (HPP : forall p idx x, nextEntryIsPP p idx x s -> 
                  nextEntryIsPP p idx x s').
    { intros. apply nextEntryIsPPAddDerivation with entry;trivial. }
assert(HindS : getIndirection structRoot va nbL stop s'  =
  getIndirection structRoot va nbL stop s ).
 { apply getIndirectionAddDerivation with entry;trivial. }
 rewrite HindS in *. clear HindS.
 assert(HppS :nextEntryIsPP partition sh2idx structRoot s') ; trivial.
 assert(Hpps : nextEntryIsPP partition sh2idx structRoot s).
 { rewrite nextEntryIsPPAddDerivation with entry;trivial.
 unfold s' in HppS.
 eassumption.
 trivial.  }
assert(Hparteq : partition = phyDescChild  \/ partition <> phyDescChild ) by apply pageDecOrNot.
destruct Hparteq as [Hparteq |Hparteq ].
- subst. 
  assert(Heq : structRoot = phySh2Child).
  { rewrite nextEntryIsPPgetSndShadow in Hpps.
    symmetry.
    apply getSh2NextEntryIsPPEq with phyDescChild s;trivial. }
  subst.
  rewrite <- HnbLS in *.
  inversion Hlevel.
  subst.
  revert HPE HVA HphySh1content HnbLS Hind Hnot3.
  clear.
  revert nbL table.
  induction stop; simpl in *.
  + right.
    inversion Hind;subst. 
    split.
    * assert( Hor : 0 < nbL \/ 0 = nbL) by omega.
      destruct Hor as [Hor | Hor].
      { left;split;trivial.
        apply HPE;trivial.
        unfold isWellFormedSndShadow in *.
        destruct HphySh1content as [(Hl & HphySh1content) | (Hl & HphySh1content)]. 
        destruct HphySh1content with idx as ( Hpe1 & Hpe2).
        apply readPhyEntryOrReadPresentIsPE;left;trivial.
        subst.
        apply fstLevelGt0False in Hor.
        now contradict Hor.  }
      { right.
        split;trivial.
        omega. right;left;split;trivial.
        apply HVA;trivial. 
        unfold isWellFormedSndShadow in *.
        destruct HphySh1content as [(Hl & HphySh1content) | (Hl & HphySh1content)].
        contradict Hor.
        apply fstLevelEq0;trivial.
        apply readVirtualIsVA;trivial. }
    * apply beq_nat_false in Hnot3.
      unfold not;intros Hfalse;subst.
      now contradict Hnot3.
  + intros.
    case_eq(StateLib.Level.eqb nbL fstLevel); intros Hlevel;
    rewrite Hlevel in *.
    inversion Hind;subst.
    right.  
    split.
    * assert( Hor :S stop < nbL \/ S stop >= nbL) by omega.
      destruct Hor as [Hor | Hor].
      { left. split;trivial. apply HPE;trivial.
        unfold isWellFormedSndShadow in *.
        destruct HphySh1content as [(Hl & HphySh1content) | (Hl & HphySh1content)].
        destruct HphySh1content with idx as ( Hpe1 & Hpe2).
        apply readPhyEntryOrReadPresentIsPE;left;trivial.
        subst.
        apply fstLevelSFalse in Hor.
        now contradict Hor. }
      { right.
        split;trivial.
        right;left;split;trivial.
        apply HVA;trivial.
         unfold isWellFormedSndShadow in *.
        destruct HphySh1content as [(Hl & HphySh1content) | (Hl & HphySh1content)].
        apply levelEqBEqNatTrue in Hlevel.
        subst.
        now contradict Hl.
        apply readVirtualIsVA;trivial. }
    * apply beq_nat_false in Hnot3.
      unfold not;intros Hfalse;subst.
      now contradict Hnot3.
    * unfold isWellFormedSndShadow in *.
      destruct HphySh1content as [(Hl & HphySh1content) | (Hl & HphySh1content)].
     ++ destruct HphySh1content with (StateLib.getIndexOfAddr va nbL)  as ( Hpe1 & Hpe2).
        rewrite Hpe1 in *.
        assert (Htrue : (defaultPage =? defaultPage) = true).      
        rewrite beq_nat_refl with defaultPage. reflexivity.
        rewrite Htrue in *.
        inversion Hind. 
        left;trivial.
     ++ 
        unfold StateLib.readVirtual in *.
        unfold StateLib.readPhyEntry in *.
        case_eq(lookup phySh2Child (StateLib.getIndexOfAddr va nbL) (memory s) beqPage beqIndex);
        [intros v Hlookup| intros Hlookup];rewrite Hlookup in *; try now contradict HphySh1content.
        case_eq(v);intros p H; rewrite H in *; try now contradict HphySh1content.
        generalize (HphySh1content (StateLib.getIndexOfAddr va nbL) );
        clear HphySh1content; intros HphySh1content.
        rewrite Hlookup in *; try now contradict HphySh1content.
- assert(Hcurparteq : (currentPartition s) = partition  \/
                (currentPartition s) <> partition ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  subst.
  + assert(HdsS : table = defaultPage \/
              (stop < nbL /\ isPE table idx s \/
               stop >= nbL /\
               (isVE table idx s /\ sh2idx = sh1idx \/
                isVA table idx s /\ sh2idx = sh2idx \/ isPE table idx s /\ sh2idx = PDidx)) /\
              table <> defaultPage).
    { assert(Hdss : dataStructurePdSh1Sh2asRoot sh2idx s ) by intuition.
      unfold  dataStructurePdSh1Sh2asRoot in Hdss.
      apply Hdss with (currentPartition s) structRoot va;trivial. }
      destruct HdsS as [HdsS | HdsS];[left;trivial|right].
      destruct HdsS as (HdsS & Hnotnull).
      split;trivial. 
      destruct HdsS as [(Hstop &HdsS) |(Hstop& HdsS)];[left|right].
      * split;trivial. apply HPE;trivial.
      * split;trivial.
        destruct HdsS as [(HdsS & Hidxrot) |[(HdsS & Hidxrot)|(HdsS& Hidxrot)]].
        left;split;trivial. apply HVE;trivial.
        right;left;split;trivial. apply HVA;trivial.
        right;right;split;trivial. apply HPE;trivial.
  + assert(HdsS : table = defaultPage \/
            (stop < nbL /\ isPE table idx s \/
             stop >= nbL /\
             (isVE table idx s /\ sh2idx = sh1idx \/
              isVA table idx s /\ sh2idx = sh2idx \/ isPE table idx s /\ sh2idx = PDidx)) /\
            table <> defaultPage).
    { assert(Hdss : dataStructurePdSh1Sh2asRoot sh2idx s ) by intuition.
      unfold  dataStructurePdSh1Sh2asRoot in Hdss.
      apply Hdss with partition structRoot va;trivial.
      apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial. unfold not;intros Hfalse.
      subst. now contradict Hcurparteq. }
      destruct HdsS as [HdsS | HdsS];[left;trivial|right].
      destruct HdsS as (HdsS & Hnotnull).
      split;trivial. 
      destruct HdsS as [(Hstop &HdsS) |(Hstop& HdsS)];[left|right].
      * split;trivial. apply HPE;trivial.
      * split;trivial.
        destruct HdsS as [(HdsS & Hidxrot) |[(HdsS & Hidxrot)|(HdsS& Hidxrot)]].
        left;split;trivial. apply HVE;trivial.
        right;left;split;trivial. apply HVA;trivial.
        right;right;split;trivial. apply HPE;trivial.
Qed.

Lemma currentPartitionInPartitionsListAddPartition table idx entry s:
 lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->
currentPartitionInPartitionsList s ->
currentPartitionInPartitionsList
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := true; va := va entry |})
              (memory s) beqPage beqIndex |} .
Proof.
intros.
unfold currentPartitionInPartitionsList in *.
simpl.
apply addPartitionKeepsAllPartitionsInTree;trivial.
Qed.

Lemma noDupMappedPagesListAddPartition  entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *)
 initConfigPagesListPostCondition phyConfigPagesList s ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 -> 
noDupMappedPagesList s'.
Proof.
intros.
subst.  
assert(Hnodumap : noDupMappedPagesList s).
{ unfold consistency in *. intuition. }
unfold noDupMappedPagesList in *.
intros.
assert(HmapS : getMappedPages partition s' = getMappedPages partition s) by 
(apply getMappedPagesAddDerivation with entry;trivial).
rewrite HmapS; clear HmapS. 
assert(Hparteq : partition = phyDescChild  \/ partition <> phyDescChild ) by apply pageDecOrNot.
destruct Hparteq as [Hparteq |Hparteq ].
- subst. 
 assert(Hmappednull : getMappedPages phyDescChild s = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial. }
  rewrite Hmappednull. constructor.
- assert(Hcurparteq : (currentPartition s) = partition  \/
                (currentPartition s) <> partition ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ]; apply   Hnodumap.
  + subst. unfold consistency in *.
    unfold currentPartitionInPartitionsList in *.
    intuition.
  + unfold consistency in *. 
    apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial.
    intuition. 
    intuition. intuition.
       intuition.
Qed.


Lemma noDupConfigPagesListAddPartition   entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv
shadow2 shadow1 pdChild list:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
false = checkVAddrsEqualityWOOffset nbLevel descChild pdChild level ->
false = checkVAddrsEqualityWOOffset nbLevel descChild shadow1 level ->
false = checkVAddrsEqualityWOOffset nbLevel descChild shadow2 level ->
false = checkVAddrsEqualityWOOffset nbLevel descChild list level ->
false = checkVAddrsEqualityWOOffset nbLevel pdChild shadow1 level ->
false = checkVAddrsEqualityWOOffset nbLevel pdChild shadow2 level ->
false = checkVAddrsEqualityWOOffset nbLevel pdChild list level ->
false = checkVAddrsEqualityWOOffset nbLevel shadow1 shadow2 level ->
false = checkVAddrsEqualityWOOffset nbLevel shadow1 list level ->
false = checkVAddrsEqualityWOOffset nbLevel shadow2 list level ->
getMappedPage currentPD s pdChild = SomePage phyPDChild -> 
getMappedPage currentPD s shadow1 = SomePage phySh1Child -> 
getMappedPage currentPD s shadow2 = SomePage phySh2Child -> 
getMappedPage currentPD s list = SomePage phyConfigPagesList -> 
getMappedPage currentPD s descChild = SomePage phyDescChild -> 
In descChild getAllVAddrWithOffset0 -> 
noDupConfigPagesList s' .
Proof.
intros.
subst.  
assert(Hnodumap : noDupConfigPagesList s).
{ unfold consistency in *. intuition. }
unfold noDupConfigPagesList in *.
intros  partition Hpart .
assert(Hind : getConfigPages partition s' = getConfigPages partition s) by 
(apply getConfigPagesAddDerivation with entry;trivial).
rewrite Hind; clear Hind. 
assert(Hparteq : partition = phyDescChild  \/ partition <> phyDescChild ) by apply pageDecOrNot.
destruct Hparteq as [Hparteq |Hparteq ].
- subst.
  unfold getConfigPages.
  unfold getConfigPagesAux.
  assert (Hroot: nextEntryIsPP phyDescChild PDidx phyPDChild s) by trivial.
  rewrite nextEntryIsPPgetPd in *.
  rewrite Hroot. clear Hroot.
  assert (Hroot: nextEntryIsPP phyDescChild sh1idx phySh1Child s) by trivial.
  rewrite nextEntryIsPPgetFstShadow in *.
  rewrite Hroot. clear Hroot.
  assert (Hroot: nextEntryIsPP phyDescChild sh2idx phySh2Child s) by trivial.
  rewrite nextEntryIsPPgetSndShadow in *.
  rewrite Hroot. clear Hroot.
  assert (Hroot: nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s) by trivial.
  apply nextEntryIsPPgetConfigList  in Hroot.
  rewrite Hroot. clear Hroot.
  rewrite getIndirectionsOnlyPD;trivial.
  rewrite getIndirectionsOnlySh1 with phySh1Child level s;trivial.
  rewrite getIndirectionsOnlySh2 with phySh2Child level s;trivial.
  assert(Hmykey :  StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
        (memory s) = Some defaultPage) by (unfold initConfigPagesListPostCondition in *; intuition).
  assert(Hsh3null : getLLPages phyConfigPagesList s (nbPage + 1) = [phyConfigPagesList]).
  { apply getLLPagesOnlyRoot;trivial. }
  rewrite Hsh3null.
(*   assert(In descChild getAllVAddr /\ In pdChild getAllVAddr /\ In shadow1 getAllVAddr /\
  In shadow2 getAllVAddr /\ In list getAllVAddr) as (Hk1 & Hk2 & Hk3 & Hk4 & Hk5). 
  { try repeat split;try apply AllVAddrAll. } *)
  assert(Hcurpd : StateLib.getPd (currentPartition s) (memory s) = Some currentPD) by trivial.
  assert(Hnodupmap : NoDup (filterOption (map (getMappedPage currentPD s) getAllVAddrWithOffset0 ))). 
  { unfold consistency in *.  
    assert(Hnodup: noDupMappedPagesList s) by intuition.
    unfold noDupMappedPagesList in *. 
    unfold getMappedPages in *.
    assert(Hcurpart : In (currentPartition s) (getPartitions multiplexer s)) by trivial.
    apply Hnodup in Hcurpart.
    rewrite Hcurpd in *.  unfold getMappedPagesAux in *. trivial. } 
  assert(phyDescChild <> phyPDChild).
  { apply twoMappedPagesAreDifferent with descChild pdChild currentPD level s;trivial.
    symmetry;trivial.
    symmetry;trivial. }
  assert(phyDescChild <> phySh1Child).
  { apply twoMappedPagesAreDifferent with descChild shadow1 currentPD level  s;trivial;
  symmetry;trivial. }
  assert(phyDescChild <> phySh2Child).
  { apply twoMappedPagesAreDifferent with descChild shadow2 currentPD level  s;trivial;
  symmetry;trivial.  }
  assert(phyDescChild <> phyConfigPagesList).
  { apply twoMappedPagesAreDifferent with descChild list currentPD level  s;trivial;
  symmetry;trivial.  }
  constructor.
  simpl. intuition.
  assert(phyPDChild <> phySh1Child).
  { apply twoMappedPagesAreDifferent with pdChild shadow1 currentPD level  s;trivial;
  symmetry;trivial.  }
  assert(phyPDChild <> phySh2Child).
  { apply twoMappedPagesAreDifferent with pdChild shadow2 currentPD level  s;trivial;
  symmetry;trivial. }
  assert(phyPDChild <> phyConfigPagesList).
  { apply twoMappedPagesAreDifferent with pdChild list currentPD level  s;trivial;
  symmetry;trivial.  }
  constructor.
  simpl. intuition.
  assert(phySh1Child <> phySh2Child).
  { apply twoMappedPagesAreDifferent with shadow1 shadow2 currentPD level  s;trivial;
  symmetry;trivial.  }
  assert(phySh1Child <> phyConfigPagesList).
  { apply twoMappedPagesAreDifferent with shadow1 list currentPD level  s;trivial;
  symmetry;trivial.  }
  constructor.
  simpl. intuition.
  assert(phySh2Child <> phyConfigPagesList).
  { apply twoMappedPagesAreDifferent with shadow2 list currentPD level  s;trivial;
  symmetry;trivial.  }
  constructor.
  simpl. intuition.
  constructor;auto.
  constructor.  
 - assert(Hcurparteq : (currentPartition s) = partition  \/
                (currentPartition s) <> partition ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  + subst.
    apply Hnodumap ; trivial.
  + 
    apply Hnodumap ; trivial.
    unfold consistency in *;intuition.
    apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial.
      unfold consistency in *;intuition.
intuition. 
Qed.

Lemma parentInPartitionListAddPartition  entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
In descChild getAllVAddrWithOffset0 -> 
isParent s -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx ->

parentInPartitionList s'.
Proof. 
simpl;intros Hnewhypo HisParent.
intros.
unfold parentInPartitionList in *.
set(s' :=  {| currentPartition := _ |}) in *.
intros partition HpartS parent Hpps.
assert(Hparentpart : parentInPartitionList s).
{ unfold consistency in *; intuition. } 
assert(Hparteq : partition = phyDescChild  \/ partition <> phyDescChild ) by apply pageDecOrNot.
destruct Hparteq as [Hparteq |Hparteq ].
- subst.  
  assert(parent = (currentPartition s)).
   { rewrite nextEntryIsPPgetParent in Hpps.
      symmetry.
      apply getParentNextEntryIsPPEq with phyDescChild s;trivial.
      rewrite <- Hpps.
      symmetry.
      apply getParentAddDerivation with entry; trivial.  }
  subst.
  apply addPartitionKeepsAllPartitionsInTree; trivial.
- assert(Hcurparteq : (currentPartition s) = partition  \/
                (currentPartition s) <> partition ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ]; subst.
  + apply addPartitionKeepsAllPartitionsInTree.
    trivial.
    unfold parentInPartitionList in *. 
    apply Hparentpart with (currentPartition s); trivial.
    rewrite nextEntryIsPPAddDerivation with entry;trivial.
    unfold s' in *.
    eassumption.
    trivial.
  + unfold consistency in *. 
    apply addPartitionKeepsAllPartitionsInTree.
    trivial.
    unfold parentInPartitionList in *. 
    apply Hparentpart with partition; trivial.
        apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial.
      intuition. intuition. intuition. intuition.
    rewrite nextEntryIsPPAddDerivation with entry;trivial.
    unfold s' in *.
    eassumption.
    trivial.
Qed.
 

Lemma accessibleVAIsNotPartitionDescriptorAddPartition entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s -> 
In phyDescChild (getChildren (currentPartition s) s')-> 
~ In phyDescChild (getChildren  (currentPartition s) s) -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
entryUserFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) false s -> 
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 ->
accessibleVAIsNotPartitionDescriptor s' .
Proof.
intros s' HisParent Hinchildren Hnotinchildren.
intros; subst.
assert(Hcons : accessibleVAIsNotPartitionDescriptor s ).
{ unfold consistency in *. 
  intuition. }
unfold accessibleVAIsNotPartitionDescriptor in *.
intros    partition va pd sh1 pg HpartS HpdS Hsh1S HaccesS.
assert(HnbL : Some level = StateLib.getNbLevel) by trivial.
assert(Hparteq : partition = phyDescChild  \/ partition <> phyDescChild ) by apply pageDecOrNot.
destruct Hparteq as [Hparteq |Hparteq ].
- subst. 
  assert (Haccess : getAccessibleMappedPage pd s' va =
  getAccessibleMappedPage pd s va).
  apply getAccessibleMappedPageAddDerivation with entry; trivial.
  rewrite Haccess in *; clear Haccess.
  assert(Hfalse : getMappedPage pd s va = SomePage pg ).
  apply accessiblePAgeIsMapped; trivial.
   assert(Hmappednull : getMappedPages phyDescChild s = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial. }
  assert(In pg (getMappedPages phyDescChild s)).
  {
  unfold getMappedPages.  
  assert(Heqp:   StateLib.getPd phyDescChild (memory s') =
   StateLib.getPd phyDescChild (memory s)).
   apply getPdAddDerivation with entry;trivial.
   rewrite Heqp in *.
   rewrite HpdS . 
  unfold getMappedPagesAux in *.
  unfold getMappedPagesOption in *.
  rewrite filterOptionInIff.
  rewrite in_map_iff.
  assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel va va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1.
 
 simpl;split;trivial.
 rewrite <- Hfalse.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption. }
   rewrite  Hmappednull in *.
   intuition.   
- assert(Hcurparteq : (currentPartition s) = partition  \/
                (currentPartition s) <> partition ) by apply pageDecOrNot.
    destruct Hcurparteq as [Hcurparteq |Hcurparteq ]; subst.
  + assert(Hor : pg = phyDescChild \/ pg <> phyDescChild) by apply pageDecOrNot.
    assert(currentPD = pd).
  { apply getPdNextEntryIsPPEq with (currentPartition s) s; trivial.
    rewrite <- HpdS.
    symmetry.
    apply getPdAddDerivation with entry; trivial. }
    destruct Hor as [Hor | Hor].
    * subst.
          assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel va va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).

      assert(descChild = va1).
      { assert(HmappedS : getMappedPage pd s' va = SomePage phyDescChild).
        { apply accessiblePAgeIsMapped. trivial. }
        apply eqMappedPagesEqVaddrs with phyDescChild pd s;trivial.        
        apply getMappedPageGetTableRoot with ptRefChild (currentPartition s) ; trivial.
        assert(Haux : getMappedPage pd s va = SomePage phyDescChild). 
       
        rewrite <- HmappedS.
        symmetry.  
        apply getMappedPageAddDerivation with entry; trivial.
        rewrite <- Haux.
        symmetry.
       apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
        apply getNbLevelEqOption.
        unfold consistency in *.
        assert(Hnodupmap : noDupMappedPagesList s) by intuition.
        unfold noDupMappedPagesList in *.
        assert(Hcurpart : In (currentPartition s) (getPartitions multiplexer s) ) by trivial.
        apply Hnodupmap in Hcurpart. clear Hnodupmap.
        move Hcurpart at bottom.
        unfold getMappedPages in Hcurpart.
        assert(HcurpdS : StateLib.getPd (currentPartition s) (memory s') =
        StateLib.getPd (currentPartition s) (memory s) ).
        apply getPdAddDerivation with entry; trivial. 
        rewrite HcurpdS in *.
        rewrite HpdS in *.
        unfold getMappedPagesAux  in *.
        unfold getMappedPagesOption in Hcurpart;trivial. }
      subst va1.
      assert(Hnotaccess : getAccessibleMappedPage pd s descChild = NonePage).
      { apply getMappedPageNotAccessible with
      ptRefChild (currentPartition s) phyDescChild ; trivial. }
      assert(HaccessS : getAccessibleMappedPage pd s' descChild  = 
      getAccessibleMappedPage pd s descChild ).
      apply getAccessibleMappedPageAddDerivation with entry; trivial.
      move Hnotaccess at bottom.
      assert(Hnewhypo : getAccessibleMappedPage pd s' va = getAccessibleMappedPage pd s' descChild). 
      { apply getAccessibleMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
        apply getNbLevelEqOption. }
      rewrite Hnewhypo in *.
      rewrite HaccessS in *.
      rewrite Hnotaccess in HaccesS.
      now contradict HaccesS.
    * subst pd.
      unfold consistency in *.
      assert(Hchildren : exists l1 l2,
                getChildren (currentPartition s)  s' = l1 ++ [phyDescChild] ++ l2 /\
                getChildren (currentPartition s)  s = l1 ++l2).
      apply getChildrenSplitList with ptRefChild currentShadow1 currentPD; intuition.
      assert(Htrue : getPDFlag sh1 va s = false).
      apply Hcons with (currentPartition s) currentPD pg; trivial.
      rewrite <- HpdS.
      symmetry.
      apply getPdAddDerivation with entry; trivial.
      rewrite <- Hsh1S.
      symmetry.
      apply getFstShadowAddDerivation with entry; trivial.
      rewrite <- HaccesS.
      symmetry.
      apply getAccessibleMappedPageAddDerivation  with entry; trivial.
      move Hinchildren at bottom.
      move Hnotinchildren at bottom.
      destruct Hchildren as (l1 & l2 & Hi1 & Hi2).
       assert(Hsh1 : getFstShadow (currentPartition s) (memory s') = getFstShadow 
       (currentPartition s) (memory s)).
     apply getFstShadowAddDerivation with entry; trivial.
      assert (Hpdes : StateLib.getPd (currentPartition s) (memory s) = 
  StateLib.getPd (currentPartition s) (memory s')).
  symmetry.
  apply getPdAddDerivation with entry;trivial.
   assert(HmappedS : getMappedPage currentPD s' va = SomePage pg).
        { apply accessiblePAgeIsMapped. trivial. } 
      assert(Hnotpat : forall phyVa, phyVa <> phyDescChild -> 
      ~ In phyVa (getChildren (currentPartition s) s)
      -> ~ In phyVa (getChildren (currentPartition s) s')).
      { intros phyVa Hnoteq Hnotin.
       rewrite Hi2 in *.
      rewrite Hi1.
      rewrite in_app_iff.
      unfold not; intros Hfalse.
      contradict Hnotin.
      destruct Hfalse as [Hfalse | Hfalse].
      rewrite in_app_iff.
      left;trivial.
      simpl in *.
      destruct Hfalse as [Hfalse | Hfalse].
      subst. now contradict Hnoteq.
      rewrite in_app_iff.
      right;trivial.
       }
   assert(checkChild (currentPartition s) level s va = false).
   { unfold  checkChild.
     rewrite Hsh1 in *.
      rewrite Hsh1S. 
      unfold getPDFlag in *.
      rewrite <- HnbL in *.
      trivial. } 
      assert( ~ In pg (getChildren (currentPartition s) s)).
      { unfold getChildren.
        rewrite <- HnbL.
        rewrite <- Hpdes in HpdS.
        rewrite HpdS.
        unfold getMappedPagesAux.
        rewrite filterOptionInIff.
        unfold getMappedPagesOption.
        rewrite in_map_iff .
        unfold not; intros Hfalse.
        destruct Hfalse as (vi & Hii & H2ii).
        unfold getPdsVAddr in *.
        apply filter_In in H2ii.
        destruct H2ii as (H2ii & H2iii).
         assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel va va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).
        assert(va1 = vi).
      { 
        apply eqMappedPagesEqVaddrs with pg currentPD s;trivial.
        assert(Hnewgoal : getMappedPage currentPD s va = SomePage pg). 
        { rewrite  <- HmappedS.
        
         (*         
        apply getMappedPageGetTableRoot with ptRefChild (currentPartition s) ; trivial.
        apply AllVAddrAll.
        subst.        
        rewrite <- HmappedS. *)
        symmetry.   
        apply getMappedPageAddDerivation with entry; trivial. }
        rewrite <- Hnewgoal.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.
        unfold consistency in *.
        assert(Hnodupmap : noDupMappedPagesList s) by intuition.
        unfold noDupMappedPagesList in *.
        assert(Hcurpart : In (currentPartition s) (getPartitions multiplexer s) ) by trivial.
        apply Hnodupmap in Hcurpart. clear Hnodupmap.
        move Hcurpart at bottom.
        unfold getMappedPages in Hcurpart.
        rewrite HpdS in *.
        unfold getMappedPagesAux  in *.
        unfold getMappedPagesOption in Hcurpart;trivial. }
   subst vi.
   unfold getPdsVAddr in *.
assert(Hcheckeq : checkChild (currentPartition s) level s va1 = 
checkChild (currentPartition s) level s va).
{ symmetry.
  apply checkChildEq;trivial.
  symmetry;trivial.
  rewrite <- Hva11.
  f_equal.
  assert(Hlvl : StateLib.getNbLevel = Some (CLevel (nbLevel - 1))) by apply getNbLevelEqOption.
  rewrite  Hlvl in *.
  inversion HnbL;trivial. }
  rewrite Hcheckeq in *.
  
   rewrite H2iii in *.
   intuition.
   
   }
   
  assert(Hpost : ~ In pg (getChildren (currentPartition s) s')).
  apply Hnotpat; trivial.
  assert(Hfalse : checkChild (currentPartition s) level s' va = false).
  { unfold getChildren  in Hpost.
    rewrite <- HnbL in *.
    rewrite <- Hpdes in *.
    rewrite HpdS in *.
    unfold getMappedPagesAux  in *.
        unfold getMappedPagesOption in *.
        rewrite filterOptionInIff in *.
        rewrite in_map_iff in *.
     apply Classical_Prop.NNPP.
     unfold not at 1;intros Hfalse.
     contradict Hpost.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel va va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1.
     split. trivial. 
     rewrite <- HmappedS.
     symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.
  unfold getPdsVAddr .
  apply filter_In.
  split;trivial.
  assert(Hcheckeq : checkChild (currentPartition s) level s' va1 = 
checkChild (currentPartition s) level s' va).
{ symmetry.
  apply checkChildEq;trivial.
  symmetry;trivial.
  rewrite <- Hva11.
  f_equal.
  assert(Hlvl : StateLib.getNbLevel = Some (CLevel (nbLevel - 1))) by apply getNbLevelEqOption.
  rewrite  Hlvl in *.
  inversion HnbL;trivial. }
  rewrite Hcheckeq in *.

  apply not_false_is_true ; trivial. }
     
     unfold  checkChild in Hfalse.
     rewrite Hsh1 in *.
       rewrite Hsh1S in *. 
        unfold getPDFlag.
        rewrite <- HnbL in *.
        trivial. 
   
  +
  assert(Hpartintree : In partition (getPartitions multiplexer s)).
  unfold consistency in *.
     apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial.
      intuition. intuition. intuition. intuition.
   assert(Heqp:   StateLib.getPd partition (memory s') =
   StateLib.getPd partition (memory s)).
   apply getPdAddDerivation with entry;trivial.
   rewrite Heqp in *. clear Heqp.      
   assert(Hsh1:   StateLib.getFstShadow partition (memory s') =
   StateLib.getFstShadow partition (memory s)).
   apply getFstShadowAddDerivation with entry;trivial.
   rewrite Hsh1 in *.
   assert(Heqp:   getAccessibleMappedPage pd s' va  =
   getAccessibleMappedPage pd s va).
   apply getAccessibleMappedPageAddDerivation with entry;trivial.
   rewrite Heqp in *. clear Heqp.
   assert(getPDFlag sh1 va s = false).
   apply Hcons with partition pd pg;trivial.
   assert(checkChild  partition level s va = false).
   { unfold  checkChild.
      rewrite Hsh1S. 
      unfold getPDFlag in *.
      rewrite <- HnbL in *.
      trivial. }
   assert(Hfalse :  checkChild  partition level s' va = false).
   { unfold consistency in *. 
    apply addPartitionAddSingleChild with (currentPartition s) descChild;trivial.
    intuition.
    intuition.
    intuition.
    intuition.
    + move Hinchildren at bottom. 
      fold s'.
      unfold getChildren in Hinchildren.
      rewrite <- HnbL in *. 
      assert(Heqp:   StateLib.getPd (currentPartition s) (memory s') =
      StateLib.getPd (currentPartition s) (memory s)).
      apply getPdAddDerivation with entry;trivial.
      rewrite Heqp in *. clear Heqp.
      assert(HcurrentPD : StateLib.getPd (currentPartition s) (memory s) = Some currentPD). 
      apply nextEntryIsPPgetPd; trivial.
      rewrite HcurrentPD in *. 
      unfold getMappedPagesAux in *.
      rewrite filterOptionInIff in *.
      unfold getMappedPagesOption in *.
      rewrite in_map_iff in *.
      destruct Hinchildren as (vaChild & HmapVaChild & Hcheckchild).
      unfold getPdsVAddr in *.
      rewrite filter_In in *.
      destruct Hcheckchild as (Hcheckchild & HHcheckchild).
      assert(descChild = vaChild).
      { apply eqMappedPagesEqVaddrs with phyDescChild currentPD s;trivial.
        apply getMappedPageGetTableRoot with ptRefChild (currentPartition s) ; trivial.
        rewrite <- HmapVaChild.
        symmetry.
        apply getMappedPageAddDerivation with entry; trivial.
        unfold consistency in *.
        assert(Hnodupmap : noDupMappedPagesList s) by intuition.
        unfold noDupMappedPagesList in *.
        assert(Hcurpart : In (currentPartition s) (getPartitions multiplexer s) ) by trivial.
        apply Hnodupmap in Hcurpart. clear Hnodupmap.
        move Hcurpart at bottom.
        unfold getMappedPages in Hcurpart.
        rewrite HcurrentPD in *.
        unfold getMappedPagesAux  in *.
        unfold getMappedPagesOption in Hcurpart;trivial. }
      subst. intuition .
    + move Hnotinchildren at bottom.
      unfold getChildren in Hnotinchildren.
      rewrite <- HnbL in *.
      assert(HcurrentPD : StateLib.getPd (currentPartition s) (memory s) = Some currentPD). 
      apply nextEntryIsPPgetPd; trivial.
      rewrite HcurrentPD in *. 
      unfold getMappedPagesAux in *.
      rewrite filterOptionInIff in *.
      unfold getMappedPagesOption in *.
      rewrite in_map_iff in *.
      apply Classical_Prop.NNPP.
      unfold not at 1.
      intros Hfalse.
      contradict Hnotinchildren.
      exists descChild; split;trivial.
      apply getMappedPageGetTableRoot with ptRefChild (currentPartition s) ; trivial.
      unfold getPdsVAddr.
      apply filter_In.
      split;trivial.
      apply not_false_iff_true in Hfalse.
      trivial. }
     { unfold  checkChild in Hfalse.
       rewrite Hsh1 in *. 
        rewrite Hsh1S in *. 
        unfold getPDFlag.
        rewrite <- HnbL in *.
        trivial. } 
Qed.


Lemma accessibleChildPageIsAccessibleIntoParentAddPartition 
 entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s -> 
In descChild getAllVAddrWithOffset0 -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
accessibleChildPageIsAccessibleIntoParent s'.
Proof.
intros.
subst.  
assert(Hnodumap : accessibleChildPageIsAccessibleIntoParent s).
{ unfold consistency in *. intuition. }
unfold accessibleChildPageIsAccessibleIntoParent in *.
intros partition va pd accessiblePage HpartS HpdS HaccessS.
assert(HfstS : forall partition , getSndShadow partition (memory s') =
                                  getSndShadow partition (memory s)).
{ intros . apply getSndShadowAddDerivation with entry; trivial. }
assert(Hpdeq : forall partition , StateLib.getPd  partition (memory s') =
                                  StateLib.getPd  partition (memory s)).
{ intros . apply getPdAddDerivation with entry; trivial. }
assert(HaccesEq : forall pd va , getAccessibleMappedPage pd s' va =
getAccessibleMappedPage pd s va).
{ intros.  apply getAccessibleMappedPageAddDerivation with entry; trivial. }
assert(HisAccessinparent :  forall partition va accessiblePage,
isAccessibleMappedPageInParent partition va accessiblePage s =
isAccessibleMappedPageInParent partition va accessiblePage s').
{ intros.
  apply isAccessibleMappedPageInParentAddDerivattion with entry;trivial. }
  rewrite <- HisAccessinparent.  
assert(Hparteq : partition = phyDescChild  \/ partition <> phyDescChild ) by apply pageDecOrNot.
destruct Hparteq as [Hparteq |Hparteq ].
- subst.
  assert(Hacces : getAccessibleMappedPage pd s va = SomePage accessiblePage).
  { rewrite <- HaccessS.
    symmetry.
    apply getAccessibleMappedPageAddDerivation with entry;trivial. }
  assert(getMappedPage pd s va = SomePage accessiblePage).
  apply accessiblePAgeIsMapped;trivial.
  assert(In accessiblePage (getMappedPages phyDescChild s)).
  { unfold getMappedPages.
    rewrite Hpdeq in *.
    rewrite HpdS.
    unfold getMappedPagesAux.
    rewrite filterOptionInIff.
    
    unfold getMappedPagesOption .
    rewrite in_map_iff.
    assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel va va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1. split;trivial.
assert(Hnewgoal : getMappedPage pd s va = SomePage accessiblePage) by trivial.
rewrite <- Hnewgoal.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption. }
  assert(Hmappednull : getMappedPages phyDescChild s = nil).
  { unfold getMappedPages.
    unfold s'.
    simpl.
    assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
    apply nextEntryIsPPgetPd;trivial.
    rewrite Hpdnewchild.
    unfold getMappedPagesAux.
    apply  getMappedPagesOptionNil ;trivial. }
  rewrite Hmappednull in *.
  intuition.  
- assert(Hcurparteq : (currentPartition s) = partition  \/
                (currentPartition s) <> partition ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  + subst.
    apply Hnodumap with pd; trivial.
    rewrite <- HpdS.
    symmetry.
    apply getPdAddDerivation with entry;trivial. 
    rewrite <- HaccessS.
    symmetry.
    apply getAccessibleMappedPageAddDerivation with entry;trivial.
  + subst.
    apply Hnodumap with pd; trivial.
    unfold consistency in *.
    apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial.
      intuition. intuition. intuition. intuition.  
    rewrite <- HpdS.
    symmetry.
    apply getPdAddDerivation with entry;trivial. 
    rewrite <- HaccessS.
    symmetry.
    apply getAccessibleMappedPageAddDerivation with entry;trivial.
Qed.



Lemma noCycleInPartitionTreeAddPartition  entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
initConfigPagesListPostCondition phyConfigPagesList s ->  
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) -> 
 *)In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 -> 
noCycleInPartitionTree s'.
Proof.
intros ; subst.
assert(Hnocycle : noCycleInPartitionTree s). 
{ unfold consistency in *. 
  intuition. }
unfold noCycleInPartitionTree in *.
assert(Hanceq : forall part , getAncestors part s = 
getAncestors part s').
{ assert(Hlookup : lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) 
          (memory s) beqPage beqIndex =
          Some (VE entry)) by trivial.
  revert Hlookup.
  clear.
  unfold getAncestors.
  induction  (nbPage + 1).
  simpl; trivial.
  simpl;intros.
  assert(Hparenteq : forall partition , StateLib.getParent  partition (memory s') =
                              StateLib.getParent  partition (memory s)).
  { intros . apply getParentAddDerivation with entry; trivial. }
  rewrite Hparenteq.
  case_eq(getParent part (memory s)); intros; simpl; trivial.
  f_equal.
  apply IHn; trivial. } 
  intros ancestor partition Hpart Hances.
  assert(Hparteq : partition = phyDescChild  \/ partition <> phyDescChild ) by apply pageDecOrNot.
  destruct Hparteq as [Hparteq |Hparteq ].
+ subst. 
  assert(Hcurparteq : (currentPartition s) = ancestor  \/
                (currentPartition s) <> ancestor ) by apply pageDecOrNot.
  rewrite <- Hanceq in *.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  - subst.
    assert(Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      ~ (partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s)));
      trivial.
    unfold not; intros.
    unfold not in Hconfig.
    apply Hconfig with (currentPartition s);trivial.
    left;trivial.
  - assert (HpdNewPart : nextEntryIsPP phyDescChild PPRidx (currentPartition s) s) by trivial.
    rewrite nextEntryIsPPgetParent in HpdNewPart.
    assert(In (currentPartition s) (getAncestors phyDescChild s)).
    { unfold getAncestors.
      destruct nbPage; simpl;
      rewrite HpdNewPart;
      simpl;left;trivial. }
     assert(In ancestor (getAncestors (currentPartition s)  s)).
     unfold consistency in *.
     apply getAncestorsProp1 with phyDescChild; trivial.
     intuition. intuition.
     assert(In ancestor (getPartitions multiplexer s)).
     { unfold consistency in *. 
       apply ancestorInPartitionTree with (currentPartition s);trivial;
       intuition. }      
     unfold not; intros.
     assert(Hconfig : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      ~ (partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s)));
      trivial.
      unfold not in Hconfig.
      apply Hconfig with ancestor;trivial.
      left;trivial. 
+ assert(Hcurparteq : (currentPartition s) = partition  \/
                (currentPartition s) <> partition ) by apply pageDecOrNot.
  rewrite <- Hanceq in *.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  - subst. apply   Hnocycle;trivial.
  - apply Hnocycle; trivial.
    unfold consistency in *.
    apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial;intuition.
Qed.

Lemma configTablesAreDifferentAddPartition  entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->  
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 -> 
configTablesAreDifferent s'.
Proof.
intros . subst.
assert(Hconfig :  configTablesAreDifferent s).
{ unfold consistency in *.
  intuition. }
unfold configTablesAreDifferent. 
intros partition1 partition2 Hpart1 Hpart2 Hnoteq.
assert(Heqparts : partition1 = phyDescChild \/ partition2 = phyDescChild \/
(partition1 <> phyDescChild /\ partition2 <> phyDescChild) ).
{ destruct partition1; destruct partition2; destruct phyDescChild.
    assert (Hi : p = p1 \/ p0 = p1 \/
    (p <> p1 /\ p0 <> p1)) by omega.
    destruct Hi as [Hi | [Hi |(Hi1 & Hi2) ]].
    + left. subst. f_equal. apply proof_irrelevance.
    + right;left.
      subst. f_equal. apply proof_irrelevance.
    + right;right.
      split;
      unfold not; intros Hfalse;inversion Hfalse; subst; 
      try now contradict Hi1;try now contradict Hi2. }
assert(HconfigS :forall part, getConfigPages part s' = getConfigPages part s).
{ intros. apply getConfigPagesAddDerivation with entry;trivial. }
do 2 rewrite HconfigS in *.
destruct Heqparts as [Heqparts | [Heqparts | (Hnoteqpart1 & Hnoteqpart2)]].
- subst.
  unfold getConfigPages at 1.
  unfold getConfigPagesAux.
   assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
  apply nextEntryIsPPgetPd;trivial.
  rewrite Hpdnewchild.
  simpl.
  assert(Hsh1newchild :StateLib.getFstShadow phyDescChild (memory s) = Some phySh1Child).
  apply nextEntryIsPPgetFstShadow;trivial.
  rewrite Hsh1newchild.
  simpl.
  (** we have an hypothesis **)
  assert(Hsh2newchild :StateLib.getSndShadow phyDescChild (memory s) = Some phySh2Child).
  apply nextEntryIsPPgetSndShadow;trivial.
  rewrite Hsh2newchild.
  simpl.
  (** we have an hypothesis **)
  assert(Hlistnewchild :StateLib.getConfigTablesLinkedList phyDescChild (memory s) = Some phyConfigPagesList ).
  apply nextEntryIsPPgetConfigList;trivial.
  rewrite Hlistnewchild.
  (** new partition configuration : replace  *)
  rewrite getIndirectionsOnlyPD;trivial.
  rewrite getIndirectionsOnlySh1 with phySh1Child level s;trivial.
  rewrite getIndirectionsOnlySh2 with phySh2Child level s;trivial.
  rewrite getLLPagesOnlyRoot;trivial.
  assert (In partition2 (getPartitions multiplexer s)).
  {
  assert(Hcurparteq :  partition2 = (currentPartition s) \/ 
                       partition2 <> (currentPartition s)) by apply pageDecOrNot.
                        
  destruct Hcurparteq as [Hcurparteq | Hcurparteq].
  +  subst. 
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *. 
    intuition.
  + subst. unfold consistency in *. 
    apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial;intuition.
   } 
  unfold disjoint.
  intros x Hx.
  simpl in *.
  destruct Hx as [Hx | Hx].
  rewrite <- Hx.
  assert(Hconfig1 : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      ~ (partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s))) by trivial.
  apply Hconfig1;trivial.
  destruct Hx as [Hx | Hx].
  rewrite <- Hx.
  assert(Hconfig1 : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      ~ (partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s))) by trivial.
  apply Hconfig1;trivial.
  destruct Hx as [Hx | Hx].
  rewrite <- Hx.
  assert(Hconfig1 : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      ~ (partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s))) by trivial.
  apply Hconfig1;trivial.
  destruct Hx as [Hx | Hx].
  rewrite <- Hx.
  assert(Hconfig1 : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      ~ (partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s))) by trivial.
  apply Hconfig1;trivial.
  destruct Hx as [Hx | Hx].
  rewrite <- Hx.
  assert(Hconfig1 : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      ~ (partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s))) by trivial.
  apply Hconfig1;trivial.
  intuition.
- subst. 
  unfold getConfigPages at 2.
  unfold getConfigPagesAux.
   assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
  apply nextEntryIsPPgetPd;trivial.
  rewrite Hpdnewchild.
  simpl.
  assert(Hsh1newchild :StateLib.getFstShadow phyDescChild (memory s) = Some phySh1Child).
  apply nextEntryIsPPgetFstShadow;trivial.
  rewrite Hsh1newchild.
  simpl.
  (** we have an hypothesis **)
  assert(Hsh2newchild :StateLib.getSndShadow phyDescChild (memory s) = Some phySh2Child).
  apply nextEntryIsPPgetSndShadow;trivial.
  rewrite Hsh2newchild.
  simpl.
  (** we have an hypothesis **)
  assert(Hlistnewchild :StateLib.getConfigTablesLinkedList phyDescChild (memory s) = Some phyConfigPagesList ).
  apply nextEntryIsPPgetConfigList;trivial.
  rewrite Hlistnewchild.
  (** new partition configuration : replace  *)
  rewrite getIndirectionsOnlyPD;trivial.
  rewrite getIndirectionsOnlySh1 with phySh1Child level s;trivial.
  rewrite getIndirectionsOnlySh2 with phySh2Child level s;trivial.
  rewrite getLLPagesOnlyRoot;trivial.
  assert (In partition1 (getPartitions multiplexer s)).
  {
  assert(Hcurparteq :  partition1 = (currentPartition s) \/ 
                       partition1 <> (currentPartition s)) by apply pageDecOrNot.
                        
  destruct Hcurparteq as [Hcurparteq | Hcurparteq].
  +  subst. 
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *. 
    intuition.
  + subst. unfold consistency in *. 
    apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial;intuition.
   } 
  unfold disjoint.
  intros x Hxx.
  unfold not;intros Hx.
  contradict Hxx.
  simpl in *.
  destruct Hx as [Hx | Hx].
  rewrite <- Hx.
  assert(Hconfig1 : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      ~ (partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s))) by trivial.
  apply Hconfig1;trivial.
  destruct Hx as [Hx | Hx].
  rewrite <- Hx.
  assert(Hconfig1 : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      ~ (partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s))) by trivial.
  apply Hconfig1;trivial.
  destruct Hx as [Hx | Hx].
  rewrite <- Hx.
  assert(Hconfig1 : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      ~ (partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s))) by trivial.
  apply Hconfig1;trivial.
  destruct Hx as [Hx | Hx].
  rewrite <- Hx.
  assert(Hconfig1 : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      ~ (partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s))) by trivial.
  apply Hconfig1;trivial.
  destruct Hx as [Hx | Hx].
  rewrite <- Hx.
  assert(Hconfig1 : forall partition : page,
      In partition (getPartitions multiplexer s) ->
      ~ (partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s))) by trivial.
  apply Hconfig1;trivial.
  intuition.
 - assert (In partition1 (getPartitions multiplexer s)).
  {
  assert(Hcurparteq :  partition1 = (currentPartition s) \/ 
                       partition1 <> (currentPartition s)) by apply pageDecOrNot.
                        
  destruct Hcurparteq as [Hcurparteq | Hcurparteq].
  +  subst. 
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *. 
    intuition.
  + subst. unfold consistency in *. 
    apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial;intuition.
   }
   assert (In partition2 (getPartitions multiplexer s)).
  {
  assert(Hcurparteq :  partition2 = (currentPartition s) \/ 
                       partition2 <> (currentPartition s)) by apply pageDecOrNot.
                        
  destruct Hcurparteq as [Hcurparteq | Hcurparteq].
  +  subst. 
    unfold consistency in *.
    unfold currentPartitionInPartitionsList in *. 
    intuition.
  + subst. unfold consistency in *. 
    apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial;intuition.
   }
  unfold configTablesAreDifferent in Hconfig.
  apply Hconfig;trivial.  
Qed.

Lemma isChildAddPartition entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s-> 
~ In phyDescChild (getChildren  (currentPartition s) s) -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->  
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *)
 initConfigPagesListPostCondition phyConfigPagesList s ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 ->
isChild s'.
Proof.
intros s' HisParent HnotinChildren.
intros.
subst.
assert(Hischild : isChild s).
{ unfold consistency in *.
  intuition. }
unfold isChild in *.
intros partition parent Hpart Hparent.
assert(Hparteq : partition = phyDescChild  \/ partition <> phyDescChild ) by apply pageDecOrNot.
  destruct Hparteq as [Hparteq |Hparteq ].
+ subst. 
  assert(Hcurparteq : (currentPartition s) = parent  \/
                (currentPartition s) <> parent ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  - subst.
    trivial.
  - assert(Hparentnew : getParent phyDescChild (memory s) = Some (currentPartition s)).
    apply nextEntryIsPPgetParent;trivial.
    assert(HgetParent: getParent phyDescChild (memory s')  =
    getParent phyDescChild (memory s)).
    apply getParentAddDerivation with entry;trivial.
    rewrite HgetParent in *.  
    rewrite Hparentnew in *.
    inversion Hparent.
    intuition.
+ assert(Hcurparteq : (currentPartition s) = parent  \/
                (currentPartition s) <> parent ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  - subst.
    assert(HgetParent: getParent partition (memory s')  =
       getParent partition (memory s)).
    apply getParentAddDerivation with entry;trivial.
    rewrite HgetParent in *.
    assert( In partition (getChildren (currentPartition s) s)).
    {  apply Hischild; trivial.
       assert(Hcurparteq :  partition = (currentPartition s) \/ 
                       partition <> (currentPartition s)) by apply pageDecOrNot.
       destruct Hcurparteq as [Hcurparteq | Hcurparteq].
          *  subst. 
            unfold consistency in *.
            unfold currentPartitionInPartitionsList in *. 
            intuition.
          * subst. unfold consistency in *. 
            apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
              (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
              phyConfigPagesList ptRefChild currentShadow1;trivial;intuition. }
    
    assert(HnewChildrenlist : exists l1 l2 : list page,
    getChildren (currentPartition s) s' = l1 ++ [phyDescChild] ++ l2 /\ 
    getChildren (currentPartition s) s = l1 ++ l2).
    { unfold consistency in *.
      apply getChildrenSplitList with ptRefChild currentShadow1 currentPD;
      trivial; intuition. }
    destruct HnewChildrenlist as (l1 & l2 & Hi1 & Hi2).
    rewrite Hi1 in *.
    rewrite Hi2 in *.
    rewrite in_app_iff in *.
    intuition. 
 - assert(Hneweq : phyDescChild = parent  \/
                phyDescChild <> parent ) by apply pageDecOrNot.
  destruct Hneweq as [Hneweq |Hneweq ].
  * subst parent.
  assert(HgetParent: getParent partition (memory s')  =
       getParent partition (memory s)).
    apply getParentAddDerivation with entry;trivial.
    rewrite HgetParent in *.
    assert(Hfalse : In partition (getChildren phyDescChild s)).
    { apply Hischild; trivial.
      unfold consistency in *. 
      assert(Hcurparteqpart : (currentPartition s) = partition  \/
                (currentPartition s) <> partition ) by apply pageDecOrNot.
      destruct Hcurparteqpart as [Hcurparteqpart | Hcurparteqpart].
      *  subst. 
        unfold consistency in *.
        unfold currentPartitionInPartitionsList in *. 
        intuition.
      * subst. unfold consistency in *. 
        apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
          (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
          phyConfigPagesList ptRefChild currentShadow1;trivial;intuition. }
    assert (Hchildrennil : getChildren phyDescChild s = nil).
   { assert(Htrue : forall s partition, (* In partition (getPartitions multiplexer s)
              -> *)  incl (getChildren partition s) (getMappedPages partition s)).
      { intros.
        unfold incl.
        unfold getChildren.
        unfold getMappedPages.
        intros a Hins.
        destruct (StateLib.getNbLevel ); try now contradict H0.
        destruct  (StateLib.getPd partition0 (memory s0)); try now contradict H0.
        unfold getMappedPagesAux in *.
        rewrite filterOptionInIff in *.
        unfold getMappedPagesOption in *.
        rewrite in_map_iff in *.
        destruct Hins.
        
        exists x;split;intuition.
        assert(Hpds : In x (getPdsVAddr partition0 l getAllVAddrWithOffset0 s0)) by trivial.
        unfold getPdsVAddr in *. 
        apply filter_In in Hpds.
        destruct Hpds;trivial. }
     assert(Hmappednull : getMappedPages phyDescChild s = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial. }
     unfold incl in *.
     apply Htrue in Hfalse.
     rewrite Hmappednull in *.
     intuition. }
   rewrite Hchildrennil in *.
   intuition.
  * assert (HparentPart : parentInPartitionList s).
      { unfold consistency in *. intuition. }  
   assert(Hinpart : In partition (getPartitions multiplexer s)).
      {
      unfold consistency in *. 
      assert(Hcurparteqpart : (currentPartition s) = partition  \/
                (currentPartition s) <> partition ) by apply pageDecOrNot.
      destruct Hcurparteqpart as [Hcurparteqpart | Hcurparteqpart].
      *  subst. 
        unfold consistency in *.
        unfold currentPartitionInPartitionsList in *. 
        intuition.
      * subst. unfold consistency in *. 
        apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
          (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
          phyConfigPagesList ptRefChild currentShadow1;trivial;intuition. }
   assert(Hparentpart :In parent (getPartitions multiplexer s)).
   {
    unfold parentInPartitionList in *.
    
    apply HparentPart with partition;trivial.
    apply nextEntryIsPPgetParent.
       rewrite <- Hparent.
       symmetry.
        apply getParentAddDerivation with entry;trivial.  }

  assert(Hpartchild : getChildren parent s' = getChildren parent s). 
   { unfold consistency in *.
     apply addPartitionGetChildrenEq with (currentPartition s);trivial; intuition.
     assert(Hfalse : getChildren (currentPartition s)
        s' =
      getChildren (currentPartition s) s) by trivial.
     fold s' in Hfalse.
      rewrite Hfalse in *. 
      apply HnotinChildren;trivial.
   }
   rewrite Hpartchild.
   apply Hischild;trivial.
  rewrite <- Hparent.
  symmetry.
  apply getParentAddDerivation with entry;trivial.
Qed.



Lemma isPresentNotDefaultIffAddPartition  table idx entry s:
 lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->
isPresentNotDefaultIff s ->
isPresentNotDefaultIff
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := true; va := va entry |})
              (memory s) beqPage beqIndex |} .
Proof.
unfold isPresentNotDefaultIff.
simpl.
intros.
assert(StateLib.readPresent table0 idx0
  (add table idx (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex) 
  = StateLib.readPresent table0 idx0 (memory s)).
 apply readPresentAddDerivation with entry; trivial.
rewrite H1.
assert(StateLib.readPhyEntry table0 idx0
  (add table idx (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex) 
  = StateLib.readPhyEntry table0 idx0 (memory s)).
 apply readPhyEntryAddDerivation with entry; trivial.
rewrite H2.
trivial.   
Qed.

Lemma physicalPageNotDerivedAddPartition entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s ->
~ In phyDescChild (getChildren  (currentPartition s) s) -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->  
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 ->
physicalPageNotDerived s'.
Proof.
intros s' HisParent HnotinChildren.
intros. subst.
assert(Hnotderv : physicalPageNotDerived s).
{ unfold consistency in *.
  intuition. }
unfold physicalPageNotDerived in *.
intros parent va pdParent pageParent Hparentpart Hpdparent Hnotderiv Hmapped
child pdChild vaInChild pageChild Hchildren Hpdchild Hmappedchild.
assert(HmapS : forall pd va1, getMappedPage pd s' va1
 = getMappedPage pd s va1).
 { intros.  apply getMappedPageAddDerivation with entry;trivial. }
rewrite HmapS in *.
assert(HpdS : forall part , StateLib.getPd part (memory s') =
       StateLib.getPd part (memory s)).
  { intros. apply getPdAddDerivation with entry;trivial. }
rewrite HpdS in *.
assert(HderivS : forall part va1,  isDerived part va1 s' = isDerived part va1 s). 
{ intros. 
  unfold isDerived.
  assert(Hsh1S : forall part , StateLib.getFstShadow part (memory s') =
       StateLib.getFstShadow part (memory s)).
  { intros. apply getFstShadowAddDerivation with entry;trivial. }
  rewrite Hsh1S.
  case_eq (getFstShadow part (memory s)); intros; trivial.
   assert(HgetVirS :  getVirtualAddressSh1 p s' va1 =  getVirtualAddressSh1 p s va1). 
   { unfold getVirtualAddressSh1.
     case_eq(StateLib.getNbLevel);intros;trivial.
     assert(HindS : getIndirection p va1 l (nbLevel - 1) s' = getIndirection p va1 l (nbLevel - 1) s).
     { apply getIndirectionAddDerivation with entry;trivial. }
     rewrite HindS.
     destruct (getIndirection p va1 l (nbLevel - 1) s);trivial.
     destruct (defaultPage =? p0);trivial.
     unfold StateLib.readVirEntry.
     simpl. 
     case_eq( beqPairs (ptRefChildFromSh1, StateLib.getIndexOfAddr descChild fstLevel)
      (p0, StateLib.getIndexOfAddr va1 fstLevel) beqPage beqIndex);intros Hpairs;
      simpl.
      + apply beqPairsTrue in Hpairs.
        destruct Hpairs as (Hpairs1 & Hpairs2).
        rewrite <- Hpairs1.
        rewrite <- Hpairs2.
        assert(Hlookup : lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) 
       (memory s) beqPage beqIndex = Some (VE entry)) by trivial.
       rewrite Hlookup;trivial.
      + assert(Hmem : lookup p0 (StateLib.getIndexOfAddr va1 fstLevel)
    (removeDup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) 
       (memory s) beqPage beqIndex) beqPage beqIndex = 
       lookup p0 (StateLib.getIndexOfAddr va1 fstLevel) (memory s) beqPage beqIndex ).
       { apply removeDupIdentity.
        apply beqPairsFalse in Hpairs;trivial.
        intuition. }
      rewrite Hmem;trivial.
    }
    rewrite HgetVirS;trivial. }
rewrite HderivS in *.
clear   HderivS HpdS HmapS.
(* apply Hnotderv with parent va pdParent child pdChild vaInChild; trivial. *)
assert(Hcurparteq : (currentPartition s) = parent  \/
                (currentPartition s) <> parent ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  - subst.
    assert(Hneweq : phyDescChild = child  \/
                phyDescChild <> child ) by apply pageDecOrNot.
    destruct Hneweq as [Hneweq |Hneweq ].
    * subst child. 
      assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
      apply nextEntryIsPPgetPd;trivial.
       assert(Hmappednull : getMappedPages phyDescChild s = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial. }
      rewrite Hpdnewchild in *.
      inversion Hpdchild;subst pdChild; clear Hpdchild.
      assert(Htrue : In pageChild (getMappedPages phyDescChild s)).
      { unfold getMappedPages. 
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply filterOptionInIff.
        unfold getMappedPagesOption.
        apply in_map_iff.
        assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel vaInChild va1 ( CLevel (nbLevel -1) ) = true )
        by apply AllVAddrWithOffset0.
        destruct Heqvars as (va1 & Hva1 & Hva11).  
        exists va1.
        split;trivial.

        rewrite <- Hmappedchild.
        symmetry.
        apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
        apply getNbLevelEqOption. }
       rewrite Hmappednull in *.
       now contradict Htrue.
    * apply Hnotderv with (currentPartition s) va pdParent child pdChild vaInChild; trivial.

       assert(HnewChildrenlist : exists l1 l2 : list page,
      getChildren (currentPartition s) s' = l1 ++ [phyDescChild] ++ l2 /\ 
      getChildren (currentPartition s) s = l1 ++ l2).
      { unfold consistency in *.
      apply getChildrenSplitList with ptRefChild currentShadow1 currentPD;
      trivial; intuition. }
    destruct HnewChildrenlist as (l1 & l2 & Hi1 & Hi2).
    rewrite Hi1 in *.
    rewrite Hi2 in *.
    rewrite in_app_iff in *.
    destruct Hchildren as [Hchildren | Hchildren].
    left;trivial.
    rewrite in_app_iff in *.
    
    destruct Hchildren as [Hchildren | Hchildren].
    simpl in *.
    intuition.
     
    right;trivial.
 - assert(Hneweq : phyDescChild = parent  \/
                phyDescChild <> parent ) by apply pageDecOrNot.
    destruct Hneweq as [Hneweq |Hneweq ].
    * subst parent. 
     assert (Hchildrennil : getChildren phyDescChild s' = nil).
     { assert(Hincl : forall partition s, (* In partition (getPartitions multiplexer s)
                -> *)  incl (getChildren partition s) (getMappedPages partition s)).
        { intros.
          unfold incl.
          unfold getChildren.
          unfold getMappedPages.
          intros a Hx.
          destruct (StateLib.getNbLevel ); try now contradict H0.
          destruct  (StateLib.getPd partition (memory s0)); try now contradict H0.
          unfold getMappedPagesAux in *.
          rewrite filterOptionInIff in *.
          unfold getMappedPagesOption in *.
          rewrite in_map_iff in *.
          
  destruct Hx as (x & Hi & Hx).
        unfold getPdsVAddr in *.
        apply filter_In in Hx.
        
        exists x;split;intuition. }
       assert(Hmappednull : getMappedPages phyDescChild s' = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        (** we have an hypothesis **)
        rewrite getPdAddDerivation with phyDescChild  (Hardware.va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel)
        s entry true ;trivial.
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial.
        simpl.
        intros.
        rewrite readPhyEntryAddDerivation with (Hardware.va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        rewrite readPresentAddDerivation with (Hardware.va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial. }
        
       unfold incl in *.
       apply Hincl in Hchildren.
       rewrite  Hmappednull in *.
       now contradict Hchildren. }
      rewrite Hchildrennil in *;simpl;trivial.
      now contradict Hchildren.
    * assert(In parent (getPartitions multiplexer s)).
      {
       unfold consistency in *. 
      apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial;intuition. }
      apply Hnotderv with parent va pdParent child pdChild vaInChild; trivial.
       assert(Hpartchild : getChildren parent s' = getChildren parent s). 
   { unfold consistency in *.
     apply addPartitionGetChildrenEq with (currentPartition s);trivial; intuition.
     assert(Hfalse : getChildren (currentPartition s)
        s' =
      getChildren (currentPartition s) s) by trivial.
     fold s' in Hfalse.
      rewrite Hfalse in *. 
      apply HnotinChildren;trivial.
   }
   rewrite <- Hpartchild.
   trivial.
Qed.
Lemma multiplexerWithoutParentAddPartition  table idx entry s:
 lookup table idx (memory s) beqPage beqIndex = Some (VE entry) ->
multiplexerWithoutParent s ->
multiplexerWithoutParent
  {|
  currentPartition := currentPartition s;
  memory := add table idx (VE {| pd := true; va := va entry |})
              (memory s) beqPage beqIndex |} .
Proof.
unfold multiplexerWithoutParent.
simpl.
intros.
rewrite <- H0.
apply getParentAddDerivation with entry;trivial.  
Qed.


Lemma isParentAddPartition  entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1:
verticalSharing s ->
consistency s -> 
partitionsIsolation s -> 
(* partitionDescriptorEntry s ->
noDupConfigPagesList s ->
noDupMappedPagesList s -> *)
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             {|
             currentPartition := currentPartition s;
             memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                         (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}) ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->  
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
nextEntryIsPP phyDescChild PPRidx currentPart s -> 
currentPart = (currentPartition s) -> 
isParent s ->
In descChild getAllVAddrWithOffset0 -> 
isParent  {|
             currentPartition := currentPartition s;
             memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                         (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros Hvs Hcons Hiso (* Hpde Hnodupconf Hnodupmap *) Hlookup Hppsh3 Hppsh2 Hppsh1 Hpppd Hcurpart Hlevel HcurrentPD Hpost
Hnewpd Hnewsh1 Hnewsh2 Hnewsh31(*  Hnewsh32 Hnewsh33 *) HmappedDesc
HmappedPD Hmappedsh1 HmappedSh2 Hmappedsh3 Hnotconfig Hroot Hptnotnull Hep
Hpresent Hfstsh1 Hnotpart Hsh1 Hptsh1notnull
HphyPDcontent HphySh1content HphySh2content HphyListcontent1(*  HphyListcontent2 HphyListcontent3  *)
HnotConfig HnotConfig1 HnotConfig2 HnotConfig3 HnotConfig4
Ha1 Ha2 Ha3 Ha4 Ha5 Hphyparent HcurpartEq Hisparent Hnewphy.
unfold isParent  in *.
intros child parent  Hp1 Hp2.
simpl.
set(s' :=   {|
           currentPartition :=  _ |}) in *.
assert(Hparteq : parent = currentPart \/ parent <> currentPart) by apply pageDecOrNot.
destruct Hparteq as [Hparteq | Hparteq].
(* parent = currentPart *)
  + subst.
    assert(Hchildeq : child = phyDescChild  \/ child <> phyDescChild ) by apply pageDecOrNot.
    destruct Hchildeq as [Hchild1eq |Hchild1eq ].
    - subst child.
      assert(Hparentnew : getParent phyDescChild (memory s) = Some (currentPartition s)).
    apply nextEntryIsPPgetParent;trivial.
    assert(HgetParent: getParent phyDescChild (memory s')  =
    getParent phyDescChild (memory s)).
    apply getParentAddDerivation with entry;trivial.
    simpl in *.
    rewrite HgetParent in *.
    trivial.
    -  assert(Hparent : getParent child
  (add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
     (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex) =  
     getParent child(memory s) ).
     apply getParentAddDerivation with entry;trivial.
     rewrite Hparent.  
     apply Hisparent;trivial.
      { (** Have to prove this property using
      (forall partition : page,
        In partition (getPartitions multiplexer s) ->
        ~(partition = phyDescChild \/In phyDescChild (getConfigPagesAux partition s))) :
        not a partition implies not a child  **)
        assert(HnewChild : ~ In phyDescChild (getChildren  (currentPartition s) s)).
        { assert (~ In phyDescChild (getPartitions multiplexer s)).
          { unfold not. intros.
            apply Hnotconfig in H.
            contradict H;left;trivial. }         
        unfold not;intros Hfalse; contradict H.
        apply childrenPartitionInPartitionList with  (currentPartition s);trivial.
        unfold consistency in *. intuition. }
        unfold consistency in *.
        apply partitionInPreviousState with
         phyDescChild ptRefChild currentShadow1 currentPD
         {|
            currentPartition := currentPartition s;
            memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                        (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}
                         entry descChild ptRefChildFromSh1;intuition.
                          }
 +  assert(Hparentnotchild : parent = phyDescChild \/ parent <> phyDescChild ) by apply pageDecOrNot.
  destruct Hparentnotchild as [Hparentnotchild | Hparentnotchild].
  - subst.
    assert (Hchildrennil : getChildren phyDescChild
              s' =
                           nil).
   { assert(forall partition s, (* In partition (getPartitions multiplexer s)
              ->  *) incl (getChildren partition s) (getMappedPages partition s)).
      { intros.
        unfold incl.
        unfold getChildren.
        unfold getMappedPages.
        intros.
        destruct (StateLib.getNbLevel ); try now contradict H0.
        destruct  (StateLib.getPd partition (memory s0)); try now contradict H0.
        unfold getMappedPagesAux in *.
        rewrite filterOptionInIff in *.
        unfold getMappedPagesOption in *.
        rewrite in_map_iff in *.
        destruct H as (x & Hi & Hx).
        unfold getPdsVAddr in *.
        apply filter_In in Hx.
        exists x;split;intuition. intuition. intuition. }
        
    
     assert(Hmappednull : getMappedPages phyDescChild s' = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        (** we have an hypothesis **)
        rewrite getPdAddDerivation with phyDescChild  (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel)
        s entry true ;trivial.
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial.
        split;simpl.
        rewrite readPhyEntryAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        rewrite readPresentAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        (** PropagatedProperties : forall idx : index,
            StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
            StateLib.readPresent phyPDChild idx (memory s) = Some false **) }
            assert(Hbb1 :  forall (partition : page) (s : state) (a : page),
      In a (getChildren partition s) -> In a (getMappedPages partition s)) by trivial.
     generalize (Hbb1  phyDescChild s'); clear Hbb1; intros Hbb1.
     rewrite Hmappednull in *.
     destruct (getChildren phyDescChild s') .
     trivial. 
     assert(In p []).
     apply Hbb1.
     simpl;left;trivial. contradiction.
 }
     unfold s' in *.
     clear s'.
     set(s' := {|currentPartition := _|}) in *. 
   rewrite Hchildrennil in *.
   now contradict Hp2.
   - assert(Hparent : getParent child
  (add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
     (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex) =  
     getParent child(memory s) ).
     apply getParentAddDerivation with entry;trivial.
     rewrite Hparent.  
    assert(Hphynotchild : ~ In phyDescChild (getChildren currentPart s)).
    { assert(getMappedPage currentPD s descChild = SomePage phyDescChild /\
      ~ In descChild (getPdsVAddr currentPart level getAllVAddrWithOffset0 s)) as ( Hvaphy' & Hpds1).
      { split.
        + apply getMappedPageGetTableRoot with ptRefChild currentPart;trivial.
        + unfold isPartitionFalse in *.
          move Hnotpart at bottom.
          unfold getPdsVAddr.
          rewrite filter_In.
          apply Classical_Prop.or_not_and.
          right.
          unfold checkChild.
          rewrite nextEntryIsPPgetFstShadow in *.
          rewrite Hfstsh1.
          assert(getIndirection currentShadow1 descChild level (nbLevel - 1) s = Some ptRefChildFromSh1).
          apply getIndirectionGetTableRoot with currentPart;trivial.
          symmetry;trivial.
          rewrite H.
          destruct  (ptRefChildFromSh1 =? defaultPage);trivial.
          auto.
          destruct Hnotpart; rewrite H0;auto. }
     
      unfold getChildren.
      rewrite <- Hlevel.
      rewrite nextEntryIsPPgetPd in *.
      rewrite HcurrentPD.
      unfold getMappedPagesAux.
      rewrite filterOptionInIff.
      unfold getMappedPagesOption.
      rewrite in_map_iff.
      unfold not.
      intros.
      destruct H as (samev & Hi & Hii).
      assert(descChild = samev).
      apply eqMappedPagesEqVaddrs with phyDescChild currentPD s;trivial.
              unfold getPdsVAddr in *.
        apply filter_In in Hii. intuition.
      unfold consistency in *.
      assert(noDupMappedPagesList s) by intuition.
      unfold noDupMappedPagesList in *.
      apply H in Hcurpart. clear H.
      move Hcurpart at bottom.
      unfold getMappedPages in Hcurpart.
      rewrite HcurrentPD in *.
      unfold getMappedPagesAux  in *.
      unfold getMappedPagesOption in Hcurpart;trivial.
      subst.
      now contradict Hpds1. }
      unfold consistency in *.
 assert(Hkey : In parent (getPartitions multiplexer s)).
 {
   apply addPartitionAddsSinglePartition with 
   entry descChild ptRefChildFromSh1
currentPart phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1;trivial.
 intuition. 
 intuition.
 intuition.
} 
  
      apply Hisparent;trivial.
  assert(Hchildeq : child = phyDescChild \/  child <> phyDescChild ) by apply pageDecOrNot. 
  destruct Hchildeq as [Hchild1eq | Hchild2eq];
  subst.
  * assert(Hchildeq : getChildren parent s' = getChildren parent s).
    { unfold consistency in *. 
      apply addPartitionGetChildrenEq with  (currentPartition s); intuition.
      fold s' in H.
      rewrite H in *. 
      apply Hphynotchild;trivial. }  
    rewrite Hchildeq in Hp2.
    assert (In  phyDescChild (getPartitions multiplexer s)).
    apply childrenPartitionInPartitionList with parent; trivial.
    unfold consistency in *. intuition. 
    apply HnotConfig in H.
    apply Classical_Prop.not_or_and in H.
    intuition.
  * fold s' in Hpost.
    assert(Hchildeq : getChildren parent s' = getChildren parent s).
    { unfold consistency in *. 
      apply addPartitionGetChildrenEq with  (currentPartition s);intuition.
      fold s' in H.
      rewrite H in *. 
      apply Hphynotchild;trivial. }  
    rewrite Hchildeq in Hp2.
    trivial.
Qed.
 
Lemma noDupPartitionTreeAddChild entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxConfigPagesList ptConfigPagesList idxSh2
ptSh2Child shadow2 idxSh1 ptSh1Child shadow1 idxPDChild ptPDChild pdChild idxRefChild list
:
isParent s -> 
verticalSharing s ->
partitionsIsolation s -> 
consistency s -> 
(* partitionDescriptorEntry s ->
noDupConfigPagesList s ->
noDupMappedPagesList s -> *)
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
nextEntryIsPP phyDescChild PPRidx currentPart s -> 
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             {|
             currentPartition := currentPartition s;
             memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                         (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}) ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->  
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->

In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) -> 
 *) initConfigPagesListPostCondition phyConfigPagesList s ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyPDChild (getAccessibleMappedPages partition s)) -> 
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phySh1Child (getAccessibleMappedPages partition s)) ->
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phySh2Child (getAccessibleMappedPages partition s)) ->
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyConfigPagesList (getAccessibleMappedPages partition s)) ->
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyDescChild (getAccessibleMappedPages partition s)) ->

kernelDataIsolation s ->
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
StateLib.getIndexOfAddr descChild fstLevel = idxRefChild ->
entryPresentFlag ptRefChild idxRefChild true s ->
entryUserFlag ptRefChild idxRefChild false s ->
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) ->
(defaultPage =? ptPDChild) = false ->
StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild ->
entryPresentFlag ptPDChild idxPDChild true s ->
entryUserFlag ptPDChild idxPDChild false s ->
(forall idx : index,
StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) ->
(defaultPage =? ptSh1Child) = false ->
StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1 ->
entryPresentFlag ptSh1Child idxSh1 true s ->
entryUserFlag ptSh1Child idxSh1 false s ->
(forall idx : index,
StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) ->
(defaultPage =? ptSh2Child) = false ->
StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2 ->
entryPresentFlag ptSh2Child idxSh2 true s ->
entryUserFlag ptSh2Child idxSh2 false s->
(forall idx : index,
StateLib.getIndexOfAddr list fstLevel = idx ->
isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s) ->
(defaultPage =? ptConfigPagesList) = false ->
StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList ->
entryPresentFlag ptConfigPagesList idxConfigPagesList true s ->
entryUserFlag ptConfigPagesList idxConfigPagesList false s ->


isEntryPage ptPDChild idxPDChild phyPDChild s ->
isEntryPage ptSh1Child idxSh1 phySh1Child s ->
isEntryPage ptSh2Child idxSh2 phySh2Child s ->
isEntryPage ptConfigPagesList idxConfigPagesList phyConfigPagesList s ->

In descChild getAllVAddrWithOffset0 -> 
noDupPartitionTree {|
  currentPartition := currentPartition s;
  memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}.
Proof.
intros HisParent Hvs Hiso Hcons (* Hpde Hnodupconf Hnodupmap *) Hlookup Hppsh3 Hppsh2 Hppsh1 Hpppd Hppparent Hcurpart Hlevel HcurrentPD Hpost
Hnewpd Hnewsh1 Hnewsh2 Hnewsh31(*  Hnewsh32 Hnewsh33 *) HmappedDesc
HmappedPD Hmappedsh1 HmappedSh2 Hmappedsh3 Hnotconfig Hroot Hptnotnull Hep
Hpresent Hfstsh1 Hnotpart Hsh1 Hptsh1notnull.
intros HphyPDcontent
HphySh1content HphySh2content HphyListcontent1(*  HphyListcontent2 HphyListcontent3  *)
HnotConfig HnotConfig1 HnotConfig2 HnotConfig3 HnotConfig4

Ha1 Ha2 Ha3 Ha4 Ha5.
intros  Hb1 Hb2 Hb3 Hb4 Hb5.
unfold kernelDataIsolation.
intros HKDI.
intros .

assert(Hnoduptree : noDupPartitionTree s).
unfold consistency in *.
intuition.

unfold noDupPartitionTree in *.
set(s' :=  {|
     currentPartition := _ |}) in *.
 assert(Hphynotchild : ~ In phyDescChild (getChildren currentPart s)).
    { assert(getMappedPage currentPD s descChild = SomePage phyDescChild /\
      ~ In descChild (getPdsVAddr currentPart level getAllVAddrWithOffset0 s)) as ( Hvaphy' & Hpds1).
      { split.
        + apply getMappedPageGetTableRoot with ptRefChild currentPart;trivial.
        + unfold isPartitionFalse in *.
          move Hnotpart at bottom.
          unfold getPdsVAddr.
          rewrite filter_In.
          apply Classical_Prop.or_not_and.
          right.
          unfold checkChild.
          rewrite nextEntryIsPPgetFstShadow in *.
          rewrite Hfstsh1.
          assert(Hind : getIndirection currentShadow1 descChild level (nbLevel - 1) s = Some ptRefChildFromSh1).
          apply getIndirectionGetTableRoot with currentPart;trivial.
          symmetry;trivial.
          rewrite Hind.
          destruct  (ptRefChildFromSh1 =? defaultPage);trivial.
          auto.
          destruct Hnotpart as [Hnotpart|Hnotpart]; rewrite Hnotpart;auto. }
     
      unfold getChildren.
      rewrite <- Hlevel.
      rewrite nextEntryIsPPgetPd in *.
      rewrite HcurrentPD.
      unfold getMappedPagesAux.
      rewrite filterOptionInIff.
      unfold getMappedPagesOption.
      rewrite in_map_iff.
      unfold not.
      intros Hfalse.
      destruct Hfalse as (samev & Hi & Hii).
      assert(descChild = samev).
       apply eqMappedPagesEqVaddrs with phyDescChild currentPD s;trivial.
              unfold getPdsVAddr in *.
        apply filter_In in Hii. intuition.
      unfold consistency in *.
      assert(Hnodup : noDupMappedPagesList s) by intuition.
      unfold noDupMappedPagesList in *.
      apply Hnodup in Hcurpart.
       move Hcurpart at bottom.
      unfold getMappedPages in Hcurpart.
      rewrite HcurrentPD in *.
      unfold getMappedPagesAux  in *.
      unfold getMappedPagesOption in Hcurpart;trivial.
      subst.
      now contradict Hpds1. } 
      
  
  assert (Hsplitlist : exists 
   nbPagesParent  l1 l2,
          getPartitionAux multiplexer s (nbPage +1) = l1 ++ [currentPart] ++
          flat_map (fun p => getPartitionAux p s nbPagesParent  )
          (getChildren currentPart s)++ l2
          /\
          getPartitionAux multiplexer s' (nbPage +1)  = l1 ++ [currentPart] ++
          flat_map (fun p => getPartitionAux p s' nbPagesParent  )
          (getChildren currentPart s')++ l2 ).
  { unfold consistency in *.
    apply getPartitionAuxSplitListNewSate' with phyDescChild ptRefChild currentShadow1
     currentPD;intuition.
    apply addPartitionKeepsAllPartitionsInTree;trivial. }
  destruct Hsplitlist as ( nbPagesParent &  l11 & l22 & Hsplitlist).
  destruct Hsplitlist as (Hsplitlist1 & Hsplitlist2).
  unfold getPartitions in *.
  
(* rewrite Hsplitlist1 in Hnoduptree;clear Hsplitlist1.
  rewrite Hsplitlist2 ;clear Hsplitlist2. *)
 assert(HchildrenS : exists l1 l2,
  getChildren currentPart s' = l1 ++ [phyDescChild] ++ l2 /\
  getChildren currentPart s = l1 ++l2).
{  unfold consistency in *. 
  apply getChildrenSplitList with ptRefChild currentShadow1 currentPD; intuition. }
  destruct HchildrenS as (l1 & l2 & HchildrenS & Hchildrenprev).
  assert(Hnodupchildren : NoDup (getChildren currentPart s')).
  { unfold getChildren.
    rewrite <- Hlevel.
    assert(Hpd : StateLib.getPd currentPart (memory s) = 
    StateLib.getPd currentPart (memory s')).
    unfold s'. simpl. symmetry. 
    apply getPdAddDerivation with entry;trivial.
    rewrite <- Hpd.
    rewrite nextEntryIsPPgetPd in *. 
    rewrite HcurrentPD. 
    apply  addPartitionGetChildrenNoDup;trivial.
    assert(HmapS : getMappedPagesAux currentPD getAllVAddrWithOffset0
     {|
     currentPartition := currentPartition s;
     memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                 (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |}
                 = getMappedPagesAux currentPD getAllVAddrWithOffset0 s
     ). 
    apply getMappedPagesAuxAddDerivation with entry;trivial.
    rewrite HmapS.
    unfold consistency in *.
    assert(Hmap : noDupMappedPagesList s) by intuition.
    unfold noDupMappedPagesList in *.
    unfold getMappedPages in *.
    apply Hmap in Hcurpart.
    move Hcurpart at bottom.
    rewrite HcurrentPD in *;trivial.
    intuition. }
 assert(Hmappednull : getMappedPages phyDescChild s' = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        (** we have an hypothesis **)
        rewrite getPdAddDerivation with phyDescChild  (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel)
        s entry true ;trivial.
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial.
        split;simpl.
        rewrite readPhyEntryAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        rewrite readPresentAddDerivation with (va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        destruct HphyPDcontent with idx;intuition.
        (** PropagatedProperties : forall idx : index,
            StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
            StateLib.readPresent phyPDChild idx (memory s) = Some false **) }
 rewrite Hsplitlist1 in Hnoduptree. (* ;clear Hsplitlist1. *)
  rewrite Hsplitlist2. (* ;clear Hsplitlist2. *)
 move Hsplitlist2 at top.
 move Hsplitlist1 at top.
  rewrite NoDupSplitInclIff.
 rewrite NoDupSplitInclIff in Hnoduptree.
  destruct Hnoduptree as (Hnodup1 & Hnodup2).
   destruct Hnodup1 as (Hnodup1 & Hnodup3).
  simpl in *.
  rewrite NoDup_cons_iff in Hnodup3.
  destruct Hnodup3 as (Hnodup3 & Hnodup4).
    assert(Hzero : getPartitionAux phyDescChild s' nbPagesParent = [phyDescChild] \/
  getPartitionAux phyDescChild s' nbPagesParent = [] ).
  { clear Hnodup4 Hnodup2 Hnodup3 .
  induction nbPagesParent.
  simpl. right.  trivial.
  simpl. left.
   assert (Hchildrennil : getChildren phyDescChild s' = nil).
   { assert(forall partition s, (* In partition (getPartitions multiplexer s)
              ->  *) incl (getChildren partition s) (getMappedPages partition s)).
      { intros.
        unfold incl.
        unfold getChildren.
        unfold getMappedPages.
        intros aa Haaa.
        destruct (StateLib.getNbLevel ); try now contradict Haaa.
        destruct  (StateLib.getPd partition (memory s0)); try now contradict Haaa.
        unfold getMappedPagesAux in *.
        rewrite filterOptionInIff in *.
        unfold getMappedPagesOption in *.
        rewrite in_map_iff in *.
          destruct Haaa as (x & Hi & Hx).
        unfold getPdsVAddr in *.
        apply filter_In in Hx.
        
        exists x;split;intuition. }
   (*   assert(Hparent : In phyDescChild (getPartitions multiplexer s')).
     apply childrenPartitionInPartitionList with currentPart;trivial.
     apply addPartitionKeepsAllPartitionsInTree;trivial. 
     apply H in Hparent. *)
     unfold incl in *.
(*      clear IHn. 
     
     fold s'. *)
     assert(Hbb1 :  forall (partition : page) (s : state) (a : page),
      In a (getChildren partition s) -> In a (getMappedPages partition s)) by trivial.
     generalize (Hbb1  phyDescChild s'); clear Hbb1; intros Hbb1.
     rewrite Hmappednull in *.
     destruct (getChildren phyDescChild s') .
     trivial. 
     assert(In p []).
     apply Hbb1.
     simpl;left;trivial. contradiction. }
  rewrite Hchildrennil;simpl;trivial.   
  } 
  
  split.
  +
  
  split. intuition.
  
 


    
  constructor.
  -
  rewrite in_app_iff in *.
  apply Classical_Prop.not_or_and in Hnodup3 as (Hnodup3 & Hnodup5).
  apply Classical_Prop.and_not_or.
  split;trivial.
  rewrite  HchildrenS.
  rewrite Hchildrenprev in Hnodup3.
  rewrite flat_map_app_cons.
  rewrite flat_map_app in Hnodup3.
  rewrite in_app_iff in Hnodup3.
   apply Classical_Prop.not_or_and in Hnodup3 as (Hnodup3 & Hnodup6).
  rewrite in_app_iff.
  apply Classical_Prop.and_not_or.
  rewrite in_app_iff.
  split.
  contradict Hnodup3.
  {      rewrite in_flat_map in *.
     destruct Hnodup3 as (child & Hancestor1 & Hancestor2).
     exists child;split;trivial.
     assert(Hget : getPartitionAux child s nbPagesParent = 
     getPartitionAux child s' nbPagesParent).
     { unfold consistency in *.
       apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
        intuition. intuition. intuition. intuition. intuition. 
       apply childrenPartitionInPartitionList with currentPart;trivial.
        intuition.
       rewrite Hchildrenprev.
       rewrite in_app_iff.
       left;trivial.
       apply noCycleInPartitionTree2;trivial.
       intuition. intuition. intuition.
       intuition. intuition.  rewrite Hchildrenprev.
       rewrite in_app_iff.
       left;trivial. }
      trivial. 
    rewrite Hget;trivial. }
apply Classical_Prop.and_not_or.
split.
 simpl. rewrite app_nil_r.
  
 destruct Hzero as [Hzero | Hzero]; rewrite Hzero.
 simpl.
 intuition.
 apply HnotConfig with currentPart;trivial.
 left;trivial.
 subst;trivial.
 intuition.
  contradict Hnodup6.
  {      rewrite in_flat_map in *.
     destruct Hnodup6 as (child & Hancestor1 & Hancestor2).
     exists child;split;trivial.
     assert(Hget : getPartitionAux child s nbPagesParent = 
     getPartitionAux child s' nbPagesParent).
     { unfold consistency in *.
       apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
        intuition. intuition. intuition. intuition. intuition. 
       apply childrenPartitionInPartitionList with currentPart;trivial.
        intuition.
       rewrite Hchildrenprev.
       rewrite in_app_iff.
       right;trivial.
       apply noCycleInPartitionTree2;trivial.
       intuition. intuition. intuition.
       intuition. intuition.  rewrite Hchildrenprev.
       rewrite in_app_iff.
       right;trivial. }
      trivial. 
    rewrite Hget;trivial. }
- rewrite NoDupSplitInclIff in *.
destruct Hnodup4 as ((Hnodup4 & Hnodup5) & Hnodup6).
split.
*  split;trivial.
rewrite HchildrenS.
rewrite Hchildrenprev in Hnodup4.
rewrite flat_map_app_cons.
rewrite flat_map_app in Hnodup4.
rewrite NoDupSplitInclIff in *.
destruct Hnodup4 as ((Hnodup4 & Hnodup7) & Hnodup8).
split.
-- split.
++
{
 assert(Hp1 : forall a , In a l1 ->  In a (getPartitions multiplexer s)).
 intros.
 unfold consistency in *.
 apply childrenPartitionInPartitionList with currentPart;trivial.
 intuition.
  rewrite Hchildrenprev.
  apply in_app_iff.
  left;trivial.
assert(Hp2 : forall a , In a l1 -> 
~ In currentPart (getPartitionAux a s nbPagesParent)).
intros. unfold consistency in *.
  apply noCycleInPartitionTree2.
   intuition. intuition. intuition. intuition. intuition.
    intuition. intuition. rewrite Hchildrenprev.
  apply in_app_iff.
  left;trivial. 
assert(Hp3 : forall a, In a l1 -> 
In a (getChildren currentPart s)).
intros. rewrite Hchildrenprev.
  apply in_app_iff.
  left;trivial. 
assert(Hp5 : incl l1 (getChildren currentPart s)).
rewrite Hchildrenprev. intuition.
assert(Hp6 : incl l1 (getChildren currentPart s')). 
rewrite HchildrenS. intuition. 
 clear Hnodup8 HchildrenS Hchildrenprev.
induction l1.
simpl;trivial.
simpl.
apply NoDupSplitInclIff.
simpl in Hnodup4.
apply NoDupSplitInclIff in Hnodup4.
split.
split.
 assert(Ha : getPartitionAux a s' nbPagesParent = getPartitionAux a s nbPagesParent). 
{ symmetry.
unfold consistency in *. 
apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
 intuition. intuition. intuition. intuition. intuition.
 apply Hp1.
 simpl;left;trivial.
 apply Hp2.
 simpl;left;trivial. }
 rewrite Ha.
 intuition.
 apply IHl1.
 intuition.
 intros.
 apply Hp1.
 simpl.
 right;trivial.
 intros.
 apply Hp2;right;trivial.
 intros.
 apply Hp3;right;trivial.
 intros. (* 
 apply Hp4;right;trivial. *)
 unfold incl in *.
 intros. apply Hp5. simpl. right;trivial.
 unfold incl in *.
 intros. apply Hp6. simpl. right;trivial.   
 clear IHl1. 
destruct Hnodup4 as ((Hnodup4 & Hnodup9) & Hnodup10).
unfold disjoint in Hnodup10.
unfold disjoint.
intros x Hx.      
 
 
 assert(Htrue : 
  getPartitionAux a s nbPagesParent = getPartitionAux a s' nbPagesParent).
{  unfold consistency in *. 
  apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
 intuition. intuition. intuition. intuition. intuition.
 apply Hp1.
 simpl;left;trivial.
 apply Hp2.
 simpl;left;trivial. }
 rewrite <- Htrue in *. 
  apply Hnodup10 in Hx.
  contradict Hx.        
 
{      rewrite in_flat_map in *.
     destruct Hx as (child & Hancestor1 & Hancestor2).
     exists child;split;trivial.
     assert(Hget : getPartitionAux child s nbPagesParent = 
     getPartitionAux child s' nbPagesParent).
     { unfold consistency in *.
       apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
        intuition. intuition. intuition. intuition. intuition. 
       apply childrenPartitionInPartitionList with currentPart;trivial.
        intuition.
        unfold incl in Hp5.
        apply Hp5. simpl;right;trivial.
       apply noCycleInPartitionTree2;trivial.
       intuition. intuition. intuition.
       intuition. intuition.   unfold incl in Hp5.
        apply Hp5. simpl;right;trivial. }
      trivial. 
    rewrite Hget;trivial. } }
    ++
simpl.
rewrite app_nil_r.
apply NoDupSplitInclIff.
split.
split. 
simpl.
destruct Hzero as [Hzero | Hzero]; rewrite Hzero.
 constructor;intuition.
 
 constructor. constructor.
{
 assert(Hp1 : forall a , In a l2 ->  In a (getPartitions multiplexer s)).
 intros.
 unfold consistency in *.
 apply childrenPartitionInPartitionList with currentPart;trivial.
 intuition.
  rewrite Hchildrenprev.
  apply in_app_iff.
  right;trivial.
assert(Hp2 : forall a , In a l2 -> 
~ In currentPart (getPartitionAux a s nbPagesParent)).
intros. unfold consistency in *.
  apply noCycleInPartitionTree2.
   intuition. intuition. intuition. intuition. intuition.
    intuition. intuition. rewrite Hchildrenprev.
  apply in_app_iff.
  right;trivial. 
assert(Hp3 : forall a, In a l2 -> 
In a (getChildren currentPart s)).
intros. rewrite Hchildrenprev.
  apply in_app_iff.
  right;trivial. 
assert(Hp5 : incl l2 (getChildren currentPart s)).
rewrite Hchildrenprev. intuition.
assert(Hp6 : incl l2 (getChildren currentPart s')). 
rewrite HchildrenS. intuition. 
 clear Hnodup8 HchildrenS Hchildrenprev.
induction l2.
simpl;trivial.
simpl.
apply NoDupSplitInclIff.
simpl in Hnodup7.
apply NoDupSplitInclIff in Hnodup7.
split.
*
split.
++
 assert(Ha : getPartitionAux a s' nbPagesParent = getPartitionAux a s nbPagesParent). 
{ symmetry.
unfold consistency in *. 
apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
 intuition. intuition. intuition. intuition. intuition.
 apply Hp1.
 simpl;left;trivial.
 apply Hp2.
 simpl;left;trivial. }
 rewrite Ha.
 intuition.
++ apply IHl2.
 intuition.
 intros.
 apply Hp1.
 simpl.
 right;trivial.
 intros.
 apply Hp2;right;trivial.
 intros.
 apply Hp3;right;trivial.
 intros. (* 
 apply Hp4;right;trivial. *)
 unfold incl in *.
 intros. apply Hp5. simpl. right;trivial.
 unfold incl in *.
 intros. apply Hp6. simpl. right;trivial.
*   
 clear IHl2. 
destruct Hnodup7 as ((Hnodup7 & Hnodup9) & Hnodup10).
unfold disjoint in Hnodup10.
unfold disjoint.
intros x Hx.
 assert(Htrue : 
  getPartitionAux a s nbPagesParent = getPartitionAux a s' nbPagesParent).
  unfold consistency in *. 
  apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
 intuition. intuition. intuition. intuition. intuition.
 apply Hp1.
 simpl;left;trivial.
 apply Hp2.
 simpl;left;trivial.
 rewrite <- Htrue in *. 
  apply Hnodup10 in Hx.
  contradict Hx.        
 
{      rewrite in_flat_map in *.
     destruct Hx as (child & Hancestor1 & Hancestor2).
     exists child;split;trivial.
     assert(Hget : getPartitionAux child s nbPagesParent = 
     getPartitionAux child s' nbPagesParent).
     { unfold consistency in *.
       apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
        intuition. intuition. intuition. intuition. intuition. 
       apply childrenPartitionInPartitionList with currentPart;trivial.
        intuition.
        unfold incl in Hp5.
        apply Hp5. simpl;right;trivial.
       apply noCycleInPartitionTree2;trivial.
       intuition. intuition. intuition.
       intuition. intuition.   unfold incl in Hp5.
        apply Hp5. simpl;right;trivial. }
      trivial. 
    rewrite Hget;trivial. } }
        
 destruct Hzero as [Hzero | Hzero]; rewrite Hzero.
unfold disjoint. 
 simpl.
intros x Hx.
destruct Hx as [Hx | Hx]; try now contradict  Hx.
   subst x.
   clear Hzero.
   rewrite in_flat_map.
   unfold not;intros Hfalse.
   destruct Hfalse as (x & Hx & Hxx).
   contradict Hxx.
    
 
 
 assert(Htrue : 
  getPartitionAux x s nbPagesParent = getPartitionAux x s' nbPagesParent).
  { unfold consistency in *. 
  apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
 intuition. intuition. intuition. intuition. intuition.

       apply childrenPartitionInPartitionList with currentPart;trivial.
        intuition.
        rewrite Hchildrenprev.
        intuition. 
       apply noCycleInPartitionTree2;trivial.
       intuition. intuition. intuition.
       intuition. intuition. rewrite Hchildrenprev.
        intuition. }
      trivial. 
    rewrite <- Htrue;trivial.
    assert (Hicl : incl (getPartitionAux x s nbPagesParent) (getPartitions multiplexer s)).
    unfold getPartitions.
    rewrite Hsplitlist1.
    rewrite  Hchildrenprev.
    unfold incl.
    intros.
    apply in_app_iff.
    right.
    simpl.
    right.
    rewrite flat_map_app.
    apply in_app_iff.
    left. 
    apply in_app_iff.
    right.
    rewrite in_flat_map.
    exists x. split; trivial.
    assert (Hnotintree : ~ In phyDescChild (getPartitions multiplexer s)).
          { unfold not. intros Hfalse.
            apply HnotConfig in Hfalse.
            contradict Hfalse;left;trivial. }
      contradict Hnotintree.
      unfold incl in Hicl.
      apply Hicl;trivial.
      unfold disjoint.
      intros. 
      intuition.
--  

unfold disjoint.
intros x Hdisjoint.
rewrite in_app_iff.
apply Classical_Prop.and_not_or.

split.
++

 simpl.
 rewrite app_nil_r.
 destruct Hzero as [Hzero | Hzero]; rewrite Hzero.
 simpl.
 apply Classical_Prop.and_not_or.
 split;[|intuition].
     unfold not;intros Hfalse.
   subst x.
  rewrite in_flat_map in Hdisjoint.
   destruct Hdisjoint as (x & Hx & Hxx).
   contradict Hxx.
    
 
 
 assert(Htrue : 
  getPartitionAux x s nbPagesParent = getPartitionAux x s' nbPagesParent).
  { unfold consistency in *. 
  apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
 intuition. intuition. intuition. intuition. intuition.

       apply childrenPartitionInPartitionList with currentPart;trivial.
        intuition.
        rewrite Hchildrenprev.
        intuition. 
       apply noCycleInPartitionTree2;trivial.
       intuition. intuition. intuition.
       intuition. intuition. rewrite Hchildrenprev.
        intuition. }
      trivial. 
    rewrite <- Htrue;trivial.
    assert (Hicl : incl (getPartitionAux x s nbPagesParent) (getPartitions multiplexer s)).
    { unfold getPartitions.
    rewrite Hsplitlist1.
    rewrite  Hchildrenprev.
    unfold incl.
    intros.
    apply in_app_iff.
    right.
    simpl.
    right.
    rewrite flat_map_app.
    apply in_app_iff.
    left. 
    apply in_app_iff.
    left.
    rewrite in_flat_map.
    exists x. split; trivial. }
    assert (Hnotintree : ~ In phyDescChild (getPartitions multiplexer s)).
          { unfold not. intros Hfalse.
            apply HnotConfig in Hfalse.
            contradict Hfalse;left;trivial. }
      contradict Hnotintree.
      unfold incl in Hicl.
      apply Hicl;trivial.
      unfold disjoint.
      intros. 
      intuition.
++  

unfold disjoint in Hnodup8.
assert(Hpre : In x (flat_map (fun p : page => getPartitionAux p s nbPagesParent) l1)). 
rewrite in_flat_map in *.
destruct Hdisjoint as (x0 & Hx0 & Hx00).
exists x0; split;trivial.
 assert(Htrue : 
  getPartitionAux x0 s nbPagesParent = getPartitionAux x0 s' nbPagesParent).
  { unfold consistency in *. 
  apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
 intuition. intuition. intuition. intuition. intuition.

       apply childrenPartitionInPartitionList with currentPart;trivial.
        intuition.
        rewrite Hchildrenprev.
        intuition. 
       apply noCycleInPartitionTree2;trivial.
       intuition. intuition. intuition.
       intuition. intuition. rewrite Hchildrenprev.
        intuition. }

      trivial.
   
       
    rewrite  Htrue;trivial.
       apply Hnodup8 in Hpre.
       contradict Hpre.
 rewrite in_flat_map in *.
destruct Hpre as (x0 & Hx0 & Hx00).
exists x0; split;trivial.
 assert(Htrue : 
  getPartitionAux x0 s nbPagesParent = getPartitionAux x0 s' nbPagesParent).
  { unfold consistency in *. 
  apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
 intuition. intuition. intuition. intuition. intuition.

       apply childrenPartitionInPartitionList with currentPart;trivial.
        intuition.
        rewrite Hchildrenprev.
        intuition. 
       apply noCycleInPartitionTree2;trivial.
       intuition. intuition. intuition.
       intuition. intuition. rewrite Hchildrenprev.
        intuition. }

      trivial.
   
       
    rewrite  Htrue;trivial.
*   unfold disjoint.
 unfold disjoint in Hnodup6.
intros x Hdisjoint.

rewrite HchildrenS in Hdisjoint.
rewrite flat_map_app_cons in Hdisjoint.
rewrite in_app_iff in Hdisjoint.
destruct Hdisjoint as [ Hdisjoint | Hdisjoint].
++
apply Hnodup6.
rewrite Hchildrenprev.
rewrite flat_map_app.
apply in_app_iff.
left.
rewrite in_flat_map in *.
destruct Hdisjoint as (x0 & Hx0 & Hx00).
exists x0; split;trivial.
 assert(Htrue : 
  getPartitionAux x0 s nbPagesParent = getPartitionAux x0 s' nbPagesParent).
  { unfold consistency in *. 
  apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
 intuition. intuition. intuition. intuition. intuition.

       apply childrenPartitionInPartitionList with currentPart;trivial.
        intuition.
        rewrite Hchildrenprev.
        intuition. 
       apply noCycleInPartitionTree2;trivial.
       intuition. intuition. intuition.
       intuition. intuition. rewrite Hchildrenprev.
        intuition. }

      trivial.
   
rewrite Htrue;trivial.
++ rewrite in_app_iff in Hdisjoint.
destruct Hdisjoint as [ Hdisjoint | Hdisjoint].
-- simpl in *.
  rewrite app_nil_r in Hdisjoint.
 destruct Hzero as [Hzero | Hzero]; rewrite Hzero in *.
** simpl in *.
intuition.
subst x.


    assert (Hicl : incl l22 (getPartitions multiplexer s)).
    { unfold getPartitions.
    rewrite Hsplitlist1.
    intuition.
 }
    assert (Hnotintree : ~ In phyDescChild (getPartitions multiplexer s)).
          { unfold not. intros Hfalse.
            apply HnotConfig in Hfalse.
            contradict Hfalse;left;trivial. left;trivial. }
      contradict Hnotintree.
      unfold incl in Hicl.
      apply Hicl;trivial.
** now contradict Hdisjoint.
--   apply Hnodup6.
rewrite Hchildrenprev.
rewrite flat_map_app.
apply in_app_iff.
right.
rewrite in_flat_map in *.
destruct Hdisjoint as (x0 & Hx0 & Hx00).
exists x0; split;trivial.
 assert(Htrue : 
  getPartitionAux x0 s nbPagesParent = getPartitionAux x0 s' nbPagesParent).
  { unfold consistency in *. 
  apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
 intuition. intuition. intuition. intuition. intuition.

       apply childrenPartitionInPartitionList with currentPart;trivial.
        intuition.
        rewrite Hchildrenprev.
        intuition. 
       apply noCycleInPartitionTree2;trivial.
       intuition. intuition. intuition.
       intuition. intuition. rewrite Hchildrenprev.
        intuition. }

      trivial.
   
rewrite Htrue;trivial.
+  rewrite HchildrenS. 
      unfold disjoint.
      intros x Hx.
      simpl.
  
     
apply Classical_Prop.and_not_or.

unfold consistency in *.
assert(Hnoduptree : noDupPartitionTree s) by intuition.
unfold noDupPartitionTree in *.
unfold getPartitions in Hnoduptree.
rewrite  Hsplitlist1 in Hnoduptree.
apply NoDupSplitInclIff in Hnoduptree.
destruct Hnoduptree as ((Hnodup8 & Hnodup9) &Hnodup10).
unfold disjoint in Hnodup10.
split. 
* apply Hnodup10 in Hx. clear Hnodup10.
simpl in *.
apply Classical_Prop.not_or_and in Hx as (Hnodup11 & Hnodup12).

trivial.
*
rewrite in_app_iff.
apply Classical_Prop.and_not_or.
split;trivial.
--
rewrite flat_map_app_cons.
simpl.

rewrite app_nil_r.
rewrite in_app_iff.
apply Classical_Prop.and_not_or.
split;trivial.
++ apply Hnodup10 in Hx. clear Hnodup10.
simpl in *.
apply Classical_Prop.not_or_and in Hx as (Hnodup11 & Hnodup12).

rewrite in_app_iff in Hnodup12.
apply Classical_Prop.not_or_and in Hnodup12 as (Hnodup12 & Hnodup13).
rewrite Hchildrenprev in Hnodup12.
rewrite flat_map_app in Hnodup12.
rewrite in_app_iff in Hnodup12.
apply Classical_Prop.not_or_and in Hnodup12 as 
(Hnodup12 & Hnodup14).
contradict Hnodup12.
rewrite in_flat_map in *.
destruct Hnodup12 as (x0 & Hx0 & Hx00).
exists x0; split;trivial.
 assert(Htrue : 
  getPartitionAux x0 s nbPagesParent = getPartitionAux x0 s' nbPagesParent).
  { unfold consistency in *. 
  apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
 intuition. intuition. intuition. intuition. intuition.

       apply childrenPartitionInPartitionList with currentPart;trivial.
        intuition.
        rewrite Hchildrenprev.
        intuition. 
       apply noCycleInPartitionTree2;trivial.
       intuition. intuition. intuition.
       intuition. intuition. rewrite Hchildrenprev.
        intuition. }

      trivial.
   
rewrite Htrue;trivial.
++  simpl. rewrite in_app_iff.
 apply Classical_Prop.and_not_or.
split;trivial.
**
destruct Hzero as [Hzero | Hzero]; rewrite Hzero in *.
simpl in *.
intuition.
subst x.


    assert (Hicl : incl l11 (getPartitions multiplexer s)).
    { unfold getPartitions.
    rewrite Hsplitlist1.
    intuition.
 }
    assert (Hnotintree : ~ In phyDescChild (getPartitions multiplexer s)).
          { unfold not. intros Hfalse.
            apply HnotConfig in Hfalse.
            contradict Hfalse;left;trivial. left;trivial. }
      contradict Hnotintree.
      unfold incl in Hicl.
      apply Hicl;trivial.
 intuition.
** apply Hnodup10 in Hx. clear Hnodup10.
simpl in *.
apply Classical_Prop.not_or_and in Hx as (Hnodup11 & Hnodup12).

rewrite in_app_iff in Hnodup12.
apply Classical_Prop.not_or_and in Hnodup12 as (Hnodup12 & Hnodup13).
rewrite Hchildrenprev in Hnodup12.
rewrite flat_map_app in Hnodup12.
rewrite in_app_iff in Hnodup12.
apply Classical_Prop.not_or_and in Hnodup12 as 
(Hnodup12 & Hnodup14).
contradict Hnodup14.
rewrite in_flat_map in *.
destruct Hnodup14 as (x0 & Hx0 & Hx00).
exists x0; split;trivial.
 assert(Htrue : 
  getPartitionAux x0 s nbPagesParent = getPartitionAux x0 s' nbPagesParent).
  { unfold consistency in *. 
  apply deuxiemeLemmePoseAvecSam with phyDescChild ptRefChild currentShadow1
        currentPD currentPart;trivial.
 intuition. intuition. intuition. intuition. intuition.

       apply childrenPartitionInPartitionList with currentPart;trivial.
        intuition.
        rewrite Hchildrenprev.
        intuition. 
       apply noCycleInPartitionTree2;trivial.
       intuition. intuition. intuition.
       intuition. intuition. rewrite Hchildrenprev.
        intuition. }

      trivial.
   
rewrite Htrue;trivial.
-- unfold consistency in *.
assert(Hnoduptree : noDupPartitionTree s) by intuition.
unfold noDupPartitionTree in *.
unfold getPartitions in Hnoduptree.
rewrite  Hsplitlist1 in Hnoduptree.
apply NoDupSplitInclIff in Hnoduptree.
destruct Hnoduptree as (_ &Hnodup11).
unfold disjoint in Hnodup11.
 apply Hnodup11 in Hx. clear Hnodup11.
simpl in *.
apply Classical_Prop.not_or_and in Hx as (Hnodup11 & Hnodup12).
rewrite in_app_iff in Hnodup12.
intuition.
Qed. 

Lemma wellFormedFstShadowAddPartition entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s ->
~ In phyDescChild (getChildren  (currentPartition s) s) -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->  
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 -> 
wellFormedFstShadow s'.
Proof.
intros s' HisParent HnotinChildren.
intros. subst.
assert(Hnotderv : wellFormedFstShadow s).
{ unfold consistency in *.
  intuition. }
unfold wellFormedFstShadow in *.
intros parent Hparentpart (* Hnotmult *) va pg pd sh1 Hpd Hsh1 Hmapped.
assert(HmapS : forall pd va1, getMappedPage pd s' va1
 = getMappedPage pd s va1).
 { intros.  apply getMappedPageAddDerivation with entry;trivial. }
rewrite HmapS in *.
assert(HpdS : forall part , StateLib.getPd part (memory s') =
       StateLib.getPd part (memory s)).
  { intros. apply getPdAddDerivation with entry;trivial. }
rewrite HpdS in *.
  assert(Hsh1S : forall part , StateLib.getFstShadow part (memory s') =
       StateLib.getFstShadow part (memory s)).
  { intros. apply getFstShadowAddDerivation with entry;trivial. }
  rewrite Hsh1S in*.
   assert(HgetVirS :  getVirtualAddressSh1 sh1 s' va =  getVirtualAddressSh1 sh1 s va). 
   { unfold getVirtualAddressSh1.
     case_eq(StateLib.getNbLevel);intros;trivial.
     assert(HindS : getIndirection sh1 va l (nbLevel - 1) s' = getIndirection sh1 va l (nbLevel - 1) s).
     { apply getIndirectionAddDerivation with entry;trivial. }
     rewrite HindS.
     destruct (getIndirection sh1 va l (nbLevel - 1) s);trivial.
     destruct (defaultPage =? p);trivial.
     unfold StateLib.readVirEntry.
     simpl. 
     case_eq( beqPairs (ptRefChildFromSh1, StateLib.getIndexOfAddr descChild fstLevel)
      (p, StateLib.getIndexOfAddr va fstLevel) beqPage beqIndex);intros Hpairs;
      simpl.
      + apply beqPairsTrue in Hpairs.
        destruct Hpairs as (Hpairs1 & Hpairs2).
        rewrite <- Hpairs1.
        rewrite <- Hpairs2.
        assert(Hlookup : lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) 
       (memory s) beqPage beqIndex = Some (VE entry)) by trivial.
       rewrite Hlookup;trivial.
      + assert(Hmem : lookup p (StateLib.getIndexOfAddr va fstLevel)
    (removeDup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) 
       (memory s) beqPage beqIndex) beqPage beqIndex = 
       lookup p (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ).
       { apply removeDupIdentity.
        apply beqPairsFalse in Hpairs;trivial.
        intuition. }
      rewrite Hmem;trivial.
    }
    rewrite HgetVirS;trivial.
    
(* apply Hnotderv with parent va pdParent child pdChild vaInChild; trivial. *)
assert(Hcurparteq : (currentPartition s) = parent  \/
                (currentPartition s) <> parent ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  - subst. apply Hnotderv with (currentPartition s) pg pd; trivial.
 - assert(Hneweq : phyDescChild = parent  \/
                phyDescChild <> parent ) by apply pageDecOrNot.
    destruct Hneweq as [Hneweq |Hneweq ].
    * subst parent.  rewrite <- HmapS in *.
       assert(Hmappednull : getMappedPages phyDescChild s' = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        (** we have an hypothesis **)
        rewrite getPdAddDerivation with phyDescChild  (Hardware.va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel)
        s entry true ;trivial.
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial.
        simpl.
        intros.
        rewrite readPhyEntryAddDerivation with (Hardware.va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        rewrite readPresentAddDerivation with (Hardware.va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.  }
        
       unfold incl in *.
       assert(Hfalse : In pg (getMappedPages phyDescChild s' )).
       unfold getMappedPages.
       rewrite HpdS.
       rewrite Hpd.
       unfold getMappedPagesAux.
       rewrite filterOptionInIff.
       unfold getMappedPagesOption.
       apply in_map_iff.
      assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
      StateLib.checkVAddrsEqualityWOOffset nbLevel va va1 ( CLevel (nbLevel -1) ) = true )
      by apply AllVAddrWithOffset0.
      destruct Heqvars as (va1 & Hva1 & Hva11).  
      exists va1.
      split;trivial.
      rewrite <- Hmapped.
      symmetry.
      apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
      apply getNbLevelEqOption.
      
       rewrite Hmappednull in *.
       now contradict Hfalse.
       * assert(In parent (getPartitions multiplexer s)).
      {
       unfold consistency in *. 
      apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial;intuition. }
      apply Hnotderv with parent pg pd;trivial. 
Qed.


Lemma wellFormedFstShadowIfNoneAddPartition entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s ->
~ In phyDescChild (getChildren  (currentPartition s) s) -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->  
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 -> 
wellFormedFstShadowIfNone s'.
Proof.
intros s' HisParent HnotinChildren.
intros. subst.
assert(Hnotderv : wellFormedFstShadowIfNone s).
{ unfold consistency in *.
  intuition. }
unfold wellFormedFstShadowIfNone in *.
intros parent  (* Hnotmult *) va pd sh1 Hparentpart Hpd Hsh1 Hmapped.
assert(HmapS : forall pd va1, getMappedPage pd s' va1
 = getMappedPage pd s va1).
 { intros.  apply getMappedPageAddDerivation with entry;trivial. }
rewrite HmapS in *.
assert(HpdS : forall part , StateLib.getPd part (memory s') =
       StateLib.getPd part (memory s)).
  { intros. apply getPdAddDerivation with entry;trivial. }
rewrite HpdS in *.
  assert(Hsh1S : forall part , StateLib.getFstShadow part (memory s') =
       StateLib.getFstShadow part (memory s)).
  { intros. apply getFstShadowAddDerivation with entry;trivial. }
  rewrite Hsh1S in*. 
assert(Hlevel : Some level = StateLib.getNbLevel) by trivial.
assert(Hcurparteq : (currentPartition s) = parent  \/
                (currentPartition s) <> parent ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  - subst.
    assert(currentPD=pd).
    { apply getPdNextEntryIsPPEq with (currentPartition s) s;trivial. }
    subst pd.
    assert( currentShadow1  =sh1).
    { apply getSh1NextEntryIsPPEq with (currentPartition s) s;trivial. }
    subst sh1.
    assert(Hor : checkVAddrsEqualityWOOffset nbLevel va descChild level = true \/
    checkVAddrsEqualityWOOffset nbLevel va descChild level = false).
    { destruct (checkVAddrsEqualityWOOffset nbLevel va descChild level).
      left;trivial.
      right;trivial. }
    destruct Hor as [Hor | Hor].
    + assert(Htrue : getMappedPage currentPD s descChild = SomePage phyDescChild).
      { apply getMappedPageGetTableRoot with ptRefChild (currentPartition s);trivial. }
      assert(Heqmap :  getMappedPage currentPD s va =  getMappedPage currentPD s descChild).
      { apply getMappedPageEq with level;trivial.
        symmetry;trivial. }
      rewrite Heqmap in *.
      rewrite Htrue in Hmapped.
      now contradict Hmapped. 
    + assert(Hnewgoal :getPDFlag currentShadow1 va s' = getPDFlag currentShadow1 va s /\
getVirtualAddressSh1 currentShadow1 s' va = getVirtualAddressSh1 currentShadow1 s va).
{ (*    rewrite <- Hnotderv with (currentPartition s) va currentPD currentShadow1;
      trivial.
  *)     unfold getPDFlag.
      unfold getVirtualAddressSh1. 
      rewrite <- Hlevel.
      assert(HindS : getIndirection currentShadow1 va level (nbLevel - 1) s' =
       getIndirection currentShadow1 va level (nbLevel - 1) s).
     { apply getIndirectionAddDerivation with entry;trivial. }
     rewrite HindS. clear HindS.
     case_eq (getIndirection currentShadow1 va level (nbLevel - 1) s );intros;split;
     trivial.
     case_eq(p =? defaultPage);intros;trivial.
     
     simpl. 
     assert(p<> ptRefChildFromSh1 \/ (StateLib.getIndexOfAddr va fstLevel) <> 
      (StateLib.getIndexOfAddr descChild fstLevel)).
     { assert(partitionDescriptorEntry s).
        { unfold consistency in *.  intuition. }
       apply pageTablesOrIndicesAreDifferent with currentShadow1 currentShadow1 level 
      nbLevel s;trivial.
      apply sh1PartNotNull with (currentPartition s ) s;trivial.
      apply sh1PartNotNull with (currentPartition s ) s;trivial.
      apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) sh1idx;trivial.
      unfold consistency in *.
      assert(Hnodup : noDupConfigPagesList s ) by intuition.
      apply Hnodup;trivial.
      right;left;trivial.
      apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) sh1idx;trivial.
      unfold consistency in *.
      assert(Hnodup : noDupConfigPagesList s ) by intuition.
      apply Hnodup;trivial.
      right;left;trivial.
      left;split;trivial.
      apply getNbLevelEq;trivial.
      assert(Htmp : (p =? defaultPage) = false) by trivial.
      apply beq_nat_false in Htmp.
      unfold not;intros;subst.
      now contradict Htmp.
      assert(Hdef1 : (defaultPage =? ptRefChildFromSh1) = false) by trivial.
      apply beq_nat_false in Hdef1.
       unfold not;intros;subst.
      now contradict Hdef1.
      assert(Htmp: getIndirection currentShadow1 va level (nbLevel - 1) s = Some p ) by trivial.
      
      apply getIndirectionStopLevelGT with (nbLevel -1);trivial.
      apply getNbLevelLt;symmetry;trivial.
      symmetry;rewrite getNbLevelEq with level;trivial.
      symmetry.
      apply nbLevelEq.
      assert(Htmp: getIndirection currentShadow1 descChild level (nbLevel - 1) s =
       Some ptRefChildFromSh1 ).
     { apply getIndirectionGetTableRoot with (currentPartition s);trivial.
        symmetry;trivial. }
      apply getIndirectionStopLevelGT with (nbLevel -1);trivial.
      apply getNbLevelLt;symmetry;trivial.
      symmetry;rewrite getNbLevelEq with level;trivial.
      symmetry.
      apply nbLevelEq. }
     assert(Hreadeq : StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel)
    (add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
       (VE {| pd := true; va := Hardware.va entry |}) (memory s) beqPage
       beqIndex) =
         StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
    apply readPDflagAddDerivation;trivial.
    rewrite Hreadeq;trivial.
     case_eq(defaultPage =? p);intros;trivial.     
     simpl. 
     assert(p<> ptRefChildFromSh1 \/ (StateLib.getIndexOfAddr va fstLevel) <> 
      (StateLib.getIndexOfAddr descChild fstLevel)).
     { assert(partitionDescriptorEntry s).
        { unfold consistency in *.  intuition. }
       apply pageTablesOrIndicesAreDifferent with currentShadow1 currentShadow1 level 
      nbLevel s;trivial.
      apply sh1PartNotNull with (currentPartition s ) s;trivial.
      apply sh1PartNotNull with (currentPartition s ) s;trivial.
      apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) sh1idx;trivial.
      unfold consistency in *.
      assert(Hnodup : noDupConfigPagesList s ) by intuition.
      apply Hnodup;trivial.
      right;left;trivial.
      apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) sh1idx;trivial.
      unfold consistency in *.
      assert(Hnodup : noDupConfigPagesList s ) by intuition.
      apply Hnodup;trivial.
      right;left;trivial.
      left;split;trivial.
      apply getNbLevelEq;trivial.
      assert(Htmp : (defaultPage =? p) = false) by trivial.
      apply beq_nat_false in Htmp.
      unfold not;intros;subst.
      now contradict Htmp.
      assert(Hdef1 : (defaultPage =? ptRefChildFromSh1) = false) by trivial.
      apply beq_nat_false in Hdef1.
       unfold not;intros;subst.
      now contradict Hdef1.
      assert(Htmp: getIndirection currentShadow1 va level (nbLevel - 1) s = Some p ) by trivial.
      
      apply getIndirectionStopLevelGT with (nbLevel -1);trivial.
      apply getNbLevelLt;symmetry;trivial.
      symmetry;rewrite getNbLevelEq with level;trivial.
      symmetry.
      apply nbLevelEq.
      assert(Htmp: getIndirection currentShadow1 descChild level (nbLevel - 1) s =
       Some ptRefChildFromSh1 ).
     { apply getIndirectionGetTableRoot with (currentPartition s);trivial.
        symmetry;trivial. }
      apply getIndirectionStopLevelGT with (nbLevel -1);trivial.
      apply getNbLevelLt;symmetry;trivial.
      symmetry;rewrite getNbLevelEq with level;trivial.
      symmetry.
      apply nbLevelEq. }
    apply readVirEntryAddDerivation;trivial. }
  destruct Hnewgoal as (Hi1 & Hi2).
  rewrite Hi1.
  rewrite Hi2. 
  apply Hnotderv with  (currentPartition s) currentPD;trivial.
 - assert(Hneweq : phyDescChild = parent  \/
                phyDescChild <> parent ) by apply pageDecOrNot.
    destruct Hneweq as [Hneweq |Hneweq ].
    * subst parent. 
      assert(Hsh1eq : phySh1Child = sh1).
      apply getSh1NextEntryIsPPEq with phyDescChild s;trivial.
      subst sh1. 
      unfold getVirtualAddressSh1.
      unfold getPDFlag.
      unfold getMappedPage in Hmapped.
      rewrite <- Hlevel.
      rewrite <- Hlevel in Hmapped. 
       assert(HindS : getIndirection phySh1Child va level (nbLevel - 1) s' =
       getIndirection phySh1Child va level (nbLevel - 1) s).
     { apply getIndirectionAddDerivation with entry;trivial. }
     rewrite HindS.
     assert(Hwell : isWellFormedFstShadow level phySh1Child s) by trivial.
     unfold isWellFormedFstShadow in Hwell.
     apply getNbLevelEq in Hlevel.
     subst.
split. 
  {
     case_eq (nbLevel - 1);simpl;[intros Hk | intros k Hk];trivial.
     + case_eq( phySh1Child =? defaultPage);intros;trivial.
       destruct Hwell as [(Hfalse & Hwell) | (Htrue & Hwell)].
       { contradict Hfalse. rewrite Hk. unfold fstLevel;trivial. }
       { generalize(Hwell (StateLib.getIndexOfAddr va fstLevel) );clear Hwell;
          intros (Hwell1 & Hwell2).
         assert(Hmykey : phySh1Child <> ptRefChildFromSh1 \/
          StateLib.getIndexOfAddr va fstLevel <>
          StateLib.getIndexOfAddr descChild fstLevel).
          { left.
            assert(Hinconfig :In ptRefChildFromSh1 (getConfigPages (currentPartition s) s)).
            { apply isConfigTableSh1WithVE with descChild;trivial.
              unfold consistency in *;intuition. }
             unfold not;intros Hfalse.
             assert(Hnotconfig : forall partition : page,
                In partition (getPartitions multiplexer s) ->
                ~
                (partition = phySh1Child \/
                 In phySh1Child (getConfigPagesAux partition s))) by trivial.
            unfold not in Hnotconfig.
            apply Hnotconfig with (currentPartition s) ;trivial.
            subst;trivial. } 
         assert(Hreadeq : StateLib.readPDflag phySh1Child (StateLib.getIndexOfAddr va fstLevel)
          (add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
             (VE {| pd := true; va := Hardware.va entry |}) (memory s) beqPage
             beqIndex) =
               StateLib.readPDflag phySh1Child (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
          { apply readPDflagAddDerivation;trivial. }(* 
        assert(Hreadeq1 : StateLib.readVirEntry phySh1Child (StateLib.getIndexOfAddr va fstLevel)
          (add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
             (VE {| pd := true; va := Hardware.va entry |}) (memory s) beqPage
             beqIndex) =
               StateLib.readVirEntry phySh1Child (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
          { apply readVirEntryAddDerivation;trivial. } *)
         rewrite Hreadeq;trivial. clear Hreadeq.
        
         rewrite  Hwell2;trivial.
        }
     
        
       +  simpl in *.
          assert(Htrue :  StateLib.Level.eqb (CLevel (S k)) fstLevel = false). 
          { apply notFstLevel. rewrite <- Hk.
            unfold CLevel.
            case_eq( lt_dec (nbLevel - 1) nbLevel);intros. 
            simpl. omega.
            assert(0 <nbLevel) by apply nbLevelNotZero.
            omega. }
          rewrite Htrue.
     destruct Hwell as [(Hwell &  Hi2) | Hwell].
     { generalize(Hi2  (StateLib.getIndexOfAddr va (CLevel (S k))) );clear Hi2 ;
      intros (Hi1 & Hi2).
      rewrite Hi1.
      assert(Hdef : (defaultPage =? defaultPage) = true).
      symmetry.
      apply beq_nat_refl.
      rewrite Hdef. rewrite Hdef;trivial. }
      apply levelEqBEqNatFalse in Htrue.
      destruct Hwell as (Hwell & Hii).
      rewrite <- Hk in Htrue.
      rewrite Hwell in Htrue.
      omega. }
    {
     case_eq (nbLevel - 1);simpl;[intros Hk | intros k Hk];trivial.
     + assert(Htrue1 : (defaultPage =? phySh1Child) = false) by trivial. 
      rewrite Htrue1.
       destruct Hwell as [(Hfalse & Hwell) | (Htrue & Hwell)].
       { contradict Hfalse. rewrite Hk. unfold fstLevel;trivial. }
       { generalize(Hwell (StateLib.getIndexOfAddr va fstLevel) );clear Hwell;
          intros (Hwell1 & Hwell2).
         assert(Hmykey : phySh1Child <> ptRefChildFromSh1 \/
          StateLib.getIndexOfAddr va fstLevel <>
          StateLib.getIndexOfAddr descChild fstLevel).
          { left.
            assert(Hinconfig :In ptRefChildFromSh1 (getConfigPages (currentPartition s) s)).
            { apply isConfigTableSh1WithVE with descChild;trivial.
              unfold consistency in *;intuition. }
             unfold not;intros Hfalse.
             assert(Hnotconfig : forall partition : page,
                In partition (getPartitions multiplexer s) ->
                ~
                (partition = phySh1Child \/
                 In phySh1Child (getConfigPagesAux partition s))) by trivial.
            unfold not in Hnotconfig.
            apply Hnotconfig with (currentPartition s) ;trivial.
            subst;trivial. } 
          
        assert(Hreadeq1 : StateLib.readVirEntry phySh1Child (StateLib.getIndexOfAddr va fstLevel)
          (add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
             (VE {| pd := true; va := Hardware.va entry |}) (memory s) beqPage
             beqIndex) =
               StateLib.readVirEntry phySh1Child (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
          { apply readVirEntryAddDerivation;trivial. }
         rewrite Hreadeq1;trivial. clear Hreadeq1.
         subst.
         assert(Hmykey1 : forall idx : index,
      StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
      StateLib.readPresent phyPDChild idx (memory s) = Some false) by trivial.
      move Hmapped at bottom.
      rewrite Hk in *.
      simpl in Hmapped.
      assert(pd = phyPDChild).
      apply getPdNextEntryIsPPEq with phyDescChild s';trivial.
      apply nextEntryIsPPgetPd.
      rewrite <- Hpd.
      apply HpdS;trivial.
      assert(Hpsch : nextEntryIsPP phyDescChild PDidx phyPDChild s) by trivial.
      apply nextEntryIsPPgetPd in Hpsch.
            rewrite <- Hpsch.
      apply HpdS;trivial.
      subst pd.
      assert(Hdef : (defaultPage =? phyPDChild) = false) by trivial.
      rewrite Hdef in *.
      destruct Hmykey1 with  (StateLib.getIndexOfAddr va fstLevel)
      as (Hi1 & Hi2);trivial.
      rewrite Hi2 in *.
      now contradict Hmapped. }
         +   simpl in *.
          assert(Htrue :  StateLib.Level.eqb (CLevel (S k)) fstLevel = false). 
          { apply notFstLevel. rewrite <- Hk.
            unfold CLevel.
            case_eq( lt_dec (nbLevel - 1) nbLevel);intros. 
            simpl. omega.
            assert(0 <nbLevel) by apply nbLevelNotZero.
            omega. }
          rewrite Htrue.
     destruct Hwell as [(Hwell &  Hi2) | Hwell].
     { generalize(Hi2  (StateLib.getIndexOfAddr va (CLevel (S k))) );clear Hi2 ;
      intros (Hi1 & Hi2).
      rewrite Hi1.
      assert(Hdef : (defaultPage =? defaultPage) = true).
      symmetry.
      apply beq_nat_refl.
      rewrite Hdef. rewrite Hdef;trivial. }
      apply levelEqBEqNatFalse in Htrue.
      destruct Hwell as (Hwell & Hii).
      rewrite <- Hk in Htrue.
      rewrite Hwell in Htrue.
      omega. }    
    * assert(In parent (getPartitions multiplexer s)).
      {
       unfold consistency in *. 
      apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial;intuition. }
      assert( getPDFlag sh1 va s = false /\ 
      getVirtualAddressSh1 sh1 s va = None) as (Hi1 & Hi2).
      apply Hnotderv with parent pd;trivial.
      rewrite <- Hi1.
      rewrite <- Hi2.
      unfold getVirtualAddressSh1.
       unfold getPDFlag.
      rewrite <- Hlevel.
      assert(HindS : getIndirection sh1 va level (nbLevel - 1) s' =
       getIndirection sh1 va level (nbLevel - 1) s).
     { apply getIndirectionAddDerivation with entry;trivial. }
     rewrite HindS. clear HindS.
     case_eq (getIndirection sh1 va level (nbLevel - 1) s );intros;
     split;trivial.
     +
     case_eq(p =? defaultPage);intros;trivial.
     simpl.
     assert(Hmyconskey : configTablesAreDifferent s).
     { unfold consistency in *. intuition. }
     unfold configTablesAreDifferent in Hmyconskey.
     assert(p <>  ptRefChildFromSh1).
     assert(Hmykey1 : In p (getConfigPages parent s)).
     { unfold getConfigPages.
       simpl;right.
       apply inGetIndirectionsAuxInConfigPagesSh1 with sh1;trivial.
       unfold consistency in *;intuition.
       apply getIndirectionInGetIndirections with va level (nbLevel-1) ;trivial.
       apply nbLevelNotZero.
       assert(Htrue : (p =? defaultPage) = false) by trivial.
       apply beq_nat_false in Htrue;unfold not;intros ;subst;now contradict Htrue.
       apply getNbLevelLe;trivial.
       apply sh1PartNotNull with parent s;trivial.
       apply nextEntryIsPPgetFstShadow;trivial.
       unfold consistency in *;intuition. }
     assert(Hinconfig :In ptRefChildFromSh1 (getConfigPages (currentPartition s) s)).
          { apply isConfigTableSh1WithVE with descChild;trivial.
            unfold consistency in *;intuition. }
    unfold disjoint in Hmyconskey.
    unfold not in Hmyconskey.
    unfold not;intros Hfalse.
    apply Hmyconskey with parent (currentPartition s) ptRefChildFromSh1;
    trivial.
    intuition.
    subst;trivial.
    assert(Hreadeq : StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel)
          (add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
             (VE {| pd := true; va := Hardware.va entry |}) (memory s) beqPage
             beqIndex) =
               StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
          { apply readPDflagAddDerivation;trivial.
            left. trivial. }
    rewrite Hreadeq;trivial.
+
     case_eq(defaultPage =? p);intros;trivial.
     simpl.
     assert(Hmyconskey : configTablesAreDifferent s).
     { unfold consistency in *. intuition. }
     unfold configTablesAreDifferent in Hmyconskey.
     assert(p <>  ptRefChildFromSh1).
     assert(Hmykey1 : In p (getConfigPages parent s)).
     { unfold getConfigPages.
       simpl;right.
       apply inGetIndirectionsAuxInConfigPagesSh1 with sh1;trivial.
       unfold consistency in *;intuition.
       apply getIndirectionInGetIndirections with va level (nbLevel-1) ;trivial.
       apply nbLevelNotZero.
       assert(Htrue : (defaultPage =? p) = false) by trivial.
       apply beq_nat_false in Htrue;unfold not;intros ;subst;now contradict Htrue.
       apply getNbLevelLe;trivial.
       apply sh1PartNotNull with parent s;trivial.
       apply nextEntryIsPPgetFstShadow;trivial.
       unfold consistency in *;intuition. }
     assert(Hinconfig :In ptRefChildFromSh1 (getConfigPages (currentPartition s) s)).
          { apply isConfigTableSh1WithVE with descChild;trivial.
            unfold consistency in *;intuition. }
    unfold disjoint in Hmyconskey.
    unfold not in Hmyconskey.
    unfold not;intros Hfalse.
    apply Hmyconskey with parent (currentPartition s) ptRefChildFromSh1;
    trivial.
    intuition.
    subst;trivial.
    apply readVirEntryAddDerivation;left;trivial.
Qed.

Lemma wellFormedFstShadowIfDefaultAddPartition entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s ->
~ In phyDescChild (getChildren  (currentPartition s) s) -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->  
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 -> 
wellFormedFstShadowIfDefaultValues s'.
Proof.
intros s' HisParent HnotinChildren.
intros. subst.
assert(Hnotderv : wellFormedFstShadowIfDefaultValues s).
{ unfold consistency in *.
  intuition. }
unfold wellFormedFstShadowIfDefaultValues in *.
intros parent  (* Hnotmult *) va pd sh1 Hparentpart Hpd Hsh1 Hmapped.
assert(HmapS : forall pd va1, getMappedPage pd s' va1
 = getMappedPage pd s va1).
 { intros.  apply getMappedPageAddDerivation with entry;trivial. }
rewrite HmapS in *.
assert(HpdS : forall part , StateLib.getPd part (memory s') =
       StateLib.getPd part (memory s)).
  { intros. apply getPdAddDerivation with entry;trivial. }
rewrite HpdS in *.
  assert(Hsh1S : forall part , StateLib.getFstShadow part (memory s') =
       StateLib.getFstShadow part (memory s)).
  { intros. apply getFstShadowAddDerivation with entry;trivial. }
  rewrite Hsh1S in*. 
assert(Hlevel : Some level = StateLib.getNbLevel) by trivial.
assert(Hcurparteq : (currentPartition s) = parent  \/
                (currentPartition s) <> parent ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  - subst.
    assert(currentPD=pd).
    { apply getPdNextEntryIsPPEq with (currentPartition s) s;trivial. }
    subst pd.
    assert( currentShadow1  =sh1).
    { apply getSh1NextEntryIsPPEq with (currentPartition s) s;trivial. }
    subst sh1.
    assert(Hor : checkVAddrsEqualityWOOffset nbLevel va descChild level = true \/
    checkVAddrsEqualityWOOffset nbLevel va descChild level = false).
    { destruct (checkVAddrsEqualityWOOffset nbLevel va descChild level).
      left;trivial.
      right;trivial. }
    destruct Hor as [Hor | Hor].
    + assert(Htrue : getMappedPage currentPD s descChild = SomePage phyDescChild).
      { apply getMappedPageGetTableRoot with ptRefChild (currentPartition s);trivial. }
      assert(Heqmap :  getMappedPage currentPD s va =  getMappedPage currentPD s descChild).
      { apply getMappedPageEq with level;trivial.
        symmetry;trivial. }
      rewrite Heqmap in *.
      rewrite Htrue in Hmapped.
      now contradict Hmapped. 
    + assert(Hnewgoal :getPDFlag currentShadow1 va s' = getPDFlag currentShadow1 va s /\
getVirtualAddressSh1 currentShadow1 s' va = getVirtualAddressSh1 currentShadow1 s va).
{ (*    rewrite <- Hnotderv with (currentPartition s) va currentPD currentShadow1;
      trivial.
  *)     unfold getPDFlag.
      unfold getVirtualAddressSh1. 
      rewrite <- Hlevel.
      assert(HindS : getIndirection currentShadow1 va level (nbLevel - 1) s' =
       getIndirection currentShadow1 va level (nbLevel - 1) s).
     { apply getIndirectionAddDerivation with entry;trivial. }
     rewrite HindS. clear HindS.
     case_eq (getIndirection currentShadow1 va level (nbLevel - 1) s );intros;split;
     trivial.
     case_eq(p =? defaultPage);intros;trivial.
     
     simpl. 
     assert(p<> ptRefChildFromSh1 \/ (StateLib.getIndexOfAddr va fstLevel) <> 
      (StateLib.getIndexOfAddr descChild fstLevel)).
     { assert(partitionDescriptorEntry s).
        { unfold consistency in *.  intuition. }
       apply pageTablesOrIndicesAreDifferent with currentShadow1 currentShadow1 level 
      nbLevel s;trivial.
      apply sh1PartNotNull with (currentPartition s ) s;trivial.
      apply sh1PartNotNull with (currentPartition s ) s;trivial.
      apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) sh1idx;trivial.
      unfold consistency in *.
      assert(Hnodup : noDupConfigPagesList s ) by intuition.
      apply Hnodup;trivial.
      right;left;trivial.
      apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) sh1idx;trivial.
      unfold consistency in *.
      assert(Hnodup : noDupConfigPagesList s ) by intuition.
      apply Hnodup;trivial.
      right;left;trivial.
      left;split;trivial.
      apply getNbLevelEq;trivial.
      assert(Htmp : (p =? defaultPage) = false) by trivial.
      apply beq_nat_false in Htmp.
      unfold not;intros;subst.
      now contradict Htmp.
      assert(Hdef1 : (defaultPage =? ptRefChildFromSh1) = false) by trivial.
      apply beq_nat_false in Hdef1.
       unfold not;intros;subst.
      now contradict Hdef1.
      assert(Htmp: getIndirection currentShadow1 va level (nbLevel - 1) s = Some p ) by trivial.
      
      apply getIndirectionStopLevelGT with (nbLevel -1);trivial.
      apply getNbLevelLt;symmetry;trivial.
      symmetry;rewrite getNbLevelEq with level;trivial.
      symmetry.
      apply nbLevelEq.
      assert(Htmp: getIndirection currentShadow1 descChild level (nbLevel - 1) s =
       Some ptRefChildFromSh1 ).
     { apply getIndirectionGetTableRoot with (currentPartition s);trivial.
        symmetry;trivial. }
      apply getIndirectionStopLevelGT with (nbLevel -1);trivial.
      apply getNbLevelLt;symmetry;trivial.
      symmetry;rewrite getNbLevelEq with level;trivial.
      symmetry.
      apply nbLevelEq. }
     assert(Hreadeq : StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel)
    (add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
       (VE {| pd := true; va := Hardware.va entry |}) (memory s) beqPage
       beqIndex) =
         StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
    apply readPDflagAddDerivation;trivial.
    rewrite Hreadeq;trivial.
     case_eq(defaultPage =? p);intros;trivial.     
     simpl. 
     assert(p<> ptRefChildFromSh1 \/ (StateLib.getIndexOfAddr va fstLevel) <> 
      (StateLib.getIndexOfAddr descChild fstLevel)).
     { assert(partitionDescriptorEntry s).
        { unfold consistency in *.  intuition. }
       apply pageTablesOrIndicesAreDifferent with currentShadow1 currentShadow1 level 
      nbLevel s;trivial.
      apply sh1PartNotNull with (currentPartition s ) s;trivial.
      apply sh1PartNotNull with (currentPartition s ) s;trivial.
      apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) sh1idx;trivial.
      unfold consistency in *.
      assert(Hnodup : noDupConfigPagesList s ) by intuition.
      apply Hnodup;trivial.
      right;left;trivial.
      apply noDupConfigPagesListNoDupGetIndirections with (currentPartition s) sh1idx;trivial.
      unfold consistency in *.
      assert(Hnodup : noDupConfigPagesList s ) by intuition.
      apply Hnodup;trivial.
      right;left;trivial.
      left;split;trivial.
      apply getNbLevelEq;trivial.
      assert(Htmp : (defaultPage =? p) = false) by trivial.
      apply beq_nat_false in Htmp.
      unfold not;intros;subst.
      now contradict Htmp.
      assert(Hdef1 : (defaultPage =? ptRefChildFromSh1) = false) by trivial.
      apply beq_nat_false in Hdef1.
       unfold not;intros;subst.
      now contradict Hdef1.
      assert(Htmp: getIndirection currentShadow1 va level (nbLevel - 1) s = Some p ) by trivial.
      
      apply getIndirectionStopLevelGT with (nbLevel -1);trivial.
      apply getNbLevelLt;symmetry;trivial.
      symmetry;rewrite getNbLevelEq with level;trivial.
      symmetry.
      apply nbLevelEq.
      assert(Htmp: getIndirection currentShadow1 descChild level (nbLevel - 1) s =
       Some ptRefChildFromSh1 ).
     { apply getIndirectionGetTableRoot with (currentPartition s);trivial.
        symmetry;trivial. }
      apply getIndirectionStopLevelGT with (nbLevel -1);trivial.
      apply getNbLevelLt;symmetry;trivial.
      symmetry;rewrite getNbLevelEq with level;trivial.
      symmetry.
      apply nbLevelEq. }
    apply readVirEntryAddDerivation;trivial. }
  destruct Hnewgoal as (Hi1 & Hi2).
  rewrite Hi1.
  rewrite Hi2. 
  apply Hnotderv with  (currentPartition s) currentPD;trivial.
 - assert(Hneweq : phyDescChild = parent  \/
                phyDescChild <> parent ) by apply pageDecOrNot.
    destruct Hneweq as [Hneweq |Hneweq ].
    * subst parent. 
      assert(Hsh1eq : phySh1Child = sh1).
      apply getSh1NextEntryIsPPEq with phyDescChild s;trivial.
      subst sh1. 
      unfold getVirtualAddressSh1.
      unfold getPDFlag.
      unfold getMappedPage in Hmapped.
      rewrite <- Hlevel.
      rewrite <- Hlevel in Hmapped. 
       assert(HindS : getIndirection phySh1Child va level (nbLevel - 1) s' =
       getIndirection phySh1Child va level (nbLevel - 1) s).
     { apply getIndirectionAddDerivation with entry;trivial. }
     rewrite HindS.
     assert(Hwell : isWellFormedFstShadow level phySh1Child s) by trivial.
     unfold isWellFormedFstShadow in Hwell.
     apply getNbLevelEq in Hlevel.
     subst.
split. 
  {
     case_eq (nbLevel - 1);simpl;[intros Hk | intros k Hk];trivial.
     + case_eq( phySh1Child =? defaultPage);intros;trivial.
       destruct Hwell as [(Hfalse & Hwell) | (Htrue & Hwell)].
       { contradict Hfalse. rewrite Hk. unfold fstLevel;trivial. }
       { generalize(Hwell (StateLib.getIndexOfAddr va fstLevel) );clear Hwell;
          intros (Hwell1 & Hwell2).
         assert(Hmykey : phySh1Child <> ptRefChildFromSh1 \/
          StateLib.getIndexOfAddr va fstLevel <>
          StateLib.getIndexOfAddr descChild fstLevel).
          { left.
            assert(Hinconfig :In ptRefChildFromSh1 (getConfigPages (currentPartition s) s)).
            { apply isConfigTableSh1WithVE with descChild;trivial.
              unfold consistency in *;intuition. }
             unfold not;intros Hfalse.
             assert(Hnotconfig : forall partition : page,
                In partition (getPartitions multiplexer s) ->
                ~
                (partition = phySh1Child \/
                 In phySh1Child (getConfigPagesAux partition s))) by trivial.
            unfold not in Hnotconfig.
            apply Hnotconfig with (currentPartition s) ;trivial.
            subst;trivial. } 
         assert(Hreadeq : StateLib.readPDflag phySh1Child (StateLib.getIndexOfAddr va fstLevel)
          (add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
             (VE {| pd := true; va := Hardware.va entry |}) (memory s) beqPage
             beqIndex) =
               StateLib.readPDflag phySh1Child (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
          { apply readPDflagAddDerivation;trivial. }(* 
        assert(Hreadeq1 : StateLib.readVirEntry phySh1Child (StateLib.getIndexOfAddr va fstLevel)
          (add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
             (VE {| pd := true; va := Hardware.va entry |}) (memory s) beqPage
             beqIndex) =
               StateLib.readVirEntry phySh1Child (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
          { apply readVirEntryAddDerivation;trivial. } *)
         rewrite Hreadeq;trivial. clear Hreadeq.
        
         rewrite  Hwell2;trivial.
        }
     
        
       +  simpl in *.
          assert(Htrue :  StateLib.Level.eqb (CLevel (S k)) fstLevel = false). 
          { apply notFstLevel. rewrite <- Hk.
            unfold CLevel.
            case_eq( lt_dec (nbLevel - 1) nbLevel);intros. 
            simpl. omega.
            assert(0 <nbLevel) by apply nbLevelNotZero.
            omega. }
          rewrite Htrue.
     destruct Hwell as [(Hwell &  Hi2) | Hwell].
     { generalize(Hi2  (StateLib.getIndexOfAddr va (CLevel (S k))) );clear Hi2 ;
      intros (Hi1 & Hi2).
      rewrite Hi1.
      assert(Hdef : (defaultPage =? defaultPage) = true).
      symmetry.
      apply beq_nat_refl.
      rewrite Hdef. rewrite Hdef;trivial. }
      apply levelEqBEqNatFalse in Htrue.
      destruct Hwell as (Hwell & Hii).
      rewrite <- Hk in Htrue.
      rewrite Hwell in Htrue.
      omega. }
    {
     case_eq (nbLevel - 1);simpl;[intros Hk | intros k Hk];trivial.
     + assert(Htrue1 : (defaultPage =? phySh1Child) = false) by trivial. 
      rewrite Htrue1.
       destruct Hwell as [(Hfalse & Hwell) | (Htrue & Hwell)].
       { contradict Hfalse. rewrite Hk. unfold fstLevel;trivial. }
       { generalize(Hwell (StateLib.getIndexOfAddr va fstLevel) );clear Hwell;
          intros (Hwell1 & Hwell2).
         assert(Hmykey : phySh1Child <> ptRefChildFromSh1 \/
          StateLib.getIndexOfAddr va fstLevel <>
          StateLib.getIndexOfAddr descChild fstLevel).
          { left.
            assert(Hinconfig :In ptRefChildFromSh1 (getConfigPages (currentPartition s) s)).
            { apply isConfigTableSh1WithVE with descChild;trivial.
              unfold consistency in *;intuition. }
             unfold not;intros Hfalse.
             assert(Hnotconfig : forall partition : page,
                In partition (getPartitions multiplexer s) ->
                ~
                (partition = phySh1Child \/
                 In phySh1Child (getConfigPagesAux partition s))) by trivial.
            unfold not in Hnotconfig.
            apply Hnotconfig with (currentPartition s) ;trivial.
            subst;trivial. } 
          
        assert(Hreadeq1 : StateLib.readVirEntry phySh1Child (StateLib.getIndexOfAddr va fstLevel)
          (add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
             (VE {| pd := true; va := Hardware.va entry |}) (memory s) beqPage
             beqIndex) =
               StateLib.readVirEntry phySh1Child (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
          { apply readVirEntryAddDerivation;trivial. }
         rewrite Hreadeq1;trivial.  }
         +   simpl in *.
          assert(Htrue :  StateLib.Level.eqb (CLevel (S k)) fstLevel = false). 
          { apply notFstLevel. rewrite <- Hk.
            unfold CLevel.
            case_eq( lt_dec (nbLevel - 1) nbLevel);intros. 
            simpl. omega.
            assert(0 <nbLevel) by apply nbLevelNotZero.
            omega. }
          rewrite Htrue.
     destruct Hwell as [(Hwell &  Hi2) | Hwell].
     { generalize(Hi2  (StateLib.getIndexOfAddr va (CLevel (S k))) );clear Hi2 ;
      intros (Hi1 & Hi2).
      rewrite Hi1.

      move Hk at bottom.
      move Hmapped at bottom.
      rewrite Hk in Hmapped. 
      simpl in Hmapped.
      rewrite Htrue in Hmapped.
               assert(Hmykey1 : forall idx : index,
      StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
      StateLib.readPresent phyPDChild idx (memory s) = Some false) by trivial.
      move Hmapped at bottom.
      rewrite Hk in *.
      simpl in Hmapped.
      assert(pd = phyPDChild).
      apply getPdNextEntryIsPPEq with phyDescChild s';trivial.
      apply nextEntryIsPPgetPd.
      rewrite <- Hpd.
      apply HpdS;trivial.
      assert(Hpsch : nextEntryIsPP phyDescChild PDidx phyPDChild s) by trivial.
      apply nextEntryIsPPgetPd in Hpsch.
            rewrite <- Hpsch.
      apply HpdS;trivial.
      subst pd.
      assert(Hdef : (defaultPage =? phyPDChild) = false) by trivial.
      rewrite Hdef in *.
      destruct Hmykey1 with  (StateLib.getIndexOfAddr va (CLevel (S k)))
      as (Hi11 & Hi12);trivial.
      rewrite Hi11 in Hmapped.
        assert(Hdef1 : (defaultPage =? defaultPage) = true).
      symmetry.
      apply beq_nat_refl.
      rewrite Hdef1 in Hmapped.
      rewrite Hdef1 in Hmapped.
      now contradict Hmapped. }
      apply levelEqBEqNatFalse in Htrue.
      destruct Hwell as (Hwell & Hii).
      rewrite <- Hk in Htrue.
      rewrite Hwell in Htrue.
      omega. }    
    * assert(In parent (getPartitions multiplexer s)).
      {
       unfold consistency in *. 
      apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial;intuition. }
      assert( getPDFlag sh1 va s = false /\ 
      getVirtualAddressSh1 sh1 s va = Some defaultVAddr) as (Hi1 & Hi2).
      apply Hnotderv with parent pd;trivial.
      rewrite <- Hi1.
      rewrite <- Hi2.
      unfold getVirtualAddressSh1.
       unfold getPDFlag.
      rewrite <- Hlevel.
      assert(HindS : getIndirection sh1 va level (nbLevel - 1) s' =
       getIndirection sh1 va level (nbLevel - 1) s).
     { apply getIndirectionAddDerivation with entry;trivial. }
     rewrite HindS. clear HindS.
     case_eq (getIndirection sh1 va level (nbLevel - 1) s );intros;
     split;trivial.
     +
     case_eq(p =? defaultPage);intros;trivial.
     simpl.
     assert(Hmyconskey : configTablesAreDifferent s).
     { unfold consistency in *. intuition. }
     unfold configTablesAreDifferent in Hmyconskey.
     assert(p <>  ptRefChildFromSh1).
     assert(Hmykey1 : In p (getConfigPages parent s)).
     { unfold getConfigPages.
       simpl;right.
       apply inGetIndirectionsAuxInConfigPagesSh1 with sh1;trivial.
       unfold consistency in *;intuition.
       apply getIndirectionInGetIndirections with va level (nbLevel-1) ;trivial.
       apply nbLevelNotZero.
       assert(Htrue : (p =? defaultPage) = false) by trivial.
       apply beq_nat_false in Htrue;unfold not;intros ;subst;now contradict Htrue.
       apply getNbLevelLe;trivial.
       apply sh1PartNotNull with parent s;trivial.
       apply nextEntryIsPPgetFstShadow;trivial.
       unfold consistency in *;intuition. }
     assert(Hinconfig :In ptRefChildFromSh1 (getConfigPages (currentPartition s) s)).
          { apply isConfigTableSh1WithVE with descChild;trivial.
            unfold consistency in *;intuition. }
    unfold disjoint in Hmyconskey.
    unfold not in Hmyconskey.
    unfold not;intros Hfalse.
    apply Hmyconskey with parent (currentPartition s) ptRefChildFromSh1;
    trivial.
    intuition.
    subst;trivial.
    assert(Hreadeq : StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel)
          (add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
             (VE {| pd := true; va := Hardware.va entry |}) (memory s) beqPage
             beqIndex) =
               StateLib.readPDflag p (StateLib.getIndexOfAddr va fstLevel) (memory s)). 
          { apply readPDflagAddDerivation;trivial.
            left. trivial. }
    rewrite Hreadeq;trivial.
+
     case_eq(defaultPage =? p);intros;trivial.
     simpl.
     assert(Hmyconskey : configTablesAreDifferent s).
     { unfold consistency in *. intuition. }
     unfold configTablesAreDifferent in Hmyconskey.
     assert(p <>  ptRefChildFromSh1).
     assert(Hmykey1 : In p (getConfigPages parent s)).
     { unfold getConfigPages.
       simpl;right.
       apply inGetIndirectionsAuxInConfigPagesSh1 with sh1;trivial.
       unfold consistency in *;intuition.
       apply getIndirectionInGetIndirections with va level (nbLevel-1) ;trivial.
       apply nbLevelNotZero.
       assert(Htrue : (defaultPage =? p) = false) by trivial.
       apply beq_nat_false in Htrue;unfold not;intros ;subst;now contradict Htrue.
       apply getNbLevelLe;trivial.
       apply sh1PartNotNull with parent s;trivial.
       apply nextEntryIsPPgetFstShadow;trivial.
       unfold consistency in *;intuition. }
     assert(Hinconfig :In ptRefChildFromSh1 (getConfigPages (currentPartition s) s)).
          { apply isConfigTableSh1WithVE with descChild;trivial.
            unfold consistency in *;intuition. }
    unfold disjoint in Hmyconskey.
    unfold not in Hmyconskey.
    unfold not;intros Hfalse.
    apply Hmyconskey with parent (currentPartition s) ptRefChildFromSh1;
    trivial.
    intuition.
    subst;trivial.
    apply readVirEntryAddDerivation;left;trivial.
Qed.

Lemma wellFormedSndShadowAddPartition entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s ->
~ In phyDescChild (getChildren  (currentPartition s) s) -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->  
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 -> 
wellFormedSndShadow s'.
Proof.
intros s' HisParent HnotinChildren.
intros. subst.
assert(Hnotderv : wellFormedSndShadow s).
{ unfold consistency in *.
  intuition. }
unfold wellFormedSndShadow in *.
intros parent Hparentpart Hnotmult va pg pd sh1 Hpd Hsh1 Hmapped.
assert(HmapS : forall pd va1, getMappedPage pd s' va1
 = getMappedPage pd s va1).
 { intros.  apply getMappedPageAddDerivation with entry;trivial. }
rewrite HmapS in *.
assert(HpdS : forall part , StateLib.getPd part (memory s') =
       StateLib.getPd part (memory s)).
  { intros. apply getPdAddDerivation with entry;trivial. }
rewrite HpdS in *.
  assert(Hsh1S : forall part , StateLib.getSndShadow part (memory s') =
       StateLib.getSndShadow part (memory s)).
  { intros. apply getSndShadowAddDerivation with entry;trivial. }
  rewrite Hsh1S in*.
   assert(HgetVirS :  getVirtualAddressSh2 sh1 s' va =  getVirtualAddressSh2 sh1 s va). 
   { unfold getVirtualAddressSh2.
     case_eq(StateLib.getNbLevel);intros;trivial.
     assert(HindS : getIndirection sh1 va l (nbLevel - 1) s' = getIndirection sh1 va l (nbLevel - 1) s).
     { apply getIndirectionAddDerivation with entry;trivial. }
     rewrite HindS.
     destruct (getIndirection sh1 va l (nbLevel - 1) s);trivial.
     destruct (defaultPage =? p);trivial.
     unfold StateLib.readVirtual.
     simpl. 
     case_eq( beqPairs (ptRefChildFromSh1, StateLib.getIndexOfAddr descChild fstLevel)
      (p, StateLib.getIndexOfAddr va fstLevel) beqPage beqIndex);intros Hpairs;
      simpl.
      + apply beqPairsTrue in Hpairs.
        destruct Hpairs as (Hpairs1 & Hpairs2).
        rewrite <- Hpairs1.
        rewrite <- Hpairs2.
        assert(Hlookup : lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) 
       (memory s) beqPage beqIndex = Some (VE entry)) by trivial.
       rewrite Hlookup;trivial.
      + assert(Hmem : lookup p (StateLib.getIndexOfAddr va fstLevel)
    (removeDup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) 
       (memory s) beqPage beqIndex) beqPage beqIndex = 
       lookup p (StateLib.getIndexOfAddr va fstLevel) (memory s) beqPage beqIndex ).
       { apply removeDupIdentity.
        apply beqPairsFalse in Hpairs;trivial.
        intuition. }
      rewrite Hmem;trivial.
    }
    rewrite HgetVirS;trivial.
    
(* apply Hnotderv with parent va pdParent child pdChild vaInChild; trivial. *)
assert(Hcurparteq : (currentPartition s) = parent  \/
                (currentPartition s) <> parent ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  - subst. apply Hnotderv with (currentPartition s) pg pd; trivial.
 - assert(Hneweq : phyDescChild = parent  \/
                phyDescChild <> parent ) by apply pageDecOrNot.
    destruct Hneweq as [Hneweq |Hneweq ].
    * subst parent.  rewrite <- HmapS in *.
       assert(Hmappednull : getMappedPages phyDescChild s' = nil).
      { unfold getMappedPages.
        unfold s'.
        simpl.
        (** we have an hypothesis **)
        rewrite getPdAddDerivation with phyDescChild  (Hardware.va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel)
        s entry true ;trivial.
        assert(Hpdnewchild :StateLib.getPd phyDescChild (memory s) = Some phyPDChild).
        apply nextEntryIsPPgetPd;trivial.
        rewrite Hpdnewchild.
        unfold getMappedPagesAux.
        apply  getMappedPagesOptionNil ;trivial.
        simpl.
        intros.
        rewrite readPhyEntryAddDerivation with (Hardware.va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.
        rewrite readPresentAddDerivation with (Hardware.va entry) ptRefChildFromSh1
        (StateLib.getIndexOfAddr descChild fstLevel) s  phyPDChild idx entry true;trivial.  }
        
       unfold incl in *.
       assert(Hfalse : In pg (getMappedPages phyDescChild s' )).
       unfold getMappedPages.
       rewrite HpdS.
       rewrite Hpd.
       unfold getMappedPagesAux.
       rewrite filterOptionInIff.
       unfold getMappedPagesOption.
       apply in_map_iff.
       assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
StateLib.checkVAddrsEqualityWOOffset nbLevel va va1 ( CLevel (nbLevel -1) ) = true )
by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
exists va1. split;trivial.
rewrite <- Hmapped.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
apply getNbLevelEqOption.
       rewrite Hmappednull in *.
       now contradict Hfalse.
       * assert(In parent (getPartitions multiplexer s)).
      {
       unfold consistency in *. 
      apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial;intuition. }
      apply Hnotderv with parent pg pd;trivial. 
Qed.

Lemma wellFormedShadowsFstAddPartition entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s ->
~ In phyDescChild (getChildren  (currentPartition s) s) -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->  
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 -> 
wellFormedShadows sh1idx s'.
Proof.
intros s' HisParent HnotinChildren.
intros. subst.
assert(Hnotderv : wellFormedShadows sh1idx s).
{ unfold consistency in *.
  intuition. }
unfold wellFormedShadows in *.
intros parent Hparent pdroot Hpdroot structroot Hstructroot 
nbL stop HnbL indirection1    va Hind1 Hdef1 .

assert(HmapS : forall structroot va nbL stop , getIndirection structroot va nbL stop s' 
= getIndirection structroot va nbL stop s ).
 { intros.  apply getIndirectionAddDerivation with entry;trivial. }
rewrite HmapS in *.
assert(HpdS : forall part , StateLib.getPd part (memory s') =
       StateLib.getPd part (memory s)).
  { intros. apply getPdAddDerivation with entry;trivial. }
rewrite HpdS in *.
  assert(Hsh1S : forall part , StateLib.getFstShadow part (memory s') =
       StateLib.getFstShadow part (memory s)).
  { intros. apply getFstShadowAddDerivation with entry;trivial. }
rewrite nextEntryIsPPgetFstShadow in *. 
  rewrite  Hsh1S in*.
    
(* apply Hnotderv with parent va pdParent child pdChild vaInChild; trivial. *)
assert(Hcurparteq : (currentPartition s) = parent  \/
                (currentPartition s) <> parent ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  - subst.  apply Hnotderv  with (currentPartition s) pdroot indirection1; trivial.
    rewrite nextEntryIsPPgetFstShadow;trivial.
 - assert(Hneweq : phyDescChild = parent  \/
                phyDescChild <> parent ) by apply pageDecOrNot.
    destruct Hneweq as [Hneweq |Hneweq ].
    * subst parent. 
      assert(Heq : structroot = phySh1Child).
  { 
    symmetry.
    apply getSh1NextEntryIsPPEq with phyDescChild s;trivial.
    rewrite <- nextEntryIsPPgetFstShadow in *;trivial. }
  subst.
  assert(Hlevel : Some level = StateLib.getNbLevel) by trivial.
   rewrite <- HnbL in *.
   inversion Hlevel; subst level.
   assert(Hwell :isWellFormedFstShadow nbL phySh1Child s) by trivial.
   assert(Hwellpd : forall idx : index,
      StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
      StateLib.readPresent phyPDChild idx (memory s) = Some false) by trivial.
      assert(Heq : pdroot = phyPDChild).
  { 
    symmetry.
    apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
   subst pdroot. 
   assert(Hnotnull : (defaultPage =? phySh1Child) = false) by trivial.
   revert  HnbL Hind1 Hwell Hdef1 Hwellpd  Hparent  Hpdroot  Hstructroot 
        Hdef1 Hnotnull  .
   clear.
   revert phyPDChild phySh1Child nbL indirection1 va stop .
   induction stop.
   intros. 
   + simpl in *.
    exists phySh1Child; split;trivial.
   + intros.
     simpl in Hind1.
     simpl.
     case_eq (StateLib.Level.eqb nbL fstLevel);intros Hleveleq;
     rewrite Hleveleq in *.
     ++  exists phySh1Child; split;trivial.
     ++  destruct Hwellpd with ( (StateLib.getIndexOfAddr va nbL) ) as
     (Hwell1 & Hwell2). 
     rewrite Hwell1 in *.
     assert((defaultPage =? defaultPage) = true).
     rewrite <- beq_nat_refl;trivial.
     rewrite H in Hind1.
      inversion Hind1.
      subst. 
       
     
      apply beq_nat_false in Hdef1.
      now contradict Hdef1.
      *
     assert(In parent (getPartitions multiplexer s)).
      {
       unfold consistency in *. 
      apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial;intuition. 
      rewrite nextEntryIsPPgetFstShadow;trivial.
      rewrite nextEntryIsPPgetFstShadow;trivial. }
      apply Hnotderv with parent  pdroot indirection1;trivial.
      rewrite  nextEntryIsPPgetFstShadow;trivial.
Qed.

Lemma wellFormedShadowsSh2AddPartition entry s descChild ptRefChildFromSh1 currentPart
phyDescChild level currentPD   phyPDChild phySh1Child phySh2Child
phyConfigPagesList ptRefChild currentShadow1 idxPPR idxSH3 idxSH2 idxSH1 idxPD idxPR nullv:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va entry |}) (memory s) beqPage beqIndex |} in 
isParent s ->
~ In phyDescChild (getChildren  (currentPartition s) s) -> 
consistency s -> 
partitionsIsolation s -> 
verticalSharing s -> 
lookup ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
(memory s) beqPage beqIndex = Some (VE entry) ->
nextEntryIsPP phyDescChild sh3idx phyConfigPagesList s ->
nextEntryIsPP phyDescChild sh2idx phySh2Child s ->
nextEntryIsPP phyDescChild sh1idx phySh1Child s ->
nextEntryIsPP phyDescChild PDidx phyPDChild s ->
In currentPart (getPartitions multiplexer s ) ->
Some level = StateLib.getNbLevel ->
nextEntryIsPP currentPart PDidx currentPD s ->
In phyDescChild
          (getChildren currentPart
             s') ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1))
(memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx ->
StateLib.readVirtual phyConfigPagesList idx (memory s) =
Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx ->
exists idxValue : index,
StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->  *)
initConfigPagesListPostCondition phyConfigPagesList s ->  
In phyDescChild (getMappedPages currentPart s) ->
In phyPDChild (getMappedPages currentPart s) ->
In phySh1Child (getMappedPages currentPart s) ->
In phySh2Child (getMappedPages currentPart s) ->
In phyConfigPagesList (getMappedPages currentPart s) ->
(forall partition : page,
 In partition (getPartitions multiplexer s) ->
 ~ (partition = phyDescChild \/
 In phyDescChild (getConfigPagesAux partition s))) ->
( forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
isEntryPage ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) phyDescChild s ->
entryPresentFlag ptRefChild (StateLib.getIndexOfAddr descChild fstLevel) true s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
isPartitionFalse ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel) s ->
(forall idx : index,
       StateLib.getIndexOfAddr descChild fstLevel = idx ->
       isVE ptRefChildFromSh1 idx s /\
       getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s)
      ->
(defaultPage =? ptRefChildFromSh1) = false ->
(forall idx : index,
 StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
 StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
 idx <> CIndex (tableSize - 1) ->
 Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
 Nat.Even idx ->
 exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *) initConfigPagesListPostCondition phyConfigPagesList s ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyDescChild \/
In phyDescChild (getConfigPagesAux partition s))) ->  
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyPDChild \/
In phyPDChild (getConfigPagesAux partition s))) ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh1Child \/
In phySh1Child (getConfigPagesAux partition s))) ->

(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phySh2Child \/
In phySh2Child (getConfigPagesAux partition s)))->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~
(partition = phyConfigPagesList \/
In phyConfigPagesList (getConfigPagesAux partition s)))   ->  
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->   
currentPart = currentPartition s -> 
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(defaultPage =? phyPDChild) = false -> 
(defaultPage =? phySh1Child) = false ->
(defaultPage =? phySh2Child) = false ->
(defaultPage =? phyConfigPagesList) = false -> 
(defaultPage =? phyDescChild) = false ->
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx -> 
In descChild getAllVAddrWithOffset0 -> 
wellFormedShadows sh2idx s'.
Proof.
intros s' HisParent HnotinChildren.
intros. subst.
assert(Hnotderv : wellFormedShadows sh2idx s).
{ unfold consistency in *.
  intuition. }
unfold wellFormedShadows in *.
intros parent Hparent pdroot Hpdroot structroot Hstructroot 
nbL stop HnbL indirection1    va Hind1 Hdef1 .

assert(HmapS : forall structroot va nbL stop , getIndirection structroot va nbL stop s' 
= getIndirection structroot va nbL stop s ).
 { intros.  apply getIndirectionAddDerivation with entry;trivial. }
rewrite HmapS in *.
assert(HpdS : forall part , StateLib.getPd part (memory s') =
       StateLib.getPd part (memory s)).
  { intros. apply getPdAddDerivation with entry;trivial. }
rewrite HpdS in *.
  assert(Hsh1S : forall part , StateLib.getSndShadow part (memory s') =
       StateLib.getSndShadow part (memory s)).
  { intros. apply getSndShadowAddDerivation with entry;trivial. }
rewrite nextEntryIsPPgetSndShadow in *. 
  rewrite  Hsh1S in*.
    
(* apply Hnotderv with parent va pdParent child pdChild vaInChild; trivial. *)
assert(Hcurparteq : (currentPartition s) = parent  \/
                (currentPartition s) <> parent ) by apply pageDecOrNot.
  destruct Hcurparteq as [Hcurparteq |Hcurparteq ].
  - subst.  apply Hnotderv  with (currentPartition s) pdroot indirection1; trivial.
    rewrite nextEntryIsPPgetSndShadow;trivial.
 - assert(Hneweq : phyDescChild = parent  \/
                phyDescChild <> parent ) by apply pageDecOrNot.
    destruct Hneweq as [Hneweq |Hneweq ].
    * subst parent. 
      assert(Heq : structroot = phySh2Child).
  { 
    symmetry.
    apply getSh2NextEntryIsPPEq with phyDescChild s;trivial.
    rewrite <- nextEntryIsPPgetSndShadow in *;trivial. }
  subst.
  assert(Hlevel : Some level = StateLib.getNbLevel) by trivial.
   rewrite <- HnbL in *.
   inversion Hlevel; subst level.
   assert(Hwell :isWellFormedSndShadow nbL phySh2Child s) by trivial.
   assert(Hwellpd : forall idx : index,
      StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
      StateLib.readPresent phyPDChild idx (memory s) = Some false) by trivial.
      assert(Heq : pdroot = phyPDChild).
  { 
    symmetry.
    apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
   subst pdroot. 
   assert(Hnotnull : (defaultPage =? phySh2Child) = false) by trivial.
   revert  HnbL Hind1 Hwell Hdef1 Hwellpd  Hparent  Hpdroot  Hstructroot 
        Hdef1 Hnotnull  .
   clear.
   revert phyPDChild phySh2Child nbL indirection1 va stop .
   induction stop.
   intros. 
   + simpl in *.
    exists phySh2Child; split;trivial.
   + intros.
     simpl in Hind1.
     simpl.
     case_eq (StateLib.Level.eqb nbL fstLevel);intros Hleveleq;
     rewrite Hleveleq in *.
     ++  exists phySh2Child; split;trivial.
     ++  destruct Hwellpd with ( (StateLib.getIndexOfAddr va nbL) ) as
     (Hwell1 & Hwell2). 
     rewrite Hwell1 in *.
     assert((defaultPage =? defaultPage) = true).
     rewrite <- beq_nat_refl;trivial.
     rewrite H in Hind1.
      inversion Hind1.
      subst. 
       
     
      apply beq_nat_false in Hdef1.
      now contradict Hdef1.
      *
     assert(In parent (getPartitions multiplexer s)).
      {
       unfold consistency in *. 
      apply addPartitionAddsSinglePartition with entry descChild ptRefChildFromSh1
      (currentPartition s) phyDescChild level currentPD phyPDChild phySh1Child phySh2Child
      phyConfigPagesList ptRefChild currentShadow1;trivial;intuition. 
      rewrite nextEntryIsPPgetSndShadow;trivial. }
      apply Hnotderv with parent  pdroot indirection1;trivial.
      rewrite  nextEntryIsPPgetSndShadow;trivial.
Qed.

Lemma consistencyAddChild  v0   zero nullv idxPR idxPD idxSH1 idxSH2
idxSH3 idxPPR
pdChild currentPart currentPD level ptRefChild descChild idxRefChild
 ptPDChild idxPDChild   ptSh1Child shadow1 idxSh1
  ptSh2Child shadow2 idxSh2   ptConfigPagesList
idxConfigPagesList 
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 
ptSh1ChildFromSh1  childSh2
 childListSh1  list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s:
let s' :=  
{| currentPartition := currentPartition s;
   memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va v0 |}) (memory s) beqPage beqIndex |} in 
~ In phyDescChild (getChildren  (currentPartition s) s) -> 
partitionsIsolation s ->
kernelDataIsolation s ->
verticalSharing s ->
consistency s ->
Some level = StateLib.getNbLevel ->
false = checkVAddrsEqualityWOOffset nbLevel descChild pdChild level ->
false = checkVAddrsEqualityWOOffset nbLevel descChild shadow1 level ->
false = checkVAddrsEqualityWOOffset nbLevel descChild shadow2 level ->
false = checkVAddrsEqualityWOOffset nbLevel descChild list level ->
false = checkVAddrsEqualityWOOffset nbLevel pdChild shadow1 level ->
false = checkVAddrsEqualityWOOffset nbLevel pdChild shadow2 level ->
false = checkVAddrsEqualityWOOffset nbLevel pdChild list level ->
false = checkVAddrsEqualityWOOffset nbLevel shadow1 shadow2 level ->
false = checkVAddrsEqualityWOOffset nbLevel shadow1 list level ->
false = checkVAddrsEqualityWOOffset nbLevel shadow2 list level ->
(Kidx =? nth (length descChild - (nbLevel - 1 + 2)) descChild defaultIndex) = false ->
(Kidx =? nth (length pdChild - (nbLevel - 1 + 2)) pdChild defaultIndex) = false ->
(Kidx =? nth (length shadow1 - (nbLevel - 1 + 2)) shadow1 defaultIndex) = false ->
(Kidx =? nth (length shadow2 - (nbLevel - 1 + 2)) shadow2 defaultIndex) = false ->
(Kidx =? nth (length list - (nbLevel - 1 + 2)) list defaultIndex) = false ->
currentPart = currentPartition s ->
nextEntryIsPP currentPart PDidx currentPD s ->
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) ->
(defaultPage =? ptRefChild) = false ->
StateLib.getIndexOfAddr descChild fstLevel = idxRefChild ->
entryPresentFlag ptRefChild idxRefChild true s ->
entryUserFlag ptRefChild idxRefChild false s ->
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) ->
(defaultPage =? ptPDChild) = false ->
StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild ->
entryPresentFlag ptPDChild idxPDChild true s ->
entryUserFlag ptPDChild idxPDChild false s ->
(forall idx : index,
StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) ->
(defaultPage =? ptSh1Child) = false ->
StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1 ->
entryPresentFlag ptSh1Child idxSh1 true s ->
entryUserFlag ptSh1Child idxSh1 false s ->
(forall idx : index,
StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) ->
(defaultPage =? ptSh2Child) = false ->
StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2 ->
entryPresentFlag ptSh2Child idxSh2 true s ->
entryUserFlag ptSh2Child idxSh2 false s ->
(forall idx : index,
StateLib.getIndexOfAddr list fstLevel = idx ->
isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s) ->
(defaultPage =? ptConfigPagesList) = false ->
StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList ->
entryPresentFlag ptConfigPagesList idxConfigPagesList true s ->
entryUserFlag ptConfigPagesList idxConfigPagesList false s ->
nextEntryIsPP currentPart sh1idx currentShadow1 s ->
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isVE ptRefChildFromSh1 idx s /\ getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) ->
(defaultPage =? ptRefChildFromSh1) = false ->
(exists va : vaddr, isEntryVA ptRefChildFromSh1 idxRefChild va s /\ beqVAddr defaultVAddr va = derivedRefChild) ->
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isVE ptPDChildSh1 idx s /\ getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) ->
(defaultPage =? ptPDChildSh1) = false ->
(forall idx : index,
StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
isVE ptSh1ChildFromSh1 idx s /\ getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) ->
(defaultPage =? ptSh1ChildFromSh1) = false ->
(forall idx : index,
StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) ->
(defaultPage =? childSh2) = false ->
(forall idx : index,
StateLib.getIndexOfAddr list fstLevel = idx ->
isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 sh1idx currentPart list s) ->
(defaultPage =? childListSh1) = false ->
isEntryPage ptPDChild idxPDChild phyPDChild s ->
(defaultPage =? phyPDChild) = false ->
(forall partition : page,
In partition (getPartitions multiplexer s) -> ~ (partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s))) ->
isEntryPage ptSh1Child idxSh1 phySh1Child s ->
(defaultPage =? phySh1Child) = false ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s))) ->
isEntryPage ptSh2Child idxSh2 phySh2Child s ->
(defaultPage =? phySh2Child) = false ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s))) ->
isEntryPage ptConfigPagesList idxConfigPagesList phyConfigPagesList s ->
(defaultPage =? phyConfigPagesList) = false ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s))) ->
isEntryPage ptRefChild idxRefChild phyDescChild s ->
(defaultPage =? phyDescChild) = false ->
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s))) ->
isPartitionFalse ptSh1ChildFromSh1 idxSh1 s ->
isPartitionFalse childSh2 idxSh2 s ->
isPartitionFalse childListSh1 idxConfigPagesList s ->
isPartitionFalse ptRefChildFromSh1 idxRefChild s ->
isPartitionFalse ptPDChildSh1 idxPDChild s ->
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyPDChild (getAccessibleMappedPages partition s)) ->
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phySh1Child (getAccessibleMappedPages partition s)) ->
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phySh2Child (getAccessibleMappedPages partition s)) ->
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyConfigPagesList (getAccessibleMappedPages partition s)) ->
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyDescChild (getAccessibleMappedPages partition s)) ->       
zero = CIndex 0 ->
isWellFormedSndShadow level phySh2Child s ->
isWellFormedFstShadow level phySh1Child s ->
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) ->
(* StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage ->
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) ->
(forall idx : index,
Nat.Even idx -> exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) ->
 *)
initConfigPagesListPostCondition phyConfigPagesList s ->  
nullv = defaultVAddr ->
idxPR = PRidx ->
idxPD = PDidx ->
idxSH1 = sh1idx ->
idxSH2 = sh2idx ->
idxSH3 = sh3idx ->
idxPPR = PPRidx ->
isVA phyDescChild idxPPR s ->
nextEntryIsPP phyDescChild idxPPR currentPart s ->
isVA phyDescChild idxSH3 s ->
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s ->
isVA phyDescChild idxSH2 s ->
nextEntryIsPP phyDescChild idxSH2 phySh2Child s ->
isVA phyDescChild idxSH1 s ->
nextEntryIsPP phyDescChild idxSH1 phySh1Child s ->
isVA phyDescChild idxPD s ->
nextEntryIsPP phyDescChild idxPD phyPDChild s ->
isVA phyDescChild idxPR s ->
nextEntryIsPP phyDescChild idxPR phyDescChild s ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) ->
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) ->
(* isEntryVA ptPDChildSh1 idxPDChild descChild s ->
isEntryVA ptSh1ChildFromSh1 idxSh1 descChild s -> isEntryVA childSh2 idxSh2 descChild s ->
(* isEntryVA childListSh1 idxConfigPagesList descChild s -> *) *)
lookup ptRefChildFromSh1 idxRefChild (memory s) beqPage beqIndex =
Some (VE v0)  -> 
In phyDescChild
  (getChildren (currentPartition s)
     {|
     currentPartition := currentPartition s;
     memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
                 (VE {| pd := true; va := va v0 |}) (memory s) beqPage beqIndex |})
                 -> 
In phyDescChild (getMappedPages (currentPartition s) s) ->
In phyPDChild (getMappedPages (currentPartition s) s)->
In phySh1Child (getMappedPages (currentPartition s) s)->
In phySh2Child (getMappedPages (currentPartition s) s)->
In phyConfigPagesList (getMappedPages (currentPartition s) s) ->
getMappedPage currentPD s pdChild = SomePage phyPDChild -> 
getMappedPage currentPD s shadow1 = SomePage phySh1Child -> 
getMappedPage currentPD s shadow2 = SomePage phySh2Child -> 
getMappedPage currentPD s list = SomePage phyConfigPagesList -> 
getMappedPage currentPD s descChild = SomePage phyDescChild -> 
In descChild getAllVAddrWithOffset0 -> 
consistency {|
  currentPartition := currentPartition s;
  memory := add ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
              (VE {| pd := true; va := va v0 |}) (memory s) beqPage beqIndex |}.
Proof.
intros s' Hnotinchildren.
unfold consistency in *.
intros.
intuition.
+ subst. apply partitionDescriptorEntryAddPartition with  (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst.  apply dataStructurePdAsRootAddPartition  with  (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst.  apply dataStructureSh1AsRootAddPartition  with  (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst.  apply dataStructureSh2AsRootAddPartition  with  (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst. apply currentPartitionInPartitionsListAddPartition (* with entry; *); intuition.
+ subst.  apply noDupMappedPagesListAddPartition with  (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst.   apply noDupConfigPagesListAddPartition with  (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr shadow2 shadow1 pdChild list ;trivial.
  unfold consistency;intuition.
+ subst.  apply parentInPartitionListAddPartition with  (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst.  apply accessibleVAIsNotPartitionDescriptorAddPartition  with  (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst.  apply accessibleChildPageIsAccessibleIntoParentAddPartition with  
(currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst.  apply noCycleInPartitionTreeAddPartition with (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst.  apply configTablesAreDifferentAddPartition  with (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst.  apply isChildAddPartition (* with entry  *) with (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst.  apply isPresentNotDefaultIffAddPartition ;intuition.
+ subst. apply physicalPageNotDerivedAddPartition with (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition. 
 + subst.  apply multiplexerWithoutParentAddPartition;trivial.
 +  subst.  apply isParentAddPartition with (currentPartition s) phyDescChild level currentPD
phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild currentShadow1;trivial.
unfold consistency in *. intuition.
 +   apply noDupPartitionTreeAddChild  with   (currentPartition s) phyDescChild level
currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
currentShadow1 idxConfigPagesList ptConfigPagesList idxSh2 ptSh2Child shadow2
idxSh1 ptSh1Child shadow1 idxPDChild ptPDChild pdChild idxRefChild list; subst;intuition.
unfold consistency in *;intuition.
+ subst. apply  wellFormedFstShadowAddPartition with (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition. 
+ subst. apply wellFormedSndShadowAddPartition with (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst. apply wellFormedShadowsFstAddPartition with (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition. 
+ subst. apply wellFormedShadowsSh2AddPartition with (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst. apply  wellFormedFstShadowIfNoneAddPartition with (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
+ subst. apply  wellFormedFstShadowIfDefaultAddPartition with (currentPartition s) phyDescChild
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1
  PPRidx sh3idx sh2idx sh1idx PDidx PRidx defaultVAddr ;trivial.
  unfold consistency;intuition.
Qed.

 Lemma getTableAddrRootEqOffset descChild va1 part table s idxroot:
(idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx) -> 
checkVAddrsEqualityWOOffset nbLevel descChild va1
          (CLevel (nbLevel - 1)) = true -> 
 getTableAddrRoot table idxroot part descChild s -> 
 getTableAddrRoot table idxroot part va1 s.
 Proof.
 intros. 
 unfold getTableAddrRoot in *.
 destruct H1;split;trivial.
 intros.
 apply H2 in H3.
 destruct H3 as (nbL & Hnbl & stop & Hstop & Hind).
 exists nbL;split;trivial.
 exists stop;split;trivial.
 rewrite <- Hind.
 symmetry.
 apply getIndirectionEq.
 apply getNbLevelLt;symmetry;trivial.
 rewrite <- H0.
 f_equal.
assert(StateLib.getNbLevel = Some (CLevel (nbLevel - 1))). 
apply getNbLevelEqOption.
rewrite  H3 in *.
inversion Hnbl;trivial.
Qed.

Lemma createPartitionPostcondition  v0   (* zero *) (* nullv *) (* idxPR idxPD idxSH1 idxSH2
idxSH3 idxPPR *)
pdChild currentPart currentPD level ptRefChild descChild idxRefChild
 ptPDChild idxPDChild   ptSh1Child shadow1 idxSh1
  ptSh2Child shadow2 idxSh2   ptConfigPagesList
idxConfigPagesList 
currentShadow1 ptRefChildFromSh1 derivedRefChild ptPDChildSh1 
ptSh1ChildFromSh1  childSh2
 childListSh1  list phyPDChild phySh1Child
phySh2Child phyConfigPagesList phyDescChild s :
 propagatedProperties false false false false pdChild currentPart currentPD level ptRefChild
       descChild idxRefChild true ptPDChild idxPDChild true ptSh1Child shadow1 idxSh1 true ptSh2Child
       shadow2 idxSh2 true ptConfigPagesList idxConfigPagesList true currentShadow1 ptRefChildFromSh1
       derivedRefChild ptPDChildSh1 false ptSh1ChildFromSh1 false childSh2 false childListSh1 false list
       phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild s /\
     newPropagatedProperties s (CIndex 0) defaultVAddr PRidx PDidx sh1idx sh2idx sh3idx PPRidx
       currentPart level phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild /\
     (forall child : page,
      In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) /\
     (forall child : page,
      In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) /\
     (forall child : page,
      In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) /\
     (forall child : page,
      In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) /\
     (forall child : page,
      In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) /\
     isEntryVA ptPDChildSh1 idxPDChild descChild s /\
     isEntryVA ptSh1ChildFromSh1 idxSh1 descChild s /\
     isEntryVA childSh2 idxSh2 descChild s /\ isEntryVA childListSh1 idxConfigPagesList descChild s /\
(* partitionsIsolation s /\
kernelDataIsolation s /\
verticalSharing s /\
consistency s /\
Some level = StateLib.getNbLevel /\
false = checkVAddrsEqualityWOOffset nbLevel descChild pdChild level /\
false = checkVAddrsEqualityWOOffset nbLevel descChild shadow1 level /\
false = checkVAddrsEqualityWOOffset nbLevel descChild shadow2 level /\
false = checkVAddrsEqualityWOOffset nbLevel descChild list level /\
false = checkVAddrsEqualityWOOffset nbLevel pdChild shadow1 level /\
false = checkVAddrsEqualityWOOffset nbLevel pdChild shadow2 level /\
false = checkVAddrsEqualityWOOffset nbLevel pdChild list level /\
false = checkVAddrsEqualityWOOffset nbLevel shadow1 shadow2 level /\
false = checkVAddrsEqualityWOOffset nbLevel shadow1 list level /\
false = checkVAddrsEqualityWOOffset nbLevel shadow2 list level /\
(Kidx =? nth (length descChild - (nbLevel - 1 + 2)) descChild defaultIndex) = false /\
(Kidx =? nth (length pdChild - (nbLevel - 1 + 2)) pdChild defaultIndex) = false /\
(Kidx =? nth (length shadow1 - (nbLevel - 1 + 2)) shadow1 defaultIndex) = false /\
(Kidx =? nth (length shadow2 - (nbLevel - 1 + 2)) shadow2 defaultIndex) = false /\
(Kidx =? nth (length list - (nbLevel - 1 + 2)) list defaultIndex) = false /\
beqVAddr defaultVAddr pdChild = false /\ 
beqVAddr defaultVAddr shadow1 = false /\
beqVAddr defaultVAddr shadow2 = false /\ 
beqVAddr defaultVAddr list = false /\
currentPart = currentPartition s /\
nextEntryIsPP currentPart PDidx currentPD s /\
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptRefChild idx s /\ getTableAddrRoot ptRefChild PDidx currentPart descChild s) /\
(defaultPage =? ptRefChild) = false /\
StateLib.getIndexOfAddr descChild fstLevel = idxRefChild /\
entryPresentFlag ptRefChild idxRefChild true s /\
entryUserFlag ptRefChild idxRefChild false s /\
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isPE ptPDChild idx s /\ getTableAddrRoot ptPDChild PDidx currentPart pdChild s) /\
(defaultPage =? ptPDChild) = false /\
StateLib.getIndexOfAddr pdChild fstLevel = idxPDChild /\
entryPresentFlag ptPDChild idxPDChild true s /\
entryUserFlag ptPDChild idxPDChild false s /\
(forall idx : index,
StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
isPE ptSh1Child idx s /\ getTableAddrRoot ptSh1Child PDidx currentPart shadow1 s) /\
(defaultPage =? ptSh1Child) = false /\
StateLib.getIndexOfAddr shadow1 fstLevel = idxSh1 /\
entryPresentFlag ptSh1Child idxSh1 true s /\
entryUserFlag ptSh1Child idxSh1 false s /\
(forall idx : index,
StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
isPE ptSh2Child idx s /\ getTableAddrRoot ptSh2Child PDidx currentPart shadow2 s) /\
(defaultPage =? ptSh2Child) = false /\
StateLib.getIndexOfAddr shadow2 fstLevel = idxSh2 /\
entryPresentFlag ptSh2Child idxSh2 true s /\
entryUserFlag ptSh2Child idxSh2 false s /\
(forall idx : index,
StateLib.getIndexOfAddr list fstLevel = idx ->
isPE ptConfigPagesList idx s /\ getTableAddrRoot ptConfigPagesList PDidx currentPart list s) /\
(defaultPage =? ptConfigPagesList) = false /\
StateLib.getIndexOfAddr list fstLevel = idxConfigPagesList /\
entryPresentFlag ptConfigPagesList idxConfigPagesList true s /\
entryUserFlag ptConfigPagesList idxConfigPagesList false s /\
nextEntryIsPP currentPart sh1idx currentShadow1 s /\
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isVE ptRefChildFromSh1 idx s /\ getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) /\
(defaultPage =? ptRefChildFromSh1) = false /\
(exists va : vaddr, isEntryVA ptRefChildFromSh1 idxRefChild va s /\ beqVAddr defaultVAddr va = derivedRefChild) /\
(forall idx : index,
StateLib.getIndexOfAddr pdChild fstLevel = idx ->
isVE ptPDChildSh1 idx s /\ getTableAddrRoot ptPDChildSh1 sh1idx currentPart pdChild s) /\
(defaultPage =? ptPDChildSh1) = false /\
(forall idx : index,
StateLib.getIndexOfAddr shadow1 fstLevel = idx ->
isVE ptSh1ChildFromSh1 idx s /\ getTableAddrRoot ptSh1ChildFromSh1 sh1idx currentPart shadow1 s) /\
(defaultPage =? ptSh1ChildFromSh1) = false /\
(forall idx : index,
StateLib.getIndexOfAddr shadow2 fstLevel = idx ->
isVE childSh2 idx s /\ getTableAddrRoot childSh2 sh1idx currentPart shadow2 s) /\
(defaultPage =? childSh2) = false /\
(forall idx : index,
StateLib.getIndexOfAddr list fstLevel = idx ->
isVE childListSh1 idx s /\ getTableAddrRoot childListSh1 sh1idx currentPart list s) /\
(defaultPage =? childListSh1) = false /\
isEntryPage ptPDChild idxPDChild phyPDChild s /\
(defaultPage =? phyPDChild) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) -> ~ (partition = phyPDChild \/ In phyPDChild (getConfigPagesAux partition s))) /\
isEntryPage ptSh1Child idxSh1 phySh1Child s /\
(defaultPage =? phySh1Child) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phySh1Child \/ In phySh1Child (getConfigPagesAux partition s))) /\
isEntryPage ptSh2Child idxSh2 phySh2Child s /\
(defaultPage =? phySh2Child) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phySh2Child \/ In phySh2Child (getConfigPagesAux partition s))) /\
isEntryPage ptConfigPagesList idxConfigPagesList phyConfigPagesList s /\
(defaultPage =? phyConfigPagesList) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phyConfigPagesList \/ In phyConfigPagesList (getConfigPagesAux partition s))) /\
isEntryPage ptRefChild idxRefChild phyDescChild s /\
(defaultPage =? phyDescChild) = false /\
(forall partition : page,
In partition (getPartitions multiplexer s) ->
~ (partition = phyDescChild \/ In phyDescChild (getConfigPagesAux partition s))) /\
isPartitionFalse ptSh1ChildFromSh1 idxSh1 s /\
isPartitionFalse childSh2 idxSh2 s /\
isPartitionFalse childListSh1 idxConfigPagesList s /\
isPartitionFalse ptRefChildFromSh1 idxRefChild s /\
isPartitionFalse ptPDChildSh1 idxPDChild s /\
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyPDChild (getAccessibleMappedPages partition s)) /\
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phySh1Child (getAccessibleMappedPages partition s)) /\
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phySh2Child (getAccessibleMappedPages partition s)) /\
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyConfigPagesList (getAccessibleMappedPages partition s)) /\
(forall partition : page,
In partition (getAncestors currentPart s) ->
~ In phyDescChild (getAccessibleMappedPages partition s)) /\       
zero = CIndex 0 /\
isWellFormedSndShadow level phySh2Child s /\
isWellFormedFstShadow level phySh1Child s /\
(forall idx : index,
StateLib.readPhyEntry phyPDChild idx (memory s) = Some defaultPage /\
StateLib.readPresent phyPDChild idx (memory s) = Some false) /\
StateLib.readPhysical phyConfigPagesList (CIndex (tableSize - 1)) (memory s) = Some defaultPage /\
(forall idx : index,
idx <> CIndex (tableSize - 1) ->
Nat.Odd idx -> StateLib.readVirtual phyConfigPagesList idx (memory s) = Some defaultVAddr) /\
(forall idx : index,
Nat.Even idx -> exists idxValue : index, StateLib.readIndex phyConfigPagesList idx (memory s) = Some idxValue) /\
nullv = defaultVAddr /\
idxPR = PRidx /\
idxPD = PDidx /\
idxSH1 = sh1idx /\
idxSH2 = sh2idx /\
idxSH3 = sh3idx /\
idxPPR = PPRidx /\
isVA phyDescChild idxPPR s /\
nextEntryIsPP phyDescChild idxPPR currentPart s /\
isVA phyDescChild idxSH3 s /\
nextEntryIsPP phyDescChild idxSH3 phyConfigPagesList s /\
isVA phyDescChild idxSH2 s /\
nextEntryIsPP phyDescChild idxSH2 phySh2Child s /\
isVA phyDescChild idxSH1 s /\
nextEntryIsPP phyDescChild idxSH1 phySh1Child s /\
isVA phyDescChild idxPD s /\
nextEntryIsPP phyDescChild idxPD phyPDChild s /\
isVA phyDescChild idxPR s /\
nextEntryIsPP phyDescChild idxPR phyDescChild s /\
(forall child : page, In child (getChildren currentPart s) -> ~ In phyDescChild (getMappedPages child s)) /\
(forall child : page, In child (getChildren currentPart s) -> ~ In phyPDChild (getMappedPages child s)) /\
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh1Child (getMappedPages child s)) /\
(forall child : page, In child (getChildren currentPart s) -> ~ In phySh2Child (getMappedPages child s)) /\
(forall child : page, In child (getChildren currentPart s) -> ~ In phyConfigPagesList (getMappedPages child s)) /\
isEntryVA ptPDChildSh1 idxPDChild descChild s /\
isEntryVA ptSh1ChildFromSh1 idxSh1 descChild s /\ isEntryVA childSh2 idxSh2 descChild s /\
isEntryVA childListSh1 idxConfigPagesList descChild s /\ *)
lookup ptRefChildFromSh1 idxRefChild (memory s) beqPage beqIndex =
Some (VE v0) ->
partitionsIsolation
{|
currentPartition := currentPartition s;
memory := add ptRefChildFromSh1 idxRefChild
    (VE {| pd := true; va := va v0 |}) (memory s) beqPage beqIndex |} /\
kernelDataIsolation
{|
currentPartition := currentPartition s;
memory := add ptRefChildFromSh1 idxRefChild
    (VE {| pd := true; va := va v0 |}) (memory s) beqPage beqIndex |} /\
verticalSharing
{|
currentPartition := currentPartition s;
memory := add ptRefChildFromSh1 idxRefChild
    (VE {| pd := true; va := va v0 |}) (memory s) beqPage beqIndex |} /\
consistency
{|
currentPartition := currentPartition s;
memory := add ptRefChildFromSh1 idxRefChild
    (VE {| pd := true; va := va v0 |}) (memory s) beqPage beqIndex |}.
Proof.
set(s' := {|
currentPartition := currentPartition s;
memory := add ptRefChildFromSh1 idxRefChild
    (VE {| pd := true; va := va v0 |}) (memory s) beqPage beqIndex |}).
intros.
unfold propagatedProperties, newPropagatedProperties  in *.
assert(Hpost : In phyDescChild (getChildren (currentPartition s) {|
  currentPartition := currentPartition s;
  memory := add ptRefChildFromSh1 idxRefChild (VE {| pd := true; va := va v0 |})
              (memory s) beqPage beqIndex |})).
intuition;
subst.
apply addNewChild with ptRefChild level currentPD currentShadow1;intuition.
assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
      StateLib.checkVAddrsEqualityWOOffset nbLevel descChild va1 ( CLevel (nbLevel -1) ) = true )
    by apply AllVAddrWithOffset0.
destruct Heqvars as (va1 & Hva1 & Hva11).  
assert(Hi1 : forall idx : index,
  StateLib.getIndexOfAddr descChild fstLevel = idx ->
  isPE ptRefChild idx s /\
  getTableAddrRoot ptRefChild PDidx currentPart descChild s) by intuition.
destruct Hi1 with (StateLib.getIndexOfAddr descChild fstLevel) as(Hnew1 & Hnew2); trivial.
assert(Hi2 : forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isVE ptRefChildFromSh1 idx s /\
getTableAddrRoot ptRefChildFromSh1 sh1idx currentPart descChild s) by intuition.
destruct Hi2 with (StateLib.getIndexOfAddr descChild fstLevel) as(Hnew3 & Hnew4);
trivial.
assert (Hidxeq : (StateLib.getIndexOfAddr descChild fstLevel) =(StateLib.getIndexOfAddr va1 fstLevel)) . 
{ apply checkVAddrsEqualityWOOffsetTrue'
  with nbLevel (CLevel (nbLevel - 1));trivial .
  apply fstLevelLe.
  apply getNbLevelLt. 
  apply getNbLevelEqOption. }
 
assert(Hphynotchild : ~ In phyDescChild (getChildren  (currentPartition s) s)).
{ unfold not; intros Hfalse.
  intuition subst. 
  contradict Hfalse.
  assert(Hnotpart : StateLib.readPDflag ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
             (memory s) = Some false \/
           StateLib.readPDflag ptRefChildFromSh1 (StateLib.getIndexOfAddr descChild fstLevel)
             (memory s) = None) by trivial.
          
  assert(getMappedPage currentPD s va1 = SomePage phyDescChild /\
  ~ In va1 (getPdsVAddr (currentPartition s) level getAllVAddrWithOffset0 s)) as ( Hvaphy' & Hpds1).
  { split.
    + rewrite  Hidxeq in *. apply getMappedPageGetTableRoot with ptRefChild (currentPartition s);trivial.
      intros;subst;split;trivial.
      apply getTableAddrRootEqOffset with descChild;trivial.
      left;trivial.
    + unfold isPartitionFalse in *.
      move Hnotpart at bottom.
      unfold getPdsVAddr.
      rewrite filter_In.
      apply Classical_Prop.or_not_and.
      right.
      unfold checkChild.
      rewrite nextEntryIsPPgetFstShadow in *.
      assert(Hfstsh1 : getFstShadow (currentPartition s) (memory s) = Some currentShadow1).
      trivial. 
      rewrite Hfstsh1.
      assert(Hind : getIndirection currentShadow1 descChild level (nbLevel - 1) s = Some ptRefChildFromSh1).
      apply getIndirectionGetTableRoot with (currentPartition s);trivial.
      symmetry;trivial.
      assert(Hineq :  getIndirection currentShadow1 va1 level (nbLevel - 1) s  = Some ptRefChildFromSh1).
      { rewrite <- Hind.
        symmetry.
        apply getIndirectionEq;trivial.
        apply getNbLevelLt;
        symmetry;trivial.
        rewrite <- Hva11.
        f_equal.
        assert(Hlevel : Some level = StateLib.getNbLevel ) by trivial.
        assert(Hlvl : StateLib.getNbLevel = Some (CLevel (nbLevel - 1))) by apply getNbLevelEqOption. 
        rewrite  Hlvl in *.
        inversion Hlevel;trivial. }
        rewrite Hineq.
      destruct  (ptRefChildFromSh1 =? defaultPage);trivial.
      auto.

      rewrite Hidxeq in *.
      destruct Hnotpart as [Hiaux | Hiaux]; rewrite Hiaux;auto. }
  unfold getChildren.
  assert(Hlevel : Some level = StateLib.getNbLevel) by trivial.
  rewrite <- Hlevel.
  rewrite nextEntryIsPPgetPd in *.
  assert(HcurrentPD : StateLib.getPd (currentPartition s)  (memory s) = Some currentPD) by trivial.
  rewrite HcurrentPD.
  unfold getMappedPagesAux.
  rewrite filterOptionInIff.
  unfold getMappedPagesOption.
  rewrite in_map_iff.
  unfold not.
  intros Hfalse.
  destruct Hfalse as (samev & Hi & Hii).
 


  assert(va1 = samev).
  { apply eqMappedPagesEqVaddrs with phyDescChild currentPD s;trivial.
unfold getPdsVAddr in Hii.
apply filter_In in Hii.
destruct Hii;trivial.
  unfold consistency in *.
  assert(Hnodumap : noDupMappedPagesList s) by intuition.
  unfold noDupMappedPagesList in *.
  assert(Hcurpart : In  (currentPartition s) (getPartitions multiplexer s)).
  { unfold consistency in *. unfold currentPartitionInPartitionsList in *.
    intuition. }
  apply Hnodumap in Hcurpart.
  clear Hnodumap.
  move Hcurpart at bottom.
  unfold getMappedPages in Hcurpart.
  rewrite HcurrentPD in *.
  unfold getMappedPagesAux  in *.
  unfold getMappedPagesOption in Hcurpart;trivial. }
    
  subst.
  
  now contradict Hpds1. } 
assert(HmappedPD : In phyPDChild (getMappedPages currentPart s)).
{ intuition.
  subst.
  apply inGetMappedPagesGetTableRoot with pdChild ptPDChild
  currentPD ;intuition. }
assert(Hmappedsh1 : In phySh1Child(getMappedPages currentPart s)).
{ intuition.
  subst.
  apply inGetMappedPagesGetTableRoot with shadow1 ptSh1Child
  currentPD ;intuition. }
assert(HmappedSh2 : In phySh2Child (getMappedPages currentPart s)).
{ intuition.
  subst.
  apply inGetMappedPagesGetTableRoot with shadow2 ptSh2Child
  currentPD ;intuition. }
assert(Hmappedsh3 : In phyConfigPagesList (getMappedPages currentPart s)).
{ intuition.
  subst.
  apply inGetMappedPagesGetTableRoot with list ptConfigPagesList
  currentPD ;intuition. }
assert(HmappedDesc : In phyDescChild (getMappedPages currentPart s)).
{ intuition.
  subst.
  apply inGetMappedPagesGetTableRoot with descChild ptRefChild
  currentPD ;intuition. }
assert(Hcurpart : In (currentPartition s) (getPartitions multiplexer s)).
{ unfold consistency in *.
  unfold currentPartitionInPartitionsList in *.
  intuition. }
assert(Hmap1 : getMappedPage currentPD s pdChild = SomePage phyPDChild).
{ intuition. apply getMappedPageGetTableRoot with ptPDChild currentPart ;subst;trivial. }
assert(Hmap2 : getMappedPage currentPD s shadow1 = SomePage phySh1Child).
{ intuition. apply getMappedPageGetTableRoot with ptSh1Child currentPart ;subst;trivial. }
assert(Hmap3 : getMappedPage currentPD s shadow2 = SomePage phySh2Child).
{ intuition. apply getMappedPageGetTableRoot with ptSh2Child currentPart ;subst;trivial. }
assert(Hmap4 : getMappedPage currentPD s list = SomePage phyConfigPagesList).
{ intuition. apply getMappedPageGetTableRoot with ptConfigPagesList currentPart ;subst;trivial. }
assert(Hmap5 : getMappedPage currentPD s descChild = SomePage phyDescChild).
{ intuition. apply getMappedPageGetTableRoot with ptRefChild currentPart ;subst;trivial. }

assert(isParent s).
unfold consistency in *.
 intuition. (** isParent *)

unfold s' in *.
clear s'.
  rewrite Hidxeq in *.
intuition.

(** partitionsIsolation **)
+ subst.
  apply partitionsIsolationAddChild  with  (currentPartition s) ptRefChild
  phyDescChild level currentPD currentShadow1 phyPDChild phySh1Child
  phySh2Child phyConfigPagesList;intuition;subst;trivial. 
  apply getTableAddrRootEqOffset with descChild;trivial.
  left;trivial.
  apply getTableAddrRootEqOffset with descChild;trivial.
  right;left;trivial.
  
(** kernelDataIsolation **) 
+ 
 assert(Hidx :(StateLib.getIndexOfAddr va1 fstLevel = idxRefChild))  by trivial.
 rewrite <- Hidx. 
 subst idxRefChild.
 
  apply kernelDataIsolationAddChild  with   (currentPartition s) phyDescChild level
  currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList ptRefChild
  currentShadow1 idxConfigPagesList ptConfigPagesList idxSh2 ptSh2Child shadow2
  idxSh1 ptSh1Child shadow1 idxPDChild ptPDChild pdChild (StateLib.getIndexOfAddr va1 fstLevel) list;subst;
   intuition;
  subst; trivial.
  apply getTableAddrRootEqOffset with descChild;trivial.
  left;trivial.
  apply getTableAddrRootEqOffset with descChild;trivial.
  right;left;trivial.
  apply getTableAddrRootEqOffset with descChild;trivial.
  left;trivial.
(** verticalSharing **)
+ subst.  apply verticalSharingAddChild  with (currentPartition s) phyDescChild 
  level currentPD phyPDChild phySh1Child phySh2Child phyConfigPagesList 
  ptRefChild currentShadow1; intuition;subst;trivial. 
    apply getTableAddrRootEqOffset with descChild;trivial.
  left;trivial.
  apply getTableAddrRootEqOffset with descChild;trivial.
  right;left;trivial.
(** consistency **)
+ assert(Hidx :(StateLib.getIndexOfAddr va1 fstLevel = idxRefChild))  by trivial.
 rewrite <- Hidx. 
  assert(Hlevel : Some level = StateLib.getNbLevel ) by trivial.
 assert(Hlvl : StateLib.getNbLevel = Some (CLevel (nbLevel - 1))) by apply getNbLevelEqOption. 

   apply consistencyAddChild  with (CIndex 0)  defaultVAddr  PRidx PDidx sh1idx sh2idx
sh3idx PPRidx pdChild currentPart currentPD level ptRefChild idxRefChild ptPDChild
idxPDChild ptSh1Child shadow1 idxSh1 ptSh2Child shadow2 idxSh2 ptConfigPagesList
idxConfigPagesList currentShadow1 derivedRefChild ptPDChildSh1 ptSh1ChildFromSh1 childSh2
childListSh1 list phyPDChild phySh1Child phySh2Child phyConfigPagesList phyDescChild;
intuition; subst; trivial.

symmetry; rewrite  Hlvl in *;
apply checkVAddrsEqualityWOOffsetTrans with descChild;trivial;
rewrite checkVAddrsEqualityWOOffsetPermut. 
rewrite <- Hva11;
inversion Hlevel;trivial.
symmetry ;trivial.
symmetry; rewrite  Hlvl in *;
apply checkVAddrsEqualityWOOffsetTrans with descChild;trivial;
rewrite checkVAddrsEqualityWOOffsetPermut. 
rewrite <- Hva11;
inversion Hlevel;trivial.
symmetry ;trivial.

symmetry; rewrite  Hlvl in *;
apply checkVAddrsEqualityWOOffsetTrans with descChild;trivial;
rewrite checkVAddrsEqualityWOOffsetPermut. 
rewrite <- Hva11;
inversion Hlevel;trivial.
symmetry ;trivial.

symmetry; rewrite  Hlvl in *;
apply checkVAddrsEqualityWOOffsetTrans with descChild;trivial;
rewrite checkVAddrsEqualityWOOffsetPermut. 
rewrite <- Hva11;
inversion Hlevel;trivial.
symmetry ;trivial.
assert(Hkidx : (Kidx =?
       nth (length descChild - (nbLevel - 1 + 2)) descChild defaultIndex) =
      false) by trivial.
      rewrite <- Hkidx.
      f_equal.
assert(Heqidx : StateLib.getIndexOfAddr va1 (CLevel(nbLevel-1)) = StateLib.getIndexOfAddr descChild
(CLevel (nbLevel -1))).
{ apply checkVAddrsEqualityWOOffsetTrue' with nbLevel level;trivial.
rewrite  Hlvl in *.
rewrite <- Hva11;
inversion Hlevel;trivial.
rewrite checkVAddrsEqualityWOOffsetPermut;trivial.
rewrite <- Hlevel in *.
inversion Hlvl.
omega.
apply getNbLevelLt;trivial.
symmetry ;trivial. }
unfold StateLib.getIndexOfAddr  in Heqidx.
revert Heqidx.
clear.
intros. 
unfold CLevel in *. 
case_eq(lt_dec (nbLevel - 1) nbLevel);intros ; rewrite H in *. 
simpl in *.
rewrite Heqidx.
trivial.
assert(0<nbLevel) by apply nbLevelNotZero.
omega. 
apply getTableAddrRootEqOffset with descChild;trivial.
left;trivial.
apply getTableAddrRootEqOffset with descChild;trivial.
right;left;trivial.
assert(Hnewgoal : getMappedPage currentPD s descChild = SomePage phyDescChild) by trivial.
rewrite <- Hnewgoal.
symmetry.
apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.


Qed. (** createPartitionPostcondition*)

