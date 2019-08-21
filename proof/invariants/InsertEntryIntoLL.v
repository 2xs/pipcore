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
    This file contains required lemmas to prove that updating the linked list 
    structure preserves isolation and consistency properties  *)
Require Import Model.ADT Core.Internal Isolation Consistency WeakestPreconditions 
Invariants StateLib Model.Hardware  Model.MAL 
DependentTypeLemmas Model.Lib InternalLemmas PropagatedProperties UpdateShadow2Structure
IWritePhysical WriteIndex.
Require Import Coq.Logic.ProofIrrelevance Omega List Bool.
(************************** TO MOVE ******************************)
(*%%%%%%%%%%%%Consistency%%%%%%%%%%%*)


(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

(*%%%%%%%%%%%%%InternalLemmas%%%%%%%%%%%*)
Lemma getMaxIndexSome :
exists x, StateLib.getMaxIndex =Some x.
Proof.
unfold StateLib.getMaxIndex.
pose proof tableSizeBigEnough.
case_eq(gt_dec tableSize 0);intros;simpl.
eexists.
f_equal.
omega.
Qed. 
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
(* %%%%%%%%%%%%%%%%%%%%%%DependentTypeLemmas %%%%%%%%%%%%%%%%%%%*)
Lemma indexPredMinus1 a b:
StateLib.Index.pred a = Some b -> 
a = (CIndex (b -1)).
Admitted.
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

(********************************************************************)
Lemma getVirtualAddressSh2UpdateLLContent newLastLLable FFI x sh2 va entry LL partition s:
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
getConfigTablesLinkedList partition (memory s) = Some LL -> 
In newLastLLable (getLLPages LL s (nbPage + 1)) ->
consistency s ->
In partition (getPartitions multiplexer s) ->
getSndShadow partition (memory s) = Some sh2 ->
getVirtualAddressSh2 sh2 s va = getVirtualAddressSh2 sh2 {|
      currentPartition := currentPartition s;
      memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |} va .
Proof.
intros Hlookup HLL Hkey Hcons Hpart Hsh2.
unfold getVirtualAddressSh2.
case_eq(StateLib.getNbLevel); [intros l Hlevel|intros];trivial.
assert(Hind : getIndirection sh2 va l (nbLevel - 1)
{|
currentPartition := currentPartition s;
memory := add newLastLLable FFI (VA x) (memory s) beqPage
            beqIndex |} = getIndirection  sh2 va l (nbLevel - 1)
s).
{ apply getIndirectionUpdateSh2 with entry;trivial. }
rewrite Hind.
case_eq (getIndirection sh2 va l (nbLevel - 1) s );
[ intros tbl Htbl | intros Htbl]; trivial.
case_eq (defaultPage =? tbl);trivial.
intros Htblnotnul.
simpl.
assert(HinconfigSh2: In tbl (getIndirections sh2 s)).
{ unfold getIndirections.
  assert(nbLevel>0) by apply nbLevelNotZero.
  replace nbLevel with ((nbLevel-1) + 1) by omega.
  apply getIndirectionInGetIndirections1 with va l;trivial; try omega. 
  apply beq_nat_false in Htblnotnul.
  contradict Htblnotnul.
  rewrite pageEqNatEqEquiv;symmetry;trivial.
  apply sh2PartNotNull with partition s;trivial.
  apply nextEntryIsPPgetSndShadow;trivial.
  unfold consistency in *;intuition. }
symmetry.
apply readVirtualUpdateSh2.
left.
apply disjointSh2LLstruct with sh2 LL partition s;trivial.
assert(Hconskey: noDupConfigPagesList s) by (unfold consistency in *;intuition).
unfold noDupConfigPagesList in *.
apply Hconskey in Hpart;clear Hconskey.
unfold getConfigPages in *.
apply NoDup_cons_iff in Hpart.
intuition.
Qed.

Lemma isAccessibleMappedPageInParentUpdateLLContentSamePart partition accessiblePage newLastLLable FFI x va entry  LL (* l *) s:
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
getConfigTablesLinkedList partition (memory s) = Some LL -> 
In newLastLLable (getLLPages LL s (nbPage + 1)) ->
consistency s ->
(* Some l = StateLib.getNbLevel -> *)
In partition (getPartitions multiplexer s) ->
isAccessibleMappedPageInParent partition va accessiblePage s =
isAccessibleMappedPageInParent partition va accessiblePage {|
      currentPartition := currentPartition s;
      memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {|currentPartition := _ |}).
intros Hlookup HLL Hkey Hcons (* Hlevel *) Hpart.
unfold isAccessibleMappedPageInParent. 
assert(Hsh2' :  getSndShadow partition (add newLastLLable FFI (VA x) (memory s) beqPage
       beqIndex) =  getSndShadow partition (memory s)).
apply getSndShadowUpdateSh2 with entry;trivial.
simpl.
rewrite  Hsh2'; clear Hsh2'.
case_eq(getSndShadow partition (memory s));[intros sh2 Hsh2|intros]; trivial.
assert(Hgetva: getVirtualAddressSh2 sh2 s va  = getVirtualAddressSh2 sh2 s' va ).
{ apply getVirtualAddressSh2UpdateLLContent with entry LL partition;trivial. }
rewrite <- Hgetva.
case_eq(getVirtualAddressSh2 sh2 s va );[ intros vaInParent Hvainparent | intros Hvainparent];
trivial. 
assert(Hparent : getParent partition
  (add newLastLLable FFI (VA x) (memory s) beqPage beqIndex) = getParent partition (memory s)).
apply getParentUpdateSh2 with entry;trivial.
rewrite Hparent.
destruct (getParent partition (memory s) );trivial.
assert(Hpd :  StateLib.getPd p (memory s) =
StateLib.getPd p
  (add newLastLLable FFI (VA x) (memory s) beqPage beqIndex)).
{ symmetry.  apply getPdUpdateSh2 with entry;trivial. }
rewrite <- Hpd in *.
clear Hpd.
destruct (StateLib.getPd p (memory s));trivial.
assert(Haccessmap : forall part, getAccessibleMappedPage part {|
     currentPartition := currentPartition s;
     memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |} vaInParent =
getAccessibleMappedPage part s vaInParent).
{ intros. apply getAccessibleMappedPageUpdateSh2 with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
trivial.
Qed.

 Lemma getVirtualAddressSh2UpdateLLContentNotSamePart partition (va : vaddr)
 newLastLLable FFI x entry phyDescChild LLDescChild sh2 s :
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
getConfigTablesLinkedList phyDescChild (memory s) = Some LLDescChild ->
getSndShadow partition (memory s) = Some sh2 ->
consistency s ->
In newLastLLable (getLLPages LLDescChild s (nbPage + 1)) ->
In phyDescChild (getPartitions multiplexer s) ->
In partition (getPartitions multiplexer s) ->
partition <> phyDescChild ->
getVirtualAddressSh2 sh2
  {| currentPartition := currentPartition s; memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |} va =
getVirtualAddressSh2 sh2 s va.
Proof.
intros Hlookup HLL Hsh2part.
intros.
unfold getVirtualAddressSh2. 
unfold propagatedPropertiesAddVaddr in *. 
case_eq(StateLib.getNbLevel); [intros level Hlevel|intros];trivial.
assert(Hind : getIndirection sh2 va level (nbLevel - 1)
{|
currentPartition := currentPartition s;
memory := add newLastLLable FFI (VA x) (memory s) beqPage
            beqIndex |} = getIndirection  sh2 va level (nbLevel - 1)
s).
{ apply getIndirectionUpdateSh2 with entry;trivial. }
rewrite Hind.
case_eq (getIndirection  sh2 va level (nbLevel - 1) s );
[ intros tbl Htbl | intros Htbl]; trivial.
case_eq (defaultPage =? tbl);trivial.
intros Htblnotnul.
simpl.
apply readVirtualUpdateSh2;trivial.
left. 
assert(Hconfig : configTablesAreDifferent s ) by (
unfold consistency in *; intuition).
unfold configTablesAreDifferent in *. 
assert(Hinconfig1 : In tbl (getConfigPages partition s)).

{ assert (Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
  apply pdSh1Sh2ListExistsNotNull with s partition  in Hpde;trivial.
  destruct Hpde as ((pd1 & Hpd1 & Hpdnotnull) 
    & (sh1 & Hsh1 & Hsh1notnull) & (sh22 & Hsh22 & Hsh2notnull) & 
    (sh3 & Hsh3 & Hsh3notnull)).
  unfold getConfigPages.
  unfold getConfigPagesAux.
  rewrite Hpd1, Hsh1, Hsh2part, Hsh3.
  simpl.
  right.
  do 2 (rewrite in_app_iff;
  right).
   rewrite in_app_iff.
  left.
  apply getIndirectionInGetIndirections with va level (nbLevel - 1);trivial.
  apply nbLevelNotZero.
  apply beq_nat_false in Htblnotnul.
  unfold not;intros Hfalse;subst; now contradict Htblnotnul.
  apply getNbLevelLe;intuition.
  unfold consistency in *.
  apply rootStructNotNull with partition s sh2idx;intuition.
  rewrite nextEntryIsPPgetSndShadow in *;trivial.  }
assert(Hinconfig2 : In newLastLLable (getConfigPages phyDescChild s)).
{ assert (Hpde : partitionDescriptorEntry s) by (unfold consistency in *;intuition).
  apply pdSh1Sh2ListExistsNotNull with s phyDescChild  in Hpde;trivial.
  destruct Hpde as ((pd1 & Hpd1 & Hpdnotnull) 
    & (sh1 & Hsh1 & Hsh1notnull) & (sh22 & Hsh22 & Hsh2notnull) & 
    _).
  unfold getConfigPages.
  unfold getConfigPagesAux.
  rewrite Hpd1, Hsh1, Hsh22, HLL.
  simpl.
  right.
  do 3 rewrite in_app_iff.
  do 3 right;trivial. }
  

unfold not;intros; subst.
unfold Lib.disjoint in *.
contradict Hinconfig2.
apply Hconfig with partition;trivial.
Qed.

Lemma isAccessibleMappedPageInParentUpdateLLContentNotSamePart partition va 
 accessiblePage newLastLLable FFI x entry phyDescChild LLDescChild s :
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
getConfigTablesLinkedList phyDescChild (memory s) = Some LLDescChild ->
consistency s ->
In newLastLLable (getLLPages LLDescChild s (nbPage + 1)) ->
In phyDescChild (getPartitions multiplexer s) ->
In partition (getPartitions multiplexer s) ->
partition <> phyDescChild ->
isAccessibleMappedPageInParent partition va accessiblePage s = 
isAccessibleMappedPageInParent partition va accessiblePage 
{| currentPartition := currentPartition s; memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |}.
Proof.
intros Hlookup HLL.
intros.
unfold   isAccessibleMappedPageInParent.
simpl. 
assert(Hsh2 : getSndShadow partition
(add newLastLLable FFI (VA x) (memory s) beqPage
   beqIndex) =getSndShadow partition (memory s)).
{ apply getSndShadowUpdateSh2 with entry;trivial. }
rewrite Hsh2.
case_eq (getSndShadow partition (memory s));[ intros sh2 Hsh2part | intros Hnone];trivial. 
assert(Hgetva : getVirtualAddressSh2 sh2
{|
currentPartition := currentPartition s;
memory := add newLastLLable FFI (VA x)
            (memory s) beqPage beqIndex |} va =
 getVirtualAddressSh2 sh2 s va).
apply getVirtualAddressSh2UpdateLLContentNotSamePart with partition entry phyDescChild LLDescChild;
trivial. 
rewrite Hgetva.  
case_eq (getVirtualAddressSh2 sh2 s va);[ intros vainparent Hvainparent | intros Hnone];trivial. 
assert(Hparent : getParent partition
(add newLastLLable FFI (VA x) (memory s) beqPage
   beqIndex) = getParent partition (memory s)).
apply getParentUpdateSh2 with entry;trivial.
rewrite Hparent.
destruct (getParent partition (memory s) );trivial.
assert(Hpd :  StateLib.getPd p (memory s) =
StateLib.getPd p
  (add newLastLLable FFI (VA x)  (memory s) beqPage beqIndex)).
{ symmetry.  apply getPdUpdateSh2 with entry;trivial. }
rewrite <- Hpd in *.
clear Hpd.
destruct (StateLib.getPd p (memory s));trivial.
assert(Haccessmap : forall part, getAccessibleMappedPage part {|
     currentPartition := currentPartition s;
     memory := add newLastLLable FFI (VA x) (memory s) beqPage
                 beqIndex |} vainparent =
getAccessibleMappedPage part s vainparent).
{ intros. apply getAccessibleMappedPageUpdateSh2 with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
trivial.
Qed.

Lemma accessibleChildPageIsAccessibleIntoParentUpdateLLContent newLastLLable FFI x   
entry  (phyDescChild (* pdChildphy *) LLDescChild: page)s:
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
getConfigTablesLinkedList phyDescChild (memory s) = Some LLDescChild ->
(* nextEntryIsPP phyDescChild PDidx pdChildphy s -> *)
consistency s ->
In newLastLLable (getLLPages LLDescChild s (nbPage + 1)) ->
In phyDescChild (getPartitions multiplexer s) ->
accessibleChildPageIsAccessibleIntoParent
  {|
  currentPartition := currentPartition s;
  memory := add newLastLLable FFI  (VA x) (memory s) beqPage
              beqIndex |}. 
Proof.
set(s':=  {|
  currentPartition := _ |}). 
intros Hlookup HLL.
intros.
assert(Hcons: accessibleChildPageIsAccessibleIntoParent s ) by 
(unfold consistency in *;intuition).
unfold accessibleChildPageIsAccessibleIntoParent in *. 
intros partition va pd accessiblePage Hpart Hpdpart Hacces ; 
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer s').
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Haccessmap : forall part, getAccessibleMappedPage part s' va =
getAccessibleMappedPage part s va).
{ intros. apply getAccessibleMappedPageUpdateSh2 with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
assert(Hpd :  StateLib.getPd partition (memory s) =
StateLib.getPd partition
    (add newLastLLable FFI (VA x) (memory s) beqPage beqIndex)).
{ symmetry.  apply getPdUpdateSh2 with entry;trivial. }
rewrite <- Hpd in Hpdpart.
clear Hpd.
rewrite <- Hcons with partition va pd accessiblePage;trivial.
symmetry.
assert(Hor : partition = phyDescChild \/ partition <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor];
subst.
+ (* assert (Hpdeq : pdChildphy = pd). 
  { apply getPdNextEntryIsPPEq with phyDescChild s;trivial. }
  subst pd. *)
  apply isAccessibleMappedPageInParentUpdateLLContentSamePart with entry LLDescChild;trivial.
+ apply isAccessibleMappedPageInParentUpdateLLContentNotSamePart with 
  entry phyDescChild LLDescChild; trivial.
Qed.

Lemma wellFormedSndShadowUpdateLLContent newLastLLable FFI x   
entry  (phyDescChild (* pdChildphy *) LLDescChild: page)s:
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
getConfigTablesLinkedList phyDescChild (memory s) = Some LLDescChild ->
(* nextEntryIsPP phyDescChild PDidx pdChildphy s -> *)
consistency s ->
In newLastLLable (getLLPages LLDescChild s (nbPage + 1)) ->
In phyDescChild (getPartitions multiplexer s) ->
wellFormedSndShadow
  {|
  currentPartition := currentPartition s;
  memory := add newLastLLable FFI  (VA x) (memory s) beqPage
              beqIndex |}. 
Proof.
set(s':=  {| currentPartition := _ |}). 
intros Hlookup HLL.
intros.
assert(Hcons: wellFormedSndShadow s ) by 
(unfold consistency in *;intuition).
unfold wellFormedSndShadow in *. 
intros(*  partition va pd accessiblePage Hpart Hpdpart Hacces ;  *).
simpl.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer s').
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
simpl in *.
assert(Haccessmap : forall part, getMappedPage part s' va =
getMappedPage part s va).
{ intros. apply getMappedPageUpdateSh2 with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
assert(Hpd :  StateLib.getPd partition (memory s) =
StateLib.getPd partition
    (add newLastLLable FFI (VA x) (memory s) beqPage beqIndex)).
{ symmetry.  apply getPdUpdateSh2 with entry;trivial. }
rewrite <- Hpd in *.
clear Hpd.
assert(Hpd :  getSndShadow partition (memory s) =
getSndShadow partition
    (add newLastLLable FFI (VA x) (memory s) beqPage beqIndex)).
{ symmetry.  apply getSndShadowUpdateSh2 with entry;trivial. }
rewrite <- Hpd in *.
assert(Hgoal: exists vainparent : vaddr,
          getVirtualAddressSh2 sh2 s va = Some vainparent /\ beqVAddr defaultVAddr vainparent = false) 
          by (apply Hcons with partition pg pd;trivial).
destruct Hgoal as (vainparent & Hgoal & Hi).
exists vainparent;split;trivial.
rewrite <- Hgoal.
assert(Hor : partition = phyDescChild \/ partition <> phyDescChild) by apply pageDecOrNot.
destruct Hor as [Hor | Hor];
subst.
+ symmetry. apply getVirtualAddressSh2UpdateLLContent with entry LLDescChild phyDescChild;trivial.       
+ apply getVirtualAddressSh2UpdateLLContentNotSamePart with partition entry phyDescChild LLDescChild;trivial.
Qed.



Lemma consistencyUpdateLLContent s phyDescChild LLDescChild (* pdChildphy *) 
  newLastLLable FFI x entry:
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
consistency s -> 
getConfigTablesLinkedList phyDescChild (memory s) = Some LLDescChild ->
(* nextEntryIsPP phyDescChild PDidx pdChildphy s -> *)
In newLastLLable (getLLPages LLDescChild s (nbPage + 1)) ->
In phyDescChild (getPartitions multiplexer s) -> 
consistency  {| currentPartition := currentPartition s; memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |}.
Proof.
intros Hlookup Hcons.
intros.
unfold consistency in *.
intuition.
(** partitionDescriptorEntry **)
- apply partitionDescriptorEntryUpdateSh2 with entry;trivial.
(** dataStructurePdSh1Sh2asRoot **)
- apply dataStructurePdSh1Sh2asRootUpdateSh2 with entry;trivial.
(** dataStructurePdSh1Sh2asRoot **)
- apply dataStructurePdSh1Sh2asRootUpdateSh2 with entry;trivial.
(** dataStructurePdSh1Sh2asRoot **)
- apply dataStructurePdSh1Sh2asRootUpdateSh2 with entry;trivial.
(** currentPartitionInPartitionsList **)
- apply currentPartitionInPartitionsListUpdateSh2 with entry;trivial.
(** noDupMappedPagesList **)
- apply noDupMappedPagesListUpdateSh2 with entry;trivial.
(** noDupConfigPagesList **)
- apply noDupConfigPagesListUpdateSh2 with entry ; trivial.
(** parentInPartitionList **)
- apply parentInPartitionListUpdateSh2 with entry ; trivial.
(** accessibleVAIsNotPartitionDescriptor **)
- apply accessibleVAIsNotPartitionDescriptorUpdateSh2 with entry ; trivial.
(** accessibleChildPageIsAccessibleIntoParent **)
- apply accessibleChildPageIsAccessibleIntoParentUpdateLLContent  with entry 
  phyDescChild (* pdChildphy *) LLDescChild;trivial;unfold consistency; intuition.
(** noCycleInPartitionTree **)
- apply noCycleInPartitionTreeUpdateSh2 with entry;trivial.
(** configTablesAreDifferent **)
- apply configTablesAreDifferentUpdateSh2 with entry;trivial.
(** isChild **)
- apply isChildUpdateSh2 with entry;trivial.
(** isPresentNotDefaultIff *)
- apply isPresentNotDefaultIffUpdateSh2 with entry;trivial.
(** physicalPageNotDerived **)
- apply physicalPageNotDerivedUpdateSh2 with entry;trivial.
(** multiplexerWithoutParent *)
- apply multiplexerWithoutParentUpdateSh2 with entry;trivial.
(** isParent **)
- apply isParentUpdateSh2 with entry;trivial.
(** noDupPartitionTree **)
- apply noDupPartitionTreeUpdateSh2 with entry;trivial.
(** wellFormedFstShadow **)
- apply wellFormedFstShadowUpdateSh2 with entry;trivial.
(** wellFormedSndShadow **)
- apply wellFormedSndShadowUpdateLLContent with entry phyDescChild
LLDescChild;trivial. unfold consistency; intuition. 
(** wellFormedShadows *)
- apply wellFormedShadowsUpdateSh2 with entry;trivial.
(** wellFormedShadows *)
- apply wellFormedShadowsUpdateSh2 with entry;trivial.
- apply wellFormedFstShadowIfNoneUpdateSh2 with entry;trivial.
- apply wellFormedFstShadowIfDefaultValuesUpdateSh2 with entry;trivial.
Qed.
Lemma indirectionDescriptionUpdateLLContent s descChildphy phyPDChild idxroot 
vaToPrepare l newLastLLable FFI x entry:
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
indirectionDescription s descChildphy phyPDChild idxroot vaToPrepare l ->
indirectionDescription  
{| currentPartition := currentPartition s; 
   memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |}  
   descChildphy phyPDChild idxroot vaToPrepare l.
Proof.
intros Hlookup Htoprop.
intros.
unfold indirectionDescription in *.
destruct Htoprop as (tableroot & Hpp & Hnotnull & Htableroot).
exists tableroot;split.
rewrite <- nextEntryIsPPUpdateSh2 with entry;trivial.
split;trivial.
destruct Htableroot as [Htableroot | Htableroot] ;[left;trivial|right].
destruct Htableroot as (nbL0 & stop & Hnbl0 & Hstop & Hind & Hdef & Hnbl).
exists nbL0;exists stop. try repeat split;trivial.
rewrite <- Hind.
apply getIndirectionUpdateSh2 with entry;trivial.
Qed.

Lemma initPEntryTablePreconditionToPropagatePreparePropertiesUpdateLLContent x table newLastLLable FFI entry s:
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
initPEntryTablePreconditionToPropagatePrepareProperties s table ->
initPEntryTablePreconditionToPropagatePrepareProperties 
{| currentPartition := currentPartition s; memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |} table.
Proof.
intros.
assert(Hi: getPartitions multiplexer {| currentPartition := currentPartition s; memory := add newLastLLable FFI 
(VA x) (memory s) beqPage beqIndex |} = getPartitions multiplexer s).
symmetry;apply getPartitionsUpdateSh2 with entry;trivial.
unfold initPEntryTablePreconditionToPropagatePrepareProperties in *.
intros.
split;[|intuition].
intros.
rewrite Hi in *;clear Hi.
assert(Hi: getConfigPages partition {| currentPartition := currentPartition s; memory := add newLastLLable FFI 
(VA x) (memory s) beqPage beqIndex |} = getConfigPages partition s).
apply getConfigPagesUpdateSh2 with entry;trivial.
rewrite Hi;trivial.
destruct H0.
apply H0;trivial.
Qed. 

Lemma writeAccessibleRecPreparePostconditionUpdateLLContent s currentPart phyMMUaddr newLastLLable FFI x entry:
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
writeAccessibleRecPreparePostcondition currentPart phyMMUaddr s ->
writeAccessibleRecPreparePostcondition currentPart phyMMUaddr 
{| currentPartition := currentPartition s; 
   memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |}).
intros Hlookup Htoprop.
intros.
unfold writeAccessibleRecPreparePostcondition in *.
intros.
assert(Hpartitions : getAncestors currentPart s = getAncestors currentPart s').
symmetry;apply getAncestorsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
assert(Haccessmap : forall partition, getAccessibleMappedPages partition s' =
getAccessibleMappedPages partition s).
{ intros. apply getAccessibleMappedPagesUpdateSh2 with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
apply Htoprop;trivial.
Qed.

Lemma isWellFormedTablesUpdateLLContent (phyMMUaddr phySh1addr phySh2addr : page) (lpred : level) (s : state)
 newLastLLable FFI x entry LLDescChild descChildphy:
initPEntryTablePreconditionToPropagatePrepareProperties s phySh2addr->
In newLastLLable (getLLPages LLDescChild s (nbPage + 1)) ->
getConfigTablesLinkedList descChildphy (memory s) = Some LLDescChild ->
In descChildphy (getPartitions multiplexer s) ->
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s  ->
consistency s ->
isWellFormedTables  phyMMUaddr phySh1addr phySh2addr lpred 
{| currentPartition := currentPartition s; 
   memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |}.
Proof.
set(s':= {| currentPartition := _ |}).
intros Hnotconfig Htrd HLL Hchildpart Hlookup Htoprop Hcons.
intros.
unfold isWellFormedTables in *.
destruct Htoprop as (Ha1 & Ha2 & Ha3).
intuition.
+ unfold isWellFormedMMUTables in *;intros;
  destruct Ha1 with idx as (Hi1 & Hi2);
  unfold s';simpl;
  rewrite <- Hi1;rewrite<- Hi2;split.
  apply readPhyEntryUpdateSh2 with entry;trivial.
  apply readPresentUpdateSh2 with entry;trivial.
+ unfold isWellFormedFstShadow in *.
  destruct Ha2 as [(Hx & Ha2) | (Hx & Ha2)];[left|right];split;trivial;
  intros;
  destruct Ha2 with idx as (Hi1 & Hi2);
  unfold s';simpl;rewrite <- Hi1;rewrite <- Hi2;split.
  apply readPhyEntryUpdateSh2 with entry;trivial.
  apply readPresentUpdateSh2 with entry;trivial.
  apply readVirEntryUpdateSh2 with entry;trivial.
  apply readPDflagUpdateSh2 with entry;trivial.
+ unfold isWellFormedSndShadow in *.
  destruct Ha3 as [(Hx & Ha3) | (Hx & Hi1)];[left|right];split;trivial;
  intros;[
  destruct Ha3 with idx as (Hi1 & Hi2)|]. 
  unfold s';simpl;rewrite <- Hi1;rewrite <- Hi2;split.
  apply readPhyEntryUpdateSh2 with entry;trivial.
  apply readPresentUpdateSh2 with entry;trivial.
  destruct Hi1 with idx.
  apply readVirtualUpdateSh2.
  left.
  assert(Hconfig: In newLastLLable (getConfigPages  descChildphy s)).
  { apply inGetTrdShadowInConfigPages with LLDescChild;trivial.
  unfold consistency in *;intuition. }
  unfold initPEntryTablePreconditionToPropagatePrepareProperties in *.
  destruct Hnotconfig as (Hnotconfig & _).
  contradict Hconfig.
  subst.
  apply Hnotconfig;trivial.
Qed.

Lemma isIndexValueUpdateLLVA idx table idx2 table2  entry s m x:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
isIndexValue table2 idx2 m s ->
isIndexValue table2 idx2 m 
  {|
currentPartition := currentPartition s;
memory := add table idx (VA x)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold isIndexValue.
cbn.
case_eq (beqPairs (table, idx) (table2, idx2) beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup  table2 idx2 (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup table2 idx2 (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma newIndirectionsAreNotAccessibleUpdateLLVA idx table    entry s x phyMMUaddr phySh1addr phySh2addr:
let s':=  {|
currentPartition := currentPartition s;
memory := add table idx (VA x)
            (memory s) beqPage beqIndex |}  in 
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
newIndirectionsAreNotAccessible s phyMMUaddr phySh1addr phySh2addr ->
newIndirectionsAreNotAccessible
 s' phyMMUaddr phySh1addr phySh2addr.  
Proof.
intros * Hentry.
unfold newIndirectionsAreNotAccessible.
intros.
assert(Haccessmap : forall partition, getAccessibleMappedPages partition s' =
getAccessibleMappedPages partition s).
{ intros. apply getAccessibleMappedPagesUpdateSh2 with entry;trivial. }
rewrite Haccessmap in *. clear Haccessmap.
apply H;trivial.
assert(Hpartitions : getPartitions multiplexer
    s = 
getPartitions multiplexer s').
apply getPartitionsUpdateSh2 with entry; trivial.
rewrite <- Hpartitions in *; clear Hpartitions;trivial.
Qed.
  
Lemma propagatedPropertiesPrepareUpdateLLContent s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
      lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
      ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
      vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI  newLastLLable FFI x entry LLroot LLChildphy minFI indMMUToPreparebool:
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable
 s ptMMUTrdVA
  phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child
  currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l false false false false false false idxFstVA idxSndVA idxTrdVA zeroI minFI ->
propagatedPropertiesPrepare indMMUToPreparebool LLroot LLChildphy newLastLLable
  {| currentPartition := currentPartition s; memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |} ptMMUTrdVA
  phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child
  currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l false false false false false false idxFstVA idxSndVA idxTrdVA zeroI minFI.
Proof.
unfold propagatedPropertiesPrepare;intros.
set (s':= {| currentPartition := _ |}).
intuition;subst.
+ apply kernelDataIsolationUpdateSh2 with entry;trivial.
+ apply partitionsIsolationUpdateSh2 with entry;trivial.
+ apply verticalSharingUpdateSh2 with entry; trivial.
+ apply consistencyUpdateLLContent with descChildphy LLroot entry;trivial.
  (** getConfigTablesLinkedList descChildphy (memory s) = Some LLDescChild **)
  (** In newLastLLable (getLLPages LLDescChild s (nbPage + 1)) *)
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply isPEUpdateSh2 with entry;trivial.
+ assert(Hva: exists va : vaddr, isEntryVA ptSh1TrdVA (StateLib.getIndexOfAddr trdVA fstLevel) 
          va s /\ beqVAddr defaultVAddr va = false) by trivial.
  destruct Hva as (va & Hva & Htrue).
  exists va;split;trivial.
  unfold s'.
  apply isEntryVAUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply isVEUpdateSh2 with entry;trivial.
+ apply isEntryPageUpdateSh2  with entry;trivial.
+ apply entryPresentFlagUpdateSh2  with entry;trivial.
+ apply entryUserFlagUpdateSh2  with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply isPEUpdateSh2 with entry;trivial.
+ assert(Hva: exists va : vaddr, isEntryVA ptSh1SndVA (StateLib.getIndexOfAddr sndVA fstLevel)  
          va s /\ beqVAddr defaultVAddr va = false) by trivial.
  destruct Hva as (va & Hva & Htrue).
  exists va;split;trivial.
  unfold s'.
  apply isEntryVAUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply isVEUpdateSh2 with entry;trivial.
+ assert(Hva: exists va : vaddr, isEntryVA ptSh1FstVA (StateLib.getIndexOfAddr fstVA fstLevel) 
          va s /\ beqVAddr defaultVAddr va = false) by trivial.
  destruct Hva as (va & Hva & Htrue).
  exists va;split;trivial.
  unfold s'.
  apply isEntryVAUpdateSh2 with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply isVEUpdateSh2 with entry;trivial.
+ apply isEntryPageUpdateSh2  with entry;trivial.
+ apply entryPresentFlagUpdateSh2  with entry;trivial.
+ apply entryUserFlagUpdateSh2  with entry;trivial.
+ apply getTableAddrRootUpdateSh2 with entry;trivial.
+ apply isPEUpdateSh2 with entry;trivial.
+ apply entryUserFlagUpdateSh2  with entry;trivial.
+ apply entryPresentFlagUpdateSh2  with entry;trivial.
+ apply isEntryPageUpdateSh2  with entry;trivial.
+ apply isEntryPageUpdateSh2  with entry;trivial.
+ apply nextEntryIsPPUpdateSh2  with entry;trivial.
+ apply nextEntryIsPPUpdateSh2  with entry;trivial.
+ apply nextEntryIsPPUpdateSh2  with entry;trivial.
+ assert(Hi: getPartitions multiplexer s' = getPartitions multiplexer s).
  symmetry;apply getPartitionsUpdateSh2 with entry;trivial.
  rewrite Hi;trivial.
+ unfold indirectionDescriptionAll in *.  
  intuition; apply indirectionDescriptionUpdateLLContent  with entry;trivial.
+ unfold initPEntryTablePreconditionToPropagatePreparePropertiesAll in *.  
  intuition; apply initPEntryTablePreconditionToPropagatePreparePropertiesUpdateLLContent with entry;trivial.
+ assert(Hconf:  getConfigTablesLinkedList descChildphy (memory s) = Some LLroot) by trivial.
  rewrite <- Hconf.
  unfold s'.
  apply getConfigTablesLinkedListUpdateSh2 with entry;trivial.
+ assert(Heq: getLLPages LLroot s (nbPage + 1) = getLLPages LLroot s' (nbPage + 1)).
  unfold s';simpl.
  symmetry.
  apply getConfigTablesLinkedListsUpdateSh2 with entry;trivial.
  rewrite <- Heq;trivial.
+ assert(Heq: getLLPages LLroot s (nbPage + 1) = getLLPages LLroot s' (nbPage + 1)).
  unfold s';simpl.
  symmetry.
  apply getConfigTablesLinkedListsUpdateSh2 with entry;trivial.
  rewrite <- Heq;trivial.
 
+ assert(exists NbFI : index,
        isIndexValue newLastLLable (CIndex 1) NbFI s /\ NbFI >= minFI) as (m & Hx & Hx1) by trivial.
  exists m;split;trivial.
  apply isIndexValueUpdateLLVA with entry;trivial.
Qed.



Lemma insertEntryIntoLLPCUpdateLLContent s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
      lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
      ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
      vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred newLastLLable FFI x entry LLroot LLChildphy minFI indMMUToPreparebool:
      lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
      lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
      ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
      vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable minFI indMMUToPreparebool ->
insertEntryIntoLLPC
  {|
  currentPartition := currentPartition s;
  memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |} ptMMUTrdVA
  phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
  currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
  currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA
  nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable minFI indMMUToPreparebool.
Proof.
unfold insertEntryIntoLLPC;intros.
intuition.
+ apply propagatedPropertiesPrepareUpdateLLContent with entry;trivial.
+  unfold writeAccessibleRecPreparePostconditionAll in *.  
  intuition;apply writeAccessibleRecPreparePostconditionUpdateLLContent with entry;trivial.
+ unfold propagatedPropertiesPrepare, initPEntryTablePreconditionToPropagatePreparePropertiesAll in *;intuition.
  eapply isWellFormedTablesUpdateLLContent with (entry:= entry)  (descChildphy:=descChildphy);
  trivial.
  eassumption.
  trivial.
  (** In newLastLLable (getLLPages ?LLDescChild s (nbPage + 1)) **)
  (** getConfigTablesLinkedList descChildphy (memory s) = Some ?LLDescChild *)
+ apply newIndirectionsAreNotAccessibleUpdateLLVA with entry;trivial.
+ apply isEntryVAUpdateSh2 with entry;trivial.
+ apply isEntryVAUpdateSh2 with entry;trivial.
+ apply isEntryVAUpdateSh2 with entry;trivial.
Qed.

Lemma isIndexValueVAUpdateLLContent idx  table  entry s   x newLastLLable zeroI' FFI:
lookup table idx (memory s) beqPage beqIndex = Some (VA entry) ->
isIndexValue newLastLLable zeroI' FFI s -> 
isIndexValue newLastLLable zeroI' FFI
  {|
currentPartition := currentPartition s;
memory := add table idx (VA x)
            (memory s) beqPage beqIndex |}.
Proof.
intros Hentry.
unfold isIndexValue.
cbn.
case_eq (beqPairs (table, idx) (newLastLLable, zeroI')  beqPage beqIndex);trivial;intros Hpairs.
 + apply beqPairsTrue in Hpairs.
   destruct Hpairs as (Htable & Hidx).  subst.
   rewrite Hentry.
   trivial.
 + apply beqPairsFalse in Hpairs.
   assert (lookup newLastLLable zeroI' (removeDup table idx (memory s) beqPage beqIndex)
           beqPage beqIndex = lookup  newLastLLable zeroI' (memory s) beqPage beqIndex) as Hmemory.
   { apply removeDupIdentity. intuition. }
     rewrite Hmemory. trivial.
Qed.

Lemma writeVirtualUpdateLLContent ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare 
ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD 
ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA 
zeroI lpred zeroI' newLastLLable FFI LLChildphy LLroot vavalue minFI indMMUToPreparebool:
{{ fun s : state =>
   (insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy
      phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred  LLroot LLChildphy newLastLLable minFI indMMUToPreparebool/\
    zeroI' = CIndex 0) /\ isIndexValue newLastLLable zeroI' FFI s }} writeVirtual newLastLLable FFI vavalue
 {{ fun _ s=>
   (insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy
      phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable minFI indMMUToPreparebool/\
    zeroI' = CIndex 0) /\ isIndexValue newLastLLable zeroI' FFI s /\ isVA' newLastLLable FFI vavalue s}}.
Proof.
eapply weaken.
eapply WP.writeVirtual.
simpl;intros.
assert(Hlookup :exists entry, 
 lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry)).
 admit. (** Consistency not found : LLconfiguration4 *) 
destruct Hlookup as (entry & Hlookup). 
intuition.
+ apply insertEntryIntoLLPCUpdateLLContent with entry;trivial.
+ apply isIndexValueVAUpdateLLContent with entry;trivial.
+ unfold isVA'.
  simpl.
  assert(Htrue: beqPairs (newLastLLable, FFI) (newLastLLable, FFI) beqPage beqIndex = true).
  apply beqPairsTrue;split;trivial.
  rewrite Htrue;trivial.
Admitted.
Lemma writePhysicalUpdateLLContent ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare 
ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD 
ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA 
zeroI lpred zeroI' newLastLLable FFI LLChildphy LLroot nextFFI newFFI vavalue pgvalue minFI indMMUToPreparebool: 
{{ fun s : state =>
   (((insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable
        phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
        currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l
        idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable minFI indMMUToPreparebool /\ zeroI' = CIndex 0) /\
     isIndexValue newLastLLable zeroI' FFI s /\ isVA' newLastLLable FFI vavalue s) /\
    StateLib.Index.succ FFI = Some nextFFI) /\ isIndexValue newLastLLable nextFFI newFFI s }} 
  writePhysical newLastLLable nextFFI pgvalue {{ fun _ s => (((insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable
        phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
        currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l
        idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable minFI indMMUToPreparebool/\ zeroI' = CIndex 0) /\
     isIndexValue newLastLLable zeroI' FFI s /\ isVA' newLastLLable FFI vavalue s) /\
    StateLib.Index.succ FFI = Some nextFFI) /\ isPP' newLastLLable nextFFI pgvalue s }}.
Proof.
eapply weaken.
eapply WP.writePhysical.
intros;simpl.
assert(Hlookup :exists entry, 
 lookup newLastLLable nextFFI (memory s) beqPage beqIndex = Some (I entry)).
 intuition.
 assert(Hi :  isIndexValue newLastLLable nextFFI newFFI s) ;trivial.
 unfold isIndexValue in Hi.
 case_eq(lookup newLastLLable nextFFI (memory s) beqPage beqIndex);
  [intros v Hv |intros Hv];rewrite Hv in *;try now contradict Hi.
  destruct v;try now contradict Hv.
  subst.
 exists newFFI;trivial.
destruct Hlookup as (entry & Hlookup). 
intuition.
+ subst. eapply IWritePhysical.insertEntryIntoLLPCUpdateLLCouplePPVA  with entry FFI ;trivial.
assert(exists maxidx, StateLib.getMaxIndex = Some maxidx) as (maxidx & Hmaxidx).
apply getMaxIndexSome.
rewrite Hmaxidx.
unfold not;intros Hx;inversion Hx; subst.
assert(Hcons1: isPP newLastLLable nextFFI s) by admit.  (** Consistency not found : LLconfiguration2 *) 
unfold isPP in *.
rewrite Hlookup in Hcons1.
trivial.
+ apply isIndexValueUpdateLLCouplePPVA;trivial.
  right;subst.
  apply indexSuccNot0 with FFI;trivial.
+ apply isVA'UpdateLLCouplePPVA with entry;trivial.
+ unfold isPP';simpl.
  assert(Htrue: beqPairs (newLastLLable, nextFFI) (newLastLLable, nextFFI) beqPage beqIndex = true).
  apply beqPairsTrue;split;trivial.
  rewrite Htrue;trivial.
Admitted.

Lemma writeIndexUpdateLLContentZero  ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare 
ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD 
ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA 
zeroI lpred zeroI' newLastLLable FFI LLChildphy LLroot nextFFI newFFI vavalue pgvalue minFI indMMUToPreparebool:  
{{ fun s : state =>
  (((insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
        lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA
        ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare
        sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable minFI indMMUToPreparebool/\
      zeroI' = CIndex 0) /\
     isIndexValue newLastLLable zeroI' FFI s /\ isVA' newLastLLable FFI vavalue s) /\
    StateLib.Index.succ FFI = Some nextFFI) /\ isPP' newLastLLable nextFFI pgvalue s }} writeIndex newLastLLable zeroI' newFFI
 {{  fun _ s =>
   (((insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
        lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA
        ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare
        sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable minFI indMMUToPreparebool /\
      zeroI' = CIndex 0) /\
     isIndexValue newLastLLable zeroI' newFFI s /\ isVA' newLastLLable FFI vavalue s) /\
    StateLib.Index.succ FFI = Some nextFFI) /\ isPP' newLastLLable nextFFI pgvalue s }}.
Proof.
eapply weaken.
eapply WP.writeIndex.
simpl;intros.
assert(exists entry, 
 lookup newLastLLable zeroI' (memory s) beqPage beqIndex = Some (I entry)) as (entry & Hlookup).
{ intuition.
subst.
 assert(Hi :  isIndexValue newLastLLable (CIndex 0) FFI s) ;trivial.
 unfold isIndexValue in Hi.
 case_eq(lookup newLastLLable  (CIndex 0) (memory s) beqPage beqIndex);
  [intros v Hv |intros Hv];rewrite Hv in *;try now contradict Hi.
  destruct v;try now contradict Hv.
  subst.
 exists FFI;trivial. }
intuition.
subst.
apply insertEntryIntoLLPCUpdateLLIndex with entry minFI;trivial.
{ unfold insertEntryIntoLLPC, propagatedPropertiesPrepare in *.
  assert(exists NbFI : index, isIndexValue newLastLLable (CIndex 1) NbFI s /\ 
                NbFI >= minFI) as (nbFI & Hnbfi & Hnbfi1) by intuition.
  exists nbFI.
  split;trivial.
  apply isIndexValueUpdateLLIndex;trivial.
  right.
  pose proof tableSizeBigEnough.
  unfold tableSizeLowerBound in *.
  apply indexEqFalse;try omega. }
apply isIndexValueSameUpdateLLIndex ;trivial.
apply isVA'UpdateLLIndex with entry;trivial.
apply isPP'UpdateLLIndex with entry;trivial.
Qed.

Lemma  writeIndexUpdateLLContentOne  ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare 
ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD 
ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA 
zeroI lpred zeroI' newLastLLable FFI LLChildphy LLroot nextFFI newFFI oneI NbFI newNbFI vavalue pgvalue minFI indMMUToPreparebool: 
{{ fun s : state =>
   ((((((insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA
           phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA
           ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
           currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA
           idxTrdVA zeroI lpred LLroot LLChildphy newLastLLable minFI indMMUToPreparebool/\ 
         zeroI' = CIndex 0) /\
        isIndexValue newLastLLable zeroI' newFFI s /\ isVA' newLastLLable FFI vavalue s) /\
       StateLib.Index.succ FFI = Some nextFFI) /\ isPP' newLastLLable nextFFI pgvalue s) /\
     StateLib.Index.succ zeroI' = Some oneI) /\ isIndexValue newLastLLable oneI NbFI s) /\
   StateLib.Index.pred NbFI = Some newNbFI }} 
  writeIndex newLastLLable oneI newNbFI {{ fun (_ : unit) (s : state) =>
                                           insertEntryIntoLLPC s ptMMUTrdVA phySh2addr
                                             phySh1addr indMMUToPrepare ptMMUFstVA
                                             phyMMUaddr lastLLTable phyPDChild
                                             currentShadow2 phySh2Child currentPD ptSh1TrdVA
                                             ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1
                                             descChildphy phySh1Child currentPart trdVA
                                             nextVA vaToPrepare sndVA fstVA nbLgen l
                                             idxFstVA idxSndVA idxTrdVA zeroI lpred LLroot
                                             LLChildphy newLastLLable (CIndex (minFI-1)) indMMUToPreparebool}}.
Proof.
eapply weaken.
eapply WP.writeIndex.
simpl;intros.
assert(exists entry, 
 lookup newLastLLable oneI (memory s) beqPage beqIndex = Some (I entry)) as (entry & Hlookup).
{ intuition.
  subst.
 assert(Hi :  isIndexValue newLastLLable oneI NbFI s) ;trivial.
 unfold isIndexValue in Hi.
 case_eq(lookup newLastLLable  oneI (memory s) beqPage beqIndex);
  [intros v Hv |intros Hv];rewrite Hv in *;try now contradict Hi.
  destruct v;try now contradict Hv.
  subst.
 exists NbFI;trivial. }
intuition.
subst.
apply insertEntryIntoLLPCUpdateLLIndex with entry (minFI);trivial.
unfold insertEntryIntoLLPC,  propagatedPropertiesPrepare in *.
intuition.
assert(exists NbFI : index,
        isIndexValue newLastLLable (CIndex 1) NbFI s /\ NbFI >= minFI) as (nbFI & Hnbfi & Hnbfi1) by trivial.
exists newNbFI.
assert(Hsucc: StateLib.Index.succ (CIndex 0) = Some oneI) by trivial.
apply Succ0is1 in Hsucc.
subst.
split;trivial.
apply isIndexValueSameUpdateLLIndex.
subst.
assert(nbFI=NbFI).
{ unfold isIndexValue in *.
case_eq(lookup newLastLLable (CIndex 1) (memory s) beqPage beqIndex);[intros vi Hvi |intros Hvi];
rewrite Hvi in *;try now contradict Hnbfi.
destruct vi;try now contradict Hnbfi.
subst;trivial. }
subst.
assert(Hkey: StateLib.Index.pred NbFI = Some newNbFI) by trivial.
apply indexPredMinus1 in Hkey.
subst.
(* assert (Htodefine: minFi <=3). *)
revert Hnbfi1.
clear.
intros.
unfold CIndex.
case_eq(lt_dec (minFI - 1) tableSize);intros;simpl.
unfold CIndex in *.
case_eq(lt_dec (newNbFI - 1) tableSize);intros;rewrite H0 in *.
simpl in *.
omega.
destruct minFI;simpl in *;omega.
destruct minFI;simpl in *;omega.
Qed.                                             

Lemma insertEntryIntoLLHT  ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare 
ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD 
ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA 
zeroI lpred LLroot LLChildphy newLastLLable vavalue pgvalue minFI indMMUToPreparebool:
{{ fun s : state =>
   insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare 
ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD 
ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA 
zeroI lpred LLroot LLChildphy newLastLLable minFI indMMUToPreparebool}} 
insertEntryIntoLL newLastLLable vavalue pgvalue  
{{ fun _ s  => insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare 
ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD 
ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA 
zeroI lpred LLroot LLChildphy newLastLLable (CIndex(minFI -1)) indMMUToPreparebool}}.
Proof.
unfold insertEntryIntoLL. 
eapply bindRev.
(** Index.zero  **)
unfold Index.zero.
eapply weaken;simpl.
eapply Invariants.ret.
intros;simpl.
eapply H.
intros zeroI'.
simpl.
replace ( {| i := 0; Hi := MALInternal.Index.zero_obligation_1 |}) with (CIndex 0).
2:{ unfold CIndex. 
    case_eq(lt_dec 0 tableSize);intros;simpl.
    f_equal.
    apply proof_irrelevance.
    assert(tableSize > tableSizeLowerBound).
    apply tableSizeBigEnough.
    unfold tableSizeLowerBound in *.
    omega. }
(**  readIndex **)
eapply bindRev.
eapply weaken.
eapply Invariants.readIndex.
simpl;intros.
split. eapply H.
admit. (** Consistency not found : LLconfiguration3 *) 
intros FFI.
(** writeVirtual **)
eapply bindRev.
eapply weaken.
apply writeVirtualUpdateLLContent.
simpl;intros.
eassumption.
intros[].
(** Index.succ **)
eapply bindRev.
eapply weaken.
eapply Invariants.Index.succ.
simpl;intros.
split.
eapply H.
admit. (** Consistency not found : LLconfiguration4 (FFI < tableSize - 1) **)
intros nextFFI.
(**  readIndex  **)
eapply bindRev.
eapply weaken.
eapply Invariants.readIndex;simpl.
simpl;intros.
split. 
eapply H.
admit. (** Consistency not found : LLconfiguration4 (isI LLtable nextFFI s.) **) 
intros newFFI;simpl.
(** writePhysical **)
eapply bindRev.
eapply weaken.
apply writePhysicalUpdateLLContent with (zeroI':=zeroI').
intuition; subst;try eassumption.
subst;trivial.
intros [].
(** writeIndex **)
eapply bindRev.
eapply weaken.
eapply writeIndexUpdateLLContentZero.
intros.
simpl.
intuition;eassumption.
intros [].
(** Index.succ *)
eapply bindRev.
eapply weaken.
eapply Invariants.Index.succ.
simpl;intros.
split.
eapply H.
intuition;subst.
apply CIndex0lt.
intros oneI.
simpl.
(** readIndex **)
eapply bindRev.
eapply weaken.
eapply Invariants.readIndex.
intros;simpl.
split.
eapply H;simpl.
admit. (** Consistency not found : LLconfiguration1 (isI newLastLLable oneI s) **) 
intros NbFI.
simpl.
(** Index.pred NbFI *)
eapply bindRev.
eapply weaken.
eapply Invariants.Index.pred.
simpl.
intros.
split.
eapply H.
admit. (** Internal property not found : (NbFI > 0) **)
intros newNbFI.
simpl.
(** writeIndex **)
eapply weaken.
eapply strengthen.
eapply writeIndexUpdateLLContentOne with (zeroI':=zeroI');trivial.
intros.
simpl in *.
eassumption.
intros;simpl.
intuition ; try eassumption.
Admitted.