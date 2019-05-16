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
DependentTypeLemmas Model.Lib InternalLemmas PropagatedProperties UpdateShadow2Structure.
Require Import Coq.Logic.ProofIrrelevance Omega List Bool.
(************************** TO MOVE ******************************)
(*%%%%%%%%%%%%Consistency%%%%%%%%%%%*)
Definition LLconfiguration3 s:=
forall part fstLL LLtable,
In part (getPartitions multiplexer s) -> 
nextEntryIsPP part sh3idx fstLL s ->  
In LLtable (getTrdShadows part s nbPage) -> 
isI LLtable (CIndex 0) s.

Definition LLconfiguration4 s:=
forall part fstLL LLtable,
In part (getPartitions multiplexer s) -> 
nextEntryIsPP part sh3idx fstLL s ->  
In LLtable (getTrdShadows part s nbPage) -> 
exists FFI,
StateLib.readIndex LLtable (CIndex 0) (memory s)= Some FFI /\
isVA LLtable FFI s.
(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)

(*%%%%%%%%%%%%%InternalLemmas%%%%%%%%%%%*)
 Lemma pdPartNotNone phyDescChild s:
In phyDescChild (getPartitions multiplexer s) -> 
partitionDescriptorEntry s -> 
StateLib.getPd phyDescChild (memory s) = None -> False.
Proof.
intros. 
unfold partitionDescriptorEntry in *. 
  assert(Hexist : (exists entry : page,
          nextEntryIsPP phyDescChild PDidx entry s /\ entry <> defaultPage)).
        apply H0;trivial.
        left;trivial.
        destruct Hexist as (entryPd & Hpp & Hnotnull).
apply nextEntryIsPPgetPd in Hpp.
rewrite Hpp in *.
now contradict H1.
Qed.

Lemma disjointSh2LLstruct tbl newLastLLable sh2 LL partition s: 
getSndShadow partition (memory s) = Some sh2 ->
getConfigTablesLinkedList partition (memory s) = Some LL -> 
consistency s ->
In partition (getPartitions multiplexer s) ->
In tbl (getIndirections sh2 s) ->
In newLastLLable (getTrdShadows LL s (nbPage + 1)) -> 
NoDup (getConfigPagesAux partition s) -> tbl <> newLastLLable.
Proof.
intros Hsh2 HLL Hcons Hpart Hi1 Hi2 Hnodup. 
unfold getConfigPagesAux in Hnodup.
case_eq(StateLib.getPd partition (memory s));intros pd Hpd.
2:{ assert False. apply pdPartNotNone with partition s;trivial. 
    unfold consistency in *;intuition. auto. }
rewrite Hpd in Hnodup.    
case_eq(getFstShadow  partition (memory s));intros sh1 Hsh1.
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

(*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*)
Definition insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare 
ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD 
ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA 
zeroI lpred:=
propagatedPropertiesPrepare s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
     currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
     currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l false false false false false false idxFstVA idxSndVA idxTrdVA zeroI /\
writeAccessibleRecPreparePostconditionAll currentPart phyMMUaddr phySh1addr phySh2addr s /\
StateLib.Level.pred l = Some lpred /\
isWellFormedTables phyMMUaddr phySh1addr phySh2addr lpred s /\
isEntryVA ptSh1FstVA idxFstVA fstVA s /\ isEntryVA ptSh1SndVA idxSndVA sndVA s /\ isEntryVA ptSh1TrdVA idxTrdVA trdVA s.
(********************************************************************)
Lemma getVirtualAddressSh2UpdateLLContent newLastLLable FFI x sh2 va entry LL partition s:
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
getConfigTablesLinkedList partition (memory s) = Some LL -> 
In newLastLLable (getTrdShadows LL s (nbPage + 1)) ->
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
In newLastLLable (getTrdShadows LL s (nbPage + 1)) ->
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
In newLastLLable (getTrdShadows LLDescChild s (nbPage + 1)) ->
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
In newLastLLable (getTrdShadows LLDescChild s (nbPage + 1)) ->
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
In newLastLLable (getTrdShadows LLDescChild s (nbPage + 1)) ->
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
In newLastLLable (getTrdShadows LLDescChild s (nbPage + 1)) ->
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
In newLastLLable (getTrdShadows LLDescChild s (nbPage + 1)) ->
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

Lemma propagatedPropertiesPrepareUpdateLLContent s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
      lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
      ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
      vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI  newLastLLable FFI x entry (LLDescChild:page):
lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
propagatedPropertiesPrepare
 s ptMMUTrdVA
  phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child
  currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l false false false false false false idxFstVA idxSndVA idxTrdVA zeroI ->
propagatedPropertiesPrepare
  {| currentPartition := currentPartition s; memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |} ptMMUTrdVA
  phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child
  currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
  vaToPrepare sndVA fstVA nbLgen l false false false false false false idxFstVA idxSndVA idxTrdVA zeroI.
Proof.
unfold propagatedPropertiesPrepare;intros.
intuition;subst.
apply kernelDataIsolationUpdateSh2 with entry;trivial.
apply partitionsIsolationUpdateSh2 with entry;trivial.
apply verticalSharingUpdateSh2 with entry; trivial.
apply consistencyUpdateLLContent with descChildphy LLDescChild entry;trivial.
admit. (** getConfigTablesLinkedList descChildphy (memory s) = Some LLDescChild **)
admit. (** In newLastLLable (getTrdShadows LLDescChild s (nbPage + 1)) *)
Admitted.

Lemma insertEntryIntoLLPCUpdateLLContent s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
      lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
      ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
      vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred newLastLLable FFI x entry:
      lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry) ->
insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr
      lastLLTable phyPDChild currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA
      ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA
      vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred ->
insertEntryIntoLLPC
  {|
  currentPartition := currentPartition s;
  memory := add newLastLLable FFI (VA x) (memory s) beqPage beqIndex |} ptMMUTrdVA
  phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
  currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA
  currentShadow1 descChildphy phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA
  nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred.
Proof.
unfold insertEntryIntoLLPC;intros.
intuition.
Admitted.
  
  
  
Lemma writeVirtualUpdateLLContent ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare 
ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD 
ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA 
zeroI lpred zeroI' newLastLLable FFI:
{{ fun s : state =>
   (insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy
      phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred /\
    zeroI' = CIndex 0) /\ isIndexValue newLastLLable zeroI' FFI s }} writeVirtual newLastLLable FFI fstVA
 {{ fun _ s=>
   (insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare ptMMUFstVA phyMMUaddr lastLLTable phyPDChild
      currentShadow2 phySh2Child currentPD ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy
      phySh1Child currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l idxFstVA idxSndVA idxTrdVA zeroI lpred /\
    zeroI' = CIndex 0) /\ isIndexValue newLastLLable zeroI' FFI s }}.
Proof.
eapply weaken.
eapply WP.writeVirtual.
simpl;intros.
assert(Hlookup :exists entry, 
 lookup newLastLLable FFI (memory s) beqPage beqIndex = Some (VA entry)).
 admit. (** Consistency not found : LLconfiguration4 *) 
destruct Hlookup as (entry & Hlookup). 
intuition.
Admitted.
 
 
Lemma insertEntryIntoLLHT  ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare 
ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD 
ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA 
zeroI lpred newLastLLable:
{{ fun s : state =>
   insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare 
ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD 
ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA 
zeroI lpred }} 
insertEntryIntoLL newLastLLable fstVA phyMMUaddr  
{{ fun _ s  => insertEntryIntoLLPC s ptMMUTrdVA phySh2addr phySh1addr indMMUToPrepare 
ptMMUFstVA phyMMUaddr lastLLTable phyPDChild currentShadow2 phySh2Child currentPD 
ptSh1TrdVA ptMMUSndVA ptSh1SndVA ptSh1FstVA currentShadow1 descChildphy phySh1Child
currentPart trdVA nextVA vaToPrepare sndVA fstVA nbLgen l  idxFstVA idxSndVA idxTrdVA 
zeroI lpred}}.
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




Admitted.