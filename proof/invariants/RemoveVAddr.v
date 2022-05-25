(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2021)                *)
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
    This file contains the invariant of [removeVAddr]. 
    We prove that this PIP service preserves the isolation property *)
Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.Lib
               Pip.Model.MAL Pip.Model.Constants Pip.Model.Ops.
Require Import Pip.Core.Internal Pip.Core.Services.
Require Import Pip.Proof.Consistency Pip.Proof.DependentTypeLemmas Pip.Proof.InternalLemmas
               Pip.Proof.Isolation Pip.Proof.StateLib Pip.Proof.WeakestPreconditions.
Require Import Invariants GetTableAddr WritePEntryRemoveVaddr PropagatedProperties
               UpdateShadow2Structure UpdateShadow1Structure.

Import Arith List Bool.

Lemma removeVAddr   (descChild : vaddr) (vaChild : vaddr) :
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }} 
removeVAddr descChild vaChild 
{{fun _ s  => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold removeVAddr.
(** checkKernelMap *)
eapply WP.bindRev.
eapply WP.weaken.   
eapply Invariants.checkKernelMap.
intros. simpl. pattern s in H. eexact H.
intros iskernelmap.
simpl.
case_eq iskernelmap; intros. 
(** ret iskernelmap *)
intros.
eapply WP.weaken.
eapply WP.ret .
simpl. intros.
intuition.
(** ret notkernelmap *)
(** getCurPartition **)
subst.
eapply WP.bindRev.
eapply WP.weaken. 
eapply Invariants.getCurPartition .
cbn. 
intros. 
pattern s in H. 
eexact H.
intro currentPart.
(** getNbLevel **)
eapply WP.bindRev.
eapply weaken.
eapply Invariants.getNbLevel.
simpl. intros.
pattern s in H.
eexact H.
intros level.
simpl.
subst.
(** checkChild **)
  unfold Internal.checkChild.
  rewrite assoc.
  eapply bindRev.
  (** getFstShadow **)
  eapply WP.weaken. 
  eapply Invariants.getFstShadow. cbn.
  intros s H.
  split.
  pattern s in H.
  eexact H.
  unfold consistency in *.
  unfold partitionDescriptorEntry in *.
  intuition.
  simpl.
  intros currentShadow1.
  rewrite assoc.
  (** StateLib.getIndexOfAddr **)                
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getIndexOfAddr.
  { simpl. intros.
    pattern s in H.
    eexact H.  }
  intro idxDescChild. simpl.
  rewrite assoc.
  (** getTableAddr **)
  eapply WP.bindRev.
  eapply WP.weaken. 
  apply getTableAddr.
  simpl.
  intros s H.
  split.
  pattern s in H. 
  eexact H. subst.
  split. 
  intuition.
  split. 
  instantiate (1:= currentPart).
  intuition. 
  subst.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *. 
  intuition.
  instantiate (1:= idxShadow1).
  split. intuition.
  assert(Hcons : consistency s) by intuition.
  assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
  assert(Hcp : currentPart = currentPartition s) by intuition.
  assert (H0 : nextEntryIsPP currentPart idxShadow1 currentShadow1 s) by intuition.
  exists currentShadow1.
  split. intuition.
  
  unfold consistency in *.
  destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
  unfold partitionDescriptorEntry in Hpd.
  assert (idxShadow1 = idxPageDir \/ idxShadow1 = idxShadow1 \/ idxShadow1 = idxShadow2 \/  idxShadow1  = idxShadow3
  \/  idxShadow1  = idxParentDesc \/  idxShadow1 = idxPartDesc) as Htmp 
  by auto.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
  generalize (Hpd idxShadow1 Htmp); clear Hpd; intros Hpd.
  destruct Hpd as (Hidxpd & _& Hentry). 
  destruct Hentry as (page1 & Hpd & Hnotnull).
  subst.
  split.
  unfold nextEntryIsPP in *. 
  destruct (StateLib.Index.succ idxShadow1); [ | now contradict H0].
  destruct (lookup (currentPartition s) i (memory s) pageEq idxEq) ; try now contradict H0.
  destruct v ; try now contradict H0.
  subst. assumption.
  subst. left. split;intuition.
  intro ptDescChild. simpl.
  (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2: {
  intros.
  destruct H as (H0 & H1).
  assert ( (getTableAddrRoot' ptDescChild idxShadow1 currentPart descChild s /\ ptDescChild = pageDefault) \/
  (forall idx : index,
  StateLib.getIndexOfAddr descChild levelMin = idx ->
  isVE ptDescChild idx s /\ getTableAddrRoot ptDescChild idxShadow1 currentPart descChild s  )).
  { destruct H1 as [H1 |(Hi & Hi1 & H1)].
    + left. trivial. 
    + right. intros idx Hidx.
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
      - split; assumption.
      - contradict Hfalse. 
        symmetrynot. 
        apply idxSh2idxSh1notEq.
      - contradict Hfalse. 
        symmetrynot. apply idxPDidxSh1notEq.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP. }
  rewrite assoc.
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptDescChildIsnull. simpl.
  case_eq ptDescChildIsnull.
  { intros.
    eapply WP.weaken.
    eapply WP.ret .
    simpl. intros.
    intuition. }
  intros HptDescChildIsnull. 
  subst.
  (* readPDflag *)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.readPDflag.
  simpl;intros.
  split.
  destruct H as (((Ha1 & Ha2) & Ha3) & Ha4).
  assert (Hnewget : isVE ptDescChild (StateLib.getIndexOfAddr descChild levelMin) s /\
       getTableAddrRoot ptDescChild idxShadow1 currentPart descChild s /\ 
       (pageDefault =? ptDescChild) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr descChild levelMin);trivial.
      intuition. }
  assert (HP := conj (conj Ha1 Ha2) Hnewget).
  pattern s in HP.
  eexact HP.
  destruct H as (H & Htrue).
  destruct H as (H & Hor).
  destruct Hor as [(Hor & Hfalse) | Hor].
  subst.
  apply beq_nat_false in Htrue.
  now contradict Htrue.
  destruct H as (H & Hidx).
  subst.
  destruct Hor with (StateLib.getIndexOfAddr descChild levelMin);
  trivial.
  intros ischild;simpl in *.
  intros.
(** end checkChild *)
case_eq (negb ischild); 
intros Hischild.
(** isnotchild *)
eapply weaken. eapply WP.ret;simpl; intuition. simpl. intuition.
(** is child *)
(** getPd **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getPd.
cbn.
intros s H.
split.
pattern s in H.
eexact H.
split.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
unfold consistency in *.
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
intuition.
intros currentPD.
(** getTableAddr **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
split. 
instantiate (1:= currentPart).
unfold consistency in *. 
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
intuition.
instantiate (1:= idxPageDir).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP currentPart idxPageDir currentPD s) by intuition.
exists currentPD.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2 \/  idxPageDir  = idxShadow3
\/  idxPageDir  = idxParentDesc \/  idxPageDir = idxPartDesc) as Htmp 
by auto.
    generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
generalize (Hpd idxPageDir Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
unfold nextEntryIsPP in *. 
destruct (StateLib.Index.succ idxPageDir); [ | now contradict H0].
destruct (lookup (currentPartition s) i (memory s) pageEq idxEq) ; try now contradict H0.
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptDescChildFromPD. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptDescChildFromPD idxPageDir currentPart descChild s /\ ptDescChildFromPD = pageDefault) \/
(forall idx : index,
StateLib.getIndexOfAddr descChild levelMin = idx ->
isPE ptDescChildFromPD idx s /\ getTableAddrRoot ptDescChildFromPD idxPageDir currentPart descChild s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
    - (*  split; assumption.
    - *) contradict Htrue.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - split;trivial. }
assert (HP := conj H0 H).
pattern s in HP.
eapply HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro ptDescChildFromPDIsnull. simpl.
case_eq ptDescChildFromPDIsnull.
{ intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition. }
intros HptDescChildFromPDNotNull. subst.   
(** StateLib.getIndexOfAddr **)                            
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getIndexOfAddr.
{ simpl. intros.
  destruct H as ((Ha1 & Ha3) & Ha4).
  assert (Hnewget : isPE ptDescChildFromPD 
  (StateLib.getIndexOfAddr descChild levelMin) s /\
       getTableAddrRoot ptDescChildFromPD idxPageDir currentPart descChild s /\ 
       (pageDefault =? ptDescChildFromPD) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr descChild levelMin);trivial.
      intuition. }
   subst.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  eexact HP. }
intro idxDescChild1.
simpl. 
(** readPresent **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPresent. simpl.
  intros.
  split.
  pattern s in H.
  eexact H. 
  intuition. subst;trivial. }
intros presentDescPhy. simpl.
case_eq (negb presentDescPhy);intros Hlegit;subst.
eapply weaken. eapply WP.ret. 
simpl. intros;intuition.
(** readPhyEntry **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPhyEntry. simpl.
  intros.
  split.
  pattern s in H.
  eapply H. 
  subst.
  intuition;subst;trivial. }
intros phyDescChild. simpl.
(** getPd **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getPd.
cbn.
intros s H.
apply negb_false_iff in Hischild.
subst.
(** descChild is a child *)
assert(Hchildren : In phyDescChild (getChildren (currentPartition s) s)).
{ unfold getChildren.
  assert(Hlevel : Some level = StateLib.getNbLevel) by intuition.
  rewrite <- Hlevel.
  assert(Hcurpd : StateLib.getPd currentPart (memory s) = Some currentPD).
  { apply nextEntryIsPPgetPd.
    intuition. }
  assert (Heq : currentPartition s = currentPart) by intuition.
  subst.
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
assert(Hnewgoal : getMappedPage currentPD s descChild = SomePage phyDescChild). 
{  apply getMappedPageGetTableRoot with ptDescChildFromPD (currentPartition s); intuition;
  subst;trivial.
  apply negb_false_iff in Hlegit.
  subst;trivial. }
  rewrite <- Hnewgoal.
  symmetry.
  apply getMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
  apply getNbLevelEqOption.
  unfold getPdsVAddr.
  apply filter_In.
  split;trivial. 
  assert(Hnewgoal : checkChild (currentPartition s) level s descChild = true).
  { unfold checkChild. 
  assert(Hcursh1 : StateLib.getFstShadow (currentPartition s) (memory s) = Some currentShadow1).
  { apply nextEntryIsPPgetFstShadow. intuition; subst;trivial. }
  rewrite Hcursh1.
  assert(Hpt :getIndirection currentShadow1 descChild level (nbLevel - 1) s  = Some ptDescChild). 
  { apply getIndirectionGetTableRoot with (currentPartition s);intuition.
    subst;trivial. }
  rewrite Hpt.
  assert(Htrue : (ptDescChild =? pageDefault) = false ). 
  { rewrite Nat.eqb_neq in *.
    assert(Hfalse: (pageDefault =? ptDescChild) = false) by intuition.
    apply beq_nat_false in Hfalse.  intuition. }
  rewrite Htrue.
  assert(Hpdchild :  entryPDFlag ptDescChild idxDescChild true s) by intuition.
  assert(Hpdtrue : StateLib.readPDflag ptDescChild
    (StateLib.getIndexOfAddr descChild levelMin) (memory s) = Some true).
  { unfold StateLib.readPDflag, entryPDFlag in *.
    intuition. subst.
    destruct (lookup ptDescChild (StateLib.getIndexOfAddr descChild levelMin) (memory s) pageEq idxEq );
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
  inversion Hlevel;trivial. }
split. 
assert(Hnew := conj H Hchildren).  
pattern s in Hnew.
eexact Hnew.
split.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
unfold consistency in *.
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
apply childrenPartitionInPartitionList with (currentPartition s); intuition.
intros pdChildphy.
simpl.
(** StateLib.getIndexOfAddr **)                
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getIndexOfAddr.
{ simpl. intros.
  pattern s in H.
  eexact H.  }
intro idxvaChild. simpl.
(** getTableAddr : to check if the virtual address is mapped in the child  **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
assert(Hchildpart : In phyDescChild (getPartitions pageRootPartition s)). 
{ unfold consistency in *. 
  apply childrenPartitionInPartitionList with currentPart; intuition.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  subst;trivial. }
split. 
instantiate (1:= phyDescChild );trivial.
instantiate (1:= idxPageDir).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP phyDescChild idxPageDir pdChildphy s) by intuition.
exists pdChildphy.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (idxPageDir = idxPageDir \/ idxPageDir = idxShadow1 \/ idxPageDir = idxShadow2 \/  idxPageDir  = idxShadow3
\/  idxPageDir  = idxParentDesc \/  idxPageDir = idxPartDesc) as Htmp 
by auto.
    generalize (Hpd  phyDescChild  Hchildpart); clear Hpd; intros Hpd.
generalize (Hpd idxPageDir Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.

unfold nextEntryIsPP in *. 
destruct (StateLib.Index.succ idxPageDir); [ | now contradict H0].
destruct (lookup phyDescChild i (memory s) pageEq idxEq) ; try now contradict H0.
destruct v ; try now contradict H0.
subst ; assumption.
subst. left. split;intuition.
intro ptVaChildpd. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptVaChildpd idxPageDir phyDescChild vaChild s /\ ptVaChildpd = pageDefault) \/
(forall idx : index,
StateLib.getIndexOfAddr vaChild levelMin = idx ->
isPE ptVaChildpd idx s /\ getTableAddrRoot ptVaChildpd idxPageDir phyDescChild vaChild s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
    - (*  split; assumption.
    - *) contradict Htrue.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - split;trivial. }
assert (HP := conj H0 H).
pattern s in HP.
exact HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro ptVaChildpdIsnull. simpl.
case_eq ptVaChildpdIsnull.
{ intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition. }
intros HptVaChildpdIsnull. subst.
 
(** readAccessible **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readAccessible. simpl.
  intros.
  destruct H as ((Ha1 & Ha3) & Ha4).
  assert (Hnewget : isPE ptVaChildpd (
  StateLib.getIndexOfAddr vaChild levelMin) s /\
       getTableAddrRoot ptVaChildpd idxPageDir phyDescChild
         vaChild s /\ 
       (pageDefault =? ptVaChildpd) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr vaChild levelMin);trivial.
      intuition. }
   subst.
 split.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  eexact HP. clear Ha3. 
  intuition. subst;trivial. }
intros access. simpl.
(** readPresent **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPresent. simpl.
  intros.
  split.
  pattern s in H.
  eexact H. 
  intuition. subst;trivial. }
intros present. simpl.
(** getFstShadow **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getFstShadow1. cbn.
intros s H.
split.
pattern s in H.
eexact H.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
{ unfold consistency in *. 
  apply childrenPartitionInPartitionList with currentPart; intuition.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  subst;trivial. }
intros shadow1Child.
(** getTableAddr **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
split. 
instantiate (1:= phyDescChild).
unfold consistency in *. 
unfold  currentPartitionInPartitionsList in *.
subst.
intuition.
{ unfold consistency in *. 
  apply childrenPartitionInPartitionList with currentPart; intuition.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  subst;trivial. }
instantiate (1:= idxShadow1).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition.
(*  
assert(Hcp : currentPart = currentPartition s) by intuition. *)
assert (H0 : nextEntryIsPP phyDescChild idxShadow1 shadow1Child s) by intuition.
exists shadow1Child.
split. intuition.
unfold consistency in *.

destruct Hcons as (Hpd & _ ).
assert(Hpr : In phyDescChild (getPartitions pageRootPartition s)). 
 { unfold consistency in *. 
  apply childrenPartitionInPartitionList with currentPart; intuition.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  subst;trivial. }
unfold partitionDescriptorEntry in Hpd.
assert (idxShadow1 = idxPageDir \/ idxShadow1 = idxShadow1 \/ idxShadow1 = idxShadow2 \/  idxShadow1  = idxShadow3
\/  idxShadow1  = idxParentDesc \/  idxShadow1 = idxPartDesc) as Htmp 
by auto.
    generalize (Hpd  phyDescChild  Hpr); clear Hpd; intros Hpd.
generalize (Hpd idxShadow1 Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.

unfold nextEntryIsPP in *. 
destruct (StateLib.Index.succ idxShadow1); [ | now contradict H0].
destruct (lookup phyDescChild i (memory s) pageEq idxEq) ; try now contradict H0.
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptVaChildFromSh1. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptVaChildFromSh1 idxShadow1 phyDescChild vaChild s /\ ptVaChildFromSh1 = pageDefault) \/
(forall idx : index,
StateLib.getIndexOfAddr vaChild levelMin = idx ->
isVE ptVaChildFromSh1 idx s /\ getTableAddrRoot ptVaChildFromSh1 idxShadow1 phyDescChild vaChild s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
    - split; assumption.
    - contradict Hfalse. 
      symmetrynot. 
      apply idxSh2idxSh1notEq.
    - contradict Hfalse. 
      symmetrynot. apply idxPDidxSh1notEq.  }
assert (HP := conj H0 H).
pattern s in HP.
eapply HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro childListSh1Isnull. simpl.
case_eq childListSh1Isnull.
{ intros. eapply WP.weaken.  eapply WP.ret . simpl. intros.
 pattern false, s in H0.
 eapply H0. }
intros HptVaChildFromSh1NotNull. clear HptVaChildFromSh1NotNull.

(** checkDerivation **)
unfold Internal.checkDerivation.
rewrite assoc.
(** readVirEntry **)
eapply WP.bindRev.
{ eapply WP.weaken.
eapply Invariants.readVirEntry.
  intros.
  destruct H as ((Ha1 & Ha3) & Ha4).

  assert (Hnewget : isVE ptVaChildFromSh1 (
  StateLib.getIndexOfAddr vaChild levelMin) s /\
       getTableAddrRoot ptVaChildFromSh1 idxShadow1 phyDescChild vaChild s /\ 
       (pageDefault =? ptVaChildFromSh1) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr vaChild levelMin);trivial.
      intuition. }
   subst.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  split.
  eexact HP.  clear Ha3. 
  intuition. subst;trivial. }
intros vainve. simpl.
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.compareVAddrToNull.
intro isnotderiv. simpl.
case_eq(access && isnotderiv && present); intros Hi;[|
(** if accessible, present and not shared  = false**)
eapply weaken;[ eapply WP.ret;simpl; intuition |simpl; intuition]].
(** if accessible, present and not shared **)
apply andb_true_iff in Hi; destruct Hi as (Hii & Hpresent);
apply andb_true_iff in Hii; destruct Hii as (Haccess & Hderived).
subst. 
(** getSndShadow **)
eapply bindRev.
eapply weaken.
eapply Invariants.getSndShadow.
simpl;intros.
split. 
pattern s in H. 
exact H.
split. trivial.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
assert(Hchildpart : In phyDescChild (getPartitions pageRootPartition s)). 
{ unfold consistency in *. 
  apply childrenPartitionInPartitionList with currentPart; intuition.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  subst;trivial. }
unfold consistency in *.
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
apply childrenPartitionInPartitionList with (currentPartition s); intuition.
intros sh2Childphy.
simpl.
(** getTableAddr : to access to the second shadow page table  **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
assert(Hchildpart : In phyDescChild (getPartitions pageRootPartition s)). 
{ unfold consistency in *. 
  apply childrenPartitionInPartitionList with currentPart; intuition.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  subst;trivial. }
split. 
instantiate (1:= phyDescChild );trivial.
instantiate (1:= idxShadow2).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP phyDescChild idxShadow2 sh2Childphy s) by intuition.
exists sh2Childphy.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (idxShadow2 = idxPageDir \/ idxShadow2 = idxShadow1 \/ idxShadow2 = idxShadow2 \/  idxShadow2  = idxShadow3
\/  idxShadow2  = idxParentDesc \/  idxShadow2 = idxPartDesc) as Htmp 
by auto.
generalize (Hpd  phyDescChild  Hchildpart); clear Hpd; intros Hpd.
generalize (Hpd idxShadow2 Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.

unfold nextEntryIsPP in *. 
destruct (StateLib.Index.succ idxShadow2); [ | now contradict H0].
destruct (lookup phyDescChild i (memory s) pageEq idxEq) ; try now contradict H0.
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptVaChildsh2. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptVaChildsh2 idxShadow2 phyDescChild vaChild s /\ ptVaChildsh2 = pageDefault) \/
(forall idx : index,
StateLib.getIndexOfAddr vaChild levelMin = idx ->
isVA ptVaChildsh2 idx s /\ getTableAddrRoot ptVaChildsh2 idxShadow2 phyDescChild vaChild s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
    - (*  split; assumption.
    - *) contradict Htrue.
      apply idxSh2idxSh1notEq.
    - split;trivial.
    - contradict Hfalse.
      symmetrynot.
      apply idxPDidxSh2notEq. }
assert (HP := conj H0 H).
pattern s in HP.
exact HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro ptVaChildpdIsnull. simpl.
case_eq ptVaChildpdIsnull.
{ intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition. }
intros HptVaChildpdIsnull. subst.
(** readVirtual **) 
eapply WP.bindRev.
eapply weaken.
eapply Invariants.readVirtual.
simpl. intros. 
destruct H as ((Ha1 & Ha3) & Ha4).
assert (Hnewget : isVA ptVaChildsh2 (
 StateLib.getIndexOfAddr vaChild levelMin) s /\
       getTableAddrRoot ptVaChildsh2 idxShadow2 phyDescChild vaChild s /\ 
       (pageDefault =? ptVaChildsh2) = false).
{ destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
  + subst.
    apply beq_nat_false in Ha4.
    now contradict Ha4.
  + destruct Ha3 with (StateLib.getIndexOfAddr vaChild levelMin);trivial.
    intuition. }
subst.
assert (HP := conj Ha1 Hnewget).
pattern s in HP.
split.
eexact HP.  clear Ha3. 
intuition. subst;trivial.
intros vainparent. simpl.
(** getFstShadow **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getFstShadow. cbn.
intros s H.
split.
pattern s in H.
eexact H.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
intros currentShadow.
(** getTableAddr **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
assert(Hsh1eq : currentShadow = currentShadow1).
apply getSh1NextEntryIsPPEq with currentPart s;trivial.
intuition.
apply nextEntryIsPPgetFstShadow;intuition.
subst currentShadow1.
destruct H as (H & _).
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
split. 
instantiate (1:= currentPart).
unfold consistency in *. 
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
intuition.
instantiate (1:= idxShadow1).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP currentPart idxShadow1 currentShadow s) by intuition.
exists currentShadow.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (idxShadow1 = idxPageDir \/ idxShadow1 = idxShadow1 \/ idxShadow1 = idxShadow2 \/  idxShadow1  = idxShadow3
\/  idxShadow1  = idxParentDesc \/  idxShadow1 = idxPartDesc) as Htmp 
by auto.
    generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
generalize (Hpd idxShadow1 Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.

unfold nextEntryIsPP in *. 
destruct (StateLib.Index.succ idxShadow1); [ | now contradict H0].
destruct (lookup (currentPartition s) i (memory s) pageEq idxEq) ; try now contradict H0.
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptVaInCurPart. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptVaInCurPart idxShadow1 currentPart vainparent s /\ ptVaInCurPart = pageDefault) \/
(forall idx : index,
StateLib.getIndexOfAddr vainparent levelMin = idx ->
isVE ptVaInCurPart idx s /\ getTableAddrRoot ptVaInCurPart idxShadow1 currentPart vainparent s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
    - split; assumption.
    - contradict Hfalse. 
      symmetrynot. 
      apply idxSh2idxSh1notEq.
    - contradict Hfalse. 
      symmetrynot. apply idxPDidxSh1notEq.  }
assert (HP := conj H0 H).
pattern s in HP.
eapply HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro notnull. simpl.
case_eq notnull.
{ intros. eapply WP.weaken.  eapply WP.ret . simpl. intros.
 pattern false, s in H0.
 eapply H0. }
intros HptVaInCurPartNotNull. subst.
(** StateLib.getIndexOfAddr **)                
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getIndexOfAddr.
{ simpl. intros.
    destruct H as ((Ha1  & Ha3) & Ha4).
  assert (Hnewget : isVE ptVaInCurPart (
  StateLib.getIndexOfAddr vainparent levelMin) s /\
       getTableAddrRoot ptVaInCurPart idxShadow1 currentPart vainparent s /\ 
       (pageDefault =? ptVaInCurPart) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr vainparent levelMin);trivial.
      intuition. }
   subst.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  eexact HP.  }
intro idxvainparent.
simpl.
(** getDefaultVAddr **)
eapply WP.bindRev.
eapply weaken.
eapply getDefaultVAddr.
simpl.
intros .
pattern s in H.
eapply H.
simpl;intros defautvaddr.
(** getDefaultPage **)
apply negb_false_iff in Hischild;subst.
apply negb_false_iff in Hlegit;subst.
eapply WP.bindRev.
eapply weaken.
eapply Invariants.getDefaultPage.
intros.
simpl.
pattern s in H.
eapply H.
simpl;intros defaultpage.
(** writePhyEntry **)
eapply WP.bindRev.
eapply weaken.
apply writePhyEntryRemoveMMUPage.
intros.
simpl.
split.
destruct H as ((H  & H2) & H3).
try repeat rewrite and_assoc in H.
unfold propagatedPropertiesRemoveVaddr.
exact H.
split.
unfold propagatedPropertiesRemoveVaddr in *.
apply H.
intuition.
intros [].
(** writeVirtual **)
eapply WP.bindRev.
eapply weaken.
apply writeVirtualRemoveVaddr.
intros.
simpl.
eexact H.
intros[].
(** writePhyEntry **)

eapply WP.bindRev.
eapply weaken.
apply writeVirEntryRemoveVaddr.
intros.
simpl.
destruct H as (Ha & Hb & Hc).
split.
eexact Ha.
split.
unfold propagatedPropertiesRemoveVaddr in *.
intuition.
subst.
trivial. 
intros[].
(* ret **)
eapply weaken.
eapply WP.ret.
simpl.
intros;trivial.
Qed.

