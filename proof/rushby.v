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

Require Import Pip.Model.ADT Pip.Model.Hardware Pip.Model.MMU Pip.Model.MAL Pip.Model.Lib.
Require Import Pip.Core.Services Pip.Core.Internal.

Require Import Pip.Proof.StateLib Pip.Proof.Isolation Pip.Proof.InternalLemmas Pip.Proof.Consistency.
Require Import Pip.Proof.DependentTypeLemmas.

Require Import GetTableAddr Invariants.

Require Import List Classical_Prop Lia EqNat.

(* Definition writeUser (partition: page) (va : vaddr) (v : page) s:=
 match  StateLib.getPd partition (memory s), StateLib.getNbLevel  with 
 | Some currentPD, Some nbL => 
  match runvalue (translate currentPD va nbL) s with 
  | Some phypage => 
   match runvalue (comparePageToNull phypage) s with
   | Some isNull =>  
   if isNull then ret tt else
   writePhysical phypage (nth nbLevel va defaultIndex) v 
   | _ => ret tt
   end
 | _ => ret tt
 end
 |_ , _ => ret tt 
 end. *)

Definition observation (partition : page) s: list page :=
getAccessibleMappedPages partition s.

Lemma MMUSimulation pd va l : 
 translateAux nbLevel pd va l = getTableAddrAux nbLevel pd va l.
Proof.
destruct nbLevel;simpl;trivial.
Qed.

Lemma comparePageToNullEq : 
MMU.comparePageToNull = Internal.comparePageToNull.
Proof.
unfold MMU.comparePageToNull;unfold Internal.comparePageToNull;trivial.
Qed.

Lemma getIndexOfAddrEq :
MMU.getIndexOfAddr = MAL.getIndexOfAddr.
Proof.
unfold MAL.getIndexOfAddr;unfold MMU.getIndexOfAddr;trivial.
Qed.

Lemma readPresentEq : 
MMU.readPresent = MAL.readPresent.
Proof.
unfold MMU.readPresent;unfold MAL.readPresent;trivial.
Qed.

Lemma readAccessibleEq : 
MMU.readAccessible = MAL.readAccessible.
Proof.
unfold MMU.readAccessible;unfold MAL.readAccessible;trivial.
Qed.
Lemma readPhyEntryEq : 
MMU.readPhyEntry = MAL.readPhyEntry.
Proof.
unfold MMU.readPhyEntry;unfold MAL.readPhyEntry;trivial.
Qed.

(* Definition translate1(pd : page) (va : vaddr) (l : level) s := 
match runvalue (translateAux nbLevel pd va l ) s with
|None => 
|Some lastTable => match  runvalue (comparePageToNull lastTable) s
let isNull :=  in
if isNull then defaultPage else
let idx := runvalue( getIndexOfAddr va fstLevel) s in
 runvalue(readPhyEntry lastTable idx) s. *)
Lemma translateMappedPage : 
forall partition phypage va pd nbL s,
In partition (getPartitions pageRootPartition s) -> 
consistency s ->
phypage <> pageDefault -> 
StateLib.getPd partition (memory s)  = Some pd -> 
StateLib.getNbLevel = Some nbL -> 
runvalue (translate pd va nbL) s = Some (Some phypage) -> 
In phypage (observation partition s).
Proof.
intros partition phypage va pd nbL s Hparttree Hcons Hnotdefault.
intros.
assert(HgetTableAddr :forall P currentPart idxroot
indirection l,  {{fun s => P s /\consistency s /\ In currentPart (getPartitions pageRootPartition s) /\
            (idxroot = idxPageDir \/ idxroot = idxShadow1 \/ idxroot = idxShadow2)/\
            ( exists (tableroot : page), 
                nextEntryIsPP currentPart idxroot tableroot s/\
                tableroot <> pageDefault /\  
                ( (tableroot = indirection /\ Some l = StateLib.getNbLevel ) \/
                (exists nbL stop, Some nbL = StateLib.getNbLevel /\ stop <= nbL /\
                StateLib.getIndirection tableroot va nbL stop s = Some indirection /\
                indirection <> pageDefault  /\ 
                l = CLevel (nbL - stop)))) }}

Internal.getTableAddr indirection va l

{{fun (table : page) (s : state) =>  P s/\ 
                 (getTableAddrRoot' table idxroot currentPart va s /\ table = pageDefault \/ 
                 (getTableAddrRoot table idxroot currentPart va s /\  table<> pageDefault  /\ 
                    ( forall idx,  StateLib.getIndexOfAddr va levelMin = idx -> 
                    ( (isVE table idx s /\ idxroot = idxShadow1) \/ 
                      (isVA table idx s /\ idxroot = idxShadow2) \/
                      (isPE table idx s /\ idxroot = idxPageDir) )  ) ) )
 }}).
intros.
apply getTableAddr.
generalize (HgetTableAddr (fun s' => s = s' ) partition idxPageDir pd nbL s); 
clear HgetTableAddr; intros Hx.
unfold hoareTriple in *.
unfold Internal.getTableAddr in *. 
case_eq(getTableAddrAux nbLevel pd va nbL s);intros; rewrite H2 in *.
+ assert(let (a, s') := p in
     s = s' /\
     (getTableAddrRoot' a idxPageDir partition va s' /\ a = pageDefault \/
      getTableAddrRoot a idxPageDir partition va s' /\
      a <> pageDefault /\
      (forall idx : index,
       StateLib.getIndexOfAddr va levelMin = idx ->
       isVE a idx s' /\ idxPageDir = idxShadow1 \/
       isVA a idx s' /\ idxPageDir = idxShadow2 \/ isPE a idx s' /\ idxPageDir = idxPageDir))).
  { apply Hx.
    split;trivial.
    split;trivial.
    split;trivial.
    split. 
    left;trivial.
    exists pd.
    split. 
    apply nextEntryIsPPgetPd;trivial.
    split.
    apply pdPartNotNull with partition s;trivial.
    apply nextEntryIsPPgetPd;trivial.
    unfold consistency in *;intuition.
    left;trivial.
    split;trivial.
    symmetry;trivial. }
  clear Hx.
  destruct p.
  destruct H3 as (Hs & H3).
  destruct H3 as [(H3 & Hdef)| (H3 & Hdef & _)].
  * subst s0.
  unfold runvalue in *.
  case_eq(translate pd va nbL s); intros; rewrite H4 in *.
  destruct p0.
  subst.
  inversion H1; subst.
  unfold translate in *.
  unfold bind in *.
  rewrite MMUSimulation in *.
  rewrite H2 in *.
  case_eq(MMU.comparePageToNull pageDefault s);intros;rewrite H5 in *.
  destruct p.
  case_eq b;intros;subst;
  unfold MMU.comparePageToNull in *;
  unfold bind in *;
  case_eq(getPageDefault s);intros;rewrite H6 in *.
  -
  destruct p.
  unfold getPageDefault in *.
  simpl in *.
  unfold Hardware.ret in *.
  inversion H4;subst;clear H4. (* 
  inversion H6;subst;clear H6.
  now contradict Hnotdefault. *)
  -
  now contradict H5.
  - destruct p.
    unfold pageEqM in *.
    unfold Hardware.ret in *.
    inversion H5;subst;clear H5.
    unfold getPageDefault in *.
  simpl in *.
  unfold Hardware.ret in *.
  inversion H6;subst;clear H6.
  apply beq_nat_false in H8.
  now contradict H8.
  - now contradict H5.
  - now contradict H4.
  - now contradict H1.
  * subst s0.
  unfold runvalue in *.
  case_eq(translate pd va nbL s); intros; rewrite H4 in *;try now contradict H1.
  destruct p0.
  inversion H1; subst.
  unfold translate in *.
  unfold bind in *.
  rewrite MMUSimulation in *.
  rewrite H2 in *.
  case_eq(MMU.comparePageToNull p s);intros;rewrite H5 in *;try now contradict H4.
  destruct p0.
  case_eq b;intros;subst;
  unfold MMU.comparePageToNull in *;
  unfold bind in *;
  case_eq(getPageDefault s);intros;rewrite H6 in *.
  -
  destruct p0.
  unfold getPageDefault in *.
  simpl in *.
  unfold Hardware.ret in *.
  inversion H4;subst;clear H4.
  (* 
  inversion H6;subst;clear H6.
  now contradict Hnotdefault. *)
  -
  now contradict H5.
  - destruct p0.
    unfold pageEqM in *.
    unfold Hardware.ret in *.
    inversion H5;subst;clear H5.
    unfold getPageDefault in *.
    simpl in *.
    unfold Hardware.ret in *.
    inversion H6;subst;clear H6.
    case_eq(MMU.readPresent p (nth (length va - (levelMin + 2)) va idxDefault)
         s1);intros;rewrite H5 in *;try now contradict H4.
    destruct p0.
    case_eq( MMU.readAccessible p
         (nth (length va - (levelMin + 2)) va idxDefault) s);intros;
         rewrite H6 in *;try now contradict H4.
    destruct p0.
    case_eq (b && b0)%bool; intros Hbool;intros;subst;
    rewrite Hbool in *; [|inversion H4; try now contradict H4 ].
    apply Bool.andb_true_iff in Hbool as (Hb & Hb0); subst.
    case_eq(MMU.readPhyEntry p (nth (length va - (levelMin + 2)) va idxDefault)
         s2); [intros (ax & sx) Hx| intros ax sx  Hx]; rewrite Hx in *;inversion H4;subst;
    try now contradict H4. 
    clear H4.
    unfold observation.
    unfold getAccessibleMappedPages.
    rewrite H.
    unfold getAccessibleMappedPagesAux.
    apply filterOptionInIff.
    unfold getAccessibleMappedPagesOption.
    apply in_map_iff.
    assert(Heqvars : exists va1, In va1 getAllVAddrWithOffset0 /\ 
    StateLib.checkVAddrsEqualityWOOffset nbLevel va va1 ( CLevel (nbLevel -1) ) = true )
    by apply AllVAddrWithOffset0.
    destruct Heqvars as (va1 & Hva1 & Hva11).  
    exists va1.
    split;trivial.
    assert(getAccessibleMappedPage pd s1 va = SomePage phypage).
    { 
    unfold MMU.readPresent in *.
    unfold bind in *.
    case_eq(get s1);intros ss Hgets1;[| intros Hundef; unfold get in *;now contradict Hundef].
    unfold get in *.
    clear Hgets1.    
    case_eq(lookup p (nth (length va - (levelMin + 2)) va idxDefault)
         (memory s1) pageEq idxEq); 
      [intros v Hpresent |intros Hpresent];rewrite Hpresent in *; try now contradict H5.
    destruct v; try now contradict H5.
    unfold Hardware.ret in *.
    inversion H5;subst.
    clear H5 ss.
    unfold MMU.readAccessible in *.
    unfold bind in *.
    case_eq(get s);intros ss Hgets1;[| intros Hundef; unfold get in *;now contradict Hundef].
    unfold get in *.
    clear Hgets1.    
    case_eq(lookup p (nth (length va - (levelMin + 2)) va idxDefault)
         (memory s) pageEq idxEq); 
      [intros v Haccess |intros Haccess];rewrite Haccess in *; try now contradict H6.
    destruct v; try now contradict H6.
    unfold Hardware.ret in *.
    inversion H6. subst s2.
    clear H6 ss.
     unfold MMU.readPhyEntry in *.
    unfold bind in *.
    case_eq(get s);intros ss Hgets1;[| intros Hundef; unfold get in *;now contradict Hundef].
    unfold get in *.
    clear Hgets1.    
    case_eq(lookup p (nth (length va - (levelMin + 2)) va idxDefault)
         (memory s) pageEq idxEq); 
      [intros v Hpage |intros Hpage];rewrite Hpage in *; try now contradict H7.
    destruct v; try now contradict H7.
    unfold Hardware.ret in *.
    inversion Hx. subst s0.
    inversion Hpresent.
    inversion Haccess.
    subst.
    apply isAccessibleMappedPage2 with partition p;trivial.
    + unfold entryPresentFlag.
      unfold StateLib.getIndexOfAddr.
      rewrite Hpage.
      symmetry;trivial.
    + unfold entryUserFlag.
      unfold StateLib.getIndexOfAddr.
      rewrite Hpage.
      symmetry;trivial.
    + unfold isEntryPage.
      unfold StateLib.getIndexOfAddr.
      rewrite Hpage.
      trivial.
    + apply nextEntryIsPPgetPd;trivial.
    + intros;split;trivial.
      unfold isPE.
      unfold StateLib.getIndexOfAddr in *.
      rewrite <- H4.
      rewrite Hpage;trivial. }
    rewrite <- H4.
    symmetry.
    apply getAccessibleMappedPageEq with (CLevel (nbLevel - 1)) ;trivial.
    apply getNbLevelEqOption.

  - now contradict H5. 
  + assert (False).
  apply Hx.
  split;trivial.
  split;trivial.
  split;trivial.
  split. 
  left;trivial.
  exists pd.
  split. 
  apply nextEntryIsPPgetPd;trivial.
  split.
  apply pdPartNotNull with partition s;trivial.
  apply nextEntryIsPPgetPd;trivial.
  unfold consistency in *;intuition.
  left;trivial.
  split;trivial.
  symmetry;trivial.
  now contradict H3.
Qed.

Definition select (s : state) (p : page) (i : index) :=
lookup p i s.(memory) pageEq idxEq .

(* Definition next (s : state) (partition : page) (va: vaddr) v: option state :=  
 runstate (writeUser partition va v s) s. *)
 
Definition isolatedPartitions partition1 partition2 s :=
~ In partition1 (getPartitionAux partition2 s (nbPage+1)) /\ 
~ In partition2 (getPartitionAux partition1 s (nbPage+1)).

Fixpoint translateVaddrsAux valist nbL pd s:=
match valist with 
|nil => nil
|va :: l => 
  match runvalue (translate pd va nbL) s with 
  | Some pa => pa :: translateVaddrsAux l nbL pd s
  | _ => translateVaddrsAux l nbL pd s
  end 
end.

Fixpoint filterOption1 (l : list (option page)) : list page :=
  match l with
  | nil => nil
  | Some a :: l1 => a :: filterOption1 l1
  | None :: l1 => filterOption1 l1
  end.
  
Definition translateVaddrs valist nbL pd s :=
filterOption1  (translateVaddrsAux valist nbL pd s).
Lemma filterOption1InIff l elt : 
List.In elt (filterOption1 l) <-> List.In (Some elt) l.
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
Qed.


(* specification of a one-step action, applying in a MMU-controlled way 
   the (bare-metal) stateful function k *)
Definition UserFun (pdpartition: page)
                   (k: state -> list page -> value -> state) nbL:
list vaddr -> value -> state -> state :=
fun valist v s => 
k s (translateVaddrs valist nbL pdpartition s) v. 

(* condition meant to be required by one-step actions:
   it states that for any state s, the stateful function k
   can change s at most in one page, i.e. in p0 *)
Definition UserFunWCond (k: state -> list page -> value -> state) : Type :=
  forall (s:state) (listpage : list page)  (p1:page) (v:value) (i : index),
    ~In p1 listpage -> select s p1 i = select (k s listpage v) p1 i.

(* condition meant to be required by one-step actions:
   it states that for any state s, the stateful function k
   can depend at most on one page, i.e. on p *)
Definition UserFunRCond (k: state -> list page -> value -> state) : Type :=
  forall (s1 s2:state) (listpage :list page) (v:value) (i : index) (p : page),
  In p listpage -> 
  (forall (i : index) ,   select s1 p i = select s2 p i )->
                select (k s1 listpage v) p i = select (k s2 listpage v) p i.
Lemma translateNotDefault  partition1 s1 pd1 nbL obs a:
In partition1 (getPartitions pageRootPartition s1) -> 
consistency s1 ->
StateLib.getPd partition1 (memory s1) = Some pd1 ->
StateLib.getNbLevel = Some nbL ->
runvalue (translate pd1 a nbL) s1 = Some (Some obs) -> 
obs <> pageDefault.
Proof.
intros Hcurpart Hcons Hpd HnbL Hpa.
unfold runvalue in *.
case_eq( translate pd1 a nbL s1 );[intros pg Hpg | intros code s Hpg];rewrite Hpg in *;
try now contradict Hpg.
destruct pg.
inversion Hpa;subst. clear Hpa.
unfold translate in *.
unfold bind in *.
case_eq( translateAux nbLevel pd1 a nbL s1 );
[intros table Htable | intros code s' Htable];
rewrite Htable in *;try now contradict Htable .
destruct table as [table s'].
case_eq(MMU.comparePageToNull table s');[intros v1 Hv1 | intros code s2 Hv1];
rewrite Hv1 in *;try now contradict Hv1 .
destruct v1.
case_eq b;intros;subst.
* unfold Hardware.ret in *.
  inversion Hpg.
* case_eq(MMU.getIndexOfAddr a levelMin s0);[intros i Hi | intros code s3 Hi];
  rewrite Hi in *;try now contradict Hi .
  destruct i.
  case_eq(MMU.readPresent table i s2);[intros pres Hpres | intros code s4 Hpres];
  rewrite Hpres in *;try now contradict Hpres.
  destruct pres.
  case_eq(MMU.readAccessible table i s3);[intros access Haccess | intros code s4 Haccess];
  rewrite Haccess in *;try now contradict Haccess.
  destruct access.
  case_eq (b && b0)%bool;intros Hbool; rewrite Hbool in *.  
  { apply Bool.andb_true_iff in Hbool; destruct Hbool; subst.
    case_eq(MMU.readPhyEntry table i s4);[intros phy Hphy | intros code s5 Hphy];
    rewrite Hphy in *;try now contradict Hphy.
    destruct phy.
    unfold Hardware.ret in *.
    inversion Hpg.
    subst. clear Hpg.
    assert(s' = s1).
    assert(HgetTableAddr : {{fun s => s = s1  }} Internal.getTableAddr pd1 a nbL
    {{fun (table : page) (s : state) =>  s = s1}}). 
    { intros.
      eapply WeakestPreconditions.weaken.
      eapply WeakestPreconditions.strengthen.
      eapply getTableAddr.
      intros.
      simpl in *.
      destruct H as (H & _).
      apply H.
      intros.
      subst.
      split;trivial.
      split;trivial.
      split. eexact Hcurpart.
      split.
      instantiate (1:= idxPageDir).
      left. trivial.
      exists pd1.
      split.
      apply nextEntryIsPPgetPd;trivial.
      split.
      apply pdPartNotNull with partition1 s1;trivial.
      apply nextEntryIsPPgetPd;trivial.
      unfold consistency in *.
      intuition.
      left;split;trivial.
      symmetry. trivial. }
     unfold hoareTriple in *.
     generalize(HgetTableAddr s1);clear HgetTableAddr;intros Heq.
     unfold Internal.getTableAddr in *.
     rewrite <- MMUSimulation in Heq.
     rewrite Htable in Heq.
     apply Heq;trivial.
     subst.
(*      clear Htable. *)
     rewrite comparePageToNullEq in Hv1.
     assert(Hcompinv : {{fun s => s = s1 }} Internal.comparePageToNull table 
        {{fun (isnull : bool) (s : state) => s=s1 /\ (Nat.eqb pageDefault table) = isnull }}). 
     apply comparePageToNull. 
     unfold hoareTriple in *.
     generalize(Hcompinv s1);clear Hcompinv;intros Hcompinv.
     rewrite Hv1 in Hcompinv .
     destruct Hcompinv as (Hcomp1 & Hcomp2);trivial.
     subst.
     clear Hv1.
     assert(Hii : {{ fun s : state => s = s1 }} MAL.getIndexOfAddr a levelMin
        {{ fun (idx : index) s => s = s1 }}).
     eapply WeakestPreconditions.weaken.
     eapply WeakestPreconditions.strengthen. 
     apply getIndexOfAddr.
     intros.
     simpl in *.
     destruct H as (Hii &  Htmp).
     eapply Hii.
     intros.
     simpl. subst;trivial.
     unfold hoareTriple in *.
     generalize(Hii s1);clear Hii;intros Hii.
     rewrite getIndexOfAddrEq in *.
     rewrite Hi in Hii.
     destruct Hii;trivial.
     clear Hi.
     rewrite readPresentEq in Hpres.
     assert (Hpe : isPE table i s2).
     { 
     unfold MAL.readPresent in *.
     unfold bind in *.
     case_eq (get s2);[intros b Hb | intros code sk Hb];rewrite Hb in *;
     try now contradict Hpres.
     destruct b.
     unfold get in *.
     inversion Hb;subst.
     clear Hb.
     unfold hoareTriple in *.
     unfold isPE.
     destruct (lookup table i (memory s1) pageEq idxEq); try now contradict Hpres.
     destruct v;try now contradict Hpres.
     auto. }
     assert(Hii : {{ fun s => s = s2 /\ isPE table i s }} MAL.readPresent table i 
{{ fun (ispresent : bool) (s : state) => s= s2 /\  entryPresentFlag table i ispresent s }}).
     { apply readPresent. }
     generalize(Hii s2);clear Hii;intros Hii.
     rewrite Hpres in Hii.
     destruct Hii;trivial.
     rewrite readPhyEntryEq in Hphy.
     split;trivial.
     subst.
          assert(Hii : {{ fun s => s = s2 /\ isPE table i s }} MAL.readAccessible table i 
{{ fun (isaccessible : bool) (s : state) => s= s2 /\  entryUserFlag table i isaccessible s }}).
     { apply readAccessible. }
     generalize(Hii s2);clear Hii;intros Hii.
     rewrite readAccessibleEq in Haccess.
     rewrite Haccess in Hii.
     destruct Hii;trivial.
     rewrite readPhyEntryEq in Hphy.
     split;trivial.
     subst.
     
     
     
     
     
     
     assert(isPresentNotDefaultIff s2).
     { unfold consistency in *. intuition. }
     unfold isPresentNotDefaultIff in *.
     generalize (H table i);clear H;intros H.
     destruct H.
     unfold not;intros;subst.
     assert(StateLib.readPhyEntry table i (memory s2) = Some pageDefault).
     assert(Hread: {{fun s => s = s2/\  isPE table i s}} MAL.readPhyEntry table i 
    {{fun (page1 : page) (s : state) => s = s2 /\ isEntryPage table i page1 s}}).
     eapply readPhyEntry.
     unfold hoareTriple in *.
     generalize(Hread s2);clear Hread;intros Hread.
     rewrite readPhyEntryEq in *.
     rewrite Hphy in Hread.
     destruct Hread. 
     split;trivial.
     subst.
     apply isEntryPageReadPhyEntry1;trivial.
     apply entryPresentFlagReadPresent in H0.
     rewrite H0 in H2.
     apply H2 in H3.
     inversion H3. }
  { unfold Hardware.ret in *. inversion Hpg. }
Qed.

Lemma translatePagesInObservation partition1 s1 pd1 nbL valist:
In partition1 (getPartitions pageRootPartition s1) -> 
consistency s1 ->
StateLib.getPd partition1 (memory s1) = Some pd1 ->
StateLib.getNbLevel = Some nbL ->
incl (translateVaddrs valist nbL pd1 s1) (observation partition1 s1).
Proof.
intros Hcurpart Hcons Hpd HnbL.
unfold incl.
intros obs Htrans.
unfold translateVaddrs in *.
apply filterOption1InIff in Htrans.
revert obs Htrans.
induction valist;simpl in *;intros; try now contradict Htrans.
case_eq(runvalue (translate pd1 a nbL) s1);
[intros pa Hpa | intros Hpa];rewrite Hpa in *.
- simpl in *.
  destruct Htrans as [Htrans | Htrans];subst.
  + apply translateMappedPage with a pd1 nbL;trivial.
    apply translateNotDefault with partition1 s1 pd1 nbL a;trivial.
  + apply IHvalist;trivial.
- apply IHvalist;trivial.
Qed.


(** non-leakage *)
Theorem weakStepConsistency :
forall s1 s2  partition1,
consistency s1 -> 
consistency s2 -> 
In partition1 (getPartitions pageRootPartition s1) -> 
In partition1 (getPartitions pageRootPartition s2) -> 
forall pd1 nbL pd2, StateLib.getPd partition1 (memory s1)  = Some pd1 -> 
StateLib.getNbLevel = Some nbL ->  
StateLib.getPd partition1 (memory s2)  = Some pd2 -> 
pd1 = pd2 -> 
forall p, p <> pageDefault -> 
(forall i, select s1 p i = select s2 p i) -> 
(forall p, In p (observation partition1 s1) -> 
           forall i, select s1 p i = select s2 p i) ->
observation partition1 s1 = observation partition1 s2 ->
(forall va , runvalue (translate pd1 va nbL) s1 = runvalue (translate pd1 va nbL) s2) -> 
forall s1' s2' v valist k,
UserFunWCond k ->
UserFunRCond k -> 
UserFun pd1 k nbL valist v s1 = s1' ->
UserFun pd2 k nbL valist v s2 = s2' ->
forall i, select s1' p i = select s2' p i.
Proof.
intros s1 s2 partition1 Hcons1 Hcons2 Htree1 Htree2.
intros pd1 nbL pd2.
intros H H0 H1 H2 p Hdefault H3 H4 H5 H8 s1' s2' v valist k X X0 H6 H7 i .
unfold UserFunWCond in *.
unfold UserFun in *.
unfold translateVaddrs in *.
induction valist as [| va]; simpl in *.
* subst.
generalize (X s1 nil p v i);  intros X1.
generalize (X s2 nil p v i);  intros X2.
simpl.
rewrite <- X1; intuition.
generalize (H3 i); clear H3;intros H3.
rewrite H3 .
trivial.
* rewrite H8 in *.
assert(Hk : forall valist , translateVaddrsAux valist nbL pd1 s1 = translateVaddrsAux valist nbL pd1 s2).
{  revert H8. 
  clear. 
  intros. 
  unfold translateVaddrs.
  induction valist;simpl;trivial.
  rewrite H8. 
  case_eq( runvalue (translate pd1 a nbL) s2);intros;trivial.
   f_equal;trivial. } 
rewrite Hk in *.
subst pd2. 
assert(Hor: In p (observation partition1 s1) \/ 
~ In p (observation partition1 s1)) by apply inNotInList.
destruct Hor as [Hor | Hor].
- case_eq(runvalue (translate pd1 va nbL) s2);[intros table H2|intros H2]; 
  rewrite H2 in *. 
  + simpl in *.
    rename table into optiontable.
    case_eq optiontable;[intros table Htable | intros Htable];
    subst;[| apply IHvalist;trivial].
    clear IHvalist.
    assert(In table (observation partition1 s2)).
    apply translateMappedPage with va pd1 nbL;trivial .
    apply translateNotDefault with partition1 s2 pd1 nbL va;trivial.
    rewrite <- H5 in *.
    assert(H10 :In p (table :: translateVaddrs valist nbL pd1 s1)
     \/ ~ In p ((table :: translateVaddrs valist nbL pd1 s1))).
    { generalize (table :: translateVaddrs valist nbL pd1 s1). 
      intros.
      apply inNotInList. }
    destruct H10.
    subst.
    unfold UserFunRCond in *.
    generalize (X0 s1 s2 (table :: translateVaddrs valist nbL pd1 s1) v i p H7 );intros X1; trivial.
    unfold translateVaddrs in *.
    rewrite Hk in *.
    apply X1;trivial.
    generalize (X s1 (table :: translateVaddrs valist nbL pd1 s1) p v i);intros X1.
    subst. 
    generalize (X s2 (table :: translateVaddrs valist nbL pd1 s1)p v i);intros X2.
    unfold translateVaddrs in *.
    rewrite Hk in *.
    rewrite <- X1.
    rewrite <- X2.
    apply H3.
    intuition.
    intuition.
  + subst.
    apply IHvalist;trivial.
- case_eq(runvalue (translate pd1 va nbL) s2);[intros table H2|intros H2]; rewrite H2 in *. 
  + subst.
    rename table into optiontable.
    case_eq optiontable;[intros table Htable | intros Htable];
    subst;[| apply IHvalist;trivial].
    clear IHvalist.
    assert(In table (observation partition1 s2)).
    apply translateMappedPage with va pd1 nbL;trivial .
    apply translateNotDefault with partition1 s2 pd1 nbL va;trivial.
    rewrite <- H5 in H6.
    subst.
    generalize (X s1 (table :: translateVaddrs valist nbL pd1 s2) p v i);intros X1.
    subst. 
    generalize (X s2 (table :: translateVaddrs valist nbL pd1 s2) p v i);intros X2.
    assert(~ In p (table :: translateVaddrs valist nbL pd1 s2)). 
    { 
    simpl. 
    apply and_not_or.
    split. 
    unfold not;intros; subst;try now contradict Hor.
    clear X1 X2.
    assert(forall obs, obs <> pageDefault -> In obs (translateVaddrs valist nbL pd1 s1) ->
In obs (observation partition1 s1)).
    { revert H H0 Htree1 Hcons1.
    clear .
    intros.
    unfold incl;intros.
    apply translatePagesInObservation with pd1 nbL valist ;trivial. }
    contradict Hor. 
    apply H7;trivial.
    unfold  translateVaddrs in *.
    rewrite Hk;trivial. }
    unfold  translateVaddrs in *.
    simpl in *.        
    rewrite <- X1;trivial.
    rewrite <- X2;trivial.
  + subst.
    apply IHvalist;trivial.
Qed.

Theorem weakLocalRespect :
forall s s' partition1 partition2,
isolatedPartitions partition1 partition2 s-> 
verticalSharing s -> 
isChild s -> 
currentPartitionInPartitionsList s -> 
noDupPartitionTree s -> 
consistency s -> 
isParent s -> 
partitionsIsolation s ->  
partition1 = (currentPartition s) -> 
In partition2 (getPartitions pageRootPartition s) -> 
partition1 <> partition2 ->  
forall p k, In p (observation partition2 s) -> 
(forall listpages (p1:page) (v:value) (i : index), 
 ~In p1 listpages -> select s p1 i = select (k s listpages v) p1 i) -> 
forall pd nbL valist v,  StateLib.getPd partition1 (memory s)  = Some pd -> 
StateLib.getNbLevel = Some nbL -> 
UserFun pd k nbL valist v s = s' -> 
forall i, select s p i = select s' p i.
Proof.
intros s s' partition1 partition2 Hisolated Hvs Hischild Hcurintree Hnoduptree Hconsistency
Hisparent.
intros.
unfold UserFun in *.
unfold translateVaddrs in *.
induction valist as [|va];simpl in *.
subst.
generalize(H4 nil p v i);clear H4;intros H4.
rewrite <- H4;trivial.
auto.
case_eq(runvalue (translate pd va nbL) s );[intros p0 H8 | intros H8]; rewrite H8 in *; 
subst;trivial.
simpl in *.
rename p0 into p0option.
case_eq (p0option);[intros p0 Hp0 | intros Hp0];subst;[| apply IHvalist;trivial].
generalize (H4 (p0 :: filterOption1 (translateVaddrsAux valist nbL pd s)) p v i); clear H4; intros H4.
apply H4.

assert (In p0 (observation (currentPartition s)  s)).
apply  translateMappedPage with va pd nbL;trivial.
apply translateNotDefault with (currentPartition s) s pd nbL va;trivial.
assert(Hnew : incl (translateVaddrs valist nbL pd s) (observation (currentPartition s) s)).
    { apply translatePagesInObservation;trivial. }
clear IHvalist.
unfold partitionsIsolation in *.
unfold isolatedPartitions in *.
destruct Hisolated as (Hisolated1 & Hisolated2) .
assert(exists px, In px (p0 :: translateVaddrs valist nbL pd s) /\
In px (observation (currentPartition s) s)).  
exists p0.
split;trivial.
simpl.
left;trivial.
rename p0 into px.
destruct H7 as (px1 & Hpx1 & Hpx11).
assert( forall p0,In p0 (observation (currentPartition s) s) ->
 ~ In p0  (observation partition2 s)).
{ intros p0 Hpnew.
assert(Hnotmult2 : partition2 <> pageRootPartition).
  { unfold not;intros; subst.
    assert(Hcurpart : currentPartitionInPartitionsList s).
    unfold consistency in *.
    intuition.
    unfold currentPartitionInPartitionsList in *.
    unfold getPartitions in *.
    now contradict Hisolated1. }
  assert(Hnotmult1: (currentPartition s) <> pageRootPartition).
  { unfold not ;intros;subst.
  rewrite H7 in *.
  unfold getPartitions in *.
  now contradict Hisolated2. }
  assert(Hmulteq :(currentPartition s) = pageRootPartition \/ (currentPartition s) <> pageRootPartition ) by apply pageDecOrNot.
  destruct Hmulteq as [Hmulteq | Hmulteq].
  subst .
  unfold getPartitions in H1.
  rewrite <- Hmulteq in H1.
  now contradict H1.
  assert(Hcurpart: In (currentPartition s) (getPartitions pageRootPartition s)).
  unfold consistency in *.
  intuition.
  unfold consistency in *.
  assert(Hmultnone : multiplexerWithoutParent s) by intuition.
  assert(match closestAncestor (currentPartition s) partition2 s with 
            | Some closestAnc =>  True
            | None => False
         end).
  { case_eq (closestAncestor (currentPartition s) partition2 s ); [intros  closestAnc Hclose| 
    intros Hclose];trivial.
    revert Hmultnone Hnoduptree Hcurpart Hclose Hisparent  .
    clear.
    unfold closestAncestor, getPartitions.
    intro. intro.
    revert partition2.
    generalize (currentPartition s) as currentPart.
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
    case_eq ( in_dec pageDec partition2 (getPartitionAux parent s (nbPage + 1))); 
    intros i Hi; rewrite Hi in *.
    now contradict Hclose.
    apply IHn with parent partition2;trivial.
    assert (In currentPart (getPartitionAux pageRootPartition s (n + 2))).
    replace (n + 2) with (S n +1) by lia.
    simpl;right;trivial.
    apply getPartitionAuxMinus1 with currentPart;trivial.
    unfold getPartitions. destruct nbPage;simpl;left;trivial. }
    case_eq(closestAncestor (currentPartition s) partition2 s); [intros  closestAnc Hclose| 
          intros Hclose];
    rewrite Hclose in *; try now contradict H1.     
    assert(Hcloseintree : In closestAnc (getPartitions pageRootPartition s)). 
    { revert Hclose Hcurpart.
      unfold consistency in *. 
      assert(Hchild : isChild s) by intuition.
      assert(Hparent: isParent s) by intuition.
      assert(Hparenintreet: parentInPartitionList s) by intuition.
      revert Hchild Hparent Hparenintreet.
      clear. intro . intros Hisparent Hparentintree.
      revert partition2 closestAnc.
      generalize (currentPartition s) as currentPart.
      unfold closestAncestor.
      induction (nbPage+1);simpl;intros. now contradict Hclose.
      case_eq( StateLib.getParent currentPart (memory s));[intros parent Hparent | intros Hparent];
      rewrite Hparent in *.
      - case_eq(in_dec pageDec partition2 (getPartitionAux parent s (nbPage + 1)));
        intros i Hi; rewrite Hi in *.
        * inversion Hclose;subst.
          unfold parentInPartitionList in *.
          apply Hparentintree with currentPart;trivial.
          apply nextEntryIsPPgetParent;trivial.
        * apply IHn with parent partition2;trivial. 
          unfold parentInPartitionList in *.
          apply Hparentintree with currentPart;trivial.
          apply nextEntryIsPPgetParent;trivial.
      - inversion Hclose; subst. unfold getPartitions.
        destruct nbPage;simpl;left;trivial. }
      assert (Hinsubtree1 : In (currentPartition s)  (getPartitionAux closestAnc s (nbPage +1))).
      { assert (Hcurpart1 :In (currentPartition s) (getPartitions pageRootPartition s)) by trivial.   
        revert Hnoduptree Hmultnone Hclose Hcurpart Hcurpart1.
        unfold consistency in *. 
        assert(Hchild : isChild s) by intuition.
        assert(Hparent: isParent s) by intuition.
        assert(Hparenintreet: parentInPartitionList s) by intuition.
        revert Hchild Hparent Hparenintreet. 
        clear. intro . intros Hisparent Hparentintree Hnoduptree.
        intro.
        revert  partition2 closestAnc.
        generalize (currentPartition s) as currentPart.
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
        + right.
          case_eq(StateLib.getParent currentPart (memory s));[intros parent Hparent | intros Hparent];
          rewrite Hparent in *.
          - case_eq(in_dec pageDec partition2 (getPartitionAux parent s (nbPage + 1)));
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
              apply IHn with partition2;trivial.
              apply getPartitionAuxMinus1 with currentPart;trivial.
              unfold getPartitions. destruct nbPage;simpl;left;trivial. 
              unfold parentInPartitionList in *.
              apply Hparentintree with currentPart;trivial.
              apply nextEntryIsPPgetParent;trivial.
              apply getPartitionAuxSn with parent;trivial.
          - inversion Hclose; subst. trivial. }   
      assert (Hinsubtree2 : In partition2  (getPartitionAux closestAnc s (nbPage +1))).
      { assert (Hcurpart1 :In partition2 (getPartitions pageRootPartition s)) by trivial.   
        revert Hclose Hcurpart Hcurpart1.
        unfold consistency in *. 
        assert(Hchild : isChild s) by intuition.
        assert(Hparent: isParent s) by intuition.
        assert(Hparenintreet: parentInPartitionList s) by intuition.
        revert Hchild Hparent Hparenintreet.
        clear. intro . intros Hisparent Hparentintree.
        revert partition2 closestAnc.
        generalize(currentPartition s) as currentPart.
        unfold closestAncestor.
        assert(Hnbpage : nbPage <= nbPage) by lia.
        revert Hnbpage.
        generalize nbPage at 1 3.
        induction n;simpl;intros.
        trivial.  
       + case_eq(StateLib.getParent currentPart (memory s));[intros parent Hparent | intros Hparent];
         rewrite Hparent in *.
         - case_eq(in_dec pageDec partition2 (getPartitionAux parent s (nbPage + 1)));
           intros i Hi; rewrite Hi in *.
           * inversion Hclose;subst. trivial.
           *  now contradict Hclose.
         -  inversion Hclose. subst. unfold getPartitions in *;trivial.
        + case_eq(StateLib.getParent currentPart (memory s));[intros parent Hparent | intros Hparent];
          rewrite Hparent in *.
          - case_eq(in_dec pageDec partition2 (getPartitionAux parent s (nbPage + 1)));
            intros i Hi; rewrite Hi in *.
            * inversion Hclose;subst. trivial.
            * apply IHn with parent;trivial. lia.           
              unfold parentInPartitionList in *.
              apply Hparentintree with currentPart;trivial.
              apply nextEntryIsPPgetParent;trivial.
          - inversion Hclose; subst. trivial.  }  
         assert(Heqclose : partition2 = closestAnc \/ partition2 <> closestAnc) by apply pageDecOrNot.
         destruct Heqclose as [Heqclose | Heqclose].
         ** subst closestAnc.
            assert( partitionDescriptorEntry s /\ parentInPartitionList s) as (Hpde & Hparent).
            { unfold consistency in *. intuition. } 
            assert(Hfalse : In partition2 (getAncestors (currentPartition s) s)).
            { revert Hclose Hcurpart Hpde Hparent. clear .
              unfold  closestAncestor.
              unfold  getAncestors.
              revert partition2.
              generalize (currentPartition s) as currentPart.
              induction (nbPage + 1).
              simpl in *. intros.
              now contradict Hclose.
              simpl.
              intros.    
              case_eq(StateLib.getParent currentPart (memory s) );intros.
              rewrite H in *.
              case_eq ( in_dec pageDec partition2 (getPartitionAux p s (nbPage + 1)));intros;
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
         ** assert(Hsub1 : In (currentPartition s)
            (flat_map (fun p : page => getPartitionAux p s nbPage) (getChildren closestAnc s))).
          { replace (nbPage +1) with (1 + nbPage) in * by lia.
            simpl in *.
            apply Classical_Prop.not_or_and in Hisolated2 as (_ & Hin).  
            destruct  Hinsubtree1 as [Hsub1 | Hsub1]; subst.
            destruct  Hinsubtree2 as [Hsub2 | Hsub2]; subst.
            now contradict Heqclose.  now contradict Hsub2.
            destruct  Hinsubtree2 as [Hsub2 | Hsub2]; subst.
            now contradict Heqclose. trivial. }
          assert(Hsub2 : In partition2 (flat_map (fun p : page => getPartitionAux p s nbPage) (getChildren closestAnc s))).
          { replace (nbPage +1) with (1 + nbPage) in * by lia.
            simpl in *.
            apply Classical_Prop.not_or_and in Hisolated2 as (_ & Hin).  
            destruct  Hinsubtree2 as [Hsub2 | Hsub2]; subst.
            destruct  Hinsubtree1 as [Hsub11 | Hsub11]; subst.
            now contradict Heqclose.  now contradict Heqclose.
            destruct  Hinsubtree1 as [Hsub11 | Hsub11]; subst.
            now contradict Heqclose. trivial. }               
          rewrite in_flat_map in Hsub1 , Hsub2.
          destruct Hsub1 as (child1 & Hchild1 &  Hchild11).
          destruct Hsub2 as (child2 & Hchild2 &  Hchild22).
          assert(Horcurpart : child1 = (currentPartition s) \/ child1 <> (currentPartition s) ) by apply pageDecOrNot.
          destruct Horcurpart as [Horcurpart | Horcurpart].
          --- subst. 
              assert (Htrue : (currentPartition s) <> child2 ). 
              { unfold not;intros Hfasle;subst child2.
                contradict Hisolated2. 
                apply getPartitionAuxSbound;trivial. 
                }
              assert(Hdisjoint :Lib.disjoint (getUsedPages (currentPartition s) s) (getUsedPages child2 s)).
              { unfold partitionsIsolation in *. 
                apply H with closestAnc;trivial. }
              assert (Hor1 : partition2 = child2 \/ partition2 <> child2) by apply pageDecOrNot.
         destruct Hor1 as [Hor1 |Hor1].
         { subst child2. 
         unfold Lib.disjoint in *.
         intros.
         assert(Hx : In p (getAccessibleMappedPages partition2 s)).
         { unfold observation in *;trivial. }
         unfold observation.
         assert (~ In p0 (getUsedPages partition2 s)).
         apply H with closestAnc (currentPartition s);trivial. 
         unfold getUsedPages.
         apply in_app_iff.
         right.
         apply accessibleMappedPagesInMappedPages;trivial.
         unfold not;intros. 
         contradict H9. 
         unfold getUsedPages.
         apply in_app_iff.
         right.
         apply accessibleMappedPagesInMappedPages;trivial. 
 }      
        { assert(Hincl2:  incl (getMappedPages partition2 s) (getMappedPages child2 s)).
          { apply verticalSharingRec with (nbPage-1);trivial.
          unfold consistency in *.
          intuition.
          apply childrenPartitionInPartitionList with closestAnc; trivial.           
          intuition.
          destruct nbPage.
          simpl in *. intuition.
          simpl.
          replace    (n - 0 + 1) with (S n) by lia.
          trivial. }
          destruct nbPage.
          simpl in *. intuition.
          simpl.
          replace    (n - 0 + 1) with (S n) by lia.
          trivial.
          unfold Lib.disjoint in *.
          intros.
          unfold incl in Hincl2.
          assert(In p0 (getUsedPages (currentPartition s) s)).
          { unfold getUsedPages.
          apply in_app_iff.
          right. unfold observation in *. apply accessibleMappedPagesInMappedPages;trivial. }
          apply Hdisjoint in H9.
          unfold not;intros.
          contradict H9.
          unfold getUsedPages.
          apply in_app_iff.
          right.
          apply Hincl2.
          
          apply accessibleMappedPagesInMappedPages.
          unfold observation in *;trivial.
          } 
     --- assert(Horpart1 : child2 = partition2 \/ child2 <> partition2 ) by apply pageDecOrNot.
         destruct Horpart1 as [Horpart1 | Horpart1].
         +++ subst. 
             assert (Htrue : partition2 <> child1 ). 
             { unfold not;intros Hfasle;subst child1.
               contradict Hisolated1.
               revert Hchild11 Horcurpart  H1 Hcurpart .

                 assert( partitionDescriptorEntry s /\ parentInPartitionList s) as (Hpde & Hparentintree).
          { unfold consistency in *. intuition. } 
                revert Hnoduptree Hisparent Hparentintree Hpde. 
                clear.
                revert  partition2.
                generalize (currentPartition s) as currentPart.
                induction nbPage;simpl. intuition.
                intros.               
                destruct Hchild11. intuition.
                right.
                rewrite in_flat_map in *.
                destruct H as (x & Hx1 & Hx2).
                assert(x = currentPart \/ x <> currentPart) by apply pageDecOrNot.
                destruct H;subst.
                exists currentPart;split;trivial.
                destruct n;left;trivial.
                exists x;split;trivial.
                apply IHn;trivial.
                apply childrenPartitionInPartitionList with partition2;trivial. }
       assert(Hdisjoint : Lib.disjoint (getUsedPages partition2 s) (getUsedPages child1 s)).
          { unfold partitionsIsolation in *. 
            apply H with closestAnc;trivial. }
        { assert(Hincl2:  incl (getMappedPages (currentPartition s) s) (getMappedPages child1 s)).
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
          unfold Lib.disjoint in *.
          unfold incl in Hincl2.
       
          assert(In p0 (getMappedPages (currentPartition s) s)).
          { unfold observation in *. apply accessibleMappedPagesInMappedPages;trivial. }
apply Hincl2 in H9.
unfold not;intros.          contradict H9.
assert(In p0 (getUsedPages partition2 s) ).

          unfold getUsedPages.
          apply in_app_iff.
          right.
          apply accessibleMappedPagesInMappedPages.
          unfold observation in *;trivial.
          apply Hdisjoint in H9.
          unfold not;intros;contradict H9.
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
           unfold closestAncestor.
           revert dependent child2. 
(*            revert dependent child1.  *)


           assert( partitionsIsolation s /\  verticalSharing s) as His.
           { unfold consistency in *. intuition. }
(*            intros partition2 Htmp Htmp1.  *)
           revert Hparentintree Hischild Hmultnone Hnoduptree Hisparent Hcurpart (* Hmulteq *).
           revert dependent closestAnc.
           revert Hpde  Hnocycle His  Hvs.
           clear Hisolated1 Hisolated2.
                      revert dependent partition2.
           clear .
           generalize(currentPartition s) as currentPart.
           unfold closestAncestor.
           unfold getAncestors.
           assert(Hnbpage : nbPage <= nbPage) by lia.
           revert Hnbpage.
           generalize nbPage at 1  3 5 . 
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
            case_eq (in_dec pageDec partition2 
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
           assert( Lib.disjoint (getUsedPages currentPart s) (getUsedPages child2 s)).
           unfold partitionsIsolation in *.
           apply His with closestAnc;trivial.
           unfold not;intros; subst.
           rewrite in_flat_map in Hchild11.
           destruct Hchild11 as (x & Hx1 & Hx11).
           contradict Hx11.
              
           apply noCycleInPartitionTree2;trivial.
           intuition.
            unfold Lib.disjoint in *.
            unfold getUsedPages in *.
            
            assert( ~ In currentPart (getConfigPages child2 s ++ getMappedPages child2 s) ).
            apply H.  
           unfold getConfigPages.
           simpl;left;trivial.
           rewrite in_app_iff in H2.
           intuition.
           (** contradict Hparent, Hchild11 and Hchild1*)      
           - assert(parent= partition2 \/ parent <> partition2 )by apply pageDecOrNot.
           destruct H as [ Hi1 | Hi1].
           subst.
           destruct nbPage;simpl in *.
           now contradict Hchild22.
           intuition.
            assert(parent= child2 \/ parent <> child2 )by apply pageDecOrNot.
           destruct H as [ Hi2 | Hi2].
           subst.
           clear Hi.
           contradict i.
           revert Hchild22. 
           clear.
           revert partition2 child2.
           induction nbPage;simpl in *;intros.
           now contradict Hchild22.
           destruct Hchild22.
           left;trivial.
           right.
           rewrite in_flat_map in *.
           destruct H as (x & hx & hxx).
           exists x;split;trivial.
           apply IHn;trivial.
           unfold closestAncestorAux.
            apply IHn with  child2; trivial.
(*            * lia. *)
           * lia. 
(*            * unfold parentInPartitionList in *. 
             apply Hparentintree with currentPart;trivial.
             apply nextEntryIsPPgetParent;trivial.  *)  
          * unfold parentInPartitionList in *. 
             apply Hparentintree with currentPart;trivial.
             apply nextEntryIsPPgetParent;trivial.
          * apply getPartitionAuxMinus1 with currentPart;trivial.
          * intuition.
          
          +   unfold partitionDescriptorEntry in *.
           assert((exists entry : page,
          nextEntryIsPP currentPart idxParentDesc entry s /\ entry <> pageDefault)).
          apply Hpde;trivial.
          do 4 right;left;trivial.
          destruct H as (entry & Hi1 & _).
          rewrite nextEntryIsPPgetParent in *.
          rewrite Hi1 in Hparent. now contradict Hi1.  }
         assert(Hintree : In  closestAnc (getPartitions pageRootPartition s)) by trivial.
         assert(Horc1 : partition2 = child2 \/ partition2 <> child2) by apply pageDecOrNot.
         { destruct Horc1 as [Horc1 | Horc1].
           subst child2.  
           **
           assert(Horc1 : (currentPartition s) = child1 \/ (currentPartition s) <> child1) by apply pageDecOrNot.
           destruct Horc1 as [Horc1 | Horc1].
           --- subst child1. now contradict Horpart1.
           --- now contradict Horpart1.
           
            ** assert(Horc2 : (currentPartition s) = child1 \/ (currentPartition s) <> child1) by apply pageDecOrNot.
           destruct Horc2 as [Horc2 | Horc2].
           --- subst child1. now contradict Horcurpart.
           ---   assert(Hincl1 :  incl (getMappedPages (currentPartition s) s) (getMappedPages child1 s)).
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
            assert(Hincl2:  incl (getMappedPages partition2 s) (getMappedPages child2 s)).
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
           assert(Hdisjoint : Lib.disjoint (getUsedPages child1 s) (getUsedPages child2 s)).
{           unfold partitionsIsolation in *.
           apply H with closestAnc; trivial. }
           unfold Lib.disjoint in *.
           intros.
           unfold incl in *.
           clear Hconsistency.
           assert( In p0 (getMappedPages (currentPartition s) s)).
           apply accessibleMappedPagesInMappedPages.
           unfold observation in *.
           trivial.
           apply Hincl1 in H9.
           clear Hincl1.
           assert (In p0 (getUsedPages child1 s)). 
           unfold getUsedPages.
           apply in_app_iff.
           right;trivial.
           clear H9. 
           apply Hdisjoint in H10.
            clear Hdisjoint.
            unfold not. 
            intros.
            assert( In p0 (getMappedPages partition2 s)).
           unfold observation in *.
           apply accessibleMappedPagesInMappedPages;trivial.
           apply Hincl2 in H11.
           contradict H10.
          unfold getUsedPages;
           apply in_app_iff;
           right.
           trivial. }
}
assert(incl (px :: translateVaddrs valist nbL pd s) 
(observation (currentPartition s) s)).
{ unfold incl;intros.
  assert (a = px \/ a <> px) by apply pageDecOrNot.
  destruct H10.
  subst.
  trivial.
  simpl in *.
  destruct H9. intuition.
  apply Hnew;trivial. }
clear H4 H8.
revert dependent px.
intro.
unfold translateVaddrs.
generalize  (px :: filterOption1 (translateVaddrsAux valist nbL pd s)).
intros.
clear Hnew.
unfold incl in *.
apply H9 in Hpx1.
contradict H3.
apply H7.
apply H9 ;trivial.
apply IHvalist;trivial.
Qed.
