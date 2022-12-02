Require Import Arith.
Require Import Lia.
Require Import List.
Require Import Coq.Strings.String.
Import List.ListNotations.

From Pip.Model.Isolation Require Import IsolationTypes IsolationState IsolationInterface.
Import IsolationTypes.
Import IsolationState.
Import IsolationInterface.SAMM.




Module Index.

Program Definition idxSuccM (n : index) : SAM index :=
  let isucc := n+1 in
  if lt_dec isucc tableSize
  then ret (Build_index_s isucc _)
  else undefined "Can't find a successor to an index larger than tableSize".

Definition succ (n : index): option index:=
let isucc := n + 1 in
match lt_dec isucc tableSize with
| left x =>
    Some {| i := isucc; Hi := idxSuccM_obligation_1 n x |}
| right _ => None
end.

Program Definition pred (n : index) : option index := 
if gt_dec n 0 then
let ipred := n-1 in 
Some (Build_index_s ipred _ )
else  None.
Next Obligation.
destruct n.
simpl.
lia.
Qed.

End Index.

Fixpoint getAllIndicesAux (pos count: nat) : list index :=
  match count with
    | 0        => []
    | S count1 => match lt_dec pos tableSize with
                   | left pf => Build_index_s pos pf :: getAllIndicesAux (S pos) count1
                   | _       => []
                 end
  end.

(** The [getAllIndicesAux] function returns the list of all indices  *)
Definition getAllIndices := getAllIndicesAux 0 tableSize.

Fixpoint getAllVAddrAux (levels: nat) : list (list index) :=
  match levels with
    | 0         => [[]]
    | S levels1 => let alls := getAllVAddrAux levels1 in
                  flat_map (fun (idx : index) => map (cons idx) alls) getAllIndices
  end.

(** The [getAllVAddr] function returns the list of all virtual addresses *)
Definition getAllVAddr :=map CVaddr (getAllVAddrAux (S nbLevel)).

Definition checkOffset0 (va : vaddr) :bool :=
if (nth nbLevel va index_d =? CIndex 0) then true else false .


Definition getAllVAddrWithOffset0 :=filter checkOffset0 getAllVAddr.

(**  The [getPd] function returns the physical page of the page directory of
     a given partition  *)
Definition getPd partition memory: option page:= 
match Index.succ idxPageDir with 
|None => None
|Some idx => readPhysical partition idx memory
end.

(** The [getChildren] function Returns all children of a given partition *)
Definition getChildren (partition : page) s := 
let vaList := getAllVAddrWithOffset0 in 
match getNbLevel, getPd partition s.(memory) with 
|Some l1,Some pd => getMappedPagesAux pd (getPdsVAddr partition l1 vaList s) s
|_, _ => []
end.

(** The [getPartitionsAux] function returns all pages marked as descriptor partition *)
Fixpoint getPartitionAux (partitionRoot : page) (s : state) bound {struct bound} : list page :=
  match bound with
    | O => []
    | S bound1 => partitionRoot :: flat_map (fun p => getPartitionAux p s bound1) 
                                    (getChildren partitionRoot s )
  end.

(** The [getPartitions] function fixes the sufficient timeout value to retrieve all partitions *)
Definition getPartitions (root : page) s : list page  :=
(getPartitionAux root s (nbPage+1)).