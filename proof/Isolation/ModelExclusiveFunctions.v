Require Import Arith.
Require Import Lia.
Require Import Coq.Strings.String.
Require Import List.
Import List.ListNotations.

From Pip.Model.Isolation Require Import IsolationTypes IsolationState IsolationInterface.
Import IsolationTypes.
Import IsolationState.
Import IsolationInterface.

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

Module Level.

Program Definition pred (n : level) : option level := 
if gt_dec n 0 then
let ipred := n-1 in 
Some (Build_level_s ipred _ )
else  None.
Next Obligation.
destruct n.
simpl.
lia.
Qed.
End Level. 

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

Fixpoint lookup {A B C: Type} (k : A) (i : B)  (assoc : list ((A * B)*C))  (eqA : A -> A -> bool) (eqB : B -> B -> bool) :=
  match assoc with
    | nil => None  
    | (a, b) :: assoc' => if beqPairs a (k,i) eqA eqB then Some b else lookup k i assoc' eqA eqB
  end.

Definition idxEq (x y : index) : bool := x =? y.
Definition pageEq (x y : page) : bool := x =? y.
Notation pageEqM x y := (ret (pageEq x y)) (only parsing).

Definition readPhysical (paddr : page) (idx : index) memory: option page :=
let entry :=  lookup paddr idx memory pageEq idxEq  in 
  match entry with
  | Some (PP a) => Some a
  | _ => None
 end.

(**  The [getPd] function returns the physical page of the page directory of
     a given partition  *)
Definition getPd partition memory: option page:= 
match Index.succ idxPageDir with 
|None => None
|Some idx => readPhysical partition idx memory
end.

Definition levelEq (x y : level) : bool := x =? y.

Definition getIndexOfAddr (va : vaddr) (l : level) : index:=
nth ((length va) - (l + 2))  va index_d.
Definition readPhyEntry(paddr : page) (idx : index) memory: option page :=
let entry :=  lookup paddr idx memory pageEq idxEq  in 
  match entry with
  | Some (PE a) => Some a.(pa)
  | Some _ => None
  | None => None
 end. 

Fixpoint  getIndirection (pd : page) (va : vaddr) (currentlevel : level) (stop : nat) s :=
match stop with 
|0 => Some pd 
|S stop1 => 
if (levelEq currentlevel levelMin)  
then Some pd 
  else  
    let idx :=  getIndexOfAddr va currentlevel in 
       match readPhyEntry pd idx s.(memory) with 
       | Some addr =>  if  pageDefault =? addr 
                          then Some pageDefault 
                          else 
                            match Level.pred currentlevel with
                            |Some p =>  getIndirection addr va p stop1 s
                            |None => None
                            end
      |None => None
    end
   end. 

Inductive optionPage : Type:= 
|SomePage : page -> optionPage
|SomeDefault :  optionPage
|NonePage : optionPage
.

Fixpoint getTablePages (table : page ) (idx : nat) s : list page := 
match idx with 
| 0 => []
|S idx1 => match  lookup table (CIndex idx1) s.(memory) pageEq idxEq  with 
              | Some (PE entry) => if (pa entry =? pageDefault ) then getTablePages table idx1 s
                                      else getTablePages table idx1 s ++ [pa entry] 
              | _ => getTablePages table idx1 s
            end
end.

Fixpoint getIndirectionsAux (pa : page) (s : state) level {struct level} : list page :=
  match level with
    | O => []
    | S level1 => pa :: flat_map (fun p => getIndirectionsAux p s level1) 
                                    (getTablePages pa tableSize s)
  end.

(** The [getIndirectionsAux] function returns the list of physical pages 
    used into a configuration tables tree *)
Definition getIndirections pd s : list page :=
  getIndirectionsAux pd s nbLevel.

(** The [getNbLevel] function returns the number of translation levels of the MMU *) 
Definition getNbLevel : option level:=
match gt_dec nbLevel 0 with
| left x =>
    Some {| l := nbLevel - 1; Hl := IsolationInterface.IsolationInterface.getNbLevel_obligation_1 x |}
| right _ => None
end.

Definition readPresent  (paddr : page) (idx : index) memory : option bool:=
let entry :=  lookup paddr idx memory pageEq idxEq  in 
  match entry with
  | Some (PE a) => Some a.(present)
  | Some _ => None
  | None => None
 end. 

Definition getMappedPage pd s va: optionPage  :=
match getNbLevel  with 
 |None => NonePage
 |Some level => let idxVA := getIndexOfAddr va levelMin  in 
               match getIndirection pd va level (nbLevel - 1) s with 
                | Some tbl =>  if pageDefault =? tbl
                                   then NonePage 
                                   else match (readPresent tbl idxVA s.(memory)) with 
                                         | Some false => SomeDefault
                                         |Some true => match readPhyEntry tbl idxVA s.(memory)  with 
                                                       | Some a => SomePage a
                                                       | _ => NonePage
                                                       end
                                         |_ => NonePage
                                         end
                | _ => NonePage
               end
end.

(** The [getMappedPagesOption] function Return all physical pages marked as 
    present into a partition *)
Definition getMappedPagesOption (pd : page) (vaList : list vaddr) s : list optionPage :=
map (getMappedPage pd s) vaList.

(** The [getAccessibleMappedPagesOption] function Return all physical pages 
    marked as present and accessible into a partition *)
Definition getAccessibleMappedPagesOption (pd : page) (vaList : list vaddr) s : list optionPage :=
map (getAccessibleMappedPage pd s) vaList.

(** The [filterOption] function Remove option type from list *)
Fixpoint filterOption (l : list (optionPage)) := 
match l with 
| [] => []
| SomePage a :: l1 => a:: filterOption l1
| _ :: l1 => filterOption l1
end.

(** The [getMappedPagesAux] function removes option type from mapped pages list *)
Definition getMappedPagesAux (pd :page)  (vaList : list vaddr) s : list page  := 
filterOption (getMappedPagesOption pd vaList s).

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