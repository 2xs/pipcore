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

Definition readAccessible  (paddr : page) (idx : index) memory : option bool:=
let entry :=  lookup paddr idx memory pageEq idxEq  in 
  match entry with
  | Some (PE a) => Some a.(user)
  | Some _ => None
  | None => None
 end.

Definition getAccessibleMappedPage pd s va: optionPage :=
match getNbLevel  with 
 |None => NonePage
 |Some level =>let idxVA := getIndexOfAddr va levelMin  in 
               match getIndirection pd va level (nbLevel - 1) s with 
                | Some tbl => if pageDefault =? tbl
                                   then NonePage 
                                   else  match (readPresent tbl idxVA s.(memory)),
                                                   (readAccessible tbl idxVA s.(memory)) with 
                                           |Some true, Some true => match readPhyEntry tbl idxVA s.(memory)  with 
                                                       | Some a => SomePage a
                                                       | _ => NonePage
                                                       end
                                           | _, _ =>  NonePage 
                                          end
                | _ => NonePage
               end
end.

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

Definition getFstShadow partition memory: option page:= 
match Index.succ idxShadow1 with 
|None => None
|Some idx => readPhysical partition idx memory
end.

Definition readPDflag  (paddr : page) (idx : index) memory : option bool:=
let entry :=  lookup paddr idx memory pageEq idxEq in
  match entry with
  | Some (VE a) => Some a.(pd)
  | Some _ => None
  | None => None
 end.

Definition checkChild partition level (s:state) va : bool :=
let idxVA :=  getIndexOfAddr va levelMin in
match getFstShadow partition s.(memory) with
| Some sh1 =>
   match getIndirection sh1 va level (nbLevel -1) s with
    |Some tbl => if tbl =? pageDefault
                    then false
                    else match readPDflag tbl idxVA s.(memory) with
                          | Some true => true
                          | _ => false
                          end
    |None => false
    end
| _ => false
end.

Definition getPdsVAddr partition l1 (vaList : list vaddr) s :=
filter (checkChild partition l1 s) vaList.

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

Definition getMappedPages (partition : page) s : list page :=
  match getPd partition s.(memory) with
    |None => []
    |Some pd => let vaList := getAllVAddrWithOffset0 in getMappedPagesAux pd vaList s
  end.

Definition getConfigTablesLinkedList partition memory: option page:= 
match Index.succ idxShadow3 with 
|None => None
|Some idx => readPhysical partition idx memory
end.

Definition getSndShadow partition memory: option page:= 
match Index.succ idxShadow2 with 
|None => None
|Some idx => readPhysical partition idx memory
end.

Definition getMaxIndex : option index:=
match gt_dec tableSize 0 with
| left x =>
    Some
      {|
      i := tableSize - 1;
      Hi := IsolationInterface.IsolationInterface.getMaxIndex_obligation_1 x |}
| right _ => None 
end.

Fixpoint getLLPages (sh3 : page) s bound :=
match bound with 
|0 => []
|S bound1 => match getMaxIndex with 
            |None => []
            |Some maxindex =>  match readPhysical sh3 maxindex s.(memory) with 
                                |None => [sh3]
                                |Some addr => if addr =? pageDefault then [sh3] else sh3 :: getLLPages addr s bound1
                               end
           end
end.

Definition getConfigPagesAux (partition : page) (s : state) : list page := 
match getPd partition s.(memory),
      getFstShadow partition s.(memory),
      getSndShadow partition s.(memory),
      getConfigTablesLinkedList partition s.(memory) with
| Some pd , Some sh1, Some sh2 , Some sh3  => (getIndirections pd s)++
                         (getIndirections sh1 s)++
                         (getIndirections sh2 s )++
                         (getLLPages sh3 s (nbPage+1))
|_,_,_,_ => []
end.

Definition getConfigPages (partition : page) (s : state) :=
partition :: (getConfigPagesAux partition s).

Definition getUsedPages (partition: page) s : list page :=
  getConfigPages partition s ++ getMappedPages partition s.


Definition disjoint {A : Type} (l1 l2 : list A) : Prop := 
forall x : A,  In x l1  -> ~ In x l2.

Definition getAccessibleMappedPagesAux (pd :page)  (vaList : list vaddr) s : list page := 
filterOption (getAccessibleMappedPagesOption pd vaList s).

Definition getAccessibleMappedPages (partition : page) s : list page :=
  match getPd partition s.(memory) with
    |None => []
    |Some pd => let vaList := getAllVAddrWithOffset0 in getAccessibleMappedPagesAux pd vaList s
  end.

Definition nextEntryIsPP table idxroot tableroot s : Prop:=
match Index.succ idxroot with
| Some idxsucc => match lookup table idxsucc (memory s) pageEq idxEq with
                  | Some (PP table) => tableroot = table
                  |_ => False
                  end
| _ => False
end.

Definition isPE table idx s: Prop :=
match lookup table idx s.(memory) pageEq idxEq with
| Some (PE _) => True
| _ => False
end.

Definition isVE table idx s: Prop :=
match lookup table idx s.(memory) pageEq idxEq with
| Some (VE _) => True
| _ => False
end.

Definition isVA table idx s: Prop := 
match lookup table idx s.(memory) pageEq idxEq with
| Some (VA _) => True
| _ => False
end.

Definition isPP table idx s: Prop :=
match lookup table idx s.(memory) pageEq idxEq with
| Some (PP _) => True
| _ => False
end.

Definition readVirEntry (paddr : page) (idx : index) memory : option vaddr :=
let entry :=  lookup paddr idx memory pageEq idxEq in
match entry with
| Some (VE addr) => Some (va addr)
| Some _ => None
| None => None
end.

Definition getVirtualAddressSh1 sh1 s va: option vaddr :=
match getNbLevel  with
| None => None
| Some level => let idxVA := getIndexOfAddr va levelMin in
                match getIndirection sh1 va level (nbLevel - 1) s with
                | Some tbl => if pageDefault =? tbl
                              then None
                              else readVirEntry tbl idxVA s.(memory)
                | _ => None
                end
end.

Definition readVirtual (paddr : page) (idx : index) memory : option vaddr :=
let entry := lookup paddr idx memory pageEq idxEq in
match entry with
| Some (VA addr) => Some addr
| Some _ => None
| None => None
end.

Definition getVirtualAddressSh2 sh2 s va: option vaddr :=
match getNbLevel  with 
| None => None
| Some level => let idxVA := getIndexOfAddr va levelMin in
                match getIndirection sh2 va level (nbLevel - 1) s with
                | Some tbl => if pageDefault =? tbl
                              then None
                              else readVirtual tbl idxVA s.(memory)
                | _ => None
               end
end.

Definition vaddrEq (x y : vaddr) : bool := eqList x y idxEq.

Definition getParent partition memory :=
match Index.succ idxParentDesc with
| Some idx => readPhysical partition idx memory
| _ => None
end.

Definition getPDFlag sh1 va s :=
let idxVA := getIndexOfAddr va levelMin in
match getNbLevel with
| Some nbL =>  match getIndirection sh1 va nbL (nbLevel - 1) s with
               | Some tbl => if tbl =? pageDefault
                             then false
                             else match readPDflag tbl idxVA (memory s) with
                                  | Some true => true
                                  | Some false => false
                                  | None => false
                                  end
               | None => false
               end
| None => false
end.

Definition isAccessibleMappedPageInParent partition va accessiblePage s :=
match getSndShadow partition (memory s) with
| Some sh2 =>
  match getVirtualAddressSh2 sh2 s va  with
  | Some vaInParent =>
    match getParent partition (memory s) with
    | Some parent =>
      match getPd parent (memory s) with
      | Some pdParent =>
        match getAccessibleMappedPage pdParent s vaInParent with
        | SomePage sameAccessiblePage => accessiblePage =? sameAccessiblePage
        | _ => false
        end
      | None => false
      end
    | None => false
    end
  | None => false
  end
| None => false
end.

Fixpoint getAncestorsAux (partition : page) memory depth : list page :=
match depth with
| 0 => []
| S depth1 => match getParent partition memory with
              | Some parent => parent :: getAncestorsAux parent memory depth1
              | _ => []
              end
end.

(** The [getAncestors] function fixes the sufficient timeout value to retrieve all ancestors *)
Definition getAncestors (partition : page) s :=
getAncestorsAux partition s.(memory) (nbPage+1).

Definition isDerived partition va s :=
match getFstShadow partition (memory s) with
| Some sh1 =>
  match getVirtualAddressSh1 sh1 s va with
  | Some va0 => vaddrEq vaddrDefault va0 = false
  | _ => False
  end
| None => False
end.

Definition isI table idx s : Prop :=
match lookup table idx s.(memory) pageEq idxEq with
| Some (I _) => True
| _ => False
end.

Definition readIndex  (paddr : page) (idx : index) memory : option index :=
let entry := lookup paddr idx memory pageEq idxEq in
match entry with
| Some (I indexValue) => Some indexValue
| Some _ => None
| None => None
end.

Definition isIndexValue table idx vindex s :=
match lookup table idx (memory s) pageEq idxEq with
| Some (I value) => value = vindex
| _ => False
end.








