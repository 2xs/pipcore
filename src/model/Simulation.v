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

(* BEGIN SIMULATION

(** Into this file we test PIP memory services, considering : 
    ** MMU : 2 levels
    ** tableSize : 12 entries
    ** nbPages : 100 pages
    ** Kernel page : page number 10 
    ** Multiplexer Partition descriptor : page number 1 
    At the initial state the multiplexer has all available pages 
    present and accessible into its virtual space. 
    Step 1 "createPartition" : The multiplexer creates new partition 
            (Child)
    Step 2 "countToPrepare" : The multiplexer counts the number of pages
            required to map a virtual address into the child
    Step 3 "prepare" : The multiplexer inserts required physical pages
           to map the virtual address into the child 
    Step 4 "addVAddr" : The multiplexer maps the virtual address into 
            the child
    Step 5 "removeVAddr" : The multiplexer removes the virtual address 
            mapping from the child
    Step 6 "collect" : The multiplexer removes empty pages already used 
           for mapping
    Step 7 "deletePartition" : The multiplexer deletes the child and gets 
            all used pages back *) 

Require Import List Core.Services Model.Hardware Model.ADT Model.MALInternal Model.MAL Model.IAL.
Import List.ListNotations.

Definition K := 10.

Definition memory : list (paddr * value):=
[(CPage 1, CIndex 0, VA defaultVAddr) ;
 (CPage 1, CIndex 1, PP (CPage 1)) ;
 (CPage 1, CIndex 2, VA defaultVAddr) ;
 (CPage 1, CIndex 3, PP (CPage 2)) ;
 (CPage 1, CIndex 4, VA defaultVAddr) ;
 (CPage 1, CIndex 5, PP (CPage 3)) ;
 (CPage 1, CIndex 6, VA defaultVAddr) ;
 (CPage 1, CIndex 7, PP (CPage 4)) ;
 (CPage 1, CIndex 8, VA defaultVAddr) ;
 (CPage 1, CIndex 9, PP (CPage 5)) ;
 (CPage 1, CIndex 10, VA defaultVAddr) ;
 (CPage 1, CIndex 11, PP (CPage 7)) ;

 (CPage 2, CIndex  0, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, Kidx     , PE (Build_Pentry false false false true  true  (CPage K)  )) ; 
 (CPage 2, CIndex  2, PE (Build_Pentry false false false true  true  (CPage 6)  )) ;
 (CPage 2, CIndex  3, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex  4, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex  5, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex  6, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex  7, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex  8, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex  9, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 10, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 11, PE (Build_Pentry false false false false false defaultPage)) ;

 (CPage 3, CIndex  0, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex  1, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex  2, PE (Build_Pentry false false false true  true  (CPage 8)  )) ; 
 (CPage 3, CIndex  3, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex  4, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex  5, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex  6, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex  7, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex  8, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex  9, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 10, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 11, PE (Build_Pentry false false false false false defaultPage)) ;

 (CPage 6, CIndex  0, PE (Build_Pentry false false false true true (CPage 12)));
 (CPage 6, CIndex  1, PE (Build_Pentry false false false true true (CPage 13)));
 (CPage 6, CIndex  2, PE (Build_Pentry false false false true true (CPage 14)));
 (CPage 6, CIndex  3, PE (Build_Pentry false false false true true (CPage 15)));
 (CPage 6, CIndex  4, PE (Build_Pentry false false false true true (CPage 16)));
 (CPage 6, CIndex  5, PE (Build_Pentry false false false true true (CPage 17)));
 (CPage 6, CIndex  6, PE (Build_Pentry false false false true true (CPage 18)));
 (CPage 6, CIndex  7, PE (Build_Pentry false false false true true (CPage 19)));
 (CPage 6, CIndex  8, PE (Build_Pentry false false false true true (CPage 20)));
 (CPage 6, CIndex  9, PE (Build_Pentry false false false true true (CPage 21)));
 (CPage 6, CIndex 10, PE (Build_Pentry false false false true true (CPage 22)));
 (CPage 6, CIndex 11, PE (Build_Pentry false false false true true (CPage 23)));

 (CPage 8, CIndex  0, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex  1, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex  2, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex  3, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex  4, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex  5, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex  6, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex  7, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex  8, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex  9, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 10, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 11, VE (Build_Ventry false defaultVAddr))
 ].


Definition init : state := 
Build_state multiplexer memory.
Notation "'P' v" := (Build_page v _) ( at level 9).
Notation "'I' v" := (Build_index v _) ( at level 9).
Notation "'VAddr' v" := (Build_vaddr v _) ( at level 9).

Definition createPartition :=
put init ;;

Services.createPartition (CVaddr [(CIndex 2); (CIndex 0); (CIndex 0)]) (* child*)
                         (CVaddr [(CIndex 2); (CIndex 1); (CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 2); (CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 3); (CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 4); (CIndex 0)]).
(** createPartition test : OK *)
Eval vm_compute in  createPartition.

(* Definition initConfigPagesListAux :=
createPartition;; 
Internal.initConfigPagesListAux 20 (CPage 12) (CIndex 0). 
Eval vm_compute in initConfigPagesListAux.  *)

Definition countToPrepare := 
createPartition;;

Services.countToMap (CVaddr [(CIndex 2); (CIndex 0);(CIndex 0)]) (* child *)
                    (CVaddr [(CIndex 2); (CIndex 3);(CIndex 0)]). (* vaddr to prepare in the child *)
(** countToPrepare test : OK *)
Eval vm_compute in  countToPrepare.


Definition prepare := 
createPartition;;
storeVirtual (CVaddr [(CIndex 2); (CIndex 5); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 2); (CIndex 6); CIndex 0]) ;;
storeVirtual (CVaddr [(CIndex 2); (CIndex 6); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 2); (CIndex 7); CIndex 0]) ;;

Services.prepare (CVaddr [(CIndex 2); (CIndex 0); CIndex 0]) (* child *)
                 (CVaddr [(CIndex 3); (CIndex 3); CIndex 0]) (* vaddr to prepare in the child *)
                 (CVaddr [(CIndex 2); (CIndex 5); CIndex 0]).(* fst vaddr lent to the kernel *)
(** prepare test : OK *)
Eval vm_compute in prepare.

 Definition countToPrepare1 := 
prepare;;
Services.countToMap (CVaddr [(CIndex 2); (CIndex 0);(CIndex 0)])
                           (CVaddr [(CIndex 5); (CIndex 3);(CIndex 0)]).
(** countToPrepare test : OK *)
Eval vm_compute in  countToPrepare1.

Definition prepareStore := 
prepare;;
storeVirtual (CVaddr [(CIndex 2); (CIndex 8); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 2); (CIndex 9); CIndex 0]) ;;
storeVirtual (CVaddr [(CIndex 2); (CIndex 9); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 2); (CIndex 9); CIndex 0]) ;;
storeVirtual (CVaddr [(CIndex 2); (CIndex 10); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 2); (CIndex 11); CIndex 0]).
(** prepare test : OK *)
Eval vm_compute in prepareStore.

Definition prepare1:=
prepareStore ;;
Services.prepare (CVaddr [(CIndex 2); (CIndex 0); CIndex 0])
                            (CVaddr [(CIndex 5); (CIndex 2) ; CIndex 0])
                            (CVaddr [(CIndex 2); (CIndex 8); CIndex 0]).
(** prepare test : OK *)
Eval vm_compute in prepare1.

Definition addVAddr := 
prepare ;;
Services.addVAddr (CVaddr [(CIndex 2); (CIndex 9); (CIndex 0)])
         (CVaddr [(CIndex 2); (CIndex 0); (CIndex 0)])
         (CVaddr [(CIndex 3); (CIndex 7); (CIndex 0)])
         false false false .
(** addVaddr test : OK *)
Eval vm_compute in addVAddr. 

Definition mapInChild := 
addVAddr ;; Services.mappedInChild (CVaddr [(CIndex 2); (CIndex 9); (CIndex 0)]).
Eval vm_compute in mapInChild. 
 
Definition removeVAddr := 
addVAddr ;;
Services.removeVAddr (CVaddr [(CIndex 2); (CIndex 0);(CIndex 0)])
                     (CVaddr [(CIndex 3); (CIndex 7);(CIndex 0)]).
(** removeVAddr test : OK *)
Eval vm_compute in removeVAddr.

Definition collect := 
removeVAddr ;;
Services.collect(CVaddr [(CIndex 2); (CIndex 0) ;(CIndex 0)])
                         (CVaddr [(CIndex 3); (CIndex 7) ;(CIndex 0)]).
(** collect test : OK *)
Eval vm_compute in collect.

Definition deletePartition := 
addVAddr ;;
Services.deletePartition (CVaddr [(CIndex 2); (CIndex 0) ;(CIndex 0)]).

(** deletePartition test : OK *)
Eval vm_compute in deletePartition.

(* Definition dispatch := 
addVAddr;;
Services.dispatch (CVaddr [(CIndex 2); (CIndex 0) ;(CIndex 0)]).

(** dispatch test : OK *)
Eval vm_compute in dispatch. *)

Definition memoryVidtNotPresent : list (paddr * value):=
[
 (* Partition Descriptor *)
 (CPage 1, CIndex 0,  VA defaultVAddr) ;
 (CPage 1, CIndex 1,  PP (CPage 1)) ;
 (CPage 1, CIndex 2,  VA defaultVAddr) ;
 (CPage 1, CIndex 3,  PP (CPage 2)) ;
 (CPage 1, CIndex 4,  VA defaultVAddr) ;
 (CPage 1, CIndex 5,  PP (CPage 3)) ;
 (CPage 1, CIndex 6,  VA defaultVAddr) ;
 (CPage 1, CIndex 7,  PP (CPage 4)) ;
 (CPage 1, CIndex 8,  VA defaultVAddr) ;
 (CPage 1, CIndex 9,  PP (CPage 5)) ;
 (CPage 1, CIndex 10, VA defaultVAddr) ;
 (CPage 1, CIndex 11, PP (CPage 7)) ;

 (* MMU root *)
 (CPage 2, CIndex 0,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, Kidx    ,  PE (Build_Pentry false false false true  true  (CPage K ) )) ;
 (CPage 2, CIndex 2,  PE (Build_Pentry false false false true  true  (CPage 6 ) )) ;
 (CPage 2, CIndex 3,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 4,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 5,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 6,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 7,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 8,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 9,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 10, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 11, PE (Build_Pentry false false false true  true  (CPage 99) )) ; (* VIDT root MMU page *)

 (* Shadow 1 *)
 (CPage 3, CIndex 0,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 1,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 2,  PE (Build_Pentry false false false true  true  (CPage 8 ) )) ;
 (CPage 3, CIndex 3,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 4,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 5,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 6,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 7,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 8,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 9,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 10, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 11, PE (Build_Pentry false false false true  true  (CPage 98) )) ;

 (* MMU Tables *)
 (CPage 6, CIndex 0,  PE (Build_Pentry false false false true true (CPage 12))); (* ChildPartDesc *)
 (CPage 6, CIndex 1,  PE (Build_Pentry false false false true true (CPage 13)));
 (CPage 6, CIndex 2,  PE (Build_Pentry false false false true true (CPage 14)));
 (CPage 6, CIndex 3,  PE (Build_Pentry false false false true true (CPage 15)));
 (CPage 6, CIndex 4,  PE (Build_Pentry false false false true true (CPage 16)));
 (CPage 6, CIndex 5,  PE (Build_Pentry false false false true true (CPage 17)));
 (CPage 6, CIndex 6,  PE (Build_Pentry false false false true true (CPage 18)));
 (CPage 6, CIndex 7,  PE (Build_Pentry false false false true true (CPage 19)));
 (CPage 6, CIndex 8,  PE (Build_Pentry false false false true true (CPage 20)));
 (CPage 6, CIndex 9,  PE (Build_Pentry false false false true true (CPage 21)));
 (CPage 6, CIndex 10, PE (Build_Pentry false false false true true (CPage 22)));
 (CPage 6, CIndex 11, PE (Build_Pentry false false false true true (CPage 23)));
 

 (CPage 99, CIndex 0,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 99, CIndex 1,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 99, CIndex 2,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 99, CIndex 3,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 99, CIndex 4,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 99, CIndex 5,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 99, CIndex 6,  PE (Build_Pentry false false false true  true  (CPage 92) ));
 (CPage 99, CIndex 7,  PE (Build_Pentry false false false true  true  (CPage 93) ));
 (CPage 99, CIndex 8,  PE (Build_Pentry false false false true  true  (CPage 94) ));
 (CPage 99, CIndex 9,  PE (Build_Pentry false false false true  true  (CPage 95) ));
 (CPage 99, CIndex 10, PE (Build_Pentry false false false true  true  (CPage 96) ));
 (CPage 99, CIndex 11, PE (Build_Pentry false false false false false defaultPage)); (* VIDT not mapped *)

 (* Shadow 1 Tables *)
 (CPage 8, CIndex 0,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 1,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 2,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 3,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 4,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 5,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 6,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 7,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 8,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 9,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 10, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 11, VE (Build_Ventry false defaultVAddr));

 (CPage 98, CIndex 0,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 1,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 2,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 3,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 4,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 5,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 6,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 7,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 8,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 9,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 10, VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 11, VE (Build_Ventry false defaultVAddr))
].

Definition memoryVidtInaccessible : list (paddr * value):=
[
 (* Partition Descriptor *)
 (CPage 1, CIndex 0,  VA defaultVAddr) ;
 (CPage 1, CIndex 1,  PP (CPage 1)) ;
 (CPage 1, CIndex 2,  VA defaultVAddr) ;
 (CPage 1, CIndex 3,  PP (CPage 2)) ;
 (CPage 1, CIndex 4,  VA defaultVAddr) ;
 (CPage 1, CIndex 5,  PP (CPage 3)) ;
 (CPage 1, CIndex 6,  VA defaultVAddr) ;
 (CPage 1, CIndex 7,  PP (CPage 4)) ;
 (CPage 1, CIndex 8,  VA defaultVAddr) ;
 (CPage 1, CIndex 9,  PP (CPage 5)) ;
 (CPage 1, CIndex 10, VA defaultVAddr) ;
 (CPage 1, CIndex 11, PP (CPage 7)) ;

 (* MMU root *)
 (CPage 2, CIndex 0,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, Kidx    ,  PE (Build_Pentry false false false true  true  (CPage K ) )) ;
 (CPage 2, CIndex 2,  PE (Build_Pentry false false false false false (CPage 6 ) )) ;
 (CPage 2, CIndex 3,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 4,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 5,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 6,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 7,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 8,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 9,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 10, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 11, PE (Build_Pentry false false false true  true  (CPage 99) )) ; (* VIDT root MMU page *)

 (* Shadow 1 *)
 (CPage 3, CIndex 0,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 1,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 2,  PE (Build_Pentry false false false true  true  (CPage 8 ) )) ;
 (CPage 3, CIndex 3,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 4,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 5,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 6,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 7,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 8,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 9,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 10, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 11, PE (Build_Pentry false false false true  true  (CPage 98) )) ;

 (* MMU Tables *)
 (CPage 6, CIndex 0,  PE (Build_Pentry false false false true true (CPage 12))); (* ChildPartDesc *)
 (CPage 6, CIndex 1,  PE (Build_Pentry false false false true true (CPage 13)));
 (CPage 6, CIndex 2,  PE (Build_Pentry false false false true true (CPage 14)));
 (CPage 6, CIndex 3,  PE (Build_Pentry false false false true true (CPage 15)));
 (CPage 6, CIndex 4,  PE (Build_Pentry false false false true true (CPage 16)));
 (CPage 6, CIndex 5,  PE (Build_Pentry false false false true true (CPage 17)));
 (CPage 6, CIndex 6,  PE (Build_Pentry false false false true true (CPage 18)));
 (CPage 6, CIndex 7,  PE (Build_Pentry false false false true true (CPage 19)));
 (CPage 6, CIndex 8,  PE (Build_Pentry false false false true true (CPage 20)));
 (CPage 6, CIndex 9,  PE (Build_Pentry false false false true true (CPage 21)));
 (CPage 6, CIndex 10, PE (Build_Pentry false false false true true (CPage 22)));
 (CPage 6, CIndex 11, PE (Build_Pentry false false false true true (CPage 23)));
 
 (CPage 99, CIndex 0,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 99, CIndex 1,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 99, CIndex 2,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 99, CIndex 3,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 99, CIndex 4,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 99, CIndex 5,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 99, CIndex 6,  PE (Build_Pentry false false false true  true  (CPage 92) ));
 (CPage 99, CIndex 7,  PE (Build_Pentry false false false true  true  (CPage 93) ));
 (CPage 99, CIndex 8,  PE (Build_Pentry false false false true  true  (CPage 94) ));
 (CPage 99, CIndex 9,  PE (Build_Pentry false false false true  true  (CPage 95) ));
 (CPage 99, CIndex 10, PE (Build_Pentry false false false true  true  (CPage 96) ));
 (CPage 99, CIndex 11, PE (Build_Pentry false false false true  false (CPage 97) )); (* VIDT not mapped *)

 (* Shadow 1 Tables *)
 (CPage 8, CIndex 0,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 1,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 2,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 3,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 4,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 5,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 6,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 7,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 8,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 9,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 10, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 11, VE (Build_Ventry false defaultVAddr));

 (CPage 98, CIndex 0,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 1,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 2,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 3,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 4,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 5,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 6,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 7,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 8,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 9,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 10, VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 11, VE (Build_Ventry false defaultVAddr))
].

Definition memoryVidt : list (paddr * value):=
[
 (* Partition Descriptor *)
 (CPage 1, CIndex 0,  VA defaultVAddr) ;
 (CPage 1, CIndex 1,  PP (CPage 1)) ;
 (CPage 1, CIndex 2,  VA defaultVAddr) ;
 (CPage 1, CIndex 3,  PP (CPage 2)) ;
 (CPage 1, CIndex 4,  VA defaultVAddr) ;
 (CPage 1, CIndex 5,  PP (CPage 3)) ;
 (CPage 1, CIndex 6,  VA defaultVAddr) ;
 (CPage 1, CIndex 7,  PP (CPage 4)) ;
 (CPage 1, CIndex 8,  VA defaultVAddr) ;
 (CPage 1, CIndex 9,  PP (CPage 5)) ;
 (CPage 1, CIndex 10, VA defaultVAddr) ;
 (CPage 1, CIndex 11, PP (CPage 7)) ;

 (* MMU root *)
 (CPage 2, CIndex 0,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, Kidx    ,  PE (Build_Pentry false false false true  true  (CPage K ) )) ;
 (CPage 2, CIndex 2,  PE (Build_Pentry false false false true  true  (CPage 6 ) )) ;
 (CPage 2, CIndex 3,  PE (Build_Pentry false false false false false defaultPage)) ; (* not mapped for FAIL_CTX_SAVE_ADDR_VIDT_mmu_table *)
 (CPage 2, CIndex 4,  PE (Build_Pentry false false false true  true  (CPage 50) )) ;
 (CPage 2, CIndex 5,  PE (Build_Pentry false false false false false defaultPage)) ; (* not mapped for FAIL_CTX_SAVE_ADDR_VIDT_end_addr_mmu_table *)
 (CPage 2, CIndex 6,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 7,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 8,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 9,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 10, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 11, PE (Build_Pentry false false false true  true  (CPage 99) )) ;

 (* Shadow 1 *)
 (CPage 3, CIndex 0,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 1,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 2,  PE (Build_Pentry false false false true  true  (CPage 8 ) )) ;
 (CPage 3, CIndex 3,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 4,  PE (Build_Pentry false false false true  true  (CPage 58) )) ;
 (CPage 3, CIndex 5,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 6,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 7,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 8,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 9,  PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 10, PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 11, PE (Build_Pentry false false false true  true  (CPage 98) )) ;

 (* MMU Tables *)
 (CPage 6, CIndex 0,  PE (Build_Pentry false false false true true (CPage 12))); (* ChildPartDesc *)
 (CPage 6, CIndex 1,  PE (Build_Pentry false false false true true (CPage 13)));
 (CPage 6, CIndex 2,  PE (Build_Pentry false false false true true (CPage 14)));
 (CPage 6, CIndex 3,  PE (Build_Pentry false false false true true (CPage 15)));
 (CPage 6, CIndex 4,  PE (Build_Pentry false false false true true (CPage 16)));
 (CPage 6, CIndex 5,  PE (Build_Pentry false false false true true (CPage 17)));
 (CPage 6, CIndex 6,  PE (Build_Pentry false false false true true (CPage 18)));
 (CPage 6, CIndex 7,  PE (Build_Pentry false false false true true (CPage 19)));
 (CPage 6, CIndex 8,  PE (Build_Pentry false false false true true (CPage 20)));
 (CPage 6, CIndex 9,  PE (Build_Pentry false false false true true (CPage 21)));
 (CPage 6, CIndex 10, PE (Build_Pentry false false false true true (CPage 22)));
 (CPage 6, CIndex 11, PE (Build_Pentry false false false true true (CPage 23)));

 (CPage 50, CIndex 0,  PE (Build_Pentry false false false false false defaultPage)); (* not mapped for FAIL_CTX_SAVE_ADDR_VIDT_not_present *)
 (CPage 50, CIndex 1,  PE (Build_Pentry false false false true  false (CPage 51) )); (* mapped but inaccessible for FAIL_CTX_SAVE_ADDR_VIDT_not_accessible  *)
 (CPage 50, CIndex 2,  PE (Build_Pentry false false false true  true  (CPage 52) )); (* valid ctx range, present to test for ctx end addr *)
 (CPage 50, CIndex 3,  PE (Build_Pentry false false false false false defaultPage)); (* not mapped for FAIL_CTX_SAVE_ADDR_VIDT_end_addr_not_present *)
 (CPage 50, CIndex 4,  PE (Build_Pentry false false false true  true  (CPage 54) )); (* valid ctx range, present to test for ctx end addr *)
 (CPage 50, CIndex 5,  PE (Build_Pentry false false false true  false (CPage 55) )); (* mapped but inaccessible for FAIL_CTX_SAVE_ADDR_VIDT_end_addr_not_accessible *)
 (CPage 50, CIndex 6,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 50, CIndex 7,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 50, CIndex 8,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 50, CIndex 9,  PE (Build_Pentry false false false false false defaultPage));
 (CPage 50, CIndex 10, PE (Build_Pentry false false false false false defaultPage));
 (CPage 50, CIndex 11, PE (Build_Pentry false false false true  true  (CPage 53) )); (* valid ctx range, present to test for ctx end addr *)

 (CPage 99, CIndex 0,  PE (Build_Pentry false false false true  true  (CPage 70) ));
 (CPage 99, CIndex 1,  PE (Build_Pentry false false false true  true  (CPage 87) ));
 (CPage 99, CIndex 2,  PE (Build_Pentry false false false true  true  (CPage 88) ));
 (CPage 99, CIndex 3,  PE (Build_Pentry false false false true  true  (CPage 89) ));
 (CPage 99, CIndex 4,  PE (Build_Pentry false false false true  true  (CPage 90) ));
 (CPage 99, CIndex 5,  PE (Build_Pentry false false false true  true  (CPage 91) ));
 (CPage 99, CIndex 6,  PE (Build_Pentry false false false true  true  (CPage 92) ));
 (CPage 99, CIndex 7,  PE (Build_Pentry false false false true  true  (CPage 93) )); (* child valid VIDT *)
 (CPage 99, CIndex 8,  PE (Build_Pentry false false false true  true  (CPage 94) ));
 (CPage 99, CIndex 9,  PE (Build_Pentry false false false true  true  (CPage 95) ));
 (CPage 99, CIndex 10, PE (Build_Pentry false false false true  true  (CPage 96) ));
 (CPage 99, CIndex 11, PE (Build_Pentry false false false true  true  (CPage 97) ));

 (* Shadow 1 Tables *)
 (CPage 8, CIndex 0,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 1,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 2,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 3,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 4,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 5,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 6,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 7,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 8,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 9,  VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 10, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 11, VE (Build_Ventry false defaultVAddr));

 (CPage 58, CIndex 0,  VE (Build_Ventry false defaultVAddr));
 (CPage 58, CIndex 1,  VE (Build_Ventry false defaultVAddr));
 (CPage 58, CIndex 2,  VE (Build_Ventry false defaultVAddr));
 (CPage 58, CIndex 3,  VE (Build_Ventry false defaultVAddr));
 (CPage 58, CIndex 4,  VE (Build_Ventry false defaultVAddr));
 (CPage 58, CIndex 5,  VE (Build_Ventry false defaultVAddr));
 (CPage 58, CIndex 6,  VE (Build_Ventry false defaultVAddr));
 (CPage 58, CIndex 7,  VE (Build_Ventry false defaultVAddr));
 (CPage 58, CIndex 8,  VE (Build_Ventry false defaultVAddr));
 (CPage 58, CIndex 9,  VE (Build_Ventry false defaultVAddr));
 (CPage 58, CIndex 10, VE (Build_Ventry false defaultVAddr));
 (CPage 58, CIndex 11, VE (Build_Ventry false defaultVAddr));

 (CPage 98, CIndex 0,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 1,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 2,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 3,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 4,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 5,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 6,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 7,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 8,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 9,  VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 10, VE (Build_Ventry false defaultVAddr));
 (CPage 98, CIndex 11, VE (Build_Ventry false defaultVAddr))
].


Definition initWithVidtNotPresent : state := 
Build_state multiplexer memoryVidtNotPresent.

Definition initWithVidtInaccessible : state := 
Build_state multiplexer memoryVidtInaccessible.

Definition initWithVidt : state := 
Build_state multiplexer memoryVidt.

Definition createPartitionVidtNotPresent :=
put initWithVidtNotPresent ;;
Services.createPartition (CVaddr [(CIndex 2); (CIndex 0);(CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 1);(CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 2);(CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 3);(CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 4);(CIndex 0)]).

Definition createPartitionVidtInaccessible :=
put initWithVidtInaccessible ;;
Services.createPartition (CVaddr [(CIndex 2); (CIndex 0);(CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 1);(CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 2);(CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 3);(CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 4);(CIndex 0)]).

Definition createPartitionVidt :=
put initWithVidt ;;
Services.createPartition (CVaddr [(CIndex 2); (CIndex 0);(CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 1);(CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 2);(CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 3);(CIndex 0)])
                         (CVaddr [(CIndex 2); (CIndex 4);(CIndex 0)]).

Definition prepareChildVidtMMURoot :=
createPartition ;;
storeVirtual (CVaddr [(CIndex 2); (CIndex 5); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 2); (CIndex 6); CIndex 0]) ;;
storeVirtual (CVaddr [(CIndex 2); (CIndex 6); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 2); (CIndex 7); CIndex 0]) ;;

Services.prepare (CVaddr [(CIndex  2); (CIndex  0); CIndex 0])
                 (CVaddr [(CIndex 11); (CIndex 11); CIndex 0])
                 (CVaddr [(CIndex  2); (CIndex  5); CIndex 0]) false.

Definition prepareChildVidtNotPresent :=
createPartitionVidtNotPresent ;;
storeVirtual (CVaddr [(CIndex 11); (CIndex 8 ); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 11); (CIndex 9 ); CIndex 0]) ;;
storeVirtual (CVaddr [(CIndex 11); (CIndex 9 ); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 11); (CIndex 10); CIndex 0]) ;;
(* store pointers *)
storeVirtual (CVaddr [(CIndex 11); (CIndex 7 ); CIndex 2]) (CIndex 2)
             (CVaddr [(CIndex 6 ); (CIndex 6 ); CIndex 6]) ;;
storeVirtual (CVaddr [(CIndex 11); (CIndex 7 ); CIndex 3]) (CIndex 3)
             (CVaddr [(CIndex 7 ); (CIndex 7 ); CIndex 7]) ;;

Services.prepare (CVaddr [(CIndex 2 ); (CIndex  0); CIndex 0])
                 (CVaddr [(CIndex 11); (CIndex  0); CIndex 0])
                 (CVaddr [(CIndex 11); (CIndex  8); CIndex 0]) false.

Definition prepareChildVidtInaccessible :=
createPartitionVidtInaccessible ;;
storeVirtual (CVaddr [(CIndex 11); (CIndex 8 ); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 11); (CIndex 9 ); CIndex 0]) ;;
storeVirtual (CVaddr [(CIndex 11); (CIndex 9 ); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 11); (CIndex 10); CIndex 0]) ;;
(* store pointers *)
storeVirtual (CVaddr [(CIndex 11); (CIndex 7 ); CIndex 2]) (CIndex 2)
             (CVaddr [(CIndex 6 ); (CIndex 6 ); CIndex 6]) ;;
storeVirtual (CVaddr [(CIndex 11); (CIndex 7 ); CIndex 3]) (CIndex 3)
             (CVaddr [(CIndex 7 ); (CIndex 7 ); CIndex 7]) ;;

Services.prepare (CVaddr [(CIndex 2 ); (CIndex  0); CIndex 0])
                 (CVaddr [(CIndex 11); (CIndex  0); CIndex 0])
                 (CVaddr [(CIndex 11); (CIndex  8); CIndex 0]) false.

Definition prepareChildVidt :=
createPartitionVidt ;;
storeVirtual (CVaddr [(CIndex 11); (CIndex 8 ); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 11); (CIndex 9 ); CIndex 0]) ;;
storeVirtual (CVaddr [(CIndex 11); (CIndex 9 ); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 11); (CIndex 10); CIndex 0]) ;;
(* store pointers *)
storeVirtual (CVaddr [(CIndex 11); (CIndex 7 ); CIndex 2]) (CIndex 2)
             (CVaddr [(CIndex 6 ); (CIndex 6 ); CIndex 6]) ;;
storeVirtual (CVaddr [(CIndex 11); (CIndex 7 ); CIndex 3]) (CIndex 3)
             (CVaddr [(CIndex 7 ); (CIndex 7 ); CIndex 7]) ;;

Services.prepare (CVaddr [(CIndex 2 ); (CIndex  0); CIndex 0])
                 (CVaddr [(CIndex 11); (CIndex  0); CIndex 0])
                 (CVaddr [(CIndex 11); (CIndex  8); CIndex 0]) false.

Definition addChildVidtMMURoot :=
prepareChildVidtMMURoot ;;
Services.addVAddr (CVaddr [(CIndex 2 ); (CIndex 8 ); (CIndex 0)])
                  (CVaddr [(CIndex 2 ); (CIndex 0 ); (CIndex 0)])
                  (CVaddr [(CIndex 11); (CIndex 11); (CIndex 0)])
                  false false false.

Definition addChildVidtNotPresent :=
prepareChildVidtNotPresent ;;
Services.addVAddr (CVaddr [(CIndex 11); (CIndex 7 ); (CIndex 0)])
                  (CVaddr [(CIndex 2 ); (CIndex 0 ); (CIndex 0)])
                  (CVaddr [(CIndex 11); (CIndex 11); (CIndex 0)])
                  false false false.

Definition addChildVidtInaccessible :=
prepareChildVidtInaccessible ;;
Services.addVAddr (CVaddr [(CIndex 11); (CIndex 7 ); (CIndex 0)])
                  (CVaddr [(CIndex 2 ); (CIndex 0 ); (CIndex 0)])
                  (CVaddr [(CIndex 11); (CIndex 11); (CIndex 0)])
                  false false false.

Definition addChildVidt :=
prepareChildVidt ;;
Services.addVAddr (CVaddr [(CIndex 11); (CIndex 7 ); (CIndex 0)])
                  (CVaddr [(CIndex 2 ); (CIndex 0 ); (CIndex 0)])
                  (CVaddr [(CIndex 11); (CIndex 11); (CIndex 0)])
                  false false false.

(*
Definition testYield_FAIL_VINT :=
Services.yield   defaultVAddr
                 15 (* > maxVint *)
                 0
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_VINT.


Definition testYield_FAIL_CTX_SAVE_INDEX :=
put initWithVidt ;;
Services.yield   defaultVAddr
                 1
                 15
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_CTX_SAVE_INDEX.


Definition testYield_FAIL_CALLER_VIDT_mmu_table :=
put init ;; (* no vidt mapped in caller *)
Services.yield   defaultVAddr (* targetPartitionDesc *)
                 1 (* vint *)
                 0 (* contextSaveIndex *)
                 (CIntMask []) (* flagsOnWake *)
                 (CIntMask []) (* flagsOnYield *)
                 0 (* interruptedContext *).

Eval vm_compute in testYield_FAIL_CALLER_VIDT_mmu_table.


Definition testYield_FAIL_CALLER_VIDT_not_present :=
put initWithVidtNotPresent ;; (* no vidt mapped in last MMU table *)
Services.yield   defaultVAddr (* targetPartitionDesc *)
                 1 (* vint *)
                 0 (* contextSaveIndex *)
                 (CIntMask []) (* flagsOnWake *)
                 (CIntMask []) (* flagsOnYield *)
                 0 (* interruptedContext *).

Eval vm_compute in testYield_FAIL_CALLER_VIDT_not_present.


Definition testYield_FAIL_CALLER_VIDT_inaccessible :=
put initWithVidtInaccessible ;; (* vidt mapped but kernelland *)
Services.yield   defaultVAddr (* targetPartitionDesc *)
                 1 (* vint *)
                 0 (* contextSaveIndex *)
                 (CIntMask []) (* flagsOnWake *)
                 (CIntMask []) (* flagsOnYield *)
                 0 (* interruptedContext *).

Eval vm_compute in testYield_FAIL_CALLER_VIDT_inaccessible.

*)
(** Child to parent specific tests *)

Definition testYield_FAIL_ROOT_CALLER :=
put initWithVidt;;
Services.yield defaultVAddr (* targetPartitionDesc *)
               1 (* vint *)
               0 (* contextSaveIndex *)
               (CIntMask []) (* flagsOnWake *)
               (CIntMask []) (* flagsOnYield *)
               0 (* interruptedContext *).

Eval vm_compute in testYield_FAIL_ROOT_CALLER.

(** Parent to child specific tests *)


Definition testYield_FAIL_INVALID_CHILD_mmu_root :=
put initWithVidt ;;
Services.yield   (CVaddr [(CIndex 3); (CIndex 0) ;(CIndex 0)])
                 1 (* > maxVint *)
                 0
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_INVALID_CHILD_mmu_root.

Definition testYield_FAIL_INVALID_CHILD_not_present :=
put initWithVidt ;;
Services.yield   (CVaddr [(CIndex 4); (CIndex 0) ;(CIndex 0)])
                 1 (* > maxVint *)
                 0
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_INVALID_CHILD_not_present.

Definition testYield_FAIL_INVALID_CHILD_not_a_child :=
put initWithVidt ;;
Services.yield   (CVaddr [(CIndex 4); (CIndex 5) ;(CIndex 0)])
                 1 (* > maxVint *)
                 0
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_INVALID_CHILD_not_a_child.





Definition testYield_FAIL_CTX_SAVE_ADDR_VIDT_mmu_table :=
put initWithVidt ;;
Services.yield   defaultVAddr
                 1
                 (CVaddr [(CIndex 3); (CIndex 0); (CIndex 0)]) (*First CIndex is not mapped to a physical page*)
                 (CIndex 0)
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_CTX_SAVE_ADDR_VIDT_mmu_table.

Definition testYield_FAIL_CTX_SAVE_ADDR_VIDT_not_present :=
put initWithVidt ;;
Services.yield   defaultVAddr
                 1
                 (CVaddr [(CIndex 4); (CIndex 0) ;(CIndex 0)]) (*Second CIndex is not mapped to a physical page*)
                 (CIndex 0)
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_CTX_SAVE_ADDR_VIDT_not_present.

Definition testYield_FAIL_CTX_SAVE_ADDR_VIDT_not_accessible :=
put initWithVidt ;;
Services.yield   defaultVAddr
                 1
                 (CVaddr [(CIndex 4); (CIndex 1) ;(CIndex 0)]) (*Second CIndex is mapped but unaccessible *)
                 (CIndex 0)
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_CTX_SAVE_ADDR_VIDT_not_accessible.

Definition testYield_FAIL_CTX_SAVE_ADDR_VIDT_end_addr_overflow :=
put initWithVidt ;;
Services.yield   defaultVAddr
                 1
                 (CVaddr [(CIndex 11); (CIndex 11) ;(CIndex 11)]) (* vaddr is mapped but ctx end addr will overflow *)
                 (CIndex 0)
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_CTX_SAVE_ADDR_VIDT_end_addr_overflow.

Definition testYield_FAIL_CTX_SAVE_ADDR_VIDT_end_addr_mmu_table :=
put initWithVidt ;;
Services.yield   defaultVAddr
                 1
                 (CVaddr [(CIndex 4); (CIndex 11) ;(CIndex 8)]) (* vaddr is mapped but ctx end addr will have no MMU root page *)
                 (CIndex 0)
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_CTX_SAVE_ADDR_VIDT_end_addr_mmu_table.

Definition testYield_FAIL_CTX_SAVE_ADDR_VIDT_end_addr_not_present :=
put initWithVidt ;;
Services.yield   defaultVAddr
                 1
                 (CVaddr [(CIndex 4); (CIndex 2) ;(CIndex 8)]) (* vaddr is mapped but ctx end addr will have no MMU leaf page *)
                 (CIndex 0)
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_CTX_SAVE_ADDR_VIDT_end_addr_not_present.

Definition testYield_FAIL_CTX_SAVE_ADDR_VIDT_end_addr_not_accessible :=
put initWithVidt ;;
Services.yield   defaultVAddr
                 1
                 (CVaddr [(CIndex 4); (CIndex 4) ;(CIndex 8)]) (* vaddr is mapped but ctx end addr will have no MMU leaf page *)
                 (CIndex 0)
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_CTX_SAVE_ADDR_VIDT_end_addr_not_accessible. 








Definition testYield_from_child_FAIL_TARGET_VIDT_mmu_root :=
addChildVidtMMURoot ;;
activate((CPage 12)) ;;
Services.yield   defaultVAddr (* targetPartitionDesc *)
                 1 (* vint *)
                 defaultVAddr (* contextSaveAddr *)
                 (CIndex 0) (* contextSaveIndex *)
                 (CIntMask []) (* flagsOnWake *)
                 (CIntMask []) (* flagsOnYield *)
                 0 (* interruptedContext *).

Eval vm_compute in testYield_from_child_FAIL_TARGET_VIDT_mmu_root.

Definition testYield_from_child_FAIL_TARGET_VIDT_not_present :=
addChildVidtNotPresent ;;
activate((CPage 12)) ;;
Services.yield   defaultVAddr (* targetPartitionDesc *)
                 1 (* vint *)
                 defaultVAddr (* contextSaveAddr *)
                 (CIndex 0) (* contextSaveIndex *)
                 (CIntMask []) (* flagsOnWake *)
                 (CIntMask []) (* flagsOnYield *)
                 0 (* interruptedContext *).

Eval vm_compute in testYield_from_child_FAIL_TARGET_VIDT_not_present.

Definition testYield_from_child_FAIL_TARGET_VIDT_not_accessible :=
addChildVidtInaccessible ;;
activate((CPage 12)) ;;
Services.yield   defaultVAddr (* targetPartitionDesc *)
                 1 (* vint *)
                 defaultVAddr (* contextSaveAddr *)
                 (CIndex 0) (* contextSaveIndex *)
                 (CIntMask []) (* flagsOnWake *)
                 (CIntMask []) (* flagsOnYield *)
                 0 (* interruptedContext *).

Eval vm_compute in testYield_from_child_FAIL_TARGET_VIDT_not_accessible.

(* Can't test if interrupts are masked, because it is not implemented in the model *)

Definition testYield_SUCCESS_FROM_CHILD_no_save :=
addChildVidt ;;
activate((CPage 12)) ;;
Services.yield   defaultVAddr
                 1 (* vint *)
                 defaultVAddr
                 (CIndex 0)
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_SUCCESS_FROM_CHILD_no_save.



Definition testYield_FAIL_TARGET_VIDT_mmu_root :=
createPartitionVidt ;;
Services.yield   (CVaddr [(CIndex 2); (CIndex 0) ;(CIndex 0)])
                 1 (* > maxVint *)
                 defaultVAddr
                 (CIndex 0)
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_TARGET_VIDT_mmu_root.

Definition testYield_FAIL_TARGET_VIDT_not_present :=
prepareChildVidt ;;
Services.yield   (CVaddr [(CIndex 2); (CIndex 0) ;(CIndex 0)])
                 1 (* > maxVint *)
                 defaultVAddr
                 (CIndex 0)
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_TARGET_VIDT_not_present.

(* TODO : midly tricky - Map yet another child inside the child and give it the VIDT *)
Definition testYield_FAIL_TARGET_VIDT_not_accessible :=
addChildVidt ;;
(* giving to child 4 more pages to be able to map a child in the child *)
Services.addVAddr (CVaddr [(CIndex  2); (CIndex  8); (CIndex  0)])
                  (CVaddr [(CIndex  2); (CIndex  0); (CIndex  0)])
                  (CVaddr [(CIndex 11); (CIndex  7); (CIndex  0)])
                  false false false ;;
Services.addVAddr (CVaddr [(CIndex  2); (CIndex  9); (CIndex  0)])
                  (CVaddr [(CIndex  2); (CIndex  0); (CIndex  0)])
                  (CVaddr [(CIndex 11); (CIndex  8); (CIndex  0)])
                  false false false ;;
Services.addVAddr (CVaddr [(CIndex  2); (CIndex 10); (CIndex  0)])
                  (CVaddr [(CIndex  2); (CIndex  0); (CIndex  0)])
                  (CVaddr [(CIndex 11); (CIndex  9); (CIndex  0)])
                  false false false ;;
Services.addVAddr (CVaddr [(CIndex  2); (CIndex 11); (CIndex  0)])
                  (CVaddr [(CIndex  2); (CIndex  0); (CIndex  0)])
                  (CVaddr [(CIndex 11); (CIndex 10); (CIndex  0)])
                  false false false ;;
(* switch to child partition *)
activate((CPage 12)) ;;
(* create a grandchild partition whose parent is the child, and give the kernel the child's VIDT  *)
Services.createPartition (CVaddr [(CIndex 11); (CIndex 11);(CIndex 0)])
                         (CVaddr [(CIndex 11); (CIndex 10);(CIndex 0)])
                         (CVaddr [(CIndex 11); (CIndex  9);(CIndex 0)])
                         (CVaddr [(CIndex 11); (CIndex  8);(CIndex 0)])
                         (CVaddr [(CIndex 11); (CIndex  7);(CIndex 0)]) ;;
(* switch back to the root partition *)
activate((CPage  1)) ;;
(* try to pass the execution flow to the child, whose VIDT isn't accessible anymore *)
Services.yield   (CVaddr [(CIndex 2); (CIndex 0) ;(CIndex 0)])
                 1 (* > maxVint *)
                 defaultVAddr
                 (CIndex 0)
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_FAIL_TARGET_VIDT_not_accessible.

Definition testYield_from_parent_FAIL_TARGET_CTX_mmu_root :=
addChildVidt ;;
writeVirtual   (CPage 93) (CIndex 1) (* Index 1 in child VIDT *)
               (CVaddr [(CIndex  9); (CIndex  0); (CIndex 0)]);; (* not mapped in child *)
Services.yield (CVaddr [(CIndex  2); (CIndex  0); (CIndex 0)])
               1 (* > maxVint *)
               defaultVAddr
               0 (* saveIndex *)
               (CIntMask [])
               (CIntMask [])
               0.

Eval vm_compute in testYield_from_parent_FAIL_TARGET_CTX_mmu_root.

Definition testYield_from_parent_FAIL_TARGET_CTX_not_present :=
addChildVidt ;;
writeVirtual   (CPage 93) (CIndex 1) (* Index 1 in child VIDT *)
               (CVaddr [(CIndex 11); (CIndex  5); (CIndex 0)]);; (* not mapped in child, but 11,11 is mapped *)
Services.yield (CVaddr [(CIndex  2); (CIndex  0); (CIndex 0)])
               1 (* > maxVint *)
               defaultVAddr
               0 (* saveIndex *)
               (CIntMask [])
               (CIntMask [])
               0.

Eval vm_compute in testYield_from_parent_FAIL_TARGET_CTX_not_present.

(* Midly tricky again, create a child inside a child to make pages inaccessible *)
Definition testYield_from_parent_FAIL_TARGET_CTX_not_accessible :=
addChildVidt ;;
writeVirtual   (CPage 93) (CIndex 1) (* Index 1 in child VIDT *)
               (CVaddr [(CIndex  11); (CIndex 1); (CIndex 0)]);; (* Page is mapped, but kernel-land *)
(* giving to child 5 more pages to be able to map a child in the child *)
Services.addVAddr (CVaddr [(CIndex 11); (CIndex  1); (CIndex  0)])
                  (CVaddr [(CIndex  2); (CIndex  0); (CIndex  0)])
                  (CVaddr [(CIndex 11); (CIndex  1); (CIndex  0)])
                  false false false ;;
Services.addVAddr (CVaddr [(CIndex 11); (CIndex  2); (CIndex  0)])
                  (CVaddr [(CIndex  2); (CIndex  0); (CIndex  0)])
                  (CVaddr [(CIndex 11); (CIndex  2); (CIndex  0)])
                  false false false ;;
Services.addVAddr (CVaddr [(CIndex 11); (CIndex  3); (CIndex  0)])
                  (CVaddr [(CIndex  2); (CIndex  0); (CIndex  0)])
                  (CVaddr [(CIndex 11); (CIndex  3); (CIndex  0)])
                  false false false ;;
Services.addVAddr (CVaddr [(CIndex 11); (CIndex  4); (CIndex  0)])
                  (CVaddr [(CIndex  2); (CIndex  0); (CIndex  0)])
                  (CVaddr [(CIndex 11); (CIndex  4); (CIndex  0)])
                  false false false ;;
Services.addVAddr (CVaddr [(CIndex 11); (CIndex  5); (CIndex  0)])
                  (CVaddr [(CIndex  2); (CIndex  0); (CIndex  0)])
                  (CVaddr [(CIndex 11); (CIndex  5); (CIndex  0)])
                  false false false ;;
(* switch to child partition *)
activate((CPage 12)) ;;
(* create a grandchild partition whose parent is the child, and give the kernel the child's VIDT  *)
Services.createPartition (CVaddr [(CIndex 11); (CIndex  1);(CIndex 0)])
                         (CVaddr [(CIndex 11); (CIndex  2);(CIndex 0)])
                         (CVaddr [(CIndex 11); (CIndex  3);(CIndex 0)])
                         (CVaddr [(CIndex 11); (CIndex  4);(CIndex 0)])
                         (CVaddr [(CIndex 11); (CIndex  5);(CIndex 0)]) ;;
(* switch back to the root partition *)
activate((CPage  1)) ;;
(* try to pass the execution flow to the child, whose VIDT isn't accessible anymore *)
Services.yield (CVaddr [(CIndex  2); (CIndex  0); (CIndex 0)])
               1 (* > maxVint *)
               defaultVAddr
               0 (* saveIndex *)
               (CIntMask [])
               (CIntMask [])
               0.

Eval vm_compute in testYield_from_parent_FAIL_TARGET_CTX_not_accessible.

Definition testYield_from_parent_FAIL_TARGET_CTX_end_overflow :=
addChildVidt ;;
writeVirtual   (CPage 93) (CIndex 1) (* Index 1 in child VIDT *)
               (CVaddr [(CIndex 11); (CIndex 11); (CIndex 11)]);; (* mapped in child, but will overflow *)
Services.yield (CVaddr [(CIndex  2); (CIndex  0); (CIndex  0)])
               1 (* > maxVint *)
               defaultVAddr
               0 (* saveIndex *)
               (CIntMask [])
               (CIntMask [])
               0.

Eval vm_compute in testYield_from_parent_FAIL_TARGET_CTX_end_overflow.

Definition testYield_from_parent_FAIL_TARGET_CTX_end_mmu_root :=
addChildVidt ;;
(* Services.countToMap (CVaddr [(CIndex  2); (CIndex  0); (CIndex 0)])
                  (CVaddr [(CIndex  9); (CIndex  0); (CIndex 0)]).  *)
storeVirtual (CVaddr [(CIndex 11); (CIndex  2); (CIndex  0)]) (CIndex 0)
             (CVaddr [(CIndex 11); (CIndex  3); (CIndex  0)]) ;;
storeVirtual (CVaddr [(CIndex 11); (CIndex  3); (CIndex  0)]) (CIndex 0)
             (CVaddr [(CIndex 11); (CIndex  4); (CIndex  0)]) ;;
storeVirtual (CVaddr [(CIndex 11); (CIndex  4); (CIndex  0)]) (CIndex 0)
             (CVaddr [(CIndex 11); (CIndex  5); (CIndex  0)]) ;;
Services.prepare  (CVaddr [(CIndex  2); (CIndex  0); (CIndex 0)])
                  (CVaddr [(CIndex  9); (CIndex  0); (CIndex 0)])
                  (CVaddr [(CIndex 11); (CIndex  2); (CIndex 0)]) true ;;
Services.addVAddr (CVaddr [(CIndex 11); (CIndex  1); (CIndex  0)])
                  (CVaddr [(CIndex  2); (CIndex  0); (CIndex  0)])
                  (CVaddr [(CIndex  9); (CIndex 11); (CIndex  0)])
                  false false false ;;

writeVirtual   (CPage 93) (CIndex 1) (* Index 1 in child VIDT *)
               (CVaddr [(CIndex  9); (CIndex 11); (CIndex 11)]);; (* mapped in child, but will overflow *)
Services.yield (CVaddr [(CIndex  2); (CIndex  0); (CIndex  0)])
               1 (* > maxVint *)
               defaultVAddr
               0 (* saveIndex *)
               (CIntMask [])
               (CIntMask [])
               0.

Eval vm_compute in testYield_from_parent_FAIL_TARGET_CTX_end_mmu_root.

(*
Definition testYield_SUCCESS_FROM_ROOT_no_save :=
addChildVidt ;;
Services.yield   (CVaddr [(CIndex 2); (CIndex 0) ;(CIndex 0)])
                 1 (* > maxVint *)
                 defaultVAddr
                 (CIndex 0)
                 (CIntMask [])
                 (CIntMask [])
                 0.

Eval vm_compute in testYield_SUCCESS_FROM_ROOT_no_save.

Definition testYield_SUCCESS_FROM_ROOT_save :=
addChildVidt ;;
Services.yield   (CVaddr [(CIndex 2); (CIndex 0) ;(CIndex 0)])
                 1 (* > maxVint *)
                 (CVaddr [(CIndex 11); (CIndex 0) ;(CIndex 0)])
                 (CIndex 0)
                 (CIntMask [])
                 (CIntMask [])
                 0.


Eval vm_compute in testYield_SUCCESS_FROM_ROOT_save.*)

   END SIMULATION *)

