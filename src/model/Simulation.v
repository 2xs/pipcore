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
Require Import List Core.Services Model.Hardware Isolation IsolationInternal 
Model.ADT Model.MALInternal Model.MAL.
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

 (CPage 2, CIndex 0 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, Kidx, PE (Build_Pentry false false false true true (CPage K))) ; 
 (CPage 2, CIndex 2 ,PE (Build_Pentry false false false true true (CPage 6))) ;
 (CPage 2, CIndex 3 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 4 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 5 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 6 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 7 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 8 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 9 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 10 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 2, CIndex 11 ,PE (Build_Pentry false false false false false defaultPage)) ;

 (CPage 3, CIndex 0 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 1 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 2 ,PE (Build_Pentry false false false true true (CPage 8))) ; 
 (CPage 3, CIndex 3 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 4 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 5 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 6 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 7 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 8 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 9 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 10 ,PE (Build_Pentry false false false false false defaultPage)) ;
 (CPage 3, CIndex 11 ,PE (Build_Pentry false false false false false defaultPage)) ;
 
 
 (CPage 6, CIndex 0, PE (Build_Pentry false false false true true (CPage 12)));
 (CPage 6, CIndex 1, PE (Build_Pentry false false false true true (CPage 13)));
 (CPage 6, CIndex 2, PE (Build_Pentry false false false true true (CPage 14)));
 (CPage 6, CIndex 3, PE (Build_Pentry false false false true true (CPage 15)));
 (CPage 6, CIndex 4, PE (Build_Pentry false false false true true (CPage 16)));
 (CPage 6, CIndex 5, PE (Build_Pentry false false false true true (CPage 17)));
 (CPage 6, CIndex 6, PE (Build_Pentry false false false true true (CPage 18)));
 (CPage 6, CIndex 7, PE (Build_Pentry false false false true true (CPage 19)));
 (CPage 6, CIndex 8, PE (Build_Pentry false false false true true (CPage 20)));
 (CPage 6, CIndex 9, PE (Build_Pentry false false false true true (CPage 21)));
 (CPage 6, CIndex 10, PE (Build_Pentry false false false true true (CPage 22)));
 (CPage 6, CIndex 11, PE (Build_Pentry false false false true true (CPage 23)));
 
 (CPage 8, CIndex 0, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 1, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 2, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 3, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 4, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 5, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 6, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 7, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 8, VE (Build_Ventry false defaultVAddr));
 (CPage 8, CIndex 9, VE (Build_Ventry false defaultVAddr));
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
Services.createPartition (CVaddr [(CIndex 2); (CIndex 0);(CIndex 0)] )
                              (CVaddr [(CIndex 2); (CIndex 1);(CIndex 0)])
                              (CVaddr [(CIndex 2); (CIndex 2);(CIndex 0)])
                              (CVaddr [(CIndex 2); (CIndex 3);(CIndex 0)])
                              (CVaddr [(CIndex 2); (CIndex 4);(CIndex 0)]).
(** createPartition test : OK *)
Eval vm_compute in  createPartition.

Definition countToPrepare := 
createPartition;;
Services.countToPrepare (CVaddr [(CIndex 2); (CIndex 0);(CIndex 0)])
                           (CVaddr [(CIndex 2); (CIndex 3);(CIndex 0)]).
(** countToPrepare test : OK *)
Eval vm_compute in  countToPrepare.

Definition prepare := 
createPartition;;
storeVirtual (CVaddr [(CIndex 2); (CIndex 5); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 2); (CIndex 6); CIndex 0]) ;;
storeVirtual (CVaddr [(CIndex 2); (CIndex 6); CIndex 0]) (CIndex 0)
             (CVaddr [(CIndex 2); (CIndex 7); CIndex 0]) ;;
Services.prepare (CVaddr [(CIndex 2); (CIndex 0); CIndex 0])
                            (CVaddr [(CIndex 3); (CIndex 3) ; CIndex 0])
                            (CVaddr [(CIndex 2); (CIndex 5); CIndex 0]) false.
(** prepare test : OK *)
Eval vm_compute in prepare.

Definition addVAddr := 
prepare ;;
Services.addVAddr (CVaddr [(CIndex 2); (CIndex 9); (CIndex 0)])
         (CVaddr [(CIndex 2); (CIndex 0); (CIndex 0)])
         (CVaddr [(CIndex 3); (CIndex 7); (CIndex 0)])
         false false false .
(** addVaddr test : OK *)
Eval vm_compute in addVAddr. 

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

Definition dispatch := 
addVAddr;;
Services.dispatch (CVaddr [(CIndex 2); (CIndex 0) ;(CIndex 0)]).

(** dispatch test : OK *)
Eval vm_compute in dispatch.  

   END SIMULATION *)

