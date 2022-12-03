From Pip.Model.Isolation Require Import IsolationTypes IsolationState IsolationInterface.
From Pip.Proof.Isolation Require Import ModelExclusiveFunctions.

Require Import List.

Import IsolationTypes.

(** THE VERTICAL SHARING PROPERTY:
    All child used pages (configuration tables and mapped pages) are mapped into 
    the parent partition  *)
Definition verticalSharing s : Prop :=
forall parent child : page,
  In parent (getPartitions pageRootPartition s) ->
  In child (getChildren parent s) ->
  incl (getUsedPages child s) (getMappedPages parent s).

(** THE ISOLATION PROPERTY BETWEEN PARTITIONS,
    If we take two different children of a given parent,
    so all their used pages are different  *)
Definition partitionsIsolation  s : Prop :=
forall parent child1 child2 : page ,
  In parent (getPartitions pageRootPartition s)->
  In child1 (getChildren parent s) ->
  In child2 (getChildren parent s) ->
  child1 <> child2 ->
  disjoint (getUsedPages child1 s)(getUsedPages child2 s).

(** THE ISOLATION PROPERTY BETWEEN THE KERNEL DATA AND PARTITIONS
    kernel data is the configuration pages of partitions.
    All configuration tables of a given partition are inaccessible by all
    partitions *)
Definition kernelDataIsolation s : Prop :=
forall partition1 partition2,
  In partition1 (getPartitions pageRootPartition s) ->
  In partition2 (getPartitions pageRootPartition s) ->
  disjoint (getAccessibleMappedPages partition1 s) (getConfigPages partition2 s).