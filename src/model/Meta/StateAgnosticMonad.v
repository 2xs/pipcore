Require Import String.
From Pip.Model.Meta Require Import StateModel.

Module StateAgnosticMonad (Export State : StateModel).

  Inductive result (A : Type) : Type :=
  | val : A -> result A
  | undef : string -> state -> result A.

  Arguments val   [ A ].
  Arguments undef [ A ].

  Definition SAM (A : Type) : Type :=
    state -> result (A * state).

  Definition ret {A : Type} (a : A) : SAM A :=
    fun s => val (a , s).

  Definition bind {A B : Type} (m : SAM A)
                               (f : A -> SAM B)
                               : SAM B :=
    fun s => match m s with
    | val (a, s') => f a s'
    | undef msg s' => undef msg s'
    end.

  Declare Scope state_scope.

  Notation "'perform' x ':=' m 'in' e" := (bind m (fun x => e))
    (
      at level 60, x name, m at level 200, e at level 60,
      format "'[v' '[' 'perform' x ':=' m 'in' ']' '/' '[' e ']' ']'"
    ) : state_scope.

  Notation "m1 ;; m2" := (bind m1 (fun _ => m2))
    (
      at level 60, right associativity
    ) : state_scope.

   Open Scope state_scope.

  Definition put (s : state) : SAM unit :=
    fun _ => val (tt, s).

  Definition get : SAM state :=
    fun s => val (s, s).

  Definition modify (f : state -> state) : SAM unit :=
    perform s := get in
    put (f s).

  Definition undefined {A : Type} (msg : string) : SAM A :=
    fun s => undef msg s.

  Definition hoareTriple {A : Type} (P : state -> Prop)
                                    (m : SAM A)
                                    (Q : A -> state -> Prop)
                                    : Prop :=
    forall s, P s -> match m s with
    | val (a, s') => Q a s'
    | undef _ _=> False
    end.

  Notation "{{ P }} m {{ Q }}" := (hoareTriple P m Q)
    (
      at level 90,
      format "'[' '[' {{  P  }}  ']' '/  ' '[' m ']' '['  {{  Q  }} ']' ']'"
    ) : state_scope.

End StateAgnosticMonad.