Module Applicative.

(* The Applicative Functor provides a way to lift both functions and values *)
(* to a functor space. *)
Class Applicative (A : Type -> Type) := {
    pure : forall {t : Type}, t -> A t;
    app : forall {a b : Type}, A (a -> b) -> A a -> A b
}.

Declare Scope applicative_scope.

Delimit Scope applicative_scope with applicative.

(* The ⊛ operator maps to app. *)
Infix "⊛" := app (at level 65, left associativity) : applicative_scope.

(* Gather the implicit type t parameter from implicit context. *)
Arguments app {A} {_} {t} _ : rename.

End Applicative.
