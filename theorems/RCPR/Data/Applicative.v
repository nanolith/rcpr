Module Applicative.

(* The Applicative Functor provides a way to lift both functions and values *)
(* to a functor space. *)
Class Applicative (A : Type -> Type) := {
    pure : forall {t : Type}, t -> A t;
    app : forall {a b : Type}, A (a -> b) -> A a -> A b
}.

End Applicative.
