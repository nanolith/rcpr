Module Semigroup.

(* The Semigroup typeclass provides a single computation operation that has *)
(* associativity. *)
Class Semigroup (S: Type -> Type) : Type := {
    op : forall {a : Type}, S a -> S a -> S a;
}.

End Semigroup.
