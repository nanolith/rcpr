Module Semigroup.

(* The Semigroup typeclass provides a single computation operation that has *)
(* associativity. *)
Class Semigroup (S: Type -> Type) : Type := {
    op : forall {a : Type}, S a -> S a -> S a;
}.

Declare Scope semigroup_scope.

Delimit Scope semigroup_scope with semigroup.

(* The <o> operator maps to op. *)
Infix "<o>" := op (at level 65, left associativity) : semigroup_scope.

End Semigroup.
