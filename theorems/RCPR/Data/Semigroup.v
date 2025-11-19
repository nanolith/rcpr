Module Semigroup.

(* The Semigroup typeclass provides a single computation operation that has *)
(* associativity. *)
Class Semigroup (A: Type) : Type := {
    op : A -> A -> A;
}.

Declare Scope semigroup_scope.

Delimit Scope semigroup_scope with semigroup.

(* The <o> operator maps to op. *)
Infix "<o>" := op (at level 65, left associativity) : semigroup_scope.

(* Gather the implicit type A parameter from implicit context. *)
Arguments op {A} {_} _ _ : rename.

End Semigroup.
