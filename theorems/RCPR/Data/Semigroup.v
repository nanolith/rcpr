Require Import RCPR.Helpers.Notation.

Import Notation.

Module Semigroup.

(* The Semigroup typeclass provides a single computation operation that has *)
(* associativity. *)
Class Semigroup (S: Type → Type) := {
    op : ∀ {a : Type}, S a → S a → S a;
    op_assoc : ∀ {a : Type} (x y z : S a), op x (op y z) = op (op x y) z
}.

Declare Scope semigroup_scope.

Delimit Scope semigroup_scope with semigroup.

(* The <o> operator maps to op. *)
Infix "⊙" := op (at level 65, left associativity) : semigroup_scope.

(* Gather the implicit type A parameter from implicit context. *)
Arguments op {S} {_} {A} _ : rename.

End Semigroup.
