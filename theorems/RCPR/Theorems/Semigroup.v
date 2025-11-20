Require Import RCPR.Helpers.Notation.
Require Import RCPR.Data.Semigroup.

Import Notation.
Import Semigroup.

Module Semigroup.

Section SemigroupTheories.
    Variable S : Type -> Type.
    Context `{Semigroup S}.

    Open Scope semigroup_scope.

    (* verify associativity. *)
    Lemma simple_assoc : ∀ {a : Type} (x y z : S a),
        x ⊙ (y ⊙ z) = (x ⊙ y) ⊙ z.
    Proof.
        intros.
        apply op_assoc.
    Qed.
End SemigroupTheories.

End Semigroup.
