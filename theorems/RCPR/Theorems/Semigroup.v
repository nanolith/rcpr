Require Import RCPR.Data.Semigroup.

Import Semigroup.

Module Semigroup.

Section SemigroupTheories.
    Variable S : Type -> Type.
    Context `{Semigroup S}.

    Open Scope semigroup_scope.

    (* verify associativity. *)
    Lemma simple_assoc : forall {a : Type} (x y z : S a),
        x ⊙ (y ⊙ z) = (x ⊙ y) ⊙ z.
    Proof.
        intros.
        apply op_assoc.
    Qed.
End SemigroupTheories.

End Semigroup.
