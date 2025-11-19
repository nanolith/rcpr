Require Import RCPR.Data.Semigroup.

Import Semigroup.

Module Semigroup.

Section SemigroupTheories.
    Variable A : Type.
    Context `{Semigroup A}.

    Open Scope semigroup_scope.

    (* verify associativity. *)
    Lemma simple_assoc : forall x y z : A,
        x <o> (y <o> z) = (x <o> y) <o> z.
    Proof.
        intros.
        apply op_assoc.
    Qed.
End SemigroupTheories.

End Semigroup.
