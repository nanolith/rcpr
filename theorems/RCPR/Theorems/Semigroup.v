Require Import RCPR.Data.Semigroup.

Import Semigroup.

Module Semigroup.

Section SemigroupTheories.
    Variable S : Type -> Type.
    Context `{Semigroup S}.

    Open Scope semigroup_scope.

    (* verify associativity. *)
    Lemma simple_assoc : forall {a : Type} (x y z : S a),
        x <o> (y <o> z) = (x <o> y) <o> z.
    Proof.
        intros.
        apply op_assoc.
    Qed.
End SemigroupTheories.

End Semigroup.
