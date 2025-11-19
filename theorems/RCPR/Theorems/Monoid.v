Require Import RCPR.Data.Monoid.
Require Import RCPR.Data.Semigroup.

Import Monoid.
Import Semigroup.

Module Monoid.

Section MonoidTheories.
    Variable S : Type -> Type.
    Context `{Monoid S}.

    Open Scope semigroup_scope.

    (* verify right associative identity. *)
    Lemma identity_right : forall {t : Type} (x : S t),
        x <o> mempty = x.
    Proof.
        intros.
        apply mempty_right.
    Qed.

    (* verify left associative identity. *)
    Lemma identity_left : forall {t : Type} (x : S t),
        mempty <o> x = x.
    Proof.
        intros.
        apply mempty_left.
    Qed.
End MonoidTheories.

End Monoid.
