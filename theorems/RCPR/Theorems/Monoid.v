Require Import RCPR.Data.Monoid.
Require Import RCPR.Data.Semigroup.
Require Import RCPR.Helpers.Notation.

Import Monoid.
Import Notation.
Import Semigroup.

Module Monoid.

Section MonoidTheories.
    Variable S : Type -> Type.
    Context `{Monoid S}.

    Open Scope semigroup_scope.

    (* verify right associative identity. *)
    Lemma identity_right : ∀ {t : Type} (x : S t),
        x ⊙ mempty = x.
    Proof.
        intros.
        apply mempty_right.
    Qed.

    (* verify left associative identity. *)
    Lemma identity_left : ∀ {t : Type} (x : S t),
        mempty ⊙ x = x.
    Proof.
        intros.
        apply mempty_left.
    Qed.
End MonoidTheories.

End Monoid.
