Require Import RCPR.Data.Applicative.
Require Import RCPR.Helpers.Notation.

Import Applicative.
Import Notation.

Module Applicative.

Section ApplicativeTheories.
    Variable A : Type → Type.
    Context `{Applicative A}.

    Open Scope applicative_scope.

    (* verify ap identity. *)
    Lemma ap_identity : ∀ {t : Type} (v : A t),
        pure (λ x ↦ x) ⊛ v = v.
    Proof.
        intros.
        apply ap_id.
    Qed.
End ApplicativeTheories.

End Applicative.
