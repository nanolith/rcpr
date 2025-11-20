Require Import RCPR.Data.Applicative.
Require Import RCPR.Data.Functor.
Require Import RCPR.Helpers.Notation.

Import Applicative.
Import Functor.
Import Notation.

Module Applicative.

Section ApplicativeTheories.
    Variable A : Type → Type.
    Context `{Applicative A}.

    Open Scope applicative_scope.
    Open Scope functor_scope.

    (* verify ap identity. *)
    Lemma ap_identity : ∀ {t : Type} (v : A t),
        pure (λ x ↦ x) ⊛ v = v.
    Proof.
        intros.
        apply ap_id.
    Qed.

    (* verify ap identity using fmap. *)
    Lemma ap_identity_fmap : ∀ {t : Type} (v : A t),
        (λ x ↦ x) ⟨$⟩ v = v.
    Proof.
        intros.
        unfold fmap.
        apply functor_id.
    Qed.

    (* verify composition using fmap. *)
    Lemma applicative_composition_fmap : ∀ {t u v : Type} (f : t → u)
        (g : u → v) (x : A t),
            (λ y ↦ g (f y)) ⟨$⟩ x = g ⟨$⟩ (f ⟨$⟩ x).
    Proof.
        intros.
        apply functor_comp.
    Qed.
End ApplicativeTheories.

End Applicative.
