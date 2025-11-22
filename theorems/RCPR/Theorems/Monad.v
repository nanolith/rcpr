Require Import RCPR.Data.Applicative.
Require Import RCPR.Data.Monad.
Require Import RCPR.Data.Functor.
Require Import RCPR.Helpers.Notation.

Import Applicative.
Import Functor.
Import Monad.
Import Notation.

Module Monad.

Section MonadTheories.
    Variable M : Type → Type.
    Context `{Monad M}.

    Open Scope applicative_scope.
    Open Scope functor_scope.
    Open Scope monad_scope.

    (* verify left identity. *)
    Lemma left_identity : ∀ {A B : Type} (x : A) (f : A → M B),
        (ret x) ▶ f = f x.
    Proof.
        intros.
        apply monad_left_id.
    Qed.

    (* verify right identity. *)
    Lemma right_identity: ∀ {A : Type} (m : M A),
        m ▶ ret = m.
    Proof.
        intros.
        apply monad_right_id.
    Qed.

    (* verify associativity. *)
    Lemma associativity: ∀ {A B C : Type} (m : M A) (f : A → M B) (g : B → M C),
        m ▶ f ▶ g = m ▶ (λ x ↦ f x ▶ g).
    Proof.
        intros.
        apply monad_assoc.
    Qed.
End MonadTheories.

End Monad.
