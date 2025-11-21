Require Import RCPR.Data.Applicative.
Require Import RCPR.Helpers.Notation.

Import Applicative.
Import Notation.

Module Monad.

(* The Monady provides a way to lift functions and effects into Monadic *)
(* operator space. *)
Class Monad (M : Type → Type) `{Applicative M} := {
    bind : ∀ {A B : Type}, M A → (A → M B) → M B;
    ret : ∀ {t : Type}, t → M t;
}.

End Monad.
