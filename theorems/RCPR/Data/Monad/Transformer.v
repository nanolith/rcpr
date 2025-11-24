Require Import RCPR.Data.Monad.
Require Import RCPR.Helpers.Notation.

Import Monad.
Import Notation.

Module Transformer.

(* MonadTrans provides a way to stack Monad instances. *)
Class MonadTrans (T: (Type → Type) → Type → Type) := {
    lift : ∀ {M : Type → Type} `{Monad M} {A : Type}, M A → T M A;
}.

End Transformer.
