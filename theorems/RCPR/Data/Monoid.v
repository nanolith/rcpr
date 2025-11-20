Require Import RCPR.Data.Semigroup.
Require Import RCPR.Helpers.Notation.

Import Notation.
Import Semigroup.

Module Monoid.

(* The Monoid typeclass provides a way to describe a binary operation with *)
(* identity. *)
Class Monoid (M : Type -> Type) `{S : Semigroup M} := {
    mempty : ∀ {t : Type}, M t;
    mempty_right : ∀ {t : Type} (x : M t), op x mempty = x;
    mempty_left : ∀ {t : Type} (x : M t), op mempty x = x;
}.

End Monoid.
