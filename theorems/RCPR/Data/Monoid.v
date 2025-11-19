Require Import RCPR.Data.Semigroup.

Import Semigroup.

Module Monoid.

(* The Monoid typeclass provides a way to describe a binary operation with *)
(* identity. *)
Class Monoid (M : Type -> Type) `{S : Semigroup M} := {
    mempty : forall {t : Type}, M t;
    mempty_right : forall {t : Type} (x : M t), op x mempty = x;
    mempty_left : forall {t : Type} (x : M t), op mempty x = x;
}.

End Monoid.
