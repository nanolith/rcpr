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

    (* Left identity. *)
    monad_left_id : ∀ {A B : Type} (x : A) (f : A → M B),
        bind (ret x) f = f x;
}.

Arguments bind {M} {_} {A B} m f : rename.
Arguments ret  {M} {_} {A} x : rename.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.

(* The ▶ operator maps to bind. *)
Infix "▶" := bind (at level 65, left associativity) : monad_scope.

(* The » operator maps to "do". *)
Notation "f » g" :=
    (bind f (λ _ ↦ g)) (at level 65, left associativity) : monad_scope.

End Monad.
