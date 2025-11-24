Require Import RCPR.Data.Applicative.
Require Import RCPR.Helpers.Notation.

Import Applicative.
Import Notation.

Module Monad.

(* The Monad provides a way to lift functions and effects into Monadic *)
(* operator space. *)
Class Monad (M : Type → Type) `{Applicative M} := {
    bind : ∀ {A B : Type}, M A → (A → M B) → M B;
    ret : ∀ {A : Type}, A → M A;
    (* Left identity. *)
    monad_left_id : ∀ {A B : Type} (x : A) (f : A → M B),
        bind (ret x) f = f x;
    (* Right identity. *)
    monad_right_id : ∀ {A : Type} (m : M A),
        bind m ret = m;
    (* Associativity. *)
    monad_assoc : ∀ {A B C : Type} (m : M A) (f : A → M B) (g : B → M C),
        bind (bind m f) g = bind m (λ x ↦ bind (f x) g)
}.

Declare Scope monad_scope.
Delimit Scope monad_scope with monad.

(* The ▶ operator maps to bind. *)
Notation "f ▶ g" := (bind f g) (at level 65, left associativity) : monad_scope.

(* The » operator maps to "do". *)
Notation "f » g" :=
    (bind f (λ _ ↦ g)) (at level 65, left associativity) : monad_scope.

End Monad.
