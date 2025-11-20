Require Import RCPR.Data.Functor.
Require Import RCPR.Helpers.Notation.

Import Functor.
Import Notation.

Module Applicative.

(* The Applicative Functor provides a way to lift both functions and values *)
(* to a functor space. *)
Class Applicative (A : Type → Type) `{Functor A} := {
    pure : ∀ {t : Type}, t → A t;
    ap : ∀ {a b : Type}, A (a → b) → A a → A b;
    (* Identity property. *)
    ap_id : ∀ {t : Type} (v : A t),
        ap (pure (λ x ↦ x)) v = v;
    (* Composition property. *)
    ap_comp : ∀ {X Y Z : Type} (u : A (Y → Z)) (v : A (X → Y)) (w : A X),
        ap (ap (ap (pure (λ g f x ↦ g (f x))) u) v) w = ap u (ap v w);
    (* Homomorphism property. *)
    ap_hmorph : ∀ {X Y : Type} (f : X → Y) (x : X),
        ap (pure f) (pure x) = pure (f x);
}.

Declare Scope applicative_scope.

Delimit Scope applicative_scope with applicative.

(* The ⊛ operator maps to ap. *)
Infix "⊛" := ap (at level 65, left associativity) : applicative_scope.

(* Gather the implicit type t parameter from implicit context. *)
Arguments ap {A} {_} {t} _ : rename.

End Applicative.
