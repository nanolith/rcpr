Require Import RCPR.Helpers.Notation.

Import Notation.

Module FunctionalExtensionality.

Axiom functional_extensionality :
    ∀ {A B : Type} (f g : A → B), (∀ x, f x = g x) → f = g.

End FunctionalExtensionality.
