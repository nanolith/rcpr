Module Notation.

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
   format "'[' '∀'  x  ..  y ,  '/  ' P ']'") : type_scope.

End Notation.
