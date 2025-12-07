Module Notation.

(* Provide nicer forall. *)
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
   format "'[' '∀'  x  ..  y ,  '/  ' P ']'") : type_scope.

(* Provide nicer implication arrow. *)
Reserved Notation "A → B" (at level 99, right associativity, B at level 200).
Notation "A → B" := (forall (_ : A), B) : type_scope.

(* Provide a prettier lambda fun binding. *)
Notation "'λ' x .. y ↦ t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
   format "'[' 'λ'  x  ..  y  ↦  '/  ' t ']'").

(* Provide a nicer existential operator. *)
Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
   format "'[' '∃'  x  ..  y ,  '/  ' P ']'").

(* Provide a nicer conjunction. *)
Reserved Notation "A ∧ B" (at level 80, right associativity).
Notation "A ∧ B" := (and A B).

End Notation.
