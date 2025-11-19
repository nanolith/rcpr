Module Functor.

(* The Functor provides a way to map a function into a functor space. *)
Class Functor (F : Type -> Type) := {
    fmap : forall {A B : Type} , (A -> B) -> F A -> F B;
    functor_id : forall {A : Type} (x : F A),
        fmap (fun a => a) x = x;
    functor_comp : forall {A B C : Type} (f : A -> B) (g : B -> C) (x : F A),
        fmap (fun y => g (f y)) x = fmap g (fmap f x)
}.

Declare Scope functor_scope.

Delimit Scope functor_scope with functor.

(* The ⟨$⟩ operator maps to fmap. *)
Infix "⟨$⟩" := fmap (at level 65, left associativity) : functor_scope.

(* Gather the implicit types A and B from implicit context. *)
Arguments fmap {F} {_} {A B} _ _.

End Functor.
