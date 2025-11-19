Module Functor.

(* The Functor provides a way to map a function into a functor space. *)
Class Functor (F : Type -> Type) := {
    fmap : forall {A B : Type} , (A -> B) -> F A -> F B;
    functor_id : forall {A : Type} (x : F A),
        fmap (fun a => a) x = x;
    functor_comp : forall {A B C : Type} (f : A -> B) (g : B -> C) (x : F A),
        fmap (fun y => g (f y)) x = fmap g (fmap f x)
}.

End Functor.
