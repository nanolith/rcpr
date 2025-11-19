Module Functor.

(* The Functor provides a way to map a function into a functor space. *)
Class Functor (F : Type -> Type) := {
    fmap : forall {A B : Type} , (A -> B) -> F A -> F B;
    functor_id : forall {A : Type} (x : F A),
        fmap (fun a => a) x = x;
}.

End Functor.
