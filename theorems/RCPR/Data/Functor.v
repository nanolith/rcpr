Module Functor.

(* The Functor provides a way to map a function into a functor space. *)
Class Functor (F : Type -> Type) := {
    fmap : forall {A B : Type} , (A -> B) -> F A -> F B;
}.

End Functor.
