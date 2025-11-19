Require Import RCPR.Data.Functor.

Import Functor.

Module Functor.

Section FunctorTheories.
    Variable F : Type -> Type.
    Context `{Functor F}.

    Open Scope functor_scope.

    (* verify functor identity. *)
    Lemma identity : forall {A : Type} (x : F A),
        (fun a => a) ⟨$⟩ x = x.
    Proof.
        intros.
        apply functor_id.
    Qed.

    (* verify functor composition. *)
    Lemma composition : forall {A B C : Type} (f : A -> B) (g : B -> C)
                               (x : F A),
        (fun y => g (f y)) ⟨$⟩ x = g ⟨$⟩ (f ⟨$⟩ x).
    Proof.
        intros.
        apply functor_comp.
    Qed.

End FunctorTheories.

End Functor.
