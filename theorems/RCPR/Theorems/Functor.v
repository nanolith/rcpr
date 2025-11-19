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

End FunctorTheories.

End Functor.
