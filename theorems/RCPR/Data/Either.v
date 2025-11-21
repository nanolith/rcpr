Require Import RCPR.Data.Functor.
Require Import RCPR.Helpers.Notation.

Import Functor.
Import Notation.

Module Either.

(* The Either inductive type describes a disjunctive value. *)
Inductive Either (A B : Type) : Type :=
    | Left : A → Either A B
    | Right : B → Either A B.

(* The implicit type A maps to the Left type. *)
Arguments Left {A B} _ , [A] B _.
(* The implicit type B maps to the Right type. *)
Arguments Right {A B} _ , A [B] _.

(* The Either Functor instance provides us with an error Functor. *)
Program Instance EitherFunctor (E : Type) : Functor (Either E) := {
    fmap := λ A B f x ↦ 
        match x with
        | Left e => Left e
        | Right a => Right (f a)
        end;
}.
(* Proof of id law. *)
Next Obligation.
    intros.
    destruct x.
    reflexivity.
    reflexivity.
Qed.
(* Proof of composition law. *)
Next Obligation.
    intros.
    destruct x.
    reflexivity.
    reflexivity.
Qed.

End Either.
