Require Import RCPR.Data.Applicative.
Require Import RCPR.Data.Functor.
Require Import RCPR.Helpers.Notation.

Import Applicative.
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

(* The Either Applicative instance provides us with an error Applicative. *)
Program Instance EitherApplicative (E : Type) : Applicative (Either E) := {
    pure := λ A x ↦ Right x;
    ap := λ A B f x ↦
        match f with
        | Left e => Left e
        | Right f' =>
            match x with
            | Left e => Left e
            | Right x' => Right (f' x')
            end
        end;
}.
Next Obligation.
    intros E t x.
    simpl.
    destruct x.
    reflexivity.
    reflexivity.
Qed.
Next Obligation.
    intros E X Y Z w x y.
    simpl.
    destruct w.
    reflexivity.
    simpl.
    destruct x.
    reflexivity.
    destruct y.
    reflexivity.
    reflexivity.
Qed.
Next Obligation.
    intros.
    simpl.
    reflexivity.
Qed.
Next Obligation.
    intros E A B f x.
    simpl.
    destruct f.
    reflexivity.
    reflexivity.
Qed.

End Either.
