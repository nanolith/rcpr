Require Import RCPR.Data.Applicative.
Require Import RCPR.Data.Functor.
Require Import RCPR.Data.Monad.
Require Import RCPR.Helpers.Notation.

Import Applicative.
Import Functor.
Import Monad.
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

Arguments EitherFunctor {E}.

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
(* Proof of identity law. *)
Next Obligation.
    intros E t x.
    simpl.
    destruct x.
    reflexivity.
    reflexivity.
Qed.
(* Proof of composition law. *)
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
(* Proof of homomorphism law. *)
Next Obligation.
    intros.
    simpl.
    reflexivity.
Qed.
(* Proof of interchange law. *)
Next Obligation.
    intros E A B f x.
    simpl.
    destruct f.
    reflexivity.
    reflexivity.
Qed.

Arguments EitherApplicative {E}.

(* The Either Monad instance provides us with an error Monad. *)
Program Instance EitherMonad (E : Type) : Monad (Either E) := {
    bind := λ {A B} (m : Either E A) (f : A → Either E B) ↦
        match m with
        | Left e => Left e
        | Right a => f a
    end;
    ret := λ A x ↦ Right x;
}.
Next Obligation.
    intros.
    simpl.
    reflexivity.
Qed.
Next Obligation.
    intros E A m.
    simpl.
    destruct m.
    reflexivity.
    reflexivity.
Qed.
Next Obligation.
    intros E A B C m f g.
    simpl.
    destruct m.
    reflexivity.
    simpl.
    destruct f.
    reflexivity.
    reflexivity.
Qed.

Arguments EitherMonad {E}.

End Either.
