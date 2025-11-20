Require Import RCPR.Helpers.Notation.

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

End Either.
