Require Import RCPR.Data.Maybe.
Require Import RCPR.Helpers.Notation.

Import Maybe.
Import Notation.

Module IList.

(* Generic Linked List for Interpretation. *)
Inductive IList (A : Type) : Type :=
| nil : IList A
| cons : A → IList A → IList A.

(* Gather the implicit type A parameter from implicit context. *)
Arguments nil {A}.
(* The implicit type A maps to the type of the cons parameter. *)
Arguments cons {A} a _.

(* Use [] notation to indicate nil. *)
Notation "[ ]" := nil (format "[ ]").
(* Use [ x ] notation to indicate a list of one item. *)
Notation "[ x ]" := (cons x nil).
(* Use [x ; y ; .. ; z ] notation to indicate a variable length list. *)
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)).
(* Use x :: y to break down a cons cell in a list. *)
Notation "x :: y" := (cons x y).

(* Get the head of a given IList. *)
Definition head {A : Type} (lst : IList A) : Maybe A :=
    match lst with
        | [] => Nothing
        | x :: xs => Just x
    end.

(* Get the tail of a given IList. *)
Definition tail {A : Type} (lst : IList A) : IList A :=
    match lst with
        | [] => []
        | x :: xs => xs
    end.

(* Drop n elements from an IList. *)
Fixpoint drop {A : Type} (n : nat) (lst : IList A) : IList A :=
    match n with
        | 0 => lst
        | S n' => drop n' (tail lst)
    end.

(* Append two ILists. *)
Fixpoint append {A : Type} (l1 l2 : IList A) : IList A :=
    match l1 with
        | [] => l2
        | (x :: xs) => x :: append xs l2
    end.

(* Use xs ++ ys to append two lists. *)
Notation "xs ++ ys" := (append xs ys).

(* Get the length of an IList. *)
Fixpoint length {A : Type} (l : IList A) : nat :=
    match l with
        | [] => 0
        | (x :: xs) => S (length xs)
    end.

(* Reverse an IList. *)
Fixpoint reverse {A : Type} (l : IList A) : IList A :=
    match l with
    | [] => []
    | (x :: xs) => reverse xs ++ [x]
    end.

End IList.
