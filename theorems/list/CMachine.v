Require Import RCPR.Data.Maybe.

Import Maybe.

(* Simulated Linked List node in C. *)
Inductive CLinkedListNode : Type :=
| Node (prev : Maybe nat) (next : Maybe nat) (val : nat).
