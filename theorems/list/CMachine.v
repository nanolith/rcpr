Require Import RCPR.Data.IList.
Require Import RCPR.Data.Maybe.

Import IList.
Import Maybe.

(* Simulated Linked List node in C. *)
Inductive CLinkedListNode : Type :=
| Node (prev : Maybe nat) (next : Maybe nat) (val : nat).

(* Simulated Linked List in C. *)
Inductive CLinkedList : Type :=
| List (head : Maybe nat) (tail : Maybe nat) (count : nat).

(* Simulated Memory Location in C. *)
Inductive CMemoryLocation : Type :=
| CMemUninit (loc : nat)
| CMemNode (loc: nat) (node : CLinkedListNode)
| CMemList (loc: nat) (list : CLinkedList)
| CMemNodePtr (loc : nat) (ptr : nat)
| CMemListPtr (loc : nat) (ptr : nat).

(* Simulated Heap in C. *)
Inductive CHeap : Type :=
| CHeapState (index : nat) (values : IList CMemoryLocation).

(* Simulated function local memory in C. *)
Inductive CLocal : Type :=
| CLocalState (index : nat) (values : IList CMemoryLocation).

(* Possible Error Types in Machine Definition. *)
Inductive MachineErrorCode : Type :=
| MachineErrorUninit
| MachineErrorLoad
| MachineErrorStore
| MachineErrorCast
| MachineErrorTermination
| MachineErrorTruncation.
