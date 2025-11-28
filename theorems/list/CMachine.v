Require Import RCPR.Data.Applicative.
Require Import RCPR.Data.Functor.
Require Import RCPR.Data.IList.
Require Import RCPR.Data.Maybe.
Require Import RCPR.Data.Monad.
Require Import RCPR.Helpers.Notation.
Require Import RCPR.Tactics.FunctionalExtensionality.

Import Applicative.
Import FunctionalExtensionality.
Import Functor.
Import IList.
Import Maybe.
Import Monad.
Import Notation.

Module CMachine.

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

(* Machine State. *)
Inductive Machine (A : Type) :=
| MachineError : MachineErrorCode → Machine A
| MachineState : nat → CLocal → CHeap → A → Machine A.

Arguments MachineError {A}.
Arguments MachineState {A}.

Program Instance MachineFunctor : Functor Machine := {
    fmap := λ A B f m ↦
        match m with
        | MachineError e => MachineError e
        | MachineState n l h v => MachineState n l h (f v)
        end;
}.
(* Proof of identity law. *)
Next Obligation.
    intros A x.
    simpl.
    destruct x.
    reflexivity.
    reflexivity.
Qed.
(* Proof of composition law. *)
Next Obligation.
    intros A B C f g x.
    simpl.
    destruct x.
    reflexivity.
    reflexivity.
Qed.

(* Transition Machine states. *)
Definition MachineM (A : Type) :=
    nat → CLocal → CHeap → Machine A.

Program Instance MachineMFunctor : Functor MachineM := {
    fmap := λ {A} {B} (f : A → B) (m : MachineM A) ↦
        λ n l h ↦
            let result := m n l h in
            match result with
            | MachineError e => MachineError e
            | MachineState n' l' h' v => MachineState n' l' h' (f v)
            end
}.
(* Proof of identity law. *)
Next Obligation.
    intros A m.
    apply functional_extensionality.  intro n.
    apply functional_extensionality.  intro l.
    apply functional_extensionality.  intro h.
    destruct (m n l h).
    simpl.
    reflexivity.
    simpl.
    reflexivity.
Qed.
(* Proof of composition law. *)
Next Obligation.
    intros A B C f g m.
    apply functional_extensionality.  intro n.
    apply functional_extensionality.  intro l.
    apply functional_extensionality.  intro h.
    destruct (m n l h).
    simpl.
    reflexivity.
    simpl.
    reflexivity.
Qed.

Program Instance MachineMApplicative : Applicative MachineM := {
    pure := λ {T} (x : T) ↦
        λ (n : nat) (l : CLocal) (h : CHeap) ↦
            MachineState n l h x;
    ap := λ {A} {B} (mf : MachineM (A → B)) (mx : MachineM A) ↦
        λ (n : nat) (l : CLocal) (h : CHeap) ↦
            match mf n l h with
            | MachineError e => MachineError e
            | MachineState n' l' h' f =>
                match mx n' l' h' with
                | MachineError e => MachineError e
                | MachineState n'' l'' h'' x =>
                    MachineState n'' l'' h'' (f x)
                end
            end;
}.
(* Proof of identity law. *)
Next Obligation.
    intros t v.
    apply functional_extensionality.  intro n.
    apply functional_extensionality.  intro l.
    apply functional_extensionality.  intro h.
    simpl.
    destruct (v n l h).
    reflexivity.
    reflexivity.
Qed.
(* Proof of composition law. *)
Next Obligation.
    intros X Y Z u v w.
    apply functional_extensionality.  intro n.
    apply functional_extensionality.  intro l.
    apply functional_extensionality.  intro h.
    simpl.
    destruct (u n l h).
    reflexivity.
    simpl.
    destruct (v n0 c c0).
    reflexivity.
    destruct (w n1 c1 c2).
    reflexivity.
    reflexivity.
Qed.
(* Proof of homomorphism law. *)
Next Obligation.
    intros X Y f x.
    apply functional_extensionality.  intro n.
    apply functional_extensionality.  intro l.
    apply functional_extensionality.  intro h.
    simpl.
    reflexivity.
Qed.
(* Proof of interchange law. *)
Next Obligation.
    intros X Y u y.
    apply functional_extensionality.  intro n.
    apply functional_extensionality.  intro l.
    apply functional_extensionality.  intro h.
    simpl.
    reflexivity.
Qed.

Program Instance MachineMMonad : Monad MachineM := {
    ret := λ {T} (x : T) ↦
        λ (n : nat) (l : CLocal) (h : CHeap) ↦
            MachineState n l h x;
    bind := λ {A} {B} (m : MachineM A) (f : A → MachineM B) ↦
        λ (n : nat) (l : CLocal) (h : CHeap) ↦
            match m n l h with
            | MachineError e => MachineError e
            | MachineState n' l' h' v =>
                (f v) n' l' h'
            end
}.
(* Left Identity. *)
Next Obligation.
    intros A B x f.
    apply functional_extensionality.  intro n.
    apply functional_extensionality.  intro l.
    apply functional_extensionality.  intro h.
    simpl.
    reflexivity.
Qed.
(* Right Identity. *)
Next Obligation.
    intros A m.
    apply functional_extensionality.  intro n.
    apply functional_extensionality.  intro l.
    apply functional_extensionality.  intro h.
    simpl.
    destruct (m n l h).
    reflexivity.
    reflexivity.
Qed.
(* Associativity. *)
Next Obligation.
    intros A B C m f g.
    apply functional_extensionality.  intro n.
    apply functional_extensionality.  intro l.
    apply functional_extensionality.  intro h.
    simpl.
    destruct (m n l h).
    reflexivity.
    destruct (f a n0 c c0).
    reflexivity.
    reflexivity.
Qed.

(* Get the address of a location on the heap. *)
Definition locAddr (cell : CMemoryLocation) : nat :=
    match cell with
    | CMemUninit loc => loc
    | CMemNode loc _ => loc
    | CMemList loc _ => loc
    | CMemNodePtr loc _ => loc
    | CMemListPtr loc _ => loc
    end.

(* Look up an address from memory. *)
Fixpoint lookupMem (addr : nat) (mem : IList CMemoryLocation) :
        Maybe CMemoryLocation :=
    match mem with
    | [] => Nothing
    | c :: cs =>
        if Nat.eqb (locAddr c) addr
            then Just c
            else lookupMem addr cs
    end.

(* Get the heap from the machine. *)
Definition getHeap : MachineM CHeap :=
    λ n l h ↦ MachineState n l h h.

(* Replace the heap with the new heap. *)
Definition putHeap (newHeap : CHeap) : MachineM unit :=
    λ n l h ↦ MachineState n l newHeap tt.

(* Throw an exception. *)
Definition throw {A} (e : MachineErrorCode) : MachineM A :=
    λ _ _ _ ↦ MachineError e.

Open Scope monad_scope.

(* Get memory from the heap. *)
Definition getHeapMemory : MachineM (IList CMemoryLocation) :=
    getHeap ▶
        λ h ↦
            match h with
            | CHeapState _ vals => ret vals
            end.

(* Put memory to the heap. *)
Definition putHeapMemory (values : IList CMemoryLocation) : MachineM unit :=
    getHeap ▶
        λ h ↦
            match h with
            | CHeapState idx _ => putHeap (CHeapState idx values)
            end.

(* Perform a raw (untyped) load of a location. *)
Definition loadRaw (addr : nat) : MachineM CMemoryLocation :=
    getHeapMemory ▶
        λ values ↦
            match lookupMem addr values with
            | Just cell => ret cell
            | Nothing => throw MachineErrorLoad
            end.

(* Perform a typed load of a linked list node. *)
Definition loadLinkedListNode (addr : nat) : MachineM CLinkedListNode :=
    loadRaw addr ▶
        λ cell ↦
            match cell with
            | CMemNode _ node => ret node
            | _ => throw MachineErrorCast
            end.

(* Perform a typed load of a linked list. *)
Definition loadLinkedList (addr : nat) : MachineM CLinkedList :=
    loadRaw addr ▶
        λ cell ↦
            match cell with
            | CMemList _ list => ret list
            | _ => throw MachineErrorCast
            end.

End CMachine.
