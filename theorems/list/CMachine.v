Require Import RCPR.Data.Applicative.
Require Import RCPR.Data.Functor.
Require Import RCPR.Data.IList.
Require Import RCPR.Data.Maybe.
Require Import RCPR.Helpers.Notation.
Require Import RCPR.Tactics.FunctionalExtensionality.

Import Applicative.
Import FunctionalExtensionality.
Import Functor.
Import IList.
Import Maybe.
Import Notation.

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
