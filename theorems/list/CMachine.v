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
| CMemNodePtr (loc : nat) (ptr : Maybe nat)
| CMemListPtr (loc : nat) (ptr : Maybe nat)
| CMemNodePtrPtr (loc : nat) (ptr : Maybe nat)
| CMemListPtrPtr (loc : nat) (ptr : Maybe nat).

(* Is this memory location uninitialized? *)
Definition isCellUninit (cell : CMemoryLocation) : bool :=
    match cell with
    | CMemUninit _ => true
    | _ => false
    end.

(* Is this memory location a linked list node? *)
Definition isCellNode (cell : CMemoryLocation) : bool :=
    match cell with
    | CMemNode _ _ => true
    | _ => false
    end.

(* Is this memory location a linked list? *)
Definition isCellList (cell : CMemoryLocation) : bool :=
    match cell with
    | CMemList _ _ => true
    | _ => false
    end.

(* Is this memory location a linked list node pointer? *)
Definition isCellNodePtr (cell : CMemoryLocation) : bool :=
    match cell with
    | CMemNodePtr _ _ => true
    | _ => false
    end.

(* Is this memory location a linked list pointer? *)
Definition isCellListPtr (cell : CMemoryLocation) : bool :=
    match cell with
    | CMemListPtr _ _ => true
    | _ => false
    end.

(* Is this memory location a linked list node pointer pointer? *)
Definition isCellNodePtrPtr (cell : CMemoryLocation) : bool :=
    match cell with
    | CMemNodePtrPtr _ _ => true
    | _ => false
    end.

(* Is this memory location a linked list pointer pointer? *)
Definition isCellListPtrPtr (cell : CMemoryLocation) : bool :=
    match cell with
    | CMemListPtrPtr _ _ => true
    | _ => false
    end.

(* Simulated Heap in C. *)
Inductive CHeap : Type :=
| CHeapState (index : nat) (values : IList CMemoryLocation).

(* Simulated function local memory in C. *)
Inductive CLocal : Type :=
| CLocalState (index : nat) (values : IList CMemoryLocation).

(* Possible status codes returned by simulated C functions. *)
Inductive CStatusCode : Type :=
| StatusSuccess
| ErrorOutOfMemory
| ErrorOther.

(* Possible Error Types in Machine Definition. *)
Inductive MachineErrorCode : Type :=
| MachineErrorBadInstruction
| MachineErrorInvalidParameter
| MachineErrorUninit
| MachineErrorLoad
| MachineErrorStore
| MachineErrorReclaim
| MachineErrorCast
| MachineErrorDereference
| MachineErrorTermination
| MachineErrorTruncation.

(* Machine instructions. *)
Inductive CMachineInstruction : Type :=
| INS_AssignLocalListPtrToHeapListPtr
    (heapAddr : nat) (localAddr : nat) (next : CMachineInstruction)
| INS_CheckHeapListPtrAddress (heapAddr : nat) (next : CMachineInstruction)
| INS_ReturnStatus (code : CStatusCode)
| INS_Crash (e : MachineErrorCode).

(* Machine instructions. *)
Inductive CMachineInstruction' : Type :=
(* Create a local variable for holding a linked list pointer. *)
| INS_CreateLocalLinkedListPtr' (addr : nat)
(* Create a linked list on the heap, storing the result in the given local
   pointer. *)
| INS_CreateLinkedList' (localAddr : nat)
(* Check to see if a given value is present. *)
| INS_IsListPtrPresent' (localAddr : nat)
| INS_ITE' (cond : CMachineInstruction') (thenIns : IList CMachineInstruction')
          (elseIns : IList CMachineInstruction')
| INS_AssignLocalListPtrToHeapListPtr' (heapAddr : nat) (localAddr : nat)
| INS_CheckHeapListPtrAddress' (hapAddr : nat)
| INS_ReturnStatus' (code : CStatusCode)
| INS_Crash' (e : MachineErrorCode).

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
    | CMemNodePtrPtr loc _ => loc
    | CMemListPtrPtr loc _ => loc
    end.

(* Set the address of a location in memory. *)
Definition locSet (addr : nat) (cell : CMemoryLocation) : CMemoryLocation :=
    match cell with
    | CMemUninit _ => CMemUninit addr
    | CMemNode _ n => CMemNode addr n
    | CMemList _ l => CMemList addr l
    | CMemNodePtr _ ptr => CMemNodePtr addr ptr
    | CMemListPtr _ ptr => CMemListPtr addr ptr
    | CMemNodePtrPtr _ ptr => CMemNodePtr addr ptr
    | CMemListPtrPtr _ ptr => CMemListPtr addr ptr
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

(* Get the local store from the machine. *)
Definition getLocal : MachineM CLocal :=
    λ n l h ↦ MachineState n l h l.

(* Replace the local store with the new local store. *)
Definition putLocal (newLocal : CLocal) : MachineM unit :=
    λ n l h ↦ MachineState n newLocal h tt.

(* Throw an exception. *)
Definition throw {A} (e : MachineErrorCode) : MachineM A :=
    λ _ _ _ ↦ MachineError e.

(* Filter an operation based on a Boolean operation. *)
(* Throw the given error if this filter fails. *)
Definition mfilter (err : MachineErrorCode) (op : bool) : MachineM unit :=
    if op then
        ret tt
    else
        throw err.

(* Attempt to coerce a Maybe value to a value, throwing an error if it fails. *)
Definition fromJust {A : Type} (mval : Maybe A) : MachineM A :=
    match mval with
    | Just val => ret val
    | Nothing => throw MachineErrorDereference
    end.

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

(* Get memory from the local store. *)
Definition getLocalMemory : MachineM (IList CMemoryLocation) :=
    getLocal ▶
        λ h ↦
            match h with
            | CLocalState _ vals => ret vals
            end.

(* Put memory to the local store. *)
Definition putLocalMemory (values : IList CMemoryLocation) : MachineM unit :=
    getLocal ▶
        λ h ↦
            match h with
            | CLocalState idx _ => putLocal (CLocalState idx values)
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

(* Perform a typed load of a linked list node pointer. *)
Definition loadLinkedListNodePtr (addr : nat) : MachineM (Maybe nat) :=
    loadRaw addr ▶
        λ cell ↦
            match cell with
            | CMemNodePtr _ node => ret node
            | _ => throw MachineErrorCast
            end.

(* Perform a typed load of a linked list pointer. *)
Definition loadLinkedListPtr (addr : nat) : MachineM (Maybe nat) :=
    loadRaw addr ▶
        λ cell ↦
            match cell with
            | CMemListPtr _ node => ret node
            | _ => throw MachineErrorCast
            end.

(* Perform a typed load of a linked list node pointer pointer. *)
Definition loadLinkedListNodePtrPtr (addr : nat) : MachineM (Maybe nat) :=
    loadRaw addr ▶
        λ cell ↦
            match cell with
            | CMemNodePtrPtr _ node => ret node
            | _ => throw MachineErrorCast
            end.

(* Perform a typed load of a linked list pointer pointer. *)
Definition loadLinkedListPtrPtr (addr : nat) : MachineM (Maybe nat) :=
    loadRaw addr ▶
        λ cell ↦
            match cell with
            | CMemListPtrPtr _ node => ret node
            | _ => throw MachineErrorCast
            end.

(* Perform a raw (untyped) load of a local location. *)
Definition loadLocalRaw (addr : nat) : MachineM CMemoryLocation :=
    getLocalMemory ▶
        λ values ↦
            match lookupMem addr values with
            | Just cell => ret cell
            | Nothing => throw MachineErrorLoad
            end.

(* Perform a typed local load of a linked list node pointer. *)
Definition loadLocalLinkedListNodePtr (addr : nat) : MachineM (Maybe nat) :=
    loadLocalRaw addr ▶
        λ cell ↦
            match cell with
            | CMemNodePtr _ node => ret node
            | _ => throw MachineErrorCast
            end.

(* Perform a typed local load of a linked list pointer. *)
Definition loadLocalLinkedListPtr (addr : nat) : MachineM (Maybe nat) :=
    loadLocalRaw addr ▶
        λ cell ↦
            match cell with
            | CMemListPtr _ node => ret node
            | _ => throw MachineErrorCast
            end.

(* Perform a typed local load of a linked list node pointer pointer. *)
Definition loadLocalLinkedListNodePtrPtr (addr : nat) : MachineM (Maybe nat) :=
    loadLocalRaw addr ▶
        λ cell ↦
            match cell with
            | CMemNodePtrPtr _ node => ret node
            | _ => throw MachineErrorCast
            end.

(* Perform a typed local load of a linked list pointer pointer. *)
Definition loadLocalLinkedListPtrPtr (addr : nat) : MachineM (Maybe nat) :=
    loadLocalRaw addr ▶
        λ cell ↦
            match cell with
            | CMemListPtrPtr _ node => ret node
            | _ => throw MachineErrorCast
            end.

(* Replace a value in the given memory list, creating a new list. *)
Fixpoint memReplaceLoop (addr : nat) (newCell : CMemoryLocation)
        (mem : IList CMemoryLocation) (acc : IList CMemoryLocation)
        : MachineM (IList CMemoryLocation) :=
    match mem with
    | [] => throw MachineErrorStore
    | m :: ms =>
        if Nat.eqb (locAddr m) addr then
            ret ((reverse acc) ++ (newCell :: ms))
        else memReplaceLoop addr newCell ms (m :: acc)
    end.

(* Replace a value in the given memory list. *)
Definition memReplace (addr : nat) (newCell : CMemoryLocation)
        (mem : IList CMemoryLocation) : MachineM (IList CMemoryLocation) :=
    memReplaceLoop addr newCell mem [].

(* Store a linked list node, overwriting an existing node. *)
Definition storeLinkedListNode (addr : nat) (node : CLinkedListNode) :
        MachineM unit :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedListNode addr »
                memReplace addr (CMemNode addr node) values ▶
                    λ values' ↦
                        putHeapMemory values'.

(* Store a linked list, overwriting an existing list. *)
Definition storeLinkedList (addr : nat) (list : CLinkedList) :
        MachineM unit :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedList addr »
                memReplace addr (CMemList addr list) values ▶
                    λ values' ↦
                        putHeapMemory values'.

(* Store a linked list node pointer, overwriting an existing pointer. *)
Definition storeLinkedListNodePtr (addr : nat) (ptr : Maybe nat) :
        MachineM unit :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedListNodePtr addr »
                memReplace addr (CMemNodePtr addr ptr) values ▶
                    λ values' ↦
                        putHeapMemory values'.

(* Store a linked list pointer, overwriting an existing pointer. *)
Definition storeLinkedListPtr (addr : nat) (ptr : Maybe nat) :
        MachineM unit :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedListPtr addr »
                memReplace addr (CMemListPtr addr ptr) values ▶
                    λ values' ↦
                        putHeapMemory values'.

(* Store a linked list node pointer pointer, overwriting an existing pointer. *)
Definition storeLinkedListNodePtrPtr (addr : nat) (ptr : Maybe nat) :
        MachineM unit :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedListNodePtrPtr addr »
                memReplace addr (CMemNodePtrPtr addr ptr) values ▶
                    λ values' ↦
                        putHeapMemory values'.

(* Store a linked list pointer pointer, overwriting an existing pointer. *)
Definition storeLinkedListPtrPtr (addr : nat) (ptr : Maybe nat) :
        MachineM unit :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedListPtrPtr addr »
                memReplace addr (CMemListPtrPtr addr ptr) values ▶
                    λ values' ↦
                        putHeapMemory values'.

(* Store a local linked list node pointer, overwriting an existing pointer. *)
Definition storeLocalLinkedListNodePtr (addr : nat) (ptr : Maybe nat) :
        MachineM unit :=
    getLocalMemory ▶
        λ values ↦
            loadLocalLinkedListNodePtr addr »
                memReplace addr (CMemNodePtr addr ptr) values ▶
                    λ values' ↦
                        putLocalMemory values'.

(* Store a local linked list pointer, overwriting an existing pointer. *)
Definition storeLocalLinkedListPtr (addr : nat) (ptr : Maybe nat) :
        MachineM unit :=
    getLocalMemory ▶
        λ values ↦
            loadLocalLinkedListPtr addr »
                memReplace addr (CMemListPtr addr ptr) values ▶
                    λ values' ↦
                        putLocalMemory values'.

(* Store a local linked list node ptr ptr, overwriting an existing pointer. *)
Definition storeLocalLinkedListNodePtrPtr (addr : nat) (ptr : Maybe nat) :
        MachineM unit :=
    getLocalMemory ▶
        λ values ↦
            loadLocalLinkedListNodePtrPtr addr »
                memReplace addr (CMemNodePtrPtr addr ptr) values ▶
                    λ values' ↦
                        putLocalMemory values'.

(* Store a local linked list ptr ptr, overwriting an existing pointer. *)
Definition storeLocalLinkedListPtrPtr (addr : nat) (ptr : Maybe nat) :
        MachineM unit :=
    getLocalMemory ▶
        λ values ↦
            loadLocalLinkedListPtrPtr addr »
                memReplace addr (CMemListPtrPtr addr ptr) values ▶
                    λ values' ↦
                        putLocalMemory values'.

(* Create a value on the heap, returning the new memory location. *)
Definition heapCreate (newCell : CMemoryLocation) : MachineM nat :=
    getHeap ▶
        λ heap ↦
            match heap with
            | CHeapState idx values =>
                let allocCell := locSet (idx + 1) newCell in
                    putHeap (CHeapState (idx + 1) (values ++ [allocCell])) »
                        ret (idx + 1)
            end.

(* Create a value on the local store, returning the new memory location. *)
Definition localCreate (newCell : CMemoryLocation) : MachineM nat :=
    getLocal ▶
        λ local ↦
            match local with
            | CLocalState idx values =>
                let allocCell := locSet (idx + 1) newCell in
                    putLocal (CLocalState (idx + 1) (values ++ [allocCell])) »
                        ret (idx + 1)
            end.

(* Create a linked list node. *)
Definition createLinkedListNode (node : CLinkedListNode) : MachineM nat :=
    heapCreate (CMemNode 0 node).

(* Create an empty linked list. *)
Definition createLinkedList : MachineM nat :=
    heapCreate (CMemList 0 (List Nothing Nothing 0)).

(* Create a linked list node pointer. *)
Definition createLinkedListNodePtr (ptr : Maybe nat) : MachineM nat :=
    heapCreate (CMemNodePtr 0 ptr).

(* Create a linked list pointer. *)
Definition createLinkedListPtr (ptr : Maybe nat) : MachineM nat :=
    heapCreate (CMemListPtr 0 ptr).

(* Create a local linked list node pointer. *)
Definition createLocalLinkedListNodePtr (ptr : Maybe nat) : MachineM nat :=
    localCreate (CMemNodePtr 0 ptr).

(* Create a local linked list pointer. *)
Definition createLocalLinkedListPtr (ptr : Maybe nat) : MachineM nat :=
    localCreate (CMemListPtr 0 ptr).

(* Remove a value in the given memory list, creating a new list. *)
Fixpoint memRemoveLoop (addr : nat) (mem : IList CMemoryLocation)
        (acc : IList CMemoryLocation) : MachineM (IList CMemoryLocation) :=
    match mem with
    | [] => throw MachineErrorReclaim
    | m :: ms =>
        if Nat.eqb (locAddr m) addr then
            ret ((reverse acc) ++ ms)
        else memRemoveLoop addr ms (m :: acc)
    end.

(* Remove a value from the given memory list. *)
Definition memRemove (addr : nat) (mem : IList CMemoryLocation)
        : MachineM (IList CMemoryLocation) :=
    memRemoveLoop addr mem [].

(* Reclaim a linked list node. *)
Definition reclaimLinkedListNode (addr : nat) : MachineM unit :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedListNode addr »
                memRemove addr values ▶
                    λ values' ↦
                        putHeapMemory values'.

(* Reclaim a linked list. *)
Definition reclaimLinkedList (addr : nat) : MachineM unit :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedList addr »
                memRemove addr values ▶
                    λ values' ↦
                        putHeapMemory values'.

(* Reclaim a linked list node ptr. *)
Definition reclaimLinkedListNodePtr (addr : nat) : MachineM unit :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedListNodePtr addr »
                memRemove addr values ▶
                    λ values' ↦
                        putHeapMemory values'.

(* Reclaim a linked list ptr. *)
Definition reclaimLinkedListPtr (addr : nat) : MachineM unit :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedListPtr addr »
                memRemove addr values ▶
                    λ values' ↦
                        putHeapMemory values'.

(* Extract a linked list into an IList of nat values. *)
Fixpoint extractList (count : nat) (midx : Maybe nat)
        (values : IList CMemoryLocation) (acc : IList nat)
        : MachineM (IList nat) :=
    match count with
    | 0 =>
        match midx with
        | Nothing => ret (reverse acc)
        | Just _ => throw MachineErrorTermination
        end
    | S n =>
        match midx with
        | Nothing => throw MachineErrorTruncation
        | Just idx =>
            loadLinkedListNode idx ▶
                λ node ↦
                    match node with
                    | Node _ next val =>
                        extractList n next values (val :: acc)
                    end
        end
    end.

(* Extract a linked list into a reverse IList of nat values. *)
Fixpoint extractReverseList (count : nat) (midx : Maybe nat)
        (values : IList CMemoryLocation) (acc : IList nat)
        : MachineM (IList nat) :=
    match count with
    | 0 =>
        match midx with
        | Nothing => ret (reverse acc)
        | Just _ => throw MachineErrorTermination
        end
    | S n =>
        match midx with
        | Nothing => throw MachineErrorTruncation
        | Just idx =>
            loadLinkedListNode idx ▶
                λ node ↦
                    match node with
                    | Node prev _ val =>
                        extractReverseList n prev values (val :: acc)
                    end
        end
    end.

(* Extract the linked list from C. *)
Definition extractListFromC (ptr : nat) : MachineM (IList nat) :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedList ptr ▶
                λ l ↦
                    match l with
                    | List h _ count =>
                        extractList count h values []
                    end.

(* Extract the reverse linked list from C. *)
Definition extractReverseListFromC (ptr : nat) : MachineM (IList nat) :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedList ptr ▶
                λ l ↦
                    match l with
                    | List _ t count =>
                        extractReverseList count t values []
                    end.

(* Simulated form of createLinkedList that could fail. *)
Definition maybeCreateLinkedList : MachineM (Maybe nat) :=
    heapCreate (CMemList 0 (List Nothing Nothing 0)) ▶
        λ listPtr ↦
            ret (Just listPtr).

(* Simulated C implementation of list_create and slist_create. *)
Definition cListCreate (listPtr : nat) : MachineM CStatusCode :=
    createLocalLinkedListPtr Nothing ▶
    λ tmp ↦
    loadLinkedListPtr listPtr »
    maybeCreateLinkedList ▶
    λ mptr ↦
    match mptr with
    | Just ptr =>
        storeLocalLinkedListPtr tmp (Just ptr) »
        loadLocalLinkedListPtr tmp ▶
        storeLinkedListPtr listPtr »
        ret StatusSuccess
    | Nothing => ret ErrorOutOfMemory
    end.

(* Stub function for reading a LinkedListPtr parameter. *)
(* By default, this instruction throws an exception. *)
(* It is overridden in equivalence proofs to provide parameters. *)
Definition getLinkedListPtrParameter (offset : nat) : MachineM nat :=
    throw MachineErrorInvalidParameter.

(* Evaluate a create local linked list ptr instruction. *)
Definition evalCreateLocalLinkedListPtr (addr : nat) : MachineM unit :=
    createLocalLinkedListPtr Nothing ▶
    λ localAddr ↦
    if Nat.eqb localAddr addr then
        ret tt
    else
        throw MachineErrorBadInstruction.

(* Evaluate a create linked list instruction. *)
Definition evalCreateLinkedList (localAddr : nat) : MachineM unit :=
    maybeCreateLinkedList ▶
    storeLocalLinkedListPtr localAddr.

(* Evaluate an is list pointer present assertion instruction. *)
Definition evalIsListPtrPresent (localAddr : nat) : MachineM bool :=
    loadLocalLinkedListPtr localAddr ▶
    λ mptr ↦
    match mptr with
    | Just ptr => ret true
    | Nothing => ret false
    end.

(* Evaluate an assignment instruction for a linked list pointer. *)
Definition evalAssignLocalListPtrToHeapListPtr (heapAddr localAddr : nat)
        : MachineM unit :=
    loadLocalLinkedListPtr localAddr ▶
    storeLinkedListPtr heapAddr.

(* Evaluate a null check instruction. *)
Definition evalCheckHeapListPtrAddress (heapAddr : nat) : MachineM unit :=
    loadLinkedListPtr heapAddr »
        ret tt.

(* Evaluate a return instruction. *)
Definition evalReturnStatus (code : CStatusCode) : MachineM CStatusCode :=
    ret code.

(* Evaluate an ITE conditional instruction. *)
Definition evalCond (ins : CMachineInstruction') : MachineM bool :=
    match ins with
    | INS_IsListPtrPresent' localAddr =>
        evalIsListPtrPresent localAddr
    | _ => throw MachineErrorBadInstruction
    end.

(* Evaluate instructions in the then or else branch of an ITE. *)
Fixpoint evalITEInstructions (ins : IList CMachineInstruction')
        : MachineM CStatusCode :=
    match ins with
    | [] => throw MachineErrorTermination
    | (INS_ReturnStatus' code) :: nil => evalReturnStatus code
    | x :: xs =>
        match x with
        | INS_CreateLocalLinkedListPtr' addr =>
            evalCreateLocalLinkedListPtr addr »
            evalITEInstructions xs
        | INS_CreateLinkedList' localAddr =>
            evalCreateLinkedList localAddr »
            evalITEInstructions xs
        | INS_IsListPtrPresent' _ => throw MachineErrorTermination
        | INS_AssignLocalListPtrToHeapListPtr' heapAddr localAddr =>
            evalAssignLocalListPtrToHeapListPtr heapAddr localAddr »
            evalITEInstructions xs
        | INS_CheckHeapListPtrAddress' heapAddr =>
            evalCheckHeapListPtrAddress heapAddr »
            evalITEInstructions xs
        | INS_ReturnStatus' _ => throw MachineErrorBadInstruction
        | INS_Crash' e => throw e
        | _ => throw MachineErrorBadInstruction
        end
    end.

(* Evaluate function instructions. *)
Fixpoint evalInstructions (ins : IList CMachineInstruction')
        : MachineM CStatusCode :=
    match ins with
    | [] => throw MachineErrorTermination
    | (INS_ReturnStatus' code) :: nil => evalReturnStatus code
    | x :: xs =>
        match x with
        | INS_CreateLocalLinkedListPtr' addr =>
            evalCreateLocalLinkedListPtr addr »
            evalInstructions xs
        | INS_CreateLinkedList' localAddr =>
            evalCreateLinkedList localAddr »
            evalInstructions xs
        | INS_IsListPtrPresent' _ => throw MachineErrorTermination
        | INS_ITE' cond thenIns elseIns =>
            evalCond cond ▶
            λ boolExpr ↦
            if boolExpr then
                evalITEInstructions thenIns
            else
                evalITEInstructions elseIns
        | INS_AssignLocalListPtrToHeapListPtr' heapAddr localAddr =>
            evalAssignLocalListPtrToHeapListPtr heapAddr localAddr »
            evalInstructions xs
        | INS_CheckHeapListPtrAddress' heapAddr =>
            evalCheckHeapListPtrAddress heapAddr »
            evalInstructions xs
        | INS_ReturnStatus' _ => throw MachineErrorBadInstruction
        | INS_Crash' e => throw e
        end
    end.

End CMachine.
