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
| Node (prev next : Maybe nat) (val : nat).

(* Simulated Linked List in C. *)
Inductive CLinkedList : Type :=
| List (head tail : Maybe nat) (count : nat).

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
| MachineErrorIntegerUnderflow
| MachineErrorTruncation.

(* Machine instructions. *)
Inductive CMachineInstruction : Type :=
| INS_CreateLocalLinkedListPtr (addr : nat) (next : CMachineInstruction)
| INS_CreateLocalLinkedListPtrPtr (addr : nat) (next : CMachineInstruction)
| INS_CreateLinkedList (localAddr : nat) (next : CMachineInstruction)
| INS_IsListPtrPresent (localAddr : nat)
| INS_ITE
    (cond : CMachineInstruction) (thenHead : CMachineInstruction)
    (elseHead : CMachineInstruction)
| INS_AssignLocalListPtrToHeapListPtr
    (heapAddr : nat) (localAddr : nat) (next : CMachineInstruction)
| INS_AssignLocalListPtrPtrToListPtrParameter
    (offset : nat) (localAddr : nat) (next : CMachineInstruction)
| INS_AssignLocalListHeapPtrToLocalListPtr
    (localHeapAddr localAddr : nat) (next : CMachineInstruction)
| INS_IncrementListCount (localAddr : nat) (next : CMachineInstruction)
| INS_DecrementListCount (localAddr : nat) (next : CMachineInstruction)
| INS_SetLinkedListHead (localAddr : nat) (headAddr : Maybe nat)
    (next : CMachineInstruction)
| INS_SetLinkedListTail (localAddr : nat) (tailAddr : Maybe nat)
    (next : CMachineInstruction)
| INS_SetListNodeNext (localAddr : nat) (nextAddr : Maybe nat)
    (next : CMachineInstruction)
| INS_CheckHeapListPtrAddress (heapAddr : nat) (next : CMachineInstruction)
| INS_ReturnStatus (code : CStatusCode)
| INS_Crash (e : MachineErrorCode).

Declare Custom Entry c_lang.

Notation "'[[' P ']]'" := (P) (at level 0, P custom c_lang).

Notation "'@isListPtrPreset' '(' addr ')'" :=
    (INS_IsListPtrPresent addr)
    (in custom c_lang at level 0, addr constr).

Notation "'@if' '(' cond ')' '{' t '}' '@else' '{' e '}'" :=
    (INS_ITE cond t e)
    (in custom c_lang at level 2,
     cond custom c_lang, t custom c_lang, e custom c_lang).

Notation "'@return' status ';'" :=
    (INS_ReturnStatus status)
    (in custom c_lang at level 1, status constr).

Notation "'@throw' err ';'" :=
    (INS_Crash err)
    (in custom c_lang at level 1, err constr).

Notation "'@createLocalLinkedListPtr' '(' addr ')' ';' next" :=
    (INS_CreateLocalLinkedListPtr addr next)
    (in custom c_lang at level 3, addr constr, next custom c_lang at level 200).

Notation "'@createLocalLinkedListPtrPtr' '(' addr ')' ';' next" :=
    (INS_CreateLocalLinkedListPtrPtr addr next)
    (in custom c_lang at level 3, addr constr, next custom c_lang at level 200).

Notation "'@createLinkedList' '(' localAddr ')' ';' next" :=
    (INS_CreateLinkedList localAddr next)
    (in custom c_lang at level 3, localAddr constr,
     next custom c_lang at level 200).

Notation "'@assignLocalListPtrToHeapListPtr' '(' heapAddr ',' localAddr ')' ';' next" :=
    (INS_AssignLocalListPtrToHeapListPtr heapAddr localAddr next)
    (in custom c_lang at level 3, heapAddr constr, localAddr constr,
     next custom c_lang at level 200).

Notation "'@assignLocalListPtrPtrToListPtrParameter' '(' offset ',' localAddr ')' ';' next" :=
    (INS_AssignLocalListPtrPtrToListPtrParameter offset localAddr next)
    (in custom c_lang at level 3, offset constr, localAddr constr,
     next custom c_lang at level 200).

Notation "'@assignLocalListHeapPtrToLocalListPtr' '(' localHeapAddr ',' localAddr ')' ';' next" :=
    (INS_AssignLocalListHeapPtrToLocalListPtr localHeapAddr localAddr next)
    (in custom c_lang at level 3, localHeapAddr constr, localAddr constr,
     next custom c_lang at level 200).

Notation "'@checkHeapListPtrAddress' '(' heapAddr ')' ';' next" :=
    (INS_CheckHeapListPtrAddress heapAddr next)
    (in custom c_lang at level 3, heapAddr constr,
     next custom c_lang at level 200).

Notation "'@incrementCount' '(' localAddr ')' ';' next" :=
    (INS_IncrementListCount localAddr next)
    (in custom c_lang at level 3, localAddr constr,
     next custom c_lang at level 200).

Notation "'@decrementCount' '(' localAddr ')' ';' next" :=
    (INS_DecrementListCount localAddr next)
    (in custom c_lang at level 3, localAddr constr,
     next custom c_lang at level 200).

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
    | CMemNodePtrPtr _ ptr => CMemNodePtrPtr addr ptr
    | CMemListPtrPtr _ ptr => CMemListPtrPtr addr ptr
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
        λ '(CHeapState _ vals) ↦ ret vals.

(* Put memory to the heap. *)
Definition putHeapMemory (values : IList CMemoryLocation) : MachineM unit :=
    getHeap ▶
        λ '(CHeapState idx _) ↦
            putHeap (CHeapState idx values).

(* Get memory from the local store. *)
Definition getLocalMemory : MachineM (IList CMemoryLocation) :=
    getLocal ▶
        λ '(CLocalState _ vals) ↦ ret vals.

(* Put memory to the local store. *)
Definition putLocalMemory (values : IList CMemoryLocation) : MachineM unit :=
    getLocal ▶
        λ '(CLocalState idx _) ↦
            putLocal (CLocalState idx values).

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
        λ '(CHeapState idx values) ↦
            let allocCell := locSet (idx + 1) newCell in
                putHeap (CHeapState (idx + 1) (values ++ [allocCell])) »
                    ret (idx + 1).

(* Create a value on the local store, returning the new memory location. *)
Definition localCreate (newCell : CMemoryLocation) : MachineM nat :=
    getLocal ▶
        λ '(CLocalState idx values) ↦
            let allocCell := locSet (idx + 1) newCell in
                putLocal (CLocalState (idx + 1) (values ++ [allocCell])) »
                    ret (idx + 1).

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

(* Create a local linked list pointer pointer. *)
Definition createLocalLinkedListPtrPtr (ptr : Maybe nat) : MachineM nat :=
    localCreate (CMemListPtrPtr 0 ptr).

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

(* Increment node count for a linked list. *)
Definition incrementLinkedListCount (addr : nat) : MachineM unit :=
    loadLinkedList addr ▶
        λ '(List head tail count) ↦
            storeLinkedList addr (List head tail (count + 1)).

(* Decrement node count for a linked list. *)
Definition decrementLinkedListCount (addr : nat) : MachineM unit :=
    loadLinkedList addr ▶
        λ '(List head tail count) ↦
            match count with
            | 0 => throw MachineErrorIntegerUnderflow
            | S n =>
                storeLinkedList addr (List head tail n)
            end.

(* Set the head pointer for a linked list to the given address. *)
Definition setLinkedListHead (addr : nat) (headAddr : Maybe nat)
        : MachineM unit :=
    match headAddr with
    | Nothing =>
        loadLinkedList addr ▶
            λ '(List _ tail count) ↦
                storeLinkedList addr (List Nothing tail count)
    | Just headAddr' =>
        loadLinkedListNode headAddr' »
        loadLinkedList addr ▶
            λ '(List _ tail count) ↦
                storeLinkedList addr (List headAddr tail count)
    end.

(* Set the tail pointer for a linked list to the given address. *)
Definition setLinkedListTail (addr : nat) (tailAddr : Maybe nat)
        : MachineM unit :=
    match tailAddr with
    | Nothing =>
        loadLinkedList addr ▶
            λ '(List head _ count) ↦
                storeLinkedList addr (List head Nothing count)
    | Just tailAddr' =>
        loadLinkedListNode tailAddr' »
        loadLinkedList addr ▶
            λ '(List head _ count) ↦
                storeLinkedList addr (List head tailAddr count)
    end.

(* Set the next pointer for a linked list node to the given address. *)
Definition setListNodeNext (addr : nat) (nextAddr : Maybe nat)
        : MachineM unit :=
    match nextAddr with
    | Nothing =>
        loadLinkedListNode addr ▶
            λ '(Node prev _ val) ↦
                storeLinkedListNode addr (Node prev Nothing val)
    | Just nextAddr' =>
        loadLinkedListNode nextAddr' »
        loadLinkedListNode addr ▶
            λ '(Node prev _ val) ↦
                storeLinkedListNode addr (Node prev nextAddr val)
    end.

(* Set the prev pointer for a linked list node to the given address. *)
Definition setListNodePrev (addr : nat) (prevAddr : Maybe nat)
        : MachineM unit :=
    match prevAddr with
    | Nothing =>
        loadLinkedListNode addr ▶
            λ '(Node _ next val) ↦
                storeLinkedListNode addr (Node Nothing next val)
    | Just prevAddr' =>
        loadLinkedListNode prevAddr' »
        loadLinkedListNode addr ▶
            λ '(Node _ next val) ↦
                storeLinkedListNode addr (Node prevAddr next val)
    end.

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
                λ '(Node _ next val) ↦
                    extractList n next values (val :: acc)
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
                λ '(Node prev _ val) ↦
                    extractReverseList n prev values (val :: acc)
        end
    end.

(* Extract the linked list from C. *)
Definition extractListFromC (ptr : nat) : MachineM (IList nat) :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedList ptr ▶
                λ '(List h _ count) ↦
                    extractList count h values [].

(* Extract the reverse linked list from C. *)
Definition extractReverseListFromC (ptr : nat) : MachineM (IList nat) :=
    getHeapMemory ▶
        λ values ↦
            loadLinkedList ptr ▶
                λ '(List _ t count) ↦
                    extractReverseList count t values [].

(* Stand-in for an operation that could succeed or fail. *)
Parameter maybeCreateLinkedList : MachineM (Maybe nat).

(* Simulated form of createLinkedList that always succeeds. *)
Definition maybeCreateLinkedList' : MachineM (Maybe nat) :=
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
Parameter getLinkedListPtrParameter : nat → MachineM (Maybe nat).

(* Evaluate an assign list pointer parameter to local list ptr ptr. *)
Definition evalAssignLocalListPtrPtrToListPtrParameter
        (offset : nat) (localAddr : nat) : MachineM unit :=
    getLinkedListPtrParameter offset ▶
    storeLocalLinkedListPtrPtr localAddr.

(* Evaluate an assign local list heap pointer to local list ptr. *)
Definition evalAssignLocalListHeapPointerToLocalListPtr
        (localHeapAddr localAddr : nat) : MachineM unit :=
    loadLocalLinkedListPtrPtr localHeapAddr ▶
    λ mptr ↦
    match mptr with
    | Just ptr =>
        loadLocalLinkedListPtr localAddr ▶
        storeLinkedListPtr ptr
    | Nothing =>
        throw MachineErrorDereference
    end.

(* Evaluate a create local linked list ptr instruction. *)
Definition evalCreateLocalLinkedListPtr (addr : nat) : MachineM unit :=
    createLocalLinkedListPtr Nothing ▶
    λ localAddr ↦
    if Nat.eqb localAddr addr then
        ret tt
    else
        throw MachineErrorBadInstruction.

(* Evaluate a create local linked list ptr ptr instruction. *)
Definition evalCreateLocalLinkedListPtrPtr (addr : nat) : MachineM unit :=
    createLocalLinkedListPtrPtr Nothing ▶
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

(* Evaluate an increment list count instruction. *)
Definition evalIncrementListCount (localAddr : nat) : MachineM unit :=
    loadLocalLinkedListPtr localAddr ▶ fromJust ▶ incrementLinkedListCount.

(* Evaluate a decrement list count instruction. *)
Definition evalDecrementListCount (localAddr : nat) : MachineM unit :=
    loadLocalLinkedListPtr localAddr ▶ fromJust ▶ decrementLinkedListCount.

(* Evaluate a set list head instruction. *)
Definition evalSetListHead (localAddr : nat) (nodePtrAddr : Maybe nat)
        : MachineM unit :=
    loadLocalLinkedListPtr localAddr ▶ fromJust ▶
    λ addr ↦ setLinkedListHead addr nodePtrAddr.

(* Evaluate a set list tail instruction. *)
Definition evalSetListTail (localAddr : nat) (nodePtrAddr : Maybe nat)
        : MachineM unit :=
    loadLocalLinkedListPtr localAddr ▶ fromJust ▶
    λ addr ↦ setLinkedListTail addr nodePtrAddr.

(* Evaluate a set node next instruction. *)
Definition evalSetNodeNext (localAddr : nat) (nodePtrAddr : Maybe nat)
        : MachineM unit :=
    loadLocalLinkedListNodePtr localAddr ▶ fromJust ▶
    λ addr ↦ setListNodeNext addr nodePtrAddr.

(* Evaluate a set node prev instruction. *)
Definition evalSetNodePrev (localAddr : nat) (nodePtrAddr : Maybe nat)
        : MachineM unit :=
    loadLocalLinkedListNodePtr localAddr ▶ fromJust ▶
    λ addr ↦ setListNodePrev addr nodePtrAddr.

(* Evaluate an ITE conditional instruction. *)
Definition evalCond (ins : CMachineInstruction) : MachineM bool :=
    match ins with
    | INS_IsListPtrPresent localAddr =>
        evalIsListPtrPresent localAddr
    | _ => throw MachineErrorBadInstruction
    end.

(* Evaluate function instructions. *)
Fixpoint eval (ins : CMachineInstruction) : MachineM CStatusCode :=
    match ins with
    | INS_CreateLocalLinkedListPtr addr next =>
        evalCreateLocalLinkedListPtr addr »
        eval next
    | INS_CreateLocalLinkedListPtrPtr addr next =>
        evalCreateLocalLinkedListPtrPtr addr »
        eval next
    | INS_CreateLinkedList localAddr next =>
        evalCreateLinkedList localAddr »
        eval next
    (* This is a conditional instruction for an ITE. *)
    | INS_IsListPtrPresent localAddr => throw MachineErrorBadInstruction
    | INS_ITE cond thenHead elseHead =>
        evalCond cond ▶
        λ boolExpr ↦
        if boolExpr then
            eval thenHead
        else
            eval elseHead
    | INS_AssignLocalListPtrToHeapListPtr heapAddr localAddr next =>
        evalAssignLocalListPtrToHeapListPtr heapAddr localAddr »
        eval next
    | INS_AssignLocalListPtrPtrToListPtrParameter heapAddr localAddr next =>
        evalAssignLocalListPtrPtrToListPtrParameter heapAddr localAddr »
        eval next
    | INS_AssignLocalListHeapPtrToLocalListPtr localHeapAddr localAddr next =>
        evalAssignLocalListHeapPointerToLocalListPtr localHeapAddr localAddr »
        eval next
    | INS_IncrementListCount localAddr next =>
        evalIncrementListCount localAddr »
        eval next
    | INS_DecrementListCount localAddr next =>
        evalDecrementListCount localAddr »
        eval next
    | INS_SetLinkedListHead localAddr headAddr next =>
        evalSetListHead localAddr headAddr »
        eval next
    | INS_SetLinkedListTail localAddr tailAddr next =>
        evalSetListTail localAddr tailAddr »
        eval next
    | INS_SetListNodeNext localAddr nextAddr next =>
        evalSetNodeNext localAddr nextAddr »
        eval next
    | INS_CheckHeapListPtrAddress heapAddr next =>
        evalCheckHeapListPtrAddress heapAddr »
        eval next
    | INS_ReturnStatus code => ret code
    | INS_Crash e => throw e
    end.

Definition insListCreate : CMachineInstruction :=
    [[
        @createLocalLinkedListPtrPtr(1);
        @createLocalLinkedListPtr(2);
        @assignLocalListPtrPtrToListPtrParameter(1,1);
        @createLinkedList(2);
        @if (@isListPtrPreset(2)) {
            @assignLocalListHeapPtrToLocalListPtr(1,2);
            @return StatusSuccess;
        } @else {
            @return ErrorOutOfMemory;
        }
    ]].

End CMachine.
