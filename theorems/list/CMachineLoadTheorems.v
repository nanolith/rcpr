Require Import RCPR.Data.IList.
Require Import RCPR.Data.Maybe.
Require Import RCPR.Data.Monad.
Require Import RCPR.Helpers.Notation.
Require Import RCPR.Theorems.IListTheorems.
Require Import RCPR.Theorems.NatTheorems.
Require Import list.CMachine.

Import CMachine.
Import IList.
Import IListTheorems.
Import Maybe.
Import Monad.
Import NatTheorems.
Import Notation.

Module CMachineLoadTheorems.

Open Scope monad_scope.

(* If an upstream MachineM step fails, the whole operation fails. *)
Lemma bind_failure_MachineM :
    ∀ {A B} (m : MachineM A) (f : A → MachineM B) (n : nat) (l : CLocal)
            (h : CHeap) (e : MachineErrorCode),
        m n l h = MachineError e →
        (m ▶ f) n l h = MachineError e.
Proof.
    intros A B m f n l h e H.
    unfold bind, MachineMMonad.
    rewrite H.
    reflexivity.
Qed.

(* If an upstream MachineM step fails, the whole operation fails. *)
Lemma bind_alt_failure_MachineM :
    ∀ {A B} (m : MachineM A) (f : MachineM B) (n : nat) (l : CLocal)
            (h : CHeap) (e : MachineErrorCode),
        m n l h = MachineError e →
        (m » f) n l h = MachineError e.
Proof.
    intros A B m f n l h e H.
    unfold bind, MachineMMonad.
    rewrite H.
    reflexivity.
Qed.

(* If a memory lookup fails, loadRaw throws a MachineErrorLoad exception. *)
Lemma loadRaw_MachineErrorLoad :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (values : IList CMemoryLocation)
      (addr : nat),
            getHeapMemory n l h = MachineState n l h values →
            lookupMem addr values = Nothing →
            loadRaw addr n l h = MachineError MachineErrorLoad.
Proof.
    intros n l h values addr H1 H2.
    unfold loadRaw.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

(* If a memory lookup succeeds, loadRaw returns this value. *)
Lemma loadRaw_rw :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (values : IList CMemoryLocation)
      (addr : nat) (cell : CMemoryLocation),
            getHeapMemory n l h = MachineState n l h values →
            lookupMem addr values = Just cell →
            loadRaw addr n l h = MachineState n l h cell.
Proof.
    intros n l h values addr cell H1 H2.
    unfold loadRaw.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

(* Verify that if a location fails to load, it can't be cast to a node. *)
Lemma loadLinkedListNode_MachineErrorLoad :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat),
            loadRaw addr n l h = MachineError MachineErrorLoad →
            loadLinkedListNode addr n l h = MachineError MachineErrorLoad.
Proof.
    intros n l h addr H.
    apply bind_failure_MachineM, H.
Qed.

(* If the cell isn't a LinkedListNode, then it can't be coerced. *)
Lemma loadLinkedListNode_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (cell : CMemoryLocation),
        isCellNode cell = false →
        loadRaw addr n l h = MachineState n l h cell →
        loadLinkedListNode addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr cell H1 H2.
    unfold loadLinkedListNode.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H2.
    unfold throw.
    destruct cell.
    reflexivity.
    unfold isCellNode in H1.  inversion H1.
    reflexivity.  reflexivity.  reflexivity. reflexivity. reflexivity.
Qed.

(* Happy path: we can load linked list nodes. *)
Lemma loadLinkedListNode_rw :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : CLinkedListNode),
            loadRaw addr n l h = MachineState n l h (CMemNode addr x) →
            loadLinkedListNode addr n l h = MachineState n l h x.
Proof.
    intros n l h addr x H.
    unfold loadLinkedListNode.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Verify that if a location fails to load, it can't be cast to a list. *)
Lemma loadLinkedList_MachineErrorLoad :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat),
            loadRaw addr n l h = MachineError MachineErrorLoad →
            loadLinkedList addr n l h = MachineError MachineErrorLoad.
Proof.
    intros n l h addr H.
    apply bind_failure_MachineM, H.
Qed.

(* If the cell isn't a LinkedList, then it can't be coerced. *)
Lemma loadLinkedList_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (cell : CMemoryLocation),
        isCellList cell = false →
        loadRaw addr n l h = MachineState n l h cell →
        loadLinkedList addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr cell H1 H2.
    unfold loadLinkedList.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H2.
    unfold throw.
    destruct cell.
    reflexivity.  reflexivity.
    unfold isCellList in H1.  inversion H1.
    reflexivity.  reflexivity. reflexivity. reflexivity.
Qed.

(* Happy path: we can load linked lists. *)
Lemma loadLinkedList_rw :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : CLinkedList),
            loadRaw addr n l h = MachineState n l h (CMemList addr x) →
            loadLinkedList addr n l h = MachineState n l h x.
Proof.
    intros n l h addr x H.
    unfold loadLinkedList.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Verify that if a location fails to load, it can't be cast to a node ptr. *)
Lemma loadLinkedListNodePtr_MachineErrorLoad :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat),
            loadRaw addr n l h = MachineError MachineErrorLoad →
            loadLinkedListNodePtr addr n l h = MachineError MachineErrorLoad.
Proof.
    intros n l h addr H.
    apply bind_failure_MachineM, H.
Qed.

(* If the cell isn't a LinkedListNodePtr, then it can't be coerced. *)
Lemma loadLinkedListNodePtr_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (cell : CMemoryLocation),
        isCellNodePtr cell = false →
        loadRaw addr n l h = MachineState n l h cell →
        loadLinkedListNodePtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr cell H1 H2.
    unfold loadLinkedListNodePtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H2.
    unfold throw.
    destruct cell.
    reflexivity.  reflexivity. reflexivity.
    unfold isCellNodePtr in H1.  inversion H1.
    reflexivity. reflexivity. reflexivity.
Qed.

(* Happy path: we can load linked list node pointers. *)
Lemma loadLinkedListNodePtr_rw :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : Maybe nat),
            loadRaw addr n l h = MachineState n l h (CMemNodePtr addr x) →
            loadLinkedListNodePtr addr n l h = MachineState n l h x.
Proof.
    intros n l h addr x H.
    unfold loadLinkedListNodePtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Verify that if a location fails to load, it can't be cast to a list ptr. *)
Lemma loadLinkedListPtr_MachineErrorLoad :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat),
            loadRaw addr n l h = MachineError MachineErrorLoad →
            loadLinkedListPtr addr n l h = MachineError MachineErrorLoad.
Proof.
    intros n l h addr H.
    apply bind_failure_MachineM, H.
Qed.

(* If the cell isn't a LinkedListPtr, then it can't be coerced. *)
Lemma loadLinkedListPtr_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (cell : CMemoryLocation),
        isCellListPtr cell = false →
        loadRaw addr n l h = MachineState n l h cell →
        loadLinkedListPtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr cell H1 H2.
    unfold loadLinkedListPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H2.
    unfold throw.
    destruct cell.
    reflexivity.  reflexivity. reflexivity. reflexivity.
    unfold isCellListPtr in H1.  inversion H1.
    reflexivity. reflexivity.
Qed.

(* Happy path: we can load linked list pointers. *)
Lemma loadLinkedListPtr_rw :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : Maybe nat),
            loadRaw addr n l h = MachineState n l h (CMemListPtr addr x) →
            loadLinkedListPtr addr n l h = MachineState n l h x.
Proof.
    intros n l h addr x H.
    unfold loadLinkedListPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Verify that if a location fails to load, it can't be a node ptr ptr. *)
Lemma loadLinkedListNodePtrPtr_MachineErrorLoad :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat),
            loadRaw addr n l h = MachineError MachineErrorLoad →
            loadLinkedListNodePtrPtr addr n l h = MachineError MachineErrorLoad.
Proof.
    intros n l h addr H.
    apply bind_failure_MachineM, H.
Qed.

(* If the cell isn't a LinkedListNodePtrPtr, then it can't be coerced. *)
Lemma loadLinkedListNodePtrPtr_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (cell : CMemoryLocation),
        isCellNodePtrPtr cell = false →
        loadRaw addr n l h = MachineState n l h cell →
        loadLinkedListNodePtrPtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr cell H1 H2.
    unfold loadLinkedListNodePtrPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H2.
    unfold throw.
    destruct cell.
    reflexivity.  reflexivity. reflexivity.  reflexivity.  reflexivity.
    unfold isCellNodePtr in H1.  inversion H1.
    reflexivity.
Qed.

(* Happy path: we can load linked list node pointer pointers. *)
Lemma loadLinkedListNodePtrPtr_rw :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : Maybe nat),
            loadRaw addr n l h = MachineState n l h (CMemNodePtrPtr addr x) →
            loadLinkedListNodePtrPtr addr n l h = MachineState n l h x.
Proof.
    intros n l h addr x H.
    unfold loadLinkedListNodePtrPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Verify that if a location fails to load, it can't be a list ptr ptr. *)
Lemma loadLinkedListPtrPtr_MachineErrorLoad :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat),
            loadRaw addr n l h = MachineError MachineErrorLoad →
            loadLinkedListPtrPtr addr n l h = MachineError MachineErrorLoad.
Proof.
    intros n l h addr H.
    apply bind_failure_MachineM, H.
Qed.

(* If the cell isn't a LinkedListPtrPtr, then it can't be coerced. *)
Lemma loadLinkedListPtrPtr_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (cell : CMemoryLocation),
        isCellListPtrPtr cell = false →
        loadRaw addr n l h = MachineState n l h cell →
        loadLinkedListPtrPtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr cell H1 H2.
    unfold loadLinkedListPtrPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H2.
    unfold throw.
    destruct cell.
    reflexivity.  reflexivity. reflexivity.  reflexivity.  reflexivity.
    reflexivity.
    unfold isCellNodePtr in H1.  inversion H1.
Qed.

(* Happy path: we can load linked list pointer pointers. *)
Lemma loadLinkedListPtrPtr_rw :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : Maybe nat),
            loadRaw addr n l h = MachineState n l h (CMemListPtrPtr addr x) →
            loadLinkedListPtrPtr addr n l h = MachineState n l h x.
Proof.
    intros n l h addr x H.
    unfold loadLinkedListPtrPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Verify that if a loc fails to load, it can't be cast to a list node ptr. *)
Lemma loadLocalLinkedListNodePtr_MachineErrorLoad :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat),
            loadLocalRaw addr n l h = MachineError MachineErrorLoad →
            loadLocalLinkedListNodePtr addr n l h =
                MachineError MachineErrorLoad.
Proof.
    intros n l h addr H.
    apply bind_failure_MachineM, H.
Qed.

(* If the cell isn't a LinkedListNodePtr, then it can't be coerced. *)
Lemma loadLocalLinkedListNodePtr_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (cell : CMemoryLocation),
        isCellNodePtr cell = false →
        loadLocalRaw addr n l h = MachineState n l h cell →
        loadLocalLinkedListNodePtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr cell H1 H2.
    unfold loadLocalLinkedListNodePtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H2.
    unfold throw.
    destruct cell.
    reflexivity.  reflexivity. reflexivity.
    unfold isCellNodePtr in H1.  inversion H1.
    reflexivity. reflexivity. reflexivity.
Qed.

(* Happy path: we can load linked list node pointers. *)
Lemma loadLocalLinkedListNodePtr_rw :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : Maybe nat),
            loadLocalRaw addr n l h = MachineState n l h (CMemNodePtr addr x) →
            loadLocalLinkedListNodePtr addr n l h = MachineState n l h x.
Proof.
    intros n l h addr x H.
    unfold loadLocalLinkedListNodePtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Verify that if a location fails to load, it can't be cast to a list ptr. *)
Lemma loadLocalLinkedListPtr_MachineErrorLoad :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat),
            loadLocalRaw addr n l h = MachineError MachineErrorLoad →
            loadLocalLinkedListPtr addr n l h = MachineError MachineErrorLoad.
Proof.
    intros n l h addr H.
    apply bind_failure_MachineM, H.
Qed.

(* If the cell isn't a LinkedListPtr, then it can't be coerced. *)
Lemma loadLocalLinkedListPtr_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (cell : CMemoryLocation),
        isCellListPtr cell = false →
        loadLocalRaw addr n l h = MachineState n l h cell →
        loadLocalLinkedListPtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr cell H1 H2.
    unfold loadLocalLinkedListPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H2.
    unfold throw.
    destruct cell.
    reflexivity.  reflexivity. reflexivity. reflexivity.
    unfold isCellListPtr in H1.  inversion H1.
    reflexivity. reflexivity.
Qed.

(* loadLocalLinkedListPtr reads a pointer value from local scope. *)
Lemma loadLocalLinkedListPtr_rw :
    ∀ (n addr : nat) (h : CHeap) (l : CLocal) (val : Maybe nat),
        l = CLocalState addr [CMemListPtr addr val] →
        loadLocalLinkedListPtr addr n l h = MachineState n l h val.
Proof.
    intros.
    unfold loadLocalLinkedListPtr.
    unfold loadLocalRaw.
    unfold getLocalMemory.
    unfold getLocal.
    rewrite H.
    unfold bind, MachineMMonad.
    simpl.
    rewrite nat_eqb_refl.
    reflexivity.
Qed.

(* Verify that if a loc fails to load, it can't be cast to a node ptr ptr. *)
Lemma loadLocalLinkedListNodePtrPtr_MachineErrorLoad :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat),
            loadLocalRaw addr n l h = MachineError MachineErrorLoad →
            loadLocalLinkedListNodePtrPtr addr n l h =
                MachineError MachineErrorLoad.
Proof.
    intros n l h addr H.
    apply bind_failure_MachineM, H.
Qed.

(* If the cell isn't a LinkedListNodePtrPtr, then it can't be coerced. *)
Lemma loadLocalLinkedListNodePtrPtr_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (cell : CMemoryLocation),
        isCellNodePtrPtr cell = false →
        loadLocalRaw addr n l h = MachineState n l h cell →
        loadLocalLinkedListNodePtrPtr addr n l h =
            MachineError MachineErrorCast.
Proof.
    intros n l h addr cell H1 H2.
    unfold loadLocalLinkedListNodePtrPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H2.
    unfold throw.
    destruct cell.
    reflexivity.  reflexivity.  reflexivity.  reflexivity.  reflexivity.
    unfold isCellNodePtr in H1.  inversion H1.
    reflexivity.
Qed.

(* Happy path: we can load linked list node pointers. *)
Lemma loadLocalLinkedListNodePtrPtr_rw :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : Maybe nat),
            loadLocalRaw addr n l h =
                MachineState n l h (CMemNodePtrPtr addr x) →
            loadLocalLinkedListNodePtrPtr addr n l h = MachineState n l h x.
Proof.
    intros n l h addr x H.
    unfold loadLocalLinkedListNodePtrPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Verify that if a loc fails to load, it can't be cast to a list ptr ptr. *)
Lemma loadLocalLinkedListPtrPtr_MachineErrorLoad :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat),
            loadLocalRaw addr n l h = MachineError MachineErrorLoad →
            loadLocalLinkedListPtrPtr addr n l h =
                MachineError MachineErrorLoad.
Proof.
    intros n l h addr H.
    apply bind_failure_MachineM, H.
Qed.

(* If the cell isn't a LinkedListPtrPtr, then it can't be coerced. *)
Lemma loadLocalLinkedListPtrPtr_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (cell : CMemoryLocation),
        isCellListPtrPtr cell = false →
        loadLocalRaw addr n l h = MachineState n l h cell →
        loadLocalLinkedListPtrPtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr cell H1 H2.
    unfold loadLocalLinkedListPtrPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H2.
    unfold throw.
    destruct cell.
    reflexivity.  reflexivity. reflexivity. reflexivity.  reflexivity.
    reflexivity.
    unfold isCellListPtr in H1.  inversion H1.
Qed.

(* loadLocalLinkedListPtrPtr reads a pointer value from local scope. *)
Lemma loadLocalLinkedListPtrPtr_rw :
    ∀ (n addr : nat) (h : CHeap) (l : CLocal) (val : Maybe nat),
        l = CLocalState addr [CMemListPtrPtr addr val] →
        loadLocalLinkedListPtrPtr addr n l h = MachineState n l h val.
Proof.
    intros.
    unfold loadLocalLinkedListPtrPtr.
    unfold loadLocalRaw.
    unfold getLocalMemory.
    unfold getLocal.
    rewrite H.
    unfold bind, MachineMMonad.
    simpl.
    rewrite nat_eqb_refl.
    reflexivity.
Qed.

(* unwrap past a load linked list pointer when the top of heap doesn't match. *)
Lemma loadLinkedListPtr_unwrap :
    ∀ (index n : nat) (l : CLocal) (h : CHeap) (addr : nat)
      (cell : CMemoryLocation) (values : IList CMemoryLocation)
      (val : Maybe nat),
        Nat.eqb (locAddr cell) addr = false →
        h = CHeapState index ([cell] ++ values) →
        loadLinkedListPtr addr n l h =
                ((match lookupMem addr values with
                    | Just cell => ret cell
                    | Nothing => throw MachineErrorLoad
                    end) ▶
                (λ cell ↦
                    match cell with
                    | CMemListPtr _ val => ret val
                    | _ => throw MachineErrorCast
                    end)) n l h.
Proof.
    intros.
    unfold loadLinkedListPtr.
    unfold loadRaw.
    unfold getHeapMemory.
    unfold getHeap.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H0.
    unfold lookupMem.
    simpl.
    rewrite H.
    simpl.
    fold lookupMem.
    reflexivity.
Qed.

End CMachineLoadTheorems.
