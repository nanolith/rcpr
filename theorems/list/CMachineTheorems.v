Require Import RCPR.Data.IList.
Require Import RCPR.Data.Maybe.
Require Import RCPR.Data.Monad.
Require Import RCPR.Helpers.Notation.
Require Import RCPR.Theorems.IListTheorems.
Require Import list.CMachine.

Import CMachine.
Import IList.
Import IListTheorems.
Import Maybe.
Import Monad.
Import Notation.

Module CMachineTheorems.

Open Scope monad_scope.

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
    reflexivity.  reflexivity.  reflexivity.
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
Abort.

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
    unfold isCellNode in H1.  inversion H1.
    reflexivity.  reflexivity.
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

(* Can't coerce uninitialized memory to LinkedListNodePtr. *)
Lemma loadLinkedListNodePtr_Uninit_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat),
            loadRaw addr n l h = MachineState n l h (CMemUninit addr) →
            loadLinkedListNodePtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr H.
    unfold loadLinkedListNodePtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Can't coerce LinkedListNode to LinkedListNodePtr. *)
Lemma loadLinkedListNodePtr_LinkedListNode_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : CLinkedListNode),
            loadRaw addr n l h = MachineState n l h (CMemNode addr x) →
            loadLinkedListNodePtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr x H.
    unfold loadLinkedListNodePtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Can't coerce LinkedList to LinkedListNodePtr. *)
Lemma loadLinkedListNodePtr_LinkedList_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : CLinkedList),
            loadRaw addr n l h = MachineState n l h (CMemList addr x) →
            loadLinkedListNodePtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr x H.
    unfold loadLinkedListNodePtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Can't coerce LinkedListPtr to LinkedListNodePtr. *)
Lemma loadLinkedListNodePtr_LinkedListPtr_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : nat),
            loadRaw addr n l h = MachineState n l h (CMemListPtr addr x) →
            loadLinkedListNodePtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr x H.
    unfold loadLinkedListNodePtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Happy path: we can load linked list node pointers. *)
Lemma loadLinkedListNodePtr_rw :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : nat),
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
Abort.

(* Can't coerce uninitialized memory to LinkedListPtr. *)
Lemma loadLinkedListPtr_Uninit_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat),
            loadRaw addr n l h = MachineState n l h (CMemUninit addr) →
            loadLinkedListPtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr H.
    unfold loadLinkedListPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Can't coerce a linked list node to LinkedListPtr. *)
Lemma loadLinkedListPtr_LinkedListNode_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : CLinkedListNode),
            loadRaw addr n l h = MachineState n l h (CMemNode addr x) →
            loadLinkedListPtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr x H.
    unfold loadLinkedListPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Can't coerce a linked list to LinkedListPtr. *)
Lemma loadLinkedListPtr_LinkedList_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : CLinkedList),
            loadRaw addr n l h = MachineState n l h (CMemList addr x) →
            loadLinkedListPtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr x H.
    unfold loadLinkedListPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Can't coerce a linked list node ptr to LinkedListPtr. *)
Lemma loadLinkedListPtr_LinkedListNodePtr_MachineErrorCast :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : nat),
            loadRaw addr n l h = MachineState n l h (CMemNodePtr addr x) →
            loadLinkedListPtr addr n l h = MachineError MachineErrorCast.
Proof.
    intros n l h addr x H.
    unfold loadLinkedListPtr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* Happy path: we can load linked list pointers. *)
Lemma loadLinkedListPtr_rw :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (x : nat),
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

(* memReplace on an empty list throws a MachineErrorStore exception. *)
Lemma memReplace_EmptyValues :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (cell : CMemoryLocation),
            memReplace addr cell [] n l h = MachineError MachineErrorStore.
Proof.
    intros n l h addr cell.
    simpl.
    unfold throw.
    reflexivity.
Qed.

(* if the address of a cell matches, memReplace replaces this cell. *)
Lemma memReplace_MatchingCell :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat)
      (ocell ncell : CMemoryLocation) (values : IList CMemoryLocation),
            locAddr ocell = addr →
            memReplace addr ncell (ocell :: values) n l h =
                MachineState n l h (ncell :: values).
Proof.
    intros n l h addr ocell ncell values.
    assert (H1 : Nat.eqb addr addr = true).
    {
        induction addr.
        simpl.
        reflexivity.
        simpl.
        rewrite IHaddr.
        reflexivity.
    }
    intros H.
    unfold memReplace.
    unfold memReplaceLoop.
    rewrite H.
    rewrite H1.
    simpl.
    reflexivity.
Qed.

(* if the address of a cell does not match, memReplaceLoop keeps going. *)
Lemma memReplaceLoop_Unfold :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr1 addr2 : nat)
      (ocell ncell : CMemoryLocation) (values : IList CMemoryLocation),
            locAddr ocell = addr2 →
            Nat.eqb addr2 addr1 = false →
            memReplaceLoop addr1 ncell (ocell :: values) [] n l h =
                memReplaceLoop addr1 ncell values [ocell] n l h.
Proof.
    intros n l h addr1 addr2 ocell ncell values H1 H2.
    unfold memReplaceLoop.
    rewrite H1.
    rewrite H2.
    fold memReplaceLoop.
    reflexivity.
Qed.

End CMachineTheorems.
