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

(* Helper lemma for nat equality. *)
Lemma nat_eqb_refl :
    ∀ (x :  nat),
        Nat.eqb x x = true.
Proof.
    induction x.
    simpl.
    reflexivity.
    simpl.
    rewrite IHx.
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
    intros H.
    unfold memReplace.
    unfold memReplaceLoop.
    rewrite H.
    rewrite nat_eqb_refl.
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

(* if the address of a cell matches, memReplace replaces this cell. *)
Lemma memReplaceLoop_MatchingCell_reverse_acc :
    ∀ (lvalues : IList CMemoryLocation) (n : nat) (l : CLocal) (h : CHeap)
      (addr : nat) (ocell ncell : CMemoryLocation)
      (rvalues acc : IList CMemoryLocation),
            (∀ x, In x lvalues → Nat.eqb (locAddr x) addr = false) →
            locAddr ocell = addr →
            memReplaceLoop addr ncell (lvalues ++ (ocell :: rvalues))
                           acc n l h =
                MachineState n l h
                    ((reverse acc) ++ (lvalues ++ (ncell :: rvalues))).
Proof.
    intros lvalues.
    induction lvalues as [| head tail IH].
    (* base case: the list starts with ocell. *)
    intros n l h addr ocell ncell rvalues acc H_not_in H_match.
    simpl.
    rewrite H_match.
    rewrite nat_eqb_refl.
    reflexivity.
    (* Inductive case: lvalues = head :: tail. *)
    intros n l h addr ocell ncell rvalues acc H_not_in H_match.
    (* Show that head does not match addr. *)
    assert (H_head_neq : Nat.eqb (locAddr head) addr = false).
    {
        apply H_not_in.
        left.
        reflexivity.
    }
    unfold memReplaceLoop.
    simpl.
    rewrite H_head_neq.
    rewrite IH.
    rewrite IList_reverse_peel.
    rewrite IList_reverse_peel3.
    reflexivity.
    intros x H_in.
    apply H_not_in.
    right.
    apply H_in.
    apply H_match.
Qed.

(* if the address of a cell matches, memReplace replaces this cell. *)
Lemma memReplaceLoop_MatchingCell :
    ∀ (lvalues : IList CMemoryLocation) (n : nat) (l : CLocal) (h : CHeap)
      (addr : nat) (ocell ncell : CMemoryLocation)
      (rvalues acc : IList CMemoryLocation),
            (∀ x, In x lvalues → Nat.eqb (locAddr x) addr = false) →
            locAddr ocell = addr →
            memReplaceLoop addr ncell (lvalues ++ (ocell :: rvalues)) [] n l h =
                MachineState n l h (lvalues ++ (ncell :: rvalues)).
Proof.
    intros.
    rewrite memReplaceLoop_MatchingCell_reverse_acc; try assumption.
    simpl.
    reflexivity.
Qed.

End CMachineTheorems.
