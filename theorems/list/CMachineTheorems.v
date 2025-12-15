Require Import RCPR.Data.IList.
Require Import RCPR.Data.Maybe.
Require Import RCPR.Data.Monad.
Require Import RCPR.Helpers.Notation.
Require Import RCPR.Theorems.IListTheorems.
Require Import RCPR.Theorems.NatTheorems.
Require Import list.CMachine.
Require Import list.CMachineLoadTheorems.

Import CMachine.
Import CMachineLoadTheorems.
Import IList.
Import IListTheorems.
Import Maybe.
Import Monad.
Import NatTheorems.
Import Notation.

Module CMachineTheorems.

Open Scope monad_scope.

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
Lemma memReplace_MatchingCell_head :
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

(* if the address of a cell matches, memReplace replaces this cell. *)
Lemma memReplace_MatchingCell :
    ∀ (lvalues : IList CMemoryLocation) (n : nat) (l : CLocal) (h : CHeap)
      (addr : nat) (ocell ncell : CMemoryLocation)
      (rvalues acc : IList CMemoryLocation),
            (∀ x, In x lvalues → Nat.eqb (locAddr x) addr = false) →
            locAddr ocell = addr →
            memReplace addr ncell (lvalues ++ (ocell :: rvalues)) n l h =
                MachineState n l h (lvalues ++ (ncell :: rvalues)).
Proof.
    intros.
    unfold memReplace.
    apply memReplaceLoop_MatchingCell; try assumption.
Qed.

(* if loadLinkedListNode fails, then so does storeLinkedListNode. *)
Lemma storeLinkedListNode_loadFailure :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (e : MachineErrorCode)
      (node : CLinkedListNode),
        loadLinkedListNode addr n l h = MachineError e →
        storeLinkedListNode addr node n l h = MachineError e.
Proof.
    intros.
    unfold storeLinkedListNode.
    unfold bind, MachineMMonad.
    unfold getHeapMemory.
    unfold getHeap.
    destruct h.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* storeLinkedListNode happy path. *)
Lemma storeLinkedListNode_rw :
    ∀ (n idx : nat) (l : CLocal) (oh nh : CHeap) (addr : nat)
      (e : MachineErrorCode) (onode nnode : CLinkedListNode)
      (ll values rr : IList CMemoryLocation),
       (∀ x, In x ll → Nat.eqb (locAddr x) addr = false) →
        oh = CHeapState idx values →
        values = ll ++ ((CMemNode addr onode) :: rr) →
        nh = CHeapState idx (ll ++ ((CMemNode addr nnode) :: rr)) →
        getHeapMemory n l oh = MachineState n l oh values →
        loadLinkedListNode addr n l oh = MachineState n l oh onode →
        storeLinkedListNode addr nnode n l oh = MachineState n l nh tt.
Proof.
    intros.
    unfold storeLinkedListNode.
    unfold bind, MachineMMonad.
    unfold getHeapMemory.
    unfold getHeap.
    rewrite H0.
    rewrite H0 in H4.
    simpl.
    rewrite H4.
    rewrite H1.
    rewrite H2.
    rewrite memReplace_MatchingCell; try assumption.
    unfold putHeapMemory.
    unfold putHeap.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
Qed.

(* if loadLinkedList fails, then so does storeLinkedList. *)
Lemma storeLinkedList_loadFailure :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (e : MachineErrorCode)
      (val : CLinkedList),
        loadLinkedList addr n l h = MachineError e →
        storeLinkedList addr val n l h = MachineError e.
Proof.
    intros.
    unfold storeLinkedList.
    unfold bind, MachineMMonad.
    unfold getHeapMemory.
    unfold getHeap.
    destruct h.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* storeLinkedList happy path. *)
Lemma storeLinkedList_rw :
    ∀ (n idx : nat) (l : CLocal) (oh nh : CHeap) (addr : nat)
      (e : MachineErrorCode) (oval nval : CLinkedList)
      (ll values rr : IList CMemoryLocation),
       (∀ x, In x ll → Nat.eqb (locAddr x) addr = false) →
        oh = CHeapState idx values →
        values = ll ++ ((CMemList addr oval) :: rr) →
        nh = CHeapState idx (ll ++ ((CMemList addr nval) :: rr)) →
        getHeapMemory n l oh = MachineState n l oh values →
        loadLinkedList addr n l oh = MachineState n l oh oval →
        storeLinkedList addr nval n l oh = MachineState n l nh tt.
Proof.
    intros.
    unfold storeLinkedList.
    unfold bind, MachineMMonad.
    unfold getHeapMemory.
    unfold getHeap.
    rewrite H0.
    rewrite H0 in H4.
    simpl.
    rewrite H4.
    rewrite H1.
    rewrite H2.
    rewrite memReplace_MatchingCell; try assumption.
    unfold putHeapMemory.
    unfold putHeap.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
Qed.

(* if loadLinkedListNodePtr fails, then so does storeLinkedListNodePtr. *)
Lemma storeLinkedListNodePtr_loadFailure :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (e : MachineErrorCode)
      (val : Maybe nat),
        loadLinkedListNodePtr addr n l h = MachineError e →
        storeLinkedListNodePtr addr val n l h = MachineError e.
Proof.
    intros.
    unfold storeLinkedListNodePtr.
    unfold bind, MachineMMonad.
    unfold getHeapMemory.
    unfold getHeap.
    destruct h.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* storeLinkedListNodePtr happy path. *)
Lemma storeLinkedListNodePtr_rw :
    ∀ (n idx : nat) (l : CLocal) (oh nh : CHeap) (addr : nat)
      (e : MachineErrorCode) (oval nval : Maybe nat)
      (ll values rr : IList CMemoryLocation),
       (∀ x, In x ll → Nat.eqb (locAddr x) addr = false) →
        oh = CHeapState idx values →
        values = ll ++ ((CMemNodePtr addr oval) :: rr) →
        nh = CHeapState idx (ll ++ ((CMemNodePtr addr nval) :: rr)) →
        getHeapMemory n l oh = MachineState n l oh values →
        loadLinkedListNodePtr addr n l oh = MachineState n l oh oval →
        storeLinkedListNodePtr addr nval n l oh = MachineState n l nh tt.
Proof.
    intros.
    unfold storeLinkedListNodePtr.
    unfold bind, MachineMMonad.
    unfold getHeapMemory.
    unfold getHeap.
    rewrite H0.
    rewrite H0 in H4.
    simpl.
    rewrite H4.
    rewrite H1.
    rewrite H2.
    rewrite memReplace_MatchingCell; try assumption.
    unfold putHeapMemory.
    unfold putHeap.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
Qed.

(* if loadLinkedListPtr fails, then so does storeLinkedListPtr. *)
Lemma storeLinkedListPtr_loadFailure :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat) (e : MachineErrorCode)
      (val : Maybe nat),
        loadLinkedListPtr addr n l h = MachineError e →
        storeLinkedListPtr addr val n l h = MachineError e.
Proof.
    intros.
    unfold storeLinkedListPtr.
    unfold bind, MachineMMonad.
    unfold getHeapMemory.
    unfold getHeap.
    destruct h.
    simpl.
    rewrite H.
    reflexivity.
Qed.

(* storeLinkedListPtr happy path. *)
Lemma storeLinkedListPtr_rw :
    ∀ (n idx : nat) (l : CLocal) (oh nh : CHeap) (addr : nat)
      (e : MachineErrorCode) (oval nval : Maybe nat)
      (ll values rr : IList CMemoryLocation),
       (∀ x, In x ll → Nat.eqb (locAddr x) addr = false) →
        oh = CHeapState idx values →
        values = ll ++ ((CMemListPtr addr oval) :: rr) →
        nh = CHeapState idx (ll ++ ((CMemListPtr addr nval) :: rr)) →
        getHeapMemory n l oh = MachineState n l oh values →
        loadLinkedListPtr addr n l oh = MachineState n l oh oval →
        storeLinkedListPtr addr nval n l oh = MachineState n l nh tt.
Proof.
    intros.
    unfold storeLinkedListPtr.
    unfold bind, MachineMMonad.
    unfold getHeapMemory.
    unfold getHeap.
    rewrite H0.
    rewrite H0 in H4.
    simpl.
    rewrite H4.
    rewrite H1.
    rewrite H2.
    rewrite memReplace_MatchingCell; try assumption.
    unfold putHeapMemory.
    unfold putHeap.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
Qed.

(* createLocalLinkedListPtr updates local scope with the pointer. *)
Definition createLocalLinkedListPtr_rw :
    ∀ (n index : nat) (h : CHeap) (l nl : CLocal) (ptr : Maybe nat),
        l = CLocalState index [] →
        nl = CLocalState (index + 1) [CMemListPtr (index + 1) ptr] →
        createLocalLinkedListPtr ptr n l h = MachineState n nl h (index + 1).
Proof.
    intros.
    unfold createLocalLinkedListPtr.
    unfold localCreate.
    unfold getLocal.
    unfold putLocal.
    rewrite H.
    rewrite H0.
    unfold bind, MachineMMonad.
    simpl.
    reflexivity.
Qed.

(* storeLocalLinkedListPtr updates local scope with the pointer. *)
Lemma storeLocalLinkedListPtr_rw :
    ∀ (n addr : nat) (h : CHeap) (l nl : CLocal) (oval nval : Maybe nat),
        l = CLocalState addr [CMemListPtr addr oval] →
        nl = CLocalState addr [CMemListPtr addr nval] →
        storeLocalLinkedListPtr addr nval n l h = MachineState n nl h tt.
Proof.
    intros.
    unfold storeLocalLinkedListPtr.
    unfold loadLocalLinkedListPtr.
    unfold loadLocalRaw.
    unfold lookupMem.
    unfold getLocalMemory.
    unfold getLocal.
    rewrite H.
    unfold bind, MachineMMonad.
    simpl.
    rewrite nat_eqb_refl.
    unfold memReplace.
    unfold memReplaceLoop.
    unfold locAddr.
    rewrite nat_eqb_refl.
    simpl.
    unfold putLocalMemory.
    unfold getLocal.
    unfold putLocal.
    unfold bind, MachineMMonad.
    rewrite <- H0.
    reflexivity.
Qed.

(* maybeCreateLinkedList happy path lemma. *)
Definition maybeCreateLinkedList_rw :
    ∀ (n index : nat) (oh nh : CHeap) (l : CLocal) (ptr : Maybe nat)
      (vals : IList CMemoryLocation),
        oh = CHeapState index vals →
        nh = CHeapState (index + 1)
                        (vals ++ [CMemList (index + 1)
                                           (List Nothing Nothing 0)]) →
        maybeCreateLinkedList' n l oh = MachineState n l nh (Just (index + 1)).
Proof.
    intros.
    unfold maybeCreateLinkedList'.
    unfold heapCreate.
    unfold getHeap.
    unfold putHeap.
    rewrite H.
    unfold bind, MachineMMonad.
    simpl.
    rewrite <- H0.
    reflexivity.
Qed.

(* simplified storeLinkedListPtr happy path, linkedListPtr first element. *)
Lemma storeLinkedListPtr_simpl :
    ∀ (n index addr: nat) (l : CLocal) (oh nh : CHeap)
      (oval nval : Maybe nat) (ocell : CMemoryLocation)
      (values nvalues : IList CMemoryLocation),
        oh = CHeapState index values →
        nh = CHeapState index nvalues →
        values = [CMemListPtr addr oval; ocell] →
        nvalues = [CMemListPtr addr nval; ocell] →
        storeLinkedListPtr addr nval n l oh = MachineState n l nh tt.
Proof.
    intros.
    unfold storeLinkedListPtr.
    unfold getHeapMemory.
    unfold getHeap.
    unfold bind, MachineMMonad.
    rewrite H0.
    rewrite H2.
    simpl.
    rewrite H.
    rewrite H1.
    simpl.
    rewrite <- H1.
    rewrite <- H.
    rewrite (@loadLinkedListPtr_rw n l oh addr oval);
        try assumption.
    2: {
        rewrite H1 in H.
        erewrite loadRaw_simpl; try eauto.
    }
    unfold memReplace.
    unfold memReplaceLoop.
    rewrite H1.
    unfold locAddr.
    rewrite nat_eqb_refl.
    unfold putHeapMemory.
    unfold putHeap.
    unfold getHeap.
    unfold bind, MachineMMonad.
    rewrite H.
    simpl.
    reflexivity.
Qed.

(* simplified storeLinkedListPtr happy path, linkedListPtr not first element. *)
Lemma storeLinkedListPtr_simpl2 :
    ∀ (n index addr notAddr : nat) (l : CLocal) (oh nh : CHeap)
      (e : MachineErrorCode) (oval nval : Maybe nat) (ocell : CMemoryLocation)
      (values nvalues : IList CMemoryLocation),
        Nat.eqb (locAddr ocell) addr = false →
        oh = CHeapState index values →
        nh = CHeapState index nvalues →
        values = [ocell; CMemListPtr addr oval] →
        nvalues = [ocell; CMemListPtr addr nval] →
        storeLinkedListPtr addr nval n l oh = MachineState n l nh tt.
Proof.
    intros.
    unfold storeLinkedListPtr.
    unfold getHeapMemory.
    unfold getHeap.
    unfold bind, MachineMMonad.
    rewrite H0.
    rewrite H2.
    simpl.
    rewrite <- H2.
    rewrite <- H0.
    rewrite (@loadLinkedListPtr_unwrap index n l oh addr ocell
                                       [CMemListPtr addr oval] Nothing);
        try assumption.
    2: {
        simpl.
        rewrite H2 in H0.
        assumption.
    }
    rewrite H0.
    rewrite H2.
    unfold bind, MachineMMonad.
    simpl.
    rewrite nat_eqb_refl.
    unfold memReplace.
    unfold memReplaceLoop.
    unfold bind, MachineMMonad.
    rewrite nat_eqb_refl.
    rewrite H.
    simpl.
    unfold putHeapMemory.
    unfold putHeap.
    simpl.
    rewrite <- H3.
    rewrite <- H1.
    reflexivity.
Qed.

(* createLocalLinkedListNodePtr updates local scope with the pointer. *)
Definition createLocalLinkedListNodePtr_rw :
    ∀ (n index : nat) (h : CHeap) (l nl : CLocal) (ptr : Maybe nat),
        l = CLocalState index [] →
        nl = CLocalState (index + 1) [CMemNodePtr (index + 1) ptr] →
        createLocalLinkedListNodePtr ptr n l h =
            MachineState n nl h (index + 1).
Proof.
    intros.
    unfold createLocalLinkedListNodePtr.
    unfold localCreate.
    unfold getLocal.
    unfold putLocal.
    rewrite H.
    rewrite H0.
    unfold bind, MachineMMonad.
    simpl.
    reflexivity.
Qed.

(* incrementLinkedListCount increments the count of a linked list. *)
Definition incrementLinkedListCount_rw :
    ∀ (n index addr count : nat) (oh nh : CHeap) (l : CLocal)
      (head tail : Maybe nat),
        oh = CHeapState index [CMemList addr (List head tail count)] →
        nh = CHeapState index [CMemList addr (List head tail (count + 1))] →
        incrementLinkedListCount addr n l oh = MachineState n l nh tt.
Proof.
    intros.
    rewrite H.
    unfold incrementLinkedListCount.
    simpl.
    unfold loadLinkedList.
    simpl.
    unfold loadRaw.
    simpl.
    rewrite nat_eqb_refl.
    unfold storeLinkedList.
    simpl.
    unfold loadLinkedList.
    simpl.
    unfold loadRaw.
    simpl.
    rewrite nat_eqb_refl.
    unfold memReplace.
    simpl.
    rewrite nat_eqb_refl.
    unfold putHeapMemory.
    simpl.
    unfold putHeap.
    rewrite H0.
    reflexivity.
Qed.

(* decrementListCount raises an Integer Underflow exception if the count is *)
(* decremented below 0. *)
Definition decrementLinkedListCount_IntegerUnderflow :
    ∀ (n index addr count : nat) (h : CHeap) (l : CLocal)
      (head tail : Maybe nat),
        h = CHeapState index [CMemList addr (List head tail 0)] →
        decrementLinkedListCount addr n l h =
            MachineError MachineErrorIntegerUnderflow.
Proof.
    intros.
    rewrite H.
    unfold decrementLinkedListCount.
    simpl.
    unfold loadLinkedList.
    simpl.
    unfold loadRaw.
    simpl.
    rewrite nat_eqb_refl.
    unfold throw.
    reflexivity.
Qed.

(* decrementLinkedListCount decrements the count of a linked list. *)
Definition decrementLinkedListCount_rw :
    ∀ (n index addr count : nat) (oh nh : CHeap) (l : CLocal)
      (head tail : Maybe nat),
        count > 0 →
        oh = CHeapState index [CMemList addr (List head tail count)] →
        nh = CHeapState index [CMemList addr (List head tail (count - 1))] →
        decrementLinkedListCount addr n l oh = MachineState n l nh tt.
Proof.
    intros.
    rewrite H0.
    unfold decrementLinkedListCount.
    simpl.
    unfold loadLinkedList.
    simpl.
    unfold loadRaw.
    simpl.
    rewrite nat_eqb_refl.
    destruct count.
    inversion H.
    unfold storeLinkedList.
    simpl.
    unfold loadLinkedList.
    simpl.
    unfold loadRaw.
    simpl.
    rewrite nat_eqb_refl.
    unfold memReplace.
    simpl.
    rewrite nat_eqb_refl.
    unfold putHeapMemory.
    simpl.
    unfold putHeap.
    rewrite H1.
    simpl.
    assert (H_count_0 : count - 0 = count).
    {
        destruct count.
        simpl.
        reflexivity.
        simpl.
        reflexivity.
    }
    rewrite H_count_0.
    reflexivity.
Qed.

(* It is an error to set the head value for a linked list to a non-existent *)
(* or invalid address. *)
Lemma setLinkedListHead_loadFailure :
    ∀ (n index addr headAddr count : nat) (l : CLocal) (h : CHeap)
      (ohead tail : Maybe nat) (e : MachineErrorCode),
        h = CHeapState index [CMemList addr (List ohead tail count)] →
        loadLinkedListNode headAddr n l h = MachineError e →
        setLinkedListHead addr (Just headAddr) n l h = MachineError e.
Proof.
    intros.
    unfold setLinkedListHead.
    unfold bind, MachineMMonad.
    rewrite H0.
    reflexivity.
Qed.

End CMachineTheorems.
