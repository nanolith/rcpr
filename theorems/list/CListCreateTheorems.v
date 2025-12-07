Require Import RCPR.Data.IList.
Require Import RCPR.Data.Maybe.
Require Import RCPR.Data.Monad.
Require Import RCPR.Helpers.Notation.
Require Import RCPR.Theorems.IListTheorems.
Require Import RCPR.Theorems.NatTheorems.
Require Import list.CMachine.
Require Import list.CMachineTheorems.
Require Import list.CMachineLoadTheorems.

Import CMachine.
Import CMachineTheorems.
Import CMachineLoadTheorems.
Import IList.
Import IListTheorems.
Import Maybe.
Import Monad.
Import NatTheorems.
Import Notation.

Module CListCreateTheorems.

Open Scope monad_scope.

(* insListCreate returns an out-of-memory error if allocation fails. *)
Lemma insListCreate_outOfMemory :
    ∀ (n index : nat) (l l2 l3 l4 : CLocal) (h h2 : CHeap),
    (* Initial local store. *)
    l = CLocalState 0 [] →
    (* Local Store after creating locals. *)
    l2 = CLocalState 2 [CMemListPtrPtr 1 Nothing; CMemListPtr 2 Nothing] →
    (* Local store after creating linked list instance and saving it. *)
    l3 = CLocalState 2 [CMemListPtrPtr 1 (Just index); CMemListPtr 2 Nothing] →
    (* Initial heap with pointer to linked list. *)
    h = CHeapState index [CMemListPtr index Nothing] →
    (* Final local store. *)
    l4 = CLocalState 2 [CMemListPtrPtr 1 (Just index);
                        CMemListPtr 2 (Just (index + 1))] →
    (* Final heap. *)
    h2 = CHeapState (index + 1) [CMemListPtr index (Just (index + 1));
                                 CMemList (index + 1)
                                          (List Nothing Nothing 0)] →
    (* The first parameter is a pointer to the linked list pointer. *)
    getLinkedListPtrParameter 1 n l2 h = MachineState n l2 h (Just index) →
    (* Creation of the linked list can succeed or fail. *)
    maybeCreateLinkedList n l3 h = MachineState n l3 h Nothing →
    eval insListCreate n l h = MachineState n l3 h ErrorOutOfMemory.
Proof.
    intros.
    rewrite H.
    rewrite H0 in H5.
    rewrite H1 in H6.
    simpl.
    unfold evalAssignLocalListPtrPtrToListPtrParameter.
    simpl.
    rewrite H5.
    unfold storeLocalLinkedListPtrPtr.
    simpl.
    unfold evalCreateLinkedList.
    simpl.
    rewrite H6.
    simpl.
    rewrite H1.
    reflexivity.
Qed.

(* Happy path for insListCreate. *)
Lemma insListCreate_rw :
    ∀ (n index : nat) (l l2 l3 l4 : CLocal) (h h2 : CHeap),
    (* Initial local store. *)
    l = CLocalState 0 [] →
    (* Local Store after creating locals. *)
    l2 = CLocalState 2 [CMemListPtrPtr 1 Nothing; CMemListPtr 2 Nothing] →
    (* Local store after creating linked list instance and saving it. *)
    l3 = CLocalState 2 [CMemListPtrPtr 1 (Just index); CMemListPtr 2 Nothing] →
    (* Initial heap with pointer to linked list. *)
    h = CHeapState index [CMemListPtr index Nothing] →
    (* Final local store. *)
    l4 = CLocalState 2 [CMemListPtrPtr 1 (Just index);
                        CMemListPtr 2 (Just (index + 1))] →
    (* Final heap. *)
    h2 = CHeapState (index + 1) [CMemListPtr index (Just (index + 1));
                                 CMemList (index + 1)
                                          (List Nothing Nothing 0)] →
    (* The first parameter is a pointer to the linked list pointer. *)
    getLinkedListPtrParameter 1 n l2 h = MachineState n l2 h (Just index) →
    (* Creation of the linked list can succeed or fail. *)
    (maybeCreateLinkedList n l3 h = maybeCreateLinkedList' n l3 h) →
    eval insListCreate n l h = MachineState n l4 h2 StatusSuccess.
Proof.
    intros.
    rewrite H.
    rewrite H2.
    simpl.
    unfold evalAssignLocalListPtrPtrToListPtrParameter.
    simpl.
    rewrite H0 in H5.
    rewrite H2 in H5.
    rewrite H5.
    simpl.
    unfold evalCreateLinkedList.
    simpl.
    rewrite H1 in H6.
    rewrite H2 in H6.
    rewrite H6.
    simpl.
    unfold evalAssignLocalListHeapPointerToLocalListPtr.
    simpl.
    rewrite H3.
    rewrite H4.
    erewrite storeLinkedListPtr_simpl; try eauto.
Qed.

(* This function terminates and is correct (will cause a machine error),
   for any input, given that the provided preconditions are met. *)
Lemma insListCreate_total_correctness :
    ∀ (n index : nat) (l l2 l3 : CLocal) (h : CHeap),
    (* Initial local store. *)
    l = CLocalState 0 [] →
    (* Local Store after creating locals. *)
    l2 = CLocalState 2 [CMemListPtrPtr 1 Nothing; CMemListPtr 2 Nothing] →
    (* Local store after creating linked list instance and saving it. *)
    l3 = CLocalState 2 [CMemListPtrPtr 1 (Just index); CMemListPtr 2 Nothing] →
    (* Initial heap with pointer to linked list. *)
    h = CHeapState index [CMemListPtr index Nothing] →
    (* The first parameter is a pointer to the linked list pointer. *)
    getLinkedListPtrParameter 1 n l2 h = MachineState n l2 h (Just index) →
    (* Creation of the linked list can succeed or fail. *)
    (maybeCreateLinkedList n l3 h = MachineState n l3 h Nothing
        ∨ maybeCreateLinkedList n l3 h = maybeCreateLinkedList' n l3 h) →
    ∃ (n' : nat) (l' : CLocal) (h' : CHeap) (c' : CStatusCode),
    eval insListCreate n l h = MachineState n' l' h' c'.
Proof.
    intros.
    destruct H4 as [H_fail | H_success].
    (* Allocation failure case. *)
    1: {
        rewrite H.
        rewrite H0 in H3.
        rewrite H1 in H_fail.
        simpl.
        unfold evalAssignLocalListPtrPtrToListPtrParameter.
        simpl.
        rewrite H3.
        unfold storeLocalLinkedListPtrPtr.
        simpl.
        unfold evalCreateLinkedList.
        simpl.
        rewrite H_fail.
        simpl.
        eauto.
    }
    (* Allocation success case. *)
    erewrite insListCreate_rw; try eauto.
Qed.

(* The list created by insListCreate is empty. *)
Lemma insListCreate_extract_empty :
    ∀ (n index : nat) (l l2 l3 l4 : CLocal) (h h2 : CHeap),
    (* Initial local store. *)
    l = CLocalState 0 [] →
    (* Local Store after creating locals. *)
    l2 = CLocalState 2 [CMemListPtrPtr 1 Nothing; CMemListPtr 2 Nothing] →
    (* Local store after creating linked list instance and saving it. *)
    l3 = CLocalState 2 [CMemListPtrPtr 1 (Just index); CMemListPtr 2 Nothing] →
    (* Initial heap with pointer to linked list. *)
    h = CHeapState index [CMemListPtr index Nothing] →
    (* The first parameter is a pointer to the linked list pointer. *)
    getLinkedListPtrParameter 1 n l2 h = MachineState n l2 h (Just index) →
    (* Creation of the linked list can succeed or fail. *)
    maybeCreateLinkedList n l3 h = maybeCreateLinkedList' n l3 h →
    l4 = CLocalState 2 [CMemListPtrPtr 1 (Just index);
                        CMemListPtr 2 (Just (index + 1))] →
    h2 = CHeapState (index + 1) [CMemListPtr index (Just (index + 1));
                                 CMemList (index + 1)
                                          (List Nothing Nothing 0)] →
    eval insListCreate n l h = MachineState n l4 h2 StatusSuccess
        ↔ extractListFromC (index + 1) n l4 h2 = MachineState n l4 h2 [].
Proof.
    intros.
    split.
    (* Case 1: The newly created C Linked List is empty in forward dir. *)
    rewrite H.
    rewrite H2.
    rewrite H5.
    rewrite H6.
    intro Hlc.
    unfold extractListFromC.
    unfold loadLinkedList.
    unfold loadRaw.
    unfold getHeapMemory.
    unfold getHeap.
    unfold bind, MachineMMonad.
    simpl.
    rewrite nat_eqb_oneoff.
    rewrite nat_eqb_refl.
    unfold extractList.
    simpl.
    reflexivity.
    (* Case 2: This function constructs this list exactly as specified.  *)
    intro Hext.
    erewrite insListCreate_rw; try eauto.
Qed.

(* The reverse list created by insListCreate is empty. *)
Lemma insListCreate_rextract_empty :
    ∀ (n index : nat) (l l2 l3 l4 : CLocal) (h h2 : CHeap),
    (* Initial local store. *)
    l = CLocalState 0 [] →
    (* Local Store after creating locals. *)
    l2 = CLocalState 2 [CMemListPtrPtr 1 Nothing; CMemListPtr 2 Nothing] →
    (* Local store after creating linked list instance and saving it. *)
    l3 = CLocalState 2 [CMemListPtrPtr 1 (Just index); CMemListPtr 2 Nothing] →
    (* Initial heap with pointer to linked list. *)
    h = CHeapState index [CMemListPtr index Nothing] →
    (* The first parameter is a pointer to the linked list pointer. *)
    getLinkedListPtrParameter 1 n l2 h = MachineState n l2 h (Just index) →
    (* Creation of the linked list can succeed or fail. *)
    maybeCreateLinkedList n l3 h = maybeCreateLinkedList' n l3 h →
    l4 = CLocalState 2 [CMemListPtrPtr 1 (Just index);
                        CMemListPtr 2 (Just (index + 1))] →
    h2 = CHeapState (index + 1) [CMemListPtr index (Just (index + 1));
                                 CMemList (index + 1)
                                          (List Nothing Nothing 0)] →
    eval insListCreate n l h = MachineState n l4 h2 StatusSuccess
        ↔ extractReverseListFromC (index + 1) n l4 h2 = MachineState n l4 h2 [].
Proof.
    intros.
    split.
    (* Case 1: The newly created C Linked List is empty in reverse dir. *)
    rewrite H.
    rewrite H2.
    rewrite H5.
    rewrite H6.
    intro Hlc.
    unfold extractReverseListFromC.
    unfold loadLinkedList.
    unfold loadRaw.
    unfold getHeapMemory.
    unfold getHeap.
    unfold bind, MachineMMonad.
    simpl.
    rewrite nat_eqb_oneoff.
    rewrite nat_eqb_refl.
    unfold extractReverseList.
    simpl.
    reflexivity.
    (* Case 2: This function constructs this list exactly as specified.  *)
    intro Hext.
    erewrite insListCreate_rw; try eauto.
Qed.

End CListCreateTheorems.
