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

(* If linked list allocation fails, cListCreate returns an error code. *)
(* Lemma cListCreate_OutOfMemory :
    ∀ (n index : nat) (ol nl : CLocal) (h : CHeap) (listPtr : nat)
      (ptr : Maybe nat),
        ol = CLocalState index [] →
        nl = CLocalState (index + 1)
                         [CMemListPtr (index + 1) Nothing] →
        loadLinkedListPtr listPtr n nl h = MachineState n nl h ptr →
        maybeCreateLinkedList n nl h = MachineState n nl h Nothing →
        cListCreate listPtr n ol h = MachineState n nl h ErrorOutOfMemory.
Proof.
    intros.
    unfold cListCreate.
    unfold bind, MachineMMonad.
    rewrite (createLocalLinkedListPtr_rw n index h ol nl Nothing);
        try assumption.
    simpl.
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed. *)

(* Happy path: cListCreate creates a new list. *)
(* Lemma cListCreate_rw :
    ∀ (n index : nat) (ol nl1 nl2 : CLocal) (addr : nat) (oh nh1 nh2 : CHeap)
      (ovals nvals1 nvals2 : IList CMemoryLocation) (listPtr : nat)
      (ptr : Maybe nat),
        ol = CLocalState index [] →
        nl1 = CLocalState (index + 1)
                          [CMemListPtr (index + 1) Nothing] →
        nl2 = CLocalState (index + 1)
                          [CMemListPtr (index + 1) (Just (addr + 1))] →
        oh = CHeapState addr ovals →
        nh1 = CHeapState (addr + 1) nvals1 →
        nh2 = CHeapState (addr + 1) nvals2 →
        ovals = [CMemListPtr listPtr Nothing] →
        nvals1 = [CMemListPtr listPtr Nothing;
                 CMemList (addr + 1) (List Nothing Nothing 0)] →
        nvals2 = [CMemListPtr listPtr (Just (addr + 1));
                 CMemList (addr + 1) (List Nothing Nothing 0)] →
        Nat.eqb listPtr (addr + 1) = false →
        cListCreate listPtr n ol oh = MachineState n nl2 nh2 StatusSuccess.
Proof.
    intros.
    unfold cListCreate.
    unfold bind, MachineMMonad.
    rewrite (createLocalLinkedListPtr_rw n index oh ol nl1 Nothing);
        try assumption.
    rewrite (loadLinkedListPtr_rw n nl1 oh listPtr Nothing); try assumption.
    (* TODO: write lemma for loadRaw. *)
    2: {
        unfold loadRaw.
        unfold getHeapMemory.
        unfold getHeap.
        rewrite H2.
        rewrite H5.
        unfold bind, MachineMMonad.
        simpl.
        rewrite nat_eqb_refl.
        reflexivity.
    }
    simpl.
    rewrite (maybeCreateLinkedList_rw n addr oh nh1 nl1 Nothing ovals);
        try assumption.
    2: {
        rewrite H5.
        simpl.
        rewrite <- H6.
        assumption.
    }
    rewrite (storeLocalLinkedListPtr_rw
                n (index + 1) nh1 nl1 nl2 Nothing (Just (addr + 1)));
        try assumption.
    rewrite(loadLocalLinkedListPtr_rw n (index + 1) nh1 nl2 (Just (addr + 1)));
        try assumption.
    rewrite (storeLinkedListPtr_simpl n (addr + 1) listPtr nl2 nh1 nh2
                Nothing (Just (addr + 1))
                (CMemList (addr + 1) (List Nothing Nothing 0)) nvals1 nvals2);
        try assumption.
    reflexivity.
Qed. *)

(* The list created by cListCreate is empty. *)
(* Lemma cListCreate_extract_empty :
    ∀ (n : nat) (l nl1 nl2 : CLocal) (addr : nat) (oh nh1 nh2 : CHeap)
      (ovals nvals1 nvals2 : IList CMemoryLocation) (listPtr : nat)
      (ptr : Maybe nat),
        l = CLocalState addr [] →
        nl1 = CLocalState (addr + 1) [CMemListPtr (addr + 1) Nothing] →
        nl2 = CLocalState (addr + 1)
                          [CMemListPtr (addr + 1) (Just (addr + 1))] →
        oh = CHeapState addr ovals →
        nh1 = CHeapState (addr + 1) nvals1 →
        nh2 = CHeapState (addr + 1) nvals2 →
        ovals = [CMemListPtr listPtr Nothing] →
        nvals1 = [CMemListPtr listPtr Nothing;
                 CMemList (addr + 1) (List Nothing Nothing 0)] →
        nvals2 = [CMemListPtr listPtr (Just (addr + 1));
                 CMemList (addr + 1) (List Nothing Nothing 0)] →
        Nat.eqb listPtr (addr + 1) = false →
        cListCreate listPtr n l oh = MachineState n nl2 nh2 StatusSuccess →
        extractListFromC (addr + 1) n nl2 nh2 = MachineState n nl2 nh2 [].
Proof.
    intros.
    rewrite (cListCreate_rw n addr l nl1 nl2 addr oh nh1 nh2 ovals nvals1
             nvals2 listPtr ptr) in H9;
        try assumption.
    unfold extractListFromC.
    unfold loadLinkedList.
    unfold loadRaw.
    unfold getHeapMemory.
    unfold getHeap.
    unfold lookupMem.
    unfold locAddr.
    rewrite H4.
    rewrite H7.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H8.
    rewrite nat_eqb_refl.
    unfold extractList.
    unfold reverse.
    simpl.
    reflexivity.
Qed. *)

(* The reverse list created by cListCreate is empty. *)
(* Lemma cListCreate_extractReverse_empty :
    ∀ (n : nat) (l nl1 nl2 : CLocal) (addr : nat) (oh nh1 nh2 : CHeap)
      (ovals nvals1 nvals2 : IList CMemoryLocation) (listPtr : nat)
      (ptr : Maybe nat),
        l = CLocalState addr [] →
        nl1 = CLocalState (addr + 1) [CMemListPtr (addr + 1) Nothing] →
        nl2 = CLocalState (addr + 1)
                          [CMemListPtr (addr + 1) (Just (addr + 1))] →
        oh = CHeapState addr ovals →
        nh1 = CHeapState (addr + 1) nvals1 →
        nh2 = CHeapState (addr + 1) nvals2 →
        ovals = [CMemListPtr listPtr Nothing] →
        nvals1 = [CMemListPtr listPtr Nothing;
                 CMemList (addr + 1) (List Nothing Nothing 0)] →
        nvals2 = [CMemListPtr listPtr (Just (addr + 1));
                 CMemList (addr + 1) (List Nothing Nothing 0)] →
        Nat.eqb listPtr (addr + 1) = false →
        cListCreate listPtr n l oh = MachineState n nl2 nh2 StatusSuccess →
        extractReverseListFromC (addr + 1) n nl2 nh2 =
            MachineState n nl2 nh2 [].
Proof.
    intros.
    rewrite (cListCreate_rw n addr l nl1 nl2 addr oh nh1 nh2 ovals nvals1
             nvals2 listPtr ptr) in H9;
        try assumption.
    unfold extractReverseListFromC.
    unfold loadLinkedList.
    unfold loadRaw.
    unfold getHeapMemory.
    unfold getHeap.
    unfold lookupMem.
    unfold locAddr.
    rewrite H4.
    rewrite H7.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H8.
    rewrite nat_eqb_refl.
    unfold extractReverseList.
    unfold reverse.
    simpl.
    reflexivity.
Qed. *)

(* This function terminates and is correct (will cause a machine error),
   for any input, given that the provided preconditions are met. *)
Lemma insListCreate_total_correctness :
    ∀ (n index : nat) (l l2 l3 : CLocal) (h h2 : CHeap),
    l = CLocalState 0 [] →
    l2 = CLocalState 2 [CMemListPtrPtr 1 Nothing; CMemListPtr 2 Nothing] →
    l3 = CLocalState 2 [CMemListPtrPtr 1 (Just index); CMemListPtr 2 Nothing] →
    h = CHeapState index [CMemListPtr index Nothing] →
    h2 = CHeapState index [CMemListPtr index Nothing] →
    getLinkedListPtrParameter 1 n l2 h = MachineState n l2 h (Just index) →
    (maybeCreateLinkedList n l3 h = MachineState n l3 h Nothing
        \/ maybeCreateLinkedList n l3 h = maybeCreateLinkedList' n l3 h) →
    ∃ (n' : nat) (l' : CLocal) (h' : CHeap) (c' : CStatusCode),
    eval insListCreate n l h = MachineState n' l' h' c'.
Proof.
    intros.
    unfold insListCreate.
    rewrite H.
    unfold eval.
    unfold evalCreateLocalLinkedListPtrPtr.
    unfold createLocalLinkedListPtrPtr.
    unfold localCreate.
    unfold putLocal.
    unfold getLocal.
    unfold bind, MachineMMonad.
    simpl.
    unfold evalAssignLocalListPtrPtrToListPtrParameter.
    unfold bind, MachineMMonad.
    rewrite H0 in H4.
    rewrite H4.
    simpl.
    unfold evalCreateLinkedList.
    unfold bind, MachineMMonad.
    rewrite H2.
    rewrite H1 in H5.
    rewrite H2 in H5.
    destruct H5 as [H_fail | H_success].
    1: {
        rewrite H_fail.
        simpl.
        eauto.
    }
    rewrite H_success.
    simpl.
    unfold evalAssignLocalListHeapPointerToLocalListPtr.
    unfold loadLocalLinkedListPtrPtr.
    unfold loadLocalRaw.
    unfold getLocalMemory.
    unfold getLocal.
    unfold bind, MachineMMonad.
    simpl.
    erewrite storeLinkedListPtr_simpl.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
Qed.

End CListCreateTheorems.
