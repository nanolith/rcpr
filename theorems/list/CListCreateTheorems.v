Require Import RCPR.Data.IList.
Require Import RCPR.Data.Maybe.
Require Import RCPR.Data.Monad.
Require Import RCPR.Helpers.Notation.
Require Import RCPR.Theorems.IListTheorems.
Require Import list.CMachine.
Require Import list.CMachineTheorems.

Import CMachine.
Import CMachineTheorems.
Import IList.
Import IListTheorems.
Import Maybe.
Import Monad.
Import Notation.

Module CListCreateTheorems.

Open Scope monad_scope.

(* If linked list allocation fails, cListCreate returns an error code. *)
Lemma cListCreate_OutOfMemory :
    ∀ (n index : nat) (ol nl : CLocal) (h : CHeap) (listPtr : nat)
      (ptr : Maybe nat) (values : IList CMemoryLocation),
        ol = CLocalState index values →
        nl = CLocalState (index + 1)
                         (values ++ [CMemListPtr (index + 1) Nothing]) →
        loadLinkedListPtr listPtr n nl h = MachineState n nl h ptr →
        maybeCreateLinkedList n nl h = MachineState n nl h Nothing →
        cListCreate listPtr n ol h = MachineState n nl h ErrorOutOfMemory.
Proof.
    intros.
    rewrite H.
    unfold cListCreate.
    unfold createLocalLinkedListPtr.
    unfold localCreate.
    unfold getLocal.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H0 in H1.
    rewrite H0 in H2.
    rewrite H1.
    rewrite H2.
    rewrite H0.
    reflexivity.
Qed.

(* Happy path: cListCreate creates a new list. *)
(* Lemma cListCreate_rw :
    ∀ (n index : nat) (ol nl1 nl2 : CLocal) (addr : nat) (oh nh : CHeap)
      (ovals nvals : IList CMemoryLocation) (listPtr : nat)
      (ptr : Maybe nat),
        ol = CLocalState index [] →
        nl1 = CLocalState (index + 1)
                          [CMemListPtr (index + 1) Nothing] →
        nl2 = CLocalState (index + 1)
                          [CMemListPtr (index + 1) (Just (addr + 1))] →
        oh = CHeapState addr ovals →
        nh = CHeapState (addr + 1) nvals →
        ovals = [CMemListPtr listPtr Nothing] →
        nvals = [CMemListPtr listPtr (Just (addr + 1));
                 CMemList (addr + 1) (List Nothing Nothing 0)] →
        cListCreate listPtr n ol oh = MachineState n nl2 nh StatusSuccess.
Proof.
    intros.
    rewrite H.
    unfold cListCreate.
    unfold createLocalLinkedListPtr.
    unfold localCreate.
    unfold getLocal.
    unfold bind, MachineMMonad.
    simpl.
    unfold loadLinkedListPtr.
    unfold loadRaw.
    unfold getHeapMemory.
    unfold getHeap.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H2.
    rewrite H4.
    simpl.
    rewrite nat_eqb_refl.
    simpl.
    unfold storeLocalLinkedListPtr.
    unfold loadLocalLinkedListPtr.
    unfold loadLocalRaw.
    unfold getLocalMemory.
    unfold getLocal.
    unfold memReplace.
    unfold memReplaceLoop.
    unfold locAddr.
    unfold bind, MachineMMonad.
    simpl.
    rewrite nat_eqb_refl.
    rewrite H1.
    simpl.
    rewrite nat_eqb_refl.
    simpl.
    unfold storeLinkedListPtr.
    unfold getHeapMemory.
    unfold getHeap.
    unfold loadLinkedListPtr.
    unfold loadRaw.
    unfold getHeapMemory.
    unfold getHeap.
    unfold bind, MachineMMonad.
    simpl.
    unfold locAddr.
    simpl.
    rewrite nat_eqb_refl.
    simpl.
    unfold memReplace.
    unfold memReplaceLoop.
    unfold locAddr.
    rewrite nat_eqb_refl.
    simpl.
    rewrite H3.
    rewrite H5.
    reflexivity.
Qed. *)

(* The list created by cListCreate is empty. *)
(* Lemma cListCreate_extract_empty :
    ∀ (n : nat) (l : CLocal) (addr : nat) (oh nh : CHeap)
      (ovals nvals : IList CMemoryLocation) (listPtr : nat) (ptr : Maybe nat),
        oh = CHeapState addr ovals →
        nh = CHeapState (addr + 1) nvals →
        ovals = [CMemListPtr listPtr Nothing] →
        nvals = [CMemListPtr listPtr (Just (addr + 1));
                 CMemList (addr + 1) (List Nothing Nothing 0)] →
        Nat.eqb listPtr (addr + 1) = false →
        cListCreate listPtr n l oh = MachineState n l nh StatusSuccess →
        extractListFromC (addr + 1) n l nh = MachineState n l nh [].
Proof.
    intros.
    rewrite (cListCreate_rw n l addr oh nh ovals nvals listPtr ptr) in H4;
        try assumption.
    unfold extractListFromC.
    unfold loadLinkedList.
    unfold loadRaw.
    unfold getHeapMemory.
    unfold getHeap.
    unfold lookupMem.
    unfold locAddr.
    rewrite H0.
    rewrite H2.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H3.
    rewrite nat_eqb_refl.
    unfold extractList.
    unfold reverse.
    simpl.
    reflexivity.
Qed. *)

(* The reverse list created by cListCreate is empty. *)
(* Lemma cListCreate_extractReverse_empty :
    ∀ (n : nat) (l : CLocal) (addr : nat) (oh nh : CHeap)
      (ovals nvals : IList CMemoryLocation) (listPtr : nat) (ptr : Maybe nat),
        oh = CHeapState addr ovals →
        nh = CHeapState (addr + 1) nvals →
        ovals = [CMemListPtr listPtr Nothing] →
        nvals = [CMemListPtr listPtr (Just (addr + 1));
                 CMemList (addr + 1) (List Nothing Nothing 0)] →
        Nat.eqb listPtr (addr + 1) = false →
        cListCreate listPtr n l oh = MachineState n l nh StatusSuccess →
        extractReverseListFromC (addr + 1) n l nh = MachineState n l nh [].
Proof.
    intros.
    rewrite (cListCreate_rw n l addr oh nh ovals nvals listPtr ptr) in H4;
        try assumption.
    unfold extractReverseListFromC.
    unfold loadLinkedList.
    unfold loadRaw.
    unfold getHeapMemory.
    unfold getHeap.
    unfold lookupMem.
    unfold locAddr.
    rewrite H0.
    rewrite H2.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H3.
    rewrite nat_eqb_refl.
    unfold extractReverseList.
    unfold reverse.
    simpl.
    reflexivity.
Qed. *)

End CListCreateTheorems.
