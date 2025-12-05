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

End CMachineLoadTheorems.
