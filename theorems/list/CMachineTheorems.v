Require Import RCPR.Data.Monad.
Require Import RCPR.Helpers.Notation.
Require Import list.CMachine.

Import CMachine.
Import Monad.
Import Notation.

Module CMachineTheorems.

(* Verify that if a location fails to load, it can't be cast to a node. *)
Lemma loadLinkedListNode_MachineErrorLoad :
    ∀ (n : nat) (l : CLocal) (h : CHeap) (addr : nat),
            loadRaw addr n l h = MachineError MachineErrorLoad →
            loadLinkedListNode addr n l h = MachineError MachineErrorLoad.
Proof.
    intros n l h addr H.
    unfold loadLinkedListNode.
    unfold bind, MachineMMonad.
    simpl.
    rewrite H.
    reflexivity.
Qed.

End CMachineTheorems.
