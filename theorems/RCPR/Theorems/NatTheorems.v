Require Import RCPR.Helpers.Notation.

Import Notation.

Module NatTheorems.

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

(* Helper lemma for nat inequality 1. *)
Lemma nat_eqb_oneoff :
    ∀ (x :  nat),
        Nat.eqb x (x + 1) = false.
Proof.
    induction x.
    simpl.
    reflexivity.
    simpl.
    rewrite IHx.
    reflexivity.
Qed.

End NatTheorems.
