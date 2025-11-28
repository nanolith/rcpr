Require Import RCPR.Data.IList.
Require Import RCPR.Helpers.Notation.

Import IList.
Import Notation.

Module IList.

(* We can peel the first item to the end of a reversed list. *)
Lemma IList_reverse_peel :
    ∀ {A} (x : A) (l : IList A),
        reverse (x :: l) = (reverse l) ++ [x].
Proof.
    intros A x l.
    unfold reverse.
    reflexivity.
Qed.

End IList.
