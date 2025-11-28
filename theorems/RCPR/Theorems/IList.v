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

(* Show that we can re-arrange cons and append operations. *)
Lemma IList_cons_append_associativity :
    ∀ {A} (a x : A) (l : IList A),
        (a :: l) ++ [x] = a :: (l ++ [x]).
Proof.
    intros A a x l.
    simpl.
    reflexivity.
Qed.

End IList.
