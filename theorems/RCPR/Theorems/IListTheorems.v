Require Import RCPR.Data.IList.
Require Import RCPR.Helpers.Notation.

Import IList.
Import Notation.

Module IListTheorems.

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

(* Peel the reverse of a list append. *)
Lemma IList_reverse_peel2 :
    ∀ {A} (x : A) (l : IList A),
        reverse (l ++ [x]) = x :: reverse l.
Proof.
    intros A x l.
    induction l.
    simpl.
    reflexivity.
    rewrite IList_cons_append_associativity.
    rewrite IList_reverse_peel.
    rewrite IList_reverse_peel.
    rewrite IHl.
    rewrite IList_cons_append_associativity.
    reflexivity.
Qed.

(* Prove the classic double reverse. *)
Lemma IList_reverse_reverse :
    ∀ (A : Type) (l : IList A),
        reverse (reverse l) = l.
Proof.
    intros A l.
    induction l.
    simpl.
    reflexivity.
    rewrite IList_reverse_peel.
    rewrite IList_reverse_peel2.
    rewrite IHl.
    reflexivity.
Qed.

(* Helper for the even proof. *)
Inductive even : nat → Prop :=
| ev_0 : even 0
| ev_SS {n : nat} : even n → even (S (S n)).

(* Helper list for the below proof. *)
Definition even_list : IList nat := 2 :: 4 :: 6 :: nil.

(* Proof that even_list satisfies a Forall predicate. *)
Lemma even_list_using_Forall :
    Forall even even_list.
Proof.
    unfold even_list.
    apply Forall_cons.  apply ev_SS.  apply ev_0.
    apply Forall_cons.  apply ev_SS.  apply ev_SS.  apply ev_0.
    apply Forall_cons.  apply ev_SS.  apply ev_SS.  apply ev_SS.  apply ev_0.
    apply Forall_nil.
Qed.

End IListTheorems.
