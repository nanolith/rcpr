Module Maybe.

(* The Maybe inductive type describes an optional value. *)
Inductive Maybe (A : Type) : Type :=
    | Just : A -> Maybe A
    | Nothing : Maybe A.

(* The implicit type A maps to the type of the Just parameter. *)
Arguments Just {A} a.
(* Gather the type A parameter from implicit context. *)
Arguments Nothing {A}.

End Maybe.
