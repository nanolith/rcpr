Require Import RCPR.Data.Either.
Require Import RCPR.Data.Monad.
Require Import RCPR.Helpers.Notation.
Require Import list.CMachine.

From Corelib Require Extraction.

Import CMachine.
Import Either.
Import Monad.
Import Notation.

Extraction Language Scheme.

(* List of extraction errors. *)
Inductive ExtractionError :=
| ExtractionErrorGeneral.

(* Extract an INS_CreateLocalLinkedListPtr. *)
Parameter extractInsCreateLocalLinkedListPtr :
    nat → Either ExtractionError unit.

Extract Constant extractInsCreateLocalLinkedListPtr =>
    "gen-create-local-linked-list-ptr".

(* Extract an INS_CreateLocalLinkedListPtrPtr. *)
Parameter extractInsCreateLocalLinkedListPtrPtr :
    nat → Either ExtractionError unit.

Extract Constant extractInsCreateLocalLinkedListPtrPtr =>
    "gen-create-local-linked-list-ptr-ptr".
