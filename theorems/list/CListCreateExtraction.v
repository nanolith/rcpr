Require Import RCPR.Data.Either.
Require Import RCPR.Data.Monad.
Require Import RCPR.Helpers.Notation.
Require Import list.CMachine.
Require Import list.CExtraction.

From Corelib Require Extraction.

Import CExtraction.
Import CMachine.
Import Either.
Import Monad.
Import Notation.

Extraction Language Scheme.

(* Extract the list_create function. *)
Definition extractListCreateFunction : Either ExtractionError unit :=
    extractInsBeginListCreateFunction tt »
    extractInstructions insListCreate »
    extractInsEndListCreateFunction tt.

(* Perform the extraction to Scheme. *)
Extraction "list_create.generated.scm" extractListCreateFunction.
