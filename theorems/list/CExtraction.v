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

Inductive ExtractionError :=
| ExtractionErrorGeneral.
