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

(* Extract an INS_CreateLinkedList. *)
Parameter extractInsCreateLinkedList :
    nat → Either ExtractionError unit.

Extract Constant extractInsCreateLinkedList =>
    "gen-create-linked-list".

(* Extract an INS_IsListPtrPresent. *)
Parameter extractInsIsListPtrPresent :
    nat → Either ExtractionError unit.

Extract Constant extractInsIsListPtrPresent =>
    "gen-cond-is-list-ptr-present".

(* Extract the beginning of an if statement. *)
Parameter extractInsBeginIfStatement : Either ExtractionError unit.

Extract Constant extractInsBeginIfStatement => "gen-begin-if-statement".

(* Extract the beginning of a then block. *)
Parameter extractInsBeginThenBlock : Either ExtractionError unit.

Extract Constant extractInsBeginThenBlock =>
    "gen-begin-then-block".

(* Extract the end of a then block. *)
Parameter extractInsEndThenBlock : Either ExtractionError unit.

Extract Constant extractInsEndThenBlock =>
    "gen-end-then-block".

(* Extract the beginning of an else block. *)
Parameter extractInsBeginElseBlock : Either ExtractionError unit.

Extract Constant extractInsBeginElseBlock =>
    "gen-begin-else-block".

(* Extract the end of an else block. *)
Parameter extractInsEndElseBlock : Either ExtractionError unit.

Extract Constant extractInsEndElseBlock =>
    "gen-end-else-block".

(* Extract an INS_AssignLocalListPtrToHeapListPtr. *)
Parameter extractInsAssignLocalListPtrToHeapListPtr :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListPtrToHeapListPtr =>
    "gen-assign-local-list-ptr-to-heap-list-ptr".

(* Extract an INS_AssignLocalListPtrPtrToListPtrParameter. *)
Parameter extractInsAssignLocalListPtrPtrToListPtrParameter :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListPtrPtrToListPtrParameter =>
    "gen-assign-local-list-ptr-ptr-to-list-ptr-parameter".

(* Extract an INS_AssignLocalListHeapPtrToLocalListPtr. *)
Parameter extractInsAssignLocalListHeapPtrToLocalListPtr :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListHeapPtrToLocalListPtr =>
    "gen-assign-local-list-heap-ptr-to-local-list-ptr".

(* Extract an INS_CheckHeapListPtrAddress. *)
Parameter extractInsCheckHeapListPtrAddress :
    nat → Either ExtractionError unit.

Extract Constant extractInsCheckHeapListPtrAddress =>
    "gen-check-heap-list-ptr-address".

(* Extract an INS_ReturnStatus. *)
Parameter extractInsReturnStatus :
    CStatusCode → Either ExtractionError unit.

Extract Constant extractInsReturnStatus =>
    "gen-return-status".

(* Extract an INS_Crash. *)
Parameter extractInsCrash :
    MachineErrorCode → Either ExtractionError unit.

Extract Constant extractInsCrash =>
    "gen-crash".

(* Extract the beginning of the list_create function. *)
Parameter extractInsBeginListCreateFunction : Either ExtractionError unit.

Extract Constant extractInsBeginListCreateFunction =>
    "gen-begin-list-create-function".
