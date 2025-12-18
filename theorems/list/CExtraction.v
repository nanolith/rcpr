Require Import RCPR.Data.Either.
Require Import RCPR.Data.Maybe.
Require Import RCPR.Data.Monad.
Require Import RCPR.Helpers.Notation.
Require Import list.CMachine.

From Corelib Require Extraction.

Import CMachine.
Import Either.
Import Maybe.
Import Monad.
Import Notation.

Module CExtraction.

(* List of extraction errors. *)
Inductive ExtractionError : Type :=
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
Parameter extractInsBeginIfStatement : unit → Either ExtractionError unit.

Extract Constant extractInsBeginIfStatement => "gen-begin-if-statement".

(* Extract the beginning of a then block. *)
Parameter extractInsBeginThenBlock : unit → Either ExtractionError unit.

Extract Constant extractInsBeginThenBlock =>
    "gen-begin-then-block".

(* Extract the end of a then block. *)
Parameter extractInsEndThenBlock : unit → Either ExtractionError unit.

Extract Constant extractInsEndThenBlock =>
    "gen-end-then-block".

(* Extract the beginning of an else block. *)
Parameter extractInsBeginElseBlock : unit → Either ExtractionError unit.

Extract Constant extractInsBeginElseBlock =>
    "gen-begin-else-block".

(* Extract the end of an else block. *)
Parameter extractInsEndElseBlock : unit → Either ExtractionError unit.

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

(* Extract an INS_IncrementListCount. *)
Parameter extractInsIncrementListCount :
    nat → Either ExtractionError unit.

Extract Constant extractInsIncrementListCount =>
    "gen-increment-list-count".

(* Extract an INS_DecrementListCount. *)
Parameter extractInsDecrementListCount :
    nat → Either ExtractionError unit.

Extract Constant extractInsDecrementListCount =>
    "gen-decrement-list-count".

(* Extract an INS_SetLinkedListHead. *)
Parameter extractInsSetLinkedListHead :
    nat → Maybe nat → Either ExtractionError unit.

Extract Constant extractInsSetLinkedListHead =>
    "gen-set-linked-list-head".

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

Definition ignoreParameter {A} (x : A) : Either ExtractionError unit :=
    ret tt.

(* Extract an if statement conditional instruction. *)
Definition extractInsCond (ins : CMachineInstruction)
        : Either ExtractionError unit :=
    match ins with
    | INS_CreateLocalLinkedListPtr addr next =>
        ignoreParameter addr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_CreateLocalLinkedListPtrPtr addr next =>
        ignoreParameter addr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_CreateLinkedList localAddr next =>
        ignoreParameter localAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_IsListPtrPresent localAddr =>
        extractInsIsListPtrPresent localAddr
    | INS_ITE cond thenHead elseHead =>
        ignoreParameter cond »
        ignoreParameter thenHead »
        ignoreParameter elseHead »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListPtrToHeapListPtr heapAddr localAddr next =>
        ignoreParameter heapAddr »
        ignoreParameter localAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListPtrPtrToListPtrParameter heapAddr localAddr next =>
        ignoreParameter heapAddr »
        ignoreParameter localAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListHeapPtrToLocalListPtr localHeapAddr localAddr next =>
        ignoreParameter localHeapAddr »
        ignoreParameter localAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_IncrementListCount localAddr next =>
        ignoreParameter localAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_DecrementListCount localAddr next =>
        ignoreParameter localAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_SetLinkedListHead localAddr headAddr next =>
        ignoreParameter localAddr »
        ignoreParameter headAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_CheckHeapListPtrAddress heapAddr next =>
        ignoreParameter heapAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_ReturnStatus code =>
        ignoreParameter code »
        Left ExtractionErrorGeneral
    | INS_Crash e =>
        ignoreParameter e »
        Left ExtractionErrorGeneral
    end.

(* Extract instructions. *)
Fixpoint extractInstructions (ins : CMachineInstruction)
        : Either ExtractionError unit :=
    match ins with
    | INS_CreateLocalLinkedListPtr addr next =>
        extractInsCreateLocalLinkedListPtr addr »
        extractInstructions next
    | INS_CreateLocalLinkedListPtrPtr addr next =>
        extractInsCreateLocalLinkedListPtrPtr addr »
        extractInstructions next
    | INS_CreateLinkedList localAddr next =>
        extractInsCreateLinkedList localAddr »
        extractInstructions next
    | INS_IsListPtrPresent localAddr => Left ExtractionErrorGeneral
    | INS_ITE cond thenHead elseHead =>
        extractInsBeginIfStatement tt »
        extractInsCond cond »
        extractInsBeginThenBlock tt »
        extractInstructions thenHead »
        extractInsEndThenBlock tt »
        extractInsBeginElseBlock tt »
        extractInstructions elseHead »
        extractInsEndElseBlock tt
    | INS_AssignLocalListPtrToHeapListPtr heapAddr localAddr next =>
        extractInsAssignLocalListPtrToHeapListPtr heapAddr localAddr »
        extractInstructions next
    | INS_AssignLocalListPtrPtrToListPtrParameter heapAddr localAddr next =>
        extractInsAssignLocalListPtrPtrToListPtrParameter heapAddr localAddr »
        extractInstructions next
    | INS_AssignLocalListHeapPtrToLocalListPtr localHeapAddr localAddr next =>
        extractInsAssignLocalListHeapPtrToLocalListPtr localHeapAddr localAddr »
        extractInstructions next
    | INS_IncrementListCount localAddr next =>
        extractInsIncrementListCount localAddr »
        extractInstructions next
    | INS_DecrementListCount localAddr next =>
        extractInsDecrementListCount localAddr »
        extractInstructions next
    | INS_SetLinkedListHead localAddr headAddr next =>
        extractInsSetLinkedListHead localAddr headAddr »
        extractInstructions next
    | INS_CheckHeapListPtrAddress heapAddr next =>
        extractInsCheckHeapListPtrAddress heapAddr »
        extractInstructions next
    | INS_ReturnStatus code =>
        extractInsReturnStatus code
    | INS_Crash e =>
        extractInsCrash e
    end.

End CExtraction.
