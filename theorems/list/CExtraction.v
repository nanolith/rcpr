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

(* Extract an INS_IsListNodePtrPresent. *)
Parameter extractInsIsListNodePtrPresent :
    nat → Either ExtractionError unit.

Extract Constant extractInsIsListNodePtrPresent =>
    "gen-cond-is-list-node-ptr-present".

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

(* Extract an INS_AssignLocalListNodePtrToListNodePtrParameter. *)
Parameter extractInsAssignLocalListNodePtrToListNodePtrParameter :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListNodePtrToListNodePtrParameter =>
    "gen-assign-local-list-node-ptr-to-list-node-ptr-parameter".

(* Extract an INS_AssignLocalListPtrToListPtrParameter. *)
Parameter extractInsAssignLocalListPtrToListPtrParameter :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListPtrToListPtrParameter =>
    "gen-assign-local-list-ptr-to-list-ptr-parameter".

(* Extract an INS_AssignLocalListHeapPtrToLocalListPtr. *)
Parameter extractInsAssignLocalListHeapPtrToLocalListPtr :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListHeapPtrToLocalListPtr =>
    "gen-assign-local-list-heap-ptr-to-local-list-ptr".

(* Extract an INS_AssignLocalListNodePtrToHeapListNodePtr. *)
Parameter extractInsAssignLocalListNodePtrToHeapListNodePtr :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListNodePtrToHeapListNodePtr =>
    "gen-assign-local-list-node-ptr-to-heap-list-node-ptr".

(* Extract an INS_AssignLocalListNodePtrToHeapListHead. *)
Parameter extractInsAssignLocalListNodePtrToHeapListHead :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListNodePtrToHeapListHead =>
    "gen-assign-local-list-node-ptr-to-heap-list-head".

(* Extract an INS_AssignLocalListNodePtrToHeapListTail. *)
Parameter extractInsAssignLocalListNodePtrToHeapListTail :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListNodePtrToHeapListTail =>
    "gen-assign-local-list-node-ptr-to-heap-list-tail".

(* Extract an INS_AssignLocalListNodePtrToLocalListPtrHead. *)
Parameter extractInsAssignLocalListNodePtrToLocalListPtrHead :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListNodePtrToLocalListPtrHead =>
    "gen-assign-local-list-node-ptr-to-local-list-ptr-head".

(* Extract an INS_AssignLocalListNodePtrToLocalListPtrTail. *)
Parameter extractInsAssignLocalListNodePtrToLocalListPtrTail :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListNodePtrToLocalListPtrTail =>
    "gen-assign-local-list-node-ptr-to-local-list-ptr-tail".

(* Extract an INS_AssignLocalListNodePtrToHeapListNodeNext. *)
Parameter extractInsAssignLocalListNodePtrToHeapListNodeNext :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListNodePtrToHeapListNodeNext =>
    "gen-assign-local-list-node-ptr-to-heap-list-node-next".

(* Extract an INS_AssignLocalListNodePtrToHeapListNodePrev. *)
Parameter extractInsAssignLocalListNodePtrToHeapListNodePrev :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListNodePtrToHeapListNodePrev =>
    "gen-assign-local-list-node-ptr-to-heap-list-node-prev".

(* Extract an INS_AssignLocalListNodePtrToLocalListNodePtrNext. *)
Parameter extractInsAssignLocalListNodePtrToLocalListNodePtrNext :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListNodePtrToLocalListNodePtrNext =>
    "gen-assign-local-list-node-ptr-to-local-list-node-ptr-next".

(* Extract an INS_AssignLocalListNodePtrToLocalListNodePtrPrev. *)
Parameter extractInsAssignLocalListNodePtrToLocalListNodePtrPrev :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsAssignLocalListNodePtrToLocalListNodePtrPrev =>
    "gen-assign-local-list-node-ptr-to-local-list-node-ptr-prev".

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

(* Extract an INS_SetLinkedListTail. *)
Parameter extractInsSetLinkedListTail :
    nat → Maybe nat → Either ExtractionError unit.

Extract Constant extractInsSetLinkedListTail =>
    "gen-set-linked-list-tail".

(* Extract an INS_SetListNodeNext. *)
Parameter extractInsSetListNodeNext :
    nat → Maybe nat → Either ExtractionError unit.

Extract Constant extractInsSetListNodeNext =>
    "gen-set-list-node-next".

(* Extract an INS_SetListNodePrev. *)
Parameter extractInsSetListNodePrev :
    nat → Maybe nat → Either ExtractionError unit.

Extract Constant extractInsSetListNodePrev =>
    "gen-set-list-node-prev".

(* Extract an INS_SetLocalListHead. *)
Parameter extractInsSetLocalListHead :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsSetLocalListHead =>
    "gen-set-local-list-head".

(* Extract an INS_SetLocalListTail. *)
Parameter extractInsSetLocalListTail :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsSetLocalListTail =>
    "gen-set-local-list-tail".

(* Extract an INS_SetLocalListNodeNext. *)
Parameter extractInsSetLocalListNodeNext :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsSetLocalListNodeNext =>
    "gen-set-local-list-node-next".

(* Extract an INS_SetLocalListNodePrev. *)
Parameter extractInsSetLocalListNodePrev :
    nat → nat → Either ExtractionError unit.

Extract Constant extractInsSetLocalListNodePrev =>
    "gen-set-local-list-node-prev".

(* Extract an INS_SetLocalListHeadNull. *)
Parameter extractInsSetLocalListHeadNull :
    nat → Either ExtractionError unit.

Extract Constant extractInsSetLocalListHeadNull =>
    "gen-set-local-list-head-null".

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
    | INS_IsListNodePtrPresent localAddr =>
        extractInsIsListNodePtrPresent localAddr
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
    | INS_AssignLocalListNodePtrToListNodePtrParameter
            heapAddr localAddr next =>
        ignoreParameter heapAddr »
        ignoreParameter localAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListPtrToListPtrParameter
            offset localAddr next =>
        ignoreParameter offset »
        ignoreParameter localAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListHeapPtrToLocalListPtr localHeapAddr localAddr next =>
        ignoreParameter localHeapAddr »
        ignoreParameter localAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListNodePtrToHeapListNodePtr localAddr heapAddr next =>
        ignoreParameter localAddr »
        ignoreParameter heapAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListNodePtrToHeapListHead localAddr heapAddr next =>
        ignoreParameter localAddr »
        ignoreParameter heapAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListNodePtrToHeapListTail localAddr heapAddr next =>
        ignoreParameter localAddr »
        ignoreParameter heapAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListNodePtrToLocalListPtrHead localAddr listAddr next =>
        ignoreParameter localAddr »
        ignoreParameter listAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListNodePtrToLocalListPtrTail localAddr listAddr next =>
        ignoreParameter localAddr »
        ignoreParameter listAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListNodePtrToHeapListNodeNext localAddr heapAddr next =>
        ignoreParameter localAddr »
        ignoreParameter heapAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListNodePtrToHeapListNodePrev localAddr heapAddr next =>
        ignoreParameter localAddr »
        ignoreParameter heapAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListNodePtrToLocalListNodePtrNext
            localAddr nodeAddr next =>
        ignoreParameter localAddr »
        ignoreParameter nodeAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_AssignLocalListNodePtrToLocalListNodePtrPrev
            localAddr nodeAddr next =>
        ignoreParameter localAddr »
        ignoreParameter nodeAddr »
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
    | INS_SetLinkedListTail localAddr tailAddr next =>
        ignoreParameter localAddr »
        ignoreParameter tailAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_SetListNodeNext localAddr nextAddr next =>
        ignoreParameter localAddr »
        ignoreParameter nextAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_SetListNodePrev localAddr prevAddr next =>
        ignoreParameter localAddr »
        ignoreParameter prevAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_SetLocalListHead localAddr localNodeAddr next =>
        ignoreParameter localAddr »
        ignoreParameter localNodeAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_SetLocalListTail localAddr localNodeAddr next =>
        ignoreParameter localAddr »
        ignoreParameter localNodeAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_SetLocalListNodeNext localAddr localNodeAddr next =>
        ignoreParameter localAddr »
        ignoreParameter localNodeAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_SetLocalListNodePrev localAddr localNodeAddr next =>
        ignoreParameter localAddr »
        ignoreParameter localNodeAddr »
        ignoreParameter next »
        Left ExtractionErrorGeneral
    | INS_SetLocalListHeadNull localAddr next =>
        ignoreParameter localAddr »
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
    | INS_IsListNodePtrPresent localAddr => Left ExtractionErrorGeneral
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
    | INS_AssignLocalListNodePtrToListNodePtrParameter
            heapAddr localAddr next =>
        extractInsAssignLocalListNodePtrToListNodePtrParameter
            heapAddr localAddr »
        extractInstructions next
    | INS_AssignLocalListPtrToListPtrParameter
            offset localAddr next =>
        extractInsAssignLocalListPtrToListPtrParameter offset localAddr »
        extractInstructions next
    | INS_AssignLocalListHeapPtrToLocalListPtr localHeapAddr localAddr next =>
        extractInsAssignLocalListHeapPtrToLocalListPtr localHeapAddr localAddr »
        extractInstructions next
    | INS_AssignLocalListNodePtrToHeapListNodePtr localAddr heapAddr next =>
        extractInsAssignLocalListNodePtrToHeapListNodePtr localAddr heapAddr »
        extractInstructions next
    | INS_AssignLocalListNodePtrToHeapListHead localAddr heapAddr next =>
        extractInsAssignLocalListNodePtrToHeapListHead localAddr heapAddr »
        extractInstructions next
    | INS_AssignLocalListNodePtrToHeapListTail localAddr heapAddr next =>
        extractInsAssignLocalListNodePtrToHeapListTail localAddr heapAddr »
        extractInstructions next
    | INS_AssignLocalListNodePtrToLocalListPtrHead localAddr listAddr next =>
        extractInsAssignLocalListNodePtrToLocalListPtrHead localAddr listAddr »
        extractInstructions next
    | INS_AssignLocalListNodePtrToLocalListPtrTail localAddr listAddr next =>
        extractInsAssignLocalListNodePtrToLocalListPtrTail localAddr listAddr »
        extractInstructions next
    | INS_AssignLocalListNodePtrToHeapListNodeNext localAddr heapAddr next =>
        extractInsAssignLocalListNodePtrToHeapListNodeNext localAddr heapAddr »
        extractInstructions next
    | INS_AssignLocalListNodePtrToHeapListNodePrev localAddr heapAddr next =>
        extractInsAssignLocalListNodePtrToHeapListNodePrev localAddr heapAddr »
        extractInstructions next
    | INS_AssignLocalListNodePtrToLocalListNodePtrNext
            localAddr nodeAddr next =>
        extractInsAssignLocalListNodePtrToLocalListNodePtrNext
            localAddr nodeAddr »
        extractInstructions next
    | INS_AssignLocalListNodePtrToLocalListNodePtrPrev
            localAddr nodeAddr next =>
        extractInsAssignLocalListNodePtrToLocalListNodePtrPrev
            localAddr nodeAddr »
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
    | INS_SetLinkedListTail localAddr tailAddr next =>
        extractInsSetLinkedListTail localAddr tailAddr »
        extractInstructions next
    | INS_SetListNodeNext localAddr nextAddr next =>
        extractInsSetListNodeNext localAddr nextAddr »
        extractInstructions next
    | INS_SetListNodePrev localAddr prevAddr next =>
        extractInsSetListNodePrev localAddr prevAddr »
        extractInstructions next
    | INS_SetLocalListHead localAddr localNodeAddr next =>
        extractInsSetLocalListHead localAddr localNodeAddr »
        extractInstructions next
    | INS_SetLocalListTail localAddr localNodeAddr next =>
        extractInsSetLocalListTail localAddr localNodeAddr »
        extractInstructions next
    | INS_SetLocalListNodeNext localAddr localNodeAddr next =>
        extractInsSetLocalListNodeNext localAddr localNodeAddr »
        extractInstructions next
    | INS_SetLocalListNodePrev localAddr localNodeAddr next =>
        extractInsSetLocalListNodePrev localAddr localNodeAddr »
        extractInstructions next
    | INS_SetLocalListHeadNull localAddr next =>
        extractInsSetLocalListHeadNull localAddr »
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
