#include <rcpr/model_assert.h>
#include <string.h>

#include "../../../src/fiber/common/fiber_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_fiber_internal;
RCPR_IMPORT_resource;

/* forward decls. */
RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(fiber);

status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_create_for_thread)(
    fiber** fib, fiber_scheduler* sched, allocator* a)
{
    fiber* tmp;
    status retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    RCPR_MODEL_ASSERT(NULL != fib);

    /* attempt to allocate memory for this fiber. */
    tmp = malloc(sizeof(fiber));
    if (NULL == tmp)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto done;
    }

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(tmp->RCPR_MODEL_STRUCT_TAG_REF(fiber), fiber);

    /* set the release method. */
    resource_init(&tmp->hdr, &fiber_resource_release);

    /* save the init values. */
    tmp->alloc = a;
    tmp->st = NULL;
    tmp->context = NULL;
    tmp->fn = NULL;
    tmp->stack_ptr = NULL;

    /* set the return pointer. */
    *fib = tmp;
    retval = STATUS_SUCCESS;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_fiber_valid(*fib));

    /* success. */
    goto done;

done:
    return retval;
}
