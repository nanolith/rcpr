#include <rcpr/model_assert.h>
#include <string.h>

#include "../../../src/fiber/common/fiber_internal.h"

/* forward decls. */
MODEL_STRUCT_TAG_GLOBAL_EXTERN(fiber);

status FN_DECL_MUST_CHECK
dummy_fiber_create(
    fiber** fib, allocator* a, fiber_fn fn)
{
    stack* st;
    fiber* tmp;
    status retval, reclaim_retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_allocator_valid(a));
    MODEL_ASSERT(NULL != fib);
    MODEL_ASSERT(NULL != fn);

    /* fake a stack instance. */
    st = malloc(sizeof(stack));
    if (NULL == st)
    {
        goto done;
    }
    
    /* attempt to allocate memory for this fiber. */
    tmp = malloc(sizeof(fiber));
    if (NULL == tmp)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto cleanup_stack;
    }

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(tmp->MODEL_STRUCT_TAG_REF(fiber), fiber);

    /* set the release method. */
    resource_init(&tmp->hdr, &fiber_resource_release);

    /* save the init values. */
    tmp->alloc = a;
    tmp->st = st;
    tmp->context = NULL;
    tmp->fn = fn;
    tmp->stack_ptr = NULL;

    /* set the return pointer. */
    *fib = tmp;
    retval = STATUS_SUCCESS;

    /* verify that this structure is now valid. */
    MODEL_ASSERT(prop_fiber_valid(*fib));

    /* success. */
    goto done;

cleanup_stack:
    reclaim_retval = resource_release(stack_resource_handle(st));
    if (STATUS_SUCCESS != reclaim_retval)
    {
        return reclaim_retval;
    }

done:
    return retval;
}
