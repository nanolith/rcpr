#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#include "../../../src/stack/stack_internal.h"

/* forward decls. */
static status stack_release(resource*);

MODEL_STRUCT_TAG_GLOBAL_EXTERN(stack);

status FN_DECL_MUST_CHECK
stack_create(
    stack** st, allocator* a, size_t stack_size)
{
    status retval, reclaim_retval;
    void* mem;
    stack* tmp = NULL;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != st);
    MODEL_ASSERT(prop_allocator_valid(a));
    MODEL_ASSERT(stack_size > 0);

    /* attempt to allocate memory for this stack. */
    tmp = malloc(sizeof(stack));
    if (NULL == tmp)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto done;
    }

    /* clear structure. */
    memset(tmp, 0, sizeof(stack));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->MODEL_STRUCT_TAG_REF(stack), stack);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(tmp->MODEL_STRUCT_TAG_REF(stack), stack);

    /* set the release method. */
    resource_init(&tmp->hdr, &stack_release);

    /* save the init values. */
    tmp->alloc = a;
    tmp->size = stack_size;

    /* Allocate memory for the stack. */
    mem = malloc(stack_size);
    if (NULL == mem)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto free_stack;
    }

    /* set the region. */
    tmp->region = mem;

    /* Set the return pointer. */
    *st = tmp;
    retval = STATUS_SUCCESS;

    /* verify that this stack is now valid. */
    MODEL_ASSERT(prop_stack_valid(*st));

    /* success. */ 
    goto done;

free_stack:
    memset(tmp, 0, sizeof(stack));
    reclaim_retval = allocator_reclaim(a, tmp);
    if (STATUS_SUCCESS != reclaim_retval)
        retval = reclaim_retval;

done:
    return retval;
}

static status stack_release(resource* r)
{
    status retval;
    stack* st = (stack*)r;
    MODEL_ASSERT(prop_stack_valid(st));

    /* free the stack. */
    free(st->region);

    /* reclaim the stack structure. */
    free(st);

    return STATUS_SUCCESS;
}
