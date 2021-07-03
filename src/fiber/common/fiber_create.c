/**
 * \file fiber/common/fiber_create.c
 *
 * \brief Create a fiber instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_fiber_internal;
RCPR_IMPORT_resource;
RCPR_IMPORT_stack;

/* forward decls. */
RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(fiber);

/**
 * \brief Create a \ref fiber instance.
 *
 * \param fib           Pointer to the \ref fiber pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      fiber resource.
 * \param sched         Pointer to the fiber scheduler to use for this instance.
 * \param stack_size    The size of the stack in bytes for this fiber.
 * \param context       An opaque pointer to a context structure to use for this
 *                      \ref fiber instance.
 * \param fn            The function this \ref fiber should execute.
 *
 * \note This \ref fiber is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref fiber_resource_handle on this \ref fiber instance. The fiber must be in
 * a terminated state before releasing this resource. If the fiber is
 * not yet terminated, then the resource release will fail. It
 * is up to the caller to ensure that the fiber has terminated, such as devising
 * a termination strategy, prior to releasing this resource.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p fib must not reference a valid \ref fiber instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p stack_size must be greater than zero and must follow platform rules
 *        for fiber stack size.
 *      - \p fn must be a valid function.
 *
 * \post
 *      - On success, \p fib is set to a pointer to a valid \ref fiber instance,
 *        which is a \ref resource owned by the caller that must be released by
 *        the caller when no longer needed.
 *      - On failure, \p fib is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_create)(
    RCPR_SYM(fiber)** fib, RCPR_SYM(allocator)* a,
    RCPR_SYM(fiber_scheduler)* sched,
    size_t stack_size, void* context, fiber_fn fn)
{
    fiber* tmp;
    status retval, release_retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    RCPR_MODEL_ASSERT(stack_size > 0);
    RCPR_MODEL_ASSERT(NULL != fn);

    /* attempt to allocate memory for this fiber. */
    retval = allocator_allocate(a, (void**)&tmp, sizeof(fiber));
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto done;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(fiber));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(fiber), fiber);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(tmp->RCPR_MODEL_STRUCT_TAG_REF(fiber), fiber);

    /* set the release method. */
    resource_init(&tmp->hdr, &fiber_resource_release);

    /* save the init values. */
    tmp->alloc = a;
    tmp->context = context;
    tmp->fn = fn;

    /* create the stack. */
    retval = stack_create(&tmp->st, a, stack_size);
    if (retval != STATUS_SUCCESS)
    {
        tmp->st = NULL;
        goto fiber_release;
    }

    /* set the stack pointer. */
    tmp->stack_ptr = ((uint8_t*)tmp->st->region) + tmp->st->size;

    /* make the fiber instance. */
    fiber_make(tmp, sched, &fiber_entry);

    /* the fiber has been created. */
    tmp->fiber_state = FIBER_STATE_CREATED;

    /* save the scheduler. */
    tmp->sched = sched;

    /* set the return pointer. */
    *fib = tmp;
    retval = STATUS_SUCCESS;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_fiber_valid(*fib));

    /* success. */
    goto done;

fiber_release:
    RCPR_MODEL_EXEMPT(memset(tmp, 0, sizeof(fiber)));
    release_retval = allocator_reclaim(a, tmp);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}
