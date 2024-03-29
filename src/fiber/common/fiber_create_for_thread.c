/**
 * \file fiber/common/fiber_create_for_thread.c
 *
 * \brief Create a fiber for a main thread context.
 *
 * \copyright 2021-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_fiber_internal;
RCPR_IMPORT_resource;

/* forward decls. */
RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(fiber);

/* the vtable entry for the fiber instance. */
RCPR_VTABLE
resource_vtable fiber_vtable = {
    &fiber_resource_release };

/**
 * \brief Create a \ref fiber instance for the main thread.
 *
 * \param fib           Pointer to the \ref fiber pointer to receive this
 *                      resource on success.
 * \param sched         Pointer to the fiber scheduler to use for this fiber.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      fiber resource.
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
 *
 * \post
 *      - On success, \p fib is set to a pointer to a valid \ref fiber instance,
 *        which is a \ref resource owned by the caller that must be released by
 *        the caller when no longer needed.
 *      - On failure, \p fib is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_create_for_thread)(
    RCPR_SYM(fiber)** fib, RCPR_SYM(fiber_scheduler)* sched,
    RCPR_SYM(allocator)* a)
{
    fiber* tmp;
    status retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT(NULL != fib);

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
    resource_init(&tmp->hdr, &fiber_vtable);

    /* save the init values. */
    tmp->alloc = a;
    tmp->st = NULL;
    tmp->context = NULL;
    tmp->fn = NULL;

    /* the thread fiber state is running. */
    tmp->fiber_state = FIBER_STATE_RUNNING;

    /* save the scheduler. */
    tmp->sched = sched;

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
