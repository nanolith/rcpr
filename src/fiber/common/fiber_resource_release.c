/**
 * \file fiber/common/fiber_resource_release.c
 *
 * \brief Release a fiber resource.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

/**
 * \brief Release a fiber resource.
 *
 * \param r         The fiber resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status fiber_resource_release(RCPR_SYM(resource)* r)
{
    status stack_retval, retval;
    fiber* fib = (fiber*)r;
    MODEL_ASSERT(prop_fiber_valid(fib));

    /* cache the allocator. */
    allocator* a = fib->alloc;

    /* is there a stack? */
    if (NULL != fib->st)
    {
        /* release it. */
        stack_retval = resource_release(stack_resource_handle(fib->st));
    }
    else
    {
        stack_retval = STATUS_SUCCESS;
    }

    /* clear the fiber structure. */
    MODEL_EXEMPT(memset(fib, 0, sizeof(fiber)));

    /* reclaim the fiber structure. */
    retval = allocator_reclaim(a, fib);

    /* if we succeeeded at reclaiming the fiber structure, return the stack
     * reclaim retval. */
    if (STATUS_SUCCESS == retval)
    {
        return stack_retval;
    }
    else
    {
        return retval;
    }
}
