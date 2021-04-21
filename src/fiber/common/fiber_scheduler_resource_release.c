/**
 * \file fiber/common/fiber_scheduler_resource_release.c
 *
 * \brief Release a fiber scheduler resource.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

/**
 * \brief Release a fiber scheduler resource.
 *
 * \param r         The fiber scheduler resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status fiber_scheduler_resource_release(resource* r)
{
    status sched_retval, fiber_retval, retval;
    fiber_scheduler* sched = (fiber_scheduler*)r;
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* cache the allocator. */
    allocator* a = sched->alloc;

    /* is there a main fiber? */
    if (NULL != sched->main_fiber)
    {
        /* instruct the callback to release any resources. */
        fiber* resume_fib;
        int resume_event;
        void* resume_param;
        sched_retval =
            sched->fn(
                sched->context, sched->main_fiber,
                FIBER_SCHEDULER_YIELD_EVENT_RESOURCE_RELEASE, NULL, &resume_fib,
                &resume_event, &resume_param);

        /* release it. */
        fiber_retval =
            resource_release(fiber_resource_handle(sched->main_fiber));
    }
    else
    {
        sched_retval = STATUS_SUCCESS;
        fiber_retval = STATUS_SUCCESS;
    }

    /* clear the scheduler structure. */
    MODEL_EXEMPT(memset(sched, 0, sizeof(*sched)));

    /* reclaim the scheduler structure. */
    retval = allocator_reclaim(a, sched);

    /* if we succeeded at reclaiming the scheduler structure... */
    if (STATUS_SUCCESS == retval)
    {
        /* if we succeeded at reclaiming the scheduler details. */
        if (STATUS_SUCCESS == sched_retval)
        {
            /* return the fiber release status. */
            return fiber_retval;
        }
        else
        {
            return sched_retval;
        }
    }
    else
    {
        return retval;
    }
}
