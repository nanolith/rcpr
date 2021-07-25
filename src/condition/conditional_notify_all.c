/**
 * \file condition/conditional_notify_all.c
 *
 * \brief Unblock all fibers waiting on a condition variable.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "condition_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_condition;
RCPR_IMPORT_uuid;

/**
 * \brief Notify all fibers waiting on a \ref conditional to resume.
 *
 * \param handle        The \ref conditional handle.
 * \param condisc       Pointer to the condition discipline.
 *
 * \note This fiber will resume AFTER the notified fiber.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(conditional_notify_all)(
    RCPR_SYM(conditional) handle,
    RCPR_SYM(fiber_scheduler_discipline)* condisc)
{
    status retval;
    const rcpr_uuid* resume_id;
    int resume_event;
    void* resume_param;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(handle > 0);
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(condisc));

    /* Notify one fiber to resume. */
    retval =
        fiber_discipline_yield(
            condisc, FIBER_SCHEDULER_CONDITION_YIELD_EVENT_NOTIFY_ALL,
            (void*)handle, &resume_id, &resume_event, &resume_param);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* if the resume event is NOTIFY_FAILURE, return the error. */
    if (FIBER_SCHEDULER_CONDITION_RESUME_EVENT_NOTIFY_FAILURE == resume_event)
    {
        retval = (status)(ptrdiff_t)resume_param;
        return retval;
    }
    else if (
        FIBER_SCHEDULER_CONDITION_RESUME_EVENT_NOTIFY_SUCCESS
            == resume_event)
    {
        return STATUS_SUCCESS;
    }
    else
    {
        /* TODO - add support for out-of-band events. */

        return ERROR_CONDITION_UNKNOWN_ERROR;
    }
}
