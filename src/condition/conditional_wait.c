/**
 * \file condition/conditional_receive.c
 *
 * \brief Wait on a condition variable.
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
 * \brief Wait on a \ref conditional.
 *
 * \param handle        The \ref conditional handle on which to wait.
 * \param condisc       Pointer to the condition discipline.
 *
 * \note This fiber will be suspended until it is notified on this conditional.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(conditional_wait)(
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

    /* wait on a conditional. */
    retval =
        fiber_discipline_yield(
            condisc, FIBER_SCHEDULER_CONDITION_YIELD_EVENT_COND_WAIT,
            (void*)handle, &resume_id, &resume_event, &resume_param);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* if the resume event is WAIT_FAILURE, return the error. */
    if (FIBER_SCHEDULER_CONDITION_RESUME_EVENT_WAIT_FAILURE == resume_event)
    {
        retval = (status)(ptrdiff_t)resume_param;
        return retval;
    }
    else if (
        FIBER_SCHEDULER_CONDITION_RESUME_EVENT_WAIT_SUCCESS
            == resume_event)
    {
        return STATUS_SUCCESS;
    }
    else
    {
        /* TODO - add support for out-of-band events. */

        return ERROR_MESSAGE_UNKNOWN_ERROR;
    }
}
