/**
 * \file condition/conditional_close.c
 *
 * \brief Close a conditional using the condition discipline.
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
 * \brief Close a \ref conditional handle using the condition discipline.
 *
 * \param handle        The \ref conditional handle to close.
 * \param condisc       Pointer to the condition discipline.
 *
 * \note The \ref conditional handle pointed to by \p handle will be closed.  No
 * other fibers can wait or notify using this handle once it has been closed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(conditional_close)(
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

    retval =
        fiber_discipline_yield(
            condisc, FIBER_SCHEDULER_CONDITION_YIELD_EVENT_CLOSE,
            (void*)(ptrdiff_t)handle, &resume_id, &resume_event, &resume_param);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    if (
        FIBER_SCHEDULER_CONDITION_RESUME_EVENT_CLOSE_FAILURE == resume_event
     || FIBER_SCHEDULER_CONDITION_RESUME_EVENT_CLOSE_SUCCESS == resume_event)
    {
        retval = (status)(ptrdiff_t)resume_param;
        return retval;
    }
    else
    {
        /* TODO - add support for out-of-band events. */
        return ERROR_CONDITION_UNKNOWN_ERROR;
    }
}
