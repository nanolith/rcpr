/**
 * \file condition/conditional_create.c
 *
 * \brief Create a conditional using the condition discipline.
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
 * \brief Create a \ref conditional using the condition discipline.
 *
 * \param addr          Pointer to the \ref conditional handle to receive
 *                      this new instance handle.
 * \param condisc       Pointer to the condition discipline.
 *
 * \note This \ref conditional is a unique handle that references a condition
 * barrier created by the condition discipline.  This is an abstract resource
 * that must be released by calling \ref conditional_close when it is no longer
 * needed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(conditional_create)(
    RCPR_SYM(conditional)* handle,
    RCPR_SYM(fiber_scheduler_discipline)* condisc)
{
    status retval;
    const rcpr_uuid* resume_id;
    int resume_event;
    void* resume_param;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != handle);
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(condisc));

    retval =
        fiber_discipline_yield(
            condisc, FIBER_SCHEDULER_CONDITION_YIELD_EVENT_CREATE, NULL,
            &resume_id, &resume_event, &resume_param);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    if (
        FIBER_SCHEDULER_CONDITION_RESUME_EVENT_CREATE_FAILURE
            == resume_event)
    {
        retval = (status)(ptrdiff_t)resume_param;
        return retval;
    }
    else if (
        FIBER_SCHEDULER_CONDITION_RESUME_EVENT_CREATE_SUCCESS
            == resume_event)
    {
        *handle = (conditional)(resume_param);
        return STATUS_SUCCESS;
    }
    else
    {
        /* TODO - add support for out-of-band events. */
        return ERROR_CONDITION_UNKNOWN_ERROR;
    }
}
