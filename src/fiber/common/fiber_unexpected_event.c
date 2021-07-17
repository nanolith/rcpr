/**
 * \file fiber/common/fiber_unexpected_event.c
 *
 * \brief Notify the fiber of an unexpected event, calling the unexpected event
 * handler if set.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

/**
 * \brief Notify the fiber of an unexpected event, calling the unexpected event
 * handler if set.
 *
 * \param fib                       The fiber for which the unexpected handler
 *                                  should be called.
 * \param resume_disc_id            The resume discipline id received by the
 *                                  caller.
 * \param resume_event              The resume discipline event received by the
 *                                  caller.
 * \param resume_param              The resume parameter received by the caller.
 * \param expected_resume_disc_id   The discipline ID that the caller expected
 *                                  to receive on resume.
 * \param expected_resume_event     The resume event that the caller expected to
 *                                  receive.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when the yielding function should retry.
 *      - ERROR_FIBER_NO_UNEXPECTED_HANDLER if the unexpected handler was not
 *        set.
 *      - any other non-zero status code is an error code from the yielding
 *        function.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_unexpected_event)(
    RCPR_SYM(fiber)* fib, const RCPR_SYM(rcpr_uuid)* resume_disc_id,
    int resume_event, void* resume_param,
    const RCPR_SYM(rcpr_uuid)* expected_resume_disc_id,
    int expected_resume_event)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_fiber_valid(fib));
    RCPR_MODEL_ASSERT(NULL != resume_disc_id);
    RCPR_MODEL_ASSERT(NULL != expected_resume_disc_id);

    /* first, check to see if the unexpected handler has been set. */
    if (NULL == fib->unexpected_fn)
    {
        return ERROR_FIBER_NO_UNEXPECTED_HANDLER;
    }

    /* call the unexpected event handler. */
    return
        fib->unexpected_fn(
            fib->unexpected_context, fib, resume_disc_id, resume_event,
            resume_param, expected_resume_disc_id, expected_resume_event);
}
