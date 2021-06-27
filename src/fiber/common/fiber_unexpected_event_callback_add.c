/**
 * \file fiber/common/fiber_unexpected_event_callback_add.c
 *
 * \brief Add an unexpected event handler to the fiber.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

/**
 * \brief Add an unexpected event handler to a given fiber instance.
 *
 * \param fib           The fiber to which this event handler should be added.
 * \param fn            The unexpected event handler callback function.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p fib is a pointer to a valid \ref fiber instance.
 *      - \p fn is a pointer to a valid \ref fiber_unexpected_event_callback_fn
 *        callback function.
 *
 * \post
 *      - On success, \p fib is updated to use \p fn during an unexpected event
 *        received by participating yielding functions.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_unexpected_event_callback_add)(
    RCPR_SYM(fiber)* fib, RCPR_SYM(fiber_unexpected_event_callback_fn) fn)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_fiber_valid(fib));
    RCPR_MODEL_ASSERT(NULL != fn);

    /* assign the callback function. */
    fib->unexpected_fn = fn;

    return STATUS_SUCCESS;
}
