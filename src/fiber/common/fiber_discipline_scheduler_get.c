/**
 * \file fiber/common/fiber_discipline_scheduler_get.c
 *
 * \brief Get the fiber scheduler associated with the given fiber scheduler
 * discipline.
 *
 * \copyright 2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_fiber_internal;

/**
 * \brief Given a fiber scheduler discipline, get the associated fiber
 * scheduler.
 *
 * \param sched         Pointer to the fiber scheduler pointer to receive the
 *                      fiber scheduler on success.
 * \param disc          The discipline.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 *
 * \pre
 *      - \p sched is a valid pointer and is not NULL.
 *      - \p disc is a pointer to a valid \ref fiber_scheduler_discipline
 *        instance.
 *
 * \post
 *      - On success, \p sched is set to the associated fiber scheduler for this
 *        discipline.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_discipline_scheduler_get)(
    RCPR_SYM(fiber_scheduler)** sched,
    RCPR_SYM(fiber_scheduler_discipline)* disc)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != sched);
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(disc));

    /* set the scheduler. */
    *sched = disc->sched;

    /* success. */
    return STATUS_SUCCESS;
}
