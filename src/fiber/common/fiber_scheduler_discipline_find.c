/**
 * \file fiber/common/fiber_scheduler_discipline_find.c
 *
 * \brief Find a discipline by id in a fiber scheduler.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_fiber_internal;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_resource;
RCPR_IMPORT_uuid;

/**
 * \brief Find a fiber scheduler discipline in the \ref fiber_scheduler.
 *
 * \param disc          Pointer to the \ref fiber_scheduler_discipline pointer
 *                      to hold the result if found.
 * \param sched         The scheduler to search.
 * \param id            The discipline uuid to search for.
 *
 * \note The ownership of this \ref fiber_scheduler_discipline remains with the
 * scheduler, and is only valid for the lifetime of the scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_FIBER_SCHEDULER_DISCIPLINE_NOT_FOUND if the discipline wasn't
 *        found in the scheduler.
 *
 * \pre
 *      - \p disc is a valid pointer to a \ref fiber_scheduler_discipline
 *        pointer.
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p id is a pointer to a valid \ref rcpr_uuid.
 *
 * \post
 *      - On success, \p disc is updated to point to a valid \ref
 *        fiber_scheduler_discipline instance owned by the scheduler.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_scheduler_discipline_find)(
    RCPR_SYM(fiber_scheduler_discipline)** disc,
    RCPR_SYM(fiber_scheduler)* sched, const RCPR_SYM(rcpr_uuid)* id)
{
    status retval;
    fiber_scheduler_disciplined_context* ctx = NULL;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != disc);
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    MODEL_ASSERT(prop_uuid_valid(id));
    MODEL_ASSERT(sched->disciplined);

    /* if the scheduler is not disciplined, this call is in error. */
    if (!sched->disciplined)
    {
        return ERROR_FIBER_SCHEDULER_NOT_DISCIPLINED;
    }

    /* get the fiber scheduler discipline context. */
    ctx = (fiber_scheduler_disciplined_context*)sched->context;

    /* attempt to find the discipline resource by id. */
    resource* discipline_resource = NULL;
    retval = rbtree_find(&discipline_resource, ctx->disciplines_by_uuid, id);
    if (STATUS_SUCCESS != retval)
    {
        return ERROR_FIBER_SCHEDULER_DISCIPLINE_NOT_FOUND;
    }

    /* return the discipline. */
    *disc = (fiber_scheduler_discipline*)discipline_resource;
    MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(*disc));

    /* success. */
    return STATUS_SUCCESS;
}
