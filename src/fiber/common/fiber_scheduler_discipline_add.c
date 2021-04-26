/**
 * \file fiber/common/fiber_scheduler_discipline_add.c
 *
 * \brief Add a discipline to a fiber scheduler.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "fiber_internal.h"

/**
 * \brief Add a fiber scheduler discipline to the \ref fiber_scheduler.
 *
 * \param sched         The scheduler to which this discipline is added.
 * \param disc          The \ref fiber_scheduler_discipline to add.
 *
 * \note The \ref fiber_scheduler takes ownership of this discipline and will
 * release it by calling \ref resource_release on its
 * \ref fiber_scheduler_discipline_resource_handle when no longer needed.
 * Ultimately, it is up to the callback method for this \ref fiber_scheduler to
 * maintain ownership of this disciplineuntil it is no longer needed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *      - ERROR_FIBER_SCHEDULER_DUPLICATE_DISCIPLINE_ID if an attempt is made to
 *        add a discipline with the same ID twice.
 *      - ERROR_FIBER_SCHEDULER_NOT_DISCIPLINED if an attempt is made to add a
 *        disciplined to an undisciplined fiber scheduler.
 *
 * \pre
 *      - \p sched is a pointer to a valid \ref fiber_scheduler instance.
 *      - \p disc is a pointer to a valid \ref fiber_scheduler_discipline
 *        instance.
 *      - The caller owns \p disc.
 *
 * \post
 *      - On success, \p sched takes ownership of \p disc.
 */
status FN_DECL_MUST_CHECK
fiber_scheduler_discipline_add(
    fiber_scheduler* sched, fiber_scheduler_discipline* disc)
{
    status retval;
    fiber_scheduler_disciplined_context* ctx = NULL;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(disc));

    if (!sched->disciplined)
    {
        return ERROR_FIBER_SCHEDULER_NOT_DISCIPLINED;
    }

    /* get the fiber scheduler discipline context. */
    ctx = (fiber_scheduler_disciplined_context*)sched->context;

    /* verify that this discipline does not currently exist in the discipline
     * tree. */
    resource* discipline_resource = NULL;
    retval =
        rbtree_find(&discipline_resource, ctx->disciplines_by_uuid, &disc->id);
    if (STATUS_SUCCESS == retval)
    {
        return ERROR_FIBER_SCHEDULER_DUPLICATE_DISCIPLINE_ID;
    }
 
    /* add this discipline to the discipline tree. */
    retval =
        rbtree_insert(
            ctx->disciplines_by_uuid,
            fiber_scheduler_discipline_resource_handle(disc));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* create or reallocate the callback vector to hold these callbacks. */
    size_t callback_offset = ctx->callback_vector_size;
    if (NULL == ctx->callback_vector)
    {
        retval =
            allocator_allocate(
                ctx->alloc, (void**)&ctx->callback_vector,
                disc->callback_vector_size
                    * sizeof(fiber_scheduler_discipline_callback_fn));
    }
    else
    {
        retval =
            allocator_reallocate(
                ctx->alloc, (void**)&ctx->callback_vector,
                (callback_offset + disc->callback_vector_size)
                    * sizeof(fiber_scheduler_discipline_callback_fn));
    }

    /* did the (re)allocation fail? */
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* update the callback vector size. */
    ctx->callback_vector_size += disc->callback_vector_size;

    /* update the callback codes. */
    for (size_t i = 0; i < disc->callback_vector_size; ++i)
    {
        ctx->callback_vector[i + callback_offset] = disc->callback_vector[i];
        disc->callback_codes[i] = i + callback_offset;
    }

    /* this discipline is now owned by this scheduler. */
    disc->sched = sched;

    /* success. */
    return STATUS_SUCCESS;
}
