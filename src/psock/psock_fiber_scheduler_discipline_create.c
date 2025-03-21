/**
 * \file psock/psock_fiber_scheduler_discipline_create.c
 *
 * \brief Create the fiber scheduler discipline for psock fiber I/O.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/fiber.h>
#include <rcpr/model_assert.h>
#include <stddef.h>
#include <string.h>

#include "psock_internal.h"

#ifdef RCPR_FIBER_FOUND

RCPR_IMPORT_fiber;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;

/**
 * \brief Create a psock I/O discipline instance.
 *
 * \param disc          Pointer to a pointer that will hold the discipline
 *                      instance on success.
 * \param context       Pointer to a pointer to receive the context to send to
 *                      the idle fiber.
 * \param sched         The scheduler to be used for this discipline.
 * \param alloc         The allocator to use to create this instance.
 *
 * \note This only creates the discipline, it does not add it to the scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status
RCPR_SYM(psock_fiber_scheduler_discipline_create)(
    RCPR_SYM(fiber_scheduler_discipline)** disc, RCPR_SYM(resource)** context,
    RCPR_SYM(fiber_scheduler)* sched, RCPR_SYM(allocator)* alloc)
{
    status retval, release_retval;
    resource* ctx;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != disc);
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));

    /* create the fiber I/O discipline callback structure. */
    fiber_scheduler_discipline_callback_fn callbacks[2] = {
        &psock_fiber_scheduler_disciplined_read_wait_callback_handler,
        &psock_fiber_scheduler_disciplined_write_wait_callback_handler };

    /* create the context to use for this discipline. */
    retval =
        psock_fiber_scheduler_discipline_context_create(&ctx, sched, alloc);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* create the discipline. */
    retval =
        fiber_scheduler_discipline_create(
            disc, &FIBER_SCHEDULER_PSOCK_IO_DISCIPLINE, alloc, ctx, 2,
            callbacks);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_ctx;
    }

    /* call special function to override the resource release for this
     * discipline. */
    psock_fiber_scheduler_discipline_set_resource_release(*disc, ctx);

    /* set the context pointer. */
    *context = ctx;

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_ctx:
    release_retval = resource_release(ctx);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

#endif /* RCPR_FIBER_FOUND */
