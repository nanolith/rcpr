/**
 * \file message/message_discipline_get_or_create.c
 *
 * \brief Get or create / add the message displine from/to the given fiber
 * scheduler.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "message_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_message;
RCPR_IMPORT_message_internal;
RCPR_IMPORT_resource;

/**
 * \brief Create or get the \ref fiber_scheduler_discipline for messaging.
 *
 * \param msgdisc       Pointer to the \ref fiber_scheduler_discipline pointer
 *                      to receive the messaging discipline.
 * \param alloc         The \ref allocator instance to use to create this
 *                      discipline if it does not already exist.
 * \param sched         The \ref fiber_scheduler from which this discipline is
 *                      either looked up or to which it is added.
 *
 * \note If the discipline does not already exist in the provided
 * \ref fiber_scheduler, it is created and added.  The discipline is owned by
 * the \p sched instance and NOT by the caller.  The lifetime for this
 * discipline is the lifetime of the \p sched instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(message_discipline_get_or_create)(
    RCPR_SYM(fiber_scheduler_discipline)** msgdisc, RCPR_SYM(allocator)* alloc,
    RCPR_SYM(fiber_scheduler)* sched)
{
    status retval, release_retval;
    resource* ctx;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != msgdisc);
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* return the fiber scheduler discipline if it already exists. */
    retval =
        fiber_scheduler_discipline_find(
            msgdisc, sched, &FIBER_SCHEDULER_MESSAGE_DISCIPLINE);
    if (STATUS_SUCCESS == retval)
    {
        goto done;
    }

    /* create the message discipline callback structure. */
    fiber_scheduler_discipline_callback_fn callbacks[4] = {
        &message_discipline_mailbox_create_callback_handler,
        &message_discipline_mailbox_close_callback_handler,
        &message_discipline_message_send_callback_handler,
        &message_discipline_message_receive_callback_handler };

    /* create the context to use for this discipline. */
    retval =
        message_discipline_context_create(&ctx, alloc, sched);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* create the discipline. */
    retval =
        fiber_scheduler_discipline_create(
            msgdisc, &FIBER_SCHEDULER_MESSAGE_DISCIPLINE, alloc, ctx, 4,
            callbacks);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_ctx;
    }

    /* add the discipline to the scheduler. */
    retval = fiber_scheduler_discipline_add(sched, *msgdisc);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_msgdisc;
    }

    /* override the resource release for this discipline. */
    message_discipline_set_resource_release(*msgdisc, ctx);

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_msgdisc:
    release_retval =
        resource_release(fiber_scheduler_discipline_resource_handle(*msgdisc));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }
    *msgdisc = NULL;

cleanup_ctx:
    release_retval = resource_release(ctx);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}
