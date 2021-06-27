/**
 * \file select/psock_fiber_scheduler_discipline_context_create.c
 *
 * \brief Create the fiber scheduler discipline for select event management.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/fiber.h>
#include <rcpr/model_assert.h>
#include <string.h>

#include "psock_poll_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_resource;

/* forward decls. */
static status psock_io_poll_context_resource_release(resource* r);

/**
 * \brief Create a platform-specific fiber scheduler discipline context for
 * psock I/O.
 *
 * \param context       Pointer to receive the context pointer on success.
 * \param sched         The fiber scheduler to which this discipline will
 *                      belong.
 * \param alloc         The allocator to use to create this resource.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(psock_fiber_scheduler_discipline_context_create)(
    RCPR_SYM(resource)** context, RCPR_SYM(fiber_scheduler)* sched,
    RCPR_SYM(allocator)* alloc)
{
    status retval, release_retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != context);
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));

    /* attempt to allocate memory for this context. */
    psock_io_poll_context* ctx = NULL;
    retval =
        allocator_allocate(
            alloc, (void**)&ctx, sizeof(psock_io_poll_context));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear out the structure. */
    memset(ctx, 0, sizeof(psock_io_poll_context));

    /* attempt to allocate memory for the poll event array. */
    ctx->poll_max = POLL_EVENT_SIZE_INCREMENT;
    retval =
        allocator_allocate(
            alloc, (void**)&ctx->poll_events,
            ctx->poll_max * sizeof(struct pollfd));
    if (STATUS_SUCCESS != retval)
    {
        goto release_ctx;
    }

    /* clear out the poll structure. */
    for (size_t i = 0; i < ctx->poll_max; ++i)
    {
        ctx->poll_events[i].fd = -1;
        ctx->poll_events[i].events = ctx->poll_events[i].revents = 0;
    }

    /* attempt to allocate memory for the fiber array. */
    retval =
        allocator_allocate(
            alloc, (void**)&ctx->poll_fibers,
            ctx->poll_max * sizeof(fiber*));
    if (STATUS_SUCCESS != retval)
    {
        goto release_poll_events;
    }

    /* clear out the fiber array. */
    memset(ctx->poll_fibers, 0, ctx->poll_max * sizeof(fiber*));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        ctx->hdr.RCPR_MODEL_STRUCT_TAG_REF(psock_io_poll_context),
        psock_io_poll_context);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        ctx->hdr.RCPR_MODEL_STRUCT_TAG_REF(psock_io_poll_context),
        psock_io_poll_context);

    /* set the release method. */
    resource_init(&ctx->hdr, &psock_io_poll_context_resource_release);

    /* set the init fields. */
    ctx->sched = sched;
    ctx->alloc = alloc;
    ctx->poll_curr = 0;

    /* set the context. */
    *context = &ctx->hdr;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_poll_io_struct_valid(ctx));

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

release_poll_events:
    release_retval = allocator_reclaim(alloc, ctx->poll_events);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

release_ctx:
    release_retval = allocator_reclaim(alloc, ctx);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

/**
 * \brief Release a psock poll io context.
 *
 * \param r         The resource to release.
 *
 * \returns a status code on success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status psock_io_poll_context_resource_release(resource* r)
{
    psock_io_poll_context* ctx = (psock_io_poll_context*)r;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_poll_io_struct_valid(ctx));

    /* get the allocator. */
    allocator* alloc = ctx->alloc;

    /* clear the event array. */
    memset(ctx->poll_events, 0, ctx->poll_max * sizeof(struct pollfd));

    /* release the event array. */
    status event_array_retval = allocator_reclaim(alloc, ctx->poll_events);

    /* clear the fiber array. */
    memset(ctx->poll_fibers, 0, ctx->poll_max * sizeof(fiber*));

    /* release the fiber array. */
    status fiber_array_retval = allocator_reclaim(alloc, ctx->poll_fibers);

    /* clear the structure. */
    memset(ctx, 0, sizeof(psock_io_poll_context));

    /* reclaim the structure. */
    status ctx_retval = allocator_reclaim(alloc, ctx);

    /* return a valid return code. */
    if (STATUS_SUCCESS != event_array_retval)
    {
        return event_array_retval;
    }
    else if (STATUS_SUCCESS != fiber_array_retval)
    {
        return fiber_array_retval;
    }
    else if (STATUS_SUCCESS != ctx_retval)
    {
        return ctx_retval;
    }
    else
    {
        return STATUS_SUCCESS;
    }
}
