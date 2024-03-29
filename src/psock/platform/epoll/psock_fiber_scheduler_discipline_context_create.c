/**
 * \file epoll/psock_fiber_scheduler_discipline_context_create.c
 *
 * \brief Create the fiber scheduler discipline for epoll event management.
 *
 * \copyright 2021-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/fiber.h>
#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>
#include <string.h>
#include <unistd.h>

#include "psock_epoll_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_resource;

/* forward decls. */
static status psock_io_epoll_context_resource_release(resource* r);

/* the vtable entry for psock fiber scheduler discipline context instance. */
RCPR_VTABLE
resource_vtable psock_fiber_scheduler_discipline_vtable = {
    &psock_io_epoll_context_resource_release };

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
    psock_io_epoll_context* ctx = NULL;
    retval =
        allocator_allocate(
            alloc, (void**)&ctx, sizeof(psock_io_epoll_context));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear out the structure. */
    memset(ctx, 0, sizeof(psock_io_epoll_context));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        ctx->hdr.RCPR_MODEL_STRUCT_TAG_REF(psock_io_epoll_context),
        psock_io_epoll_context);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        ctx->hdr.RCPR_MODEL_STRUCT_TAG_REF(psock_io_epoll_context),
        psock_io_epoll_context);

    /* set the release method. */
    resource_init(&ctx->hdr, &psock_fiber_scheduler_discipline_vtable);

    /* set the init fields. */
    ctx->sched = sched;
    ctx->alloc = alloc;
    ctx->outputs = 0;

    /* create the epoll instance for this discipline context. */
    ctx->ep = epoll_create1(0);
    if (ctx->ep < 0)
    {
        retval = ERROR_PSOCK_EPOLL_CREATE_FAILED;
        goto cleanup_ctx;
    }

    /* set the context. */
    *context = &ctx->hdr;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_epoll_io_struct_valid(ctx));

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_ctx:
    release_retval = allocator_reclaim(alloc, ctx);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

/**
 * \brief Release a psock epoll io context.
 *
 * \param r         The resource to release.
 *
 * \returns a status code on success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status psock_io_epoll_context_resource_release(resource* r)
{
    psock_io_epoll_context* ctx = (psock_io_epoll_context*)r;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_epoll_io_struct_valid(ctx));

    /* get the allocator. */
    allocator* a = ctx->alloc;

    /* close the epoll instance. */
    close(ctx->ep);

    /* clear the structure. */
    memset(ctx, 0, sizeof(psock_io_epoll_context));

    /* reclaim the structure. */
    return
        allocator_reclaim(a, ctx);
}
