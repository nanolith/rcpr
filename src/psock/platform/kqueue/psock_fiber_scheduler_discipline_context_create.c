/**
 * \file kqueue/psock_fiber_scheduler_discipline_context_create.c
 *
 * \brief Create the fiber scheduler discipline for kqueue event management.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>
#include <unistd.h>

#include "psock_kqueue_internal.h"

/* forward decls. */
static status psock_io_kqueue_context_resource_release(resource* r);

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
status psock_fiber_scheduler_discipline_context_create(
    resource** context, fiber_scheduler* sched, allocator* alloc)
{
    status retval, release_retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != context);
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    MODEL_ASSERT(prop_allocator_valid(alloc));

    /* attempt to allocate memory for this context. */
    psock_io_kqueue_context* ctx = NULL;
    retval =
        allocator_allocate(
            alloc, (void**)&ctx, sizeof(psock_io_kqueue_context));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear out the structure. */
    memset(ctx, 0, sizeof(psock_io_kqueue_context));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        ctx->hdr.MODEL_STRUCT_TAG_REF(psock_io_kqueue_context),
        psock_io_kqueue_context);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(
        ctx->hdr.MODEL_STRUCT_TAG_REF(psock_io_kqueue_context),
        psock_io_kqueue_context)

    /* set the release method. */
    resource_init(&ctx->hdr, &psock_io_kqueue_context_resource_release);

    /* set the init fields. */
    ctx->sched = sched;
    ctx->alloc = alloc;
    ctx->inputs = 0;
    ctx->outputs = 0;

    /* create the kqueue instance for this discipline context. */
    ctx->kq = kqueue();
    if (ctx->kq < 0)
    {
        retval = ERROR_PSOCK_KQUEUE_FAILED;
        goto cleanup_ctx;
    }

    /* set the context. */
    *context = &ctx->hdr;

    /* verify that this structure is now valid. */
    MODEL_ASSERT(prop_kqueue_io_struct_valid(*context));

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
 * \brief Release a psock kqueue io context.
 *
 * \param r         The resource to release.
 *
 * \returns a status code on success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status psock_io_kqueue_context_resource_release(resource* r)
{
    psock_io_kqueue_context* ctx = (psock_io_kqueue_context*)r;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_kqueue_io_struct_valid(ctx));

    /* get the allocator. */
    allocator* a = ctx->alloc;

    /* close the kqueue. */
    close(ctx->kq);

    /* clear the structure. */
    memset(ctx, 0, sizeof(psock_io_kqueue_context));

    /* reclaim the structure. */
    return
        allocator_reclaim(a, ctx);
}
