/**
 * \file message/message_discipline_set_resource_release.c
 *
 * \brief Set the resource release method for the fiber scheduler discipline, to
 * chain the context resource release.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "../fiber/common/fiber_internal.h"
#include "message_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_message;
RCPR_IMPORT_message_internal;
RCPR_IMPORT_queue;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_resource;

/* forward decls. */
static status message_discipline_context_chained_release(resource* r);

/**
 * \brief Override the resource release method for a message discipline.
 *
 * \param msgdisc       The message discipline to override.
 * \param context       The context to be released by this overridden release
 *                      method.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(message_discipline_set_resource_release)(
    RCPR_SYM(fiber_scheduler_discipline)* msgdisc, RCPR_SYM(resource)* context)
{
    message_discipline_context* ctx = (message_discipline_context*)context;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(msgdisc));
    MODEL_ASSERT(prop_message_discipline_context_valid(ctx));

    /* cache the resource header for this discipline. */
    resource* pdisc = fiber_scheduler_discipline_resource_handle(msgdisc);
    memcpy(&ctx->discipline_cache, pdisc, sizeof(resource));

    /* set the resource release method. */
    resource_init(pdisc, &message_discipline_context_chained_release);

    /* success. */
    return STATUS_SUCCESS;
}

/**
 * \brief Do the chained release of both the fiber scheduler discipline and the
 * message discipline context.
 *
 * \param r         The fiber scheduler discipline resource handle.
 *
 * \returns a status code on success or failure.
 */
static status message_discipline_context_chained_release(resource* r)
{
    status ctx_release_retval, release_retval;
    fiber_scheduler_discipline* disc = (fiber_scheduler_discipline*)r;
    message_discipline_context* ctx =
        (message_discipline_context*)disc->context;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(disc));
    MODEL_ASSERT(prop_message_discipline_context_valid(ctx));

    /* copy the original resource to the discipline. */
    memcpy(&disc->hdr, &ctx->discipline_cache, sizeof(resource));

    /* release the context. */
    ctx_release_retval = resource_release(&ctx->hdr);

    /* release the discipline. */
    release_retval = resource_release(&disc->hdr);

    /* bubble up the first error. */
    if (STATUS_SUCCESS != ctx_release_retval)
    {
        return ctx_release_retval;
    }
    else
    {
        return release_retval;
    }
}
