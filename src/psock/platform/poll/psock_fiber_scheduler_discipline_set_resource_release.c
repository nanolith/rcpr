/**
 * \file select/psock_fiber_scheduler_discipline_set_resource_release.c
 *
 * \brief Set the resource release override for this discipline.
 *
 * \copyright 2021-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>
#include <string.h>

#include "../../../fiber/common/fiber_internal.h"
#include "psock_poll_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_resource;

/* forward decls. */
static status psock_poll_discipline_chained_release(resource* r);

/* the vtable entry for the psock poll discipline chaned instance. */
RCPR_VTABLE
resource_vtable psock_poll_discipline_chained_vtable = {
    &psock_poll_discipline_chained_release };

/**
 * \brief Hook the fiber discipline resource release method in order to ensure
 * that the psock fiber discipline context resource is release as part of the
 * release of this fiber discipline resource.
 * 
 * \param disc          The discipline to override.
 * \param context       The discipline user context.
 */
void RCPR_SYM(psock_fiber_scheduler_discipline_set_resource_release)(
    RCPR_SYM(fiber_scheduler_discipline)* disc, RCPR_SYM(resource)* context)
{
    psock_io_poll_context* ctx = (psock_io_poll_context*)context;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(disc));
    RCPR_MODEL_ASSERT(prop_poll_io_struct_valid(ctx));

    /* cache the resource header for this discipline. */
    resource* pdisc = fiber_scheduler_discipline_resource_handle(disc);
    memcpy(&ctx->discipline_cache, pdisc, sizeof(resource));

    /* set the resource release method. */
    resource_init(pdisc, &psock_poll_discipline_chained_vtable);
}

/**
 * \brief Do the chained release of both the fiber scheduler discipline and the
 * poll context.
 *
 * \param r         The fiber scheduler discipline resource handle.
 *
 * \returns a status code on success or failure.
 */
static status psock_poll_discipline_chained_release(resource* r)
{
    status ctx_release_retval, release_retval;
    fiber_scheduler_discipline* disc = (fiber_scheduler_discipline*)r;
    psock_io_poll_context* ctx = (psock_io_poll_context*)disc->context;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(disc));
    RCPR_MODEL_ASSERT(prop_poll_io_struct_valid(ctx));

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
