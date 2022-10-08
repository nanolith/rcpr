/**
 * \file psock/psock_br_release.c
 *
 * \brief Release a \ref psock_br instance.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <string.h>

#include "psock_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock_internal;

/**
 * \brief Release a psock_br resource.
 *
 * \param r             Pointer to the psock_br resource to be
 *                      released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status RCPR_SYM(psock_br_release)(RCPR_SYM(resource)* r)
{
    status reclaim_retval = STATUS_SUCCESS;
    status buffer_reclaim_retval = STATUS_SUCCESS;

    psock_br* br = (psock_br*)r;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_br_valid(*br));

    /* cache allocator. */
    allocator* alloc = br->hdr.alloc;

    /* reclaim the buffer if set. */
    if (NULL != br->buffer)
    {
        memset(br->buffer, 0, br->size);
        buffer_reclaim_retval = allocator_reclaim(alloc, br->buffer);
    }

    /* clear structure. */
    memset(br, 0, sizeof(*br));

    /* reclaim memory. */
    reclaim_retval = allocator_reclaim(alloc, br);

    /* decode return value. */
    if (STATUS_SUCCESS != buffer_reclaim_retval)
    {
        return buffer_reclaim_retval;
    }
    else
    {
        return reclaim_retval;
    }
}
