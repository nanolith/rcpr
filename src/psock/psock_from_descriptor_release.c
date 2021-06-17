/**
 * \file psock/psock_from_descriptor_release.c
 *
 * \brief Release a \ref psock instance created from a descriptor.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;

/**
 * \brief Release a psock_from_descriptor resource.
 *
 * \param r             Pointer to the psock_from_descriptor resource to be
 *                      released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status
RCPR_SYM(psock_from_descriptor_release)(RCPR_SYM(resource)* r)
{
    psock_from_descriptor* ps = (psock_from_descriptor*)r;

    /* close the descriptor. */
    close(ps->descriptor);

    /* clean up. */
    allocator* a = ps->hdr.alloc;
    memset(ps, 0, sizeof(psock_from_descriptor));

    /* if reclaiming this psock instance succeeds, so does this release. */
    return
        allocator_reclaim(a, ps);
}
