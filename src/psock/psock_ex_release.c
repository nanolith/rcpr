/**
 * \file psock/psock_ex_release.c
 *
 * \brief Release a user psock resource.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/psock.h>
#include <string.h>

#include "psock_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock_internal;

/**
 * \brief Release a psock_ex resource.
 *
 * \param r             Pointer to the psock_ex resource to be
 *                      released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status RCPR_SYM(psock_ex_release)(RCPR_SYM(resource)* r)
{
    status ex_release_retval = STATUS_SUCCESS;
    status reclaim_retval = STATUS_SUCCESS;
    psock_ex* ps = (psock_ex*)r;

    /* call the release method if set. */
    if (ps->ex_release_fn)
    {
        ex_release_retval = ps->ex_release_fn(&ps->hdr, ps->ctx);
    }

    /* clean up. */
    allocator* a = ps->hdr.alloc;
    memset(ps, 0, sizeof(psock_ex));

    /* reclaim memory. */
    reclaim_retval = allocator_reclaim(a, ps);

    /* decode return value. */
    if (STATUS_SUCCESS != ex_release_retval)
    {
        return ex_release_retval;
    }
    else
    {
        return reclaim_retval;
    }
}
