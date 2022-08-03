/**
 * \file psock/psock_ex_write.c
 *
 * \brief Write to a user psock instance.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/psock.h>
#include <string.h>

#include "psock_internal.h"

RCPR_IMPORT_psock_internal;

/**
 * \brief Write data to the given \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to write.
 * \param data          Pointer to the buffer from which data should be written.
 * \param size          Pointer to the size to write, updated with the size
 *                      written.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_ex_write)(
    RCPR_SYM(psock)* sock, const void* data, size_t* size)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != data);
    RCPR_MODEL_ASSERT(NULL != size);
    RCPR_MODEL_ASSERT(prop_valid_range(data, *size));

    /* convert this to a psock_ex. */
    psock_ex* s = (psock_ex*)sock;

    /* call the user function if defined. */
    if (s->ex_write_fn)
    {
        return s->ex_write_fn(&s->hdr, s->ctx, data, size);
    }
    else
    {
        return ERROR_PSOCK_USER_METHOD_UNDEFINED;
    }
}
