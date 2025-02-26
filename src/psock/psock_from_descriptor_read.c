/**
 * \file psock/psock_from_descriptor_read.c
 *
 * \brief Read data from a descriptor.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <errno.h>
#include <rcpr/model_assert.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;

/**
 * \brief Read data from the given \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to read.
 * \param ctx           User context (ignored).
 * \param data          Pointer to the buffer into which data should be read.
 * \param size          Pointer to the size to read, updated with the size read.
 * \param block         Ignored for raw descriptor reads.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_from_descriptor_read)(
    RCPR_SYM(psock)* sock, void* ctx, void* data, size_t* size, bool block)
{
    (void)ctx;
    (void)block;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != data);
    RCPR_MODEL_ASSERT(NULL != size);
    RCPR_MODEL_ASSERT(prop_valid_range(data, *size));

    /* convert this to a psock_from_descriptor. */
    psock_from_descriptor* s = (psock_from_descriptor*)sock;

    /* attempt to read from the descriptor. */
    ssize_t retval = read(s->descriptor, data, *size);
    if (retval < 0)
    {
        if (EAGAIN == errno || EWOULDBLOCK == errno)
        {
            return ERROR_PSOCK_READ_WOULD_BLOCK;
        }
        else
        {
            return ERROR_PSOCK_READ_GENERAL;
        }
    }

    /* save the size read. */
    *size = (size_t)retval;

    /* success, but the read might have been truncated; that's up to the
     * caller to sort out.
     */
    return STATUS_SUCCESS;
}
