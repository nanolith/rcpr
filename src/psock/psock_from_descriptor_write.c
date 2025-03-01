/**
 * \file psock/psock_from_descriptor_write.c
 *
 * \brief Write data to a descriptor.
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
 * \brief Write data to the given \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to write.
 * \param ctx           User context (ignored).
 * \param data          Pointer to the buffer from which data should be written.
 * \param size          Pointer to the size to write, updated with the size
 *                      written.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_from_descriptor_write)(
    RCPR_SYM(psock)* sock, void* ctx, const void* data, size_t* size)
{
    (void)ctx;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != data);
    RCPR_MODEL_ASSERT(NULL != size);
    RCPR_MODEL_ASSERT(prop_valid_range(data, *size));

    /* convert this to a psock_from_descriptor. */
    psock_from_descriptor* s = (psock_from_descriptor*)sock;

    /* attempt to write to the descriptor. */
    ssize_t retval = write(s->descriptor, data, *size);
    if (retval < 0)
    {
        if (EAGAIN == errno || EWOULDBLOCK == errno)
        {
            return ERROR_PSOCK_WRITE_WOULD_BLOCK;
        }
        else
        {
            return ERROR_PSOCK_WRITE_GENERAL;
        }
    }

    /* save the size written. */
    *size = (size_t)retval;

    /* success, but the write might have been truncated; that's up to the
     * caller to sort out.
     */
    return STATUS_SUCCESS;
}
