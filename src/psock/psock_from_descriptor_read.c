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

/**
 * \brief Read data from the given \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to read.
 * \param data          Pointer to the buffer into which data should be read.
 * \param size          Pointer to the size to read, updated with the size read.
 * \param block         Ignored for raw descriptor reads.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status psock_from_descriptor_read(
    psock* sock, void* data, size_t* size, bool block)
{
    (void)block;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_psock_valid(sock));
    MODEL_ASSERT(NULL != data);
    MODEL_ASSERT(NULL != size);
    MODEL_ASSERT(prop_valid_range(data, *size));

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
