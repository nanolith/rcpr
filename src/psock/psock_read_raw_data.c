/**
 * \file psock/psock_read_raw_data.c
 *
 * \brief Read a fixed raw data value from a \ref psock instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/socket_utilities.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_allocator;

/**
 * \brief Read a raw value from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_raw_data.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param a             The allocator to be used to allocate memory for the
 *                      value.
 * \param data          Pointer to the value to be set based on a successful I/O
 *                      operation.  On success, this pointer is updated to a
 *                      data value that is owned by the caller and must be
 *                      released to the allocator when no longer needed.
 * \param data_size     Size of the data to read.
 *
 * The \ref psock_write_raw_data method writes a raw data value to the socket,
 * which is then read by this function on the other end of the socket.  This
 * raw data value is written and read as-is, and requires coordination with the
 * peer to determine the correct size to read or write.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p a must be a pointer to a valid \ref allocator instance and must not
 *        be NULL.
 *      - \p data must be a pointer to a valid pointer and must not be NULL.
 *
 * \post
 *      - On success, \p data is set to a buffer containing the data read from
 *        the socket.
 *      - On failure, \p data is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
psock_read_raw_data(
    psock* sock, RCPR_SYM(allocator)* a, void** data, size_t data_size)
{
    status retval, release_retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_psock_valid(sock));
    MODEL_ASSERT(prop_allocator_valid(a));
    MODEL_ASSERT(NULL != data);

    /* allocate data_size bytes for the data. */
    void* buffer = NULL;
    retval = allocator_allocate(a, &buffer, data_size);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* read data to the buffer. */
    size_t read_size = data_size;
    retval = sock->read_fn(sock, buffer, &read_size, true);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_buffer;
    }

    /* verify read size. */
    if (read_size != data_size)
    {
        retval = ERROR_PSOCK_READ_INVALID_SIZE;
        goto cleanup_buffer;
    }

    /* on success, update output parameter. */
    *data = buffer;
    retval = STATUS_SUCCESS;
    goto done;

cleanup_buffer:
    release_retval = allocator_reclaim(a, buffer);
    if (STATUS_SUCCESS == retval && STATUS_SUCCESS != release_retval)
    {
        /* cascade error if deallocation fails. */
        retval = release_retval;
    }

done:
    return retval;
}
