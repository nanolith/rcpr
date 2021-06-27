/**
 * \file psock/psock_read_boxed_data.c
 *
 * \brief Read a boxed data value from a \ref psock instance.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/socket_utilities.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;

/**
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_data.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param a             The allocator to be used to allocate memory for the
 *                      value.
 * \param data          Pointer to the value to be set based on a successful I/O
 *                      operation.  On success, this pointer is updated to a
 *                      data value that is owned by the caller and must be
 *                      released to the allocator when no longer needed.
 * \param data_size     Pointer to a variable to be set to the length of this
 *                      data on success.
 *
 * The \ref psock_write_boxed_data method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is a raw data
 * value.
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
 *      - \p data_size must be a pointer to a size_t value and must not be NULL.
 *
 * \post
 *      - On success, \p data is set to a buffer containing the data read from
 *        the socket and unboxed.
 *      - On success, \p data_size is set to the length of the data buffer.
 *      - On failure, \p data is unchanged and an error status is returned.
 *      - On failure, \p data_size is unchanged.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_data)(
    RCPR_SYM(psock)* sock, RCPR_SYM(allocator)* a, void** data,
    size_t* data_size)
{
    status retval, release_retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT(NULL != data);
    RCPR_MODEL_ASSERT(NULL != data_size);

    /* attempt to read the type from the socket. */
    uint32_t type = 0U;
    retval = psock_read_raw_uint32(sock, &type);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* verify that the type matches what we expect. */
    if (PSOCK_BOXED_TYPE_DATA != type)
    {
        retval = ERROR_PSOCK_READ_BOXED_INVALID_TYPE;
        goto done;
    }

    /* attempt to read the size from the socket. */
    uint32_t size = 0U;
    retval = psock_read_raw_uint32(sock, &size);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* allocate size bytes for the data. */
    void* buffer = NULL;
    retval = allocator_allocate(a, &buffer, size);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* read data to the buffer. */
    size_t read_size = size;
    retval = sock->read_fn(sock, buffer, &read_size, true);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_buffer;
    }

    /* verify read size. */
    if (read_size != size)
    {
        retval = ERROR_PSOCK_READ_INVALID_SIZE;
        goto cleanup_buffer;
    }

    /* on success, update output parameters. */
    *data = buffer;
    *data_size = size;
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
