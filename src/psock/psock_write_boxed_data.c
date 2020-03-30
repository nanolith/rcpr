/**
 * \file psock/psock_write_boxed_data.c
 *
 * \brief Write a boxed data value to a \ref psock instance.
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

/**
 * \brief Write a boxed packet to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_boxed_data.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param data          A raw data value to be written to the socket.
 * \param data_size     The size of the data to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_data method.  This boxed packet
 * contains a tag noting that the following value is a raw data packet.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p data must be a pointer to a buffer that is \p data_size bytes in
 *        length.
 */
status FN_DECL_MUST_CHECK
psock_write_boxed_data(
    psock* sock, const void* data, size_t data_size)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_psock_valid(sock));
    MODEL_ASSERT(NULL != data);
    MODEL_ASSERT(data_size <= UINT32_MAX);

    /* attempt to write the type to the socket. */
    status retval = psock_write_raw_uint32(sock, PSOCK_BOXED_TYPE_DATA);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* attempt to write the size to the socket. */
    uint32_t size = (uint32_t)data_size;
    retval = psock_write_raw_uint32(sock, size);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* attempt to write the data to the socket. */
    size_t write_size = data_size;
    retval = sock->write_fn(sock, data, &write_size);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* verify the size. */
    if (data_size != write_size)
    {
        return ERROR_PSOCK_WRITE_INVALID_SIZE;
    }

    /* success. */
    return STATUS_SUCCESS;
}
