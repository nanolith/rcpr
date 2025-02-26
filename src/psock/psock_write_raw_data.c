/**
 * \file psock/psock_write_raw_data.c
 *
 * \brief Write a raw data value to a \ref psock instance.
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

RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;

/**
 * \brief Write a raw value to the given \ref psock instance that will be read
 * from the remote end of this socket by the peer calling
 * \ref psock_read_raw_data.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param data          A raw data value to be written to the socket.
 * \param data_size     The size of the data to be written to the socket.
 *
 * This method writes a raw data value to the socket, which is then read by the
 * remote peer using the \ref psock_read_raw_data method.  This raw data value
 * is just the value, so care must be used to synchronize communication between
 * the two peers in order to coordinate a read of this raw data and its size.
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
RCPR_SYM(psock_write_raw_data)(
    RCPR_SYM(psock)* sock, const void* data, size_t data_size)
{
    status retval;
    const psock_vtable* sock_vtable;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != data);
    RCPR_MODEL_ASSERT(data_size <= UINT32_MAX);

    /* get the socket's vtable. */
    sock_vtable =
        (const psock_vtable*)resource_vtable_get(psock_resource_handle(sock));

    /* loop to write all data. */
    const uint8_t* dptr = (const uint8_t*)data;
    while (data_size > 0)
    {
        /* attempt to write the data to the socket. */
        size_t write_size = data_size;
        retval = sock_vtable->write_fn(sock, sock->context, dptr, &write_size);
        if (STATUS_SUCCESS != retval)
        {
            return retval;
        }

        /* a zero size write indicates failure. */
        if (0 == write_size)
        {
            break;
        }

        /* update counters. */
        dptr += write_size;
        data_size -= write_size;
    }

    /* verify the size. */
    if (data_size > 0)
    {
        return ERROR_PSOCK_WRITE_INVALID_SIZE;
    }

    /* success. */
    return STATUS_SUCCESS;
}
