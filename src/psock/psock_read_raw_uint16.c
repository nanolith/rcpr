/**
 * \file psock/psock_read_raw_uint16.c
 *
 * \brief Read a raw 16-bit unsigned integer value from a \ref psock instance.
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
RCPR_IMPORT_socket_utilities;

/**
 * \brief Read a raw value from the given \ref psock instance that was written
 * to the remote end of this socket by the peer calling
 * \ref psock_write_raw_uint16.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_raw_uint16 method writes a raw value to the socket,
 * which is then read by this function on the other end of the socket.  This
 * raw value is just the value, so care must be used to synchronize
 * communication between two peers that use this method.  The value is written
 * in Big Endian order.  No matter the platform of either peer, the value will
 * be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid uint16_t variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the 16-bit integer value read from the
 *        socket.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_uint16)(
    RCPR_SYM(psock)* sock, uint16_t* val)
{
    status retval;
    const psock_vtable* sock_vtable;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != val);

    /* size and data locals. */
    size_t size = sizeof(uint16_t);
    uint16_t data = 0UL;

    /* get the socket's vtable. */
    retval =
        resource_vtable_read(
            (const resource_vtable**)&sock_vtable, psock_resource_handle(sock));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* attempt to read from the socket. */
    retval = sock_vtable->read_fn(sock, sock->context, &data, &size, true);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* verify the size. */
    if (sizeof(uint16_t) != size)
    {
        return ERROR_PSOCK_READ_INVALID_SIZE;
    }

    /* copy the data. */
    *val = socket_utility_ntoh16(data);

    /* success. */
    return STATUS_SUCCESS;
}
