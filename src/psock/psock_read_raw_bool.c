/**
 * \file psock/psock_read_raw_bool.c
 *
 * \brief Read a raw boolean value from a \ref psock instance.
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
 * \brief Read a raw value from the given \ref psock instance that was written
 * to the remote end of this socket by the peer calling
 * \ref psock_write_raw_bool.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_raw_bool method writes a raw value to the socket, which
 * is then read by this function on the other end of the socket.  This
 * raw value is just the value, so care must be used to synchronize
 * communication between two peers that use this method.  No matter the platform
 * of either peer, the value will be converted to or from native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a pointer to a valid bool variable and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p val is set to the boolean value read from the socket.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_raw_bool)(
    RCPR_SYM(psock)* sock, bool* val)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != val);
    const psock_vtable* sock_vtable;

    /* size and data locals. */
    size_t size = sizeof(uint8_t);
    uint8_t data = 0U;

    /* get the socket's vtable. */
    sock_vtable =
        (const psock_vtable*)resource_vtable_get(psock_resource_handle(sock));

    /* attempt to read from the socket. */
    int retval = sock_vtable->read_fn(sock, sock->context, &data, &size, true);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* verify the size. */
    if (sizeof(uint8_t) != size)
    {
        return ERROR_PSOCK_READ_INVALID_SIZE;
    }

    /* set the boolean value. */
    if (data)
        *val = true;
    else
        *val = false;

    /* success. */
    return STATUS_SUCCESS;
}
