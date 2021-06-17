/**
 * \file psock/psock_write_raw_uint16.c
 *
 * \brief Write a raw 16-bit unsigned integer value to a \ref psock instance.
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

/**
 * \brief Write a raw value to the given \ref psock instance that will be read
 * from the remote end of this socket by the peer calling
 * \ref psock_read_raw_uint16.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           A uint16_t value to be written to the socket.
 *
 * This method writes a raw value to the socket, which is then read by the
 * remote peer using the \ref psock_read_raw_uint16 method.  This raw value is
 * just the value, so care must be used to synchronize communication between the
 * two peers that use this method.  This value is written in Big Endian order.
 * No matter the platform of either peer, the value will be converted to or from
 * native ordering.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_raw_uint16)(
    RCPR_SYM(psock)* sock, uint16_t val)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_psock_valid(sock));

    /* size to write. */
    size_t size = sizeof(uint16_t);
    uint16_t data = socket_utility_hton16(val);

    /* attempt to write to the socket. */
    int retval =
        sock->write_fn(sock, &data, &size);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* verify the size. */
    if (sizeof(uint16_t) != size)
    {
        return ERROR_PSOCK_WRITE_INVALID_SIZE;
    }

    /* success. */
    return STATUS_SUCCESS;
}
