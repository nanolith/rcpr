/**
 * \file psock/psock_write_boxed_int16.c
 *
 * \brief Write a boxed 16-bit integer value to a \ref psock instance.
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
 * psock_read_boxed_int16.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           An int16_t value to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_int16 method.  This boxed packet
 * contains a tag noting that the following value is a 16-bit integer, which is
 * written in Big Endian order.  No matter the platform of either peer, the
 * value will be converted to or from native ordering.
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
psock_write_boxed_int16(
    psock* sock, int16_t val)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_psock_valid(sock));

    /* attempt to write the type to the socket. */
    status retval = psock_write_raw_uint32(sock, PSOCK_BOXED_TYPE_INT16);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* attempt to write the value to the socket. */
    return psock_write_raw_int16(sock, val);
}