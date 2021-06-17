/**
 * \file psock/psock_write_boxed_string.c
 *
 * \brief Write a boxed string value to a \ref psock instance.
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
 * \brief Write a boxed packet to the given \ref psock instance that will be
 * read from the remote end of this socket by the peer calling \ref
 * psock_read_boxed_string.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           A C-string value to be written to the socket.
 *
 * This method writes a boxed packet to the socket, which is then read by the
 * remote peer using the \ref psock_read_boxed_string method.  This boxed packet
 * contains a tag noting that the following value is a C-string value.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p val must be a valid C-string pointer.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_write_boxed_string)(
    RCPR_SYM(psock)* sock, const char* val)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_psock_valid(sock));
    MODEL_ASSERT(NULL != val);

    /* calculate the string length. */
    size_t len = strlen(val);
    if (len >= UINT32_MAX)
    {
        return ERROR_PSOCK_WRITE_INVALID_SIZE;
    }

    /* attempt to write the type to the socket. */
    status retval = psock_write_raw_uint32(sock, PSOCK_BOXED_TYPE_STRING);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* attempt to write the string length to the socket. */
    uint32_t size = (uint32_t)len;
    retval = psock_write_raw_uint32(sock, size);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* attempt to write the string to the socket. */
    size_t write_size = len;
    retval = sock->write_fn(sock, val, &write_size);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* verify the size. */
    if (len != write_size)
    {
        return ERROR_PSOCK_WRITE_INVALID_SIZE;
    }

    /* success. */
    return STATUS_SUCCESS;
}
