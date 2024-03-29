/**
 * \file psock/psock_read_boxed_bool.c
 *
 * \brief Read a boxed Boolean value from a \ref psock instance.
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
 * \brief Read a boxed packet from the given \ref psock instance that was
 * written to the remote end of this socket by the peer calling \ref
 * psock_write_boxed_bool.
 *
 * \param sock          Pointer to the \ref psock pointer on which this
 *                      operation occurs.
 * \param val           Pointer to the value to be set based on a successful I/O
 *                      operation.
 *
 * The \ref psock_write_boxed_bool method writes a boxed packet to the socket,
 * which is then read by this function on the other end of the socket.  This
 * boxed packet contains a tag noting that the following value is a boolean
 * value. No matter the platform of either peer, the value will be converted to
 * or from native ordering.
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
 *      - On success, \p val is set to the boolean value read from the socket
 *        and unboxed.
 *      - On failure, \p val is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_read_boxed_bool)(
    RCPR_SYM(psock)* sock, bool* val)
{
    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != val);

    /* attempt to read the type from the socket. */
    uint32_t type = 0U;
    status retval = psock_read_raw_uint32(sock, &type);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* verify that the type matches what we expect. */
    if (PSOCK_BOXED_TYPE_BOOL != type)
    {
        return ERROR_PSOCK_READ_BOXED_INVALID_TYPE;
    }

    /* attempt to read the data value from the socket. */
    return psock_read_raw_bool(sock, val);
}
