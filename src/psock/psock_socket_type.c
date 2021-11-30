/**
 * \file psock/psock_socket_type.c
 *
 * \brief Get the socket type of a \ref psock instance.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

/**
 * \brief Given a \ref psock instance, return the socket type for this
 * \ref psock instance, if applicable.
 *
 * \param sock          The \ref psock instance from which this socket type is
 *                      returned.
 * \returns the socket type for this \ref psock instance.
 */
RCPR_SYM(socket_type)
RCPR_SYM(psock_socket_type)(
    RCPR_SYM(psock)* sock)
{
    return sock->socktype;
}
