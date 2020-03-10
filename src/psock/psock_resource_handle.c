/**
 * \file psock/psock_resource_handle.c
 *
 * \brief Get the \ref resource handle from a \ref psock.
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
 * \brief Given a \ref psock instance, return the resource handle for this
 * \ref psock instance.
 *
 * \param sock          The \ref psock instance from which the resource handle
 *                      is returned.
 *
 * \returns the resource handle for this \ref psock instance.
 */
resource* psock_resource_handle(psock* sock)
{
    return &sock->hdr;
}
