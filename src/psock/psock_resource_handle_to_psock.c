/**
 * \file psock/psock_resource_handle_to_psock.c
 *
 * \brief Downcast a \ref resource handle to a \ref psock.
 *
 * \copyright 2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_psock;

/**
 * \brief Given a \ref resource for a \ref psock instance, get the \ref psock
 * instance.
 *
 * \note that this MUST be a \ref psock \ref resource, or bad things can happen.
 * This cast should be model checked, and any function using this cast should
 * ensure that its contract specifies that the \ref resource is a \ref psock.
 *
 * \param r             The \ref resource to downcast to a \ref psock.
 *
 * \returns the \ref psock instance for this \ref resource.
 */
RCPR_SYM(psock)*
RCPR_SYM(psock_resource_handle_to_psock)(
    RCPR_SYM(resource)* r)
{
    psock* sock = (psock*)r;

    RCPR_MODEL_ASSERT(prop_psock_valid(sock));

    return sock;
}
