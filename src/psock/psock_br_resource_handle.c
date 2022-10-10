/**
 * \file psock/psock_br_resource_handle.c
 *
 * \brief Get the \ref resource handle from a \ref psock_br instance.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "psock_internal.h"

/**
 * \brief Given a \ref psock_br instance, return the resource handle for this
 * \ref psock_br instance.
 *
 * \param br            The \ref psock_br instance from which the resource
 *                      handle is returned.
 *
 * \returns the resource handle for this \ref psock_br instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(psock_br_resource_handle)(
    RCPR_SYM(psock_br)* br)
{
    return &br->hdr.hdr;
}
