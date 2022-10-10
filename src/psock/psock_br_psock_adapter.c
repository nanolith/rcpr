/**
 * \file psock/psock_br_psock_adapter.c
 *
 * \brief Get the \ref psock adapter for this \ref psock_br instance.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "psock_internal.h"

/**
 * \brief Given a \ref psock_br instance, returned the wrapped \ref psock
 * instance pointer that can be used to perform buffered reads using \ref psock
 * methods.
 *
 * \param br            The \ref psock_br instance from which the \ref psock
 *                      adapter instance is returned.
 *
 * \returns the \ref psock adapter instance for this \ref psock_br instance.
 */
RCPR_SYM(psock)*
RCPR_SYM(psock_br_psock_adapter)(
    RCPR_SYM(psock_br)* br)
{
    return &br->hdr;
}
