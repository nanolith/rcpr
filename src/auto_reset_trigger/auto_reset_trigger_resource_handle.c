/**
 * \file auto_reset_trigger/auto_reset_trigger_resource_handle.c
 *
 * \brief Return the \ref resource handle for this \ref auto_reset_trigger
 * instance.
 *
 * \copyright 2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "auto_reset_trigger_internal.h"

/**
 * \brief Given a \ref auto_reset_trigger instance, return the resource handle
 * for this \ref auto_reset_trigger instance.
 *
 * \param trigger           The \ref auto_reset_trigger from which this resource
 *                          handle is returned.
 *
 * \returns the resource handle for this \ref auto_reset_trigger instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(auto_reset_trigger_resource_handle)(
    RCPR_SYM(auto_reset_trigger)* trigger)
{
    return &trigger->hdr;
}
