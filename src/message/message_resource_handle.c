/**
 * \file message/message_resource_handle.c
 *
 * \brief Return the resource handle of a message instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "message_internal.h"

RCPR_IMPORT_message;
RCPR_IMPORT_message_internal;

/**
 * \brief Given a \ref message instance, return the resource handle for this
 * \ref message instance.
 *
 * \param msg           The \ref message instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref message instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(message_resource_handle)(
    RCPR_SYM(message)* msg)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_message_valid(msg));

    return &msg->hdr;
}
