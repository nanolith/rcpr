/**
 * \file message/message_payload.c
 *
 * \brief Return the payload of a message.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "message_internal.h"

RCPR_IMPORT_resource;

/**
 * \brief Given a \ref message instance, return the payload \ref resource
 * associated with it.
 *
 * \note The ownership of this resource remains with the message, unless the
 * boolean flag, \p xfer is set to true.
 *
 * \param msg           The \ref message instance from which the payload \ref
 *                      resource is returned.
 * \param xfer          If set to true, then ownership is transferred to the
 *                      caller, and the payload for this message is set to NULL
 *                      after it is returned to the caller.
 *
 * \returns the return payload \ref resource, or NULL if the payload \ref
 * resource is not set.
 */
RCPR_SYM(resource)*
message_payload(message* msg, bool xfer)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_message_valid(msg));

    resource* tmp = msg->payload;

    /* if transfer has been requested, then the caller takes ownership. */
    if (xfer)
    {
        msg->payload = NULL;
    }

    return tmp;
}
