/**
 * \file message/message_return_address.c
 *
 * \brief Return the return address of a message.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "message_internal.h"

/**
 * \brief Given a \ref message instance, return the return \ref mailbox_address
 * associated with it.
 *
 * \param msg           The \ref message instance from which the return \ref
 *                      mailbox_address is returned.
 *
 * \returns the return \ref mailbox_address or MESSAGE_ADDRESS_NONE if there is
 * not a return address.
 */
mailbox_address
message_return_address(const message* msg)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(prop_message_valid(msg));

    return msg->returnaddr;
}
