/**
 * \file message/mailbox_close.c
 *
 * \brief Close a mailbox address using the messaging discipline.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "message_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_message;
RCPR_IMPORT_uuid;

/**
 * \brief Close a \ref mailbox_address using the messaging discipline.
 *
 * \param addr          The \ref mailbox_address to close.
 * \param msgdisc       Pointer to the messaging discipline.
 *
 * \note The \ref mailbox_address pointed to by \p addr will be closed.  No
 * other messages can be sent to this address once it has been closed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(mailbox_close)(
    RCPR_SYM(mailbox_address) addr,
    RCPR_SYM(fiber_scheduler_discipline)* msgdisc)
{
    status retval;
    const rcpr_uuid* resume_id;
    int resume_event;
    void* resume_param;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(addr > 0);
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(msgdisc));

    retval =
        fiber_discipline_yield(
            msgdisc, FIBER_SCHEDULER_MESSAGE_YIELD_EVENT_MAILBOX_CLOSE,
            (void*)(ptrdiff_t)addr, &resume_id, &resume_event, &resume_param);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* TODO - add support for out-of-band events. */

    return STATUS_SUCCESS;
}
