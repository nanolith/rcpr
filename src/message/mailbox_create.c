/**
 * \file message/mailbox_create.c
 *
 * \brief Create a mailbox address using the messaging discipline.
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
 * \brief Create a \ref mailbox_address using the messaging discipline.
 *
 * \param addr          Pointer to the \ref mailbox_address value to receive
 *                      this address.
 * \param msgdisc       Pointer to the messaging discipline.
 *
 * \note This \ref mailbox_address is a unique value that references a mailbox
 * created by the messaging discipline.  This is an abstract resource that must
 * be released by calling \ref mailbox_close when it is no longer needed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(mailbox_create)(
    RCPR_SYM(mailbox_address)* addr,
    RCPR_SYM(fiber_scheduler_discipline)* msgdisc)
{
    status retval;
    const rcpr_uuid* resume_id;
    int resume_event;
    void* resume_param;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != addr);
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(msgdisc));

    retval =
        fiber_discipline_yield(
            msgdisc, FIBER_SCHEDULER_MESSAGE_YIELD_EVENT_MAILBOX_CREATE, NULL,
            &resume_id, &resume_event, &resume_param);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* TODO - add support for out-of-band events. */

    *addr = (mailbox_address)(resume_param);

    return STATUS_SUCCESS;
}
