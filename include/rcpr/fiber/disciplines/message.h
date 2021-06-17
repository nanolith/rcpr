/**
 * \file rcpr/fiber/disciplines/message.h
 *
 * \brief The RCPR message fiber scheduler discipline.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/fiber.h>
#include <rcpr/uuid.h>

/* C++ compatibility. */
# ifdef    __cplusplus
extern "C" {
# endif /* __cplusplus */

/**
 * \brief The message fiber scheduler discipline.
 */
extern const RCPR_SYM(rcpr_uuid) FIBER_SCHEDULER_MESSAGE_DISCIPLINE;

/**
 * \brief message discipline yield events.
 */
enum fiber_scheduler_message_discipline_yield_events
{
    /** \brief Create a mailbox. */
    FIBER_SCHEDULER_MESSAGE_YIELD_EVENT_MAILBOX_CREATE              = 0x0000,

    /** \brief Close a mailbox. */
    FIBER_SCHEDULER_MESSAGE_YIELD_EVENT_MAILBOX_CLOSE               = 0x0001,

    /** \brief Send a message to a mailbox. */
    FIBER_SCHEDULER_MESSAGE_YIELD_EVENT_MESSAGE_SEND                = 0x0002,

    /** \brief Receive a message from a mailbox. */
    FIBER_SCHEDULER_MESSAGE_YIELD_EVENT_MESSAGE_RECEIVE             = 0x0003,
};

/**
 * \brief The message discipline resume events.
 */
enum fiber_scheduler_message_discipline_resume_events
{
    /** \brief Success response from creating a mailbox. */
    FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MAILBOX_CREATE_SUCCESS     = 0x0000,

    /** \brief Fail response from creating a mailbox. */
    FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MAILBOX_CREATE_FAILURE     = 0x0001,

    /** \brief Success response from closing a mailbox. */
    FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MAILBOX_CLOSE              = 0x0002,

    /** \brief Success response from sending a message to a mailbox. */
    FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_SEND_SUCCESS       = 0x0003,

    /** \brief Fail response from sending a message to a mailbox. */
    FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_SEND_FAILURE       = 0x0004,

    /** \brief Success response from receiving a message from a mailbox. */
    FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_RECEIVE_SUCCESS    = 0x0005,

    /** \brief Fail response from receiving a message from a mailbox. */
    FIBER_SCHEDULER_MESSAGE_RESUME_EVENT_MESSAGE_RECEIVE_FAILURE    = 0x0006,
};

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
