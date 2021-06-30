/**
 * \file rcpr/fiber/disciplines/management.h
 *
 * \brief The RCPR fiber management discipline.
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
 * \brief The fiber management discipline ID.
 */
extern const RCPR_SYM(rcpr_uuid) FIBER_SCHEDULER_MANAGEMENT_DISCIPLINE;

/**
 * \brief Management discipline yield events.
 */
enum fiber_scheduler_management_discipline_yield_events
{
    /** \brief Receive a management event from the scheduler. */
    FIBER_SCHEDULER_MANAGEMENT_YIELD_EVENT_RECEIVE_EVENT            = 0x0000,

    /** \brief Send a quiesce request to the given fiber. */
    FIBER_SCHEDULER_MANAGEMENT_YIELD_EVENT_QUIESCE_REQUEST          = 0x0002,

    /** \brief Send a termination request to the given fiber. */
    FIBER_SCHEDULER_MANAGEMENT_YIELD_EVENT_TERMINATION_REQUEST      = 0x0003,

    /** \brief Send a quiesce request to all fibers. */
    FIBER_SCHEDULER_MANAGEMENT_YIELD_EVENT_QUIESCE_ALL_REQUEST      = 0x0004,

    /** \brief Send a termination request to all fibers. */
    FIBER_SCHEDULER_MANAGEMENT_YIELD_EVENT_TERMINATION_ALL_REQUEST  = 0x0005,
};

/**
 * \brief Management discipline resume events.
 */
enum fiber_scheduler_management_discipline_resume_events
{
    /** \brief This event occurs when a new fiber is added. */
    FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_FIBER_ADD               = 0x0000,

    /** \brief This event occurs when a fiber stops. */
    FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_FIBER_STOP              = 0x0001,

    /** \brief This occurs when the fiber has been requested to quiesce. */
    FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_QUIESCE_REQUEST         = 0x0002,

    /** \brief This occurs when the fiber has been requested to terminate. */
    FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_TERMINATION_REQUEST     = 0x0003,

    /** \brief A request was sent to the management discipline; param is the
     * result.*/
    FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_REQUEST_RESULT          = 0x0004,
};

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
