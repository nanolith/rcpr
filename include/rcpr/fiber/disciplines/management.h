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
extern const rcpr_uuid FIBER_SCHEDULER_MANAGEMENT_DISCIPLINE;

/**
 * \brief Management discipline yield events.
 */
enum fiber_scheduler_management_discipline_yield_events
{
    /** \brief Receive a management event from the scheduler. */
    FIBER_SCHEDULER_MANAGEMENT_YIELD_EVENT_RECEIVE_EVENT            = 0x0000,
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
};

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
