/**
 * \file rcpr/fiber/disciplines/condition.h
 *
 * \brief The RCPR condition fiber scheduler discipline.
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
 * \brief The condition fiber scheduler discipline.
 */
extern const RCPR_SYM(rcpr_uuid) FIBER_SCHEDULER_CONDITION_DISCIPLINE;

/**
 * \brief The condition discipline yield events.
 */
enum fiber_scheduler_condition_discipline_yield_events
{
    /** \brief Create a condition barrier. */
    FIBER_SCHEDULER_CONDITION_YIELD_EVENT_CREATE                    = 0x0000,

    /** \brief Close a condition barrier. */
    FIBER_SCHEDULER_CONDITION_YIELD_EVENT_CLOSE                     = 0x0001,

    /** \brief Wait on a condition barrier. */
    FIBER_SCHEDULER_CONDITION_YIELD_EVENT_COND_WAIT                 = 0x0002,

    /** \brief Notify one fiber to restart. */
    FIBER_SCHEDULER_CONDITION_YIELD_EVENT_NOTIFY_ONE                = 0x0003,

    /** \brief Notify all fibers to restart. */
    FIBER_SCHEDULER_CONDITION_YIELD_EVENT_NOTIFY_ALL                = 0x0004,
};

/**
 * \brief The condition discipline resume events.
 */
enum fiber_scheduler_condition_discipline_resume_events
{
    /** \brief This event occurs when a condition create operation completed
     * successfully.
     */
    FIBER_SCHEDULER_CONDITION_RESUME_EVENT_CREATE_SUCCESS          = 0x0000,

    /** \brief This event occurs when a condition create operation failed. */
    FIBER_SCHEDULER_CONDITION_RESUME_EVENT_CREATE_FAILURE          = 0x0001,

    /** \brief This event occurs when a condition close operation completed
     * successfully.
     */
    FIBER_SCHEDULER_CONDITION_RESUME_EVENT_CLOSE_SUCCESS           = 0x0002,

    /** \brief This event occurs when a condition close operation failed. */
    FIBER_SCHEDULER_CONDITION_RESUME_EVENT_CLOSE_FAILURE           = 0x0003,

    /** \brief This event occurs when a condition wait operation completed
     * successfully.
     */
    FIBER_SCHEDULER_CONDITION_RESUME_EVENT_WAIT_SUCCESS            = 0x0004,

    /** \brief This event occurs when a condition wait operation failed. */
    FIBER_SCHEDULER_CONDITION_RESUME_EVENT_WAIT_FAILURE            = 0x0005,

    /** \brief This event occurs when a condition notify operation completed
     * successfully.
     */
    FIBER_SCHEDULER_CONDITION_RESUME_EVENT_NOTIFY_SUCCESS          = 0x0006,

    /** \brief This event occurs when a condition notify operation failed. */
    FIBER_SCHEDULER_CONDITION_RESUME_EVENT_NOTIFY_FAILURE          = 0x0007,
};

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
