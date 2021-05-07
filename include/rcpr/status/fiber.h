/**
 * \file rcpr/status/fiber.h
 *
 * \brief Fiber status codes for RCPR.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/status.h>

/**
 * \brief The fiber scheduler callback state is invalid.
 */
#define ERROR_FIBER_SCHEDULER_CALLBACK_STATE \
    STATUS_CODE(1, RCPR_COMPONENT_FIBER, 0x0000)

/**
 * \brief The fiber scheduler could not find a requested discipline.
 */
#define ERROR_FIBER_SCHEDULER_DISCIPLINE_NOT_FOUND \
    STATUS_CODE(1, RCPR_COMPONENT_FIBER, 0x0001)

/**
 * \brief The fiber scheduler is not disciplined, and attempt was made to use a
 * disciplined feature.
 */
#define ERROR_FIBER_SCHEDULER_NOT_DISCIPLINED \
    STATUS_CODE(1, RCPR_COMPONENT_FIBER, 0x0002)

/**
 * \brief A discipline with the same uuid already exists in this fiber scheduler
 * instance.
 */
#define ERROR_FIBER_SCHEDULER_DUPLICATE_DISCIPLINE_ID \
    STATUS_CODE(1, RCPR_COMPONENT_FIBER, 0x0003)

/**
 * \brief An attempt was made to add a discipline that is already owned to a
 * fiber scheduler.
 */
#define ERROR_FIBER_SCHEDULER_DISCIPLINE_ALREADY_OWNED \
    STATUS_CODE(1, RCPR_COMPONENT_FIBER, 0x0004)

/**
 * \brief A bad yield event was encountered.
 */
#define ERROR_FIBER_SCHEDULER_BAD_YIELD_EVENT \
    STATUS_CODE(1, RCPR_COMPONENT_FIBER, 0x0005)

/**
 * \brief The run queue is exhausted, and no idle fiber has been set.
 */
#define ERROR_FIBER_SCHEDULER_EXHAUSTED \
    STATUS_CODE(1, RCPR_COMPONENT_FIBER, 0x0006)
