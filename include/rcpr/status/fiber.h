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
