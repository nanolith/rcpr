/**
 * \file rcpr/status/stack.h
 *
 * \brief Stack status codes for RCPR.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/status.h>

/**
 * \brief Stack unmapping error.
 */
#define ERROR_STACK_UNMAP \
    STATUS_CODE(1, RCPR_COMPONENT_THREAD, 0x0000)
