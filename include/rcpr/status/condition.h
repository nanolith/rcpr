/**
 * \file rcpr/status/condition.h
 *
 * \brief condition status codes for RCPR.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/status.h>

/**
 * \brief An unknown error has occurred.
 */
#define ERROR_CONDITION_UNKNOWN_ERROR \
    STATUS_CODE(1, RCPR_COMPONENT_MESSAGE, 0x0000)
