/**
 * \file rcpr/status/message.h
 *
 * \brief message status codes for RCPR.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/status.h>

/**
 * \brief Two threads are attempting to block on the same mailbox.
 */
#define ERROR_MESSAGE_ALREADY_BLOCKED \
    STATUS_CODE(1, RCPR_COMPONENT_MESSAGE, 0x0000)

/**
 * \brief An unknown error has occurred.
 */
#define ERROR_MESSAGE_UNKNOWN_ERROR \
    STATUS_CODE(1, RCPR_COMPONENT_MESSAGE, 0x0001)
