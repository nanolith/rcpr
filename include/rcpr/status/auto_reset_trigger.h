/**
 * \file rcpr/status/auto_reset_trigger.h
 *
 * \brief auto_reset_trigger status codes for RCPR.
 *
 * \copyright 2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/status.h>

/**
 * \brief An attempt was made to register a listener after a listener was
 * already registered.
 */
#define ERROR_AUTO_RESET_TRIGGER_LISTENER_ALREADY_REGISTERED \
    STATUS_CODE(1, RCPR_COMPONENT_AUTO_RESET_TRIGGER, 0x0000)
