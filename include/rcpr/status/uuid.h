/**
 * \file rcpr/status/uuid.h
 *
 * \brief uuid status codes for RCPR.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/status.h>

/**
 * \brief An attempt to parse a UUID string failed.
 */
#define ERROR_UUID_PARSING_FAILED \
    STATUS_CODE(1, RCPR_COMPONENT_UUID, 0x0000)
