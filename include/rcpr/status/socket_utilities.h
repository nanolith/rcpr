/**
 * \file rcpr/status/socket_utilities.h
 *
 * \brief Socket utilities status codes for RCPR.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/status.h>

/**
 * \brief Out-of-memory error.
 */
#define ERROR_SOCKET_UTILITIES_SOCKETPAIR_FAILURE \
    STATUS_CODE(1, RCPR_COMPONENT_SOCKET_UTILITIES, 0x0000)
