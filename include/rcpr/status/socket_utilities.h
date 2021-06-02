/**
 * \file rcpr/status/socket_utilities.h
 *
 * \brief Socket utilities status codes for RCPR.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/status.h>

/**
 * \brief Socket pair creation error.
 */
#define ERROR_SOCKET_UTILITIES_SOCKETPAIR_FAILURE \
    STATUS_CODE(1, RCPR_COMPONENT_SOCKET_UTILITIES, 0x0000)

/**
 * \brief Socket utility set non-blocking error.
 */
#define ERROR_SOCKET_UTILITIES_SET_NONBLOCK_FAILURE \
    STATUS_CODE(1, RCPR_COMPONENT_SOCKET_UTILITIES, 0x0001)
