/**
 * \file rcpr/status/psock.h
 *
 * \brief Process Socket library status codes for RCPR.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/status.h>

/**
 * \brief General error from a psock read.
 */
#define ERROR_PSOCK_READ_GENERAL \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0000)

/**
 * \brief General error from a psock write.
 */
#define ERROR_PSOCK_WRITE_GENERAL \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0001)

/**
 * \brief This read returned because it would block and the socket is
 * non-blocking.
 */
#define ERROR_PSOCK_READ_WOULD_BLOCK \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0002)

/**
 * \brief This write returned because it would block and the socket is
 * non-blocking.
 */
#define ERROR_PSOCK_WRITE_WOULD_BLOCK \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0003)

/**
 * \brief psock read invalid size error.
 */
#define ERROR_PSOCK_READ_INVALID_SIZE \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0004)

/**
 * \brief psock write invalid size error.
 */
#define ERROR_PSOCK_WRITE_INVALID_SIZE \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0005)
