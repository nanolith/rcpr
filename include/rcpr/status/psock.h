/**
 * \file rcpr/status/psock.h
 *
 * \brief Process Socket library status codes for RCPR.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
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

/**
 * \brief psock read boxed invalid type error.
 */
#define ERROR_PSOCK_READ_BOXED_INVALID_TYPE \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0006)

/**
 * \brief psock read boxed invalid size error.
 */
#define ERROR_PSOCK_READ_BOXED_INVALID_SIZE \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0007)

/**
 * \brief psock kqueue / kevent call failed.
 */
#define ERROR_PSOCK_KEVENT_FAILED \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0008)

/**
 * \brief psock kqueue init failed.
 */
#define ERROR_PSOCK_KQUEUE_FAILED \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0009)

/**
 * \brief An unexpected event occurred when doing a psock read / write.
 */
#define ERROR_PSOCK_UNEXPECTED_EVENT \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x000a)

/**
 * \brief An unsupported psock type was encountered.
 */
#define ERROR_PSOCK_UNSUPPORTED_TYPE \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x000b)

/**
 * \brief This accept returned because it would block and the socket is
 * non-blocking.
 */
#define ERROR_PSOCK_ACCEPT_WOULD_BLOCK \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x000c)

/**
 * \brief This accept returned because of an unspecified error.
 */
#define ERROR_PSOCK_ACCEPT_GENERAL \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x000d)

/**
 * \brief Couldn't create a socket.
 */
#define ERROR_PSOCK_CREATE_FROM_ADDRESS_SOCKET_CREATE \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x000e)

/**
 * \brief Couldn't bind the socket to an address.
 */
#define ERROR_PSOCK_CREATE_FROM_ADDRESS_BIND \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x000f)

/**
 * \brief Couldn't start listening to the socket.
 */
#define ERROR_PSOCK_CREATE_FROM_ADDRESS_LISTEN \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0010)

/**
 * \brief Couldn't close a socket.
 */
#define ERROR_PSOCK_CREATE_FROM_ADDRESS_CLOSE \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0011)

/**
 * \brief EOF encountered on read.
 */
#define ERROR_PSOCK_READ_EOF \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0012)

/**
 * \brief EOF encountered on write.
 */
#define ERROR_PSOCK_WRITE_EOF \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0013)

/**
 * \brief psock epoll_create init failed.
 */
#define ERROR_PSOCK_EPOLL_CREATE_FAILED \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0014)

/**
 * \brief psock epoll_ctl call failed.
 */
#define ERROR_PSOCK_EPOLL_CTL_FAILED \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0015)

/**
 * \brief psock epoll_wait call failed.
 */
#define ERROR_PSOCK_EPOLL_WAIT_FAILED \
    STATUS_CODE(1, RCPR_COMPONENT_PSOCK, 0x0016)
