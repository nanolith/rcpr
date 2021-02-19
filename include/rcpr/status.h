/**
 * \file rcpr/status.h
 *
 * \brief Status codes for RCPR.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/component.h>
#include <rcpr/status/general.h>
#include <rcpr/status/psock.h>
#include <rcpr/status/socket_utilities.h>
#include <rcpr/status/stack.h>
#include <rcpr/status/thread.h>
#include <stdint.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/**
 * \brief Status is a 32-bit integer.
 */
typedef int32_t status;

/**
 * \brief The operation completed successfully.
 */
#define STATUS_SUCCESS                                              0x00000000

/**
 * \brief Build a status from a one bit error flag, a 16-bit component, and a
 * 15-bit reason code.
 */
#define STATUS_CODE(error_flag, component_code, reason_code) \
    ((((error_flag) ==   1 ? -1 : 0) &     ~0x7FFFFFFF)                 | \
    (((component_code)      &               0x0000FFFF)     <<      15) | \
    (((reason_code)         &               0x00007FFF)     <<       0))

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
