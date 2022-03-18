/**
 * \file rcpr/control.h
 *
 * \brief Helper macros to reduce boilerplate for common control-flow patterns
 * in resource-oriented programming.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/config.h>
#include <rcpr/macro_tricks.h>
#include <rcpr/status.h>

/* make this header C++ friendly. */
#ifdef __cplusplus
extern "C" {
#endif /*__cplusplus*/

/**
 * \brief Place this at the beginning of a function using these macros to
 * declare the retval and release_retval variables.
 */
#define CONTROL_PREAMBLE \
    status retval, release_retval; \
    (void)retval; (void)release_retval; \
    REQUIRE_SEMICOLON_HERE

/**
 * \brief Try to perform the given operation, which must return a status code.
 * If this operation fails, then jump to the given label.
 */
#define TRY_OR_FAIL(op, label) \
    retval = (op); \
    if (STATUS_SUCCESS != retval) \
    { \
    goto label; \
    } \
    REQUIRE_SEMICOLON_HERE

/**
 * \brief Try to perform the given cleanup operation. If it fails, cascade the
 * failure code into retval, ensuring that all failures are checked, even if
 * cascading failures clobber previous failures.
 */
#define CLEANUP_OR_CASCADE(op) \
    release_retval = (op); \
    if (STATUS_SUCCESS != release_retval) \
    { \
        retval = release_retval; \
    } \
    REQUIRE_SEMICOLON_HERE

/* make this header C++ friendly. */
#ifdef __cplusplus
}
#endif /*__cplusplus*/
