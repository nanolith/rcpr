/**
 * \file bigint/bigint_internal.h
 *
 * \brief Internal data types and functions for bigint.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/bigint.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <stdbool.h>
#include <stdint.h>

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/* TODO - create a platform-agnostic way to handle fast integer mults. */
typedef uint64_t RCPR_SYM(native_int);

struct RCPR_SYM(bigint)
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(bigint);

    RCPR_SYM(allocator)* a;
    bool sign;
    size_t length;
    RCPR_SYM(native_int)* array;
};

/**
 * \brief Release a \ref bigint instance.
 *
 * \param r             The \ref bigint \ref resource to release.
 *
 * \returns a status code indicating success or failure.
 */
status RCPR_SYM(bigint_release)(RCPR_SYM(resource)* r);

/******************************************************************************/
/* Start of private exports.                                                  */
/******************************************************************************/

#define RCPR_IMPORT_bigint_internal \
    typedef RCPR_SYM(native_int) native_int; \
    static inline status bigint_release( \
        RCPR_SYM(resource)*x) { \
            return RCPR_SYM(bigint_release)(x); } \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
