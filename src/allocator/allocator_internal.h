/**
 * \file allocator/allocator_internal.h
 *
 * \brief Internal data types and functions for allocator.
 *
 * \copyright 2020-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource/protected.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct RCPR_SYM(allocator)
{
    RCPR_SYM(resource) hdr;
    void* context;

    RCPR_MODEL_STRUCT_TAG(allocator);
};

/******************************************************************************/
/* Start of private exports.                                                  */
/******************************************************************************/
#define RCPR_IMPORT_allocator_internal \
    RCPR_BEGIN_EXPORT \
    static inline const RCPR_SYM(allocator_vtable)* \
    allocator_vtable_get(RCPR_SYM(allocator)* alloc) \
    { \
        return (const allocator_vtable*)alloc->hdr.vtable; \
    } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
