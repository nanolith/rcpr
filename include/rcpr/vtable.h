/**
 * \file rcpr/vtable.h
 *
 * \brief Helpers for vtable related mapping.
 *
 * \copyright 2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/function_decl.h>
#include <stdbool.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/* externals provided by linker. */
extern const void* __start_rcpr_vtable;
extern const void* __stop_rcpr_vtable;

/**
 * \brief The RCPR_VTABLE attribute macro is used when specifying that a given
 * vtable data structure should be stored in the rcpr_vtable section of the
 * binary.
 *
 * Since runtime checking of vtable pointers will be enforced in the future,
 * this attribute ensures that the given vtable is in the correct section.
 */
#define RCPR_VTABLE \
    static const \
    __attribute__ ((section ("rcpr_vtable")))

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define __INTERNAL_RCPR_IMPORT_vtable_sym(sym) \
    RCPR_BEGIN_EXPORT \
    static inline bool sym ## vtable_range_valid(\
        const void* ptr) { \
            if ( \
                (ptrdiff_t)(ptr) >= (ptrdiff_t)(&__start_rcpr_vtable) \
             && (ptrdiff_t)(ptr) <= (ptrdiff_t)(&__stop_rcpr_vtable)) \
            { \
                return true; \
            } \
            return false; } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE
#define RCPR_IMPORT_vtable_as(sym) \
    __INTERNAL_RCPR_IMPORT_vtable_sym(sym ## _)
#define RCPR_IMPORT_vtable \
    __INTERNAL_RCPR_IMPORT_vtable_sym()

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
