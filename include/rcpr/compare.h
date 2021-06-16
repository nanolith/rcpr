/**
 * \file rcpr/compare.h
 *
 * \brief Comparison type and helper functions.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/function_decl.h>
#include <rcpr/resource.h>

/* C++ compatibility. */
# ifdef    __cplusplus
extern "C" {
# endif /* __cplusplus */

/**
 * \brief Comparison results.
 */
typedef enum RCPR_SYM(rcpr_comparison_result)
{
    RCPR_COMPARE_LT = -1,
    RCPR_COMPARE_EQ =  0,
    RCPR_COMPARE_GT =  1,
} RCPR_SYM(rcpr_comparison_result);

/**
 * \brief Comparison function type for comparing two resources.
 *
 * \param context       Context data to be passed to the comparison function.
 * \param lhs           The left-hand side of the comparison.
 * \param rhs           The right-hand side of the comparison.
 *
 * \returns an integer value representing the comparison result.
 *      - RCPR_COMPARE_LT if \p lhs &lt; \p rhs.
 *      - RCPR_COMPARE_EQ if \p lhs == \p rhs.
 *      - RCPR_COMPARE_GT if \p lhs &gt; \p rhs.
 */
typedef RCPR_SYM(rcpr_comparison_result) (*RCPR_SYM(compare_fn))(
    void* context, const void* lhs, const void* rhs);
 
/**
 * \brief Given a resource, return the key for a resource.
 *
 * \param context       Context data to be passed to the accessor function.
 * \param r             The resource.
 *
 * \returns the key for the resource.
 */
typedef const void* (*RCPR_SYM(compare_key_fn))(
    void* context, const RCPR_SYM(resource)* r);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define RCPR_IMPORT_compare_as(sym) \
    typedef RCPR_SYM(rcpr_comparison_result) \
        sym ## _ ## rcpr_comparison_result; \
    typedef RCPR_SYM(compare_fn) sym ## _ ## compare_fn; \
    typedef RCPR_SYM(compare_key_fn) sym ## _ ## compare_key_fn;

#define RCPR_IMPORT_compare \
    typedef RCPR_SYM(rcpr_comparison_result) rcpr_comparison_result; \
    typedef RCPR_SYM(compare_fn) compare_fn; \
    typedef RCPR_SYM(compare_key_fn) compare_key_fn;

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
