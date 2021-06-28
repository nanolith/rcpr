/**
 * \file rcpr/function_decl.h
 *
 * \brief Function declaration macros for rcpr.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/config.h>
#include <rcpr/macro_tricks.h>

/*
 * With GCC 3.4 and clang, we can force a warning / error if the return value
 * of a function isn't checked.
 */
#if defined(__GNUC__) && defined(__GNUC_MINOR__)
# if (__GNUC__ == 3 && __GNUC_MINOR__ >= 4) || (__GNUC__ > 3)
#  define FN_DECL_MUST_CHECK __attribute__((warn_unused_result))
# endif
#endif

/*
 * For other compilers, skip this check.
 */
#ifndef FN_DECL_MUST_CHECK
# define FN_DECL_MUST_CHECK
#endif

/*
 * The RCPR_UNIQUE_NAME is a UUID-based symbol.
 */
#define RCPR_UNIQUE_NAME u0ec71e88_25af_40aa_8dd9_990d596b60de

/*
 * Symbol expansion and combination macro.
 */
#define RCPR_SYM_COMBINE(x, y, z) rcpr ## _ ## x ## _ ## y ## _ ## z
#define RCPR_SYM_COMBINE1(x, y, z) RCPR_SYM_COMBINE(x, y, z)

/*
 * The RCPR_SYM macro elevates a given symbol to the RCPR namespace.
 */
#define RCPR_SYM(sym) RCPR_SYM_COMBINE1(RCPR_UNIQUE_NAME, RCPR_VERSION_SYM, sym)

/**
 * Begin an export section.
 */
#define RCPR_BEGIN_EXPORT \
    _Pragma("GCC diagnostic push") \
    _Pragma("GCC diagnostic ignored \"-Wunused-function\"")

/**
 * End an export section.
 */
#define RCPR_END_EXPORT \
    _Pragma("GCC diagnostic pop")
