/**
 * \file rcpr/model_assert.h
 *
 * \brief Model checking assertions.
 *
 * \copyright 2020-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/macro_tricks.h>
#include <rcpr/shadow/allocator.h>
#include <rcpr/shadow/model_tag.h>
#include <rcpr/shadow/valid_range.h>

#if CBMC
# define RCPR_MODEL_ASSERT(x) __CPROVER_assert((x), #x); REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_ASSUME(x) __CPROVER_assume((x)); REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_CHECK_OBJECT_READ(x, size) \
    __CPROVER_assert(__CPROVER_r_ok((x), (size)), #x " read " #size); \
    REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_CHECK_OBJECT_WRITE(x, size) \
    __CPROVER_assert(__CPROVER_w_ok((x), (size)), #x " write " #size); \
    REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_CHECK_OBJECT_RW(x, size) \
    __CPROVER_assert(__CPROVER_rw_ok((x), (size)), #x " r/w " #size); \
    REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_CHECK_IS_STRING(x) \
    __CPROVER_assert(__CPROVER_is_zero_string((x)), #x " is string"); \
    REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_CHECK_STRING_BUFFER_SIZE(x, size) \
    __CPROVER_assert(__CPROVER_buffer_size((x)) >= size); \
    REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_EXEMPT(x)
# define RCPR_MODEL_ONLY(x) (x)
#else
# define RCPR_MODEL_ASSERT(x) REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_ASSUME(x) REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_CHECK_OBJECT_READ(x, size) REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_CHECK_OBJECT_WRITE(x, size) REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_CHECK_OBJECT_RW(x, size) REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_CHECK_IS_STRING(x) REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_CHECK_STRING_BUFFER_SIZE(x, size) REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_EXEMPT(x) (x)
# define RCPR_MODEL_ONLY(x)
#endif
