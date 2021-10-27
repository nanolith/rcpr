/**
 * \file rcpr/model_tag.h
 *
 * \brief Model tagging macros for data structures.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/macro_tricks.h>
#include <rcpr/shadow/allocator.h>
#include <rcpr/shadow/model_tag.h>

#if CBMC
# define RCPR_MODEL_STRUCT_TAG_REF(name) \
    model_struct_tag_ ## name
# define RCPR_MODEL_STRUCT_TAG(name) \
    int RCPR_MODEL_STRUCT_TAG_REF(name)
# define RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(name) \
    model_global_struct_tag_ ## name
# define RCPR_MODEL_STRUCT_TAG_GLOBAL_INIT(name) \
    int nondet_ ## name ## _tag(); \
    RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(name) = nondet_ ## name ## _tag(); \
    RCPR_MODEL_ASSUME(RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(name) != 0)
# define RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(name) \
    extern int RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(name)
# define RCPR_MODEL_STRUCT_TAG_INIT(var, name) \
    var = RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(name)
# define RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(var, name) \
    RCPR_MODEL_ASSERT(var == RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(name))
# define RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(var, name) \
    RCPR_MODEL_ASSERT(var != RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(name))
#else
# define RCPR_MODEL_STRUCT_TAG_REF(name) \
    REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_STRUCT_TAG(name) \
    REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_STRUCT_TAG_GLOBAL_REF(name) \
    REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_STRUCT_TAG_GLOBAL_INIT(name) \
    REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(name) \
    REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_STRUCT_TAG_INIT(var, name) \
    REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_ASSERT_STRUCT_TAG_INITIALIZED(var, name) \
    REQUIRE_SEMICOLON_HERE
# define RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(var, name) \
    REQUIRE_SEMICOLON_HERE
#endif
