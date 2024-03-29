/**
 * \file rcpr/model_assert.h
 *
 * \brief Model checking assertions.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/shadow/allocator.h>
#include <rcpr/shadow/model_tag.h>
#include <rcpr/shadow/valid_range.h>

#if CBMC
# define RCPR_MODEL_ASSERT(x)  __CPROVER_assert((x), #x)
# define RCPR_MODEL_ASSUME(x)  __CPROVER_assume((x))
# define RCPR_MODEL_EXEMPT(x)
# define RCPR_MODEL_ONLY(x) (x)
# ifndef CBMC_NO_MALLOC_OVERRIDE
# define malloc cbmc_malloc
# define free cbmc_free
# endif
#else
# define RCPR_MODEL_ASSERT(x)
# define RCPR_MODEL_ASSUME(x)
# define RCPR_MODEL_EXEMPT(x) (x)
# define RCPR_MODEL_ONLY(x)
#endif
