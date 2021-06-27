/**
 * \file platform/pthread/thread/thread_internal.h
 *
 * \brief Internal data types and functions for pthread thread.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/model_assert.h>
#include <rcpr/thread.h>
#include <pthread.h>
#include <stdbool.h>

#include "../../../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct RCPR_SYM(thread)
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(thread);

    RCPR_SYM(allocator)* alloc;
    pthread_t thread;
    void* context;
    RCPR_SYM(thread_fn) fn;
    volatile bool running;
    status exit_code;
};

struct RCPR_SYM(thread_mutex_lock)
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(thread_mutex_lock);

    RCPR_SYM(thread_mutex)* parent;
};

struct RCPR_SYM(thread_mutex)
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(thread_mutex);

    RCPR_SYM(allocator)* alloc;
    pthread_mutex_t mutex;
    RCPR_SYM(thread_mutex_lock) child;
};

struct RCPR_SYM(thread_cond)
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(thread_cond);

    RCPR_SYM(allocator)* alloc;
    pthread_cond_t cond;
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
