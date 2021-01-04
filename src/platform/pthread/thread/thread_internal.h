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

struct thread
{
    resource hdr;

    MODEL_STRUCT_TAG(thread);

    allocator* alloc;
    pthread_t thread;
    void* context;
    thread_fn fn;
    volatile bool running;
    status exit_code;
};

struct thread_mutex
{
    resource hdr;

    MODEL_STRUCT_TAG(thread_mutex);

    allocator* alloc;
    pthread_mutex_t mutex;
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
