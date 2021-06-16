/**
 * \file psock/platform/epoll/psock_epoll_internal.h
 *
 * \brief Internal data types and functions for psock's async epoll impl.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/psock.h>
#include <rcpr/resource.h>
#include <sys/epoll.h>

#include "../../psock_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

#define MAX_EPOLL_OUTPUTS      1024

typedef struct psock_io_epoll_context psock_io_epoll_context;

struct psock_io_epoll_context
{
    RCPR_SYM(resource) hdr;

    MODEL_STRUCT_TAG(psock_io_epoll_context);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(resource) discipline_cache;
    RCPR_SYM(fiber_scheduler)* sched;
    int ep;
    int outputs;
    struct epoll_event epoll_outputs[MAX_EPOLL_OUTPUTS];
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
