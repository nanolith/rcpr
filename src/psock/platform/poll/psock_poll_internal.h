/**
 * \file psock/platform/poll/psock_poll_internal.h
 *
 * \brief Internal data types and functions for psock's async poll impl.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <poll.h>
#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/psock.h>
#include <rcpr/resource.h>

#include "../../psock_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

#define POLL_EVENT_SIZE_INCREMENT       1024

typedef struct psock_io_poll_context psock_io_poll_context;

struct psock_io_poll_context
{
    resource hdr;

    MODEL_STRUCT_TAG(psock_io_poll_context);

    allocator* alloc;
    resource discipline_cache;
    fiber_scheduler* sched;
    size_t poll_max;
    size_t poll_curr;
    struct pollfd* poll_events;
    fiber** poll_fibers;
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
