/**
 * \file psock/platform/kqueue/psock_kqueue_internal.h
 *
 * \brief Internal data types and functions for psock's async kqueue impl.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/psock.h>
#include <rcpr/resource.h>
#include <sys/types.h>
#include <sys/event.h>

#include "../../psock_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

#define MAX_KEVENT_INPUTS       1024
#define MAX_KEVENT_OUTPUTS      1024

typedef struct psock_io_kqueue_context psock_io_kqueue_context;

struct psock_io_kqueue_context
{
    RCPR_SYM(resource) hdr;

    RCPR_MODEL_STRUCT_TAG(psock_io_kqueue_context);

    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(resource) discipline_cache;
    RCPR_SYM(fiber_scheduler)* sched;
    int kq;
    int inputs;
    struct kevent kevent_inputs[MAX_KEVENT_INPUTS];
    int outputs;
    struct kevent kevent_outputs[MAX_KEVENT_OUTPUTS];
};

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
