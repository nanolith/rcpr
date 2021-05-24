/**
 * \file epoll/psock_fiber_scheduler_discipline_context_create.c
 *
 * \brief Create the fiber scheduler discipline for epoll event management.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "../../psock_internal.h"

/**
 * \brief Create a platform-specific fiber scheduler discipline context for
 * psock I/O.
 *
 * \param context       Pointer to receive the context pointer on success.
 * \param sched         The fiber scheduler to which this discipline will
 *                      belong.
 * \param alloc         The allocator to use to create this resource.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status psock_fiber_scheduler_discipline_context_create(
    resource** context, fiber_scheduler* sched, allocator* alloc)
{
    /* TODO - fill out stub. */
    (void)context;
    (void)sched;
    (void)alloc;

    return -1;
}
