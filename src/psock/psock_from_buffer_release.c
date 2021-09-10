/**
 * \file psock/psock_from_buffer_release.c
 *
 * \brief Release a \ref psock instance created from a buffer.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;

/**
 * \brief Release a psock_from_buffer resource.
 *
 * \param r             Pointer to the psock_from_buffer resource to be
 *                      released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code on failure.
 */
status RCPR_SYM(psock_from_buffer_release)(RCPR_SYM(resource)* r)
{
    int retval = STATUS_SUCCESS;
    int input_buffer_retval = STATUS_SUCCESS;
    int output_buffer_retval = STATUS_SUCCESS;
    int output_queue_retval = STATUS_SUCCESS;

    /* reverse type erasure. */
    psock_from_buffer* ps = (psock_from_buffer*)r;

    /* cache the allocator. */
    allocator* a = ps->hdr.alloc;

    /* if the input buffer is set, reclaim it. */
    if (NULL != ps->input_buffer)
    {
        memset(ps->input_buffer, 0, ps->input_buffer_size);
        input_buffer_retval = allocator_reclaim(a, ps->input_buffer);
    }

    /* if the output buffer is set, reclaim it. */
    if (NULL != ps->output_curr_buffer)
    {
        memset(ps->output_curr_buffer, 0, ps->output_buffer_size);
        output_buffer_retval = allocator_reclaim(a, ps->output_curr_buffer);
    }

    /* if the output queue is set, release it. */
    if (NULL != ps->output_queue)
    {
        output_queue_retval =
            resource_release(slist_resource_handle(ps->output_queue));
    }

    /* clean up the struct. */
    memset(ps, 0, sizeof(psock_from_buffer));
    retval = allocator_reclaim(a, ps);

    /* did anything fail? */
    if (STATUS_SUCCESS != input_buffer_retval)
    {
        return input_buffer_retval;
    }
    else if (STATUS_SUCCESS != output_buffer_retval)
    {
        return output_buffer_retval;
    }
    else if (STATUS_SUCCESS != output_queue_retval)
    {
        return output_queue_retval;
    }
    else
    {
        return retval;
    }
}
