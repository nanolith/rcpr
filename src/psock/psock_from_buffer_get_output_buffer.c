/**
 * \file psock/psock_from_buffer_get_output_buffer.c
 *
 * \brief Get the output buffer from a psock buffer instance.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "psock_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;

/* forward decls. */
static status copy_output_buffer(
    psock_from_buffer* pb, uint8_t* buffer, size_t buffer_size);

/**
 * \brief For an output buffer backed psock, get a copy of the buffer. This
 * buffer belongs to the caller and must be reclaimed using the allocator passed
 * as a parameter.
 *
 * \param sock          Pointer to the \ref psock on which this operation
 *                      occurs.
 * \param a             The allocator to be used to allocate memory for the
 *                      buffer copy.
 * \param buffer        Pointer to the buffer pointer to be set with the copied
 *                      buffer on success.
 * \param buffer_size   Pointer to a variable to be set to the length of this
 *                      buffer on success.
 *
 * The \ref psock_from_buffer_get_output_buffer method creates a copy of the
 * current output buffer and returns it to the caller.  This copy is contiguous
 * in memory, whereas the output buffer written to by the psock may not be.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 *
 * \pre
 *      - \p sock must be a pointer to a valid \ref psock instance and must not
 *        be NULL.
 *      - \p a must be a pointer to a valid \ref allocator instance and must not
 *        be NULL.
 *      - \p buffer must be a pointer to a valid pointer and must not be NULL.
 *      - \p buffer_size must be a pointer to a size_t value and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p buffer is set to a buffer containing a copy of the data
 *        written to this psock instance.
 *      - On success, \p buffer_size is set to the length of the buffer.
 *      - On failure, \p data is unchanged and an error status is returned.
 *      - On failure, \p data_size is unchanged.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(psock_from_buffer_get_output_buffer)(
    RCPR_SYM(psock)* sock, RCPR_SYM(allocator)* a, void** buffer,
    size_t* buffer_size)
{
    status retval, release_retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT(NULL != buffer);
    RCPR_MODEL_ASSERT(NULL != buffer_size);
    RCPR_MODEL_ASSERT(PSOCK_TYPE_BUFFER == sock->type);

    /* verify the type. */
    if (PSOCK_TYPE_BUFFER != sock->type)
    {
        return ERROR_PSOCK_UNSUPPORTED_TYPE;
    }

    /* cast this to the derived type. */
    psock_from_buffer* pb = (psock_from_buffer*)sock;

    /* verify that the output buffer is initialized. */
    if (NULL == pb->output_curr_buffer || NULL == pb->output_queue)
    {
        return ERROR_PSOCK_UNSUPPORTED_TYPE;
    }

    /* set the buffer size. */
    *buffer_size = pb->output_buffer_total_size;

    /* allocate memory for the output buffer. */
    retval = allocator_allocate(a, buffer, *buffer_size);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* copy the output buffer data to this buffer. */
    retval = copy_output_buffer(pb, (uint8_t*)*buffer, *buffer_size);
    if (STATUS_SUCCESS != retval)
    {
        goto reclaim_buffer;
    }

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

reclaim_buffer:
    release_retval = allocator_reclaim(a, *buffer);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

/**
 * \brief Copy all of the output data to the output buffer.
 *
 * \param pb            The \ref psock_from_buffer instance.
 * \param buffer        The output buffer.
 * \param buffer_size   The total size of the output buffer.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status copy_output_buffer(
    psock_from_buffer* pb, uint8_t* buffer, size_t buffer_size)
{
    status retval;
    slist_node* node;
    psock_output_buffer_node* ob;

    /* get the head of the output buffer queue. */
    retval = slist_head(&node, pb->output_queue);
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* iterate through all entries, in insertion order. */
    while (NULL != node)
    {
        /* get the output buffer for this node. */
        retval = slist_node_child((resource**)&ob, node);
        if (STATUS_SUCCESS != retval)
        {
            return retval;
        }

        /* copy this output buffer to the output. */
        size_t copy_size = buffer_size > ob->size ? ob->size : buffer_size;
        buffer_size -= copy_size;
        memcpy(buffer, ob->buffer, copy_size);
        buffer += copy_size;

        /* get the next node. */
        retval = slist_node_next(&node, node);
        if (STATUS_SUCCESS != retval)
        {
            return retval;
        }
    }

    /* copy the current output buffer to the output buffer. */
    size_t copy_size =
        buffer_size > pb->buffer_write_offset
            ? pb->buffer_write_offset
            : buffer_size;
    buffer_size -= copy_size;
    memcpy(buffer, pb->output_curr_buffer, copy_size);
    buffer += copy_size;

    /* success. */
    return STATUS_SUCCESS;
}
