/**
 * \file psock/psock_from_buffer_write.c
 *
 * \brief Write data to a buffer.
 *
 * \copyright 2021-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <errno.h>
#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>
#include <string.h>
#include <unistd.h>

#include "psock_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_psock_internal;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;

/* forward decls. */
static status psock_output_buffer_node_resource_release(resource* r);
static status psock_output_buffer_node_create(
    psock_output_buffer_node** ob, allocator* a, char* buffer, size_t size);

/* the vtable entry for the psock output buffer node instance. */
RCPR_VTABLE
resource_vtable psock_output_buffer_node_vtable = {
    &psock_output_buffer_node_resource_release };

/**
 * \brief Write data to the given \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to write.
 * \param data          Pointer to the buffer from which data should be written.
 * \param size          Pointer to the size to write, updated with the size
 *                      written.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status RCPR_SYM(psock_from_buffer_write)(
    RCPR_SYM(psock)* sock, const void* data, size_t* size)
{
    status retval, release_retval;
    size_t copy_size;
    size_t total_size = 0;
    psock_output_buffer_node* ob = NULL;
    void* large_buffer = NULL;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_valid(sock));
    RCPR_MODEL_ASSERT(NULL != data);
    RCPR_MODEL_ASSERT(NULL != size);
    RCPR_MODEL_ASSERT(PSOCK_TYPE_BUFFER == sock->type);

    /* make sure this is a valid type. */
    if (PSOCK_TYPE_BUFFER != sock->type)
    {
        return ERROR_PSOCK_UNSUPPORTED_TYPE;
    }

    /* cast to the correct derived type. */
    psock_from_buffer* pb = (psock_from_buffer*)sock;

    /* verify that this is an output buffer socket type. */
    if (NULL == pb->output_curr_buffer || NULL == pb->output_queue)
    {
        return ERROR_PSOCK_UNSUPPORTED_TYPE;
    }

    /* fill the current buffer first. */
    copy_size = pb->output_buffer_size - pb->buffer_write_offset;
    if (copy_size > *size)
    {
        copy_size = *size;
    }
    memcpy(pb->output_curr_buffer + pb->buffer_write_offset, data, copy_size);
    data = ((uint8_t*)data) + copy_size;
    total_size += copy_size;
    pb->buffer_write_offset += copy_size;
    *size -= copy_size;

    /* if the current buffer is full, append it to the output queue and reset
     * the buffer. */
    if (pb->buffer_write_offset >= pb->output_buffer_size)
    {
        /* create an output buffer node. */
        retval =
            psock_output_buffer_node_create(
                &ob, sock->alloc, pb->output_curr_buffer,
                pb->output_buffer_size);
        if (STATUS_SUCCESS != retval)
        {
            goto done;
        }

        /* append this to the tail of the queue. */
        retval = slist_append_tail(pb->output_queue, &ob->hdr);
        if (STATUS_SUCCESS != retval)
        {
            /* clean up ob. */
            ob->buffer = NULL;
            release_retval = resource_release(&ob->hdr);
            if (STATUS_SUCCESS != release_retval)
            {
                retval = release_retval;
            }
            goto done;
        }

        /* the output current buffer is no longer set. */
        pb->output_curr_buffer = NULL;
        pb->output_buffer_size = PSOCK_BUFFER_SIZE;
        pb->buffer_write_offset = 0;

        /* allocate memory for the new buffer. */
        retval =
            allocator_allocate(
                sock->alloc, (void**)&pb->output_curr_buffer,
                pb->output_buffer_size);
        if (STATUS_SUCCESS != retval)
        {
            goto done;
        }
    }

    /* if the remaining size is greater than the current output buffer size,
     * then create and append a buffer equal to that size to save time. */
    if (*size >= pb->output_buffer_size)
    {
        /* create a buffer for holding this extra data. */
        retval = allocator_allocate(sock->alloc, (void**)&large_buffer, *size);
        if (STATUS_SUCCESS != retval)
        {
            goto done;
        }

        /* copy data to this buffer. */
        memcpy(large_buffer, data, *size);

        /* create an output buffer node. */
        retval =
            psock_output_buffer_node_create(
                &ob, sock->alloc, large_buffer, *size);
        if (STATUS_SUCCESS != retval)
        {
            goto cleanup_large_buffer;
        }

        /* append this to the tail of the queue. */
        retval = slist_append_tail(pb->output_queue, &ob->hdr);
        if (STATUS_SUCCESS != retval)
        {
            ob->buffer = NULL;
            goto cleanup_ob;
        }

        /* fixups. */
        data = ((uint8_t*)data) + *size;
        total_size += *size;
        *size = 0;
    }

    /* if there is still remaining data to copy, then append it. */
    if (*size > 0)
    {
        copy_size = *size;
        memcpy(
            pb->output_curr_buffer + pb->buffer_write_offset, data, copy_size);
        total_size += copy_size;
        pb->buffer_write_offset += copy_size;
        *size -= copy_size;
    }

    /* success. */
    RCPR_MODEL_ASSERT(0 == *size);
    *size = total_size;
    pb->output_buffer_total_size += *size;
    retval = STATUS_SUCCESS;
    goto done;

cleanup_ob:
    release_retval = resource_release(&ob->hdr);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_large_buffer:
    release_retval = allocator_reclaim(sock->alloc, large_buffer);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }
    goto done;

done:
    return retval;
}

/**
 * \brief Release an output buffer node resource.
 *
 * \param r         The resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status psock_output_buffer_node_resource_release(resource* r)
{
    status buffer_release_retval = STATUS_SUCCESS;
    status retval = STATUS_SUCCESS;
    psock_output_buffer_node* ob = (psock_output_buffer_node*)r;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_psock_output_buffer_node_valid(ob));

    /* cache allocator. */
    allocator* alloc = ob->alloc;

    /* release the output buffer. */
    if (NULL != ob->buffer)
    {
        buffer_release_retval = allocator_reclaim(alloc, ob->buffer);
    }

    /* release this output buffer structure. */
    retval = allocator_reclaim(alloc, ob);

    /* return the appropriate status code. */
    if (STATUS_SUCCESS != buffer_release_retval)
    {
        return buffer_release_retval;
    }
    else
    {
        return retval;
    }
}

/**
 * \brief Create an output buffer node with the given values.
 *
 * \param ob        Pointer to the output buffer node pointer to receive the
 *                  created output buffer node on success.
 * \param a         The allocator to use to create this node.
 * \param buffer    The buffer for this node (owned by the node on success.)
 * \param size      The size of the buffer for this node.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status psock_output_buffer_node_create(
    psock_output_buffer_node** ob, allocator* a, char* buffer, size_t size)
{
    status retval;
    psock_output_buffer_node* tmp;

    /* create an output buffer node. */
    retval =
        allocator_allocate(a, (void**)&tmp, sizeof(psock_output_buffer_node));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear the data structure. */
    memset(tmp, 0, sizeof(*tmp));

    /* initialize the resource header with a resource release method. */
    resource_init(&tmp->hdr, &psock_output_buffer_node_vtable);

    /* cache the allocator, buffer and size. */
    tmp->alloc = a;
    tmp->buffer = buffer;
    tmp->size = size;

    /* success. */
    *ob = tmp;
    retval = STATUS_SUCCESS;
    goto done;

done:
    return retval;
}
