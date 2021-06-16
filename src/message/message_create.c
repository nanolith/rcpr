/**
 * \file message/message_create.c
 *
 * \brief Create a message to send via the fiber messaging discipline.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "message_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

/* forward decls. */
static status message_resource_release(resource* r);

/**
 * \brief Create a \ref message with a return address and a resource payload.
 *
 * \param msg           Pointer to the \ref message pointer to receive this
 *                      resource.
 * \param alloc         The allocator to use to create this resource.
 * \param returnaddr    The return address for this message, or
 *                      MESSAGE_ADDRESS_NONE if there is no return address.
 * \param payload       The payload \ref resource for this message.
 *
 * \note This \ref message is a resource, which is owned by the caller on
 * success.  The caller is responsible to either release this resource by
 * calling \ref resource_release on its resource handle, or sending it to
 * a mailbox with \ref message_send.  The resource handle for this \ref message
 * can be obtained by calling \ref message_resource_handle.  The \p payload
 * given to this message is owned by this message on success.  It will be
 * released when the message is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
message_create(
    message** msg, RCPR_SYM(allocator)* alloc, mailbox_address returnaddr,
    RCPR_SYM(resource)* payload)
{
    message* tmp;
    status retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != msg);
    MODEL_ASSERT(prop_allocator_valid(alloc));
    MODEL_ASSERT(returnaddr >= 0);
    MODEL_ASSERT(prop_resource_valid(payload));

    /* attempt to allocate memory for this message. */
    retval = allocator_allocate(alloc, (void**)&tmp, sizeof(message));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(message));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->MODEL_STRUCT_TAG_REF(message), message);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(tmp->MODEL_STRUCT_TAG_REF(message), message);

    /* set the release method. */
    resource_init(&tmp->hdr, &message_resource_release);

    /* save the init values. */
    tmp->alloc = alloc;
    tmp->returnaddr = returnaddr;
    tmp->payload = payload;

    /* set the return pointer. */
    *msg = tmp;

    /* verify that this structure is now valid. */
    MODEL_ASSERT(prop_message_valid(*msg));

    /* success. */
    return STATUS_SUCCESS;
}

/**
 * \brief Release a message resource.
 *
 * \param r         The message resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status message_resource_release(resource* r)
{
    status reclaim_retval, payload_release_retval = STATUS_SUCCESS;
    message* msg = (message*)r;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_message_valid(msg));

    /* cache the allocator. */
    allocator* alloc = msg->alloc;

    /* release the payload if set. */
    if (NULL != msg->payload)
    {
        payload_release_retval = resource_release(msg->payload);
    }

    /* reclaim the message memory. */
    reclaim_retval = allocator_reclaim(alloc, msg);

    /* return the appropriate return code. */
    if (STATUS_SUCCESS != payload_release_retval)
    {
        return payload_release_retval;
    }
    else if (STATUS_SUCCESS != reclaim_retval)
    {
        return reclaim_retval;
    }
    else
    {
        return STATUS_SUCCESS;
    }
}
