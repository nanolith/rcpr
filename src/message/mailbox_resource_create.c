/**
 * \file message/mailbox_resource_create.c
 *
 * \brief Create a mailbox resource.
 *
 * \copyright 2021-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>
#include <string.h>

#include "message_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_message;
RCPR_IMPORT_message_internal;
RCPR_IMPORT_queue;
RCPR_IMPORT_resource;
RCPR_IMPORT_uuid;

/* forward decls. */
static status mailbox_resource_release(resource* r);

/* the vtable entry for the mailbox resource instance. */
RCPR_VTABLE
resource_vtable mailbox_resource_vtable = {
    &mailbox_resource_release };

/**
 * \brief Create a mailbox instance.
 *
 * \param mbox      Pointer to the pointer to which the mailbox is stored.
 * \param alloc     The allocator to use for this mailbox.
 * \param addr      The address of the new mailbox.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(mailbox_resource_create)(
    RCPR_SYM(mailbox)** mbox, RCPR_SYM(allocator)* alloc,
    RCPR_SYM(mailbox_address) addr)
{
    status retval, release_retval;
    mailbox* tmp;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != mbox);
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));
    RCPR_MODEL_ASSERT(addr > 0);

    /* allocate memory for this resource. */
    retval = allocator_allocate(alloc, (void**)&tmp, sizeof(mailbox));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(mailbox));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(mailbox), mailbox);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(mailbox), mailbox);

    /* set the release method. */
    resource_init(&tmp->hdr, &mailbox_resource_vtable);

    /* save the init values. */
    tmp->alloc = alloc;
    tmp->address = addr;
    tmp->blocked_fiber = NULL;

    /* create the mail queue. */
    retval = queue_create(&tmp->message_queue, alloc);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mailbox;
    }

    /* set the return pointer. */
    *mbox = tmp;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_mailbox_valid(*mailbox));

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_mailbox:
    release_retval = allocator_reclaim(alloc, tmp);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

/**
 * \brief Release the mailbox resource.
 *
 * \param r         The pointer to the mailbox resource.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status mailbox_resource_release(resource* r)
{
    mailbox* mbox = (mailbox*)r;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_mailbox_valid(mbox));

    /* cache the allocator. */
    allocator* alloc = mbox->alloc;

    /* release the message queue. */
    status queue_retval =
        resource_release(queue_resource_handle(mbox->message_queue));

    /* reclaim the mailbox structure. */
    status retval = allocator_reclaim(alloc, mbox);

    /* bubble up any errors. */
    if (STATUS_SUCCESS != queue_retval)
    {
        return queue_retval;
    }
    else
    {
        return retval;
    }
}
