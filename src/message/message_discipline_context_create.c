/**
 * \file message/message_discipline_context_create.c
 *
 * \brief Create the message discipline context.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "message_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_compare;
RCPR_IMPORT_message;
RCPR_IMPORT_message_internal;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_resource;

/* forward decls. */
static status message_discipline_context_resource_release(resource* r);
static rcpr_comparison_result message_discipline_mailbox_address_compare(
    void* context, const void* lhs, const void* rhs);
static const void* message_discipline_mailbox_get_key(
    void* context, const resource* r);

MODEL_STRUCT_TAG_GLOBAL_EXTERN(message_discipline_context);

/**
 * \brief Create the message discipline context.
 *
 * \param ctx       Pointer to the pointer to which the context is stored.
 * \param alloc     The \ref allocator used to create the context;
 * \param sched     The \ref fiber_scheduler instance for this context.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(message_discipline_context_create)(
    RCPR_SYM(resource)** ctx, RCPR_SYM(allocator)* alloc,
    RCPR_SYM(fiber_scheduler)* sched)
{
    message_discipline_context* tmp;
    status retval, release_retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != ctx);
    MODEL_ASSERT(prop_allocator_valid(alloc));
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* allocate memory for the message discipline context. */
    retval =
        allocator_allocate(
            alloc, (void**)&tmp, sizeof(message_discipline_context));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(message_discipline_context));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->MODEL_STRUCT_TAG_REF(message_discipline_context),
        message_discipline_context);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(
        tmp->MODEL_STRUCT_TAG_REF(message_discipline_context),
        message_discipline_context);

    /* set the release method. */
    resource_init(&tmp->hdr, &message_discipline_context_resource_release);

    /* set the init vars. */
    tmp->alloc = alloc;
    tmp->sched = sched;
    tmp->index = 0;

    /* create the rbtree instance for holding the mailboxes. */
    retval =
        rbtree_create(
            &tmp->mailboxes, alloc, &message_discipline_mailbox_address_compare,
            &message_discipline_mailbox_get_key, NULL);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_tmp;
    }

    /* set the return pointer. */
    *ctx = &tmp->hdr;

    /* verify that this structure is now valid. */
    MODEL_ASSERT(prop_message_discipline_context_valid(*ctx));

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_tmp:
    release_retval = allocator_reclaim(alloc, tmp);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

/**
 * \brief Compare two mailbox addresses.
 *
 * \param context       Unused context parameter.
 * \param lhs           The left-hand side of the comparison.
 * \param rhs           The right-hand side of the comparison.
 *
 * \returns an integer value representing the comparison result.
 *      - RCPR_COMPARE_LT if \p lhs &lt; \p rhs.
 *      - RCPR_COMPARE_EQ if \p lhs == \p rhs.
 *      - RCPR_COMPARE_GT if \p lhs &gt; \p rhs.
*/
static rcpr_comparison_result message_discipline_mailbox_address_compare(
    void* context, const void* lhs, const void* rhs)
{
    (void)context;

    const mailbox_address* l = (const mailbox_address*)lhs;
    const mailbox_address* r = (const mailbox_address*)rhs;

    if (*l < *r)
        return RCPR_COMPARE_LT;
    else if (*l > *r)
        return RCPR_COMPARE_GT;
    else
        return RCPR_COMPARE_EQ;
}

/**
 * \brief Given a mailbox resource, return the key for the mailbox resource.
 *
 * \param context       Unused context.
 * \param r             The mailbox resource.
 *
 * \returns the key for the resource.
 */
static const void* message_discipline_mailbox_get_key(
    void* context, const resource* r)
{
    (void)context;
    const mailbox* mb = (const mailbox*)r;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_mailbox_valid(mb));

    return &mb->address;
}

/**
 * \brief Release the message discipline context resource.
 *
 * \param r         The resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status message_discipline_context_resource_release(resource* r)
{
    message_discipline_context* ctx = (message_discipline_context*)r;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_valid_message_discipline_context(ctx));

    /* cache the allocator. */
    allocator* alloc = ctx->alloc;

    /* release the mailboxes. */
    status mailbox_retval =
        resource_release(rbtree_resource_handle(ctx->mailboxes));

    /* clear this structure. */
    memset(ctx, 0, sizeof(*ctx));

    /* reclaim the memory for this structure. */
    status release_retval = allocator_reclaim(alloc, ctx);

    /* return the appropriate status code. */
    if (STATUS_SUCCESS != mailbox_retval)
    {
        return mailbox_retval;
    }
    else if (STATUS_SUCCESS != release_retval)
    {
        return release_retval;
    }
    else
    {
        return STATUS_SUCCESS;
    }
}
