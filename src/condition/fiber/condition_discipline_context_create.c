/**
 * \file condition/condition_discipline_context_create.c
 *
 * \brief Create the condition discipline context.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "../condition_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_compare;
RCPR_IMPORT_condition;
RCPR_IMPORT_condition_internal;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_resource;

/* forward decls. */
static status condition_discipline_context_resource_release(resource* r);
static rcpr_comparison_result condition_discipline_condition_barrier_compare(
    void* context, const void* lhs, const void* rhs);
static const void* condition_discipline_condition_barrier_get_key(
    void* context, const resource* r);

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(condition_discipline_context);

/**
 * \brief Create the condition discipline context.
 *
 * \param ctx       Pointer to the pointer to which the context is stored.
 * \param alloc     The \ref allocator used to create the context;
 * \param sched     The \ref fiber_scheduler instance for this context.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(condition_discipline_context_create)(
    RCPR_SYM(resource)** ctx, RCPR_SYM(allocator)* alloc,
    RCPR_SYM(fiber_scheduler)* sched)
{
    condition_discipline_context* tmp;
    status retval, release_retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != ctx);
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* allocate memory for the condition discipline context. */
    retval =
        allocator_allocate(
            alloc, (void**)&tmp, sizeof(condition_discipline_context));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(condition_discipline_context));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(condition_discipline_context),
        condition_discipline_context);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(condition_discipline_context),
        condition_discipline_context);

    /* set the release method. */
    resource_init(&tmp->hdr, &condition_discipline_context_resource_release);

    /* set the init vars. */
    tmp->alloc = alloc;
    tmp->sched = sched;
    tmp->index = 0;

    /* create the rbtree instance for holding the condition barriers. */
    retval =
        rbtree_create(
            &tmp->condition_barriers, alloc,
            &condition_discipline_condition_barrier_compare,
            &condition_discipline_condition_barrier_get_key, NULL);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_tmp;
    }

    /* set the return pointer. */
    *ctx = &tmp->hdr;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_condition_discipline_context_valid(*ctx));

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
 * \brief Compare two condition barrier addresses.
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
static rcpr_comparison_result condition_discipline_condition_barrier_compare(
    void* context, const void* lhs, const void* rhs)
{
    (void)context;

    const conditional* l = (const conditional*)lhs;
    const conditional* r = (const conditional*)rhs;

    if (*l < *r)
        return RCPR_COMPARE_LT;
    else if (*l > *r)
        return RCPR_COMPARE_GT;
    else
        return RCPR_COMPARE_EQ;
}

/**
 * \brief Given a condition barrier resource, return the key for the condition
 * barrier resource.
 *
 * \param context       Unused context.
 * \param r             The mailbox resource.
 *
 * \returns the key for the resource.
 */
static const void* condition_discipline_condition_barrier_get_key(
    void* context, const resource* r)
{
    (void)context;
    const condition_barrier* cb = (const condition_barrier*)r;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_condition_barrier_valid(cb));

    return &cb->cond;
}

/**
 * \brief Release the condition discipline context resource.
 *
 * \param r         The resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status condition_discipline_context_resource_release(resource* r)
{
    condition_discipline_context* ctx = (condition_discipline_context*)r;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_valid_condition_discipline_context(ctx));

    /* cache the allocator. */
    allocator* alloc = ctx->alloc;

    /* release the condition barriers. */
    status barrier_retval =
        resource_release(rbtree_resource_handle(ctx->condition_barriers));

    /* clear this structure. */
    memset(ctx, 0, sizeof(*ctx));

    /* reclaim the memory for this structure. */
    status release_retval = allocator_reclaim(alloc, ctx);

    /* return the appropriate status code. */
    if (STATUS_SUCCESS != barrier_retval)
    {
        return barrier_retval;
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
