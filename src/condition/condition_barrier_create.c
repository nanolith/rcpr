/**
 * \file condition/condition_barrier_create.c
 *
 * \brief Create a condition barrier resource.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <string.h>

#include "condition_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_condition;
RCPR_IMPORT_condition_internal;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;
RCPR_IMPORT_uuid;

/* forward decls. */
static status condition_barrier_release(resource* r);

/**
 * \brief Create a \ref condition_barrier instance.
 *
 * \param cstruct   Pointer to the pointer to which the condition barrier is
 *                  stored.
 * \param alloc     The allocator to use for this condition barrier.
 * \param cond      The handle for the conditional.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status RCPR_SYM(condition_barrier_create)(
    RCPR_SYM(condition_barrier)** cstruct, RCPR_SYM(allocator)* alloc,
    RCPR_SYM(conditional) cond)
{
    status retval, release_retval;
    condition_barrier* tmp;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != cstruct);
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));
    RCPR_MODEL_ASSERT(cond > 0);

    /* allocate memory for this resource. */
    retval = allocator_allocate(alloc, (void**)&tmp, sizeof(condition_barrier));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(condition_barrier));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(condition_barrier), condition_barrier);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(condition_barrier), condition_barrier);

    /* set the release method. */
    resource_init(&tmp->hdr, &condition_barrier_release);

    /* save the init values. */
    tmp->alloc = alloc;
    tmp->cond = cond;

    /* create the wait list. */
    retval = slist_create(&tmp->wait_list, alloc);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_condition_barrier;
    }

    /* set the return pointer. */
    *cstruct = tmp;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_condition_barrier_valid(*cstruct));

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_condition_barrier:
    release_retval = allocator_reclaim(alloc, tmp);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

/**
 * \brief Release the condition barrier resource.
 *
 * \param r         The pointer to the condition barrier resource.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status condition_barrier_release(resource* r)
{
    status cleanup_retval = STATUS_SUCCESS;
    condition_barrier* cond = (condition_barrier*)r;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_condition_barrier_valid(cond));

    /* cache the allocator. */
    allocator* alloc = cond->alloc;

    /* remove all values from the list. */
    while (slist_count(cond->wait_list) > 0)
    {
        resource* ignore;

        /* pop the resource, but we don't own it, so don't release it. */
        status retval = slist_pop(cond->wait_list, &ignore);
        if (STATUS_SUCCESS != retval)
        {
            cleanup_retval = retval;
        }
    }

    /* release the wait list. */
    status waitlist_retval =
        resource_release(slist_resource_handle(cond->wait_list));

    /* reclaim the condition barrier structure. */
    status retval = allocator_reclaim(alloc, cond);

    /* bubble up any errors. */
    if (STATUS_SUCCESS != cleanup_retval)
    {
        return cleanup_retval;
    }
    else if (STATUS_SUCCESS != waitlist_retval)
    {
        return waitlist_retval;
    }
    else
    {
        return retval;
    }
}
