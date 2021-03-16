#include <rcpr/model_assert.h>
#include <string.h>

#include "../../../src/fiber/common/fiber_internal.h"

/* forward decls. */
static status fiber_scheduler_resource_release(resource*);

MODEL_STRUCT_TAG_GLOBAL_EXTERN(fiber_scheduler);

status FN_DECL_MUST_CHECK
fiber_scheduler_create(
    fiber_scheduler** sched, allocator* a, void* context,
    fiber_scheduler_callback_fn fn)
{
    fiber_scheduler* tmp;
    status retval, release_retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_allocator_valid(a));
    MODEL_ASSERT(NULL != sched);
    MODEL_ASSERT(NULL != fn);

    /* attempt to allocate memory for this fiber_scheduler. */
    tmp = malloc(sizeof(fiber_scheduler));
    if (NULL == tmp)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto done;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(fiber_scheduler));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->MODEL_STRUCT_TAG_REF(fiber_scheduler), fiber_scheduler);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(
        tmp->MODEL_STRUCT_TAG_REF(fiber_scheduler), fiber_scheduler);

    /* set the release method. */
    resource_init(&tmp->hdr, &fiber_scheduler_resource_release);

    /* save the init values. */
    tmp->alloc = a;
    tmp->main_fiber = NULL;
    tmp->context = context;
    tmp->fn = fn;

    retval = fiber_create_for_thread(&tmp->main_fiber, a);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_fiber_scheduler;
    }

    /* set the current fiber. */
    tmp->current_fiber = tmp->main_fiber;

    /* set the return pointer. */
    *sched = tmp;
    retval = STATUS_SUCCESS;

    /* verify that this structure is now valid. */
    MODEL_ASSERT(prop_fiber_scheduler_valid(*sched));

    /* success. */
    goto done;

cleanup_fiber_scheduler:
    release_retval = resource_release(fiber_scheduler_resource_handle(tmp));
    if (STATUS_SUCCESS != release_retval)
    {
        return release_retval;
    }

done:
    return retval;
}

/**
 * \brief Release a fiber scheduler resource.
 *
 * \param r         The fiber scheduler resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status fiber_scheduler_resource_release(resource* r)
{
    status sched_retval, fiber_retval, retval;
    fiber_scheduler* sched = (fiber_scheduler*)r;
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* cache the allocator. */
    allocator* a = sched->alloc;

    /* clean up main fiber. */
    if (NULL != sched->main_fiber)
    {
        fiber_resource_release(fiber_resource_handle(sched->main_fiber));
    }

    /* clear the scheduler structure. */
    MODEL_EXEMPT(memset(sched, 0, sizeof(*sched)));

    /* reclaim the scheduler structure. */
    free(sched);

    /* return the fiber release status. */
    return STATUS_SUCCESS;
}
