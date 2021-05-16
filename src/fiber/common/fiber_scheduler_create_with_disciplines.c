/**
 * \file fiber/common/fiber_scheduler_create_with_disciplines.c
 *
 * \brief Create a disciplined fiber scheduler.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stddef.h>
#include <string.h>

#include "fiber_internal.h"

/* forward decls. */
static status fiber_scheduler_disciplined_resource_release(resource*);
static status fiber_scheduler_disciplined_context_resource_release(resource*);
static status fiber_scheduler_disciplined_callback(
    void* context, fiber* yield_fib, int yield_event, void* yield_param,
    fiber** resume_fib, const rcpr_uuid** resume_id, int* resume_event,
    void** resume_param);
static rcpr_comparison_result fiber_by_pointer_compare(
    void* context, const void* lhs, const void* rhs);
static const void* fiber_by_pointer_key(void* context, const resource* r);
static rcpr_comparison_result disciplines_by_uuid_compare(
    void* context, const void* lhs, const void* rhs);
static const void* disciplines_by_uuid_key(void* context, const resource* r);
static status fiber_scheduler_disciplined_run_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param);
static status fiber_scheduler_disciplined_main_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param);
static status fiber_scheduler_disciplined_add_fiber_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param);
static status fiber_scheduler_disciplined_stop_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param);
static status fiber_scheduler_disciplined_resource_release_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param);
static status
fiber_scheduler_disciplined_management_yield_event_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param);

MODEL_STRUCT_TAG_GLOBAL_EXTERN(fiber_scheduler_disciplined_context);

/**
 * \brief Create a disciplined \ref fiber_scheduler instance.
 *
 * \param sched         Pointer to the \ref fiber_scheduler pointer to receive
 *                      this resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      fiber_scheduler resource.
 *
 * \note This \ref fiber_scheduler is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling \ref
 * fiber_scheduler_resource_handle on this \ref fiber_scheduler instance. The
 * fiber scheduler must be in a terminated state before releasing this resource.
 * If the fiber scheduler is not yet terminated, then undefined behavior can
 * occur, the least of which being that any resources owned by fibers managed by
 * this scheduler will not be released.  It is up to the caller to ensure that
 * the fiber scheduler has terminated, in this case, by making use of the
 * management discipline of the fiber scheduler.
 *
 * This is the preferred way to use the fiber library, as it is the most
 * flexible.  The \ref fiber_scheduler_create_ex method should be used for
 * specialized fiber use cases, such as simple coroutines and testing.
 *
 * This call creates a disciplined fiber scheduler, which incorporates
 * discipline domains such as I/O scheduling, fiber management, or message
 * passing. These domains can be added to a disciplined fiber scheduler
 * instance. By default, fiber management is always added to a new disciplined
 * fiber scheduler by this create function.  A new discipline should be added to
 * the fiber scheduler before using any of its methods.  This discipline should
 * be passed to the context of any fiber wishing to make use of it.  Internally,
 * the disciplined fiber scheduler will add callback vectors for each possible
 * discipline callback to its internal event router.  Only the discipline
 * instance associated with this fiber scheduler should be used to initiate
 * calls, since event codes are dynamically allocated, in order to provide a
 * flexible vectored dispatch that can accommodate user defined disciplines.
 * 
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p sched must not reference a valid \ref fiber_scheduler instance and
 *        must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *
 * \post
 *      - On success, \p sched is set to a pointer to a valid disciplined \ref
 *        fiber_scheduler instance, which is a \ref resource owned by the caller
 *        that must be released when no longer needed.
 *      - On failure, \p sched is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
fiber_scheduler_create_with_disciplines(
    fiber_scheduler** sched, allocator* a)
{
    fiber_scheduler_disciplined_context* ctx;
    fiber_scheduler* tmp;
    status retval, release_retval;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_allocator_valid(a));
    MODEL_ASSERT(NULL != sched);

    /* attempt to allocate memory for the fiber scheduler context. */
    retval =
        allocator_allocate(
            a, (void**)&ctx, sizeof(fiber_scheduler_disciplined_context));
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto done;
    }

    /* clear the structure. */
    memset(ctx, 0, sizeof(fiber_scheduler_disciplined_context));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        ctx->MODEL_STRUCT_TAG_REF(fiber_scheduler_disciplined_context),
        fiber_scheduler_disciplined_context);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(
        ctx->MODEL_STRUCT_TAG_REF(fiber_scheduler_disciplined_context),
        fiber_scheduler_disciplined_context);

    /* set the release method. */
    resource_init(
        &ctx->hdr, &fiber_scheduler_disciplined_context_resource_release);

    /* set the init values. */
    ctx->alloc = a;
    ctx->callback_vector_size = 0;

    /* create the fiber tree. */
    retval =
        rbtree_create(
            &ctx->fibers_by_pointer, a, &fiber_by_pointer_compare,
            &fiber_by_pointer_key, NULL);
    if (STATUS_SUCCESS != retval)
    {
        goto reclaim_ctx_memory;
    }

    /* create the discipline tree. */
    retval =
        rbtree_create(
            &ctx->disciplines_by_uuid, a, &disciplines_by_uuid_compare,
            &disciplines_by_uuid_key, NULL);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_fibers_by_pointer;
    }

    /* create the run queue. */
    retval = queue_create(&ctx->run_queue, a);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_disciplines_by_uuid;
    }

    /* create the initial callback vector. */
    ctx->callback_vector_size = FIBER_SCHEDULER_YIELD_EVENT_INTERNAL_COUNT;
    retval =
        allocator_allocate(
            a, (void**)&ctx->callback_vector,
            ctx->callback_vector_size
                * sizeof(fiber_scheduler_discipline_callback_fn));
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_run_queue;
    }

    /* create the initial context vector. */
    retval =
        allocator_allocate(
            a, (void**)&ctx->context_vector,
            ctx->callback_vector_size * sizeof(void*));
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_callback_vector;
    }

    /* set each internal callback. */
    ctx->callback_vector[FIBER_SCHEDULER_YIELD_EVENT_RUN] =
        &fiber_scheduler_disciplined_run_callback_handler;
    ctx->callback_vector[FIBER_SCHEDULER_YIELD_EVENT_MAIN] =
        &fiber_scheduler_disciplined_main_callback_handler;
    ctx->callback_vector[FIBER_SCHEDULER_YIELD_EVENT_ADD_FIBER] =
        &fiber_scheduler_disciplined_add_fiber_callback_handler;
    ctx->callback_vector[FIBER_SCHEDULER_YIELD_EVENT_STOP] =
        &fiber_scheduler_disciplined_stop_callback_handler;
    ctx->callback_vector[FIBER_SCHEDULER_YIELD_EVENT_RESOURCE_RELEASE] =
        &fiber_scheduler_disciplined_resource_release_callback_handler;

    /* set each internal context pointer. */
    ctx->context_vector[FIBER_SCHEDULER_YIELD_EVENT_RUN] = ctx;
    ctx->context_vector[FIBER_SCHEDULER_YIELD_EVENT_MAIN] = ctx;
    ctx->context_vector[FIBER_SCHEDULER_YIELD_EVENT_ADD_FIBER] = ctx;
    ctx->context_vector[FIBER_SCHEDULER_YIELD_EVENT_STOP] = ctx;
    ctx->context_vector[FIBER_SCHEDULER_YIELD_EVENT_RESOURCE_RELEASE] = ctx;

    /* create the fiber scheduler instance. */
    retval =
        fiber_scheduler_create(
            &tmp, a, ctx, &fiber_scheduler_disciplined_callback);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_context_vector;
    }

    /* cache the resource release method for this scheduler. */
    memcpy(
        &ctx->cached_scheduler_resource_handler, &tmp->hdr, sizeof(resource));

    /* override the resource release method for this scheduler with our own. */
    resource_init(&tmp->hdr, &fiber_scheduler_disciplined_resource_release);

    /* set the scheduler for this context. */
    ctx->sched = tmp;

    /* mark this fiber scheduler as disciplined. */
    tmp->disciplined = true;

    /* create the management discipline for this scheduler. */
    fiber_scheduler_discipline_callback_fn callbacks[1] = {
        &fiber_scheduler_disciplined_management_yield_event_callback_handler };
    retval =
        fiber_scheduler_discipline_create(
            &ctx->management_discipline, &FIBER_SCHEDULER_MANAGEMENT_DISCIPLINE,
            ctx->alloc, ctx, 1, callbacks);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_scheduler;
    }

    /* add this discipline to our scheduler. */
    retval = fiber_scheduler_discipline_add(tmp, ctx->management_discipline);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_management_discipline;
    }

    /* success. */
    *sched = tmp;
    retval = STATUS_SUCCESS;
    goto done;

cleanup_management_discipline:
    release_retval =
        resource_release(
            fiber_scheduler_discipline_resource_handle(
                ctx->management_discipline));
    /* this should always succeed. */
    MODEL_ASSERT(STATUS_SUCCESS == release_retval);
    /* runtime assurance: bubble up the error */
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_scheduler:
    release_retval = resource_release(fiber_scheduler_resource_handle(tmp));
    /* this should always succeed. */
    MODEL_ASSERT(STATUS_SUCCESS == release_retval);
    /* runtime assurance: bubble up the error */
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }
    /* at this point, all cleanup is done by the resource release. */
    goto done;

    
cleanup_context_vector:
    release_retval = allocator_reclaim(a, ctx->context_vector);
    /* this should always succeed. */
    MODEL_ASSERT(STATUS_SUCCESS == release_retval);
    /* runtime assurance: bubble up the error. */
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_callback_vector:
    release_retval = allocator_reclaim(a, ctx->callback_vector);
    /* this should always succeed. */
    MODEL_ASSERT(STATUS_SUCCESS == release_retval);
    /* runtime assurance: bubble up the error. */
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_run_queue:
    release_retval = resource_release(queue_resource_handle(ctx->run_queue));
    /* this should always succeed. */
    MODEL_ASSERT(STATUS_SUCCESS == release_retval);
    /* runtime assurance: bubble up the error. */
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_disciplines_by_uuid:
    release_retval =
        resource_release(rbtree_resource_handle(ctx->disciplines_by_uuid));
    /* this should always succeed. */
    MODEL_ASSERT(STATUS_SUCCESS == release_retval);
    /* runtime assurance: bubble up the error. */
    if (STATUS_SUCCESS != retval)
    {
        retval = release_retval;
    }

cleanup_fibers_by_pointer:
    release_retval =
        resource_release(rbtree_resource_handle(ctx->fibers_by_pointer));
    /* this should always succeed. */
    MODEL_ASSERT(STATUS_SUCCESS == release_retval);
    /* runtime assurance: bubble up the error. */
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

reclaim_ctx_memory:
    release_retval = allocator_reclaim(a, ctx);
    /* this should always succeed. */
    MODEL_ASSERT(STATUS_SUCCESS == release_retval);
    /* runtime assurance: bubble up the error. */
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

/**
 * \brief Compare two fiber pointers.
 *
 * \param context   This context is ignored.
 * \param lhs       The left-hand side for this comparison.
 * \param rhs       The right-hand side for this comparison.
 *
 * \returns A comparison result.
 *      - RCPR_COMPARE_LT if lhs < rhs.
 *      - RCPR_COMPARE_GT if lhs > rhs.
 *      - RCPR_COMPARE_EQ if lhs == rhs.
 */
static rcpr_comparison_result fiber_by_pointer_compare(
    void* context, const void* lhs, const void* rhs)
{
    (void)context;

    ptrdiff_t compare = lhs - rhs;

    if (compare < 0)
        return RCPR_COMPARE_LT;
    else if (compare > 0)
        return RCPR_COMPARE_GT;
    else
        return RCPR_COMPARE_EQ;
}

/**
 * \brief The key for the fiber_by_pointer tree is the fiber's pointer, which is
 * the resource pointer.
 *
 * \param context   The context is unused.
 * \param r         The fiber resource from which the key is extracted.
 *
 * \returns a const void pointer to the fiber pointer.
 */
static const void* fiber_by_pointer_key(void* context, const resource* r)
{
    (void)context;

    return (const void*)r;
}

/**
 * \brief Compare two discipline UUID pointers.
 *
 * \param context   This context is ignored.
 * \param lhs       The left-hand side for this comparison.
 * \param rhs       The right-hand side for this comparison.
 *
 * \returns A comparison result.
 *      - RCPR_COMPARE_LT if lhs < rhs.
 *      - RCPR_COMPARE_GT if lhs > rhs.
 *      - RCPR_COMPARE_EQ if lhs == rhs.
 */
static rcpr_comparison_result disciplines_by_uuid_compare(
    void* context, const void* lhs, const void* rhs)
{
    (void)context;
    const rcpr_uuid* ul = (const rcpr_uuid*)lhs;
    const rcpr_uuid* ur = (const rcpr_uuid*)rhs;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_uuid_valid(ul));
    MODEL_ASSERT(prop_uuid_valid(ur));

    int compare = memcmp(ul, ur, sizeof(rcpr_uuid));

    if (compare < 0)
        return RCPR_COMPARE_LT;
    else if (compare > 0)
        return RCPR_COMPARE_GT;
    else
        return RCPR_COMPARE_EQ;
}

/**
 * \brief The key for the disciplines_by_uuid tree is the discipline's uuid.
 *
 * \param context   The context is unused.
 * \param r         The discipline's resource pointer.
 *
 * \returns a const void pointer to the fiber pointer.
 */
static const void* disciplines_by_uuid_key(void* context, const resource* r)
{
    (void)context;
    const fiber_scheduler_discipline* disc =
        (const fiber_scheduler_discipline*)r;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(disc));

    return (const void*)&disc->id;
}

/**
 * \brief Release the disciplined scheduler context resources.
 * \param r         The disciplined scheduler context's resource pointer.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status fiber_scheduler_disciplined_context_resource_release(resource* r)
{
    status idle_fiber_retval = STATUS_SUCCESS;
    status fibers_by_pointer_retval = STATUS_SUCCESS;
    status disciplines_by_uuid_retval = STATUS_SUCCESS;
    status run_queue_tmp_retval = STATUS_SUCCESS;
    status run_queue_retval = STATUS_SUCCESS;
    status callback_vector_retval = STATUS_SUCCESS;
    status context_vector_retval = STATUS_SUCCESS;

    /* recover the context type. */
    fiber_scheduler_disciplined_context* ctx =
        (fiber_scheduler_disciplined_context*)r;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_disciplined_context_valid(ctx));

    /* cache the allocator. */
    allocator* alloc = ctx->alloc;

    /* release the idle fiber, if set. */
    if (NULL != ctx->idle_fiber)
    {
        idle_fiber_retval =
            resource_release(fiber_resource_handle(ctx->idle_fiber));
    }

    /* release the fibers by pointer tree, releasing all fibers still associated
     * with it. */
    fibers_by_pointer_retval =
        resource_release(rbtree_resource_handle(ctx->fibers_by_pointer));

    /* release the disciplines by UUID. */
    disciplines_by_uuid_retval =
        resource_release(rbtree_resource_handle(ctx->disciplines_by_uuid));

    /* remove all entries from the run queue. */
    resource* run_fiber = NULL;
    while (queue_count(ctx->run_queue) > 0)
    {
        run_queue_tmp_retval = queue_pop(ctx->run_queue, &run_fiber); 
        if (STATUS_SUCCESS != run_queue_tmp_retval)
        {
            run_queue_retval = run_queue_tmp_retval;
        }
    }

    /* release the run queue. */
    run_queue_tmp_retval =
        resource_release(queue_resource_handle(ctx->run_queue));
    if (STATUS_SUCCESS != run_queue_tmp_retval)
    {
        run_queue_retval = run_queue_tmp_retval;
    }

    /* if the callback vector is allocated, reclaim it. */
    if (NULL != ctx->callback_vector)
    {
        callback_vector_retval = allocator_reclaim(alloc, ctx->callback_vector);
    }

    /* if the context vector is allocated, reclaim it. */
    if (NULL != ctx->context_vector)
    {
        context_vector_retval = allocator_reclaim(alloc, ctx->context_vector);
    }

    /* check the error codes from each of the release / reclaim operations,
     * bubbling up the first error to the caller, or STATUS_SUCCESS if
     * everything succeeded. */
    if (STATUS_SUCCESS != idle_fiber_retval)
    {
        return idle_fiber_retval;
    }
    else if (STATUS_SUCCESS != fibers_by_pointer_retval)
    {
        return fibers_by_pointer_retval;
    }
    else if (STATUS_SUCCESS != disciplines_by_uuid_retval)
    {
        return disciplines_by_uuid_retval;
    }
    else if (STATUS_SUCCESS != run_queue_retval)
    {
        return run_queue_retval;
    }
    else if (STATUS_SUCCESS != callback_vector_retval)
    {
        return callback_vector_retval;
    }
    else if (STATUS_SUCCESS != context_vector_retval)
    {
        return context_vector_retval;
    }
    else
    {
        return STATUS_SUCCESS;
    }
}

/**
 * \brief Release the disciplined scheduler context resources, then release the
 * scheduler.
 *
 * \param r         The disciplined scheduler's resource pointer.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status fiber_scheduler_disciplined_resource_release(resource* r)
{
    status context_retval = STATUS_SUCCESS;
    status sched_retval = STATUS_SUCCESS;
    fiber_scheduler* sched = (fiber_scheduler*)r;
    fiber_scheduler_disciplined_context* ctx =
        (fiber_scheduler_disciplined_context*)sched->context;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    MODEL_ASSERT(prop_fiber_scheduler_disciplined_context_valid(ctx));

    /* copy over the base resource so the scheduler can be cleaned up. */
    memcpy(
        &sched->hdr, &ctx->cached_scheduler_resource_handler, sizeof(resource));

    /* clean up the scheduler. */
    sched_retval = resource_release(fiber_scheduler_resource_handle(sched));

    /* clean up the context. */
    context_retval = resource_release(&ctx->hdr);

    /* return an error code if either failed. */
    if (STATUS_SUCCESS != context_retval)
    {
        return context_retval;
    }
    else if (STATUS_SUCCESS != sched_retval)
    {
        return sched_retval;
    }
    else
    {
        return STATUS_SUCCESS;
    }
}

/**
 * \brief The disciplined fiber scheduler callback function.
 *
 * This function receives events from fibers and can send events to a fiber it
 * resumes. This function is responsible for queuing fibers and for returning
 * control to the main thread.
 *
 * \param context       The user context for this \ref fiber_scheduler.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The event causing the fiber to yield.
 * \param yield_param   Pointer to the yield parameter.
 * \param resume_fib    Pointer to receive the fiber to be resumed.
 * \param resume_id     Pointer to receive the fiber resume event discipline id.
 * \param resume_event  The event causing the fiber to be resumed.
 * \param resume_param  Pointer to the resume parameter.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when a new fiber is to be resumed.
 *      - any other non-zero status code will result in thread termination and
 *        the process aborting.
 */
static status fiber_scheduler_disciplined_callback(
    void* context, fiber* yield_fib, int yield_event, void* yield_param,
    fiber** resume_fib, const rcpr_uuid** resume_id, int* resume_event,
    void** resume_param)
{
    status retval;
    fiber_scheduler_disciplined_context* ctx =
        (fiber_scheduler_disciplined_context*)context;

    /* verify that we can handle this yield event. */
    if ((size_t)yield_event >= ctx->callback_vector_size)
    {
        return ERROR_FIBER_SCHEDULER_BAD_YIELD_EVENT;
    }

    /* vectored dispatch to the correct callback. */
    retval =
        ctx->callback_vector[yield_event](
            ctx->context_vector[yield_event], yield_fib, yield_event,
            yield_param);

    /* if the dispatch failed, return the error code. */
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* otherwise, try to get an event from the run queue. */
    if (queue_count(ctx->run_queue) != 0)
    {
        /* get the next fiber from the run queue. */
        resource* next_fiber_resource = NULL;
        retval = queue_pop(ctx->run_queue, &next_fiber_resource);
        if (STATUS_SUCCESS != retval)
        {
            return retval;
        }

        /* downcast to a fiber instance. */
        fiber* next_fiber = (fiber*)next_fiber_resource;
        MODEL_ASSERT(prop_fiber_valid(next_fiber));

        /* set that fiber as the resume fiber. */
        *resume_fib = next_fiber;
        *resume_id = next_fiber->restore_discipline_id;
        *resume_event = next_fiber->restore_reason_code;
        *resume_param = next_fiber->restore_param;

        return STATUS_SUCCESS;
    }
    /* otherwise, switch to the idle fiber. */
    else if (NULL != ctx->idle_fiber)
    {
        *resume_fib = ctx->idle_fiber;
        *resume_id = &FIBER_SCHEDULER_INTERNAL_DISCIPLINE;
        *resume_event = FIBER_SCHEDULER_RESUME_EVENT_IDLE;
        *resume_param = NULL;

        return STATUS_SUCCESS;
    }
    /* otherwise, the scheduler is exhausted... */
    else
    {
        return ERROR_FIBER_SCHEDULER_EXHAUSTED;
    }
}

/**
 * \brief Handle the internal run event callback.
 *
 * \param context       The user context for this
 *                      \ref fiber_scheduler_discipline.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The event causing the fiber to yield.
 * \param yield_param   Pointer to the yield parameter.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when this discipline callback succeeded.
 *      - any other non-zero status code will result in thread termination and
 *        the process aborting.
 */
static status fiber_scheduler_disciplined_run_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param)
{
    fiber_scheduler_disciplined_context* ctx =
        (fiber_scheduler_disciplined_context*)context;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_valid(yield_fib));
    MODEL_ASSERT(prop_fiber_scheduler_disciplined_context_valid(ctx));

    /* ignore parameters. */
    (void)yield_event;
    (void)yield_param;

    /* add the yield fiber to the back of the queue. */
    return
        disciplined_fiber_scheduler_add_fiber_to_run_queue(
            ctx->sched, yield_fib, &FIBER_SCHEDULER_INTERNAL_DISCIPLINE,
            FIBER_SCHEDULER_RESUME_EVENT_RUN, NULL);
}

/**
 * \brief Handle the internal main event callback.
 *
 * \param context       The user context for this
 *                      \ref fiber_scheduler_discipline.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The event causing the fiber to yield.
 * \param yield_param   Pointer to the yield parameter.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when this discipline callback succeeded.
 *      - any other non-zero status code will result in thread termination and
 *        the process aborting.
 */
static status fiber_scheduler_disciplined_main_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param)
{
    fiber_scheduler_disciplined_context* ctx =
        (fiber_scheduler_disciplined_context*)context;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_valid(yield_fib));
    MODEL_ASSERT(prop_fiber_scheduler_disciplined_context_valid(ctx));

    /* ignore parameters. */
    (void)yield_event;
    (void)yield_param;

    /* set the main fiber. */
    ctx->main_fiber = yield_fib;

    /* set the yielding fiber as the next fiber to run. */
    /* we must do this by hand because ctx->sched is not yet set. */
    yield_fib->restore_discipline_id = &FIBER_SCHEDULER_INTERNAL_DISCIPLINE;;
    yield_fib->restore_reason_code = FIBER_SCHEDULER_RESUME_EVENT_MAIN;
    yield_fib->restore_param = NULL;

    return queue_insert(ctx->run_queue, fiber_resource_handle(yield_fib));
}

/**
 * \brief Handle the internal add fiber event callback.
 *
 * \param context       The user context for this
 *                      \ref fiber_scheduler_discipline.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The event causing the fiber to yield.
 * \param yield_param   Pointer to the yield parameter.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when this discipline callback succeeded.
 *      - any other non-zero status code will result in thread termination and
 *        the process aborting.
 */
static status fiber_scheduler_disciplined_add_fiber_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param)
{
    status retval;
    fiber_scheduler_disciplined_context* ctx =
        (fiber_scheduler_disciplined_context*)context;
    fiber* new_fib = (fiber*)yield_param;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_valid(yield_fib));
    MODEL_ASSERT(prop_fiber_valid(new_fib));
    MODEL_ASSERT(prop_fiber_scheduler_disciplined_context_valid(ctx));

    /* ignore parameters. */
    (void)yield_event;
    (void)yield_param;

    /* save the fiber. */
    retval =
        rbtree_insert(ctx->fibers_by_pointer, fiber_resource_handle(new_fib));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* append this fiber to the run queue. */
    retval =
        disciplined_fiber_scheduler_add_fiber_to_run_queue(
            ctx->sched, new_fib, &FIBER_SCHEDULER_INTERNAL_DISCIPLINE,
            FIBER_SCHEDULER_RESUME_EVENT_ADD_FIBER, NULL);
    if (STATUS_SUCCESS != retval)
    {
        /* remove the fiber from the tree before returning an error status. */
        resource* dummy = NULL;
        status delete_retval = rbtree_delete(
            &dummy, ctx->fibers_by_pointer, fiber_resource_handle(new_fib));

        /* return the last error code to occur. */
        if (STATUS_SUCCESS != delete_retval)
            return delete_retval;
        else
            return retval;
    }

    /* insert the yielding fiber into the beginning of the run queue. */
    retval =
        disciplined_fiber_scheduler_set_next_fiber_to_run(
            ctx->sched, yield_fib, &FIBER_SCHEDULER_INTERNAL_DISCIPLINE,
            FIBER_SCHEDULER_RESUME_EVENT_ADD_FIBER, NULL);
    if (STATUS_SUCCESS != retval)
    {
        /* bubble up the error. */
        /* TODO - deal with ownership issues for added fiber. */
        return retval;
    }

    /* if the management fiber exists, */
    /* insert the management discipline into the beginning of the run queue. */
    if (NULL != ctx->management_fiber)
    {
        retval =
            disciplined_fiber_scheduler_set_next_fiber_to_run(
                ctx->sched, ctx->management_fiber,
                &FIBER_SCHEDULER_MANAGEMENT_DISCIPLINE,
                FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_FIBER_ADD,
                new_fib);
        if (STATUS_SUCCESS != retval)
        {
            return retval;
        }

        /* clear the management fiber until it yields again. */
        ctx->management_fiber = NULL;
    }

    /* success. */
    return STATUS_SUCCESS;
}

/**
 * \brief Handle the internal fiber stop event callback.
 *
 * \param context       The user context for this
 *                      \ref fiber_scheduler_discipline.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The event causing the fiber to yield.
 * \param yield_param   Pointer to the yield parameter.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when this discipline callback succeeded.
 *      - any other non-zero status code will result in thread termination and
 *        the process aborting.
 */
static status fiber_scheduler_disciplined_stop_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param)
{
    status retval;
    fiber_scheduler_disciplined_context* ctx =
        (fiber_scheduler_disciplined_context*)context;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_valid(yield_fib));
    MODEL_ASSERT(prop_fiber_valid(new_fib));
    MODEL_ASSERT(prop_fiber_scheduler_disciplined_context_valid(ctx));

    /* ignore parameters. */
    (void)yield_event;
    (void)yield_param;

    /* if the management fiber is set, let it deal with the stop event. */
    if (NULL != ctx->management_fiber)
    {
        retval =
            disciplined_fiber_scheduler_set_next_fiber_to_run(
                ctx->sched, ctx->management_fiber,
                &FIBER_SCHEDULER_MANAGEMENT_DISCIPLINE,
                FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_FIBER_STOP,
                yield_fib);
        if (STATUS_SUCCESS != retval)
        {
            return retval;
        }

        /* clear the management fiber until it yields again. */
        ctx->management_fiber = NULL;
    }

    /* NOTE: the ONLY way the fiber is removed from the tree is via the
     * management fiber, or when this scheduler is released. This is because the
     * stack for the given stopped fiber may still be in use by this scheduler
     * callback. */

    /* success. */
    return STATUS_SUCCESS;
}

/**
 * \brief Handle the internal resource release event callback.
 *
 * \param context       The user context for this
 *                      \ref fiber_scheduler_discipline.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The event causing the fiber to yield.
 * \param yield_param   Pointer to the yield parameter.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when this discipline callback succeeded.
 *      - any other non-zero status code will result in thread termination and
 *        the process aborting.
 */
static status fiber_scheduler_disciplined_resource_release_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param)
{
    fiber_scheduler_disciplined_context* ctx =
        (fiber_scheduler_disciplined_context*)context;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_valid(yield_fib));
    MODEL_ASSERT(prop_fiber_scheduler_disciplined_context_valid(ctx));

    /* ignore parameters. */
    (void)yield_event;
    (void)yield_param;

    /* insert the yielding fiber into the beginning of the run queue. */
    return
        disciplined_fiber_scheduler_set_next_fiber_to_run(
            ctx->sched, yield_fib, &FIBER_SCHEDULER_INTERNAL_DISCIPLINE,
            FIBER_SCHEDULER_RESUME_EVENT_RESOURCE_RELEASE, NULL);
}

/**
 * \brief Handle the management discipline yield receive event.
 *
 * \param context       The user context for this
 *                      \ref fiber_scheduler_discipline.
 * \param yield_fib     The yielding fiber.
 * \param yield_event   The event causing the fiber to yield.
 * \param yield_param   Pointer to the yield parameter.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS is returned when this discipline callback succeeded.
 *      - any other non-zero status code will result in thread termination and
 *        the process aborting.
 */
static status
fiber_scheduler_disciplined_management_yield_event_callback_handler(
    void* context, fiber* yield_fib, int yield_event, void* yield_param)
{
    fiber_scheduler_disciplined_context* ctx =
        (fiber_scheduler_disciplined_context*)context;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_valid(yield_fib));
    MODEL_ASSERT(prop_fiber_scheduler_disciplined_context_valid(ctx));

    /* ignore parameters. */
    (void)yield_event;
    (void)yield_param;

    /* set the management fiber. */
    ctx->management_fiber = yield_fib;

    /* success. Run the next fiber on the queue, or the idle fiber. */
    return STATUS_SUCCESS;
}
