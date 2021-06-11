/**
 * \file psock/psock_create_wrap_async.c
 *
 * \brief Wrap a \ref psock instance to make it asynchronous.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/fiber.h>
#include <rcpr/model_assert.h>
#include <rcpr/psock.h>
#include <rcpr/socket_utilities.h>
#include <string.h>

#include "psock_internal.h"

/* forward decls. */
static status psock_wrap_async_release(resource*);
static status psock_create_wrap_async_add_psock_discipline(
    fiber_scheduler_discipline** disc, allocator* a, fiber_scheduler* sched);

MODEL_STRUCT_TAG_GLOBAL_EXTERN(psock);

/**
 * \brief Wrap a \ref psock instance with an async \ref psock instance that
 * transforms reads or writes on the underlying \ref psock with yields to the
 * given \ref fiber_scheduler.
 *
 * \param sock          Pointer to the \ref psock pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this
 *                      wrapping \ref psock resource.
 * \param sched         The \ref fiber_scheduler to yield on a read / write call
 *                      that would block.  This must be a disciplined fiber
 *                      scheduler.
 * \param child         The child \ref psock instance that this \ref psock
 *                      instance wraps.
 *
 * \note This \ref psock is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref psock_resource_handle on this \ref psock instance.  The \ref psock
 * instance owns the wrapped \p child \ref psock, which will be released when
 * this resource is released.
 *
 * It is assumed that the \ref psock wrapper instance created by this call will
 * be accessed from a \ref fiber.  If a read or write fails because
 * it would block, then this \ref fiber yields to the given scheduler with a
 * message indicating that it is yielding on a read or a write for the
 * underlying descriptor.  The scheduler will then resume this \ref fiber when
 * the OS notifies it that the descriptor is again available for read or write.
 *
 * After this call completes successfully, calls to \ref psock utility functions
 * will block the calling fiber if the I/O would normally block.  If multiple
 * fibers are scheduled to run, the scheduler will switch to the next available
 * fiber.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *      - ERROR_PSOCK_UNSUPPORTED_TYPE if the type of psock pointed to by
 *        \p child is not supported for async wrappering. Currently, only
 *        descriptor children are supported.
 *
 * \pre
 *      - \p sock must be a pointer to a pointer to a \ref psock instance
 *        and must not be NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p sched must reference a valid \ref fiber_scheduler and must not be
 *        NULL.
 *      - \p child must reference a valid \ref psock instance and must not be
 *        NULL.
 *
 * \post
 *      - On success, \p sock is set to a pointer to a valid \ref psock
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p sock is unchanged and an error status is returned.
 */
status FN_DECL_MUST_CHECK
psock_create_wrap_async(
    psock** sock, allocator* a, fiber_scheduler* sched, psock* child)
{
    status retval, release_retval;
    fiber_scheduler_discipline* disc;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != sock);
    MODEL_ASSERT(prop_allocator_valid(a));
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    MODEL_ASSERT(prop_psock_valid(child));
    MODEL_ASSERT(PSOCK_TYPE_DESCRIPTOR == child->type);

    /* Verify that the psock type is descriptor. */
    if (PSOCK_TYPE_DESCRIPTOR != child->type)
    {
        retval = ERROR_PSOCK_UNSUPPORTED_TYPE;
        goto done;
    }

    /* get the real descriptor psock instance. */
    psock_from_descriptor* pchild = (psock_from_descriptor*)child;

    /* Check the scheduler to see if the psock I/O discipline exists. */
    retval =
        fiber_scheduler_discipline_find(
            &disc, sched, &FIBER_SCHEDULER_PSOCK_IO_DISCIPLINE);
    if (ERROR_FIBER_SCHEDULER_DISCIPLINE_NOT_FOUND == retval)
    {
        /* If it does not, create discipline and add it. */
        retval =
            psock_create_wrap_async_add_psock_discipline(
                &disc, a, sched);
        if (STATUS_SUCCESS != retval)
        {
            goto done;
        }
    }
    else if (STATUS_SUCCESS != retval)
    {
        goto done;
    }
    
    /* Create wrapped struct. */
    psock_wrap_async* ps = NULL;
    retval =
        allocator_allocate(a, (void**)&ps, sizeof(psock_wrap_async));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear out the structure. */
    memset(ps, 0, sizeof(psock_wrap_async));

    /* the tag is not set by default. */
    MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        ps->hdr.MODEL_STRUCT_TAG_REF(psock), psock);

    /* set the tag. */
    MODEL_STRUCT_TAG_INIT(ps->hdr.MODEL_STRUCT_TAG_REF(psock), psock);

    /* set the release method. */
    resource_init(&ps->hdr.hdr, &psock_wrap_async_release);

    /* save the child psock. */
    ps->wrapped = child;

    /* save the scheduler. */
    ps->sched = sched;

    /* add the discipline reference to the async wrap. */
    ps->psock_discipline = disc;

    /* set the type. */
    ps->hdr.type = PSOCK_TYPE_DESCRIPTOR;

    /* set the allocator. */
    ps->hdr.alloc = a;

    /* set the callbacks. */
    ps->hdr.read_fn = &psock_wrap_async_read;
    ps->hdr.write_fn = &psock_wrap_async_write;
    ps->hdr.accept_fn = &psock_wrap_async_accept;

    /* set the descriptor to non-blocking. */
    retval = socket_utility_set_nonblock(pchild->descriptor);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_psock;
    }

    /* set the socket. */
    *sock = &ps->hdr;

    /* verify that this structure is now valid. */
    MODEL_ASSERT(prop_psock_valid(*sock));

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_psock:
    release_retval = allocator_reclaim(a, ps);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

/**
 * \brief Release the async wrap instance.
 *
 * \param r         The resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status psock_wrap_async_release(resource* r)
{
    psock_wrap_async* ps = (psock_wrap_async*)r;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_psock_valid(&ps->hdr));

    /* release the child resource. */
    int child_retval = resource_release(psock_resource_handle(ps->wrapped));

    /* cache the allocator. */
    allocator* alloc = ps->hdr.alloc;

    /* reclaim the memory for this psock instance. */
    int reclaim_retval = allocator_reclaim(alloc, ps);

    if (STATUS_SUCCESS != child_retval)
    {
        return child_retval;
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

/**
 * \brief Create the psock discipline, and add it to the given scheduler, then
 * create and add the idle fiber to the scheduler.
 *
 * \param disc      The fiber scheduler discipline to create.
 * \param a         The allocator to use.
 * \param sched     The scheduler to which the discipline and idle fiber should
 *                  be added.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status psock_create_wrap_async_add_psock_discipline(
    fiber_scheduler_discipline** disc, allocator* a, fiber_scheduler* sched)
{
    status retval, release_retval;
    resource* context;
    fiber* idle_fiber;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != disc);
    MODEL_ASSERT(prop_allocator_valid(a));
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* create the fiber scheduler discipline. */
    retval =
        psock_fiber_scheduler_discipline_create(disc, &context, sched, a);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* add this discipline to the scheduler. */
    retval = fiber_scheduler_discipline_add(sched, *disc);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_discipline;
    }

    /* create the idle fiber. */
    retval =
        fiber_create(
            &idle_fiber, a, sched, 16384, context, &psock_idle_fiber_entry);
    if (STATUS_SUCCESS != retval)
    {
        /* note: if we successfully added the discipline to the scheduler, it
         * owns the discipline, so we don't need to release it anymore. */
        goto done;
    }

    /* add the idle fiber to the scheduler. */
    retval = fiber_scheduler_add(sched, idle_fiber);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_idle_fiber;
    }

    /* set the idle fiber. */
    retval = disciplined_fiber_scheduler_set_idle_fiber(sched, idle_fiber);
    if (STATUS_SUCCESS != retval)
    {
        /* note: if we've added the fiber, we can no longer clean it up. But,
         * the add won't fail. */
        /* TODO - make set idle fiber return void. */
        goto done;
    }

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_idle_fiber:
    release_retval = resource_release(fiber_resource_handle(idle_fiber));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

    /* skip the discipline cleanup; it is now handled by the scheduler. */
    goto done;

cleanup_discipline:
    release_retval =
        resource_release(fiber_scheduler_discipline_resource_handle(*disc));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }
    *disc = NULL;

done:
    return retval;
}
