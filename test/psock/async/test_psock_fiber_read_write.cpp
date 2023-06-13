/**
 * \file test/psock/async/test_psock_fiber_read_write.cpp
 *
 * \brief Test that reading and writing fibers don't hang.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <rcpr/psock.h>
#include <rcpr/resource/protected.h>
#include <rcpr/socket_utilities.h>
#include <rcpr/uuid.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_psock;
RCPR_IMPORT_resource;
RCPR_IMPORT_socket_utilities;
RCPR_IMPORT_uuid;

TEST_SUITE(psock_fiber_read_write);

typedef struct main_context main_context;
struct main_context
{
    RCPR_SYM(resource) hdr;
    RCPR_SYM(allocator)* alloc;
    RCPR_SYM(fiber_scheduler)* sched;
    RCPR_SYM(psock)* sock;
    size_t count;
    bool error;
};

typedef struct test_fiber_context test_fiber_context;
struct test_fiber_context
{
    RCPR_SYM(resource) hdr;
    RCPR_SYM(allocator)* alloc;
    main_context* ctx;
    RCPR_SYM(psock)* sock;
};

static status main_context_create(
    main_context** ctx, fiber_scheduler* sched, RCPR_SYM(allocator)* alloc);
static status main_context_resource_release(RCPR_SYM(resource)* r);
static status test_fiber_create(
    RCPR_SYM(fiber)** fib, RCPR_SYM(allocator)* alloc, main_context* mctx,
    int sock, status (*fiber_entry)(void*));
static status test_fiber_context_resource_release(RCPR_SYM(resource)* r);
static status fiber_manager_entry(void* vctx);
static status client_fiber_entry(void* vctx);
static status server_fiber_entry(void* vctx);

/**
 * Spawn a dozen readers and writers, and have them send large messages to each
 * other.
 */
TEST(basics)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    main_context* ctx = nullptr;
    fiber* mgmt_fiber = nullptr;
    fiber* tmp_fiber = nullptr;
    fiber* main_fiber = nullptr;
    int mgmt_desc, main_desc;
    psock* main_sock;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a fiber scheduler with disciplines. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* create the main context. */
    TEST_ASSERT(
        STATUS_SUCCESS == main_context_create(&ctx, sched, alloc));

    /* get the main fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            disciplined_fiber_scheduler_main_fiber_get(&main_fiber, sched));

    /* create a socket pair for the management fiber and main fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(
                AF_UNIX, SOCK_STREAM, 0, &mgmt_desc, &main_desc));

    /* create a psock instance for the main descriptor. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(&main_sock, alloc, main_desc));

    /* wrap this psock instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_wrap_async(&main_sock, alloc, main_fiber, main_sock));

    /* create a psock instance for the management descriptor. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(&ctx->sock, alloc, mgmt_desc));

    /* create the management fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_create(
                &mgmt_fiber, alloc, sched, 1024 * 1024, ctx,
                &fiber_manager_entry));

    /* wrap the management psock instance. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_wrap_async(&ctx->sock, alloc, mgmt_fiber, ctx->sock));

    /* add the management fiber. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_add(sched, mgmt_fiber));

    /* give the management fiber a chance to start. */
    TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_run(sched));

    /* add the client and server fibers. */
    for (int i = 0; i < 50; ++i)
    {
        int left, right;

        /* create the socket pair for these two. */
        TEST_ASSERT(
            STATUS_SUCCESS ==
                socket_utility_socketpair(
                    AF_UNIX, SOCK_STREAM, 0, &left, &right));

        /* create the server test context. */
        TEST_ASSERT(
            STATUS_SUCCESS ==
                test_fiber_create(
                    &tmp_fiber, alloc, ctx, left, &server_fiber_entry));

        /* add this fiber to the scheduler. */
        TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_add(sched, tmp_fiber));

        /* create the server test context. */
        TEST_ASSERT(
            STATUS_SUCCESS ==
                test_fiber_create(
                    &tmp_fiber, alloc, ctx, right, &client_fiber_entry));

        /* add this fiber to the scheduler. */
        TEST_ASSERT(STATUS_SUCCESS == fiber_scheduler_add(sched, tmp_fiber));
    }

    /* wait for the count to reach zero. */
    bool unused;
    TEST_ASSERT(STATUS_SUCCESS == psock_read_boxed_bool(main_sock, &unused));

    /* we should have had no errors. */
    TEST_ASSERT(!ctx->error);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(main_sock)));
    TEST_ASSERT(STATUS_SUCCESS == resource_release(&ctx->hdr));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * \brief Create a test fiber context.
 *
 * \param fib       Pointer to receive the fiber intance pointer on success.
 * \param alloc     The allocator to use for this operation.
 * \param mctx      Main context.
 * \param sock      The socket to use for this operation.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status test_fiber_create(
    RCPR_SYM(fiber)** fib, RCPR_SYM(allocator)* alloc, main_context* mctx,
    int sock, status (*fiber_entry)(void*))
{
    status retval, release_retval;
    test_fiber_context* tmp = NULL;
    fiber* inst = NULL;
    psock* ps = NULL;

    /* allocate memory for the context. */
    retval = allocator_allocate(alloc, (void**)&tmp, sizeof(*tmp));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* initialize resource. */
    memset(tmp, 0, sizeof(*tmp));
    resource_init(&tmp->hdr, &test_fiber_context_resource_release);
    tmp->alloc = alloc;
    tmp->ctx = mctx;

    /* create the fiber instance. */
    retval =
        fiber_create(
            &inst, alloc, mctx->sched, 1024 * 1024, tmp, fiber_entry);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_tmp;
    }

    /* create a psock instance for this descriptor. */
    retval = psock_create_from_descriptor(&ps, alloc, sock);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_inst;
    }

    /* wrap this psock instance as an async socket. */
    retval = psock_create_wrap_async(&tmp->sock, alloc, inst, ps);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_ps;
    }

    /* increment the number of contexts. */
    tmp->ctx->count += 1;

    /* assign this instance to the caller. */
    *fib = inst;
    tmp = NULL;
    ps = NULL;
    inst = NULL;
    retval = STATUS_SUCCESS;
    goto done;

cleanup_ps:
    if (NULL != ps)
    {
        release_retval = resource_release(psock_resource_handle(ps));
        if (STATUS_SUCCESS != release_retval)
        {
            retval = release_retval;
        }
    }

cleanup_inst:
    if (NULL != inst)
    {
        release_retval = resource_release(fiber_resource_handle(inst));
        if (STATUS_SUCCESS != release_retval)
        {
            retval = release_retval;
        }
    }

cleanup_tmp:
    if (NULL != tmp)
    {
        release_retval = resource_release(&tmp->hdr);
        if (STATUS_SUCCESS != release_retval)
        {
            retval = release_retval;
        }
    }

done:
    return retval;
}

/**
 * \brief Release a test fiber context resource.
 *
 * \param r         Pointer to the resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status test_fiber_context_resource_release(RCPR_SYM(resource)* r)
{
    test_fiber_context* ctx = (test_fiber_context*)r;
    status reclaim_retval = STATUS_SUCCESS;
    status sock_release_retval = STATUS_SUCCESS;

    /* cache allocator. */
    allocator* alloc = ctx->alloc;

    /* release sock if set. */
    if (NULL != ctx->sock)
    {
        sock_release_retval =
            resource_release(psock_resource_handle(ctx->sock));
    }

    /* decrement count. */
    ctx->ctx->count -= 1;

    /* clear memory. */
    memset(ctx, 0, sizeof(*ctx));

    /* reclaim memory. */
    reclaim_retval = allocator_reclaim(alloc, ctx);

    /* decode return value. */
    if (STATUS_SUCCESS != sock_release_retval)
    {
        return sock_release_retval;
    }
    else
    {
        return reclaim_retval;
    }
}

/**
 * \brief Create the main context.
 *
 * \param ctx       Pointer to receive the main context pointer on success.
 * \param sched     Pointer to the fiber scheduler.
 * \param alloc     The allocator to use for this operation.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status main_context_create(
    main_context** ctx, fiber_scheduler* sched, RCPR_SYM(allocator)* alloc)
{
    status retval;
    main_context* tmp = NULL;

    /* allocate memory for this context. */
    retval = allocator_allocate(alloc, (void**)&tmp, sizeof(*tmp));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* initialize resource. */
    memset(tmp, 0, sizeof(*tmp));
    resource_init(&tmp->hdr, &main_context_resource_release);
    tmp->alloc = alloc;
    tmp->sched = sched;

    /* success. */
    *ctx = tmp;
    tmp = NULL;
    retval = STATUS_SUCCESS;
    goto done;

done:
    return retval;
}

/**
 * \brief Release a main context resource.
 *
 * \param r         Pointer to the resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status main_context_resource_release(RCPR_SYM(resource)* r)
{
    main_context* ctx = (main_context*)r;
    status reclaim_retval = STATUS_SUCCESS;
    status sock_release_retval = STATUS_SUCCESS;

    /* cache allocator. */
    allocator* alloc = ctx->alloc;

    /* release sock if set. */
    if (NULL != ctx->sock)
    {
        sock_release_retval =
            resource_release(psock_resource_handle(ctx->sock));
    }

    /* clear memory. */
    memset(ctx, 0, sizeof(*ctx));

    /* reclaim memory. */
    reclaim_retval = allocator_reclaim(alloc, ctx);

    /* decode return status. */
    if (STATUS_SUCCESS != sock_release_retval)
    {
        return sock_release_retval;
    }
    else
    {
        return reclaim_retval;
    }
}

/**
 * \brief Entry point for the management fiber.
 *
 * This fiber manages cleanup for fibers as they stop.
 *
 * \param vctx          The type erased main context.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status fiber_manager_entry(void* vctx)
{
    status retval;
    const rcpr_uuid* resume_id;
    int resume_event;
    void* resume_param;
    fiber* stopped_fiber;

    main_context* ctx = (main_context*)vctx;

    for (;;)
    {
        /* receive a management event. */
        retval =
            disciplined_fiber_scheduler_receive_management_event(
                ctx->sched, &resume_id, &resume_event, &resume_param);
        if (STATUS_SUCCESS != retval)
        {
            return retval;
        }

        /* decode management event. */
        if (
            !memcmp(
                resume_id, &FIBER_SCHEDULER_MANAGEMENT_DISCIPLINE,
                sizeof(rcpr_uuid)))
        {
            /* decode the event code. */
            switch (resume_event)
            {
                /* a fiber has been stopped. Clean it up. */
                case FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_FIBER_STOP:
                    stopped_fiber = (fiber*)resume_param;

                    /* instruct the fiber scheduler to remove the fiber
                     * reference. */
                    retval =
                        disciplined_fiber_scheduler_remove_fiber(
                            ctx->sched, stopped_fiber);
                    if (STATUS_SUCCESS != retval)
                    {
                    }
                    else
                    {
                        /* release the fiber. */
                        retval =
                            resource_release(
                                fiber_resource_handle(stopped_fiber));
                        if (STATUS_SUCCESS != retval)
                        {
                        }
                    }

                    /* if the count is zero, signal the main fiber and exit. */
                    if (ctx->count == 0)
                    {
                        retval = psock_write_boxed_bool(ctx->sock, true);
                        goto done;
                    }
                    break;

                /* a quiesce request. */
                case FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_QUIESCE_REQUEST:
                    break;

                /* a termination request. */
                case FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_TERMINATION_REQUEST:
                    break;

                /* we don't care about any other management event. */
                default:
                    break;
            }
        }
        /* ignore any other event. */
        else
        {
            continue;
        }
    }

done:

    return retval;
}

/**
 * \brief Entry point for the client test fiber.
 *
 * This fiber sends a request to the server test fiber and reads a response.
 *
 * \param vctx          The type erased test context.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status client_fiber_entry(void* vctx)
{
    status retval, release_retval;
    test_fiber_context* ctx = (test_fiber_context*)vctx;
    uint8_t* buffer = NULL;
    uint8_t* read_buffer = NULL;
    size_t buffer_size = 25000000;
    size_t read_buffer_size;

    /* allocate a large buffer to write to the socket. */
    retval = allocator_allocate(ctx->alloc, (void**)&buffer, buffer_size);
    if (STATUS_SUCCESS != retval)
    {
        ctx->ctx->error = true;
        goto cleanup_ctx;
    }

    /* clear memory. */
    memset(buffer, 0, buffer_size);

    /* write this buffer to the server. */
    retval = psock_write_boxed_data(ctx->sock, buffer, buffer_size);
    if (STATUS_SUCCESS != retval)
    {
        ctx->ctx->error = true;
        goto cleanup_buffer;
    }

    /* read the response buffer from the server. */
    retval =
        psock_read_boxed_data(
            ctx->sock, ctx->alloc, (void**)&read_buffer, &read_buffer_size);
    if (STATUS_SUCCESS != retval)
    {
        ctx->ctx->error = true;
        goto cleanup_buffer;
    }

    /* success. */
    retval = STATUS_SUCCESS;
    goto cleanup_read_buffer;

cleanup_read_buffer:
    release_retval = allocator_reclaim(ctx->alloc, read_buffer);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_buffer:
    release_retval = allocator_reclaim(ctx->alloc, buffer);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_ctx:
    release_retval = resource_release(&ctx->hdr);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

    return retval;
}

/**
 * \brief Entry point for the server test fiber.
 *
 * This fiber receives a request from the client test fiber and sends a
 * response.
 *
 * \param vctx          The type erased test context.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status server_fiber_entry(void* vctx)
{
    status retval, release_retval;
    test_fiber_context* ctx = (test_fiber_context*)vctx;
    uint8_t* read_buffer = NULL;
    size_t read_buffer_size;

    /* read the request buffer from the client. */
    retval =
        psock_read_boxed_data(
            ctx->sock, ctx->alloc, (void**)&read_buffer, &read_buffer_size);
    if (STATUS_SUCCESS != retval)
    {
        ctx->ctx->error = true;
        goto cleanup_ctx;
    }

    /* write this buffer to the client. */
    retval = psock_write_boxed_data(ctx->sock, read_buffer, read_buffer_size);
    if (STATUS_SUCCESS != retval)
    {
        ctx->ctx->error = true;
        goto cleanup_read_buffer;
    }

    /* success. */
    retval = STATUS_SUCCESS;
    goto cleanup_read_buffer;

cleanup_read_buffer:
    release_retval = allocator_reclaim(ctx->alloc, read_buffer);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_ctx:
    release_retval = resource_release(&ctx->hdr);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

    return retval;
}
