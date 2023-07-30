/**
 * \file
 * test/fiber/test_disciplined_fiber_scheduler_send_quiesce_request_to_all.cpp
 *
 * \brief Unit tests for
 * disciplined_fiber_scheduler_send_quiesce_request_to_all.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <rcpr/psock.h>
#include <rcpr/resource/protected.h>
#include <rcpr/socket_utilities.h>
#include <rcpr/vtable.h>
#include <string.h>
#include <unistd.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_psock;
RCPR_IMPORT_resource;
RCPR_IMPORT_socket_utilities;

TEST_SUITE(disciplined_fiber_scheduler_send_quiesce_request_to_all);

#define FIBER_STACK (1024 * 1024)
#define TEST_FIBERS 5

typedef struct test_fiber_context test_fiber_context;
struct test_fiber_context
{
    resource hdr;

    allocator* alloc;
    psock* sock;
    fiber* fib;
};

static status test_fiber_entry(void* context)
{
    status retval;
    test_fiber_context* ctx = (test_fiber_context*)context;
    int64_t val;

    for (;;)
    {
        /* read an integer from the stream. */
        retval = psock_read_boxed_int64(ctx->sock, &val);
        if (STATUS_SUCCESS != retval)
        {
            goto cleanup_ctx;
        }

        /* square this integer. */
        val *= val;

        /* write this squared value to the stream. */
        retval = psock_write_boxed_int64(ctx->sock, val);
        if (STATUS_SUCCESS != retval)
        {
            goto cleanup_ctx;
        }
    }

cleanup_ctx:
    resource_release(&ctx->hdr);

    return retval;
}

static status release_test_fiber_context(resource* r)
{
    status release_sock_retval = STATUS_SUCCESS;
    status reclaim_ctx_retval = STATUS_SUCCESS;
    test_fiber_context* ctx = (test_fiber_context*)r;

    allocator* alloc = ctx->alloc;

    if (nullptr != ctx->sock)
    {
        release_sock_retval =
            resource_release(psock_resource_handle(ctx->sock));
    }

    reclaim_ctx_retval =
        allocator_reclaim(alloc, ctx);

    if (STATUS_SUCCESS != release_sock_retval)
    {
        return release_sock_retval;
    }
    else
    {
        return reclaim_ctx_retval;
    }
}

/* the vtable entry for the test fiber context instance. */
RCPR_VTABLE
resource_vtable test_fiber_context_vtable = {
    &release_test_fiber_context };

/**
 * \brief Create a test fiber and a socket for communicating with it.
 */
static status create_test_fiber(
    fiber** fib, psock** sock, fiber_scheduler* sched, allocator* alloc)
{
    status retval, release_retval;
    test_fiber_context* ctx = nullptr;
    int left = -1, right = -1;
    psock* lsock = nullptr;
    psock* rsock = nullptr;
    fiber* mainfib = nullptr;

    /* allocate the test fiber context. */
    retval =
        allocator_allocate(alloc, (void**)&ctx, sizeof(test_fiber_context));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear the test fiber context. */
    memset(ctx, 0, sizeof(test_fiber_context));

    /* init the structure. */
    resource_init(&ctx->hdr, &test_fiber_context_vtable);
    ctx->alloc = alloc;

    /* create the socket pair. */
    retval = socket_utility_socketpair(AF_UNIX, SOCK_STREAM, 0, &left, &right);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_ctx;
    }

    /* create the left psock wrapper. */
    retval = psock_create_from_descriptor(&lsock, alloc, left);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_sockets;
    }

    /* create the right psock wrapper. */
    retval = psock_create_from_descriptor(&rsock, alloc, right);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_lsock;
    }

    /* get the main fiber. */
    retval = disciplined_fiber_scheduler_main_fiber_get(&mainfib, sched);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_rsock;
    }

    /* create the wrapper psock for the main fiber. */
    retval = psock_create_wrap_async(sock, alloc, mainfib, lsock);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_rsock;
    }

    /* on success above, lsock's ownership transfers to sock. */
    lsock = nullptr;

    /* create the test fiber. */
    retval =
        fiber_create(fib, alloc, sched, FIBER_STACK, ctx, &test_fiber_entry);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_sock;
    }

    ctx->fib = *fib;

    /* create the wrapper psock for the test fiber. */
    retval = psock_create_wrap_async(&ctx->sock, alloc, *fib, rsock);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_fiber;
    }

    /* add the fiber to the scheduler. */
    retval = fiber_scheduler_add(sched, *fib);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_fiber;
    }

    /* success. */
    return STATUS_SUCCESS;

cleanup_fiber:
    release_retval = resource_release(fiber_resource_handle(*fib));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_sock:
    release_retval = resource_release(psock_resource_handle(*sock));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_rsock:
    if (nullptr != rsock)
    {
        release_retval = resource_release(psock_resource_handle(rsock));
        if (STATUS_SUCCESS != release_retval)
        {
            retval = release_retval;
        }
    }

cleanup_lsock:
    if (nullptr != lsock)
    {
        release_retval = resource_release(psock_resource_handle(lsock));
        if (STATUS_SUCCESS != release_retval)
        {
            retval = release_retval;
        }
    }

cleanup_sockets:
    if (left >= 0)
        close(left);
    if (right >= 0)
        close(right);

cleanup_ctx:
    release_retval = resource_release(&ctx->hdr);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

/**
 * Verify that we can create a few fibers and quiesce them.
 */
TEST(create_and_quiesce)
{
    allocator* alloc = nullptr;
    fiber_scheduler* sched = nullptr;
    fiber* fibs[TEST_FIBERS];
    psock* endpoints[TEST_FIBERS];

    /* We should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* We should be able to create a disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* We should be able to create some fibers. */
    for (int i = 0; i < TEST_FIBERS; ++i)
    {
        TEST_ASSERT(
            STATUS_SUCCESS ==
                create_test_fiber(&fibs[i], &endpoints[i], sched, alloc));
    }

    /* We should be able to read and write a value to/from each endpoint. */
    for (int i = 0; i < TEST_FIBERS; ++i)
    {
        /* Writing to the fiber should succeed. */
        TEST_ASSERT(
            STATUS_SUCCESS == psock_write_boxed_int64(endpoints[i], i));

        /* Reading from the fiber should succeed. */
        int64_t val;
        TEST_ASSERT(
            STATUS_SUCCESS == psock_read_boxed_int64(endpoints[i], &val));

        /* Each fiber squares the integer value as the output. */
        TEST_EXPECT(val == i * i);
    }

    /* Notify all threads to quiesce. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            disciplined_fiber_scheduler_send_quiesce_request_to_all(sched));

    /* clean up. */
    for (int i = 0; i < TEST_FIBERS; ++i)
    {
        TEST_ASSERT(
            STATUS_SUCCESS ==
                resource_release(psock_resource_handle(endpoints[i])));
    }
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(allocator_resource_handle(alloc)));
}
