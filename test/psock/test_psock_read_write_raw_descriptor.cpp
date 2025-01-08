/**
 * \file test/test_psock_read_write_raw_descriptor.cpp
 *
 * \brief Unit tests for psock_read_raw_descriptor and
 * psock_write_raw_descriptor.
 */

#include <errno.h>
#include <fcntl.h>
#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <rcpr/psock.h>
#include <rcpr/resource.h>
#include <rcpr/resource/protected.h>
#include <rcpr/socket_utilities.h>
#include <rcpr/uuid.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <unistd.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_psock;
RCPR_IMPORT_resource;
RCPR_IMPORT_socket_utilities;
RCPR_IMPORT_uuid;

TEST_SUITE(psock_read_write_raw_descriptor);



#ifdef RCPR_FIBER_FOUND
#define FIBER_STACK_SIZE (1024 * 1024)

/* forward decls for fibers. */
typedef struct accepter_context accepter_context;
static status accepter_entry(void* context);
static status accepter_unexpected_handler(
    void* context, fiber* fib, const rcpr_uuid* resume_disc_id,
    int resume_event, void* resume_param,
    const rcpr_uuid* expected_resume_disc_id, int expected_resume_event);
static status fiber_manager_entry(void* context);
static status add_management_fiber(allocator* alloc, fiber_scheduler* sched);
static status accepter_create(
    accepter_context** context, fiber** accepter, allocator* alloc,
    fiber_scheduler* sched, int desc, int write_desc);
static status add_accepter_fiber(
    allocator* alloc, fiber_scheduler* sched, accepter_context** context,
    int desc, int write_desc);
static status accepter_context_release(resource* r);
#endif /* RCPR_FIBER_FOUND */

/**
 * Verify that attempting to write a raw descriptor to a stream socket fails.
 */
TEST(write_raw_descriptor_stream)
{
    allocator* alloc = nullptr;
    psock* sl = nullptr;
    psock* sr = nullptr;
    int lhs;
    int rhs;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a socket pair. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(AF_UNIX, SOCK_STREAM, 0, &lhs, &rhs));

    /* we should be able to create a psock from the lhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &sl, alloc, lhs));

    /* we should be able to create a psock from the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &sr, alloc, rhs));

    /* writing a descriptor to the lhs socket should fail. */
    TEST_ASSERT(
        ERROR_PSOCK_UNSUPPORTED_TYPE ==
            psock_write_raw_descriptor(sl, rhs));

    /* release the lhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(sl)));

    /* release the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(psock_resource_handle(sr)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that attempting to read a raw descriptor from a stream socket fails.
 */
TEST(read_raw_descriptor_stream)
{
    allocator* alloc = nullptr;
    psock* sl = nullptr;
    psock* sr = nullptr;
    int lhs;
    int rhs;
    int desc;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a socket pair. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(AF_UNIX, SOCK_STREAM, 0, &lhs, &rhs));

    /* we should be able to create a psock from the lhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &sl, alloc, lhs));

    /* we should be able to create a psock from the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &sr, alloc, rhs));

    /* reading a descriptor from the rhs socket should fail. */
    TEST_ASSERT(
        ERROR_PSOCK_UNSUPPORTED_TYPE ==
            psock_read_raw_descriptor(
                sr, &desc));

    /* release the lhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_resource_handle(sl)));

    /* release the rhs socket. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_resource_handle(sr)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/* TODO - this test currently does not work on MacOS. */
#ifndef __RCPR_MACOS__

/* forward decls. */
static size_t count_open_fds();

/**
 * Verify that we can pass a descriptor through a datagram socket.
 */
TEST(read_write_raw_descriptor_datagram)
{
    allocator* alloc = nullptr;
    psock* sl = nullptr;
    psock* sr = nullptr;
    int lhs, lhs_dg;
    int rhs, rhs_dg;
    int desc;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* get the open file count. */
    size_t open_files1 = count_open_fds();

    /* we should be able to create socket pairs. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(
                AF_UNIX, SOCK_DGRAM, 0, &lhs_dg, &rhs_dg));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(
                AF_UNIX, SOCK_STREAM, 0, &lhs, &rhs));

    /* the number of open files should have increased by 4. */
    size_t open_files2 = count_open_fds();
    TEST_ASSERT(open_files1 + 4 == open_files2);

    /* create a psock from the lhs_dg socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &sl, alloc, lhs_dg));

    /* create a psock from the rhs_dg socket. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(
                &sr, alloc, rhs_dg));

    /* write the rhs descriptor to the sl socket. */
    TEST_ASSERT(
        STATUS_SUCCESS == psock_write_raw_descriptor(sl, rhs));

    /* the SCM_RIGHTS packet does not increase the number of open files. */
    size_t open_files3 = count_open_fds();
    TEST_ASSERT(open_files2 == open_files3);

    /* read the rhs descriptor from the sr socket. */
    TEST_ASSERT(
        STATUS_SUCCESS == psock_read_raw_descriptor(sr, &desc));

    /* reading the SCM_RIGHTS packet increases the number of open files by 1. */
    size_t open_files4 = count_open_fds();
    TEST_ASSERT(open_files3 + 1 == open_files4);

    /* verify that desc is a valid socket. */
    TEST_EXPECT(desc >= 0);

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_resource_handle(sl)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_resource_handle(sr)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
    close(lhs);
    close(rhs);
    close(desc);
}

/**
 * \brief Count the number of open file descriptors.
 */
static size_t count_open_fds()
{
    status retval;
    struct rlimit rl;
    size_t open_files = 0;

    retval = getrlimit(RLIMIT_NOFILE, &rl);
    if (retval < 0)
    {
        perror("getrlimit");
        exit(1);
    }

    for (size_t i = 0; i < (size_t)rl.rlim_max; ++i)
    {
        retval = fcntl(i, F_GETFL);
        if (retval < 0)
            continue;

        ++open_files;
    }

    return open_files;
}

#endif /* __RCPR_MACOS__ */

struct accepter_context
{
    resource hdr;
    allocator* alloc;
    psock* sock;
    psock* write_sock;
    int read_descriptors;
    bool quiesce;
};

#ifdef RCPR_FIBER_FOUND

/**
 * Verify that we can read and write raw descriptors using fibers.
 */
TEST(fiber_read_write_raw_descriptor)
{
    allocator* alloc = nullptr;
    psock* desc_psock = nullptr;
    psock* desc_out = nullptr;
    psock* io_psock = nullptr;
    psock* io_in = nullptr;
    int lhs1, rhs1;
    int lhs2, rhs2;
    int lhs3, rhs3;
    fiber_scheduler* sched;
    fiber* main_fib;
    accepter_context* ctx = nullptr;
    uint32_t val;

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(
        STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create socket pairs. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(
                AF_UNIX, SOCK_DGRAM, 0, &lhs1, &rhs1));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(
                AF_UNIX, SOCK_STREAM, 0, &lhs2, &rhs2));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            socket_utility_socketpair(
                AF_UNIX, SOCK_STREAM, 0, &lhs3, &rhs3));

    /* create the disciplined fiber scheduler. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            fiber_scheduler_create_with_disciplines(&sched, alloc));

    /* add the management fiber. */
    TEST_ASSERT(STATUS_SUCCESS == add_management_fiber(alloc, sched));

    /* add the accepter fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS == add_accepter_fiber(alloc, sched, &ctx, rhs1, rhs3));

    /* create a psock from the lhs descriptor. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(&desc_psock, alloc, lhs1));

    /* create a psock from the lhs3 descriptor. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_from_descriptor(&io_psock, alloc, lhs3));

    /* get the main fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            disciplined_fiber_scheduler_main_fiber_get(&main_fib, sched));

    /* wrap the psock to use with the main fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_wrap_async(&desc_out, alloc, main_fib, desc_psock));

    /* wrap the psock to use with the main fiber. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            psock_create_wrap_async(&io_in, alloc, main_fib, io_psock));

    /* run all fibers. */
    TEST_ASSERT(
        STATUS_SUCCESS == fiber_scheduler_run(sched));

    /* verify that the descriptor count is zero. */
    TEST_EXPECT(ctx->read_descriptors == 0);

    /* write a descriptor. */
    TEST_ASSERT(
        STATUS_SUCCESS == psock_write_raw_descriptor(desc_out, lhs2));

    /* wait on accept. */
    TEST_ASSERT(
        STATUS_SUCCESS == psock_read_raw_uint32(io_in, &val));

    /* verify that the descriptor count is one. */
    TEST_EXPECT(ctx->read_descriptors == 1);

    /* write a descriptor. */
    TEST_ASSERT(
        STATUS_SUCCESS == psock_write_raw_descriptor(desc_out, rhs2));

    /* wait on accept. */
    TEST_ASSERT(
        STATUS_SUCCESS == psock_read_raw_uint32(io_in, &val));

    /* verify that the descriptor count is two. */
    TEST_EXPECT(ctx->read_descriptors == 2);

    /* send a quiesce request to all fibers. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            disciplined_fiber_scheduler_send_quiesce_request_to_all(sched));

    /* send a terminate request to all fibers. */
    TEST_ASSERT(
        STATUS_SUCCESS ==
            disciplined_fiber_scheduler_send_terminate_request_to_all(sched));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_resource_handle(desc_out)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(psock_resource_handle(io_in)));
    TEST_ASSERT(
        STATUS_SUCCESS ==
            resource_release(fiber_scheduler_resource_handle(sched)));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * \brief Entry point for the accepter fiber.
 *
 * \param context       Opaque pointer to accepter context.
 *
 * \returns a status code indicating success or failure.
 */
static status accepter_entry(void* context)
{
    status retval, release_retval;
    int desc;
    accepter_context* ctx = (accepter_context*)context;
    uint32_t dummy = 0U;

    /* forever loop. */
    for (;;)
    {
        /* read a descriptor from our psock. */
        retval = psock_read_raw_descriptor(ctx->sock, &desc);
        if (STATUS_SUCCESS != retval)
        {
            goto cleanup_accepter_context;
        }

        /* increment the read descriptor count. */
        ++ctx->read_descriptors;

        /* write a dummy value to the socket. */
        retval = psock_write_raw_uint32(ctx->write_sock, dummy);
        if (STATUS_SUCCESS != retval)
        {
            goto cleanup_accepter_context;
        }

        /* close the descriptor. */
        close(desc);
    }

cleanup_accepter_context:
    release_retval = resource_release(&ctx->hdr);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

    return retval;
}

/**
 * \brief Unexpected handler for the accepter fiber.
 *
 * \param context                   Opaque pointer to the accepter context.
 * \param fib                       The fiber that received this unexpected
 *                                  event.
 * \param resume_disc_id            The unexpected resume discipline id.
 * \param resume_event              The unexpected resume event.
 * \param resume_param              The unexpected resume parameter.
 * \param expected_resume_disc_id   The expected discipline id.
 * \param expected_resume_event     The expected resume event.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS if the fiber should retry the yield.
 *      - a non-zero error code if the fiber should exit.
 */
static status accepter_unexpected_handler(
    void* context, fiber* fib, const rcpr_uuid* resume_disc_id,
    int resume_event, void* resume_param,
    const rcpr_uuid* expected_resume_disc_id, int expected_resume_event)
{
    (void)fib;
    (void)resume_param;
    (void)expected_resume_disc_id;
    (void)expected_resume_event;

    accepter_context* ctx = (accepter_context*)context;

    if (
        !memcmp(
            resume_disc_id, &FIBER_SCHEDULER_MANAGEMENT_DISCIPLINE,
            sizeof(rcpr_uuid)))
    {
        /* retry on quiesce. */
        if (
            FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_QUIESCE_REQUEST
                == resume_event)
        {
            ctx->quiesce = true;
            return STATUS_SUCCESS;
        }
    }

    /* for any other resume event, terminate the accepter fiber. */
    return ERROR_FIBER_INVALID_STATE;
}

/**
 * \brief Entry point for the fiber manager.
 *
 * \param context       Opaque pointer to fiber scheduler.
 *
 * \returns a status code indicating success or failure.
 */
static status fiber_manager_entry(void* context)
{
    status retval;
    const rcpr_uuid* resume_id;
    int resume_event;
    void* resume_param;
    fiber* stopped_fiber;

    fiber_scheduler* sched = (fiber_scheduler*)context;

    for (;;)
    {
        /* receive management event. */
        retval =
            disciplined_fiber_scheduler_receive_management_event(
                sched, &resume_id, &resume_event, &resume_param);
        if (STATUS_SUCCESS != retval)
        {
            fprintf(stderr, "Error reading management event.\n");
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
                            sched, stopped_fiber);
                    if (STATUS_SUCCESS != retval)
                    {
                        fprintf(
                            stderr,
                            "Error: can't remove fiber from scheduler.\n");
                    }
                    else
                    {
                        /* release the fiber. */
                        retval =
                            resource_release(
                                fiber_resource_handle(stopped_fiber));
                        if (STATUS_SUCCESS != retval)
                        {
                            fprintf(stderr, "Error: couldn't release fiber.\n");
                        }
                    }
                    break;

                /* a quiesce request. */
                case FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_QUIESCE_REQUEST:
                    break;

                /* a termination request. */
                case FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_TERMINATION_REQUEST:
                    return STATUS_SUCCESS;
            }
        }
        /* ignore any other event. */
        else
        {
            continue;
        }
    }
}

/**
 * \brief Add the management fiber to the fiber scheduler.
 *
 * \param alloc         The system allocator to use to create this fiber.
 * \param sched         The fiber scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status add_management_fiber(allocator* alloc, fiber_scheduler* sched)
{
    status retval, release_retval;
    fiber* manager;

    /* create the management fiber. */
    retval =
        fiber_create(
            &manager, alloc, sched, FIBER_STACK_SIZE, sched,
            &fiber_manager_entry);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* add the management fiber to the scheduler. */
    retval = fiber_scheduler_add(sched, manager);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_manager;
    }

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_manager:
    release_retval = resource_release(fiber_resource_handle(manager));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

/**
 * \brief Add the accepter fiber to the fiber scheduler.
 *
 * \param alloc         The system allocator to use to create this fiber.
 * \param sched         The fiber scheduler.
 * \param context       Pointer to receive the accepter fiber context.
 * \param desc          The descriptor that the accepter will use to accept
 *                      sockets.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status add_accepter_fiber(
    allocator* alloc, fiber_scheduler* sched, accepter_context** context,
    int desc, int write_desc)
{
    status retval, release_retval;
    fiber* accepter;

    /* create the accepter fiber and context. */
    retval =
        accepter_create(context, &accepter, alloc, sched, desc, write_desc);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* set the unexpected handler for the accepter fiber. */
    retval =
        fiber_unexpected_event_callback_add(
            accepter, &accepter_unexpected_handler, *context);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_accepter;
    }

    /* add the accepter fiber to the scheduler. */
    retval = fiber_scheduler_add(sched, accepter);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_accepter;
    }

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_accepter:
    release_retval = resource_release(fiber_resource_handle(accepter));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

/**
 * \brief Create the accepter fiber and context.
 *
 * \param context       Pointer to the context pointer to create.
 * \param accepter      The accepter fiber.
 * \param alloc         The system allocator to use to create this context.
 * \param sched         The fiber scheduler to use.
 * \param desc          The descriptor to use to accept sockets.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status accepter_create(
    accepter_context** context, fiber** accepter, allocator* alloc,
    fiber_scheduler* sched, int desc, int write_desc)
{
    status retval, release_retval;
    accepter_context* tmp = NULL;
    psock* tmp_sock = NULL;

    /* allocate memory for the accepter context structure. */
    retval =
        allocator_allocate(alloc, (void**)&tmp, sizeof(accepter_context));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear the accepter context. */
    memset(tmp, 0, sizeof(accepter_context));

    /* set the resource release method. */
    resource_init(&tmp->hdr, &accepter_context_release);

    /* set the remaining fields, except the psock instance. */
    tmp->alloc = alloc;
    tmp->read_descriptors = 0;

    /* create the accepter fiber. */
    retval =
        fiber_create(
            accepter, alloc, sched, FIBER_STACK_SIZE, tmp, &accepter_entry);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_accepter_context;
    }

    /* create the psock instance. */
    retval =
        psock_create_from_descriptor(&tmp_sock, alloc, desc);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_accepter;
    }

    /* wrap this socket so we can use it from our fiber. */
    retval =
        psock_create_wrap_async(&tmp->sock, alloc, *accepter, tmp_sock);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_tmp_sock;
    }

    /* create the psock instance. */
    retval =
        psock_create_from_descriptor(&tmp_sock, alloc, write_desc);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_accepter;
    }

    /* wrap this socket so we can use it from our fiber. */
    retval =
        psock_create_wrap_async(&tmp->write_sock, alloc, *accepter, tmp_sock);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_tmp_sock;
    }

    /* success. */
    *context = tmp;
    retval = STATUS_SUCCESS;
    goto done;

cleanup_tmp_sock:
    release_retval = resource_release(psock_resource_handle(tmp_sock));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_accepter:
    release_retval = resource_release(fiber_resource_handle(*accepter));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_accepter_context:
    release_retval = resource_release(&tmp->hdr);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}

/**
 * \brief Release the accepter context.
 *
 * \param r         The context to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status accepter_context_release(resource* r)
{
    status write_psock_release_retval = STATUS_SUCCESS;
    status psock_release_retval = STATUS_SUCCESS;
    status release_retval = STATUS_SUCCESS;

    accepter_context* ctx = (accepter_context*)r;

    /* cache allocator. */
    allocator* alloc = ctx->alloc;

    /* clean up the psock instance. */
    if (NULL != ctx->sock)
    {
        psock_release_retval =
            resource_release(psock_resource_handle(ctx->sock));
    }

    /* clean up the write psock instance. */
    if (NULL != ctx->write_sock)
    {
        write_psock_release_retval =
            resource_release(psock_resource_handle(ctx->write_sock));
    }

    /* clean up memory. */
    release_retval = allocator_reclaim(alloc, ctx);

    /* return the appropriate status code. */
    if (STATUS_SUCCESS != psock_release_retval)
    {
        return psock_release_retval;
    }
    else if (STATUS_SUCCESS != write_psock_release_retval)
    {
        return write_psock_release_retval;
    }
    else
    {
        return release_retval;
    }
}

#endif /* RCPR_FIBER_FOUND */

