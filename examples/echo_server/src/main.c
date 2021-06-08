/**
 * \file examples/echo_server/src/main.c
 *
 * \brief Main entry point for the echo server example.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <arpa/inet.h>
#include <netinet/in.h>
#include <rcpr/fiber.h>
#include <rcpr/fiber/disciplines/management.h>
#include <rcpr/model_assert.h>
#include <rcpr/psock.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <unistd.h>

#include "../../../src/resource/resource_internal.h"

/* forward decls. */
typedef struct dispatch_context dispatch_context;
static status FN_DECL_MUST_CHECK
dispatch(int desc, allocator* alloc, fiber_scheduler* sched);
static status FN_DECL_MUST_CHECK
dispatch_context_create(
    dispatch_context** ctx, allocator* alloc, fiber_scheduler* sched,
    psock* sock);
static status FN_DECL_MUST_CHECK
dispatch_context_release(resource* r);
static status management_fiber_add(allocator* alloc, fiber_scheduler* sched);
static status fiber_manager_entry(void* vsched);
static status echo_entry(void* context);

/**
 * \brief Context structure passed to the echo server entry function.
 */
struct dispatch_context
{
    resource hdr;

    allocator* alloc;
    fiber_scheduler* sched;
    psock* sock;
};

/**
 * \brief Main entry point for the echo server example.
 */
int main(int argc, char* argv[])
{
    status retval, release_retval;
    struct sockaddr_in name, peeraddr;
    socklen_t namelen, peerlen;
    psock* listen;
    psock* listen_async;
    allocator* alloc;
    fiber_scheduler* sched;

    /* create our allocator. */
    retval = malloc_allocator_create(&alloc);
    if (STATUS_SUCCESS != retval)
    {
        printf("Error creating malloc allocator.\n");
        goto done;
    }

    /* set the listen address to 0.0.0.0 port 9001. */
    name.sin_family = AF_INET;
    name.sin_port = htons(9001);
    name.sin_addr.s_addr = htonl(INADDR_ANY);
    namelen = sizeof(name);

    /* Create a TCP listen socket, bound to port 9001. */
    retval =
        psock_create_from_listen_address(
            &listen, alloc, (struct sockaddr*)&name, namelen);
    if (STATUS_SUCCESS != retval)
    {
        printf("Error binding to 0.0.0.0:9001\n");
        goto done;
    }

    /* create the fiber scheduler. */
    retval = fiber_scheduler_create_with_disciplines(&sched, alloc);
    if (STATUS_SUCCESS != retval)
    {
        printf("Error creating fiber scheduler.\n");
        goto cleanup_listen_socket;
    }

    /* add the management fiber. */
    retval = management_fiber_add(alloc, sched);
    if (STATUS_SUCCESS != retval)
    {
        printf("Error creating management fiber.\n");
        goto cleanup_scheduler;
    }

    /* wrap the listen socket to make it async. */
    retval = psock_create_wrap_async(&listen_async, alloc, sched, listen);
    if (STATUS_SUCCESS != retval)
    {
        printf("Error creating async socket from listen socket.\n");
        goto cleanup_scheduler;
    }

    /* the listen socket should no longer be used directly. */
    listen = NULL;

    /* loop through connections. */
    for (;;)
    {
        /* accept a new connection from the listen socket. */
        int desc;
        peerlen = sizeof(peeraddr);
        retval =
            psock_accept(
                listen_async, &desc, (struct sockaddr*)&peeraddr, &peerlen);
        if (STATUS_SUCCESS != retval)
        {
            printf("Error accepting socket.\n");
            goto cleanup_listen_async;
        }

        /* convert the address to a printable format. */
        char addrstr[INET_ADDRSTRLEN];
        inet_ntop(AF_INET, &peeraddr.sin_addr, addrstr, sizeof(addrstr));

        printf("Accepted connection from %s.\n", addrstr);

        /* sent this socket to our dispatch method. */
        retval = dispatch(desc, alloc, sched);
        if (STATUS_SUCCESS != retval)
        {
            printf("Error dispatching socket.\n");
            close(desc);
        }
    }

cleanup_listen_async:
    release_retval = resource_release(psock_resource_handle(listen_async));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_scheduler:
    release_retval = resource_release(fiber_scheduler_resource_handle(sched));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_listen_socket:
    if (NULL != listen)
    {
        release_retval = resource_release(psock_resource_handle(listen));
        if (STATUS_SUCCESS != release_retval)
        {
            retval = release_retval;
        }
    }

done:
    return retval;
}

/* \brief Dispatch a socket, creating a fiber to handle echo to / from it.
 *
 * \param desc          The socket descriptor to dispatch.
 * \param alloc         The system allocator.
 * \param sched         The fiber scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status FN_DECL_MUST_CHECK
dispatch(int desc, allocator* alloc, fiber_scheduler* sched)
{
    status retval, release_retval;
    psock* sock;
    psock* sock_async;
    dispatch_context* dispatch_ctx;
    fiber* dispatch_fiber;

    /* parameter sanity checks. */
    MODEL_ASSERT(desc >= 0);
    MODEL_ASSERT(prop_allocator_valid(alloc));
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* create a psock for this descriptor. */
    retval = psock_create_from_descriptor(&sock, alloc, desc);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* create an async psock for this descriptor. */
    retval = psock_create_wrap_async(&sock_async, alloc, sched, sock);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_sock;
    }

    /* we will no longer use sock. */
    sock = NULL;

    /* create the fiber context for our dispatch fiber. */
    retval =
        dispatch_context_create(&dispatch_ctx, alloc, sched, sock_async);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_sock_async;
    }

    /* create the fiber to run this dispatch. */
    retval =
        fiber_create(
            &dispatch_fiber, alloc, sched, 16384, dispatch_ctx,
            &echo_entry);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_dispatch_context;
    }

    /* add this fiber to the scheduler. */
    retval = fiber_scheduler_add(sched, dispatch_fiber);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_dispatch_fiber;
    }

    /* success. At this point, the fiber owns all, so we can exit cleanly. */
    retval = STATUS_SUCCESS;
    goto done;

cleanup_dispatch_fiber:
    release_retval = resource_release(fiber_resource_handle(dispatch_fiber));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_dispatch_context:
    release_retval = resource_release(&dispatch_ctx->hdr);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_sock_async:
    release_retval = resource_release(psock_resource_handle(sock_async));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

cleanup_sock:
    if (NULL != sock)
    {
        release_retval = resource_release(psock_resource_handle(sock));
        if (STATUS_SUCCESS != release_retval)
        {
            retval = release_retval;
        }
    }

done:
    return retval;
}

/**
 * \brief Create a dispatch context to pass to the echo_entry function.
 *
 * \param ctx       Pointer to receive the pointer of the created dispatch
 *                  context.
 * \param alloc     System allocator.
 * \param sched     Fiber scheduler.
 * \param sock      The client socket.
 *
 * \returns an status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status FN_DECL_MUST_CHECK
dispatch_context_create(
    dispatch_context** ctx, allocator* alloc, fiber_scheduler* sched,
    psock* sock)
{
    status retval;
    dispatch_context* tmp;

    /* parameter sanity checks. */
    MODEL_ASSERT(NULL != ctx);
    MODEL_ASSERT(prop_allocator_valid(alloc));
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));
    MODEL_ASSERT(prop_psock_valid(sock));

    /* allocate memory for the dispatch context. */
    retval = allocator_allocate(alloc, (void**)&tmp, sizeof(dispatch_context));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear out structure. */
    memset(tmp, 0, sizeof(dispatch_context));

    /* initialize resource. */
    resource_init(&tmp->hdr, &dispatch_context_release);

    /* set values. */
    tmp->alloc = alloc;
    tmp->sched = sched;
    tmp->sock = sock;

    /* success. */
    *ctx = tmp;
    retval = STATUS_SUCCESS;
    goto done;

done:
    return retval;
}

/**
 * \brief Release a dispatch context resource.
 *
 * \param r         The dispatch context resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status FN_DECL_MUST_CHECK
dispatch_context_release(resource* r)
{
    dispatch_context* ctx = (dispatch_context*)r;

    /* cache allocator. */
    allocator* alloc = ctx->alloc;

    /* clean up psock. */
    status psock_retval = resource_release(psock_resource_handle(ctx->sock));

    /* clean up memory. */
    status release_retval = allocator_reclaim(alloc, ctx);

    /* return the appropriate status code. */
    if (STATUS_SUCCESS != psock_retval)
    {
        return psock_retval;
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

/**
 * \brief Add the management fiber to clean up after fibers.
 *
 * \param alloc         The system allocator to use to create this fiber.
 * \param sched         The fiber scheduler to which this fiber should be added.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status management_fiber_add(allocator* alloc, fiber_scheduler* sched)
{
    status retval, release_retval;
    fiber* manager;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_allocator_valid(alloc));
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* create the management fiber. */
    retval =
        fiber_create(
            &manager, alloc, sched, 16384, sched, &fiber_manager_entry);
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
 * \brief Entry point for the management fiber.
 *
 * This fiber manages cleanup for fibers as they stop.
 *
 * \param vsched        The type erased scheduler.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status fiber_manager_entry(void* vsched)
{
    status retval;
    const rcpr_uuid* resume_id;
    int resume_event;
    void* resume_param;
    fiber* stopped_fiber;

    fiber_scheduler* sched = (fiber_scheduler*)vsched;

    /* parameter sanity checks. */
    MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    for (;;)
    {
        /* receive a management event. */
        retval =
            disciplined_fiber_scheduler_receive_management_event(
                sched, &resume_id, &resume_event, &resume_param);

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
                    printf("Fiber terminated.\n");
                    stopped_fiber = (fiber*)resume_param;

                    /* instruct the fiber scheduler to remove the fiber
                     * reference. */
                    retval =
                        disciplined_fiber_scheduler_remove_fiber(
                            sched, stopped_fiber);
                    if (STATUS_SUCCESS != retval)
                    {
                        printf("Error: can't remove fiber from scheduler.\n");
                    }

                    /* release the fiber. */
                    retval =
                        resource_release(fiber_resource_handle(stopped_fiber));
                    if (STATUS_SUCCESS != retval)
                    {
                        printf("Error: couldn't release fiber.\n");
                    }
                    break;

                /* we don't care about any other management event. */
                default:
                    continue;
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
 * \brief Entry point for the echo fiber.
 *
 * This fiber manages a single echo server connection, simulating synchronous
 * socket I/O.
 *
 * \param context       The dispatch context.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status echo_entry(void* context)
{
    status retval, release_retval;
    dispatch_context* ctx = (dispatch_context*)context;
    uint8_t data;

    for (;;)
    {
        /* read a byte from the peer. */
        retval = psock_read_raw_uint8(ctx->sock, &data);
        if (STATUS_SUCCESS != retval)
        {
            goto cleanup_context;
        }

        /* write this byte back to the peer. */
        retval = psock_write_raw_uint8(ctx->sock, data);
        if (STATUS_SUCCESS != retval)
        {
            goto cleanup_context;
        }
    }

cleanup_context:
    release_retval = resource_release(&ctx->hdr);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

    return retval;
}
