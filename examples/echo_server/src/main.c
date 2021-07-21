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
#include <rcpr/resource/protected.h>
#include <rcpr/socket_utilities.h>
#include <rcpr/thread.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <unistd.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_psock;
RCPR_IMPORT_resource;
RCPR_IMPORT_socket_utilities;
RCPR_IMPORT_thread;
RCPR_IMPORT_uuid;

#define FIBER_STACK_SIZE (1024 * 1024)

/**
 * \brief Context structure passed to the echo server entry function.
 */
typedef struct dispatch_context dispatch_context;
struct dispatch_context
{
    resource hdr;

    allocator* alloc;
    fiber_scheduler* sched;
    psock* sock;
};

/**
 * \brief Context structure passed to the listen fiber.
 */
typedef struct listen_context listen_context;
struct listen_context
{
    resource hdr;

    allocator* alloc;
    fiber* fib;
    fiber_scheduler* sched;
    uint16_t port;
};

/**
 * \brief Enumeration of signal states.
 */
enum signal_state
{
    SIGNAL_STATE_QUIESCE,
    SIGNAL_STATE_TERMINATE
};

/**
 * \brief The signal thread context.
 */
typedef struct signal_thread_context signal_thread_context;
struct signal_thread_context
{
    resource hdr;

    allocator* alloc;
    psock* socket;
};

/* forward decls. */
static status FN_DECL_MUST_CHECK
dispatch(int desc, allocator* alloc, fiber_scheduler* sched);
static status FN_DECL_MUST_CHECK
dispatch_context_create(
    dispatch_context** ctx, allocator* alloc, fiber_scheduler* sched,
    psock* sock);
static status dispatch_context_release(resource* r);
static status listen_context_release(resource* r);
static status signal_thread_context_release(resource* r);
static status management_fiber_add(allocator* alloc, fiber_scheduler* sched);
static status listen_fiber_add(
    allocator* alloc, fiber_scheduler* sched, uint16_t port);
static status fiber_manager_entry(void* vsched);
static status listen_entry(void* context);
static status echo_entry(void* context);
static status signal_thread_create(
    thread** th, int* signal_desc, allocator* alloc);
static status signal_thread_entry(void* context);

/**
 * \brief Main entry point for the echo server example.
 */
int main(int argc, char* argv[])
{
    status retval, release_retval;
    allocator* alloc;
    fiber* main_fiber;
    fiber_scheduler* sched;
    fiber_scheduler_discipline* msgdisc;
    thread* signal_thread;
    int signal_desc;
    psock* signal_desc_sock;
    psock* signal_sock;
    bool should_exit = false;

    /* create our allocator. */
    retval = malloc_allocator_create(&alloc);
    if (STATUS_SUCCESS != retval)
    {
        printf("Error creating malloc allocator.\n");
        goto done;
    }

    /* create the fiber scheduler. */
    retval = fiber_scheduler_create_with_disciplines(&sched, alloc);
    if (STATUS_SUCCESS != retval)
    {
        printf("Error creating fiber scheduler.\n");
        goto cleanup_allocator;
    }

    /* add the management fiber. */
    retval = management_fiber_add(alloc, sched);
    if (STATUS_SUCCESS != retval)
    {
        printf("Error creating management fiber.\n");
        goto cleanup_scheduler;
    }

    /* add the listen fiber. */
    retval = listen_fiber_add(alloc, sched, 9001);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_scheduler;
    }

    /* create the signal thread. */
    retval =
        signal_thread_create(
            &signal_thread, &signal_desc, alloc);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_scheduler;
    }

    /* create the root signal psock. */
    retval =
        psock_create_from_descriptor(&signal_desc_sock, alloc, signal_desc);
    if (STATUS_SUCCESS != retval)
    {
        goto terminate_process;
    }

    /* get the main fiber. */
    retval = disciplined_fiber_scheduler_main_fiber_get(&main_fiber, sched);
    if (STATUS_SUCCESS != retval)
    {
        goto signal_desc_psock_release;
    }

    printf("Main fiber: 0x%lx\n", listen);

    /* wrap this as an async socket. */
    retval =
        psock_create_wrap_async(
            &signal_sock, alloc, main_fiber, signal_desc_sock);
    if (STATUS_SUCCESS != retval)
    {
        goto signal_desc_psock_release;
    }

    /* the descriptor psock is now owned by the async psock. */
    signal_desc_sock = NULL;

    /* termination loop. */
    do
    {
        /* read a signal state from the signal thread. */
        uint64_t payload_state;
        retval = psock_read_boxed_int64(signal_sock, &payload_state);
        if (STATUS_SUCCESS != retval)
        {
            goto terminate_process;
        }

        /* signal dispatch. */
        switch (payload_state)
        {
            /* quiesce all fibers. */
            case SIGNAL_STATE_QUIESCE:
                printf("Quiescing fibers.\n");
                retval =
                    disciplined_fiber_scheduler_send_quiesce_request_to_all(
                        sched);
                if (STATUS_SUCCESS != retval)
                {
                    goto terminate_process;
                }
                break;

            /* terminate all fibers. */
            case SIGNAL_STATE_TERMINATE:
                printf("Terminating fibers.\n");
                should_exit = true;
                retval =
                    disciplined_fiber_scheduler_send_terminate_request_to_all(
                        sched);
                if (STATUS_SUCCESS != retval)
                {
                    goto terminate_process;
                }
        }

    } while (!should_exit);

    /* success. */
    retval = STATUS_SUCCESS;
    goto join_signal_thread;

signal_desc_psock_release:
    if (NULL != signal_desc_sock)
    {
        release_retval =
            resource_release(psock_resource_handle(signal_desc_sock));
        if (STATUS_SUCCESS != release_retval)
        {
            retval = release_retval;
        }
    }

terminate_process:
    kill(getpid(), SIGTERM);

join_signal_thread:
    /* release (join) the signal thread. */
    release_retval = resource_release(thread_resource_handle(signal_thread));
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

cleanup_allocator:
    release_retval = resource_release(allocator_resource_handle(alloc));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
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
    RCPR_MODEL_ASSERT(desc >= 0);
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* create a psock for this descriptor. */
    retval = psock_create_from_descriptor(&sock, alloc, desc);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* create the fiber context for our dispatch fiber. */
    retval =
        dispatch_context_create(&dispatch_ctx, alloc, sched, NULL);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_sock;
    }

    /* create the fiber to run this dispatch. */
    retval =
        fiber_create(
            &dispatch_fiber, alloc, sched, FIBER_STACK_SIZE, dispatch_ctx,
            &echo_entry);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_dispatch_context;
    }

    printf("Fiber %p created.\n", (void*)dispatch_fiber);

    /* create an async psock for this descriptor. */
    retval = psock_create_wrap_async(&sock_async, alloc, dispatch_fiber, sock);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_dispatch_fiber;
    }

    /* we will no longer use sock. */
    sock = NULL;

    /* move the async socket to the dispatch context. */
    dispatch_ctx->sock = sock_async;

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

    /* if we have made it this far, sock_async is owned by dispatch_context. */
    goto cleanup_dispatch_context;

cleanup_sock_async:
    release_retval = resource_release(psock_resource_handle(sock_async));
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
    RCPR_MODEL_ASSERT(NULL != ctx);
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

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
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* create the management fiber. */
    retval =
        fiber_create(
            &manager, alloc, sched, FIBER_STACK_SIZE, sched,
            &fiber_manager_entry);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    printf("Management fiber: 0x%lx\n", manager);

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
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    for (;;)
    {
        /* receive a management event. */
        retval =
            disciplined_fiber_scheduler_receive_management_event(
                sched, &resume_id, &resume_event, &resume_param);
        if (STATUS_SUCCESS != retval)
        {
            printf("Error reading management event.\n");
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
                    printf("Fiber 0x%lx terminated.\n", stopped_fiber);

                    /* instruct the fiber scheduler to remove the fiber
                     * reference. */
                    retval =
                        disciplined_fiber_scheduler_remove_fiber(
                            sched, stopped_fiber);
                    if (STATUS_SUCCESS != retval)
                    {
                        printf("Error: can't remove fiber from scheduler.\n");
                    }
                    else
                    {
                        /* release the fiber. */
                        retval =
                            resource_release(
                                fiber_resource_handle(stopped_fiber));
                        if (STATUS_SUCCESS != retval)
                        {
                            printf("Error: couldn't release fiber.\n");
                        }
                    }
                    break;

                /* a quiesce request. */
                case FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_QUIESCE_REQUEST:
                    printf("Management fiber received quiesce request.\n");
                    break;

                /* a termination request. */
                case FIBER_SCHEDULER_MANAGEMENT_RESUME_EVENT_TERMINATION_REQUEST:
                    printf("Management fiber received termination request.\n");
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
}

/**
 * \brief Add the listening fiber to listen for connections.
 *
 * \param alloc         The system allocator to use to create this fiber.
 * \param sched         The fiber scheduler to which this fiber should be added.
 * \param port          The port to which this listening socket should be bound.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status listen_fiber_add(
    allocator* alloc, fiber_scheduler* sched, uint16_t port)
{
    status retval, release_retval;
    fiber* listen;
    listen_context* ctx;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_valid(sched));

    /* allocate memory for the listen context. */
    retval = allocator_allocate(alloc, (void**)&ctx, sizeof(listen_context));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* clear the listen context. */
    memset(ctx, 0, sizeof(listen_context));

    /* set the resource release method. */
    resource_init(&ctx->hdr, &listen_context_release);

    /* set remaining fields, except the fiber. */
    ctx->alloc = alloc;
    ctx->sched = sched;
    ctx->port = port;

    /* create the listen fiber. */
    retval =
        fiber_create(
            &listen, alloc, sched, FIBER_STACK_SIZE, ctx, &listen_entry);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_listen_context;
    }

    printf("Listen fiber: 0x%lx\n", listen);

    /* set the listen fiber. */
    ctx->fib = listen;

    /* add the listen fiber to the scheduler. */
    retval = fiber_scheduler_add(sched, listen);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_listen_fiber;
    }

    /* the listen fiber is now owned by the scheduler. */
    listen = NULL;
    /* the context is now owned by the listen fiber. */
    ctx = NULL;

    /* success. */
    retval = STATUS_SUCCESS;

cleanup_listen_fiber:
    if (NULL != listen)
    {
        release_retval = resource_release(fiber_resource_handle(listen));
        if (STATUS_SUCCESS != release_retval)
        {
            retval = release_retval;
        }
    }

cleanup_listen_context:
    if (NULL != ctx)
    {
        release_retval = resource_release(&ctx->hdr);
        if (STATUS_SUCCESS != release_retval)
        {
            retval = release_retval;
        }
    }

done:
    return retval;
}

/**
 * \brief Release a listen context resource.
 *
 * \param r         The listen context resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status FN_DECL_MUST_CHECK
listen_context_release(resource* r)
{
    listen_context* ctx = (listen_context*)r;

    /* cache allocator. */
    allocator* alloc = ctx->alloc;

    /* clean up memory. */
    status release_retval = allocator_reclaim(alloc, ctx);

    /* return the appropriate status code. */
    if (STATUS_SUCCESS != release_retval)
    {
        return release_retval;
    }
    else
    {
        return STATUS_SUCCESS;
    }
}

/**
 * \brief Create the signal thread.
 *
 * \param th            The thread to create.
 * \param signal_desc   The descriptor to which the thread will write signal
 *                      state messages.
 * \param alloc         The allocator to use to create this signal thread.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status signal_thread_create(
    thread** th, int* signal_desc, allocator* alloc)
{
    sigset_t sigset;
    status retval, release_retval;
    signal_thread_context* ctx;
    int left, right;

    /* empty the signal set. */
    sigfillset(&sigset);

    /* set the signal mask for this thread. */
    pthread_sigmask(SIG_BLOCK, &sigset, NULL);

    /* create the file descriptors for thread/fiber comms. */
    retval = socket_utility_socketpair(AF_UNIX, SOCK_STREAM, 0, &left, &right);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* allocate memory for the thread context. */
    retval =
        allocator_allocate(alloc, (void**)&ctx, sizeof(signal_thread_context));
    if (STATUS_SUCCESS != retval)
    {
        goto close_fds;
    }

    /* clear the struct. */
    memset(ctx, 0, sizeof(signal_thread_context));

    /* set the resource handler. */
    resource_init(&ctx->hdr, &signal_thread_context_release);

    /* set the init values. */
    ctx->alloc = alloc;

    /* create the psock. */
    retval = psock_create_from_descriptor(&ctx->socket, alloc, left);
    if (STATUS_SUCCESS != retval)
    {
        goto release_context;
    }

    /* left is now owned by the psock, owned by the thread context. */
    left = -1;

    /* create the thread. */
    retval =
        thread_create(th, alloc, FIBER_STACK_SIZE, ctx, &signal_thread_entry);
    if (STATUS_SUCCESS != retval)
    {
        goto release_context;
    }

    /* on success, the right socket is owned by the caller. */
    *signal_desc = right;
    right = -1;

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

release_context:
    release_retval = resource_release(&ctx->hdr);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

close_fds:
    if (left >= 0) close(left);
    if (right >= 0) close(right);

done:
    return retval;
}

/**
 * \brief Release a signal thread context resource.
 *
 * \param r         The signal thread context resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status FN_DECL_MUST_CHECK
signal_thread_context_release(resource* r)
{
    signal_thread_context* ctx = (signal_thread_context*)r;

    /* cache allocator. */
    allocator* alloc = ctx->alloc;

    /* clean up psock. */
    status psock_release_retval = STATUS_SUCCESS;
    if (NULL != ctx->socket)
    {
        psock_release_retval =
            resource_release(psock_resource_handle(ctx->socket));
    }

    /* clean up memory. */
    status release_retval = allocator_reclaim(alloc, ctx);

    /* return the appropriate status code. */
    if (STATUS_SUCCESS != psock_release_retval)
    {
        return psock_release_retval;
    }
    if (STATUS_SUCCESS != release_retval)
    {
        return release_retval;
    }
    else
    {
        return STATUS_SUCCESS;
    }
}

/**
 * \brief Entry point for the signal thread.
 *
 * \param context           The signal_thread_context for this thread.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status signal_thread_entry(void* context)
{
    status retval;
    sigset_t sigset;
    int sig;

    /* get the signal thread context. */
    signal_thread_context* ctx = (signal_thread_context*)context;

    /* Wait and block on all signals. */
    sigfillset(&sigset);

    /* wait on a signal. */
    sigwait(&sigset, &sig);

    /* send the quiesce message. */
    retval = psock_write_boxed_int64(ctx->socket, SIGNAL_STATE_QUIESCE);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* wait five seconds. */
    sleep(5);

    /* send the terminate message. */
    retval = psock_write_boxed_int64(ctx->socket, SIGNAL_STATE_TERMINATE);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* success. */
    retval = STATUS_SUCCESS;
    goto done;

done:
    return retval;
}

/**
 * \brief Entry point for the listen fiber.
 *
 * This fiber listens for connections, and when it finds one, it spawns an echo
 * service fiber to manage this connection.
 *
 * \param context       The listen fiber context.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status listen_entry(void* context)
{
    status retval, release_retval;
    listen_context* ctx = (listen_context*)context;
    struct sockaddr_in name, peeraddr;
    socklen_t namelen, peerlen;
    psock* listen;
    psock* listen_async;

    /* set the listen address to 0.0.0.0 port 9001. */
    name.sin_family = AF_INET;
    name.sin_port = htons(ctx->port);
    name.sin_addr.s_addr = htonl(INADDR_ANY);
    namelen = sizeof(name);

    /* Create a TCP listen socket, bound to port 9001. */
    retval =
        psock_create_from_listen_address(
            &listen, ctx->alloc, (struct sockaddr*)&name, namelen);
    if (STATUS_SUCCESS != retval)
    {
        printf("Error binding to 0.0.0.0:9001\n");
        goto done;
    }

    /* wrap the listen socket to make it async. */
    retval =
        psock_create_wrap_async(&listen_async, ctx->alloc, ctx->fib, listen);
    if (STATUS_SUCCESS != retval)
    {
        printf("Error creating async socket from listen socket.\n");
        goto cleanup_listen;
    }

    /* the listen socket should no longer be used directly. */
    listen = NULL;

    /* display startup message. */
    printf("Listening for connections.\n");

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

        /* send this socket to our dispatch method. */
        retval = dispatch(desc, ctx->alloc, ctx->sched);
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

cleanup_listen:
    if (NULL != listen)
    {
        release_retval = resource_release(psock_resource_handle(listen));
        if (STATUS_SUCCESS != release_retval)
        {
            retval = release_retval;
        }
    }

done:
    release_retval = resource_release(&ctx->hdr);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

    return retval;
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
    uint8_t data[1024];
    size_t data_size;

    for (;;)
    {
        /* read a byte from the peer. */
        data_size = sizeof(data);
        retval = psock_read_raw(ctx->sock, data, &data_size);
        if (ERROR_PSOCK_READ_WOULD_BLOCK == retval)
        {
            retval = psock_read_block(ctx->sock);
            if (STATUS_SUCCESS != retval)
            {
                goto cleanup_context;
            }

            continue;
        }
        else if (STATUS_SUCCESS != retval)
        {
            goto cleanup_context;
        }

        /* write this byte back to the peer. */
        retval = psock_write_raw_data(ctx->sock, data, data_size);
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
