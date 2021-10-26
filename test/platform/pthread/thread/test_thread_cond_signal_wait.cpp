/**
 * \file test/platform/pthread/thread/test_thread_cond_signal_wait.cpp
 *
 * \brief Unit tests for thread_cond_signal_* and thread_cond_wait.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/thread.h>
#include <string.h>
#include <unistd.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_thread;

TEST_SUITE(thread_cond_signal_wait);

/* simple thread context. */
typedef struct threadstuff threadstuff;
struct threadstuff
{
    thread_mutex* mut;
    thread_cond* cond;
    volatile int val;
};

/* simple thread context function. */
static status incr(void* context)
{
    int retval, cleanup_retval;
    thread_mutex_lock* lock = nullptr;
    threadstuff* ts = (threadstuff*)context;

    /* acquire the mutex lock. */
    retval = thread_mutex_lock_acquire(&lock, ts->mut);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* wait on a signal. */
    retval = thread_cond_wait(&lock, ts->cond);
    if (STATUS_SUCCESS != retval)
    {
        goto release_lock;
    }

    /* increment val on signal. */
    ts->val = ts->val + 1;

    /* success. */
    retval = STATUS_SUCCESS;
    goto release_lock;

release_lock:
    cleanup_retval = resource_release(thread_mutex_lock_resource_handle(lock));
    if (STATUS_SUCCESS != cleanup_retval)
    {
        retval = cleanup_retval;
    }

done:
    return retval;
}

/**
 * Create two threads. Signal one, then the other. Verify that a counter
 * increments each time.
 */
TEST(wait_signal_one)
{
    allocator* alloc = nullptr;
    thread* one = nullptr;
    thread* two = nullptr;
    thread_mutex* mut = nullptr;
    thread_cond* cond = nullptr;
    threadstuff ts;

    /* clear thread context. */
    memset(&ts, 0, sizeof(ts));

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a thread cond. */
    TEST_ASSERT(STATUS_SUCCESS == thread_cond_create(&cond, alloc));

    /* we should be able to create a thread mutex. */
    TEST_ASSERT(STATUS_SUCCESS == thread_mutex_create(&mut, alloc));

    /* copy these resources to ts. */
    ts.mut = mut;
    ts.cond = cond;

    /* precondition: val is 0. */
    TEST_ASSERT(ts.val == 0);

    /* create thread one. */
    TEST_ASSERT(
        STATUS_SUCCESS == thread_create(&one, alloc, 16384, &ts, &incr));

    /* sleep 1 ms. */
    usleep(1000);

    /* val is still zero. */
    TEST_ASSERT(ts.val == 0);

    /* create thread two. */
    TEST_ASSERT(
        STATUS_SUCCESS == thread_create(&two, alloc, 16384, &ts, &incr));

    /* sleep 1 ms. */
    usleep(1000);

    /* val is still zero. */
    TEST_ASSERT(ts.val == 0);

    /* signal a thread. */
    TEST_ASSERT(
        STATUS_SUCCESS == thread_cond_signal_one(cond));

    /* sleep 1 ms. */
    usleep(1000);

    /* val is one. */
    TEST_ASSERT(ts.val == 1);

    /* signal a thread. */
    TEST_ASSERT(
        STATUS_SUCCESS == thread_cond_signal_one(cond));

    /* sleep 1 ms. */
    usleep(1000);

    /* val is two. */
    TEST_ASSERT(ts.val == 2);

    /* release (join) thread one. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_resource_handle(one)));

    /* release (join) thread two. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_resource_handle(two)));

    /* release the mutex. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_mutex_resource_handle(mut)));

    /* release the condition variable. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_cond_resource_handle(cond)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Create three threads. Signal all. Verify that a counter increments thrice.
 */
TEST(wait_signal_all)
{
    allocator* alloc = nullptr;
    thread* one = nullptr;
    thread* two = nullptr;
    thread* three = nullptr;
    thread_mutex* mut = nullptr;
    thread_cond* cond = nullptr;
    threadstuff ts;

    /* clear thread context. */
    memset(&ts, 0, sizeof(ts));

    /* we should be able to create a malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* we should be able to create a thread cond. */
    TEST_ASSERT(STATUS_SUCCESS == thread_cond_create(&cond, alloc));

    /* we should be able to create a thread mutex. */
    TEST_ASSERT(STATUS_SUCCESS == thread_mutex_create(&mut, alloc));

    /* copy these resources to ts. */
    ts.mut = mut;
    ts.cond = cond;

    /* precondition: val is 0. */
    TEST_ASSERT(ts.val == 0);

    /* create thread one. */
    TEST_ASSERT(
        STATUS_SUCCESS == thread_create(&one, alloc, 16384, &ts, &incr));

    /* sleep 1 ms. */
    usleep(1000);

    /* val is still zero. */
    TEST_ASSERT(ts.val == 0);

    /* create thread two. */
    TEST_ASSERT(
        STATUS_SUCCESS == thread_create(&two, alloc, 16384, &ts, &incr));

    /* sleep 1 ms. */
    usleep(1000);

    /* val is still zero. */
    TEST_ASSERT(ts.val == 0);

    /* create thread three. */
    TEST_ASSERT(
        STATUS_SUCCESS == thread_create(&three, alloc, 16384, &ts, &incr));

    /* sleep 1 ms. */
    usleep(1000);

    /* val is still zero. */
    TEST_ASSERT(ts.val == 0);

    /* signal all threads. */
    TEST_ASSERT(
        STATUS_SUCCESS == thread_cond_signal_all(cond));

    /* release (join) thread one. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_resource_handle(one)));

    /* release (join) thread two. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_resource_handle(two)));

    /* release (join) thread three. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_resource_handle(three)));

    /* val is three. */
    TEST_ASSERT(ts.val == 3);

    /* release the mutex. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_mutex_resource_handle(mut)));

    /* release the condition variable. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_cond_resource_handle(cond)));

    /* clean up. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
