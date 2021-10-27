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
    int val;
    int waiters;
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

    /* increment the number of waiters. */
    ++(ts->waiters);

    /* wait on a signal. */
    retval = thread_cond_wait(&lock, ts->cond);
    if (STATUS_SUCCESS != retval)
    {
        goto release_lock;
    }

    /* decrement the number of waiters. */
    --(ts->waiters);

    /* increment val on signal. */
    ++(ts->val);

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

static int read_val(threadstuff* ts, int* val)
{
    int cleanup_retval = 0, retval = 0;
    thread_mutex_lock* lock = nullptr;

    /* acquire the mutex lock. */
    retval = thread_mutex_lock_acquire(&lock, ts->mut);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* get val. */
    *val = ts->val;

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

static int read_waiters(threadstuff* ts, int* waiters)
{
    int cleanup_retval = 0, retval = 0;
    thread_mutex_lock* lock = nullptr;

    /* acquire the mutex lock. */
    retval = thread_mutex_lock_acquire(&lock, ts->mut);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* get waiters. */
    *waiters = ts->waiters;

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

static int wait_on_waiters(threadstuff* ts, const int num_waiters)
{
    int retval = 0;
    int waiters = 0;

    /* wait until the thread is blocking. */
    do
    {
        /* block for a bit. */
        usleep(1000);

        /* check the waiters value. */
        retval = read_waiters(ts, &waiters);
        if (STATUS_SUCCESS != retval)
        {
            return retval;
        }
    } while (num_waiters != waiters);

    return STATUS_SUCCESS;
}

static int signal_one_thread(threadstuff* ts)
{
    int cleanup_retval = 0, retval = 0;
    thread_mutex_lock* lock = nullptr;

    /* acquire the mutex lock. */
    retval = thread_mutex_lock_acquire(&lock, ts->mut);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* signal a single thread. */
    retval = thread_cond_signal_one(lock, ts->cond);
    if (STATUS_SUCCESS != retval)
    {
        goto release_lock;
    }

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

static int signal_all_threads(threadstuff* ts)
{
    int cleanup_retval = 0, retval = 0;
    thread_mutex_lock* lock = nullptr;

    /* acquire the mutex lock. */
    retval = thread_mutex_lock_acquire(&lock, ts->mut);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* signal all threads. */
    retval = thread_cond_signal_all(lock, ts->cond);
    if (STATUS_SUCCESS != retval)
    {
        goto release_lock;
    }

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
    int waiters;
    int val;

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
    TEST_ASSERT(STATUS_SUCCESS == read_val(&ts, &val));
    TEST_ASSERT(0 == val);

    /* precondition: there are no waiters. */
    TEST_ASSERT(STATUS_SUCCESS == read_waiters(&ts, &waiters));
    TEST_ASSERT(0 == waiters);

    /* create thread one. */
    TEST_ASSERT(
        STATUS_SUCCESS == thread_create(&one, alloc, 16384, &ts, &incr));

    /* wait until the thread is blocking. */
    TEST_ASSERT(STATUS_SUCCESS == wait_on_waiters(&ts, 1));

    /* val is still zero. */
    TEST_ASSERT(STATUS_SUCCESS == read_val(&ts, &val));
    TEST_ASSERT(0 == val);

    /* create thread two. */
    TEST_ASSERT(
        STATUS_SUCCESS == thread_create(&two, alloc, 16384, &ts, &incr));

    /* wait until the thread is blocking. */
    TEST_ASSERT(STATUS_SUCCESS == wait_on_waiters(&ts, 2));

    /* val is still zero. */
    TEST_ASSERT(STATUS_SUCCESS == read_val(&ts, &val));
    TEST_ASSERT(0 == val);

    /* signal a thread. */
    TEST_ASSERT(
        STATUS_SUCCESS == signal_one_thread(&ts));

    /* wait until the thread is unblocked. */
    TEST_ASSERT(STATUS_SUCCESS == wait_on_waiters(&ts, 1));

    /* val is one. */
    TEST_ASSERT(STATUS_SUCCESS == read_val(&ts, &val));
    TEST_ASSERT(1 == val);

    /* signal a thread. */
    TEST_ASSERT(
        STATUS_SUCCESS == signal_one_thread(&ts));

    /* wait until the thread is unblocked. */
    TEST_ASSERT(STATUS_SUCCESS == wait_on_waiters(&ts, 0));

    /* val is two. */
    TEST_ASSERT(STATUS_SUCCESS == read_val(&ts, &val));
    TEST_ASSERT(2 == val);

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
    int waiters;
    int val;

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
    TEST_ASSERT(STATUS_SUCCESS == read_val(&ts, &val));
    TEST_ASSERT(0 == val);

    /* precondition: there are no waiters. */
    TEST_ASSERT(STATUS_SUCCESS == read_waiters(&ts, &waiters));
    TEST_ASSERT(0 == waiters);

    /* create thread one. */
    TEST_ASSERT(
        STATUS_SUCCESS == thread_create(&one, alloc, 16384, &ts, &incr));

    /* wait until the thread is blocking. */
    TEST_ASSERT(STATUS_SUCCESS == wait_on_waiters(&ts, 1));

    /* val is still zero. */
    TEST_ASSERT(STATUS_SUCCESS == read_val(&ts, &val));
    TEST_ASSERT(0 == val);

    /* create thread two. */
    TEST_ASSERT(
        STATUS_SUCCESS == thread_create(&two, alloc, 16384, &ts, &incr));

    /* wait until the thread is blocking. */
    TEST_ASSERT(STATUS_SUCCESS == wait_on_waiters(&ts, 2));

    /* val is still zero. */
    TEST_ASSERT(STATUS_SUCCESS == read_val(&ts, &val));
    TEST_ASSERT(0 == val);

    /* create thread three. */
    TEST_ASSERT(
        STATUS_SUCCESS == thread_create(&three, alloc, 16384, &ts, &incr));

    /* wait until the thread is blocking. */
    TEST_ASSERT(STATUS_SUCCESS == wait_on_waiters(&ts, 3));

    /* val is still zero. */
    TEST_ASSERT(STATUS_SUCCESS == read_val(&ts, &val));
    TEST_ASSERT(0 == val);

    /* signal all threads. */
    TEST_ASSERT(
        STATUS_SUCCESS == signal_all_threads(&ts));

    /* wait until all threads are unblocked. */
    TEST_ASSERT(STATUS_SUCCESS == wait_on_waiters(&ts, 0));

    /* val is three. */
    TEST_ASSERT(STATUS_SUCCESS == read_val(&ts, &val));
    TEST_ASSERT(3 == val);

    /* release (join) thread one. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_resource_handle(one)));

    /* release (join) thread two. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_resource_handle(two)));

    /* release (join) thread three. */
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(thread_resource_handle(three)));

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
