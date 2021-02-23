#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/fiber.h>

void allocator_struct_tag_init();
void fiber_struct_tag_init();
void fiber_scheduler_struct_tag_init();
void stack_struct_tag_init();

static status callback(
    void* context, fiber* yield_fib, int yield_event, void* yield_param,
    fiber** resume_fib, int* resume_event, void** resume_param)
{
    MODEL_ASSERT(prop_fiber_valid(yield_fib));

    if (FIBER_SCHEDULER_YIELD_EVENT_MAIN == yield_event)
    {
        *resume_fib = yield_fib;
        *resume_event = FIBER_SCHEDULER_RESUME_EVENT_MAIN;
        *resume_param = NULL;

        return STATUS_SUCCESS;
    }
    else if (FIBER_SCHEDULER_YIELD_EVENT_RUN == yield_event)
    {
        *resume_fib = yield_fib;
        *resume_event = FIBER_SCHEDULER_RESUME_EVENT_RUN;
        *resume_param = NULL;
        fiber* addfib = (fiber*)yield_param;

        return STATUS_SUCCESS;
    }
    else if (FIBER_SCHEDULER_YIELD_EVENT_RESOURCE_RELEASE == yield_event)
    {
        *resume_fib = NULL;
        *resume_event = FIBER_SCHEDULER_RESUME_EVENT_RESOURCE_RELEASE;
        *resume_param = NULL;

        return STATUS_SUCCESS;
    }
    else
    {
        return -1;
    }
}

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    fiber_scheduler* sched = NULL;
    int retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global fiber tag. */
    fiber_struct_tag_init();

    /* set up the global fiber_scheduler tag. */
    fiber_scheduler_struct_tag_init();

    /* set up the global stack tag. */
    stack_struct_tag_init();

    /* try to create a malloc allocator. */
    retval = malloc_allocator_create(&alloc); 
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* create a fiber_scheduler instance. */
    void* ctx = NULL;
    retval = fiber_scheduler_create(&sched, alloc, ctx, &callback);
    if (STATUS_SUCCESS != retval)
    {
        /* the only reason why it could fail is due to a memory issue. */
        MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        goto cleanup_allocator;
    }

    /* run the scheduler... */
    MODEL_ASSERT(STATUS_SUCCESS == fiber_scheduler_run(sched));

cleanup_fiber_scheduler:
    /* release the fiber_scheduler. */
    retval = resource_release(fiber_scheduler_resource_handle(sched));
    MODEL_ASSERT(STATUS_SUCCESS == retval);

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
