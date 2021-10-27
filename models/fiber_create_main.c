#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/fiber.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_resource;

void allocator_struct_tag_init();
void fiber_struct_tag_init();
void fiber_scheduler_struct_tag_init();
void stack_struct_tag_init();

static status callback(
    void* context, fiber* yield_fib, int yield_event, void* yield_param,
    fiber** resume_fib, int* resume_event, void** resume_param)
{
    RCPR_MODEL_ASSERT(prop_fiber_valid(yield_fib));

    *resume_fib = yield_fib;
    *resume_param = NULL;
    *resume_event = yield_event;

    return STATUS_SUCCESS;
}

status myfiber(void* context)
{
    return STATUS_SUCCESS;
}

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    fiber_scheduler* sched = NULL;
    fiber* fib = NULL;
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
        RCPR_MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        goto cleanup_allocator;
    }

    /* create a fiber instance. */
    retval = fiber_create(&fib, alloc, sched, 100, NULL, &myfiber);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_fiber_scheduler;
    }

cleanup_fiber:
    /* release the fiber. */
    retval = resource_release(fiber_resource_handle(fib));
    RCPR_MODEL_ASSERT(STATUS_SUCCESS == retval);

cleanup_fiber_scheduler:
    /* release the fiber_scheduler. */
    retval = resource_release(fiber_scheduler_resource_handle(sched));
    RCPR_MODEL_ASSERT(STATUS_SUCCESS == retval);

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
