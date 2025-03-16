#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/stack.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_stack;

extern bool munmap_force_unmap;

void allocator_struct_tag_init();
void stack_struct_tag_init();

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    stack* st = NULL;
    int retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global stack tag. */
    stack_struct_tag_init();

    /* try to create a malloc allocator. */
    retval = malloc_allocator_create(&alloc); 
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* create a stack instance. */
    retval = stack_create(&st, alloc, 1024 * 1024);
    if (STATUS_SUCCESS != retval)
    {
        /* the only reason why it could fail is due to a memory issue. */
        RCPR_MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        goto cleanup_allocator;
    }

cleanup_stack:
    /* release the stack. */
    retval = resource_release(stack_resource_handle(st));
    if (STATUS_SUCCESS != retval)
    {
        RCPR_MODEL_ASSERT(ERROR_STACK_UNMAP == retval);

        /* note: this is only to ensure that the model check completes. */
        /* In application code, if the unmapping fails, the application */
        /* should terminate gracefully. */
        munmap_force_unmap = true;
        resource_release(stack_resource_handle(st));
    }

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
