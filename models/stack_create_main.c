#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/stack.h>

void allocator_struct_tag_init();
void stack_struct_tag_init();
void stack_node_struct_tag_init();

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
        MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        goto cleanup_allocator;
    }

cleanup_stack:
    /* release the stack. */
    resource_release(stack_resource_handle(st));

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
