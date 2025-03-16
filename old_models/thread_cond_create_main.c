#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/thread.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_thread;

void allocator_struct_tag_init();
void resource_struct_tag_init();
void thread_cond_struct_tag_init();

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    thread_cond* cond = NULL;
    int retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global resource tag. */
    resource_struct_tag_init();

    /* set up the global thread_cond tag. */
    thread_cond_struct_tag_init();

    /* try to create a malloc allocator. */
    retval = malloc_allocator_create(&alloc); 
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* initialize a thread_cond. */
    retval = thread_cond_create(&cond, alloc);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_allocator;
    }

    goto cleanup_thread_cond;

cleanup_thread_cond:
    /* release the cond. */
    resource_release(thread_cond_resource_handle(cond));

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
