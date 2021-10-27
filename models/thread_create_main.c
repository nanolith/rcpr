#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/thread.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_thread;

void allocator_struct_tag_init();
void resource_struct_tag_init();
void thread_struct_tag_init();

static status mythread(void* ctx)
{
    return STATUS_SUCCESS;
}

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    thread* th = NULL;
    int retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global resource tag. */
    resource_struct_tag_init();

    /* set up the global thread tag. */
    thread_struct_tag_init();

    /* try to create a malloc allocator. */
    retval = malloc_allocator_create(&alloc); 
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* create a thread. */
    retval = thread_create(&th, alloc, 16384, NULL, &mythread);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_allocator;
    }

    goto cleanup_thread;

cleanup_thread:
    /* join and release the thread. */
    resource_release(thread_resource_handle(th));

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
