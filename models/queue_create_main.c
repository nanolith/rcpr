#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/queue.h>
#include <rcpr/resource.h>

void allocator_struct_tag_init();
void slist_struct_tag_init();
void slist_node_struct_tag_init();
void queue_struct_tag_init();

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    queue* q = NULL;
    int retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global slist tag. */
    slist_struct_tag_init();

    /* set up the global slist_node tag. */
    slist_node_struct_tag_init();

    /* set up the global queue tag. */
    queue_struct_tag_init();

    /* try to create a malloc allocator. */
    retval = malloc_allocator_create(&alloc); 
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* create a queue instance. */
    retval = queue_create(&q, alloc);
    if (STATUS_SUCCESS != retval)
    {
        /* the only reason why it could fail is due to a memory issue. */
        MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        goto cleanup_allocator;
    }

    /* get the count. */
    MODEL_ASSERT(0 == queue_count(q));

    /* release the queue. */
    resource_release(queue_resource_handle(q));

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
