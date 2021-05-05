#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/queue.h>

void allocator_struct_tag_init();
void queue_struct_tag_init();
void resource_struct_tag_init();
void slist_struct_tag_init();
void slist_node_struct_tag_init();
status mock_resource_create(resource** r);
status mock_resource_release(resource* r);

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    queue* q = NULL;
    int retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global resource tag. */
    resource_struct_tag_init();

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

    /* create a dummy resource. */
    resource* r1 = NULL;
    retval = mock_resource_create(&r1); 
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_queue;
    }

    /* insert this resource to the queue. */
    retval = queue_insert(q, r1);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mock1;
    }

    /* create a dummy resource. */
    resource* r2 = NULL;
    retval = mock_resource_create(&r2); 
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_queue;
    }

    /* insert this resource to the queue. */
    retval = queue_insert(q, r2);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mock2;
    }

    /* create a dummy resource. */
    resource* r3 = NULL;
    retval = mock_resource_create(&r3); 
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_queue;
    }

    /* insert this resource to the queue. */
    retval = queue_insert(q, r3);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mock3;
    }

    goto cleanup_queue;

cleanup_mock3:
    mock_resource_release(r3);
    goto cleanup_queue;

cleanup_mock2:
    mock_resource_release(r2);
    goto cleanup_queue;

cleanup_mock1:
    mock_resource_release(r1);

cleanup_queue:
    /* release the queue. */
    resource_release(queue_resource_handle(q));

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
