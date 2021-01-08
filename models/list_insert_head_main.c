#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/list.h>

void allocator_struct_tag_init();
void resource_struct_tag_init();
void list_struct_tag_init();
void list_node_struct_tag_init();
status mock_resource_create(resource** r);
status mock_resource_release(resource* r);

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    list* l = NULL;
    int retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global resource tag. */
    resource_struct_tag_init();

    /* set up the global list tag. */
    list_struct_tag_init();

    /* set up the global list_node tag. */
    list_node_struct_tag_init();

    /* try to create a malloc allocator. */
    retval = malloc_allocator_create(&alloc); 
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* create an list instance. */
    retval = list_create(&l, alloc);
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
        goto cleanup_list;
    }

    /* insert this resource into the list. */
    retval = list_insert_head(l, r1);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mock1;
    }

    /* create a dummy resource. */
    resource* r2 = NULL;
    retval = mock_resource_create(&r2); 
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_list;
    }

    /* insert this resource into the list. */
    retval = list_insert_head(l, r2);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mock2;
    }

    /* get the head. */
    list_node* head = NULL;
    retval = list_head(&head, l);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_list;
    }

    /* head should NOT be null. */
    MODEL_ASSERT(NULL != head);

    /* get the tail. */
    list_node* tail = NULL;
    retval = list_tail(&tail, l);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_list;
    }

    /* tail should NOT be null for an empty list. */
    MODEL_ASSERT(NULL != tail);

    goto cleanup_list;

cleanup_mock2:
    mock_resource_release(r2);
    goto cleanup_list;

cleanup_mock1:
    mock_resource_release(r1);

cleanup_list:
    /* release the list. */
    resource_release(list_resource_handle(l));

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
