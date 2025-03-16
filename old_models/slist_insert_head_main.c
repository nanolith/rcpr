#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/slist.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_slist;

void allocator_struct_tag_init();
void resource_struct_tag_init();
void slist_struct_tag_init();
void slist_node_struct_tag_init();
status mock_resource_create(resource** r);
status mock_resource_release(resource* r);

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    slist* list = NULL;
    int retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global resource tag. */
    resource_struct_tag_init();

    /* set up the global slist tag. */
    slist_struct_tag_init();

    /* set up the global slist_node tag. */
    slist_node_struct_tag_init();

    /* try to create a malloc allocator. */
    retval = malloc_allocator_create(&alloc); 
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* create an slist instance. */
    retval = slist_create(&list, alloc);
    if (STATUS_SUCCESS != retval)
    {
        /* the only reason why it could fail is due to a memory issue. */
        RCPR_MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        goto cleanup_allocator;
    }

    /* create a dummy resource. */
    resource* r1 = NULL;
    retval = mock_resource_create(&r1); 
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_slist;
    }

    /* insert this resource into the list. */
    retval = slist_insert_head(list, r1);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mock1;
    }

    /* create a dummy resource. */
    resource* r2 = NULL;
    retval = mock_resource_create(&r2); 
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_slist;
    }

    /* insert this resource into the list. */
    retval = slist_insert_head(list, r2);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mock2;
    }

    /* get the head. */
    slist_node* head = NULL;
    retval = slist_head(&head, list);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_slist;
    }

    /* head should NOT be null. */
    RCPR_MODEL_ASSERT(NULL != head);

    /* get the tail. */
    slist_node* tail = NULL;
    retval = slist_tail(&tail, list);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_slist;
    }

    /* tail should NOT be null for an empty list. */
    RCPR_MODEL_ASSERT(NULL != tail);

    goto cleanup_slist;

cleanup_mock2:
    mock_resource_release(r2);
    goto cleanup_slist;

cleanup_mock1:
    mock_resource_release(r1);

cleanup_slist:
    /* release the slist. */
    resource_release(slist_resource_handle(list));

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
