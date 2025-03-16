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

    /* create a dummy resource to insert into the list. */
    resource* r1 = NULL;
    retval = mock_resource_create(&r1);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_slist;
    }

    /* insert this into the list. */
    retval = slist_insert_head(list, r1);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mock1;
    }

    /* create a resource to insert into the list. */
    resource* r2 = NULL;
    retval = mock_resource_create(&r2);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_slist;
    }

    /* insert this into the list. */
    retval = slist_insert_head(list, r2);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mock2;
    }

    /* create a resource to insert into the list. */
    resource* r3 = NULL;
    retval = mock_resource_create(&r3);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_slist;
    }

    /* insert this into the list. */
    retval = slist_insert_head(list, r3);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mock3;
    }

    /* get the head of the list. */
    slist_node* head = NULL;
    retval = slist_head(&head, list);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_slist;
    }

    /* pop the second resource. */
    resource* r2p = NULL;
    retval = slist_node_next_pop(head, &r2p);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_slist;
    }

    /* it should match r2. */
    RCPR_MODEL_ASSERT(r2p == r2);

    /* pop the first resource. */
    resource* r1p = NULL;
    retval = slist_node_next_pop(head, &r1p);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mock2;
    }

    /* it should match r1. */
    RCPR_MODEL_ASSERT(r1p == r1);

    /* success. clean up. */
    goto cleanup_mocks;

cleanup_mocks:
    resource_release(r1);
    resource_release(r2);
    goto cleanup_slist;

cleanup_mock3:
    resource_release(r3);
    goto cleanup_slist;

cleanup_mock2:
    resource_release(r2);
    goto cleanup_slist;

cleanup_mock1:
    resource_release(r1);

cleanup_slist:
    resource_release(slist_resource_handle(list));

cleanup_allocator:
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
