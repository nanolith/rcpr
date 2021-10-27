#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/list.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_list;
RCPR_IMPORT_resource;

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
    list_node* head = NULL;
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
        RCPR_MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        goto cleanup_allocator;
    }

    /* create a dummy resource to insert into the list. */
    resource* r1 = NULL;
    retval = mock_resource_create(&r1);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_list;
    }

    /* append this to the list. */
    retval = list_append_tail(l, r1);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_mock1;
    }

    /* get the head. */
    retval = list_head(&head, l);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_list;
    }

    /* create a resource to swap into the list. */
    resource* r2 = NULL;
    retval = mock_resource_create(&r2);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_list;
    }

    /* swap the resources. */
    retval = list_node_child_swap(head, &r2);
    RCPR_MODEL_ASSERT(STATUS_SUCCESS == retval);

cleanup_mock1:
    resource_release(r1);

cleanup_list:
    resource_release(list_resource_handle(l));

cleanup_allocator:
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
