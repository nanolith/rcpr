#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/list.h>

void allocator_struct_tag_init();
void list_struct_tag_init();
void list_node_struct_tag_init();

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    list* l = NULL;
    int retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

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

    /* create a list instance. */
    retval = list_create(&l, alloc);
    if (STATUS_SUCCESS != retval)
    {
        /* the only reason why it could fail is due to a memory issue. */
        MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        goto cleanup_allocator;
    }

    /* get the head. */
    list_node* head = NULL;
    retval = list_head(&head, l);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_list;
    }

    /* head should be null for an empty list. */
    MODEL_ASSERT(NULL == head);

    /* get the tail. */
    list_node* tail = NULL;
    retval = list_tail(&tail, l);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_list;
    }

    /* tail should be null for an empty list. */
    MODEL_ASSERT(NULL == tail);

cleanup_list:
    /* release the list. */
    resource_release(list_resource_handle(l));

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
