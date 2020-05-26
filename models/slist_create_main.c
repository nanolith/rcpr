#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/slist.h>

void allocator_struct_tag_init();
void slist_struct_tag_init();
void slist_node_struct_tag_init();

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    slist* list = NULL;
    int retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global slist tag. */
    slist_struct_tag_init();

    /* set up the global slist_node tag. */
    slist_node_struct_tag_init();

    /* try to create a malloc allocator. */
    retval = malloc_allocator_create(&alloc); 
    if (STATUS_SUCCESS != retval)
    {
        return 0;
    }

    /* create an slist instance. */
    retval = slist_create(&list, alloc);
    if (STATUS_SUCCESS != retval)
    {
        /* the only reason why it could fail is due to a memory issue. */
        MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        resource_release(allocator_resource_handle(alloc));

        return 0;
    }

    /* release the slist. */
    resource_release(slist_resource_handle(list));

    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

    return 0;
}
