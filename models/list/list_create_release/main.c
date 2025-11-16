#include <rcpr/model_assert.h>
#include <rcpr/list.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_list;
RCPR_IMPORT_resource;

void allocator_struct_tag_init();
void list_struct_tag_init();
void resource_struct_tag_init();

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    list* l = NULL;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global resource tag. */
    resource_struct_tag_init();

    /* set up the global list tag. */
    list_struct_tag_init();

    /* try to create a malloc allocator. */
    int retval = malloc_allocator_create(&alloc);
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* try to create a list instance. */
    retval = list_create(&l, alloc);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_alloc;
    }

    goto cleanup_list;

cleanup_list:
    /* we should be able to release the list. */
    retval = resource_release(list_resource_handle(l));
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_alloc;
    }

cleanup_alloc:
    /* we should be able to release the malloc allocator. */
    retval = resource_release(allocator_resource_handle(alloc));
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

done:
    return retval;
}
