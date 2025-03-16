#include <rcpr/model_assert.h>
#include <rcpr/allocator.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

void allocator_struct_tag_init();
void resource_struct_tag_init();

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global resource tag. */
    resource_struct_tag_init();

    /* try to create a malloc allocator. */
    int retval = malloc_allocator_create(&alloc);
    if (STATUS_SUCCESS != retval)
    {
        return 1;
    }

    /* we should be able to release the malloc allocator. */
    resource* alloc_resource = allocator_resource_handle(alloc);
    retval = resource_release(alloc_resource);
    if (STATUS_SUCCESS != retval)
    {
        return 1;
    }

    return 0;
}
