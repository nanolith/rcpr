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
        /* the only reason why it could fail is if we ran out of memory. */
        RCPR_MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        return 0;
    }

    /* we should be able to release the malloc allocator. */
    resource* alloc_resource = allocator_resource_handle(alloc);
    RCPR_MODEL_ASSERT(STATUS_SUCCESS == resource_release(alloc_resource));

    return 0;
}
