#include <rcpr/model_assert.h>
#include <rcpr/allocator.h>

void allocator_struct_tag_init();
void resource_struct_tag_init();

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    int* arr;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global resource tag. */
    resource_struct_tag_init();

    /* try to create a malloc allocator. */
    int retval = malloc_allocator_create(&alloc);
    if (STATUS_SUCCESS != retval)
    {
        /* the only reason why it could fail is if we ran out of memory. */
        MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        return 0;
    }

    /* we should be able to create an array of 10 integers. */
    retval = allocator_allocate(alloc, &arr, 10*sizeof(int));
    if (STATUS_SUCCESS != retval)
    {
        /* the only reason why it could fail is if we ran out of memory. */
        MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        goto cleanup_allocator;
    }

    /* the range of this array should be valid. */
    MODEL_ASSERT(prop_valid_range(arr, 10*sizeof(int)));

    /* reallocate to 15 integers. */
    retval = allocator_reallocate(alloc, &arr, 15*sizeof(int));
    if (STATUS_SUCCESS != retval)
    {
        /* the only reason why it could fail is if we ran out of memory. */
        MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);
    }

    /* the range of this array should be valid. */
    MODEL_ASSERT(prop_valid_range(arr, 15*sizeof(int)));

    /* reclaim memory. */
    retval = allocator_reclaim(alloc, arr);
    MODEL_ASSERT(STATUS_SUCCESS == retval);

cleanup_allocator:
    /* we should be able to release the malloc allocator. */
    resource* alloc_resource = allocator_resource_handle(alloc);
    MODEL_ASSERT(STATUS_SUCCESS == resource_release(alloc_resource));

    return 0;
}