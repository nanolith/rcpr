#include <rcpr/allocator.h>
#include <rcpr/bigint.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_bigint;
RCPR_IMPORT_resource;

void allocator_struct_tag_init();
void bigint_struct_tag_init();

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    bigint* i = NULL;
    bigint* clone = NULL;
    int retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global bigint tag. */
    bigint_struct_tag_init();

    /* try to create a malloc allocator. */
    retval = malloc_allocator_create(&alloc); 
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* create a bigint instance. */
    retval = bigint_create_zero(&i, alloc, 128);
    if (STATUS_SUCCESS != retval)
    {
        /* the only reason why it could fail is due to a memory issue. */
        RCPR_MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        goto cleanup_allocator;
    }

    /* clone the bigint instance. */
    retval = bigint_clone(&clone, alloc, i);
    if (STATUS_SUCCESS != retval)
    {
        /* the only reason why it could fail is due to a memory issue. */
        RCPR_MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        goto cleanup_bigint;
    }

cleanup_clone:
    /* release the clone. */
    resource_release(bigint_resource_handle(clone));

cleanup_bigint:
    /* release the bigint. */
    resource_release(bigint_resource_handle(i));

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
