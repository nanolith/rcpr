#include <rcpr/model_assert.h>
#include <rcpr/string.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_string_as(rcpr);

void allocator_struct_tag_init();
void resource_struct_tag_init();

size_t nondet_size();
size_t size()
{
    size_t retval = nondet_size();
    if (retval > 7)
        retval = 7;

    return retval;
}

int main(int argc, char* argv[])
{
    allocator* alloc;
    char* str;
    int retval, release_retval;

    /* set up global tags. */
    allocator_struct_tag_init();
    resource_struct_tag_init();

    /* a string of random data. */
    char buffer[8];
    buffer[size()] = 0;
    RCPR_MODEL_ASSUME(__CPROVER_is_zero_string(buffer));

    /* create a malloc allocator. */
    retval = malloc_allocator_create(&alloc);
    if (STATUS_SUCCESS != retval)
    {
        retval = 1;
        goto done;
    }

    /* Duplicate the buffer. */
    retval = rcpr_strdup(&str, alloc, buffer);
    if (STATUS_SUCCESS != retval)
    {
        retval = 1;
        goto cleanup_alloc;
    }

    /* release the string. */
    retval = allocator_reclaim(alloc, str);
    if (STATUS_SUCCESS != retval)
    {
        retval = 1;
        goto cleanup_alloc;
    }

    /* success. */
    retval = 0;
    goto cleanup_alloc;

cleanup_alloc:
    release_retval = resource_release(allocator_resource_handle(alloc));
    if (STATUS_SUCCESS != release_retval)
    {
        retval = release_retval;
    }

done:
    return retval;
}
