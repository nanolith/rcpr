#include <rcpr/model_assert.h>
#include <rcpr/allocator.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;

void allocator_struct_tag_init();
void resource_struct_tag_init();

#define MAX_SIZE (10 * 1024 * 1024)

static size_t nondet_size();
static size_t allocate_size()
{
    size_t size = nondet_size();
    if (size > MAX_SIZE)
    {
        size = MAX_SIZE;
    }

    return size;
}

int main(int argc, char* argv[])
{
    int retval, release_retval;
    allocator* alloc = NULL;
    resource* alloc_resource = NULL;
    void* ptr = NULL;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global resource tag. */
    resource_struct_tag_init();

    /* try to create a malloc allocator. */
    retval = malloc_allocator_create(&alloc);
    if (STATUS_SUCCESS != retval)
    {
        retval = 1;
        goto done;
    }

    /* allocate memory. */
    retval = allocator_allocate(alloc, &ptr, allocate_size());
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_alloc;
    }

    /* reclaim memory. */
    retval = allocator_reclaim(alloc, ptr);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_alloc;
    }

    /* success. */
    retval = STATUS_SUCCESS;
    goto cleanup_alloc;

cleanup_alloc:
    /* we should be able to release the malloc allocator. */
    alloc_resource = allocator_resource_handle(alloc);
    release_retval = resource_release(alloc_resource);
    if (STATUS_SUCCESS != release_retval)
    {
        retval = 1;
    }

done:
    return retval;
}
