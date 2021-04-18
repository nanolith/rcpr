#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/fiber.h>

void allocator_struct_tag_init();

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    int retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* try to create a malloc allocator. */
    retval = malloc_allocator_create(&alloc); 
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    rcpr_uuid id = { .data = {
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00 } };
    char* str;

    retval = rcpr_uuid_to_string(&str, alloc, &id);
    if (STATUS_SUCCESS != retval)
    {
        goto cleanup_allocator;
    }

    goto cleanup_string;

cleanup_string:
    allocator_reclaim(alloc, str);

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
