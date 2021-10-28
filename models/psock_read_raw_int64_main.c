#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/psock.h>
#include <rcpr/resource.h>
#include <rcpr/socket_utilities.h>
#include <unistd.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_psock;
RCPR_IMPORT_resource;
RCPR_IMPORT_socket_utilities;

void allocator_struct_tag_init();
void psock_struct_tag_init();

int nondet_domain();
int nondet_type();
int nondet_protocol();

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    psock* sock = NULL;
    int lhs, rhs, retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global psock tag. */
    psock_struct_tag_init();

    /* try to create a malloc allocator. */
    retval = malloc_allocator_create(&alloc); 
    if (STATUS_SUCCESS != retval)
    {
        return 0;
    }

    /* create a socketpair. */
    retval =
        socket_utility_socketpair(
            nondet_domain(), nondet_type(), nondet_protocol(), &lhs, &rhs);
    if (STATUS_SUCCESS != retval)
    {
        resource_release(allocator_resource_handle(alloc));

        return 0;
    }

    /* close the rhs descriptor. */
    close(rhs);

    /* create a psock from the lhs descriptor. */
    retval = psock_create_from_descriptor(&sock, alloc, lhs);
    if (STATUS_SUCCESS != retval)
    {
        /* the only reason why it could fail is due to a memory issue. */
        RCPR_MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        close(lhs);
        resource_release(allocator_resource_handle(alloc));

        return 0;
    }

    /* read a raw int64 from the psock. */
    int64_t val = 0;
    retval = psock_read_raw_int64(sock, &val);
    if (STATUS_SUCCESS != retval)
    {
        resource_release(psock_resource_handle(sock));
        resource_release(allocator_resource_handle(alloc));

        return 0;
    }

    /* release the psock. */
    resource_release(psock_resource_handle(sock));

    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

    return 0;
}
