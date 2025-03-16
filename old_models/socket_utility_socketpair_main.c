#include <rcpr/model_assert.h>
#include <rcpr/socket_utilities.h>
#include <unistd.h>

RCPR_IMPORT_socket_utilities;

int nondet_domain();
int nondet_type();
int nondet_protocol();

int main(int argc, char* argv[])
{
    int lhs, rhs;

    /* create a socketpair. */
    int retval =
        socket_utility_socketpair(
            nondet_domain(), nondet_type(), nondet_protocol(), &lhs, &rhs);
    if (STATUS_SUCCESS != retval)
    {
        RCPR_MODEL_ASSERT(ERROR_SOCKET_UTILITIES_SOCKETPAIR_FAILURE == retval);
        return 0;
    }

    /* close the descriptors. */
    close(lhs);
    close(rhs);

    return 0;
}
