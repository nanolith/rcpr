#include <rcpr/model_assert.h>
#include <rcpr/string.h>

RCPR_IMPORT_string_as(rcpr);

size_t nondet_size();
size_t size()
{
    size_t retval = nondet_size();
    if (retval > 7)
        retval = 7;

    return retval;
}

int nondet_delim();
int delim()
{
    int retval = nondet_delim();
    if (retval <= 0 || retval > 127)
        retval = 127;

    return retval;
}

int main(int argc, char* argv[])
{
    const char* lhs;
    const char* rhs;
    int retval;

    /* a string of random data. */
    char buffer[8];
    buffer[size()] = 0;
    RCPR_MODEL_ASSUME(__CPROVER_is_zero_string(buffer));

    /* check if the buffer ends with the given delimiter. */
    if (rcpr_ends_with(buffer, delim()))
    {
        return 0;
    }

    return 0;
}
