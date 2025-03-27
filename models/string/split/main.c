#include <rcpr/model_assert.h>
#include <rcpr/string.h>

RCPR_IMPORT_string_as(rcpr);

int nondet_delim();
int delim()
{
    int retval = nondet_delim();
    if (retval <= 0 || retval > 127)
        retval = ' ';

    return retval;
}

int main(int argc, char* argv[])
{
    const char* lhs;
    const char* rhs;
    int retval;

    /* a string of random data. */
    char buffer[8];
    buffer[7] = 0;
    RCPR_MODEL_ASSUME(__CPROVER_is_zero_string(buffer));

    /* split the buffer. */
    retval = rcpr_split(&lhs, &rhs, buffer, delim());
    if (STATUS_SUCCESS != retval)
    {
        return 0;
    }

    return 0;
}
