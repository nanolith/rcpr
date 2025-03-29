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

int main(int argc, char* argv[])
{
    const char* lhs;
    const char* rhs;
    int retval;

    /* a string of random data. */
    char str1[8];
    size_t str1_size = size();
    str1[str1_size] = 0;
    RCPR_MODEL_ASSUME(__CPROVER_is_zero_string(str1));

    /* a string of random data. */
    char str2[8];
    size_t str2_size = size();
    str2[str2_size] = 0;
    RCPR_MODEL_ASSUME(__CPROVER_is_zero_string(str2));

    /* split the buffer. */
    if (rcpr_starts_with(str1, str2))
    {
        return 0;
    }

    return 0;
}
