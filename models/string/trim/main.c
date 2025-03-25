#include <rcpr/model_assert.h>
#include <rcpr/string.h>

RCPR_IMPORT_string_as(rcpr);

int main(int argc, char* argv[])
{
    /* a string of random data. */
    char buffer[8];
    buffer[7] = 0;
    RCPR_MODEL_ASSUME(__CPROVER_is_zero_string(buffer));

    /* trim should work as expected. */
    rcpr_trim(buffer);

    /* success. */
    return 0;
}
