#include <rcpr/model_assert.h>
#include <rcpr/string.h>

RCPR_IMPORT_string_as(rcpr);

bool nondet_bool();
bool token_function(int ch)
{
    return nondet_bool();
}

int main(int argc, char* argv[])
{
    const char* word;
    rcpr_string_iterator iterator;
    int retval;

    /* a string of random data. */
    char buffer[8];
    buffer[7] = 0;
    RCPR_MODEL_ASSUME(__CPROVER_is_zero_string(buffer));

    /* get the first split. */
    retval = rcpr_multisplit(&word, &iterator, buffer, &token_function);
    if (STATUS_SUCCESS != retval)
    {
        return 0;
    }

    /* iterate through remaining splits. */
    while (STATUS_SUCCESS == retval)
    {
        retval = rcpr_multisplit(&word, &iterator, NULL, NULL);
    }

    return 0;
}
