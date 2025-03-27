#include <rcpr/model_assert.h>
#include <rcpr/string.h>

RCPR_IMPORT_string_as(rcpr);

int main(int argc, char* argv[])
{
    const char* word;
    rcpr_string_iterator iterator;
    int retval;

    /* a string of random data. */
    char buffer[8];
    buffer[7] = 0;
    RCPR_MODEL_ASSUME(__CPROVER_is_zero_string(buffer));

    /* get the first word. */
    retval = rcpr_words(&word, &iterator, buffer);
    if (STATUS_SUCCESS != retval)
    {
        return 0;
    }

    /* iterate through remaining words. */
    while (STATUS_SUCCESS == retval)
    {
        retval = rcpr_words(&word, &iterator, NULL);
    }

    return 0;
}
