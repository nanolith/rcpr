#include <rcpr/model_assert.h>
#include <rcpr/string.h>

RCPR_IMPORT_string_as(rcpr);

int nondet_int();

int main(int argc, char* argv[])
{
    int ch = nondet_int();

    switch (ch)
    {
        case ' ':
        case '\t':
        case '\n':
        case '\v':
        case '\f':
        case '\r':
            RCPR_MODEL_ASSERT(rcpr_is_whitespace(ch));
            break;

        default:
            RCPR_MODEL_ASSERT(!rcpr_is_whitespace(ch));
            break;
    }

    return 0;
}
