#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/uuid.h>

RCPR_IMPORT_uuid;

uint8_t nondet_char();
static void build_random_input_string(char* str);

int main(int argc, char* argv[])
{
    int retval;

    rcpr_uuid id;
    char input_string[40];

    build_random_input_string(input_string);

    retval = rcpr_uuid_parse_string(&id, input_string);
    if (STATUS_SUCCESS != retval)
    {
        return 0;
    }

    return 0;
}

static void build_random_input_string(char* str)
{
    str[ 0] = nondet_char();
    str[ 1] = nondet_char();
    str[ 2] = nondet_char();
    str[ 3] = nondet_char();
    str[ 4] = nondet_char();
    str[ 5] = nondet_char();
    str[ 6] = nondet_char();
    str[ 7] = nondet_char();
    str[ 8] = nondet_char();
    str[ 9] = nondet_char();
    str[10] = nondet_char();
    str[11] = nondet_char();
    str[12] = nondet_char();
    str[13] = nondet_char();
    str[14] = nondet_char();
    str[15] = nondet_char();
    str[16] = nondet_char();
    str[17] = nondet_char();
    str[18] = nondet_char();
    str[19] = nondet_char();
    str[20] = nondet_char();
    str[21] = nondet_char();
    str[22] = nondet_char();
    str[23] = nondet_char();
    str[24] = nondet_char();
    str[25] = nondet_char();
    str[26] = nondet_char();
    str[27] = nondet_char();
    str[28] = nondet_char();
    str[29] = nondet_char();
    str[30] = nondet_char();
    str[31] = nondet_char();
    str[32] = nondet_char();
    str[33] = nondet_char();
    str[34] = nondet_char();
    str[35] = nondet_char();
    str[36] = nondet_char();
    str[37] = nondet_char();
    str[38] = nondet_char();
    str[39] = 0;
}


