#include <rcpr/model_assert.h>
#include <rcpr/shadow/valid_range.h>
#include <stdint.h>

void *cbmc_memset(void *s, int c, size_t n)
{
    RCPR_MODEL_ASSERT(NULL != s);
    RCPR_MODEL_ASSERT(prop_valid_range(s, n));

    /* mutate the s data. */
    size_t mutate_count = n > 9 ? 9 : n;
    for (int i = 0; i < mutate_count; ++i)
    {
        uint8_t* bbuf = (uint8_t*)s;
        bbuf[i] = c;
    }

    return s;
}
