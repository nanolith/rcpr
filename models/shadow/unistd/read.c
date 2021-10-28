#include <rcpr/model_assert.h>
#include <rcpr/shadow/valid_range.h>
#include <stdint.h>
#include <unistd.h>

#include "descriptor.h"

bool nondet_bool();
uint8_t nondet_byte();
size_t nondet_size();

ssize_t read(int fd, void* buf, size_t count)
{
    RCPR_MODEL_ASSERT(fd >= 0);
    RCPR_MODEL_ASSERT(NULL != descriptor_array[fd]);
    RCPR_MODEL_ASSERT(NULL != buf);

    /* verify the min and max bounds of buf with respect to count. */
    RCPR_MODEL_ASSERT(prop_valid_range(buf, count));

    /* mutate the buf data. */
    size_t mutate_count = count > 9 ? 9 : count;
    for (int i = 0; i < mutate_count; ++i)
    {
        uint8_t* bbuf = (uint8_t*)buf;
        bbuf[i] = nondet_byte();
    }

    /* maybe return an error. */
    if (!nondet_bool())
        return -1;

    /* return a size between 0 and count. */
    size_t val = nondet_size();
    if (val >= count)
    {
        return count;
    }
    else
    {
        return count - val;
    }
}
