#include <rcpr/model_assert.h>
#include <rcpr/shadow/valid_range.h>
#include <stdint.h>
#include <unistd.h>

#include "descriptor.h"

bool nondet_bool();
size_t nondet_size();

ssize_t write(int fd, const void* buf, size_t count)
{
    MODEL_ASSERT(fd >= 0);
    MODEL_ASSERT(NULL != descriptor_array[fd]);
    MODEL_ASSERT(NULL != buf);

    /* verify the min and max bounds of buf with respect to count. */
    MODEL_ASSERT(prop_valid_range(buf, count));

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
