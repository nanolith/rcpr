#include <rcpr/model_assert.h>
#include <rcpr/shadow/valid_range.h>
#include <stdint.h>
#include <sys/socket.h>
#include <unistd.h>

#include "descriptor.h"

bool nondet_bool();
size_t nondet_size();

ssize_t sendmsg(int fd, const struct msghdr *buf, int flags)
{
    RCPR_MODEL_ASSERT(fd >= 0);
    RCPR_MODEL_ASSERT(NULL != descriptor_array[fd]);
    RCPR_MODEL_ASSERT(NULL != buf);
    RCPR_MODEL_ASSERT(prop_valid_range((void*)buf, sizeof(struct msghdr)));

    size_t count = sizeof(struct msghdr);

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
