#include <rcpr/model_assert.h>

#include "descriptor.h"

int close(int fd)
{
    /* parameter sanity checks. */
    MODEL_ASSERT(fd >= 0);
    MODEL_ASSERT(NULL != descriptor_array[fd]);

    /* trick the model checker into tracking file descriptors. */
    free(descriptor_array[fd]);

    /* only a single close is allowed. */
    descriptor_array[fd] = NULL;

    return 0;
}
