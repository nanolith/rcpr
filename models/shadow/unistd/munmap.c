#include <rcpr/model_assert.h>

int munmap(void *addr, size_t len)
{
    MODEL_ASSERT(NULL != addr);
    MODEL_ASSERT(len > 0);

    free(addr);

    /* TODO - we should simulate an unmapping failure here. */
    return 0;
}
