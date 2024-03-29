#include <rcpr/model_assert.h>

bool munmap_force_unmap = false;

bool nondet_bool();

int munmap(void *addr, size_t len)
{
    RCPR_MODEL_ASSERT(NULL != addr);
    RCPR_MODEL_ASSERT(len > 0);

    if (munmap_force_unmap || nondet_bool())
    {
        free(addr);

        return 0;
    }
    else
    {
        return -1;
    }
}
