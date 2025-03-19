#include <rcpr/model_assert.h>
#include <stdlib.h>

void *realloc(void *ptr, size_t size)
{
    RCPR_MODEL_ASSERT(NULL != ptr);

    void* newmem = malloc(size);
    if (NULL == newmem)
    {
        return NULL;
    }

    free(ptr);
    __CPROVER_havoc_object(newmem);
    return newmem;
}
