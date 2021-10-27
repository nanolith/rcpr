#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

int pthread_attr_init(pthread_attr_t *attr)
{
    RCPR_MODEL_ASSERT(NULL != attr);

    *attr = (struct pthread_attr*)malloc(sizeof(struct pthread_attr));

    /* use the non-determinism of malloc to influence our return value. */
    if (NULL == *attr)
        return 1;
    return 0;
}
