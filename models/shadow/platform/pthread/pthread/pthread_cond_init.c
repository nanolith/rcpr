#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

int pthread_cond_init(
    pthread_cond_t *cnd,
    const pthread_condattr_t *attr)
{
    dummy_pthread_cond** cond = (dummy_pthread_cond**)cnd;
    RCPR_MODEL_ASSERT(NULL != cond);

    *cond = (dummy_pthread_cond*)malloc(sizeof(dummy_pthread_cond));

    /* use the non-determinism of malloc to influence our return value. */
    if (NULL == *cond)
        return 1;

    return 0;
}
