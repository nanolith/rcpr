#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

static int nondet_return_value();

int pthread_cond_destroy(pthread_cond_t *cond)
{
    RCPR_MODEL_ASSERT(NULL != cond);
    RCPR_MODEL_ASSERT(NULL != *cond);

    free((void*)*cond);

    return nondet_return_value();
}
