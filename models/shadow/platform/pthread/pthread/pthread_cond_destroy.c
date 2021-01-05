#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

static int nondet_return_value();

int pthread_cond_destroy(pthread_cond_t *cond)
{
    MODEL_ASSERT(NULL != cond);
    MODEL_ASSERT(NULL != *cond);

    free((void*)*cond);

    return nondet_return_value();
}
