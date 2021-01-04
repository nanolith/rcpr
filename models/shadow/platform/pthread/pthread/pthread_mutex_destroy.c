#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

static int nondet_return_value();

int pthread_mutex_destroy(pthread_mutex_t *mutex)
{
    MODEL_ASSERT(NULL != mutex);
    MODEL_ASSERT(NULL != *mutex);

    free((void*)*mutex);

    return nondet_return_value();
}
