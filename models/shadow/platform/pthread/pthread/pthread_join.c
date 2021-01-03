#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

static int nondet_return_value();

int pthread_join(pthread_t *thread, void** value)
{
    MODEL_ASSERT(NULL != thread);
    MODEL_ASSERT(NULL != *thread);

    free(*thread);

    return nondet_return_value();
}
