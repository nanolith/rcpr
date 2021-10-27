#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

static int nondet_return_value();

int pthread_join(pthread_t thread, void** value)
{
    RCPR_MODEL_ASSERT(NULL != thread);

    free((void*)thread);

    return nondet_return_value();
}
