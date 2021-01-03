#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

static int nondet_return_value();

int pthread_attr_setstacksize(pthread_attr_t *attr, size_t)
{
    MODEL_ASSERT(NULL != attr);
    MODEL_ASSERT(NULL != *attr);

    return nondet_return_value();
}
