#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

static int nondet_return_value();

int pthread_attr_setstacksize(pthread_attr_t *attr, size_t)
{
    RCPR_MODEL_ASSERT(NULL != attr);
    RCPR_MODEL_ASSERT(NULL != *attr);

    return nondet_return_value();
}
