#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

static int nondet_return_value();

int pthread_attr_setstacksize(pthread_attr_t *atr, size_t)
{
    dummy_pthread_attr** attr = (dummy_pthread_attr**)atr;
    RCPR_MODEL_ASSERT(NULL != attr);
    RCPR_MODEL_ASSERT(NULL != *attr);

    return nondet_return_value();
}
