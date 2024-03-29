#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

static int nondet_return_value();

int pthread_attr_destroy(pthread_attr_t *atr)
{
    dummy_pthread_attr** attr = (dummy_pthread_attr**)atr;
    RCPR_MODEL_ASSERT(NULL != attr);
    RCPR_MODEL_ASSERT(NULL != *attr);

    free(*attr);

    return nondet_return_value();
}
