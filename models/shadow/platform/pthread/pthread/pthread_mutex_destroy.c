#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

static int nondet_return_value();

int pthread_mutex_destroy(pthread_mutex_t *mutex)
{
    RCPR_MODEL_ASSERT(NULL != mutex);
    RCPR_MODEL_ASSERT(NULL != *mutex);
    RCPR_MODEL_ASSERT(NULL == (*mutex)->lock);

    free((void*)*mutex);

    return nondet_return_value();
}
