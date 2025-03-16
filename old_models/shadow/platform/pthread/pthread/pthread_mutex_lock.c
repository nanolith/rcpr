#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

int pthread_mutex_lock(pthread_mutex_t* mu)
{
    dummy_pthread_mutex** mutex = (dummy_pthread_mutex**)mu;
    RCPR_MODEL_ASSERT(NULL != mutex);
    RCPR_MODEL_ASSERT(NULL != *mutex);
    RCPR_MODEL_ASSERT(NULL == (*mutex)->lock);

    (*mutex)->lock =
        (dummy_pthread_mutex_lock*)malloc(sizeof(dummy_pthread_mutex_lock));

    /* use the non-determinism of malloc to influence our return value. */
    if (NULL == (*mutex)->lock)
        return 1;

    return 0;
}
