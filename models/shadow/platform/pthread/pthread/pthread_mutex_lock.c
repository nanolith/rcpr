#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

int pthread_mutex_lock(pthread_mutex_t* mutex)
{
    RCPR_MODEL_ASSERT(NULL != mutex);
    RCPR_MODEL_ASSERT(NULL != *mutex);
    RCPR_MODEL_ASSERT(NULL == (*mutex)->lock);

    (*mutex)->lock =
        (struct pthread_mutex_lock*)malloc(sizeof(struct pthread_mutex_lock));

    /* use the non-determinism of malloc to influence our return value. */
    if (NULL == (*mutex)->lock)
        return 1;

    return 0;
}
