#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

int pthread_mutex_init(
    pthread_mutex_t *mutex,
    const pthread_mutexattr_t *attr)
{
    RCPR_MODEL_ASSERT(NULL != mutex);

    *mutex = (struct pthread_mutex*)malloc(sizeof(struct pthread_mutex));

    /* use the non-determinism of malloc to influence our return value. */
    if (NULL == *mutex)
        return 1;

    /* the resource was acquired, so set the lock pointer to null. */
    (*mutex)->lock = NULL;

    return 0;
}
