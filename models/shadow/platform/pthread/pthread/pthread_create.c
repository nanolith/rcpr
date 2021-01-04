#include <rcpr/model_assert.h>
#include <pthread.h>

#include "pthread_internal.h"

int pthread_create(
    pthread_t *thread, const pthread_attr_t *attr,
    void *(*start_routine)(void *), void *arg)
{
    MODEL_ASSERT(NULL != thread);
    MODEL_ASSERT(NULL != start_routine);

    *thread = (struct pthread*)malloc(sizeof(struct pthread));

    /* use the non-determinism of malloc to influence our return value. */
    if (NULL == *thread)
        return 1;

    start_routine(arg);

    return 0;
}
