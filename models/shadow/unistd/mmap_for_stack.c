/**
 * \file models/shadow/unistd/mmap_for_stack.c
 *
 * \brief mmap specifically for allocating stack frames.
 */

#include <rcpr/model_assert.h>
#include <stdbool.h>
#include <sys/mman.h>

void *mmap(
    void *addr, size_t len, int prot, int flags, int fd, off_t offset)
{
    RCPR_MODEL_ASSERT(NULL == addr);
    RCPR_MODEL_ASSERT(len > 0);
    RCPR_MODEL_ASSERT(PROT_WRITE | PROT_READ == prot);
    RCPR_MODEL_ASSERT(MAP_PRIVATE | MAP_ANONYMOUS | MAP_STACK == flags);
    RCPR_MODEL_ASSERT(-1 == fd);
    RCPR_MODEL_ASSERT(0 == offset);

    void* ret = malloc(len);
    if (NULL == ret)
    {
        return MAP_FAILED;
    }
    else
    {
        return ret;
    }
}
