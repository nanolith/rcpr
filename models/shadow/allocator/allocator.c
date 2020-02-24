/**
 * \file models/shadow/allocator/allocator.c
 *
 * \brief Overrides of the allocator methods for model checking.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#define CBMC_NO_MALLOC_OVERRIDE
#include <rcpr/model_assert.h>
#include <stdlib.h>
#include <stdbool.h>

bool nondet_bool();

/**
 * \brief A shadow method of \ref malloc() that can fail nondeterministically.
 *
 * \param size      The size of the memory region to allocate.
 *
 * \returns a pointer to a newly allocated memory region of the given size, or
 *          NULL if allocation fails.
 *
 * \post On success, a pointer to a newly allocated memory region of the given
 * size is returned; on failure, NULL is returned.
 */
void* cbmc_malloc(size_t size)
{
    if (nondet_bool())
    {
        return malloc(size);
    }
    else
    {
        return NULL;
    }
}

/**
 * \brief Free a memory region previously allocated by cbmc_malloc.
 *
 * \note - this routine asserts that the pointer is not NULL.  If this assertion
 * can fail, then the model checker will report an error.
 */
void cbmc_free(void* ptr)
{
    MODEL_ASSERT(NULL != ptr);
    free(ptr);
}
