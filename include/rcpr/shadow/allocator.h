/**
 * \file rcpr/shadow/allocator.h
 *
 * \brief Shadow methods for allocation.
 *
 * Because these overrides "wrap" the standard allocators, they have a different
 * name that is substituted by the model checker header file.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <stddef.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

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
void* cbmc_malloc(size_t size);

/**
 * \brief Free a memory region previously allocated by cbmc_malloc.
 *
 * \note - this routine asserts that the pointer is not NULL.  If this assertion
 * can fail, then the model checker will report an error.
 */
void cbmc_free(void* ptr);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
