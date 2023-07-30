/**
 * \file stack/stack_create.c
 *
 * \brief Create a stack that can be used in a fiber or process.
 *
 * \copyright 2021-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#include "stack_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_stack;

/* forward decls. */
static status stack_release(resource*);

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(stack);

/* the vtable entry for the stack instance. */
RCPR_VTABLE
resource_vtable stack_vtable = {
    &stack_release };

/**
 * \brief Create a \ref stack of at least the given size.
 *
 * \param st            Pointer to the \ref stack pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      stack resource.
 * \param stack_size    The size of the stack in bytes.
 *
 * \note This \ref stack is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref stack_resource_handle on this \ref stack instance.  The stack must not
 * be in use by any \ref fiber or other process when it is released, or
 * undefined behavior can occur.  It is up to the caller to ensure that the
 * stack is not in use.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p st must not reference a valid \ref stack instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p stack_size must be greater than zero and must follow platform rules
 *        for creating a stack.
 *
 * \post
 *      - On success, \p stack is set to a pointer to a valid \ref stack
 *        instance, which is a \ref resource owned by the caller that must be
 *        released by the caller when no longer needed.
 *      - On failure, \p stack is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(stack_create)(
    RCPR_SYM(stack)** st, RCPR_SYM(allocator)* a, size_t stack_size)
{
    status retval, reclaim_retval;
    void* mem;
    stack* tmp = NULL;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != st);
    RCPR_MODEL_ASSERT(prop_allocator_valid(a));
    RCPR_MODEL_ASSERT(stack_size > 0);

    /* attempt to allocate memory for this stack. */
    retval = allocator_allocate(a, (void**)&tmp, sizeof(stack));
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto done;
    }

    /* clear structure. */
    memset(tmp, 0, sizeof(stack));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(stack), stack);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(tmp->RCPR_MODEL_STRUCT_TAG_REF(stack), stack);

    /* set the release method. */
    resource_init(&tmp->hdr, &stack_vtable);

    /* save the init values. */
    tmp->alloc = a;
    tmp->size = stack_size;

    /* Allocate memory for the stack. */
    mem = mmap(
        NULL, stack_size,
        PROT_WRITE | PROT_READ, MAP_PRIVATE | MAP_ANONYMOUS | MAP_STACK,
        -1, 0);
    if (MAP_FAILED == mem)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto free_stack;
    }

    /* set the region. */
    tmp->region = mem;

    /* Set the return pointer. */
    *st = tmp;
    retval = STATUS_SUCCESS;

    /* verify that this stack is now valid. */
    RCPR_MODEL_ASSERT(prop_stack_valid(*st));

    /* success. */ 
    goto done;

free_stack:
    memset(tmp, 0, sizeof(stack));
    reclaim_retval = allocator_reclaim(a, tmp);
    if (STATUS_SUCCESS != reclaim_retval)
        retval = reclaim_retval;

done:
    return retval;
}

/**
 * \brief Release a stack instance, joining it.
 *
 * \param r         The stack resource to release.
 *
 * \returns a status code indicating success or failure.
 */
static status stack_release(resource* r)
{
    status retval;
    stack* st = (stack*)r;
    RCPR_MODEL_ASSERT(prop_stack_valid(st));

    /* cache the allocator. */
    allocator* a = st->alloc;

    /* unmap the stack. */
    retval = munmap(st->region, st->size);
    if (retval < 0)
    {
        return ERROR_STACK_UNMAP;
    }

    /* clear the stack structure. */
    RCPR_MODEL_EXEMPT(memset(st, 0, sizeof(stack)));

    /* reclaim the stack structure. */
    return allocator_reclaim(a, st);
}
