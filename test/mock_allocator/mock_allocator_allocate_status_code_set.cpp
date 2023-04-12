/**
 * \file test/mock_allocator/mock_allocator_allocate_status_code_set.c
 *
 * \brief Set the status code for allocater / reallocate operations.
 *
 * \copyright 2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include "../../src/allocator/allocator_internal.h"
#include "mock_allocator.h"

RCPR_IMPORT_mock_allocator;

/**
 * \brief Change the return status for an allocate / reallocate call.
 *
 * If the return status is a failing (non-zero / STATUS_SUCCESS) status, then
 * this status is returned instead of performing the wrapped operation. However,
 * if the return status is zero / STATUS_SUCCESS, then the wrapped malloc
 * allocator is called instead, and its return status is returned to the caller.
 * This allows the caller to simulate error conditions during memory allocation.
 *
 * \param alloc         The mock allocator instance to modify.
 * \param status_code   The status code to return on allocate / reallocate.
 *
 * \pre \p alloc must be a valid \ref allocator instance created as a mock
 * allocator.
 *
 * \post On success, the return status for \p alloc is modified for allocate and
 * reallocate operations.
 */
void
RCPR_SYM(mock_allocator_allocate_status_code_set)(
    RCPR_SYM(allocator)* alloc, status status_code)
{
    mock_allocator_context* ctx = (mock_allocator_context*)alloc->context;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));
    RCPR_MODEL_ASSERT(prop_mock_allocator_context_valid(ctx));

    /* set the status code. */
    ctx->allocate_status = status_code;
}
