#include <rcpr/model_assert.h>
#include <string.h>

#include "../../../src/fiber/common/fiber_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_resource;

status RCPR_SYM(fiber_resource_release)(resource* r)
{
    status stack_retval, retval;
    fiber* fib = (fiber*)r;
    RCPR_MODEL_ASSERT(prop_fiber_valid(fib));

    /* cache the allocator. */
    allocator* a = fib->alloc;

    if (NULL != fib->st)
    {
        free(fib->st->region);
        free(fib->st);
    }

    /* reclaim the fiber structure. */
    free(fib);

    return STATUS_SUCCESS;
}
