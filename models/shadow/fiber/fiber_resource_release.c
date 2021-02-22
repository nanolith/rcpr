#include <rcpr/model_assert.h>
#include <string.h>

#include "../../../src/fiber/common/fiber_internal.h"

status fiber_resource_release(resource* r)
{
    status stack_retval, retval;
    fiber* fib = (fiber*)r;
    MODEL_ASSERT(prop_fiber_valid(fib));

    /* cache the allocator. */
    allocator* a = fib->alloc;

    /* reclaim the fiber structure. */
    free(fib);

    return STATUS_SUCCESS;
}
