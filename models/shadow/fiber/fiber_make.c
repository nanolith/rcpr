#include <rcpr/fiber.h>
#include "../../../src/fiber/common/fiber_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_fiber_internal;

void RCPR_SYM(fiber_make)(
    fiber* fib, fiber_scheduler* sched, fiber_entry_fn entry)
{
    (void)fib;
    (void)sched;
    (void)entry;
}
