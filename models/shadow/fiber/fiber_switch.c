#include <rcpr/model_assert.h>

#include "../../../src/fiber/common/fiber_internal.h"

RCPR_IMPORT_fiber;
RCPR_IMPORT_uuid;

/**
 * \brief Assembler routine to switch between two fibers.
 *
 * \param prev      The previous (current) fiber.
 * \param next      The next (switching) fiber.
 * \param event     The resume event to give to the next fiber.
 * \param param     The resume parameter to give to the next fiber.
 */
void RCPR_SYM(fiber_switch)(
    fiber* prev, fiber* next, const rcpr_uuid* disc, int64_t event, void *param)
{
    RCPR_MODEL_ASSERT(prop_fiber_valid(prev));
    RCPR_MODEL_ASSERT(prop_fiber_valid(next));

    next->restore_reason_code = event;
    next->restore_param = param;
}
