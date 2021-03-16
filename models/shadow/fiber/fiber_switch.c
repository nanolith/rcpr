#include <rcpr/model_assert.h>

#include "../../../src/fiber/common/fiber_internal.h"

/**
 * \brief Assembler routine to switch between two fibers.
 *
 * \param prev      The previous (current) fiber.
 * \param next      The next (switching) fiber.
 * \param event     The resume event to give to the next fiber.
 * \param param     The resume parameter to give to the next fiber.
 */
void fiber_switch(
    fiber* prev, fiber* next, int64_t event, void *param)
{
    MODEL_ASSERT(prop_fiber_valid(prev));
    MODEL_ASSERT(prop_fiber_valid(next));

    next->restore_reason_code = event;
    next->restore_param = param;
}
