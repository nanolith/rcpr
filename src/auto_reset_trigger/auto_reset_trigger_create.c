/**
 * \file auto_reset_trigger/auto_reset_trigger_create.c
 *
 * \brief Create an \ref auto_reset_trigger instance.
 *
 * \copyright 2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>
#include <string.h>

#include "auto_reset_trigger_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_auto_reset_trigger;
RCPR_IMPORT_resource;

/* forward decls. */
RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(auto_reset_trigger);
static status auto_reset_trigger_release(resource* r);

/* the vtable entry for auto_reset_trigger. */
RCPR_VTABLE
resource_vtable auto_reset_trigger_vtable = {
    &auto_reset_trigger_release
};

/**
 * \brief Create an \ref auto_reset_trigger that can accommodate a single
 * listener.
 *
 * An \ref auto_reset_trigger will notify its listener when signaled. After the
 * listener is notified, it is removed, and the trigger is reset. After
 * notification, the listener must register with the trigger again to receive a
 * future notification. If there is no registered listener when the trigger is
 * signaled, then it will remain in signaled mode until a listener registers, at
 * which point, it will receive the notification and the trigger will be reset.
 *
 * Notifications occur when the trigger is stepped. This two step process allows
 * any side-effects that must occur after registration to be ordered prior to
 * the notification occurring. One could imagine, for instance, that the
 * registration process writes a status to a client socket as does the
 * notification process. If notification happened immediately after
 * registration, this ordering would be broken. So, the correct ordering of
 * events would be to signal the trigger, then step it, or to register the
 * trigger, then step it. Between signal and step or register and step, there is
 * an opportunity for the caller to perform operations requiring strict
 * ordering.
 *
 * \param trigger       Pointer to the \ref auto_reset_trigger pointer to be set
 *                      to this instance on success.
 * \param alloc         The allocator to use for this operation.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(auto_reset_trigger_create)(
    RCPR_SYM(auto_reset_trigger)** trigger, RCPR_SYM(allocator)* alloc)
{
    status retval;
    auto_reset_trigger* tmp;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != trigger);
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));

    /* attempt to allocate memory for this auto_reset_trigger instance. */
    retval = allocator_allocate(alloc, (void**)&tmp, sizeof(*tmp));
    if (STATUS_SUCCESS != retval)
    {
        return retval;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(*tmp));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->hdr.RCPR_MODEL_STRUCT_TAG_REF(auto_reset_trigger), tmp);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        tmp->hdr.RCPR_MODEL_STRUCT_TAG_REF(auto_reset_trigger), tmp);

    /* set the vtable. */
    resource_init(&tmp->hdr, &auto_reset_trigger_vtable);

    /* set the allocator. */
    tmp->alloc = alloc;

    /* set the trigger. */
    *trigger = tmp;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_auto_reset_trigger_valid(tmp));

    /* success. */
    return STATUS_SUCCESS;
}

/**
 * \brief Release this trigger instance.
 *
 * \param r         the trigger resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status auto_reset_trigger_release(resource* r)
{
    auto_reset_trigger* trigger = (auto_reset_trigger*)r;

    RCPR_MODEL_ASSERT(prop_auto_reset_trigger_valid(trigger));

    /* cache allocator. */
    allocator* alloc = trigger->alloc;

    /* clear memory. */
    memset(trigger, 0, sizeof(*trigger));

    /* reclaim memory. */
    return allocator_reclaim(alloc, trigger);
}
