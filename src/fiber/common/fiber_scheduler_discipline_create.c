/**
 * \file fiber/common/fiber_scheduler_discipline_create.c
 *
 * \brief Create a fiber scheduler discipline instance.
 *
 * \copyright 2021-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/vtable.h>
#include <string.h>

#include "fiber_internal.h"

RCPR_IMPORT_allocator;
RCPR_IMPORT_fiber;
RCPR_IMPORT_resource;
RCPR_IMPORT_uuid;

/* forward decls. */
static status fiber_scheduler_discipline_resource_release(resource*);

RCPR_MODEL_STRUCT_TAG_GLOBAL_EXTERN(fiber_scheduler_discipline);

/* the vtable entry for the fiber scheduler discipline instance. */
RCPR_VTABLE
resource_vtable fiber_scheduler_discipline_vtable = {
    &fiber_scheduler_discipline_resource_release };

/**
 * \brief Create a custom fiber scheduler discipline.
 *
 * \param disc              The pointer to the pointer to receive the created
 *                          discipline on success.
 * \param id                The id for this discipline.
 * \param alloc             The allocator to use to create this discipline.
 * \param context           User context for discipline callbacks.
 * \param callbacks         The number of callbacks supported in this
 *                          discipline.
 * \param callback_vector   The array of callbacks for this discipline.
 *
 * \note On success, this creates a new discipline instance which is owned by
 * the caller. When no longer needed, the caller should release the resource
 * associated with this discipline via \ref resource_release. The resource can
 * be obtained by calling \ref fiber_scheduler_discipline_resource_handle on
 * this instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p disc must not reference a valid \ref fiber_scheduler_discipline
 *        instance and must not be NULL.
 *      - \p id must be an id unique to this discipline family (e.g. unique for
 *        all fiber I/O discipline instances, or unique for all messaging
 *        discipline instances).
 *      - \p alloc must reference a valid \ref allocator and must not be NULL.
 *      - \p callbacks must be greater than zero.
 *      - \p callback_vector must have a number of entries matching \p
 *        callbacks.
 *
 * \post
 *      - On success, \p disc is set to a pointer to a valid discipline
 *        instance, which is a \ref resource owned by the caller that must be
 *        released when no longer needed.
 *      - On failure, \p sched is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(fiber_scheduler_discipline_create)(
    RCPR_SYM(fiber_scheduler_discipline)** disc, const RCPR_SYM(rcpr_uuid)* id,
    RCPR_SYM(allocator)* alloc, void* context, size_t callbacks,
    RCPR_SYM(fiber_scheduler_discipline_callback_fn)* callback_vector)
{
    fiber_scheduler_discipline* tmp;
    status retval, release_retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != disc);
    RCPR_MODEL_ASSERT(prop_uuid_valid(id));
    RCPR_MODEL_ASSERT(prop_allocator_valid(alloc));
    RCPR_MODEL_ASSERT(
        prop_valid_range(
            callback_vector,
            callbacks * sizeof(fiber_scheduler_discipline_callback_fn)));

    /* attempt to allocate memory for this fiber scheduler discipline. */
    retval =
        allocator_allocate(alloc, (void**)&tmp,
        sizeof(fiber_scheduler_discipline));
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto done;
    }

    /* clear the structure. */
    memset(tmp, 0, sizeof(fiber_scheduler_discipline));

    /* the tag is not set by default. */
    RCPR_MODEL_ASSERT_STRUCT_TAG_NOT_INITIALIZED(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(fiber_scheduler_discipline),
        fiber_scheduler_discipline);

    /* set the tag. */
    RCPR_MODEL_STRUCT_TAG_INIT(
        tmp->RCPR_MODEL_STRUCT_TAG_REF(fiber_scheduler_discipline),
        fiber_scheduler_discipline);

    /* set the release method. */
    resource_init(&tmp->hdr, &fiber_scheduler_discipline_vtable);

    /* attempt to allocate memory for the fiber scheduler callbacks. */
    retval =
        allocator_allocate(
            alloc, (void**)&tmp->callback_vector,
            callbacks * sizeof(fiber_scheduler_discipline_callback_fn));
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto reclaim_fiber_scheduler_discipline;
    }

    /* copy the vectors. */
    memcpy(
        tmp->callback_vector, callback_vector,
        callbacks * sizeof(fiber_scheduler_discipline_callback_fn));
    tmp->callback_vector_size = callbacks;

    /* attempt to allocate memory for the fiber scheduler callback codes. */
    retval =
        allocator_allocate(
            alloc, (void**)&tmp->callback_codes,
            callbacks * sizeof(uint32_t));
    if (STATUS_SUCCESS != retval)
    {
        retval = ERROR_GENERAL_OUT_OF_MEMORY;
        goto reclaim_fiber_scheduler_vector;
    }

    /* save the init values. */
    tmp->alloc = alloc;
    memcpy(&tmp->id, id, sizeof(tmp->id));
    tmp->sched = NULL;
    tmp->context = context;

    /* set the return pointer. */
    *disc = tmp;
    retval = STATUS_SUCCESS;

    /* verify that this structure is now valid. */
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(*disc));

    /* success. */
    goto done;

reclaim_fiber_scheduler_vector:
    release_retval = allocator_reclaim(alloc, tmp->callback_vector);
    if (STATUS_SUCCESS != release_retval)
    {
        return release_retval;
    }

reclaim_fiber_scheduler_discipline:
    release_retval = allocator_reclaim(alloc, tmp);
    if (STATUS_SUCCESS != release_retval)
    {
        return release_retval;
    }

done:
    return retval;
}

/**
 * \brief Release a \ref fiber_scheduler_discipline resource.
 *
 * \param r         The resource to release.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
static status fiber_scheduler_discipline_resource_release(resource* r)
{
    status vector_retval, codes_retval, disc_retval;
    fiber_scheduler_discipline* disc = (fiber_scheduler_discipline*)r;
    RCPR_MODEL_ASSERT(prop_fiber_scheduler_discipline_valid(disc));

    /* cache the allocator. */
    allocator* a = disc->alloc;

    /* reclaim up the vector. */
    vector_retval = allocator_reclaim(a, disc->callback_vector);

    /* reclaim the codes. */
    codes_retval = allocator_reclaim(a, disc->callback_codes);

    /* reclaim the discipline. */
    disc_retval = allocator_reclaim(a, disc);

    /* return a valid error code. */
    if (STATUS_SUCCESS != vector_retval)
    {
        return vector_retval;
    }
    else if (STATUS_SUCCESS != codes_retval)
    {
        return codes_retval;
    }
    else if (STATUS_SUCCESS != disc_retval)
    {
        return disc_retval;
    }
    else
    {
        return STATUS_SUCCESS;
    }
}
