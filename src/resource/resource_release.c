/**
 * \file resource/resource_release.c
 *
 * \brief Release the given resource.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>

#include "resource_internal.h"

/**
 * \brief Release a resource back to the system or API from which it was
 * acquired.
 *
 * \param r         The resource to be released.
 *
 * Upon successful execution of this function, the ownership of this resource is
 * relinquished to the system or API from which it was acquired.  From this
 * point forward, the resource should not be used.  If this function fails to
 * release this resource, then it is still owned by the caller or by the
 * previous ownership context.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_RESOURCE_INAPPROPRIATE_RELEASE when it is inappropriate to
 *        release this resource, such as a singleton or global resource.
 *      - ERROR_RESOURCE_INVALID when the resource passed to this function may
 *        be invalid.
 *      - RCPR_ERROR_RESOURCE_TEMPORARY_FAILURE when a temporary failure
 *        prevents the resource from being released.  The user should attempt to
 *        release this resource again.
 *      - RCPR_ERROR_RESOURCE_PERMANENT_FAILURE when a permanent failure
 *        prevents the resource from being released.  Additional attempts to
 *        release this resource would be futile, and this may indicate that the
 *        process should be restarted or terminated.
 *
 * \pre \p r is a valid resource that can be released.
 *
 * \post on success, \p is released to the system or API from which it was
 * acquired.  This resource can no longer be used.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(resource_release)(RCPR_SYM(resource)* r)
{
    MODEL_ASSERT(prop_resource_valid(r));

    return r->release(r);
}
