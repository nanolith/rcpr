/**
 * \file rcpr/resource.h
 *
 * \brief The resource interface provides a mechanism for describing resources
 * that can be released, reclaiming the underlying memory or external resources
 * associated with this interface.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/function_decl.h>
#include <rcpr/status.h>
#include <stdbool.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/* forward decls */
struct resource;

/**
 * \brief The resource interface describes an object that can be released by
 * calling \ref resource_release.
 */
typedef struct resource resource;

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

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
resource_release(resource* r);

/******************************************************************************/
/* Start of public types.                                                     */
/******************************************************************************/

/**
 * \brief Function type for resource release function.
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
 *      - ERROR_RESOURCE_TEMPORARY_FAILURE when a temporary failure prevents the
 *        resource from being released.  The user should attempt to release this
 *        resource again.
 *      - ERROR_RESOURCE_PERMANENT_FAILURE when a permanent failure prevents the
 *        resource from being released.  Additional attempts to release this
 *        resource would be futile, and this may indicate that the process
 *        should be restarted or terminated.
 */
typedef status (*resource_release_fn)(resource* r);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid resource property.
 *
 * \param r             The resource instance to be verified.
 *
 * \returns true if the resource instance is valid.
 */
bool prop_resource_valid(const resource* r);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
