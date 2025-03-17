/**
 * \file rcpr/resource.h
 *
 * \brief The resource interface provides a mechanism for describing resources
 * that can be released, reclaiming the underlying memory or external resources
 * associated with this interface.
 *
 * \copyright 2020-2023 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/function_contracts.h>
#include <rcpr/function_decl.h>
#include <rcpr/model_assert.h>
#include <rcpr/status.h>
#include <stdbool.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/* forward decls */
struct RCPR_SYM(resource);

/**
 * \brief The resource interface describes an object that can be released by
 * calling \ref resource_release.
 */
typedef struct RCPR_SYM(resource) RCPR_SYM(resource);

/**
 * \brief The resource vtable describes the virtual methods used by a resource
 * instance.
 */
typedef struct RCPR_SYM(resource_vtable) RCPR_SYM(resource_vtable);

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
bool
RCPR_SYM(prop_resource_valid)(
    const RCPR_SYM(resource)* r);

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
RCPR_SYM(resource_release)(
    RCPR_SYM(resource)* r);

/* preconditions. */
RCPR_MODEL_CONTRACT_PRECONDITIONS_BEGIN(
    RCPR_SYM(resource_release),
    RCPR_SYM(resource)* r)
        /* this must be a valid resource. */
        RCPR_MODEL_ASSERT(RCPR_SYM(prop_resource_valid)(r));
RCPR_MODEL_CONTRACT_PRECONDITIONS_END(RCPR_SYM(resource_release))

/* postconditions. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_BEGIN(
    RCPR_SYM(resource_release), int retval)
        /* TODO - restrict allowed status codes. */
RCPR_MODEL_CONTRACT_POSTCONDITIONS_END(RCPR_SYM(resource_release))

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
typedef status (*RCPR_SYM(resource_release_fn))(RCPR_SYM(resource)* r);

/**
 * \brief The definition of the resource vtable used for defining resource
 * instances.
 */
struct RCPR_SYM(resource_vtable)
{
    RCPR_SYM(resource_release_fn) release;
};

/******************************************************************************/
/* Start of protected methods.                                                */
/******************************************************************************/

/**
 * \brief Initialize a resource with the given resource vtable.
 *
 * \param r         The resource to be initialized.
 * \param vtable    The resource vtable to use for this resource.
 */
void
RCPR_SYM(resource_init)(
    RCPR_SYM(resource)* r, const RCPR_SYM(resource_vtable)* vtable);

/**
 * \brief Access the vtable associated with this resource.
 *
 * \param vtable    Pointer to the vtable pointer to set on success.
 * \param r         The resource.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_BAD_VTABLE if the vtable for this instance is invalid.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(resource_vtable_read)(
    const RCPR_SYM(resource_vtable)** vtable, const RCPR_SYM(resource)* r);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define __INTERNAL_RCPR_IMPORT_resource_sym(sym) \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(resource) sym ## resource; \
    typedef RCPR_SYM(resource_vtable) sym ## resource_vtable; \
    typedef RCPR_SYM(resource_release_fn) sym ## resource_release_fn; \
    static inline status sym ## resource_release(\
        RCPR_SYM(resource)* x) { \
            return RCPR_SYM(resource_release)(x); } \
    static inline void sym ## resource_init(\
        RCPR_SYM(resource)* x, const RCPR_SYM(resource_vtable)* y) { \
            RCPR_SYM(resource_init)(x, y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## resource_vtable_read( \
        const RCPR_SYM(resource_vtable)** x, const RCPR_SYM(resource)* y) { \
            return RCPR_SYM(resource_vtable_read)(x,y); } \
    static inline bool sym ## prop_resource_valid(\
        const RCPR_SYM(resource)* x) { \
            return RCPR_SYM(prop_resource_valid)(x); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE
#define RCPR_IMPORT_resource_as(sym) \
    __INTERNAL_RCPR_IMPORT_resource_sym(sym ## _)
#define RCPR_IMPORT_resource \
    __INTERNAL_RCPR_IMPORT_resource_sym()

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
