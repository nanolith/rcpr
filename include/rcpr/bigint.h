/**
 * \file rcpr/bigint.h
 *
 * \brief Simple big integer math.
 *
 * This provides a simple brute-force big-integer math library.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/function_decl.h>
#include <rcpr/resource.h>
#include <rcpr/status.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/**
 * \brief The bigint type represents a large fixed point integer value.
 */
typedef struct RCPR_SYM(bigint) RCPR_SYM(bigint);

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

/**
 * \brief Create a \ref bigint instance of a given size.
 *
 * \param i             Pointer to the \ref bigint pointer to receive this
 *                      resource on success.
 * \param a             Pointer to the allocator to use for creating this \ref
 *                      bigint resource and to allocate new nodes.
 * \param size          The minimum size of this bigint in bits; the actual
 *                      representation might be larger to accomodate native
 *                      integer size.
 *
 * \note This \ref bigint is a \ref resource that must be released by calling
 * \ref resource_release on its resource handle when it is no longer needed by
 * the caller.  The resource handle can be accessed by calling
 * \ref bigint_resource_handle on this \ref bigint instance.
 *
 * This value will be the bigint equivalent of zero on success.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p i must not reference a valid \ref bigint instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *
 * \post
 *      - On success, \p i is set to a pointer to a valid \ref bigint
 *        instance, which is a \ref resource owned by the caller that must be
 *        released.
 *      - On failure, \p i is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(bigint_create_zero)(
    RCPR_SYM(bigint)** i, RCPR_SYM(allocator)* a, size_t size);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/**
 * \brief Clone a \ref bigint instance.
 *
 * \param i         Pointer to the \ref bigint pointer to receive the new
 *                  resource on success.
 * \param a         The allocator to use for cloning this instance.
 * \param j         The \ref bigint instance to clone.
 *
 * \note The cloned \ref bigint is a \ref resource that must be released by
 * calling \ref resource_release on its resource handle when it is no longer
 * needed by the caller.  The resource handle can be accessed by calling
 * \ref bigint_resource_handle on this \ref bigint instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_GENERAL_OUT_OF_MEMORY if this method failed due to an
 *        out-of-memory condition.
 *
 * \pre
 *      - \p i must not reference a valid \ref bigint instance and must not be
 *        NULL.
 *      - \p a must reference a valid \ref allocator and must not be NULL.
 *      - \p j must reference a valid \ref bigint instance.
 *
 * \post
 *      - On success, \p i is set to a pointer to a valid \ref bigint instance,
 *        which is a \ref resource owned by the called that must be released.
 *      - On failure, \p i is set to NULL and an error status is returned.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(bigint_clone)(
    RCPR_SYM(bigint)** i, RCPR_SYM(allocator)* a, const RCPR_SYM(bigint)* j);

/**
 * \brief Get the modulus of a bigint using an integer divisor.
 *
 * \param i         The \ref bigint instance to compute.
 * \param d         The integer divisor.
 *
 * \returns the integer result of this operation.
 */
int RCPR_SYM(bigint_modulus_int)(const RCPR_SYM(bigint)* i, int d);

/**
 * \brief Divide the bigint value by the given integer value.
 *
 * \param i         The \ref bigint value to divide.
 * \param d         The integer divisor.
 */
void RCPR_SYM(bigint_divide_int)(RCPR_SYM(bigint)* i, int d);

/******************************************************************************/
/* Start of accessors.                                                        */
/******************************************************************************/

/**
 * \brief Given a \ref bigint instance, return the resource handle for this
 * \ref bigint instance.
 *
 * \param i             The \ref bigint instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref bigint instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(bigint_resource_handle)(RCPR_SYM(bigint)* i);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref bigint property.
 *
 * \param i              The \ref bigint instance to be verified.
 *
 * \returns true if the \ref bigint instance is valid.
 */
bool RCPR_SYM(prop_bigint_valid)(const RCPR_SYM(bigint)* i);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/

#define RCPR_IMPORT_bigint_as(sym) \
    typedef RCPR_SYM(bigint) sym ## _ ## bigint; \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## bigint_create_zero( \
        RCPR_SYM(bigint)** x, RCPR_SYM(allocator)* y, size_t z) { \
            return RCPR_SYM(bigint_create_zero)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## bigint_clone( \
        RCPR_SYM(bigint)** x, RCPR_SYM(allocator)* y, \
        const RCPR_SYM(bigint)* z) { \
            return RCPR_SYM(bigint_clone)(x,y,z); } \
    static inline int sym ## _ ## bigint_modulus_int( \
        RCPR_SYM(bigint)* x, int y) { \
            return RCPR_SYM(bigint_modulus_int)(x,y); } \
    static inline void sym ## _ ## bigint_divide_int( \
        RCPR_SYM(bigint)* x, int y) { \
            RCPR_SYM(bigint_divide_int)(x,y); } \
    static inline RCPR_SYM(resource*) sym ## _ ## bigint_resource_handle( \
        RCPR_SYM(bigint)* x) { \
            return RCPR_SYM(bigint_resource_handle)(x); } \
    static inline bool sym ## _ ## prop_bigint_valid( \
        const RCPR_SYM(bigint)* x) { \
            return RCPR_SYM(prop_bigint_valid(x)); } \
    REQUIRE_SEMICOLON_HERE

#define RCPR_IMPORT_bigint \
    typedef RCPR_SYM(bigint) bigint; \
    static inline status FN_DECL_MUST_CHECK bigint_create_zero( \
        RCPR_SYM(bigint)** x, RCPR_SYM(allocator)* y, size_t z) { \
            return RCPR_SYM(bigint_create_zero)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK bigint_clone( \
        RCPR_SYM(bigint)** x, RCPR_SYM(allocator)* y, \
        const RCPR_SYM(bigint)* z) { \
            return RCPR_SYM(bigint_clone)(x,y,z); } \
    static inline int bigint_modulus_int( \
        RCPR_SYM(bigint)* x, int y) { \
            return RCPR_SYM(bigint_modulus_int)(x,y); } \
    static inline void bigint_divide_int( \
        RCPR_SYM(bigint)* x, int y) { \
            RCPR_SYM(bigint_divide_int)(x,y); } \
    static inline RCPR_SYM(resource*) bigint_resource_handle( \
        RCPR_SYM(bigint)* x) { \
            return RCPR_SYM(bigint_resource_handle)(x); } \
    static inline bool prop_bigint_valid( \
        const RCPR_SYM(bigint)* x) { \
            return RCPR_SYM(prop_bigint_valid(x)); } \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
