/**
 * \file rcpr/condition.h
 *
 * \brief The RCPR fiber condition interface.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <rcpr/fiber/disciplines/condition.h>
#include <rcpr/function_decl.h>
#include <rcpr/status.h>
#include <rcpr/uuid.h>
#include <stdint.h>

/* C++ compatibility. */
# ifdef    __cplusplus
extern "C" {
# endif /* __cplusplus */

/**
 * \brief The conditional handle.
 */
typedef uint64_t RCPR_SYM(conditional);

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

/**
 * \brief Create a \ref conditional using the condition discipline.
 *
 * \param handle        Pointer to the \ref conditional handle to receive
 *                      this new instance handle.
 * \param condisc       Pointer to the condition discipline.
 *
 * \note This \ref conditional is a unique handle that references a condition
 * barrier created by the condition discipline.  This is an abstract resource
 * that must be released by calling \ref conditional_close when it is no longer
 * needed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(conditional_create)(
    RCPR_SYM(conditional)* handle,
    RCPR_SYM(fiber_scheduler_discipline)* condisc);

/**
 * \brief Create or get the condition \ref fiber_scheduler_discipline.
 *
 * \param condisc       Pointer to the \ref fiber_scheduler_discipline pointer
 *                      to receive the condition discipline.
 * \param alloc         The \ref allocator instance to use to create this
 *                      discipline if it does not already exist.
 * \param sched         The \ref fiber_scheduler from which this discipline is
 *                      either looked up or to which it is added.
 *
 * \note If the discipline does not already exist in the provided
 * \ref fiber_scheduler, it is created and added.  The discipline is owned by
 * the \p sched instance and NOT by the caller.  The lifetime for this
 * discipline is the lifetime of the \p sched instance.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(condition_discipline_get_or_create)(
    RCPR_SYM(fiber_scheduler_discipline)** condisc, RCPR_SYM(allocator)* alloc,
    RCPR_SYM(fiber_scheduler)* sched);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/**
 * \brief Close a \ref conditional handle using the condition discipline.
 *
 * \param handle        The \ref conditional handle to close.
 * \param condisc       Pointer to the condition discipline.
 *
 * \note The \ref conditional handle pointed to by \p handle will be closed.  No
 * other fibers can wait or notify using this handle once it has been closed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(conditional_close)(
    RCPR_SYM(conditional) handle,
    RCPR_SYM(fiber_scheduler_discipline)* condisc);

/**
 * \brief Wait on a \ref conditional.
 *
 * \param handle        The \ref conditional handle on which to wait.
 * \param condisc       Pointer to the condition discipline.
 *
 * \note This fiber will be suspended until it is notified on this conditional.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(conditional_wait)(
    RCPR_SYM(conditional) handle,
    RCPR_SYM(fiber_scheduler_discipline)* condisc);

/**
 * \brief Notify one fiber waiting on a \ref conditional to resume.
 *
 * \param handle        The \ref conditional handle.
 * \param condisc       Pointer to the condition discipline.
 *
 * \note This fiber will resume AFTER the notified fiber.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(conditional_notify_one)(
    RCPR_SYM(conditional) handle,
    RCPR_SYM(fiber_scheduler_discipline)* condisc);

/**
 * \brief Notify all fibers waiting on a \ref conditional to resume.
 *
 * \param handle        The \ref conditional handle.
 * \param condisc       Pointer to the condition discipline.
 *
 * \note This fiber will resume AFTER the notified fiber.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(conditional_notify_all)(
    RCPR_SYM(conditional) handle,
    RCPR_SYM(fiber_scheduler_discipline)* condisc);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define RCPR_IMPORT_condition_as(sym) \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(conditional) sym ## _ ## conditional; \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## conditional_create( \
        RCPR_SYM(conditional)* x, \
        RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(conditional_create)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## condition_discipline_get_or_create( \
        RCPR_SYM(fiber_scheduler_discipline)** x, RCPR_SYM(allocator)* y, \
        RCPR_SYM(fiber_scheduler)* z) { \
            return RCPR_SYM(condition_discipline_get_or_create)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## conditional_close( \
        RCPR_SYM(conditional) x, RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(conditional_close)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## conditional_wait( \
        RCPR_SYM(conditional) x, RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(conditional_wait)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## conditional_notify_one( \
        RCPR_SYM(conditional) x, RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(conditional_notify_one)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## conditional_notify_all( \
        RCPR_SYM(conditional) x, RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(conditional_notify_all)(x,y); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE

#define RCPR_IMPORT_condition \
    RCPR_BEGIN_EXPORT \
    typedef RCPR_SYM(conditional) conditional; \
    static inline status FN_DECL_MUST_CHECK conditional_create( \
        RCPR_SYM(conditional)* x, \
        RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(conditional_create)(x,y); } \
    static inline status FN_DECL_MUST_CHECK \
    condition_discipline_get_or_create( \
        RCPR_SYM(fiber_scheduler_discipline)** x, RCPR_SYM(allocator)* y, \
        RCPR_SYM(fiber_scheduler)* z) { \
            return RCPR_SYM(condition_discipline_get_or_create)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK conditional_close( \
        RCPR_SYM(conditional) x, RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(conditional_close)(x,y); } \
    static inline status FN_DECL_MUST_CHECK conditional_wait( \
        RCPR_SYM(conditional) x, RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(conditional_wait)(x,y); } \
    static inline status FN_DECL_MUST_CHECK conditional_notify_one( \
        RCPR_SYM(conditional) x, RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(conditional_notify_one)(x,y); } \
    static inline status FN_DECL_MUST_CHECK conditional_notify_all( \
        RCPR_SYM(conditional) x, RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(conditional_notify_all)(x,y); } \
    RCPR_END_EXPORT \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
