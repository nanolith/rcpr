/**
 * \file rcpr/message.h
 *
 * \brief The RCPR fiber messaging interface.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/fiber.h>
#include <rcpr/fiber/disciplines/message.h>
#include <rcpr/function_decl.h>
#include <rcpr/status.h>
#include <rcpr/uuid.h>
#include <stdint.h>

/* C++ compatibility. */
# ifdef    __cplusplus
extern "C" {
# endif /* __cplusplus */

/**
 * \brief The message abstraction provides an envelope to which both a payload
 * and a return address can be attached.
 */
typedef struct RCPR_SYM(message) RCPR_SYM(message);

/**
 * \brief The mailbox address uniquely addresses a mailbox.
 */
typedef uint64_t RCPR_SYM(mailbox_address);

/**
 * \brief An unexpected message handler callback function.
 *
 * \param addr          The mailbox address to which or from which a message was
 *                      trying to be sent or received.
 * \param f             The fiber that received the unexpected message.
 * \param context       The context pointer for this handler.
 * \param write         This flag is set to true on a send, and is false on a
 *                      receive.
 * \param resume_id     The resume discipline id.
 * \param resume_event  The resume event that was received.
 * \param resume_param  The resume parameter that was received.
 *
 * The unexpected message handler is called when a send or receive receives an
 * unexpected resume event.  This allows for out-of-band messaging between
 * fibers using the messaging abstraction layer.  This handler should return the
 * status that is expected to be returned to the caller of the send/receive.  A
 * special return code, \ref ERROR_MESSAGE_SHOULD_RETRY, should be returned if
 * the messaging abstraction layer should resume receiving as before the
 * out-of-band message was received.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_MESSAGE_SHOULD_RETRY if the I/O abstraction layer should resume
 *        its previosu read/write operation.
 *      - a non-zero error code on failure which is bubbled up from the I/O
 *        abstraction layer read/write as if that was returned from the
 *        simulated read/write.
 */
typedef status (*RCPR_SYM(message_unexpected_handler_callback_fn))(
    RCPR_SYM(mailbox_address) addr, RCPR_SYM(fiber)* f, void* context,
    bool write, const rcpr_uuid* resume_id, int resume_event,
    void* resume_param);

/******************************************************************************/
/* Start of constructors.                                                     */
/******************************************************************************/

/**
 * \brief Create a \ref mailbox_address using the messaging discipline.
 *
 * \param addr          Pointer to the \ref mailbox_address value to receive
 *                      this address.
 * \param msgdisc       Pointer to the messaging discipline.
 *
 * \note This \ref mailbox_address is a unique value that references a mailbox
 * created by the messaging discipline.  This is an abstract resource that must
 * be released by calling \ref mailbox_close when it is no longer needed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(mailbox_create)(
    RCPR_SYM(mailbox_address)* addr,
    RCPR_SYM(fiber_scheduler_discipline)* msgdisc);

/**
 * \brief Create a \ref message with a return address and a resource payload.
 *
 * \param msg           Pointer to the \ref message pointer to receive this
 *                      resource.
 * \param alloc         The allocator to use to create this resource.
 * \param returnaddr    The return address for this message, or
 *                      MESSAGE_ADDRESS_NONE if there is no return address.
 * \param payload       The payload \ref resource for this message.
 *
 * \note This \ref message is a resource, which is owned by the caller on
 * success.  The caller is responsible to either release this resource by
 * calling \ref resource_release on its resource handle, or sending it to
 * a mailbox with \ref message_send.  The resource handle for this \ref message
 * can be obtained by calling \ref message_resource_handle.  The \p payload
 * given to this message is owned by this message on success.  It will be
 * released when the message is released.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(message_create)(
    RCPR_SYM(message)** msg, RCPR_SYM(allocator)* alloc,
    RCPR_SYM(mailbox_address) returnaddr, RCPR_SYM(resource)* payload);

/**
 * \brief Create or get the \ref fiber_scheduler_discipline for messaging.
 *
 * \param msgdisc       Pointer to the \ref fiber_scheduler_discipline pointer
 *                      to receive the messaging discipline.
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
RCPR_SYM(message_discipline_get_or_create)(
    RCPR_SYM(fiber_scheduler_discipline)** msgdisc, RCPR_SYM(allocator)* alloc,
    RCPR_SYM(fiber_scheduler)* sched);

/******************************************************************************/
/* Start of public methods.                                                   */
/******************************************************************************/

/**
 * \brief Close a \ref mailbox_address using the messaging discipline.
 *
 * \param addr          The \ref mailbox_address to close.
 * \param msgdisc       Pointer to the messaging discipline.
 *
 * \note The \ref mailbox_address pointed to by \p addr will be closed.  No
 * other messages can be sent to this address once it has been closed.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(mailbox_close)(
    RCPR_SYM(mailbox_address) addr,
    RCPR_SYM(fiber_scheduler_discipline)* msgdisc);

/**
 * \brief Send a \ref message to the given mailbox.
 *
 * \param sendaddr      The \ref mailbox_address to which this message should be
 *                      sent.
 * \param msg           The \ref message to send to this address.
 *
 * \note On success, the ownership of this \ref message is transferred to the
 * messaging discipline.  On failure, the ownership of this \ref message remains
 * with the caller.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(message_send)(
    RCPR_SYM(mailbox_address) sendaddr, RCPR_SYM(message)* msg);

/**
 * \brief Receive a \ref message from the mailbox.
 *
 * \param recvaddr      The \ref mailbox_address from which a message should be
 *                      received.
 * \param msg           Pointer to a \ref message pointer to receive a message.
 *
 * \note This call blocks until a message is available to receive, or until this
 * call is interrupted by an out-of-bound event.  On success, a \ref message is
 * available in \p msg.  This message is a resource that is owned by the caller
 * and must be released by calling \ref resource_release on its resource handle.
 * The resource handle for this \ref message can be obtained by calling
 * \ref message_resource_handle.  On failure, \p msg does not contain a valid
 * message.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(message_receive)(
    RCPR_SYM(mailbox_address) recvaddr, RCPR_SYM(message)** msg);

/******************************************************************************/
/* Start of accessors.                                                        */
/******************************************************************************/

/**
 * \brief Given a \ref message instance, return the resource handle for this
 * \ref message instance.
 *
 * \param msg           The \ref message instance from which the resource handle
 *                      is returned.
 *
 * \returns the \ref resource handle for this \ref message instance.
 */
RCPR_SYM(resource)*
RCPR_SYM(message_resource_handle)(
    RCPR_SYM(message)* msg);

/**
 * \brief Given a \ref message instance, return the return \ref mailbox_address
 * associated with it.
 *
 * \param msg           The \ref message instance from which the return \ref
 *                      mailbox_address is returned.
 *
 * \returns the return \ref mailbox_address or MESSAGE_ADDRESS_NONE if there is
 * not a return address.
 */
RCPR_SYM(mailbox_address)
RCPR_SYM(message_return_address)(
    const RCPR_SYM(message)* msg);

/**
 * \brief Given a \ref message instance, return the payload \ref resource
 * associated with it.
 *
 * \note The ownership of this resource remains with the message, unless the
 * boolean flag, \p xfer is set to true.
 *
 * \param msg           The \ref message instance from which the payload \ref
 *                      resource is returned.
 * \param xfer          If set to true, then ownership is transferred to the
 *                      caller, and the payload for this message is set to NULL
 *                      after it is returned to the caller.
 *
 * \returns the return payload \ref resource, or NULL if the payload \ref
 * resource is not set.
 */
RCPR_SYM(resource)*
RCPR_SYM(message_payload)(
    RCPR_SYM(message)* msg, bool xfer);

/******************************************************************************/
/* Start of model checking properties.                                        */
/******************************************************************************/

/**
 * \brief Valid \ref message property.
 *
 * \param msg           The \ref message instance to be verified.
 *
 * \returns true if the \ref message instance is valid.
 */
bool
RCPR_SYM(prop_message_valid)(
    const RCPR_SYM(message)* msg);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define RCPR_IMPORT_message_as(sym) \
    typedef RCPR_SYM(message) sym ## _ ## message; \
    typedef RCPR_SYM(mailbox_address) sym ## _ ## mailbox_address; \
    typedef RCPR_SYM(message_unexpected_handler_callback_fn) \
    sym ## _ ## message_unexpected_handler_callback_fn; \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## mailbox_create( \
        RCPR_SYM(mailbox_address)* x, \
        RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(mailbox_create)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## message_create( \
        RCPR_SYM(message)** w, RCPR_SYM(allocator)* x, \
        RCPR_SYM(mailbox_address) y, RCPR_SYM(resource)* z) { \
            return RCPR_SYM(message_create)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## message_discipline_get_or_create( \
        RCPR_SYM(fiber_scheduler_discipline)** x, RCPR_SYM(allocator)* y, \
        RCPR_SYM(fiber_scheduler)* z) { \
            return RCPR_SYM(message_discipline_get_or_create)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## mailbox_close( \
        RCPR_SYM(mailbox_address) x, RCPR_SYM(fiber_scheduler_discipline)* y) {\
            return RCPR_SYM(mailbox_close)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## message_send( \
        RCPR_SYM(mailbox_address) x, RCPR_SYM(message)* y) { \
            return RCPR_SYM(message_send)(x,y); } \
    static inline status FN_DECL_MUST_CHECK sym ## _ ## message_receive( \
        RCPR_SYM(mailbox_address) x, RCPR_SYM(message)** y) { \
            return RCPR_SYM(message_receive)(x,y); } \
    static inline RCPR_SYM(resource)* sym ## _ ## message_resource_handle( \
        RCPR_SYM(message)* x) { \
            return RCPR_SYM(message_resource_handle)(x); } \
    static inline RCPR_SYM(mailbox_address) \
    sym ## _ ## message_return_address( \
        const RCPR_SYM(message)* x) { \
            return RCPR_SYM(message_return_address)(x); } \
    static inline RCPR_SYM(resource)* sym ## _ ## message_payload( \
        RCPR_SYM(message)* x, bool y) { \
            return RCPR_SYM(message_payload)(x,y); } \
    static inline bool sym ## _ ## prop_message_valid( \
        const RCPR_SYM(message)* x) { \
            return RCPR_SYM(prop_message_valid)(x); }

#define RCPR_IMPORT_message \
    typedef RCPR_SYM(message) message; \
    typedef RCPR_SYM(mailbox_address) mailbox_address; \
    typedef RCPR_SYM(message_unexpected_handler_callback_fn) \
    message_unexpected_handler_callback_fn; \
    static inline status FN_DECL_MUST_CHECK mailbox_create( \
        RCPR_SYM(mailbox_address)* x, \
        RCPR_SYM(fiber_scheduler_discipline)* y) { \
            return RCPR_SYM(mailbox_create)(x,y); } \
    static inline status FN_DECL_MUST_CHECK message_create( \
        RCPR_SYM(message)** w, RCPR_SYM(allocator)* x, \
        RCPR_SYM(mailbox_address) y, RCPR_SYM(resource)* z) { \
            return RCPR_SYM(message_create)(w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK message_discipline_get_or_create( \
        RCPR_SYM(fiber_scheduler_discipline)** x, RCPR_SYM(allocator)* y, \
        RCPR_SYM(fiber_scheduler)* z) { \
            return RCPR_SYM(message_discipline_get_or_create)(x,y,z); } \
    static inline status FN_DECL_MUST_CHECK mailbox_close( \
        RCPR_SYM(mailbox_address) x, RCPR_SYM(fiber_scheduler_discipline)* y) {\
            return RCPR_SYM(mailbox_close)(x,y); } \
    static inline status FN_DECL_MUST_CHECK message_send( \
        RCPR_SYM(mailbox_address) x, RCPR_SYM(message)* y) { \
            return RCPR_SYM(message_send)(x,y); } \
    static inline status FN_DECL_MUST_CHECK message_receive( \
        RCPR_SYM(mailbox_address) x, RCPR_SYM(message)** y) { \
            return RCPR_SYM(message_receive)(x,y); } \
    static inline RCPR_SYM(resource)* message_resource_handle( \
        RCPR_SYM(message)* x) { \
            return RCPR_SYM(message_resource_handle)(x); } \
    static inline RCPR_SYM(mailbox_address) message_return_address( \
        const RCPR_SYM(message)* x) { \
            return RCPR_SYM(message_return_address)(x); } \
    static inline RCPR_SYM(resource)* message_payload( \
        RCPR_SYM(message)* x, bool y) { \
            return RCPR_SYM(message_payload)(x,y); } \
    static inline bool prop_message_valid( \
        const RCPR_SYM(message)* x) { \
            return RCPR_SYM(prop_message_valid)(x); }

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
