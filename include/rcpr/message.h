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
#include <rcpr/fiber/disciplines/messaging.h>
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
typedef struct message message;

/**
 * \brief The mailbox address uniquely addresses a mailbox.
 */
typedef uint64_t mailbox_address;

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
typedef status (*message_unexpected_handler_callback_fn)(
    mailbox_address addr, fiber* f, void* context, bool write,
    const rcpr_uuid* resume_id, int resume_event, void* resume_param);

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
mailbox_create(mailbox_address* addr, fiber_scheduler_discipline* msgdisc);

/**
 * \brief Create a \ref message with a return address and a resource payload.
 *
 * \param msg           Pointer to the \ref message pointer to receive this
 *                      resource.
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
message_create(message** msg, mailbox_address returnaddr, resource* payload);

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
mailbox_create(mailbox_address* addr, fiber_scheduler_discipline* msgdisc);

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
message_send(mailbox_address sendaddr, message* msg);

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
message_receive(mailbox_address recvaddr, message** msg);

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
resource*
message_resource_handle(message* msg);

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
mailbox_address
message_return_address(const message* msg);

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
resource*
message_payload(message* msg, bool xfer);

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
bool prop_message_valid(const message* msg);

/* C++ compatibility. */
# ifdef    __cplusplus
}
# endif /* __cplusplus */
