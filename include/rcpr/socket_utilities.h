/**
 * \file rcpr/socket_utilities.h
 *
 * \brief Some utility functions to make working with sockets easier.
 *
 * \copyright 2020-2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/function_decl.h>
#include <rcpr/status.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/**
 * \brief Create a socket pair, with the given domain, type, and protocol.
 *
 * \param domain            The domain for this socket pair.
 * \param type              The type of this socket pair.
 * \param protocol          The protocol for this socket pair.
 * \param left              A pointer to be set to the file descriptor for the
 *                          left side of this socket pair.
 * \param right             A pointer to be set to the file descriptor for the
 *                          right side of this socket pair.
 *
 * On success, left and right are set to the left and right sides of the created
 * socket pair.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a failure code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(socket_utility_socketpair)(
    int domain, int type, int protocol, int* left, int* right);

/**
 * \brief Set a descriptor to non-blocking.
 *
 * \param desc              The descriptor to set to non-blocking.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - a failure code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(socket_utility_set_nonblock)(
    int desc);

/**
 * \brief Convert a 64-bit integer value from host to network byte order.
 *
 * \param val               The value to convert.
 *
 * \returns the value in network byte order.
 */
int64_t
RCPR_SYM(socket_utility_hton64)(
    int64_t val);

/**
 * \brief Convert a 64-bit integer value from network to host byte order.
 *
 * \param val               The value to convert.
 *
 * \returns the value in host byte order.
 */
int64_t
RCPR_SYM(socket_utility_ntoh64)(
    int64_t val);

/**
 * \brief Convert a 32-bit integer value from host to network byte order.
 *
 * \param val               The value to convert.
 *
 * \returns the value in network byte order.
 */
int32_t
RCPR_SYM(socket_utility_hton32)(
    int32_t val);

/**
 * \brief Convert a 32-bit integer value from network to host byte order.
 *
 * \param val               The value to convert.
 *
 * \returns the value in host byte order.
 */
int32_t
RCPR_SYM(socket_utility_ntoh32)(
    int32_t val);

/**
 * \brief Convert a 16-bit integer value from host to network byte order.
 *
 * \param val               The value to convert.
 *
 * \returns the value in network byte order.
 */
int16_t
RCPR_SYM(socket_utility_hton16)(
    int16_t val);

/**
 * \brief Convert a 16-bit integer value from network to host byte order.
 *
 * \param val               The value to convert.
 *
 * \returns the value in host byte order.
 */
int16_t
RCPR_SYM(socket_utility_ntoh16)(
    int16_t val);

/******************************************************************************/
/* Start of public exports.                                                   */
/******************************************************************************/
#define RCPR_IMPORT_socket_utilities_as(sym) \
    _Pragma("GCC diagnostic push") \
    _Pragma("GCC diagnostic ignored \"-Wunused-function\"") \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## socket_utility_socketpair( \
        int v, int w, int x, int* y, int* z) { \
            return RCPR_SYM(socket_utility_socketpair)(v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK \
    sym ## _ ## socket_utility_set_nonblock( \
        int x) { \
            return RCPR_SYM(socket_utility_set_nonblock)(x); } \
    static inline int64_t sym ## _ ## socket_utility_hton64( \
        int64_t x) { \
            return RCPR_SYM(socket_utility_hton64)(x); } \
    static inline int64_t sym ## _ ## socket_utility_ntoh64( \
        int64_t x) { \
            return RCPR_SYM(socket_utility_ntoh64)(x); } \
    static inline int32_t sym ## _ ## socket_utility_hton32( \
        int32_t x) { \
            return RCPR_SYM(socket_utility_hton32)(x); } \
    static inline int32_t sym ## _ ## socket_utility_ntoh32( \
        int32_t x) { \
            return RCPR_SYM(socket_utility_ntoh32)(x); } \
    static inline int16_t sym ## _ ## socket_utility_hton16( \
        int16_t x) { \
            return RCPR_SYM(socket_utility_hton16)(x); } \
    static inline int16_t sym ## _ ## socket_utility_ntoh16( \
        int16_t x) { \
            return RCPR_SYM(socket_utility_ntoh16)(x); } \
    _Pragma("GCC diagnostic pop") \
    REQUIRE_SEMICOLON_HERE

#define RCPR_IMPORT_socket_utilities \
    _Pragma("GCC diagnostic push") \
    _Pragma("GCC diagnostic ignored \"-Wunused-function\"") \
    static inline status FN_DECL_MUST_CHECK socket_utility_socketpair( \
        int v, int w, int x, int* y, int* z) { \
            return RCPR_SYM(socket_utility_socketpair)(v,w,x,y,z); } \
    static inline status FN_DECL_MUST_CHECK socket_utility_set_nonblock( \
        int x) { \
            return RCPR_SYM(socket_utility_set_nonblock)(x); } \
    static inline int64_t socket_utility_hton64( \
        int64_t x) { \
            return RCPR_SYM(socket_utility_hton64)(x); } \
    static inline int64_t socket_utility_ntoh64( \
        int64_t x) { \
            return RCPR_SYM(socket_utility_ntoh64)(x); } \
    static inline int32_t socket_utility_hton32( \
        int32_t x) { \
            return RCPR_SYM(socket_utility_hton32)(x); } \
    static inline int32_t socket_utility_ntoh32( \
        int32_t x) { \
            return RCPR_SYM(socket_utility_ntoh32)(x); } \
    static inline int16_t socket_utility_hton16( \
        int16_t x) { \
            return RCPR_SYM(socket_utility_hton16)(x); } \
    static inline int16_t socket_utility_ntoh16( \
        int16_t x) { \
            return RCPR_SYM(socket_utility_ntoh16)(x); } \
    _Pragma("GCC diagnostic pop") \
    REQUIRE_SEMICOLON_HERE

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
