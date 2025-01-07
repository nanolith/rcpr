/**
 * \file rcpr/byteswap.h
 *
 * \brief Define macros to perform byte swapping.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/config.h>

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/* CBMC shadow method equivalents. */
#if defined(CBMC)
#include <stdint.h>
int16_t byteswap16(int16_t);
int32_t byteswap32(int32_t);
int64_t byteswap64(int64_t);

/* Linux-specific byte swap utilities. */
#elif defined(__linux__)
#include <byteswap.h>
#define byteswap16(x) bswap_16((x))
#define byteswap32(x) bswap_32((x))
#define byteswap64(x) bswap_64((x))

/* OpenBSD-specific byte swap utilities. */
#elif defined(__OpenBSD__)
#include <sys/types.h>
#define byteswap16(x) swap16((x))
#define byteswap32(x) swap32((x))
#define byteswap64(x) swap64((x))

/* FreeBSD-specific byte swap utilities. */
#elif defined(__FreeBSD__)
#include <byteswap.h>
#define byteswap16(x) bswap_16(x)
#define byteswap32(x) bswap_32(x)
#define byteswap64(x) bswap_64(x)

/* MacOS-specific byte swap utilities. */
#elif defined(__RCPR_MACOS__)
#include <libkern/OSByteOrder.h>
#define byteswap16(x) OSSwapInt16((x))
#define byteswap32(x) OSSwapInt32((x))
#define byteswap64(x) OSSwapInt64((x))

/* end of platform-specific byte swap utilities. */
#endif

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
