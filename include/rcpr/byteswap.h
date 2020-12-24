/**
 * \file rcpr/byteswap.h
 *
 * \brief Define macros to perform byte swapping.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

/* Linux-specific byte swap utilities. */
#if defined(__Linux__)
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

/* end of platform-specific byte swap utilities. */
#endif

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
