/**
 * \file socket_utilities/socket_utility_hton32.c
 *
 * \brief Utility function for converting a 32-bit integer from host to network
 * byte order.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/byteswap.h>
#include <rcpr/model_assert.h>
#include <rcpr/socket_utilities.h>

/**
 * \brief Convert a 32-bit integer value from host to network byte order.
 *
 * \param val               The value to convert.
 *
 * \returns the value in network byte order.
 */
int32_t socket_utility_hton32(int32_t val)
{
#ifdef __BIG_ENDIAN__
    return val;
#else
    return byteswap32(val);
#endif
}
