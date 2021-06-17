/**
 * \file socket_utilities/socket_utility_hton16.c
 *
 * \brief Utility function for converting a 16-bit integer from host to network
 * byte order.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/byteswap.h>
#include <rcpr/model_assert.h>
#include <rcpr/socket_utilities.h>

/**
 * \brief Convert a 16-bit integer value from host to network byte order.
 *
 * \param val               The value to convert.
 *
 * \returns the value in network byte order.
 */
int16_t
RCPR_SYM(socket_utility_hton16)(
    int16_t val)
{
#ifdef __BIG_ENDIAN__
    return val;
#else
    return byteswap16(val);
#endif
}
