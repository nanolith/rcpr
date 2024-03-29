/**
 * \file socket_utilities/socket_utility_ntoh16.c
 *
 * \brief Utility function for converting a 16-bit integer from network to host
 * byte order.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/byteswap.h>
#include <rcpr/model_assert.h>
#include <rcpr/socket_utilities.h>

/**
 * \brief Convert a 16-bit integer value from network to host byte order.
 *
 * \param val               The value to convert.
 *
 * \returns the value in host byte order.
 */
int16_t
RCPR_SYM(socket_utility_ntoh16)(
    int16_t val)
{
#ifdef __BIG_ENDIAN__
    return val;
#else
    return byteswap16(val);
#endif
}
