/**
 * \file models/shadow/prop_valid_range.c
 *
 * \brief Check memory access of the given pointer.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <stdint.h>

bool prop_valid_range(void* arr, size_t size)
{
    uint8_t* barr = (uint8_t*)arr;

    barr[0] = barr[0];
    barr[size - 1] = barr[size - 1];

    return
           (barr[0] == barr[0])
        || (barr[size - 1] == barr[size - 1]);
}
