#include <rcpr/model_assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <sys/socket.h>

#include "descriptor.h"

bool nondet_bool();
uint8_t nondet_uint8();

int getsockopt(int s, int level, int optname, void* optval, socklen_t* optlen)
{
    RCPR_MODEL_ASSERT(prop_valid_range(optval, *optlen));

    /* verify descriptor. */
    if (NULL == descriptor_array[s])
    {
        return -1;
    }

    /* roll the dice: should we return an error? */
    if (nondet_bool())
    {
        return -1;
    }

    uint8_t* v = (uint8_t*)optval;
    if (*optlen >= 1)
        v[0] = nondet_uint8();
    if (*optlen >= 2)
        v[0] = nondet_uint8();
    if (*optlen >= 3)
        v[0] = nondet_uint8();
    if (*optlen >= 4)
        v[0] = nondet_uint8();

    if (*optlen >= 4)
        *optlen = 4;

    return 0;
}
