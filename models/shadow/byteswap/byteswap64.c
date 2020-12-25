#include <rcpr/model_assert.h>
#include <rcpr/byteswap.h>

int64_t byteswap64(int64_t val)
{
    uint64_t uval = (uint64_t)val;

    return (uint64_t)
          ((uval & 0x00000000000000FF) << 56)
        | ((uval & 0x000000000000FF00) << 40)
        | ((uval & 0x0000000000FF0000) << 16)
        | ((uval & 0x00000000FF000000) <<  8)
        | ((uval & 0x000000FF00000000) >>  8)
        | ((uval & 0x0000FF0000000000) >> 16)
        | ((uval & 0x00FF000000000000) >> 40)
        | ((uval & 0xFF00000000000000) >> 56);
}
