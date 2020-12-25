#include <rcpr/model_assert.h>
#include <rcpr/byteswap.h>

int32_t byteswap32(int32_t val)
{
    uint32_t uval = (uint32_t)val;

    return (int32_t)
          ((uval & 0x000000FF) << 24)
        | ((uval & 0x0000FF00) <<  8)
        | ((uval & 0x00FF0000) >>  8)
        | ((uval & 0xFF000000) >> 24);
}
