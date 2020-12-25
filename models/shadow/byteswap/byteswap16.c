#include <rcpr/model_assert.h>
#include <rcpr/byteswap.h>

int16_t byteswap16(int16_t val)
{
    uint16_t uval = (uint16_t)val;

    return (int16_t)
          ((uval & 0x00FF) << 8)
        | ((uval & 0xFF00) >> 8);
}
