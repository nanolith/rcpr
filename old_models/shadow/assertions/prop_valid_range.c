#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

bool prop_valid_range(const void* buf, size_t size)
{
    const uint8_t* bbuf = (const uint8_t*)buf;

    return
        size == 0 || ((bbuf[0] == bbuf[0]) && (bbuf[size-1] == bbuf[size-1]));
}
