#include <rcpr/model_assert.h>
#include <rcpr/shadow/valid_range.h>
#include <stdint.h>
#include <sys/socket.h>
#include <unistd.h>

#include "descriptor.h"

int accept(int s, struct sockaddr* addr, socklen_t* addrlen)
{
    /* TODO - fill out. */
    RCPR_MODEL_ASSERT(false);

    return -1;
}
