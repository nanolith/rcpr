#include <rcpr/model_assert.h>
#include <stdbool.h>

#include "descriptor.h"

bool nondet_bool();

int socketpair(int domain, int type, int protocol, int sv[2])
{
    /* range check of descriptor allocation. */
    if (curr_descriptor + 1 > MAX_DESCRIPTORS)
    {
        return -1;
    }

    /* roll the dice: should we return an error? */
    if (nondet_bool())
    {
        return -1;
    }

    /* attempt to allocate the first descriptor. */
    descriptor_array[curr_descriptor] = (int*)malloc(sizeof(int));
    if (NULL == descriptor_array[curr_descriptor])
    {
        return -1;
    }

    /* attempt to allocate the second descriptor. */
    descriptor_array[curr_descriptor + 1] = (int*)malloc(sizeof(int));
    if (NULL == descriptor_array[curr_descriptor + 1])
    {
        free(descriptor_array[curr_descriptor]);
        descriptor_array[curr_descriptor] = NULL;
        return -1;
    }

    /* both descriptors are allocated.  Set them. */
    sv[0] = *descriptor_array[curr_descriptor] = curr_descriptor;
    sv[1] = *descriptor_array[curr_descriptor + 1] = curr_descriptor + 1;
    curr_descriptor += 2;

    /* success. */
    return 0;
}
