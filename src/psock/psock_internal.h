/**
 * \file psock/psock_internal.h
 *
 * \brief Internal data types and functions for psock.
 *
 * \copyright 2020 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#pragma once

#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/psock.h>
#include <rcpr/resource.h>

#include "../resource/resource_internal.h"

/* C++ compatibility. */
# ifdef   __cplusplus
extern "C" {
# endif /*__cplusplus*/

struct psock
{
    resource hdr;

    MODEL_STRUCT_TAG(psock);

    allocator* alloc;
    status (*read_fn)(psock* sock, void* data, size_t* size);
    status (*write_fn)(psock* sock, const void* data, size_t* size);
};

/* forward decls for psock_from_descriptor. */
struct psock_from_descriptor;
typedef struct psock_from_descriptor psock_from_descriptor;

struct psock_from_descriptor
{
    psock hdr;
    int descriptor;
};

/**
 * \brief Read data from the given \ref psock instance.
 *
 * \param sock          The \ref psock instance from which to read.
 * \param data          Pointer to the buffer into which data should be read.
 * \param size          Pointer to the size to read, updated with the size read.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status psock_from_descriptor_read(psock* sock, void* data, size_t* size);

/**
 * \brief Write data to the given \ref psock instance.
 *
 * \param sock          The \ref psock instance to which to write.
 * \param data          Pointer to the buffer from which data should be written.
 * \param size          Pointer to the size to write, updated with the size
 *                      written.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - an error code indicating a specific failure condition.
 */
status psock_from_descriptor_write(psock* sock, const void* data, size_t* size);

/* C++ compatibility. */
# ifdef   __cplusplus
}
# endif /*__cplusplus*/
