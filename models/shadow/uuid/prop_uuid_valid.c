/**
 * \file models/shadow/uuid/prop_uuid_valid.c
 *
 * \brief Check whether a uuid instance is valid.
 *
 * \copyright 2021 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/uuid.h>

RCPR_IMPORT_uuid;

/**
 * \brief Valid \ref rcpr_uuid property.
 *
 * \param id            The \ref rcpr_uuid instance to be verified.
 *
 * \returns true if the \ref rcpr_uuid instance is valid.
 */
bool RCPR_SYM(prop_uuid_valid)(const rcpr_uuid* id)
{
    RCPR_MODEL_ASSERT(NULL != id);
    RCPR_MODEL_ASSERT(prop_valid_range((const void*)id, sizeof(rcpr_uuid)));

    return true;
}
