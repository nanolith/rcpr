/**
 * \file string/multisplit.c
 *
 * \brief Shadow implementation of multisplit.
 *
 * \copyright 2022-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>
#include <string.h>

RCPR_IMPORT_string_as(rcpr);

static int nondet_splits_count();
static int splits_count()
{
    int retval = nondet_splits_count();
    if (retval < 0 || retval > 3)
        retval = 3;

    return retval;
}

status FN_DECL_MUST_CHECK
RCPR_SYM(multisplit)(
    const char** seq, RCPR_SYM(string_iterator)* iterator, char* str,
    bool (*token_fn)(int))
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(
        RCPR_SYM(multisplit), seq, iterator, str, token_fn);

    status retval;

    /* if str is set, then initialize the iterator. */
    if (NULL != str)
    {
        memset(iterator, 0, sizeof(*iterator));
        iterator->startpos = str;
        iterator->token_fn = token_fn;
        iterator->endpos = (char*)splits_count();

        /* make sure that the first letter is not a token match. */
        RCPR_MODEL_ASSUME(!token_fn(token_fn(*(iterator->startpos))));
    }

    int count = (int)iterator->endpos;
    if (0 == count || 0 == *(iterator->startpos))
    {
        retval = ERROR_STRING_END_OF_INPUT;
        *seq = NULL;
        *iterator->startpos = 0;
        goto done;
    }
    else
    {
        iterator->endpos = (char*)(count-1);
        *seq = iterator->startpos;
        retval = STATUS_SUCCESS;
        goto done;
    }

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(
        RCPR_SYM(multisplit), retval, seq, iterator);

    return retval;
}
