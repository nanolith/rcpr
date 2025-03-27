/**
 * \file string/words.c
 *
 * \brief Shadow impl of words.
 *
 * \copyright 2022-2025 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>
#include <string.h>

RCPR_IMPORT_string_as(rcpr);

static int nondet_words_count();
static int words_count()
{
    int retval = nondet_words();
    if (retval < 0 || retval > 3)
        retval = 3;

    return retval;
}

status FN_DECL_MUST_CHECK
RCPR_SYM(words)(
    const char** word, RCPR_SYM(string_iterator)* iterator, char* str)
{
    RCPR_MODEL_CONTRACT_CHECK_PRECONDITIONS(
        RCPR_SYM(words), word, iterator, str);

    status retval;

    /* if str is set, then initialize the iterator. */
    if (NULL != str)
    {
        memset(iterator, 0, sizeof(*iterator));
        iterator->startpos = str;
        iterator->endpos = (char*)words_count();

        /* make sure that the first letter is a valid word. */
        RCPR_MODEL_ASSUME(rcpr_is_whitespace(*(iterator->startpos)));
    }

    int count = (int)iterator->endpos;
    if (0 == count || 0 == *(iterator->startpos))
    {
        retval = ERROR_STRING_END_OF_INPUT;
        *word = NULL;
        *iterator->startpos = 0;
        goto done;
    }
    else
    {
        iterator->endpos = (char*)(count-1);
        *word = iterator->startpos;
        retval = STATUS_SUCCESS;
        goto done;
    }

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(
        RCPR_SYM(words), retval, word, iterator, str);

    return retval;
}
