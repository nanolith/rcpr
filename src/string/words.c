/**
 * \file string/words.c
 *
 * \brief Get words from a string.
 *
 * \copyright 2022 Justin Handville.  Please see license.txt in this
 * distribution for the license terms under which this software is distributed.
 */

#include <rcpr/model_assert.h>
#include <rcpr/string.h>
#include <string.h>

RCPR_IMPORT_string_as(rcpr);

/**
 * \brief Initialize a string iterator to scan the given string for individual
 * words separated by one or more whitespace characters.
 *
 * During the first call, the first word is returned in \p word, and the \p
 * iterator argument is set up for subsequent calls. In the first call, \p str
 * should be set to the string to be scanned. This string will be modified by
 * this operation. During subsequent calls, \p str should be NULL; the
 * \p iterator argument will be used to extract subsequent words.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param word          Pointer to the character pointer to be set to the first
 *                      word on the first call or the next word on subsequent
 *                      calls. This word is a substring within the original
 *                      string, which is modified in this operation. It is a
 *                      substring of the original string and is NOT owned by the
 *                      caller.
 * \param iterator      The iterator to initialize for future calls if str is
 *                      NOT NULL or to use to get next words on subsequent
 *                      calls. The string iterator can be on the stack as it is
 *                      just a plain-old C structure. Its memory management is
 *                      up to the caller. This function only sets values in the
 *                      structure.
 * \param str           The string to scan for the first call or NULL for each
 *                      subsequent call.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_STRING_END_OF_INPUT when there are no more words to read.
 *      - a non-zero error code on failure.
 */
status FN_DECL_MUST_CHECK
RCPR_SYM(words)(
    const char** word, RCPR_SYM(string_iterator)* iterator, char* str)
{
    status retval;

    /* parameter sanity checks. */
    RCPR_MODEL_ASSERT(NULL != word);
    RCPR_MODEL_ASSERT(NULL != iterator);

    /* if str is set, then initialize the iterator. */
    if (NULL != str)
    {
        memset(iterator, 0, sizeof(*iterator));
        iterator->startpos = str;
        /* we don't use endpos or token for words. */
    }

    /* starting at startpos, skip all whitespace until either ASCIIZ or a
     * character. */
    for (int ch = *(iterator->startpos); ch != 0 && rcpr_is_whitespace(ch);
         ch = *(++(iterator->startpos)));

    /* if we are at ASCIIZ, then we've reached end of input. */
    if (0 == *(iterator->startpos))
    {
        retval = ERROR_STRING_END_OF_INPUT;
        goto done;
    }

    /* set word to this current position. */
    *word = iterator->startpos;

    /* starting at one plus startpos, skip all non-whitespace until we hit
     * whitespace or ASCIIZ. */
    for (int ch = *(++(iterator->startpos)); ch != 0 && !rcpr_is_whitespace(ch);
         ch = *(++(iterator->startpos)));

    /* if this position is not ASCIIZ, ASCIIZ it and increment startpos. */
    if (0 != *(iterator->startpos))
    {
        *(iterator->startpos) = 0;
        ++(iterator->startpos);
    }

    /* we've found a word. */
    retval = STATUS_SUCCESS;
    goto done;

done:
    return retval;
}
