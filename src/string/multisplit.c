/**
 * \file string/multisplit.c
 *
 * \brief Split a string into multiple sequences.
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
 * sequences separated by one or more occurrences of a token identified by the
 * given token function.
 *
 * This function works similarly to \ref words, except that the user can specify
 * a token matching function.
 *
 * During the first call, the first sequence is returned in \p seq, and the \p
 * iterator argument is set up for subsequent calls. In the first call, \p str
 * should be set to the string to be scanned. This string will be modified by
 * this operation. During subsequent calls, \p str should be NULL; the
 * \p iterator argument will be used to extract subsequent sequences.
 *
 * \note This operation modifies the provided string in-situ. This string must
 * be user-writable and heap allocated. This string must be ASCII-zero
 * terminated.
 *
 * \param seq           Pointer to the character pointer to be set to the first
 *                      sequence on the first call or the next sequence on
 *                      subsequent calls. This sequence is a substring within
 *                      the original string, which is modified in this
 *                      operation. It is a substring of the original string and
 *                      is NOT owned by the caller.
 * \param iterator      The iterator to initialize for future calls if str is
 *                      NOT NULL or to use to get the next seq on subsequent
 *                      calls. The string iterator can be on the stack as it is
 *                      just a plain-old C structure. Its memory management is
 *                      up to the caller. This function only sets values in the
 *                      structure.
 * \param str           The string to scan for the first call or NULL for each
 *                      subsequent call.
 * \param token_fn      A function that returns true when the given character is
 *                      a break token for individual sequences, and false
 *                      otherwise.
 *
 * \returns a status code indicating success or failure.
 *      - STATUS_SUCCESS on success.
 *      - ERROR_STRING_END_OF_INPUT when there are no more sequences to read.
 *      - a non-zero error code on failure.
 */
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
        /* we don't use endpos for multisplit. */
    }

    /* starting at startpos, skip all whitespace until either ASCIIZ or a
     * character. */
    for (int ch = *(iterator->startpos); ch != 0 && iterator->token_fn(ch);
         ch = *(++(iterator->startpos)));

    /* if we are at ASCIIZ, then we've reached end of input. */
    if (0 == *(iterator->startpos))
    {
        retval = ERROR_STRING_END_OF_INPUT;
        *seq = NULL;
        goto done;
    }

    /* set seq to this current position. */
    *seq = iterator->startpos;

    /* starting at one plus startpos, skip all non-whitespace until we hit
     * whitespace or ASCIIZ. */
    for (int ch = *(++(iterator->startpos)); ch != 0 && !iterator->token_fn(ch);
         ch = *(++(iterator->startpos)));

    /* if this position is not ASCIIZ, ASCIIZ it and increment startpos. */
    if (0 != *(iterator->startpos))
    {
        *(iterator->startpos) = 0;
        ++(iterator->startpos);
    }

    /* we've found a sequence. */
    retval = STATUS_SUCCESS;
    goto done;

done:
    RCPR_MODEL_CONTRACT_CHECK_POSTCONDITIONS(
        RCPR_SYM(multisplit), retval, seq, iterator);

    return retval;
}
