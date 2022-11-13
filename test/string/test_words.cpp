/**
 * \file test/string/test_words.cpp
 *
 * \brief Unit tests for RCPR words.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/string.h>
#include <string.h>

TEST_SUITE(string_words);

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_string_as(rcpr);

/**
 * Verify that we can perform words on an empty string.
 */
TEST(words_empty)
{
    allocator* alloc = nullptr;
    char* str = nullptr;
    const char* word = nullptr;
    rcpr_string_iterator iter;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, ""));

    /* perform words on this string. */
    TEST_ASSERT(ERROR_STRING_END_OF_INPUT == rcpr_words(&word, &iter, str));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can perform words on an all whitespace string.
 */
TEST(words_all_whitespace)
{
    allocator* alloc = nullptr;
    char* str = nullptr;
    const char* word = nullptr;
    rcpr_string_iterator iter;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "   \t\n\r\v   "));

    /* perform words on this string. */
    TEST_ASSERT(ERROR_STRING_END_OF_INPUT == rcpr_words(&word, &iter, str));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can get the first word from a sequence of words.
 */
TEST(word_sequence_1)
{
    allocator* alloc = nullptr;
    char* str = nullptr;
    const char* word = nullptr;
    rcpr_string_iterator iter;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(
        STATUS_SUCCESS == rcpr_strdup(&str, alloc, "one two three four"));

    /* perform words on this string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_words(&word, &iter, str));
    TEST_EXPECT(!strcmp(word, "one"));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can get all words from a sequence of words.
 */
TEST(word_sequence)
{
    allocator* alloc = nullptr;
    char* str = nullptr;
    const char* word = nullptr;
    rcpr_string_iterator iter;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(
        STATUS_SUCCESS == rcpr_strdup(&str, alloc, "one two three four"));

    /* perform words on this string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_words(&word, &iter, str));
    TEST_EXPECT(!strcmp(word, "one"));

    /* get the next word. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_words(&word, &iter, NULL));
    TEST_EXPECT(!strcmp(word, "two"));

    /* get the next word. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_words(&word, &iter, NULL));
    TEST_EXPECT(!strcmp(word, "three"));

    /* get the last word. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_words(&word, &iter, NULL));
    TEST_EXPECT(!strcmp(word, "four"));

    /* there are no more words, */
    TEST_ASSERT(ERROR_STRING_END_OF_INPUT == rcpr_words(&word, &iter, NULL));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can iterate through a sequence of words with multiple spaces
 * in between.
 */
TEST(word_sequence_multi_space_gaps)
{
    allocator* alloc = nullptr;
    char* str = nullptr;
    const char* word = nullptr;
    rcpr_string_iterator iter;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(
        STATUS_SUCCESS == rcpr_strdup(&str, alloc, "one\ttwo   three four   "));

    /* perform words on this string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_words(&word, &iter, str));
    TEST_EXPECT(!strcmp(word, "one"));

    /* get the next word. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_words(&word, &iter, NULL));
    TEST_EXPECT(!strcmp(word, "two"));

    /* get the next word. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_words(&word, &iter, NULL));
    TEST_EXPECT(!strcmp(word, "three"));

    /* get the last word. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_words(&word, &iter, NULL));
    TEST_EXPECT(!strcmp(word, "four"));

    /* there are no more words, */
    TEST_ASSERT(ERROR_STRING_END_OF_INPUT == rcpr_words(&word, &iter, NULL));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
