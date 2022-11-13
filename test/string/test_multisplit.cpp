/**
 * \file test/string/test_multisplit.cpp
 *
 * \brief Unit tests for RCPR multisplit.
 */

#include <minunit/minunit.h>
#include <rcpr/allocator.h>
#include <rcpr/string.h>
#include <string.h>

TEST_SUITE(string_multisplit);

RCPR_IMPORT_allocator;
RCPR_IMPORT_resource;
RCPR_IMPORT_string_as(rcpr);

/**
 * Verify that we can perform multisplit on an empty string.
 */
TEST(multisplit_empty)
{
    allocator* alloc = nullptr;
    char* str = nullptr;
    const char* word = nullptr;
    rcpr_string_iterator iter;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, ""));

    /* perform multisplit on this string. */
    TEST_ASSERT(
        ERROR_STRING_END_OF_INPUT
            == rcpr_multisplit(&word, &iter, str, &rcpr_is_whitespace));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can perform multisplit on an all whitespace string.
 */
TEST(multisplit_all_whitespace)
{
    allocator* alloc = nullptr;
    char* str = nullptr;
    const char* word = nullptr;
    rcpr_string_iterator iter;

    /* create malloc allocator. */
    TEST_ASSERT(STATUS_SUCCESS == malloc_allocator_create(&alloc));

    /* duplicate the test string. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_strdup(&str, alloc, "   \t\n\r\v   "));

    /* perform multisplit on this string. */
    TEST_ASSERT(
        ERROR_STRING_END_OF_INPUT
            == rcpr_multisplit(&word, &iter, str, &rcpr_is_whitespace));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can get the first word from a sequence of multisplit.
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

    /* perform multisplit on this string. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == rcpr_multisplit(&word, &iter, str, &rcpr_is_whitespace));
    TEST_EXPECT(!strcmp(word, "one"));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can get all multisplits from a string.
 */
TEST(multisplit_sequence)
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

    /* perform multisplit on this string. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == rcpr_multisplit(&word, &iter, str, &rcpr_is_whitespace));
    TEST_EXPECT(!strcmp(word, "one"));

    /* get the next word. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == rcpr_multisplit(&word, &iter, NULL, NULL));
    TEST_EXPECT(!strcmp(word, "two"));

    /* get the next word. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == rcpr_multisplit(&word, &iter, NULL, NULL));
    TEST_EXPECT(!strcmp(word, "three"));

    /* get the last word. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == rcpr_multisplit(&word, &iter, NULL, NULL));
    TEST_EXPECT(!strcmp(word, "four"));

    /* there are no more multisplit, */
    TEST_ASSERT(
        ERROR_STRING_END_OF_INPUT
            == rcpr_multisplit(&word, &iter, NULL, NULL));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}

/**
 * Verify that we can iterate through a sequence with multiple tokens in
 * between.
 */
TEST(multisplit_sequence_multi_space_gaps)
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

    /* perform multisplit on this string. */
    TEST_ASSERT(
        STATUS_SUCCESS
            == rcpr_multisplit(&word, &iter, str, &rcpr_is_whitespace));
    TEST_EXPECT(!strcmp(word, "one"));

    /* get the next word. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_multisplit(&word, &iter, NULL, NULL));
    TEST_EXPECT(!strcmp(word, "two"));

    /* get the next word. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_multisplit(&word, &iter, NULL, NULL));
    TEST_EXPECT(!strcmp(word, "three"));

    /* get the last word. */
    TEST_ASSERT(STATUS_SUCCESS == rcpr_multisplit(&word, &iter, NULL, NULL));
    TEST_EXPECT(!strcmp(word, "four"));

    /* there are no more multisplit, */
    TEST_ASSERT(
        ERROR_STRING_END_OF_INPUT == rcpr_multisplit(&word, &iter, NULL, NULL));

    /* clean up. */
    TEST_ASSERT(STATUS_SUCCESS == allocator_reclaim(alloc, str));
    TEST_ASSERT(
        STATUS_SUCCESS == resource_release(allocator_resource_handle(alloc)));
}
