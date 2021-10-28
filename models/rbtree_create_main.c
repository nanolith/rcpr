#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/rbtree.h>

RCPR_IMPORT_allocator;
RCPR_IMPORT_compare;
RCPR_IMPORT_rbtree;
RCPR_IMPORT_resource;

void allocator_struct_tag_init();
void rbtree_struct_tag_init();

/* dummy comparison. */
static rcpr_comparison_result dummy_compare(
    void* context, const void* lhs, const void* rhs)
{
    return RCPR_COMPARE_LT;
}

static const void* dummy_key(
    void* context, const resource* r)
{
    return r;
}

int main(int argc, char* argv[])
{
    allocator* alloc = NULL;
    rbtree* tree = NULL;
    int retval;

    /* set up the global allocator tag. */
    allocator_struct_tag_init();

    /* set up the global rbtree tag. */
    rbtree_struct_tag_init();

    /* try to create a malloc allocator. */
    retval = malloc_allocator_create(&alloc); 
    if (STATUS_SUCCESS != retval)
    {
        goto done;
    }

    /* create an rbtree instance. */
    retval = rbtree_create(&tree, alloc, &dummy_compare, &dummy_key, NULL);
    if (STATUS_SUCCESS != retval)
    {
        /* the only reason why it could fail is due to a memory issue. */
        RCPR_MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        goto cleanup_allocator;
    }

cleanup_rbtree:
    /* release the rbtree. */
    resource_release(rbtree_resource_handle(tree));

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
