#include <rcpr/allocator.h>
#include <rcpr/model_assert.h>
#include <rcpr/resource.h>
#include <rcpr/rbtree.h>

#include "../src/rbtree/rbtree_internal.h"

MODEL_STRUCT_TAG_GLOBAL_EXTERN(rbtree_node);
void allocator_struct_tag_init();
void rbtree_struct_tag_init();
void rbtree_node_struct_tag_init();

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

static const dummy_rbtree_node_resource_release(resource* r)
{
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

    /* set up the global rbtree_node tag. */
    rbtree_node_struct_tag_init();

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
        MODEL_ASSERT(ERROR_GENERAL_OUT_OF_MEMORY == retval);

        goto cleanup_allocator;
    }

    rbtree_node parent;
    rbtree_node x;
    rbtree_node y;
    rbtree_node alpha;
    rbtree_node beta;
    rbtree_node gamma;

    /* PRECONDITIONS, as per Cormen et al figure 13.2... */
    tree->root = &parent;
    resource_init(&parent.hdr, &dummy_rbtree_node_resource_release);
    MODEL_STRUCT_TAG_INIT(
        parent.MODEL_STRUCT_TAG_REF(rbtree_node), rbtree_node);
    parent.parent = tree->nil;
    parent.left = tree->nil;
    parent.right = &y;
    parent.value = &tree->hdr;
    resource_init(&x.hdr, &dummy_rbtree_node_resource_release);
    MODEL_STRUCT_TAG_INIT(x.MODEL_STRUCT_TAG_REF(rbtree_node), rbtree_node);
    x.parent = &y;
    x.left = &alpha;
    x.right = &beta;
    x.value = &tree->hdr;
    resource_init(&y.hdr, &dummy_rbtree_node_resource_release);
    MODEL_STRUCT_TAG_INIT(y.MODEL_STRUCT_TAG_REF(rbtree_node), rbtree_node);
    y.parent = &parent;
    y.left = &x;
    y.right = &gamma;
    y.value = &tree->hdr;
    resource_init(&alpha.hdr, &dummy_rbtree_node_resource_release);
    MODEL_STRUCT_TAG_INIT(alpha.MODEL_STRUCT_TAG_REF(rbtree_node), rbtree_node);
    alpha.parent = &x;
    alpha.left = tree->nil;
    alpha.right = tree->nil;
    alpha.value = &tree->hdr;
    resource_init(&beta.hdr, &dummy_rbtree_node_resource_release);
    MODEL_STRUCT_TAG_INIT(beta.MODEL_STRUCT_TAG_REF(rbtree_node), rbtree_node);
    beta.parent = &x;
    beta.left = tree->nil;
    beta.right = tree->nil;
    beta.value = &tree->hdr;
    resource_init(&gamma.hdr, &dummy_rbtree_node_resource_release);
    MODEL_STRUCT_TAG_INIT(gamma.MODEL_STRUCT_TAG_REF(rbtree_node), rbtree_node);
    gamma.parent = &y;
    gamma.left = tree->nil;
    gamma.right = tree->nil;
    gamma.value = &tree->hdr;

    rbtree_right_rotate(tree, &y);

    /* before cleaning up rbtree, set the root to nil. */
    tree->root = tree->nil;

cleanup_rbtree:
    /* release the rbtree. */
    resource_release(rbtree_resource_handle(tree));

cleanup_allocator:
    /* release the allocator. */
    resource_release(allocator_resource_handle(alloc));

done:
    return 0;
}
