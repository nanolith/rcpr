#include <rcpr/resource.h>
#include <rcpr/vtable.h>

RCPR_IMPORT_resource;

/* forward decls. */
void resource_struct_tag_init();
static int dummy_resource_release(resource* r);

RCPR_VTABLE
resource_vtable dummy_resource_vtable = {
    .release = &dummy_resource_release
};

int main(int argc, char* argv[])
{
    resource r;

    /* set up the global resource tag. */
    resource_struct_tag_init();

    /* initialize a dummy resource. */
    resource_init(&r, &dummy_resource_vtable);

    /* we should be able to release this resource. */
    RCPR_MODEL_ASSERT(STATUS_SUCCESS == resource_release(&r));

    return 0;
}

static int dummy_resource_release(resource* r)
{
    RCPR_MODEL_ASSERT(prop_resource_valid(r));

    return STATUS_SUCCESS;
}
