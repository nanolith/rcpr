CBMC?=cbmc

ALL:
	$(CBMC) --bounds-check --pointer-check --memory-leak-check \
	--div-by-zero-check --pointer-overflow-check --trace --stop-on-fail -DCBMC \
	--drop-unused-functions \
	--unwind 10 --unwinding-assertions \
    --unwindset list_release.0:1,list_release:1,prop_rbtree_node_valid:1,rbtree_delete_nodes:2,rcpr_u0ec71e88_25af_40aa_8dd9_990d596b60de_V0_2_rbtree_delete_nodes:2 \
	-I ../include -I ../build/include \
	../models/shadow/allocator/allocator.c \
	../models/shadow/allocator/allocator_struct_tag_init.c \
	../models/shadow/allocator/prop_allocator_valid.c \
	../models/shadow/rbtree/prop_rbtree_valid.c \
	../models/shadow/rbtree/prop_rbtree_node_valid.c \
	../models/shadow/rbtree/rbtree_struct_tag_init.c \
	../models/shadow/resource/prop_resource_valid.c \
	../models/shadow/resource/resource_struct_tag_init.c \
	../models/shadow/resource/mock_resource_release.c \
	../src/allocator/allocator_allocate.c \
	../src/allocator/allocator_reclaim.c \
	../src/allocator/allocator_resource_handle.c \
	../src/allocator/malloc_allocator_create.c \
	../src/rbtree/rbtree_create.c \
	../src/rbtree/rbtree_delete_nodes.c \
	../src/rbtree/rbtree_resource_handle.c \
	../src/rbtree/rbtree_node_resource_handle.c \
	../src/resource/resource_release.c \
	../src/resource/resource_init.c \
	../models/rbtree_create_main.c
