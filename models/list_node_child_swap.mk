CBMC?=cbmc

ALL:
	$(CBMC) --bounds-check --pointer-check --memory-leak-check \
	--div-by-zero-check --pointer-overflow-check --trace --stop-on-fail -DCBMC \
	--drop-unused-functions \
	--unwind 10 --unwinding-assertions \
	--unwindset list_release.0:3,list_release:3,list_node_release:2,resource_release:2 \
	-I ../include -I ../build/include \
	../models/shadow/allocator/allocator.c \
	../models/shadow/allocator/allocator_struct_tag_init.c \
	../models/shadow/allocator/prop_allocator_valid.c \
	../models/shadow/list/prop_list_valid.c \
	../models/shadow/list/prop_list_node_valid.c \
    ../models/shadow/list/list_node_cleanup.c \
    ../models/shadow/list/list_node_release.c \
	../models/shadow/list/list_node_struct_tag_init.c \
	../models/shadow/list/list_struct_tag_init.c \
	../models/shadow/resource/prop_resource_valid.c \
	../models/shadow/resource/resource_struct_tag_init.c \
	../models/shadow/resource/mock_resource_create.c \
	../models/shadow/resource/mock_resource_release.c \
	../src/allocator/allocator_allocate.c \
	../src/allocator/allocator_reclaim.c \
	../src/allocator/allocator_resource_handle.c \
	../src/allocator/malloc_allocator_create.c \
	../src/list/list_append_tail.c \
	../src/list/list_node_child_swap.c \
	../src/list/list_create.c \
	../src/list/list_head.c \
    ../src/list/list_node_create.c \
	../src/list/list_node_resource_handle.c \
	../src/list/list_resource_handle.c \
	../src/list/list_tail.c \
	../src/resource/resource_release.c \
	../src/resource/resource_init.c \
	../models/list_node_child_swap_main.c
