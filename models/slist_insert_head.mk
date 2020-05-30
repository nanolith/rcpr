CBMC?=cbmc

ALL:
	$(CBMC) --bounds-check --pointer-check --memory-leak-check \
	--div-by-zero-check --pointer-overflow-check --trace --stop-on-fail -DCBMC \
	--drop-unused-functions \
	--unwind 10 --unwinding-assertions \
	--unwindset slist_release.0:3,slist_release:3,slist_node_release:2,resource_release:2 \
	-I ../include \
	../models/shadow/allocator/allocator.c \
	../models/shadow/allocator/allocator_struct_tag_init.c \
	../models/shadow/allocator/prop_allocator_valid.c \
	../models/shadow/slist/prop_slist_valid.c \
	../models/shadow/slist/prop_slist_node_valid.c \
    ../models/shadow/slist/slist_node_cleanup.c \
    ../models/shadow/slist/slist_node_release.c \
	../models/shadow/slist/slist_node_struct_tag_init.c \
	../models/shadow/slist/slist_struct_tag_init.c \
	../models/shadow/resource/prop_resource_valid.c \
	../models/shadow/resource/resource_struct_tag_init.c \
	../models/shadow/resource/mock_resource_create.c \
	../models/shadow/resource/mock_resource_release.c \
	../src/allocator/allocator_allocate.c \
	../src/allocator/allocator_reclaim.c \
	../src/allocator/allocator_resource_handle.c \
	../src/allocator/malloc_allocator_create.c \
	../src/slist/slist_create.c \
	../src/slist/slist_head.c \
	../src/slist/slist_insert_head.c \
    ../src/slist/slist_node_create.c \
	../src/slist/slist_node_resource_handle.c \
	../src/slist/slist_resource_handle.c \
	../src/slist/slist_tail.c \
	../src/resource/resource_release.c \
	../src/resource/resource_init.c \
	../models/slist_insert_head_main.c
