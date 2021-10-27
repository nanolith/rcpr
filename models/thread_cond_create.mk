CBMC?=cbmc

ALL:
	$(CBMC) --bounds-check --pointer-check --memory-leak-check \
	--div-by-zero-check --pointer-overflow-check --trace --stop-on-fail -DCBMC \
	--drop-unused-functions \
	--unwind 10 --unwinding-assertions \
	--unwindset slist_release.0:4,slist_release:4,slist_node_release:2,resource_release:2 \
	-I ../include -I ../build/include \
	../models/shadow/allocator/allocator.c \
	../models/shadow/allocator/allocator_struct_tag_init.c \
	../models/shadow/allocator/prop_allocator_valid.c \
	../models/shadow/resource/prop_resource_valid.c \
	../models/shadow/resource/resource_struct_tag_init.c \
	../models/shadow/resource/mock_resource_create.c \
	../models/shadow/resource/mock_resource_release.c \
	../models/shadow/platform/pthread/thread/thread_cond_struct_tag_init.c \
	../models/shadow/platform/pthread/thread/prop_thread_cond_valid.c \
	../models/shadow/platform/pthread/pthread/pthread_cond_init.c \
	../models/shadow/platform/pthread/pthread/pthread_cond_destroy.c \
	../src/allocator/allocator_allocate.c \
	../src/allocator/allocator_reclaim.c \
	../src/allocator/allocator_resource_handle.c \
	../src/allocator/malloc_allocator_create.c \
	../src/resource/resource_release.c \
	../src/resource/resource_init.c \
	../src/platform/pthread/thread/thread_cond_resource_handle.c \
	../src/platform/pthread/thread/thread_cond_create.c \
	../models/thread_cond_create_main.c
