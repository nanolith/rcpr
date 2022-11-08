CBMC?=cbmc

ALL:
	$(CBMC) --bounds-check --pointer-check --memory-leak-check \
	--div-by-zero-check --pointer-overflow-check --trace --stop-on-fail -DCBMC \
	--drop-unused-functions \
	--unwind 10 --unwinding-assertions \
	--unwindset thread_start:1 \
	-I ../include -I ../build/include \
	../models/shadow/allocator/allocator.c \
	../models/shadow/allocator/allocator_struct_tag_init.c \
	../models/shadow/allocator/prop_allocator_valid.c \
	../models/shadow/resource/prop_resource_valid.c \
	../models/shadow/resource/resource_struct_tag_init.c \
	../models/shadow/resource/mock_resource_create.c \
	../models/shadow/resource/mock_resource_release.c \
	../models/shadow/platform/pthread/thread/thread_struct_tag_init.c \
	../models/shadow/platform/pthread/thread/prop_thread_valid.c \
	../models/shadow/platform/pthread/pthread/pthread_attr_init.c \
	../models/shadow/platform/pthread/pthread/pthread_attr_destroy.c \
	../models/shadow/platform/pthread/pthread/pthread_attr_setstacksize.c \
	../models/shadow/platform/pthread/pthread/pthread_create.c \
	../models/shadow/platform/pthread/pthread/pthread_join.c \
	../src/allocator/allocator_allocate.c \
	../src/allocator/allocator_reclaim.c \
	../src/allocator/allocator_resource_handle.c \
	../src/allocator/malloc_allocator_create.c \
	../src/resource/resource_release.c \
	../src/resource/resource_init.c \
	../src/platform/pthread/thread/thread_resource_handle.c \
	../src/platform/pthread/thread/thread_create.c \
	../models/thread_create_main.c
