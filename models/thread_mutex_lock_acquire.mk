CBMC?=cbmc

ALL:
	$(CBMC) --bounds-check --pointer-check --memory-leak-check \
	--div-by-zero-check --pointer-overflow-check --trace --stop-on-fail -DCBMC \
	--drop-unused-functions \
	--unwind 10 --unwinding-assertions \
	-I ../include -I ../build/include \
	../models/shadow/allocator/allocator.c \
	../models/shadow/allocator/allocator_struct_tag_init.c \
	../models/shadow/allocator/prop_allocator_valid.c \
	../models/shadow/resource/prop_resource_valid.c \
	../models/shadow/resource/resource_struct_tag_init.c \
	../models/shadow/resource/mock_resource_create.c \
	../models/shadow/resource/mock_resource_release.c \
	../models/shadow/platform/pthread/thread/thread_mutex_struct_tag_init.c \
	../models/shadow/platform/pthread/thread/thread_mutex_lock_struct_tag_init.c \
	../models/shadow/platform/pthread/thread/prop_thread_mutex_valid.c \
	../models/shadow/platform/pthread/thread/prop_thread_mutex_lock_valid.c \
	../models/shadow/platform/pthread/pthread/pthread_mutex_init.c \
	../models/shadow/platform/pthread/pthread/pthread_mutex_destroy.c \
	../models/shadow/platform/pthread/pthread/pthread_mutex_lock.c \
	../models/shadow/platform/pthread/pthread/pthread_mutex_unlock.c \
	../src/allocator/allocator_allocate.c \
	../src/allocator/allocator_reclaim.c \
	../src/allocator/allocator_resource_handle.c \
	../src/allocator/malloc_allocator_create.c \
	../src/resource/resource_release.c \
	../src/resource/resource_init.c \
	../src/platform/pthread/thread/thread_mutex_resource_handle.c \
	../src/platform/pthread/thread/thread_mutex_lock_resource_handle.c \
	../src/platform/pthread/thread/thread_mutex_create.c \
	../src/platform/pthread/thread/thread_mutex_lock_acquire.c \
	../models/thread_mutex_lock_acquire_main.c
