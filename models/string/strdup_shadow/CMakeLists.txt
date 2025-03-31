SET(MC_SOURCES
    ${CMAKE_SOURCE_DIR}/models/shadow/allocator/allocator_struct_tag_init.c
    ${CMAKE_SOURCE_DIR}/models/shadow/allocator/prop_allocator_valid.c
    ${CMAKE_SOURCE_DIR}/models/shadow/resource/resource_struct_tag_init.c
    ${CMAKE_SOURCE_DIR}/models/shadow/resource/prop_resource_valid.c
    ${CMAKE_SOURCE_DIR}/src/allocator/malloc_allocator_create.c
    ${CMAKE_SOURCE_DIR}/src/allocator/allocator_allocate.c
    ${CMAKE_SOURCE_DIR}/src/allocator/allocator_reclaim.c
    ${CMAKE_SOURCE_DIR}/src/allocator/allocator_resource_handle.c
    ${CMAKE_SOURCE_DIR}/src/resource/resource_init.c
    ${CMAKE_SOURCE_DIR}/src/resource/resource_release.c
    ${CMAKE_SOURCE_DIR}/src/resource/resource_vtable_read.c
    ${CMAKE_SOURCE_DIR}/models/shadow/string/strdup.c
    main.c)

ADD_EXECUTABLE(model_string_strdup_shadow ${MC_SOURCES})
SET_TARGET_PROPERTIES(
    model_string_strdup_shadow PROPERTIES
    C_COMPILER_LAUNCHER "${COMPILER_CHOOSER};goto-cc"
    C_LINKER_LAUNCHER "${LINKER_CHOOSER};goto-ld")
TARGET_COMPILE_OPTIONS(
    model_string_strdup_shadow
        PRIVATE ${CBMC_BUILD_OPTIONS})
SET_PROPERTY(
    TARGET model_string_strdup_shadow
    PROPERTY JOB_POOL_LINK console)

ADD_CUSTOM_COMMAND(
    TARGET model_string_strdup_shadow
    POST_BUILD
    COMMAND cbmc ${CBMC_OPTIONS} model_string_strdup_shadow
    USES_TERMINAL)
