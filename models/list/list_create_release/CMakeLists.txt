SET(MC_SOURCES
    ${CMAKE_SOURCE_DIR}/models/shadow/allocator/allocator_struct_tag_init.c
    ${CMAKE_SOURCE_DIR}/models/shadow/allocator/property_allocator_valid.c
    ${CMAKE_SOURCE_DIR}/models/shadow/list/list_struct_tag_init.c
    ${CMAKE_SOURCE_DIR}/models/shadow/list/property_list_valid.c
    ${CMAKE_SOURCE_DIR}/models/shadow/list/property_list_node_valid.c
    ${CMAKE_SOURCE_DIR}/models/shadow/resource/prop_resource_valid.c
    ${CMAKE_SOURCE_DIR}/models/shadow/resource/resource_struct_tag_init.c
    ${CMAKE_SOURCE_DIR}/src/allocator/allocator_allocate.c
    ${CMAKE_SOURCE_DIR}/src/allocator/allocator_reclaim.c
    ${CMAKE_SOURCE_DIR}/src/allocator/allocator_resource_handle.c
    ${CMAKE_SOURCE_DIR}/src/allocator/malloc_allocator_create.c
    ${CMAKE_SOURCE_DIR}/src/resource/resource_init.c
    ${CMAKE_SOURCE_DIR}/src/resource/resource_release.c
    ${CMAKE_SOURCE_DIR}/src/resource/resource_vtable_read.c
    ${CMAKE_SOURCE_DIR}/src/list/list_create.c
    ${CMAKE_SOURCE_DIR}/src/list/list_clear.c
    ${CMAKE_SOURCE_DIR}/src/list/list_resource_handle.c
    main.c)

ADD_EXECUTABLE(model_list_create_release ${MC_SOURCES})
SET_TARGET_PROPERTIES(
    model_list_create_release PROPERTIES
    C_COMPILER_LAUNCHER "${COMPILER_CHOOSER};goto-cc"
    C_LINKER_LAUNCHER "${LINKER_CHOOSER};goto-ld")
TARGET_COMPILE_OPTIONS(
    model_list_create_release
        PRIVATE ${CBMC_BUILD_OPTIONS})
SET_PROPERTY(
    TARGET model_list_create_release
    PROPERTY JOB_POOL_LINK console)

ADD_CUSTOM_COMMAND(
    TARGET model_list_create_release
    POST_BUILD
    COMMAND cbmc ${CBMC_OPTIONS} model_list_create_release
    USES_TERMINAL)
