SET(MC_SOURCES
    ${CMAKE_SOURCE_DIR}/models/shadow/resource/prop_resource_valid.c
    ${CMAKE_SOURCE_DIR}/models/shadow/resource/resource_struct_tag_init.c
    ${CMAKE_SOURCE_DIR}/src/resource/resource_init.c
    ${CMAKE_SOURCE_DIR}/src/resource/resource_release.c
    main.c)

ADD_EXECUTABLE(model_resource_init_release ${MC_SOURCES})
SET_TARGET_PROPERTIES(
    model_resource_init_release PROPERTIES
    C_COMPILER_LAUNCHER "${COMPILER_CHOOSER};goto-cc"
    C_LINKER_LAUNCHER "${LINKER_CHOOSER};goto-ld")
TARGET_COMPILE_OPTIONS(
    model_resource_init_release
        PRIVATE ${CBMC_BUILD_OPTIONS})
SET_PROPERTY(
    TARGET model_resource_init_release
    PROPERTY JOB_POOL_LINK console)

ADD_CUSTOM_COMMAND(
    TARGET model_resource_init_release
    POST_BUILD
    COMMAND cbmc ${CBMC_OPTIONS} model_resource_init_release
    USES_TERMINAL)
