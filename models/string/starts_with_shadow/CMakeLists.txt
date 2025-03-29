SET(MC_SOURCES
    ${CMAKE_SOURCE_DIR}/models/shadow/string/starts_with.c
    main.c)

ADD_EXECUTABLE(model_string_starts_with_shadow ${MC_SOURCES})
SET_TARGET_PROPERTIES(
    model_string_starts_with_shadow PROPERTIES
    C_COMPILER_LAUNCHER "${COMPILER_CHOOSER};goto-cc"
    C_LINKER_LAUNCHER "${LINKER_CHOOSER};goto-ld")
TARGET_COMPILE_OPTIONS(
    model_string_starts_with_shadow
        PRIVATE ${CBMC_BUILD_OPTIONS})
SET_PROPERTY(
    TARGET model_string_starts_with_shadow
    PROPERTY JOB_POOL_LINK console)

ADD_CUSTOM_COMMAND(
    TARGET model_string_starts_with_shadow
    POST_BUILD
    COMMAND cbmc ${CBMC_OPTIONS} model_string_starts_with_shadow
    USES_TERMINAL)
