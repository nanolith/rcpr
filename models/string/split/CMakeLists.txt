SET(MC_SOURCES
    ${CMAKE_SOURCE_DIR}/src/string/split.c
    main.c)

ADD_EXECUTABLE(model_string_split ${MC_SOURCES})
SET_TARGET_PROPERTIES(
    model_string_split PROPERTIES
    C_COMPILER_LAUNCHER "${COMPILER_CHOOSER};goto-cc"
    C_LINKER_LAUNCHER "${LINKER_CHOOSER};goto-ld")
TARGET_COMPILE_OPTIONS(
    model_string_split
        PRIVATE ${CBMC_BUILD_OPTIONS})
SET_PROPERTY(
    TARGET model_string_split
    PROPERTY JOB_POOL_LINK console)

ADD_CUSTOM_COMMAND(
    TARGET model_string_split
    POST_BUILD
    COMMAND cbmc ${CBMC_OPTIONS} model_string_split
    USES_TERMINAL)
