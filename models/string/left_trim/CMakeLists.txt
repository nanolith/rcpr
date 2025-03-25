SET(MC_SOURCES
    ${CMAKE_SOURCE_DIR}/src/string/is_whitespace.c
    ${CMAKE_SOURCE_DIR}/src/string/left_trim.c
    main.c)

ADD_EXECUTABLE(model_string_left_trim ${MC_SOURCES})
SET_TARGET_PROPERTIES(
    model_string_left_trim PROPERTIES
    C_COMPILER_LAUNCHER "${COMPILER_CHOOSER};goto-cc"
    C_LINKER_LAUNCHER "${LINKER_CHOOSER};goto-ld")
TARGET_COMPILE_OPTIONS(
    model_string_left_trim
        PRIVATE ${CBMC_BUILD_OPTIONS})
SET_PROPERTY(
    TARGET model_string_left_trim
    PROPERTY JOB_POOL_LINK console)

ADD_CUSTOM_COMMAND(
    TARGET model_string_left_trim
    POST_BUILD
    COMMAND cbmc ${CBMC_OPTIONS} model_string_left_trim
    USES_TERMINAL)
