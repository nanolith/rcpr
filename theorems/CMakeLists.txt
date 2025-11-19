FILE(GLOB_RECURSE ROCQ_DATA_SOURCES Data/*.v)

FOREACH(source ${ROCQ_DATA_SOURCES})
    STRING(REPLACE "/" "_" TARGET_NAME "build_rocq_data_${source}")

    ADD_CUSTOM_COMMAND(
        OUTPUT ${source}o
        COMMAND coqc -R ${CMAKE_CURRENT_SOURCE_DIR}/Data Data ${source}
        DEPENDS ${source})

    ADD_CUSTOM_TARGET(
        ${TARGET_NAME} ALL
        DEPENDS ${source}o)
ENDFOREACH()
