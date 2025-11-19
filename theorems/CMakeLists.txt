FILE(GLOB_RECURSE ROCQ_DATA_SOURCES Data/*.v)
FILE(GLOB_RECURSE ROCQ_BASE_THEOREM_SOURCES Theorems/*.v)

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

FOREACH(source ${ROCQ_BASE_THEOREM_SOURCES})
    STRING(REPLACE "/" "_" TARGET_NAME "build_rocq_base_theorem_${source}")

    ADD_CUSTOM_COMMAND(
        OUTPUT ${source}o
        COMMAND coqc -R ${CMAKE_CURRENT_SOURCE_DIR}/Theorems Theorems ${source}
        DEPENDS ${source})

    ADD_CUSTOM_TARGET(
        ${TARGET_NAME} ALL
        DEPENDS ${source}o)
ENDFOREACH()
