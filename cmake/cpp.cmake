include(CheckCXXCompilerFlag)

check_cxx_compiler_flag("-std=c++20" HAS_CXX_20_SUPPORT)
check_cxx_compiler_flag("-std=c++2a" HAS_CXX_2A_SUPPORT)

if (HAS_CXX_20_SUPPORT)
    SET(STD_CXX_20 "-std=c++20")
elseif (HAS_CXX_2A_SUPPORT)
    SET(STD_CXX_20 "-std=c++2a")
else ()
    MESSAGE(FATAL_ERROR "RCPR unit tests require C++20 or C++2A support.")
endif ()
