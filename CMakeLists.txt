cmake_minimum_required(VERSION 3.24.1)
project(aha_project)

add_executable(${PROJECT_NAME} main.cpp)

include(FetchContent)
FetchContent_Declare(Range-v3 GIT_REPOSITORY "https://github.com/ericniebler/range-v3")
FetchContent_MakeAvailable(Range-v3)

target_link_libraries(${PROJECT_NAME} PRIVATE range-v3)

target_compile_features(${PROJECT_NAME} PUBLIC cxx_std_20)
if(GCC)
target_compile_options(${PROJECT_NAME} PUBLIC
  -Wall -Wextra -Wpedantic -Wconversion)
elseif(MSVC)
target_compile_options(${PROJECT_NAME} PUBLIC /W3 )
endif()