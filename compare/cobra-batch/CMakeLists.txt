# cobra-batch: CoBRA's command-line pipeline over a file of expressions, one per line, timing
# each simplification and counting its heap, for bitwright-compare. Built against a CoBRA
# checkout (see ../README.md):
#
#   cmake -S . -B build -G Ninja -DCMAKE_BUILD_TYPE=Release \
#     -DCOBRA_SOURCE=/path/to/CoBRA -DCMAKE_PREFIX_PATH=/path/to/CoBRA/build-deps/install
#   cmake --build build

cmake_minimum_required(VERSION 3.20)
project(cobra-batch LANGUAGES C CXX)

set(COBRA_SOURCE "" CACHE PATH "A CoBRA checkout (github.com/trailofbits/CoBRA)")
if(NOT EXISTS "${COBRA_SOURCE}/tools/cobra-cli/ExprParser.cpp")
    message(FATAL_ERROR "Set COBRA_SOURCE to a CoBRA checkout")
endif()

# CoBRA's own build, flags included; only what the driver links is built.
add_subdirectory("${COBRA_SOURCE}" cobra EXCLUDE_FROM_ALL)

add_executable(cobra-batch main.cpp "${COBRA_SOURCE}/tools/cobra-cli/ExprParser.cpp")
# CoBRA sets C++23 for its own directory only.
target_compile_features(cobra-batch PRIVATE cxx_std_23)
set_target_properties(cobra-batch PROPERTIES CXX_EXTENSIONS OFF)
target_include_directories(cobra-batch PRIVATE "${COBRA_SOURCE}/tools/cobra-cli")
target_link_libraries(cobra-batch PRIVATE cobra-core)
