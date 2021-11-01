cmake_minimum_required(VERSION 3.10)
project(compiler-design-hw3)
add_custom_command(OUTPUT main.native
        COMMAND make main.native
        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
        MAIN_DEPENDENCY backend.ml)

add_custom_target(native DEPENDS main.native gradedtests.ml studenttests.ml)