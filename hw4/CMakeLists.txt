cmake_minimum_required(VERSION 3.16)
project(compiler-design-hw4)
add_custom_target(make-test
        COMMAND $(MAKE) test
        DEPENDS Makefile
        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
        )
add_custom_target(make-clean
        COMMAND $(MAKE) clean
        DEPENDS Makefile
        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
        )