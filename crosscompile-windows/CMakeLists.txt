# CMake file for crosscompiling Maxima/wxMaxima for Windows
# SPDX-License-Identifier: GPL-2.0-or-later
# Copyright (C) by Wolfgang Dautermann
# License GPLv2+: GNU GPL version 2 or later <http://gnu.org/licenses/gpl.html>
# This is free software: you are free to change and redistribute it.
# There is NO WARRANTY, to the extent permitted by law.

set(CMAKE_SYSTEM_NAME Windows)

option(BUILD_64BIT "Build a 64 bit installer." YES)

if(BUILD_64BIT)
    set(HOST x86_64-w64-mingw32)
    set(INSTALLERSUFFIX "win64")
else()
    set(HOST i686-w64-mingw32)
    set(INSTALLERSUFFIX "win32")
endif()

set(CMAKE_C_COMPILER   ${HOST}-gcc)
set(CMAKE_CXX_COMPILER ${HOST}-g++)
set(CMAKE_RC_COMPILER  ${HOST}-windres)

cmake_minimum_required(VERSION 3.16)
project(maxima)

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} ${CMAKE_SOURCE_DIR}/ ${CMAKE_BINARY_DIR}/)


# On which windows drive (C:, D:, ...) will be the default installation path?
set(WINDOWS_DRIVELETTER "C")


# What is the build system?
execute_process(COMMAND gcc -dumpmachine OUTPUT_VARIABLE BUILDHOST OUTPUT_STRIP_TRAILING_WHITESPACE)
message(STATUS "Build system: ${BUILDHOST}")

# Output the host system, for which we are compiling
message(STATUS "Host system: ${HOST}")

find_file(NSISTEMPLATE_IN  NAMES "NSIS.template.in"
    PATHS "${CMAKE_ROOT}/Modules/" "${CMAKE_ROOT}/Modules/Internal/CPack")
file(READ "${NSISTEMPLATE_IN}" MYNSISTEMPLATE)
string(REPLACE "RequestExecutionLevel admin" "RequestExecutionLevel admin
!include FileFunc.nsh
!include LogicLib.nsh
" MYNSISTEMPLATE "${MYNSISTEMPLATE}")

string(REPLACE "Function .onInit" "Function .onInit
\${GetParameters} \$0
\${GetOptions} \$0 \"/no_vtk\" \$1
\${IfNot} \${Errors}
    !insertmacro UnselectSection \${vtk}
\${EndIf}
\${GetOptions} \$0 \"/no_gnuplot\" \$1
\${IfNot} \${Errors}
    !insertmacro UnselectSection \${gnuplot}
\${EndIf}
\${GetOptions} \$0 \"/no_wxmaxima\" \$1
\${IfNot} \${Errors}
    !insertmacro UnselectSection \${wxmaxima}
\${EndIf}
\${GetOptions} \$0 \"/?\" \$1
\${IfNot} \${Errors}
        MessageBox MB_OK \"Installer for Maxima\$\\n\$\\nThis installer allows the following command line options:\$\\n        /S - silent install\$\\n        /D=<path> - select the install path\$\\n        /no_vtk - do not select VTK\$\\n        /no_gnuplot - do not select Gnuplot\$\\n        /no_wxmaxima - do not select wxMaxima\$\\n        /? - this help message\$\\n\$\\nMaxima Website: https://maxima.sourceforge.io\"
        Abort
\${EndIf}

" MYNSISTEMPLATE "${MYNSISTEMPLATE}")
file(WRITE ${CMAKE_BINARY_DIR}/NSIS.template.in "${MYNSISTEMPLATE}")
message(STATUS "Copied and patched ${NSISTEMPLATE_IN} to ${CMAKE_BINARY_DIR}/NSIS.template.in")

option(USE_WXMAXIMA_GIT "Use wxMaxima development snapshot." NO)
option(USE_VTK "Use VTK." YES)
# the following option is used for nightly builds of the installer.
# it builds the current Maxima/wxMaxima Git versions and also
# sets the installation directory to ${WINDOWS_DRIVELETTER}:\maxima-current
option(BUILD_CURRENT "Build a installer for current Maxima/wxMaxima." NO)

option(WITH_CLISP "Include CLISP in the installer." YES)
option(WITH_SBCL "Include SBCL in the installer." YES)
option(WITH_ABCL "Include ABCL in the installer." NO)
option(WITH_CCL64 "Include CCL64 in the installer." NO)

# Concerning the used Lisp versions:
#  - SBCL is fast, but sometimes runs out of memory in places it really shouldn't
#    (Loading LAPACK on IA32, for example) and isn't too happy with changing to
#    non-ascii-non-unicode pathnames (which wxMaxima works around by now, though,
#    and which Xmaxima doesn't even try to do)
#  - CLISP is slow. And version 2.49 only sends valid output over the network
#    if the front-end is slow enough. Test cases: Running a demo, all commands
#    with loads of compiler output (load("draw"); for the first time) or just
#    receiving a batch of new autocompletion symbols. Since the libraries the
#    front-ends use have evolved in the last years it has become easy to
#    trigger this => Setting SBCL to be the default.
#  - ABCL (optional) is a Java based Lisp.
#  - CCL64 (optional) support is very new.

# $lisp_STYLE is used for licenses.html
# $lisp_ENABLED for lispselector.tcl
if(WITH_CLISP)
    set(CLISP_STYLE "")
    set(CLISP_ENABLED 1)
else()
    set(CLISP_STYLE "display: none;")
    set(CLISP_ENABLED 0)
endif()

if(WITH_SBCL)
    set(SBCL_STYLE "")
    set(SBCL_ENABLED 1)
else()
    set(SBCL_STYLE "display: none;")
    set(SBCL_ENABLED 0)
endif()

if(WITH_ABCL)
    set(ABCL_STYLE "")
    set(ABCL_ENABLED 1)
else()
    set(ABCL_STYLE "display: none;")
    set(ABCL_ENABLED 0)
endif()

if(WITH_CCL64)
    set(CCL64_STYLE "")
    set(CCL64_ENABLED 1)
else()
    set(CCL64_STYLE "display: none;")
    set(CCL64_ENABLED 0)
endif()

set(WITH_DEFAULT_LISP "sbcl" CACHE STRING "Which Lisp should be used by default?")
set_property(CACHE WITH_DEFAULT_LISP PROPERTY STRINGS "clisp" "sbcl" "abcl" "ccl64")

# If you want to use a updated version of a program,
# update the version number and the checksum.
# If no further patches are needed, you should get a
# updated setup-file automatically.


if(BUILD_CURRENT)
    set(USE_WXMAXIMA_GIT YES)
    set(MAXIMAVERSION "current")
else()
    # Get Maxima version from configure.ac
    file(STRINGS "${CMAKE_SOURCE_DIR}/../configure.ac" CONFIGUREAC REGEX "AC_INIT\\(.*\\)")
    string(REGEX REPLACE "AC_INIT\\(\\[maxima\\],[ \t\r\n]*\\[(.*)\\]\\)" "\\1" MAXIMAVERSION ${CONFIGUREAC})
    message(STATUS "Maxima version (from configure.ac): ${MAXIMAVERSION}")
endif()

# The HTML documentation is installed in a directory depending on "git describe",
# when building from Git, e.g.:
# share/maxima/branch_5_45_base_99_g0b3357e40_dirty/doc/html/maxima_singlepage.html
# Otherwise the version number is included, e.g something like:
# share/maxima/5.45.1/doc/html/maxima_singlepage.html
# Set it first to the second variant, if Git is found and we are building
# from a Git tree use the result of "git describe --dirty" in the path instead - where
# "-" are changed to "_" (see commit d5d04f2 and the file '../configure.ac').
set(MAXIMA_SINGLEPAGE_HTML "share/maxima/${MAXIMAVERSION}/doc/html/maxima_singlepage.html")
find_package(Git)
if(Git_FOUND)
    execute_process(COMMAND ${GIT_EXECUTABLE} describe --dirty
                    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}
                    OUTPUT_VARIABLE GIT_DESCRIBE
                    ERROR_QUIET
                    OUTPUT_STRIP_TRAILING_WHITESPACE)
    if(GIT_DESCRIBE)
        string(REPLACE "-" "_" GIT_DESCRIBE ${GIT_DESCRIBE})
        set(MAXIMA_SINGLEPAGE_HTML "share/maxima/${GIT_DESCRIBE}/doc/html/maxima_singlepage.html")
    endif()
endif()



# Where are libgcc and libstdc++?
# Seems difficult. On Ubuntu 22.04 and 20.04 (64bit) the library libgcc is called libgcc_s_seh-1.dll.
# On Ubuntu 20.04 (32bit) it is libgcc_s_sjlj-1.dll - that file does not exist in Ubuntu 22.04, there it is most likely libgcc_s_dw2-1.dll
if(BUILD_64BIT)
    execute_process(COMMAND "${CMAKE_CXX_COMPILER}" -print-file-name=libgcc_s_seh-1.dll OUTPUT_VARIABLE MINGW_LIBGCC    OUTPUT_STRIP_TRAILING_WHITESPACE)
else()
    execute_process(COMMAND "${CMAKE_CXX_COMPILER}" -print-file-name=libgcc_s_sjlj-1.dll OUTPUT_VARIABLE MINGW_LIBGCC    OUTPUT_STRIP_TRAILING_WHITESPACE)
    if("${MINGW_LIBGCC}" STREQUAL "libgcc_s_sjlj-1.dll")
        # "${CMAKE_CXX_COMPILER}" -print-file-name=libgcc_s_sjlj-1.dll prints the string, if the file was not found. Otherwise the full path to the file.
        execute_process(COMMAND "${CMAKE_CXX_COMPILER}" -print-file-name=libgcc_s_dw2-1.dll OUTPUT_VARIABLE MINGW_LIBGCC    OUTPUT_STRIP_TRAILING_WHITESPACE)
    endif()
endif()

execute_process(COMMAND "${CMAKE_CXX_COMPILER}" -print-file-name=libstdc++-6.dll     OUTPUT_VARIABLE MINGW_LIBSTDCPP OUTPUT_STRIP_TRAILING_WHITESPACE)

message(STATUS "Found libstdc++ at ${MINGW_LIBSTDCPP}")

message(STATUS "Found libgcc at ${MINGW_LIBGCC}")

add_subdirectory("wine/")

find_program(SEVENZIP_EXE NAMES 7z)

if(SEVENZIP_EXE)
    message(STATUS "Found 7z at ${SEVENZIP_EXE}")
else()
    message(FATAL_ERROR "7z not found. It is required for crosscompiling Maxima.")
endif()

# Avoid warnings in CMake >= 3.24:
# FIXME: Policy OLD is needed for texinfo, it does not build with the policy NEW
# But policy OLD is deprecated and may be removed in future CMake versions, see:
# https://cmake.org/cmake/help/latest/policy/CMP0135.html
# Hopefully texinfo solves that issue.
if(${CMAKE_VERSION} VERSION_GREATER_EQUAL 3.24)
    cmake_policy(SET CMP0135 OLD)
endif()

include(ExternalProject)


add_subdirectory("gnuplot/")

add_subdirectory("tcltk/")

add_subdirectory("texinfo/")

add_subdirectory("wxwidgets/")

add_subdirectory("wxmaxima/")

if(USE_VTK)
    add_subdirectory("vtk/")
    set(VTK_STYLE "")
else()
    set(VTK_STYLE "display: none;")
endif()

if(WITH_CLISP)
    add_subdirectory("clisp/")
    set(CLISP_CONFIGURE --enable-clisp --with-clisp=${CMAKE_BINARY_DIR}/wine-clisp.sh --with-clisp-runtime=${CMAKE_BINARY_DIR}/wine-lisp.sh)
    set(CLISP_DEPENDS "clisp")
    set(CLISP_ENABLED 1)
else()
    set(CLISP_CONFIGURE "")
    set(CLISP_DEPENDS "")
    set(CLISP_ENABLED 0)
endif()

if(WITH_SBCL)
    add_subdirectory("sbcl/")
    set(SBCL_CONFIGURE --enable-sbcl --with-sbcl=${CMAKE_BINARY_DIR}/wine-sbcl.sh)
    set(SBCL_DEPENDS "sbcl")
    set(SBCL_ENABLED 1)
else()
    set(SBCL_CONFIGURE "")
    set(SBCL_DEPENDS "")
    set(SBCL_ENABLED 0)
endif()

if(WITH_ABCL)
    add_subdirectory("abcl/")
    set(ABCL_CONFIGURE --enable-abcl --with-abcl-jar=${CMAKE_BINARY_DIR}/abcl/abcl-prefix/src/abcl/abcl.jar)
    set(ABCL_DEPENDS "abcl")
    set(ABCL_ENABLED 0)
else()
    set(ABCL_CONFIGURE "")
    set(ABCL_DEPENDS "")
    set(ABCL_ENABLED 1)
endif()

if(WITH_CCL64)
    add_subdirectory("ccl/")
    set(CCL64_CONFIGURE --enable-ccl64 --with-ccl64=${CMAKE_BINARY_DIR}/wine-ccl.sh)
    set(CCL64_DEPENDS "ccl")
    set(CCL_ENABLED 1)
else()
    set(CCL64_CONFIGURE "")
    set(CCL64_DEPENDS "")
    set(CCL_ENABLED 0)
endif()

configure_file("${CMAKE_SOURCE_DIR}/wine-clisp.sh.tmpl" "${CMAKE_BINARY_DIR}/wine-clisp.sh")
configure_file("${CMAKE_SOURCE_DIR}/wine-lisp.sh.tmpl" "${CMAKE_BINARY_DIR}/wine-lisp.sh")
configure_file("${CMAKE_SOURCE_DIR}/wine-sbcl.sh.tmpl" "${CMAKE_BINARY_DIR}/wine-sbcl.sh")
configure_file("${CMAKE_SOURCE_DIR}/wine-ccl.sh.tmpl" "${CMAKE_BINARY_DIR}/wine-ccl.sh")

externalproject_add(maxima
  # first copy the maxima source to a build directory, since out-of-source-builds do not work
  DOWNLOAD_COMMAND rsync -a --exclude=crosscompile-windows/build/ "${CMAKE_SOURCE_DIR}/../"  "${CMAKE_BINARY_DIR}/maxima-prefix/src/maxima"
  DEPENDS  tcl tk texinfo ${CLISP_DEPENDS} ${SBCL_DEPENDS} ${ABCL_DEPENDS} ${CCL64_DEPENDS}
  BUILD_IN_SOURCE 1
  CONFIGURE_COMMAND sh -c "test -x ./bootstrap && ./bootstrap || return 0"
            COMMAND PATH=${CMAKE_BINARY_DIR}/texinfo-installroot/bin:$ENV{PATH} LANG=C ./configure --host=${HOST} ${CLISP_CONFIGURE} ${SBCL_CONFIGURE} ${ABCL_CONFIGURE} ${CCL64_CONFIGURE} --with-default-lisp=${WITH_DEFAULT_LISP} --prefix=${WINDOWS_DRIVELETTER}:/maxima-${MAXIMAVERSION}
  # during the crosscompiling procedure, we call configure with shell scripts (wine-xyz.sh) to use the Windows versions.
  # change that after compiliation to the real binaries (clisp.exe for CLISP, sbcl.exe for SBCL, wx86cl64.exe for CCL64).
  BUILD_COMMAND PATH=${CMAKE_BINARY_DIR}/texinfo-installroot/bin:$ENV{PATH} LANG=C $(MAKE)
        COMMAND PATH=${CMAKE_BINARY_DIR}/texinfo-installroot/bin:$ENV{PATH} LANG=C $(MAKE) pdf
        COMMAND sed -i s+^.*wine-clisp.sh+clisp.exe+g src/maxima.bat
        COMMAND sed -i s+^.*wine-sbcl.sh+sbcl.exe+g src/maxima.bat
        COMMAND sed -i s+^.*wine-ccl.sh+wx86cl64.exe+g src/maxima.bat
  INSTALL_COMMAND PATH=${CMAKE_BINARY_DIR}/texinfo-installroot/bin:$ENV{PATH} LANG=C $(MAKE) install DESTDIR=${CMAKE_BINARY_DIR}/maxima-installroot/
          COMMAND PATH=${CMAKE_BINARY_DIR}/texinfo-installroot/bin:$ENV{PATH} LANG=C $(MAKE) extradocinstall DESTDIR=${CMAKE_BINARY_DIR}/maxima-installroot/
)


option(STRIP_HELPERPROGRAMS "Strip the included helper programs (winkill, winkill_lib, maxima_longnames)." YES)

# crosscompiling winkill with autoconf does not work, compile it using CMake.
add_library(winkill_lib SHARED ${CMAKE_SOURCE_DIR}/../interfaces/xmaxima/win32/winkill_lib.c)
add_executable(winkill ${CMAKE_SOURCE_DIR}/../interfaces/xmaxima/win32/winkill.c)
set_target_properties(winkill_lib PROPERTIES PREFIX "") # remove 'lib' prefix from libwinkill_lib.dll
target_link_libraries(winkill winkill_lib)

# convert windows short names to long names (e.g.
# "C:/Users/TESTTE~1/AppData/Local/Temp" to "C:/Users/test test/AppData/Local/Temp")
# CLISP can (currently not handle short names.
add_executable(maxima_longnames maxima_longnames.c)
if(STRIP_HELPERPROGRAMS)
    add_custom_command(TARGET winkill POST_BUILD COMMAND ${CMAKE_STRIP} winkill.exe)
    add_custom_command(TARGET winkill_lib POST_BUILD COMMAND ${CMAKE_STRIP} winkill_lib.dll)
    add_custom_command(TARGET maxima_longnames POST_BUILD COMMAND ${CMAKE_STRIP} maxima_longnames.exe)
endif()
install(TARGETS winkill winkill_lib maxima_longnames COMPONENT Maxima RUNTIME DESTINATION bin LIBRARY DESTINATION bin/)
install(FILES "${CMAKE_SOURCE_DIR}/../interfaces/xmaxima/win32/win_signals.lisp" DESTINATION bin/ COMPONENT Maxima)


install(DIRECTORY ${CMAKE_BINARY_DIR}/maxima-installroot/${WINDOWS_DRIVELETTER}:/maxima-${MAXIMAVERSION}/
        DESTINATION . COMPONENT Maxima 
        PATTERN "binary-clisp" EXCLUDE PATTERN "binary-sbcl" EXCLUDE PATTERN "binary-abcl" EXCLUDE PATTERN "binary-ccl64" EXCLUDE)
if(WITH_ABCL)
    install(DIRECTORY ${CMAKE_BINARY_DIR}/maxima-installroot/${WINDOWS_DRIVELETTER}:/maxima-${MAXIMAVERSION}/
            DESTINATION . COMPONENT ABCL PATTERN "binary-abcl")
endif()
if(WITH_CLISP)
    install(DIRECTORY ${CMAKE_BINARY_DIR}/maxima-installroot/${WINDOWS_DRIVELETTER}:/maxima-${MAXIMAVERSION}/
            DESTINATION . COMPONENT CLISP PATTERN "binary-clisp")
endif()
if(WITH_SBCL)
    install(DIRECTORY ${CMAKE_BINARY_DIR}/maxima-installroot/${WINDOWS_DRIVELETTER}:/maxima-${MAXIMAVERSION}/
            DESTINATION . COMPONENT SBCL PATTERN "binary-sbcl")
endif()
if(WITH_CCL64)
    install(DIRECTORY ${CMAKE_BINARY_DIR}/maxima-installroot/${WINDOWS_DRIVELETTER}:/maxima-${MAXIMAVERSION}/
            DESTINATION . COMPONENT CCL64 PATTERN "binary-ccl64")
endif()

install(FILES "${CMAKE_SOURCE_DIR}/xmaxima.bat" DESTINATION bin/ COMPONENT Maxima)
install(FILES "${CMAKE_BINARY_DIR}/maxima-prefix/src/maxima/doc/info/maxima.pdf" DESTINATION share/doc/ COMPONENT Maxima)
configure_file("${CMAKE_SOURCE_DIR}/lispselector.tcl" "${CMAKE_BINARY_DIR}/lispselector.tcl")
install(FILES "${CMAKE_BINARY_DIR}/lispselector.tcl" DESTINATION bin/ COMPONENT Maxima)
install(FILES "${CMAKE_SOURCE_DIR}/lispselector.bat" DESTINATION bin/ COMPONENT Maxima)



# Include DLLs from the current Mingw environment.
install(FILES "${MINGW_LIBSTDCPP}" "${MINGW_LIBGCC}" DESTINATION bin/ COMPONENT Maxima)

configure_file("${CMAKE_SOURCE_DIR}/licenses.html" "${CMAKE_BINARY_DIR}/licenses.html")
install(FILES "${CMAKE_BINARY_DIR}/licenses.html" DESTINATION share/doc/ COMPONENT Maxima)

file(COPY "${CMAKE_SOURCE_DIR}/../COPYING" DESTINATION "${CMAKE_BINARY_DIR}")
file(READ "${CMAKE_SOURCE_DIR}/LICENSE_APPENDIX.txt" LICENSE_APPENDIX)
file(APPEND "${CMAKE_BINARY_DIR}/COPYING" "${LICENSE_APPENDIX}")

set(CPACK_GENERATOR "NSIS;ZIP")
set(CPACK_PACKAGE_VERSION "${MAXIMAVERSION}")
set(CPACK_PACKAGE_DESCRIPTION_SUMMARY "Maxima")
set(CPACK_PACKAGE_VENDOR "Maxima Team")
set(CPACK_PACKAGE_DESCRIPTION_FILE "${CMAKE_SOURCE_DIR}/../README")
set(CPACK_RESOURCE_FILE_LICENSE "${CMAKE_BINARY_DIR}/COPYING")
set(CPACK_PACKAGE_INSTALL_DIRECTORY "maxima-${CPACK_PACKAGE_VERSION}")
set(CPACK_NSIS_INSTALL_ROOT "${WINDOWS_DRIVELETTER}:")
set(CPACK_NSIS_ENABLE_UNINSTALL_BEFORE_INSTALL ON)
set(CPACK_PACKAGE_ICON "${CMAKE_SOURCE_DIR}/maxima-icon.bmp")
set(CPACK_NSIS_MUI_ICON "${CMAKE_SOURCE_DIR}\\\\maxima-icon.ico")
set(CPACK_NSIS_MUI_UNIICON "${CPACK_NSIS_MUI_ICON}")
set(CPACK_NSIS_INSTALLED_ICON_NAME "bin\\\\maxima-command.ico")
set(CPACK_NSIS_DISPLAY_NAME "Maxima computer algebra system")
set(CPACK_PACKAGE_EXECUTABLES "..\\\\bin\\\\wxmaxima" "wxMaxima (GUI for Maxima)")
set(CPACK_NSIS_URL_INFO_ABOUT "https://maxima.sourceforge.io")
set(CPACK_NSIS_MENU_LINKS "bin/maxima.bat" "Maxima (command line)" "bin/xmaxima.bat" "XMaxima: graphical interface for Maxima" "https://maxima.sourceforge.io" "About Maxima" "https://wxmaxima-developers.github.io/wxmaxima/" "About wxMaxima" "${MAXIMA_SINGLEPAGE_HTML}" "Maxima documentation"  "share/doc/licenses.html" "Maxima and included software licenses" "bin/lispselector.bat" "Configure default LISP for Maxima")
set(CPACK_PACKAGE_FILE_NAME "maxima-${CPACK_PACKAGE_VERSION}-${INSTALLERSUFFIX}")
set(CPACK_NSIS_COMPRESSOR "/SOLID lzma")


set(CPACK_NSIS_MUI_WELCOMEFINISHPAGE_BITMAP "${CMAKE_SOURCE_DIR}/maxima-installerimage.bmp")
include(CPack)

cpack_add_component(Maxima
                    DESCRIPTION "The Maxima computer algebra system.\nRequired." REQUIRED)

if(USE_VTK)
    cpack_add_component(VTK
                        DESCRIPTION "VTK is an advanced graphic toolkit for draw().\nOptional.")
endif()

cpack_add_component(Gnuplot
                    DESCRIPTION "Gnuplot is the main graphic toolkit.\nInstallation is strongly recommended.")

cpack_add_component(wxMaxima
                    DESCRIPTION "wxMaxima is an advanced GUI for Maxima based on wxWidgets.\nInstallation is strongly recommended.")
if(WITH_CLISP)
    cpack_add_component(Clisp
                        DESCRIPTION "The CLISP Lisp compiler.\nOne Lisp compiler is required.")
endif()
if(WITH_SBCL)
    cpack_add_component(SBCL
                        DESCRIPTION "The SBCL Lisp compiler.\nOne Lisp compiler is required.")
endif()

if(WITH_ABCL)
    cpack_add_component(ABCL
                        DESCRIPTION "The ABCL Lisp compiler.\nA Java installation is required.\nOne Lisp compiler is required.")
endif()
if(WITH_CCL64)
    cpack_add_component(CCL64
                        DESCRIPTION "The CCL (64Bit) Lisp compiler.\nOne Lisp compiler is required.")
endif()

cpack_add_component(TclTk
                    DISPLAY_NAME "Tcl/Tk"
                    DESCRIPTION "The TCL/TK scripting language.\nRequired." REQUIRED)
