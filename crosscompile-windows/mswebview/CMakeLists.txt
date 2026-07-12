# CMake file for crosscompiling Maxima/wxMaxima for Windows
# SPDX-License-Identifier: GPL-2.0-or-later
# Copyright (C) by Wolfgang Dautermann
# License GPLv2+: GNU GPL version 2 or later <http://gnu.org/licenses/gpl.html>
# This is free software: you are free to change and redistribute it.
# There is NO WARRANTY, to the extent permitted by law.

# If you want to use a updated version of a program,
# update the version number and the checksum.
# If no further patches are needed, you should get a
# updated setup-file automatically.


# WxWidgets Webview/Edge needs this package

# MSWEBVIEWVERSION / MSWEBVIEW_MD5 is set in the directory above.

externalproject_add(mswebview
  DOWNLOAD_NAME "microsoft.web.webview2.${MSWEBVIEWVERSION}.nupkg"
  URL "https://www.nuget.org/api/v2/package/Microsoft.Web.WebView2/${MSWEBVIEWVERSION}"
  # will be extracted as patch command in the external project wxwidgets.
  DOWNLOAD_NO_EXTRACT true
  DOWNLOAD_DIR ${CMAKE_SOURCE_DIR}/downloads
  URL_MD5 ${MSWEBVIEW_MD5}
  CONFIGURE_COMMAND ""
  BUILD_COMMAND ""
  INSTALL_COMMAND ""
)



# Install MsWebview DLL
if(BUILD_64BIT)
    install(FILES "${CMAKE_BINARY_DIR}/wxwidgets/wxwidgets-prefix/src/wxwidgets/3rdparty/webview2/build/native/x64/WebView2Loader.dll" DESTINATION bin COMPONENT wxMaxima)
else()
    install(FILES "${CMAKE_BINARY_DIR}/wxwidgets/wxwidgets-prefix/src/wxwidgets/3rdparty/webview2/build/native/x86/WebView2Loader.dll" DESTINATION bin COMPONENT wxMaxima)
endif()
