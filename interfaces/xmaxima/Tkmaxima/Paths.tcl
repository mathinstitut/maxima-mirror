############################################################
# Paths.tcl                                                #
# Copyright (C) 1998 William F. Schelter                   #
# For distribution under GNU public License.  See COPYING. #
#                                                          #
############################################################
#
# Attach this near the bottom of the xmaxima code to find the paths needed
# to start up the interface.

proc setMaxDir {} {
    if {$::tcl_platform(platform) == "windows"} {
	# Make sure the signals thread is started
	set ::env(MAXIMA_SIGNALS_THREAD) "1"

	# Assume the executable is one level down from the top
	# for 5.6 this was src/ and for 5.9 its bin/
	set up [file dir [file dir [info name]]]

	if {[info exists ::autoconf] && \
		[info exists ::autoconf(prefix)] && \
		[info exists ::autoconf(exec_prefix)] && \
		[info exists ::autoconf(libdir)] && \
		[info exists ::autoconf(libexecdir)] && \
		[info exists ::autoconf(datadir)] && \
		[info exists ::autoconf(infodir)] && \
		[info exists ::autoconf(version)] && \
		[info exists ::autoconf(package)] && \
		[file isdir  $::autoconf(datadir)] && \
		[file isdir \
		     [file join $::autoconf(datadir) \
			  $::autoconf(package) $::autoconf(version)]]} {
	    # Assume it's CYGWIN or  MSYS in /usr/local
	} elseif {[file isdir $up/lib] && \
		      [file isdir $up/bin] && \
		      [file isdir $up/libexec] && \
		      [file isdir $up/info] && \
		      [file isdir $up/share]} {
	    set ::autoconf(prefix) $up
	    set ::env(MAXIMA_PREFIX) $up
	    set ::autoconf(exec_prefix) $up
	    set ::autoconf(libdir) "$up/lib"
	    set ::autoconf(libexecdir) "$up/libexec"
	    set ::autoconf(datadir) "$up/share"
	    set ::autoconf(infodir) "$up/info"
	    # These two should be valid
	    # set ::autoconf(package) "maxima"
	    # set ::autoconf(version) "5.9.0rc1"
	} else {
	    # Old windows 5.5 layout
	    # Assume we are in the same directory as saved_maxima
	    if {[file isfile [set exe $up/src/saved_maxima.exe]]} {
		set ::env(MAXIMA_DIRECTORY) $up
		set ::xmaxima_priv(maxima_verpkgdatadir) \
		    $::env(MAXIMA_DIRECTORY)
		set ::xmaxima_priv(xmaxima_maxima) $exe
		set ::xmaxima_priv(maxima_xmaximadir) [file dir $exe]

		# This should be unused
		set ::xmaxima_priv(maxima_verpkglibdir) \
		    $::env(MAXIMA_DIRECTORY)
		set ::xmaxima_priv(maxima_verpkgdatadir) \
		    $::env(MAXIMA_DIRECTORY)

		# This should be unused
		set ::xmaxima_priv(maxima_prefix) \
		    $::env(MAXIMA_DIRECTORY)
	    }
	}
    }
    #mike Could someone document all of these environment variables?
    # ::autoconf(prefix) does not seem to me to be the equivalent of
    # $::env(MAXIMA_DIRECTORY) so I don't understand the next statement

    # jfa: MAXIMA_PREFIX supersedes MAXIMA_DIRECTORY. (Why? Because the
    #      option to configure is --prefix. MAXIMA_PREFIX is thus a runtime
    #      change of --prefix.)
    #      Yes, MAXIMA_DIRECTORY means the same thing. We only include
    #      it for some level of backward compatibility.
    if { [info exists env(MAXIMA_DIRECTORY)] } {
	set ::env(MAXIMA_PREFIX) $::env(MAXIMA_DIRECTORY)
    }

    # jfa: This whole routine is a disaster. The general plan for maxima
    # paths is as follows:
    #   1) Use the environment variables if they exist.
    #   2) Otherwise, attempt to use the compile-time settings from
    #      ::autoconf.
    #   3) If the entire package has been moved to a prefix other than
    #      that given at compile time, use the location of the (x)maxima
    #      executable to determine the new prefix.
    # The corresponding path setting procedure in the maxima source can
    # be found in init-cl.lisp.

    # The following section should be considered temporary work-around.
    if { [info exists env(MAXIMA_VERPKGDATADIR)] } {
	set ::xmaxima_priv(maxima_verpkgdatadir) $::env(MAXIMA_VERPKGDATADIR)
    }
    # End temporary workaround. It's only a workaround because the next
    # section is backwards: 

    #mike Is it correct to assume that ::autoconf exists and is valid
    # for binary windows distributions? I think it would be better
    # to make (MAXIMA_DIRECTORY) take precedence, and work off
    # [info nameofexe] if necessary.

    if {[info exists ::xmaxima_priv(maxima_prefix)]} {
	# drop through
    } elseif { [info exists env(MAXIMA_PREFIX)] } {
	set ::xmaxima_priv(maxima_prefix) $::env(MAXIMA_PREFIX)
    } else {
	set ::xmaxima_priv(maxima_prefix) $::autoconf(prefix)
    }
    if {[info exists ::xmaxima_priv(maxima_verpkgdatadir)]} {
	# drop through
    } else {
	if { [info exists env(MAXIMA_DATADIR)] } {
	    set maxima_datadir $::env(MAXIMA_DATADIR)
	} elseif { [info exists env(MAXIMA_PREFIX)] } {
	    set maxima_datadir \
		[file join $::env(MAXIMA_PREFIX) share]
	} else {
	    set maxima_datadir $::autoconf(datadir)
	}
	# maxima_datadir is unused outside of this proc

	if {![file isdir $maxima_datadir]} {
	    tk_messageBox -title Warning -icon warning -message \
                [mc "Maxima data directory not found in '%s'" \
			     [file native  $maxima_datadir]]
	}
	set ::xmaxima_priv(maxima_verpkgdatadir) \
	    [file join $maxima_datadir $::autoconf(package) \
		 $::autoconf(version)]
    }

    # omplotdata messages
    #::msgcat::mcload [file join $::xmaxima_priv(maxima_verpkgdatadir) msgs]

    if {[info exists ::xmaxima_priv(maxima_verpkglibdir)]} {
	# drop through
    } elseif { [info exists env(MAXIMA_VERPKGLIBDIR)] } {
	set ::xmaxima_priv(maxima_verpkglibdir) $::env(MAXIMA_VERPKGLIBDIR)
    } elseif { [info exists env(MAXIMA_PREFIX)] } {
	set ::xmaxima_priv(maxima_verpkglibdir) \
	    [file join $::env(MAXIMA_PREFIX) lib $::autoconf(package) \
		 $::autoconf(version)]
    } else {
	set ::xmaxima_priv(maxima_verpkglibdir) \
	    [file join $::autoconf(libdir) $::autoconf(package) \
		 $::autoconf(version)]
    }
    if {[info exists ::xmaxima_priv(maxima_xmaximadir)]} {
	# drop through
    } elseif { [info exists env(MAXIMA_XMAXIMADIR)] } {
	set ::xmaxima_priv(maxima_xmaximadir) $::env(MAXIMA_XMAXIMADIR)
    } else {
	set ::xmaxima_priv(maxima_xmaximadir) \
	    [file join $::xmaxima_priv(maxima_verpkgdatadir) xmaxima]
    }

    # xmaxima messages
    ::msgcat::mcload [file join $::xmaxima_priv(maxima_xmaximadir) msgs]

    # Define maxima_lang_subdir
    if { [info exists env(MAXIMA_LANG_SUBDIR)] } {
	set ::xmaxima_priv(maxima_lang_subdir) $::env(MAXIMA_LANG_SUBDIR)
    } else {
	if { $::tcl_platform(platform) == "windows" } {
    	    set wlocale [ ::msgcat::mclocale ]
	} else {
    	    set wlocale ""
	    if { [info exists env(LC_ALL)] } { 
		set wlocale $::env(LC_ALL) 
	    } elseif { [info exists env(LC_MESSAGES)] } { 
		set wlocale $::env(LC_MESSAGES) 
	    } elseif { [info exists env(LANG)] } { 
		set wlocale $::env(LANG) }
	}	
	# Only languages known to Maxima
	set wlocale [string tolower $wlocale]
	switch -glob $wlocale {
	  "es*utf*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "es.utf8"
		}
	  "es*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "es"
		}
	  "pt_br*utf*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "pt_BR.utf8"
		}
	  "pt_br*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "pt_BR"
		}
	  "pt*utf*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "pt.utf8"
		}
	  "pt*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "pt"
		}
	  "de*utf*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "de.utf8"
		}
	  "de*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "de"
		}
	  "fr*utf*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "fr.utf8"
		}
	  "fr*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "fr"
		}
	  "it*utf*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "it.utf8"
		}
	  "it*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "it"
		}
	  "ru*utf*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "ru.utf8"
		}
	  "ru*koi*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "ru.koi8r"
		}
	  "ru*" {
		    set ::xmaxima_priv(maxima_lang_subdir) "ru"
		}
	  default 
	        {
		    set ::xmaxima_priv(maxima_lang_subdir) ""
		}
	}
	#puts $::xmaxima_priv(maxima_lang_subdir)
    }

    # On Windows ::msgcat::mclocale is a good way to derive locale 
    if { $::tcl_platform(platform) == "windows" } {
	    set ::env(LANG) [ ::msgcat::mclocale ]
    }

    # Bring derived quantities up here too so we can see the
    # side effects of setting the above variables

    # used in Menu.tcl CMMenu.tcl
    if {[file isdir [set dir [file join  $::xmaxima_priv(maxima_verpkgdatadir) info]]]} {
	# 5.6 and down
	set ::xmaxima_priv(pReferenceToc) \
	    [file join $dir index.html]
    } elseif {[file isdir [set dir [file join  $::xmaxima_priv(maxima_verpkgdatadir) doc]]]} {
	# 5.9 and up
	# first choose the HTML documentation
	if { $::xmaxima_priv(maxima_lang_subdir) != "" && \
	     [file exists [file join $dir html $::xmaxima_priv(maxima_lang_subdir) index.html] ] } {
	    set ::xmaxima_priv(pReferenceToc) [file join $dir html $::xmaxima_priv(maxima_lang_subdir) index.html]
	} else {
	    set ::xmaxima_priv(pReferenceToc) [file join $dir html index.html]
	}
	# if the platform is Windows and Maxima is running localized, try the following help files
	# if they exist:
	# 1st priority: localized CHM
	# 2nd priority: localized HTML
	# 3rd priority: english CHM
	# 4th priority: english HTML
        if { $::tcl_platform(platform) == "windows" } {
	    if { $::xmaxima_priv(maxima_lang_subdir) != "" } {
		if {[file exists [file join $dir chm $::xmaxima_priv(maxima_lang_subdir) maxima.chm] ] } {
		    set ::xmaxima_priv(pReferenceToc) [file join $dir chm $::xmaxima_priv(maxima_lang_subdir) maxima.chm]
		} else {
		    if {[file exists [file join $dir html $::xmaxima_priv(maxima_lang_subdir) index.html] ] } {
			set ::xmaxima_priv(pReferenceToc) [file join $dir html $::xmaxima_priv(maxima_lang_subdir) index.html]
		    } else {
			if {[file exists [file join $dir chm maxima.chm] ] } {
			    set ::xmaxima_priv(pReferenceToc) [file join $dir chm maxima.chm]
			} else {
			    set ::xmaxima_priv(pReferenceToc) [file join $dir html index.html]
			}
		    }
		}
	    } else {
		if {[file exists [file join $dir chm maxima.chm] ] } {
		    set ::xmaxima_priv(pReferenceToc) [file join $dir chm maxima.chm]
		} else {
		    set ::xmaxima_priv(pReferenceToc) [file join $dir html index.html]
		}
	    }
	} else {
	    # Platform != windows, just choose the HTML documentation
	    if { $::xmaxima_priv(maxima_lang_subdir) != "" && \
		[file exists [file join $dir html $::xmaxima_priv(maxima_lang_subdir) index.html] ] } {
		set ::xmaxima_priv(pReferenceToc) [file join $dir html $::xmaxima_priv(maxima_lang_subdir) index.html]
	    } else {
		set ::xmaxima_priv(pReferenceToc) [file join $dir html index.html]
	    }
	}
    } else {
	tk_messageBox -title Warning -icon warning -message \
            [mc "Documentation not found in '%s'" \
                 [file native  $::xmaxima_priv(maxima_verpkgdatadir)]]
    }

    # used in Menu.tcl CMMenu.tcl
    if {[file isdir [set dir [file join  $::xmaxima_priv(maxima_verpkgdatadir) tests]]]} {
	# 5.9 and up
	set ::xmaxima_priv(pTestsDir) $dir
    } elseif {[file isdir [set dir [file join  $::xmaxima_priv(maxima_verpkgdatadir) doc]]]} {
	# 5.6 and down
	set ::xmaxima_priv(pTestsDir) $dir
    } else {
	# who cares
    }
    set file [file join $::xmaxima_priv(maxima_xmaximadir) "intro.html"]
    if {$::tcl_platform(platform) == "windows"} {
        # convert to unix
        set file [file dir $file]/[file tail $file]
    }
    # FIXME: This is bogus - need a FileToUrl
    set ::xmaxima_priv(firstUrl) file:/$file

    # set up for autoloading
    global auto_path
    set dir [file join $::xmaxima_priv(maxima_xmaximadir) Tkmaxima]
    if {[file isdir $dir]} {
	lappend auto_path $dir
    }
    # jfa: Windows 98 users were seeing long startup times because
    # MAXIMA_USERDIR defaults to HOME, which is usually C:\.
    # Make the default something else under Windows 98 as a workaround.
    # This is ugly.
    if {$::tcl_platform(os) == "Windows 95"} {
	if {![info exists env(MAXIMA_USERDIR)]} {
	    set ::env(MAXIMA_USERDIR) "$::xmaxima_priv(maxima_prefix)/user"
	}
    }
    # jfa: extend path so that gcl can see gcc in windows package
    # I don't know that this is the best place for this
    if {$::tcl_platform(platform) == "windows"} {
	# jfa: This is an attempt to get a working path designation
	# on various Windows versions.
	if {$::tcl_platform(os) == "Windows 95"} {
	    # Windows 95 or Windows 98
	    regsub -all {/} "$::xmaxima_priv(maxima_prefix)\\BIN" {\\} maxbinpath
	} else {
	    # Other versions of Windows
	    set maxbinpath "$::xmaxima_priv(maxima_prefix)/bin"
	}
	set ::env(PATH) "$maxbinpath;$::env(PATH)"
    }
}

proc vMAXSetMaximaCommand {} {
    set ::xmaxima_priv(localMaximaServer) ""
    if {[info exists ::xmaxima_priv(xmaxima_maxima)] && \
	    $::xmaxima_priv(xmaxima_maxima) != ""} {
	if {[set exe [auto_execok $::xmaxima_priv(xmaxima_maxima)]] == "" } {

	    tk_messageBox -title Error -icon error -message \
                [mc "Maxima executable not found\n%s\n\n Try setting the environment variable XMAXIMA_MAXIMA." \
			      [file native $::xmaxima_priv(xmaxima_maxima)]]
	    return
	}
    } elseif { [info exists env(XMAXIMA_MAXIMA)] } {
	set ::xmaxima_priv(xmaxima_maxima) $::env(XMAXIMA_MAXIMA)
	if {[set exe [auto_execok $::xmaxima_priv(xmaxima_maxima)]] == "" } {
	    tk_messageBox -title Error -icon error -message \
                [concat [mc "Maxima executable not found."] "\n%s\nXMAXIMA_MAXIMA=$::env(XMAXIMA_MAXIMA)"]
	    return
	}
    } else {
	set ::xmaxima_priv(xmaxima_maxima) maxima
	if {[set exe [auto_execok $::xmaxima_priv(xmaxima_maxima)]] == "" } {
	    tk_messageBox -title Error -icon error -message \
                [mc "Maxima executable not found\n\n Try setting the environment variable  XMAXIMA_MAXIMA."]
	}
	# jfa: bypass maxima script on windows
        # vvz: on Windows 9X/ME only
	if {$::tcl_platform(os) == "Windows 95"} {
	    # maybe it's in lib - I don't like this
	    set dir $::xmaxima_priv(maxima_verpkglibdir)
	    # FIXME - need ::autoconf(lisp) so we don't need glob
	    set exes [glob -nocomplain $dir/binary-*/maxima.exe]
	    if {[llength $exes] != "1" || \
		    [set exe [lindex $exes 0]] == "" || \
		    ![file isfile $exe]} {
		tk_messageBox -title Error -icon error -message \
                    [mc "Maxima executable not found\n\n Try setting the environment variable  XMAXIMA_MAXIMA."]
		return
	    }
	} else {
	    set ::xmaxima_priv(xmaxima_maxima) maxima
	    if {[set exe [auto_execok $::xmaxima_priv(xmaxima_maxima)]] == "" } {
                tk_messageBox -title Error -icon error -message \
                    [mc "Maxima executable not found\n\n Try setting the environment variable  XMAXIMA_MAXIMA."]
	    }
	}
    }
    set command {}
    lappend command $exe
    eval lappend command $::xmaxima_priv(opts)
    lappend command -s PORT
    if {$::tcl_platform(platform) == "windows"} {
        lappend command > NUL
    } else {
        lappend command > /dev/null
    }
    lappend command &
    set ::xmaxima_priv(localMaximaServer) $command
}
