Notes on Lisp implementations for Maxima:
=========================================

Clisp, CMUCL, Scieneer Common Lisp (SCL), GCL (ANSI-enabled only),
ECL, ABCL and SBCL can compile and execute Maxima.
Allegro Common Lisp (ACL) and CCL might also work, but have not
been fully tested.

Ports to other ANSI Common Lisps should be straightforward
and are welcome; please post a message on the Maxima mailing list
if you are interested in working on a port.

When Maxima is recompiled, the Lisp implementation is selected by
an argument of the form `--enable-foolisp` for the configure script.
`./configure --help` shows a list of the Lisp types recognized by
configure (among other options). It is possible to specify several
Lisp type(s) you want Maxima to be built with at the same time.
configure tries to autodetect the Lisp type if it is not specified,
but it has been reported that autodetection can fail.


Comparison of execution times (in seconds)
------------------------------------------

As of 2023-05-18 (using the current development version of Maxima)
the `run_testsuite()` function needed the following times for
these different Lisp versions and produced so many testsuite failures:

### Ubuntu 20.04, 64 bit

    Lisp            run time (real)   testsuite failures
    sbcl-2.3.0        85              none
    gcl-2.6.14       160              none
    cmucl-21d        209              none
    ccl-1.12.1       291              none
    acl-10.1         372              183
    ecl-21.2.1       546              none
    clisp-2.49.92    853              1
    abcl-1.9.1      1320              10


Clisp <http://clisp.org>
------------------------

Clisp can be built with readline support, so Maxima has
advanced command-line editing facilities when built with it.

Clisp is compiled to bytecodes, so Maxima running on Clisp is
substantially slower than on Lisps compiled to machine instructions.
On the other hand, Clisp contains code from CLN <https://www.ginac.de/CLN/>,
a library for efficient computations with all kinds of numbers in
arbitrary precision. Another advantage of Clisp is that byte code
resulting in compiling a program on one computer might work on a
computer running a different Clisp version. Also Clisp uses an
extremely efficient memory handling which means it might not run
out of memory where ECL, SBCL and GCL do.

CLISP version 2.49 has a bug that causes it to output garbled data
if the front-end is fast enough to acknowledge a data packet while
the next data packet is still being prepared.

There are Clisp implementations for many platforms including
MS Windows and Unix-like systems.


CMUCL <https://cmucl.org/>
--------------------------

CMUCL is a fast option for Maxima on platforms where it is
available. The rmaxima front-end provides advanced line-editing
facilities for Maxima when compiled with CMUCL. rlwrap is available
from: <https://github.com/hanslub42/rlwrap>

CMUCL versions: 18e and 19a and later are known to work.

There are CMUCL implementations only for Unix-like systems
(not MS Windows).


Scieneer Common Lisp (SCL) <https://web.archive.org/web/20171014210404/http://www.scieneer.com/scl/>
----------------------------------------------------------------------------------------------------

Scieneer Common Lisp (SCL) is a fast option for Maxima for a
range of Linux and Unix platforms.  The SCL 1.2.8 release and later
are supported.  SCL offers a lower case, case sensitive, version which
avoids the Maxima case inversion issues with symbol names.  Tested
front end options are: Maxima emacs mode available in the
interfaces/emacs/ directory, the Emacs imaxima mode available from
<https://sites.google.com/site/imaximaimath/>, and TeXmacs available from
<https://www.texmacs.org>


GCL <https://www.gnu.org/software/gcl/>
---------------------------------------

GCL >= 2.6.14 is required to build Maxima.

GCL can be built with readline support, so Maxima has advanced
command-line editing facilities when built with it.
GCL produces a fast Maxima executable that profit from GCL's
fast bignum algorithms.

Only the ANSI-enabled version of GCL works with Maxima, i.e.,
when GCL is built, it must be configured with the `--enable-ansi` flag,
i.e., execute `./configure --enable-ansi` in the build directory
before executing make.

Whether GCL is ANSI-enabled or not can be determined by
inspecting the banner which is printed when GCL is executed;
if ANSI-enabled, the banner should say `ANSI`.
Also, the special variable `*FEATURES*` should include the keyword `:ANSI-CL`.

On Debian based Linux distributions you can enable/disable the ANSI version using:
dpkg-reconfigure gcl

There are GCL implementations for many platforms
including MS Windows and Unix-like systems.


SBCL <https://www.sbcl.org>
--------------------------

SBCL is a fork of CMUCL which differs in some minor details,
but most notably, it is simpler to rebuild SBCL than CMUCL.
For many tasks a Maxima compiled with SBCL is considerably faster than
GCL. For other tasks GCL is faster than SBCL.

As SBCL doesn't use readline it is recommended to use rmaxima for using
a command-line Maxima with SBCL. For common details of SBCL and CMUCL
See CMUCL above.


Allegro Common Lisp <https://franz.com/products/allegro-common-lisp/>
---------------------------------------------------------------------

Maxima should work with Allegro Common Lisp, but
only limited testing has been done with these Lisp
implementations. User feedback would be welcome.


CCL <https://ccl.clozure.com/>
------------------------------

CCL, formerly known as OpenMCL, is known to work with Maxima on
all platforms where ccl runs including Linux, Mac OSX, and Windows.
There are appear to be some bugs in the 32-bit version of CCL, but
the 64-bit version passes all tests.


ECL <https://common-lisp.net/project/ecl/>
------------------------------------------

ECL is known to work with Maxima and passes the testsuite. ECL
runs on many platforms and OSes and is the lisp compiler used for
Maxima on Android. It is faster than CLISP, but seems to tend more
towards fragmenting the available memory. ECL tends to be slower
than GCL or SBCL but faster than CLISP.

ECL must be configured to use the C compiler, building Maxima with the
ECL bytecode compiler is (currently) not possible.  So do **not** use the
option `--with-cmp=no` when building ECL.


Armed Bear Common Lisp (ABCL) <https://www.abcl.org>
----------------------------------------------------

ABCL's main feature is that is tightly integrated into Java.
That also means that it is an interpreter running in a virtual machine
which makes it even slower than Clisp. Also Java doesn't automatically
convert tail-recursive function calls to loops which means that in a
few functions might run out of stack space faster than other Lisps.
