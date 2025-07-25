@c -*- mode: texinfo -*-
@menu
* Introduction to zeilberger::
* Functions and Variables for zeilberger::
@end menu

@node Introduction to zeilberger, Functions and Variables for zeilberger, Package zeilberger, Package zeilberger
@section Introduction to zeilberger

@code{zeilberger} is an implementation of Zeilberger's algorithm
for definite hypergeometric summation, and also 
Gosper's algorithm for indefinite hypergeometric
summation.

@code{zeilberger} makes use of the "filtering" optimization method developed by Axel Riese.

@code{zeilberger} was developed by Fabrizio Caruso.

@code{load ("zeilberger")} loads this package.

@opencatbox{Categories:}
@category{Sums and products}
@category{Share packages}
@category{Package zeilberger}
@closecatbox

@subsection The indefinite summation problem

@code{zeilberger} implements Gosper's algorithm for indefinite hypergeometric summation.
Given a hypergeometric term @math{F_k} in @math{k} we want to find its hypergeometric
anti-difference, that is, a hypergeometric term @math{f_k} such that

m4_displaymath(
<<<F_k = f_{k+1} - f_k.>>>,
<<<@math{F_k = f_(k+1) - f_k}.>>>)

@subsection The definite summation problem

@code{zeilberger} implements Zeilberger's algorithm for definite hypergeometric summation.
Given a proper hypergeometric term (in @math{n} and @math{k}) 
m4_math(<<<F_{n,k}>>>,<<<@math{F_(n,k)}>>>) 
and
a positive integer @math{d} we want to find a @math{d}-th order linear
recurrence with polynomial coefficients (in @math{n}) for 
m4_math(<<<F_{n,k}>>>,<<<@math{F_(n,k)}>>>) 
and
a rational function @math{R} in @math{n} and @math{k} such that

m4_displaymath(
<<<a_0 \, F_{n,k} + \ldots + a_d \, F_{n+d,k} = \Delta_K \left(R\left(n,k\right) F_{n,k}\right),>>>,
<<<@math{a_0 F_(n,k) + ... + a_d F_(n+d,k) = Delta_k(R(n,k) F_(n,k))},>>>)
where 
m4_math(\Delta_k, @math{Delta_k}) 
is the @math{k}-forward difference
operator, i.e., 
m4_mathdot(
<<<\Delta_k \left(t_k\right) \equiv t_{k+1} - t_k>>>,
<<<@math{Delta_k(t_k) := t_(k+1) - t_k}>>>)

@subsection Verbosity levels

There are also verbose versions of the commands
which are called by adding one of the following prefixes:

@table @code
@item Summary
Just a summary at the end is shown
@item Verbose
Some information in the intermediate steps
@item VeryVerbose
More information
@item Extra
Even more information including information on
the linear system in Zeilberger's algorithm
@end table

For example:@*
@code{GosperVerbose}, @code{parGosperVeryVerbose},
@code{ZeilbergerExtra}, @code{AntiDifferenceSummary}.


@node Functions and Variables for zeilberger, , Introduction to zeilberger, Package zeilberger
@section Functions and Variables for zeilberger

@anchor{AntiDifference}
@deffn {Function} AntiDifference (@math{F_k}, @var{k})

Returns the hypergeometric anti-difference of @math{F_k}, if it exists.@*
Otherwise @code{AntiDifference} returns @code{no_hyp_antidifference}.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end deffn

@anchor{Gosper}
@deffn {Function} Gosper (@math{F_k}, @var{k})
Returns the rational certificate @math{R(k)} for @math{F_k}, that is,
a rational function such
that 
m4_mathcomma(<<<F_k = R\left(k+1\right) \, F_{k+1} - R\left(k\right) \, F_k>>>,<<<@math{F_k = R(k+1) F_(k+1) - R(k) F_k}>>>) 
if it exists.
Otherwise, @code{Gosper} returns @code{no_hyp_sol}.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end deffn

@anchor{GosperSum}
@deffn {Function} GosperSum (@math{F_k}, @var{k}, @var{a}, @var{b})

Returns the summation of @math{F_k} from @math{@var{k} = @var{a}} to @math{@var{k} = @var{b}}
if @math{F_k} has a hypergeometric anti-difference.
Otherwise, @code{GosperSum} returns @code{nongosper_summable}.

Examples:

@c ===beg===
@c load ("zeilberger")$
@c GosperSum ((-1)^k*k / (4*k^2 - 1), k, 1, n);
@c GosperSum (1 / (4*k^2 - 1), k, 1, n);
@c GosperSum (x^k, k, 1, n);
@c GosperSum ((-1)^k*a! / (k!*(a - k)!), k, 1, n);
@c GosperSum (k*k!, k, 1, n);
@c GosperSum ((k + 1)*k! / (k + 1)!, k, 1, n);
@c GosperSum (1 / ((a - k)!*k!), k, 1, n);
@c ===end===
@example
(%i1) load ("zeilberger")$
@group
(%i2) GosperSum ((-1)^k*k / (4*k^2 - 1), k, 1, n);
                           n + 1      3
                      (- 1)      (n + -)
                                      2    1
(%o2)               - ------------------ - -
                                  2        4
                      2 (4 (n + 1)  - 1)
@end group
@group
(%i3) GosperSum (1 / (4*k^2 - 1), k, 1, n);
                                3
                          - n - -
                                2       1
(%o3)                  -------------- + -
                                2       2
                       4 (n + 1)  - 1
@end group
@group
(%i4) GosperSum (x^k, k, 1, n);
                          n + 1
                         x          x
(%o4)                    ------ - -----
                         x - 1    x - 1
@end group
@group
(%i5) GosperSum ((-1)^k*a! / (k!*(a - k)!), k, 1, n);
                     n + 1
                (- 1)      a! (n + 1)         a!
(%o5)       - ------------------------- - ----------
              a (- n + a - 1)! (n + 1)!   (a - 1)! a
@end group
@group
(%i6) GosperSum (k*k!, k, 1, n);
(%o6)                     (n + 1)! - 1
@end group
@group
(%i7) GosperSum ((k + 1)*k! / (k + 1)!, k, 1, n);
                  (n + 1) (n + 2) (n + 1)!
(%o7)             ------------------------ - 1
                          (n + 2)!
@end group
@group
(%i8) GosperSum (1 / ((a - k)!*k!), k, 1, n);
(%o8)                  NON_GOSPER_SUMMABLE
@end group
@end example

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end deffn

@iftex
@anchor{parGosper}
@deffn {Function} parGosper (@math{F_{n,k}}, @var{k}, @var{n}, @var{d})

Attempts to find a @var{d}-th order recurrence for
@tex
$F_{n,k}$.
@end tex

The algorithm yields a sequence @math{[s_1, s_2, ..., s_m]} of solutions.
Each solution has the form

@tex
$$\left[R\left(n, k\right), \left[a_0, a_1, \ldots, a_d\right]\right].$$
@end tex

@code{parGosper} returns @code{[]} if it fails to find a recurrence.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end deffn
@end iftex

@ifnottex
@anchor{parGosper}
@deffn {Function} parGosper (@math{F_(n,k)}, @var{k}, @var{n}, @var{d})

Attempts to find a @var{d}-th order recurrence for @math{F_(n,k)}.

The algorithm yields a sequence @math{[s_1, s_2, ..., s_m]} of solutions.
Each solution has the form

@math{[R(n, k), [a_0, a_1, ..., a_d]].}

@code{parGosper} returns @code{[]} if it fails to find a recurrence.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end deffn
@end ifnottex

@iftex
@anchor{Zeilberger}
@deffn {Function} Zeilberger (@math{F_{n,k}}, @var{k}, @var{n})

Attempts to compute the indefinite hypergeometric summation of
@tex
$F_{n,k}$.
@end tex

@code{Zeilberger} first invokes @code{Gosper}, and if that fails to find a solution, then invokes
@code{parGosper} with order 1, 2, 3, ..., up to @code{MAX_ORD}.
If Zeilberger finds a solution before reaching @code{MAX_ORD},
it stops and returns the solution.

The algorithms yields a sequence @math{[s_1, s_2, ..., s_m]} of solutions.
Each solution has the form

@tex
$$\left[R\left(n, k\right), \left[a_0, a_1, \ldots, a_d\right]\right].$$
@end tex

@code{Zeilberger} returns @code{[]} if it fails to find a solution.

@code{Zeilberger} invokes @code{Gosper} only if @code{Gosper_in_Zeilberger} is @code{true}.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end deffn
@end iftex

@ifnottex
@anchor{Zeilberger}
@deffn {Function} Zeilberger (@math{F_(n,k)}, @var{k}, @var{n})

Attempts to compute the indefinite hypergeometric summation of @math{F_(n,k)}.

@code{Zeilberger} first invokes @code{Gosper}, and if that fails to find a solution, then invokes
@code{parGosper} with order 1, 2, 3, ..., up to @code{MAX_ORD}.
If Zeilberger finds a solution before reaching @code{MAX_ORD},
it stops and returns the solution.

The algorithms yields a sequence @math{[s_1, s_2, ..., s_m]} of solutions.
Each solution has the form

@math{[R(n,k), [a_0, a_1, ..., a_d]].}

@code{Zeilberger} returns @code{[]} if it fails to find a solution.

@code{Zeilberger} invokes @code{Gosper} only if @code{Gosper_in_Zeilberger} is @code{true}.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end deffn
@end ifnottex


@node General global variables, Variables related to the modular test, Functions and Variables for zeilberger
@section General global variables

@anchor{MAX_ORD}
@defvr {Global variable} MAX_ORD
Default value: 5

@code{MAX_ORD} is the maximum recurrence order attempted by @code{Zeilberger}.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end defvr

@anchor{simplified_output}
@defvr {Global variable} simplified_output
Default value: @code{false}

When @code{simplified_output} is @code{true},
functions in the @code{zeilberger} package attempt
further simplification of the solution.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end defvr

@anchor{linear_solver}
@defvr {Global variable} linear_solver
Default value: @code{linsolve}

@code{linear_solver} names the solver which is used to solve the system
of equations in Zeilberger's algorithm.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end defvr

@anchor{warnings}
@defvr {Global variable} warnings
Default value: @code{true}

When @code{warnings} is @code{true},
functions in the @code{zeilberger} package print
warning messages during execution.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end defvr

@anchor{Gosper_in_Zeilberger}
@defvr {Global variable} Gosper_in_Zeilberger
Default value: @code{true}

When @code{Gosper_in_Zeilberger} is @code{true},
the @code{Zeilberger} function calls @code{Gosper} before calling @code{parGosper}.
Otherwise, @code{Zeilberger} goes immediately to @code{parGosper}.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end defvr

@anchor{trivial_solutions}
@defvr {Global variable} trivial_solutions
Default value: @code{true}

When @code{trivial_solutions} is @code{true},
@code{Zeilberger} returns solutions
which have certificate equal to zero, or all coefficients equal to zero.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end defvr

@node Variables related to the modular test, , General global variables
@section Variables related to the modular test

@anchor{mod_test}
@defvr {Global variable} mod_test
Default value: @code{false}

When @code{mod_test} is @code{true},
@code{parGosper} executes a
modular test for discarding systems with no solutions.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end defvr

@anchor{modular_linear_solver}
@defvr {Global variable} modular_linear_solver
Default value: @code{linsolve}

@code{modular_linear_solver} names the linear solver used by the modular test in @code{parGosper}.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end defvr

@anchor{ev_point}
@defvr {Global variable} ev_point
Default value: @code{big_primes[10]}

@code{ev_point} is the value at which the variable @var{n} is evaluated
when executing the modular test in @code{parGosper}.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end defvr

@anchor{mod_big_prime}
@defvr {Global variable} mod_big_prime
Default value: @code{big_primes[1]}

@code{mod_big_prime} is the modulus used by the modular test in @code{parGosper}.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end defvr

@anchor{mod_threshold}
@defvr {Global variable} mod_threshold
Default value: 4

@code{mod_threshold} is the
greatest order for which the modular test in @code{parGosper} is attempted.

@opencatbox{Categories:}
@category{Package zeilberger}
@closecatbox

@end defvr

