;;;  -*- LISP -*-
;;;	** (c) Copyright 1979 Massachusetts Institute of Technology **

(in-package :maxima)

;;; References:
;;; 
;;; Definite integration using the generalized hypergeometric functions
;;; Avgoustis, Ioannis Dimitrios
;;; Thesis. 1977. M.S.--Massachusetts Institute of Technology. Dept. 
;;; of Electrical Engineering and Computer Science
;;; http://dspace.mit.edu/handle/1721.1/16269
;;;
;;; Avgoustis, I. D., Symbolic Laplace Transforms of Special Functions,
;;; Proceedings of the 1977 MACSYMA Users' Conference, pp 21-41

(macsyma-module hyp)

(defvar *debug-hyp* nil)

(defmvar $prefer_whittaker nil)

;; When T give result in terms of gamma_incomplete and not gamma_incomplete_lower
(defmvar $prefer_gamma_incomplete nil)

;; When NIL do not automatically expand polynomials as a result
(defmvar $expand_polynomials t)

(eval-when
    (:execute :compile-toplevel)
    (defmacro simp (x) `(simplifya ,x ()))

    ;; The macro MABS has been renamed to HYP-MABS in order to
    ;; avoid conflict with the Maxima symbol MABS. The other
    ;; M* macros defined here should probably be similarly renamed
    ;; for consistency. jfa 03/27/2002

    (defmacro hyp-mabs (x) `(simp `((mabs) ,,x)))

    (defmacro msqrt (x) `(m^t ,x 1//2))

    (defmacro mexpt (x) `(m^t '$%e ,x))

    (defmacro mlog (x) `(simp `((%log) ,,x)))

    (defmacro msin (x) `(simp `((%sin) ,,x)))

    (defmacro mcos (x) `(simp `((%cos) ,,x)))

    (defmacro masin (x) `(simp `((%asin) ,,x)))

    (defmacro matan (x) `(simp `((%atan) ,,x)))

    (defmacro mgamma (x) `(simp `((%gamma) ,,x)))

    (defmacro mbinom (x y) `(simp `((%binomial) ,,x ,,y)))

    (defmacro merf (x) `(simp `((%erf) ,,x)))

    (defmacro =1//2 (x) `(alike1 ,x 1//2))
    )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Functions moved from hypgeo.lisp to this place.
;;; These functions are no longer used in hypgeo.lisp.

;; Gamma function
(defun gm (expr)
  (simplifya (list '(%gamma) expr) nil))

;; sin(x)
(defun sin% (arg)
  (list '(%sin) arg))

;; cos(x)
(defun cos% (arg)
  (list '(%cos) arg))

;; Test if X is a number, either Lisp number or a maxima rational.
(defun nump (x)
  (cond ((atom x)
         (numberp x))
        ((not (atom x))
         (eq (caar (simplifya x nil)) 'rat))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun hyp-integerp (x)
  ;; In this file, maxima-integerp was used in many places.  But it
  ;; seems that this code expects maxima-integerp to return T when it
  ;; is really an integer, not something that was declared an integer.
  ;; But I'm not really sure if this is true everywhere, but it is
  ;; true in some places.
  ;;
  ;; Thus, we replace all calls to maxima-integerp with hyp-integerp,
  ;; which, for now, returns T only when the arg is an integer.
  ;; Should we do something more?
  (and (maxima-integerp x) (integerp x)))

;; Main entry point for simplification of hypergeometric functions.
;;
;; F(a1,a2,a3,...;b1,b2,b3;z)
;;
;; L1 is a (maxima) list of an's, L2 is a (maxima) list of bn's.
(defmfun $hgfred (arg-l1 arg-l2 arg)
  (flet ((arg-ok (a)
	   (and (listp a)
		(eq (caar a) 'mlist))))
    (unless (arg-ok arg-l1)
      (merror (intl:gettext "hgfred: first argument must be a list; found: ~:M") arg-l1))
    (unless (arg-ok arg-l2)
      (merror (intl:gettext "hgfred: second argument must be a list; found: ~:M") arg-l2)))
  
  ;; Do we really want $radexpand set to '$all?  This is probably a
  ;; bad idea in general, but we'll leave this in for now until we can
  ;; verify find all of the code that does or does not need this and
  ;; until we can verify all of the test cases are correct.
  (let (;;($radexpand '$all)
	(*par* arg)
	(*checkcoefsignlist* nil))
    (hgfsimp-exec (cdr arg-l1) (cdr arg-l2) arg)))

(defun hgfsimp-exec (arg-l1 arg-l2 arg)
  (let* ((l1 (copy-tree arg-l1))
	 (l2 (copy-tree arg-l2))
	 ($exponentialize nil)
	 (res (hgfsimp l1 l2 arg)))
    ;; I think hgfsimp returns FAIL and UNDEF for cases where it
    ;; couldn't reduce the function.
    (cond ((eq res 'fail)
	   (fpqform l1 l2 arg))
	  ((eq res 'undef)
	   '$und)
	  (t
	   res))))

(defun hgfsimp (arg-l1 arg-l2 arg)
  (prog (resimp listcmdiff)
     (setq arg-l1 (macsimp arg-l1)
           arg-l2 (macsimp arg-l2)
           resimp (simpg arg-l1 arg-l2 arg))
     (cond ((not (eq (and (consp resimp) (car resimp)) 'fail))
            (return resimp))
           ((and (not (zerop1 arg)) ; Do not call splitfpq for a zero argument
                 (setq listcmdiff
                       (intdiffl1l2 (cadr resimp) (caddr resimp))))
            (return (splitpfq listcmdiff
                              (cadr resimp)
                              (caddr resimp)
                              arg)))
           (t
            (return (dispatch-spec-simp (cadr resimp) 
                                        (caddr resimp)
                                        arg))))))

(defun macsimp (expr)
  (mapcar #'(lambda (index) ($expand index)) expr))

;; Simplify the parameters.  If L1 and L2 have common elements, remove
;; them from both L1 and L2.
(defun simpg (arg-l1 arg-l2 arg)
  (let ((il (zl-intersection arg-l1 arg-l2)))
    (cond ((null il)
	   (simpg-exec arg-l1 arg-l2 arg))
	  (t
	   (simpg-exec (del il arg-l1)
		       (del il arg-l2)
                       arg)))))

(defun del (a b)
  (cond ((null a) b)
	(t
	 (del (cdr a) (delete (car a) b :count 1 :test #'equal)))))

;; Handle the simple cases where the result is either a polynomial, or
;; is undefined because we divide by zero.
(defun simpg-exec (arg-l1 arg-l2 arg)
  (let (n)
    (cond ((zerop-in-l arg-l1)
	   ;; A zero in the first index means the series terminates
	   ;; after the first term, so the result is always 1.
	   1)
	  ((setq n (hyp-negp-in-l arg-l1))
	   ;; A negative integer in the first series means we have a
	   ;; polynomial.
	   (create-poly arg-l1 arg-l2 n arg))
	  ((and (or (zerop-in-l arg-l2)
		    (hyp-negp-in-l arg-l2))
		(every #'mnump arg-l1)
		(every #'mnump arg-l2))
	   ;; A zero or negative number in the second index means we
	   ;; eventually divide by zero, so we're undefined.  But only
	   ;; do this if both indices contain numbers.  See Bug
	   ;; 1858964 for discussion.
	   'undef)
	  (t
	   ;; We failed so more complicated stuff needs to be done.
	   (append (list 'fail) (list arg-l1) (list arg-l2))))))

(defun intdiffl1l2 (arg-l1 arg-l2)
  (cond ((null arg-l1)
	 nil)
	(t
	 (intdiff arg-l1 arg-l2))))

;; For each element x in arg-l1 and y in arg-l2, compute d = x - y.
;; Find the smallest such non-negative integer d and return (list x
;; d).
(defun intdiff (arg-l1 arg-l2)
  (let ((result nil))
    ;; Compute all possible differences between elements in arg-l1 and
    ;; arg-l2.  Only save the ones where the difference is a positive
    ;; integer
    (dolist (x arg-l1)
      (dolist (y arg-l2)
	(let ((diff (sub x y)))
	  (when (nni diff)
	    (push (list x diff) result)))))
    ;; Find the smallest one and return it.
    (let ((min (first result)))
      (dolist (x (rest result))
	(when (< (second x) (second min))
	  (setf min x)))
      min)))

;; Create the appropriate polynomial for the hypergeometric function.
(defun create-poly (arg-l1 arg-l2 n arg)
  (let ((len1 (length arg-l1))
	(len2 (length arg-l2)))
    ;; n is the smallest (in magnitude) negative integer in L1.  To
    ;; make everything come out right, we need to make sure this value
    ;; is first in L1.  This is ok, the definition of the
    ;; hypergeometric function does not depend on the order of values
    ;; in L1.
    (setf arg-l1 (cons n (remove n arg-l1 :count 1)))
    (cond ((and (equal len1 2)
		(equal len2 1))
	   (2f1polys arg-l1 arg-l2 n arg))
	  ((and (equal len1 1)
		(equal len2 1))
	   (1f1polys arg-l2 n arg))
	  ((and (equal len1 2)
		(zerop len2))
	   (2f0polys arg-l1 n arg))
	  (t (create-any-poly arg-l1 arg-l2 (mul -1 n) arg)))))

(defun 1f1polys (arg-l2 n arg)
  (let* ((c (car arg-l2))
	 (n (mul -1 n))
	 (fact1 (mul (power 2 n)
		     (take '(mfactorial) n)
		     (inv (power -1 n))))
	 ;; For all of the polynomials here, I think it's ok to
	 ;; replace sqrt(z^2) with z because when everything is
	 ;; expanded out they evaluate to exactly the same thing.  So
	 ;; $radexpand $all is ok here.
	 (fact2 (let (($radexpand '$all))
		  (mul (power 2 '((rat simp) 1 2))
		       (power arg '((rat simp) 1 2))))))
    (cond ((alike1 c '((rat simp) 1 2))
	   ;; A&S 22.5.56
	   ;; hermite(2*n,x) = (-1)^n*(2*n)!/n!*M(-n,1/2,x^2)
	   ;;
	   ;; So
	   ;; M(-n,1/2,x) = n!/(2*n)!*(-1)^n*hermite(2*n,sqrt(x))
	   ;;
	   ;; But hermite(m,x) = 2^(m/2)*He(sqrt(2)*sqrt(x)), so
	   ;;
	   ;; M(-n,1/2,x) = (-1)^n*n!*2^n/(2*n)!*He(2*n,sqrt(2)*sqrt(x))
	   (mul fact1
		(inv (take '(mfactorial) (add n n)))
		(hermpol (add n n) fact2)))
	  ((alike1 c '((rat simp) 3 2))
	   ;; A&S 22.5.57
	   ;; hermite(2*n+1,x) = (-1)^n*(2*n+1)!/n!*M(-n,3/2,x^2)*2*x
	   ;;
	   ;; So
	   ;; M(-n,3/2,x) = n!/(2*n+1)!*(-1)^n*hermite(2*n+1,sqrt(x))/2/sqrt(x)
	   ;;
	   ;; and in terms of He, we get
	   ;;
	   ;; M(-n,3/2,x) = (-1)^n*n!*2^(n-1/2)/(2*n+1)!/sqrt(x)*He(2*n+1,sqrt(2)*sqrt(x))
	   (mul fact1
		(inv (power 2 '((rat simp) 1 2)))
		(inv (take '(mfactorial) (add n n 1)))
		(hermpol (add n n 1) fact2)
		;; Similarly, $radexpand here is ok to convert sqrt(z^2) to z.
		(let (($radexpand '$all))
		  (inv (power arg '((rat simp) 1 2))))))
          ((alike1 c (neg (add n n)))
           ;; 1F1(-n; -2*n; z)
           (mul (power -1 n)
                (inv (take '(%binomial) (add n n) n))
                (lagpol n (sub c 1) arg)))
	  (t
	   ;; A&S 22.5.54:
	   ;;
	   ;; gen_laguerre(n,alpha,x) =
	   ;; binomial(n+alpha,n)*hgfred([-n],[alpha+1],x);
	   ;;
	   ;; Or hgfred([-n],[alpha],x) =
	   ;; gen_laguerre(n,alpha-1,x)/binomial(n+alpha-1,n)
	   ;;
	   ;; But 1/binomial(n+alpha-1,n) = n!*(alpha-1)!/(n+alpha-1)!
	   ;;    = n! / (alpha * (alpha + 1) * ... * (alpha + n - 1)
	   ;;    = n! / poch(alpha, n)
	   ;;
	   ;; See Bug 1858939.
	   ;;
	   ;; However, if c is not a number leave the result in terms
	   ;; of gamma functions.  I (rtoy) think this makes for a
	   ;; simpler result, especially if n is rather large.  If the
	   ;; user really wants the answer expanded out, makefact and
	   ;; minfactorial will do that.
	   (if (and (integerp n)
	            (numberp c))
	       (if (or (zerop c)
	               (and (minusp c) (> c (- n))))
	           (merror (intl:gettext "hgfred: 1F1(~M; ~M; ~M) not defined.")
	                   (- n) c arg)
	           (mul (take '(mfactorial) n)
	                (inv (take '($pochhammer) c n))
	                (lagpol n (sub c 1) arg)))
	       (let (($gamma_expand t)) ; Expand Gamma function
	         (mul (take '(mfactorial) n)
	              (take '(%gamma) c)
	              (inv (take '(%gamma) (add c n)))
	              (lagpol n (sub c 1) arg))))))))

;; Hermite polynomial.  Note: The Hermite polynomial used here is the
;; He polynomial, defined as (A&S 22.5.18, 22.5.19)
;;
;; He(n,x) = 2^(-n/2)*H(n,x/sqrt(2))
;;
;; or
;;
;; H(n,x) = 2^(n/2)*He(x*sqrt(2))
;;
;; We want to use H, as used in specfun, so we need to convert it.
(defun hermpol (n arg)
  (let ((fact (inv (power 2 (div n 2))))
        (x (mul arg (inv (power 2 '((rat simp) 1 2))))))
    (mul fact 
         (if (and $expand_polynomials (integerp n))
             (mfuncall '$hermite n x)
             (list '($hermite simp) n x)))))

;; Generalized Laguerre polynomial
(defun lagpol (n a arg)
  (if (and (numberp a) (zerop a))
      (if (and $expand_polynomials (integerp n))
          (mfuncall '$laguerre n arg)
          (list '($laguerre simp) n arg))
      (if (and $expand_polynomials (integerp n))
          (mfuncall '$gen_laguerre n a arg)
          (list '($gen_laguerre simp) n a arg))))

(defun 2f0polys (arg-l1 n arg)
  (let ((a (car arg-l1))
	(b (cadr arg-l1)))
    (when (alike1 (sub b a) '((rat simp) -1 2))
      (rotatef a b))
    (cond ((alike1 (sub b a) '((rat simp) 1 2))
	   ;; 2F0(-n,-n+1/2,z) or 2F0(-n-1/2,-n,z)
	   (interhermpol n a b arg))
	  (t
	   ;; 2F0(a,b;z)
	   (let ((x (mul -1 (inv arg)))
		 (order (mul -1 n)))
	     (mul (take '(mfactorial) order)
		  (inv (power x order))
		  (inv (power -1 order))
		  (lagpol order (mul -1 (add b order)) x)))))))

;; Compute 2F0(-n,-n+1/2;z) and 2F0(-n-1/2,-n;z) in terms of Hermite
;; polynomials.
;;
;; Ok.  I couldn't find any references giving expressions for this, so
;; here's a quick derivation.
;;
;; 2F0(-n,-n+1/2;z) = sum(pochhammer(-n,k)*pochhammer(-n+1/2,k)*z^k/k!, k, 0, n)
;;
;; It's easy to show pochhammer(-n,k) = (-1)^k*n!/(n-k)!
;; Also, it's straightforward but tedious to show that
;; pochhammer(-n+1/2,k) = (-1)^k*(2*n)!*(n-k)!/2^(2*k)/n!/(2*n-2*k)!
;;
;; Thus,
;; 2F0 = (2*n)!*sum(z^k/2^(2*k)/k!/(2*n-2*k)!)
;;
;; Compare this to the expression for He(2*n,x) (A&S 22.3.11):
;;
;; He(2*n,x) = (2*n)! * x^(2*n) * sum((-1)^k*x^(-2*k)/2^k/k!/(2*n-2*k)!)
;;
;; Hence,
;;
;; 2F0(-n,-n+1/2;z) = y^n * He(2*n,y)
;;
;; where y = sqrt(-2/x)
;;
;; For 2F0(-n-1/2,-n;z) = sum(pochhammer(-n,k)*pochhammer(-n-1/2,k)*z^k/k!)
;; we find that
;;
;; pochhammer(-n-1/2,k) = pochhammer(-(n+1)+1/2,k)
;;  = 
;;
;; So 2F0 = (2*n+1)!*sum(z^k/z^(2*k)/k!/(2*n+1-2*k)!)
;;
;; and finally
;;
;; 2F0(-n-1/2,-n;z) = y^(2*n+1) * He(2*n+1,y)
;;
;; with y as above.
(defun interhermpol (n a b x)
  (let ((arg (power (div 2 (mul -1 x)) '((rat simp) 1 2)))
	(order (cond ((alike1 a n)
		      (mul -2 n))
		     ((alike1 b n)
		      (sub 1 (add n n))))))
    ;; 2F0(-n,-n+1/2;z) = y^(-2*n)*He(2*n,y)
    ;; 2F0(-n-1/2,-n;z) = y^(-(2*n+1))*He(2*n+1,y)
    ;;
    ;; where y = sqrt(-2/var);
    (mul (power arg (mul -1 order))
	 (hermpol order arg))))

;; F(n,b;c;z), where n is a negative integer (number or symbolic).
;; The order of the arguments must be checked by the calling routine. 
(defun 2f1polys (arg-l1 arg-l2 n arg)
  (prog (l v lgf)
     ;; Since F(a,b;c;z) = F(b,a;c;z), make sure L1 has the negative
     ;; integer first, so we have F(-n,d;c;z)
     ;; Remark: 2f1polys is only called from create-poly. create-poly calls
     ;; 2f1polys with the correct order of arg-l1. This test is not necessary.
;     (cond ((not (alike1 (car arg-l1) n))
;	    (setq arg-l1 (reverse arg-l1))))

     (cond ((mnump *par*)
            ;; The argument of the hypergeometric function is a number.
            ;; Avoid the following check which does not work for this case.
            (setq v (div (add (cadr arg-l1) n) 2)))
           (t
            ;; Check if (b+n)/2 is free of the argument.
            ;; At this point of the code there is no check of the return value
            ;; of vfvp. When nil we have no solution and the result is wrong.
            (setq l (vfvp (div (add (cadr arg-l1) n) 2) arg))
            (setq v (cdr (assoc 'v l :test #'equal)))))
     
     (cond ((and (or (not (integerp n))
                     (not $expand_polynomials))
                 ;; Assuming we have F(-n,b;c;z), then v is (b+n)/2.
                 ;; See if it can be a Legendre function.
                 ;; We call legpol-core because we know that arg-l1 has the
                 ;; correct order. This avoids questions about the parameter b
                 ;; from legpol-core, because legpol calls legpol-core with
                 ;; both order of arguments.
                 (setq lgf (legpol-core (car arg-l1) 
                                        (cadr arg-l1) 
                                        (car arg-l2)
                                        arg)))
            (return lgf))
           ((and (or (not (integerp n))
                     (not $expand_polynomials))
                 (alike1 (sub (car arg-l2) v) '((rat simp) 1 2)))
	    ;; A&S 15.4.5:
	    ;; F(-n, n+2*a; a+1/2; x) = n!*gegen(n, a, 1-2*x)/pochhammer(2*a,n)
	    ;;
	    ;; So v = a, and (car arg-l2) = a + 1/2.
	    (return (mul 
		     (cond ((zerop1 v) 1)
			   (t (mul (take '(mfactorial) (mul -1 n))
			           (inv (take '($pochhammer)
			                      (mul 2 v)
			                      (mul -1 n))))))
		     (gegenpol (mul -1 n)
			       v
			       (sub 1 (mul 2 *par*))))))
           (t
            ;; A&S 15.4.6 says
            ;; F(-n, n + a + 1 + b; a + 1; x)
            ;;   = n!*jacobi_p(n,a,b,1-2*x)/pochhammer(a+1,n)
            (return (mul (take '(mfactorial) (mul -1 n))
                         (inv (take '($pochhammer) (car arg-l2) (mul -1 n)))
                         (jacobpol (mul -1 n)
			           (add (car arg-l2) -1)
			           (sub (mul 2 v) (car arg-l2))
                                   (sub 1 (mul 2 *par*)))))))))

;; Jacobi polynomial
(defun jacobpol (n a b x)
  (if (and $expand_polynomials (integerp n))
      (mfuncall '$jacobi_p n a b x)
      (list '($jacobi_p simp) n a b x)))

;; Gegenbauer (Ultraspherical) polynomial.  We use ultraspherical to
;; match specfun.
(defun gegenpol (n v x)
  (cond ((equal v 0) (tchebypol n x))
        (t
         (if (and $expand_polynomials (integerp n))
             (mfuncall '$ultraspherical n v x)
             `(($ultraspherical simp) ,n ,v ,x)))))

;; Legendre polynomial
(defun legenpol (n x)
  (if (and $expand_polynomials (integerp n))
      (mfuncall '$legendre_p n x)
      `(($legendre_p simp) ,n ,x)))

;; Chebyshev polynomial
(defun tchebypol (n x)
  (if (and $expand_polynomials (integerp n))
      (mfuncall '$chebyshev_t n x)
      `(($chebyshev_t simp) ,n ,x)))

;; Expand the hypergeometric function as a polynomial.  No real checks
;; are made to ensure the hypergeometric function reduces to a
;; polynomial.
(defmfun $hgfpoly (arg-l1 arg-l2 arg)
  (let ((*par* arg)
	(n (hyp-negp-in-l (cdr arg-l1))))
    (create-any-poly (cdr arg-l1) (cdr arg-l2) (- n) arg)))

(defun create-any-poly (arg-l1 arg-l2 n arg)
  (prog (result exp prodnum proden)
     (setq result 1 prodnum 1 proden 1 exp 1)
     loop
     (cond ((zerop n) (return result)))
     (setq prodnum (mul prodnum (mull arg-l1))
	   proden (mul proden (mull arg-l2)))
     (setq result
	   (add result
		(mul prodnum
		     (power arg exp)
		     (inv proden)
		     (inv (factorial exp)))))
     (setq n (sub n 1)
	   exp (add exp 1)
	   arg-l1 (incr1 arg-l1)
	   arg-l2 (incr1 arg-l2))
     (go loop)))

;; Compute the product of the elements of the list L.
(defun mull (l)
 (reduce #'mul l :initial-value 1))

;; Add 1 to each element of the list L
(defun incr1 (l)
  (mapcar #'(lambda (x) (add x 1)) l))

;; Figure out the orders of generalized hypergeometric function we
;; have and call the right simplifier.
(defun dispatch-spec-simp (arg-l1 arg-l2 arg)
  (let  ((len1 (length arg-l1))
	 (len2 (length arg-l2)))
    (cond ((and (< len1 2)
		(< len2 2))
	   ;; pFq where p and q < 2.
	   (simp2>f<2 arg-l1 arg-l2 len1 len2 arg))
	  ((and (equal len1 2)
		(equal len2 1))
	   ;; 2F1
	   (simp2f1 arg-l1 arg-l2 arg))
          ((and (equal len1 2)
                (equal len2 0))
           ;; 2F0(a,b; ; z)                
           (cond ((and (maxima-integerp (car arg-l1))
                       (member ($sign (car arg-l1)) '($neg $nz)))
                  ;; 2F0(-n,b; ; z), n a positive integer
                  (2f0polys arg-l1 (car arg-l1) arg))
                 ((and (maxima-integerp (cadr arg-l1))
                       (member ($sign (cadr arg-l1)) '($neg $nz)))
                  ;; 2F0(a,-n; ; z), n a positive integer
                  (2f0polys (reverse arg-l1) (cadr arg-l1) arg))
                 (t
                  (fpqform arg-l1 arg-l2 arg))))
	  ((and (= len1 1)
		(= len2 2))
	  ;; Some 1F2 forms
	   (simp1f2 arg-l1 arg-l2 arg))
	  ((and (= len1 2)
		(= len2 2))
	   (simp2f2 arg-l1 arg-l2 arg))
	  (t
	   ;; We don't have simplifiers for any other hypergeometric
	   ;; function.
	   (fpqform arg-l1 arg-l2 arg)))))

;; Handle the cases where the number of indices is less than 2.
(defun simp2>f<2 (arg-l1 arg-l2 len1 len2 arg)
  (cond ((and (zerop len1) (zerop len2))
	 ;; hgfred([],[],z) = e^z
         (power '$%e arg))
        ((and (zerop len1) (equal len2 1))
         (cond 
           ((zerop1 arg)
            ;; hgfred([],[b],0) = 1
            (add arg 1))
           (t
            ;; hgfred([],[b],z)
            ;;
            ;; The hypergeometric series is then
            ;;
            ;; 1+sum(z^k/k!/[b*(b+1)*...(b+k-1)], k, 1, inf)
            ;;
            ;; = 1+sum(z^k/k!*gamma(b)/gamma(b+k), k, 1, inf)
            ;; = sum(z^k/k!*gamma(b)/gamma(b+k), k, 0, inf)
            ;; = gamma(b)*sum(z^k/k!/gamma(b+k), k, 0, inf)
            ;;
            ;; Note that bessel_i(b,z) has the series
            ;;
            ;; (z/2)^(b)*sum((z^2/4)^k/k!/gamma(b+k+1), k, 0, inf)
            ;;
            ;; bessel_i(b-1,2*sqrt(z))
            ;;    = (sqrt(z))^(b-1)*sum(z^k/k!/gamma(b+k),k,0,inf)
            ;;    = z^((b-1)/2)*hgfred([],[b],z)/gamma(b)
            ;;
            ;; So this hypergeometric series is a Bessel I function:
            ;;
            ;; hgfred([],[b],z) = bessel_i(b-1,2*sqrt(z))*z^((1-b)/2)*gamma(b)
            (bestrig (car arg-l2) arg))))
	((zerop len2)
	 ;; hgfred([a],[],z) = 1 + sum(binomial(a+k,k)*z^k) = 1/(1-z)^a
	 (power (sub 1 arg) (mul -1 (car arg-l1))))
	(t
	 ;; The general case of 1F1, the confluent hypergeomtric function.
	 (confl arg-l1 arg-l2 arg))))

;; Computes 
;;
;; bessel_i(a-1,2*sqrt(x))*gamma(a)*x^((1-a)/2)
;;
;; if x > 0
;;
;; or
;;
;; bessel_j(a-1,2*sqrt(x))*gamma(a)*x^((1-a)/2)
;;
;; if x < 0.
;;
;; If a is half of an odd integer and small enough, the Bessel
;; functions are expanded in terms of trig or hyperbolic functions.

(defun bestrig (b x)
  ;; I think it's ok to have $radexpand $all here so that sqrt(z^2) is
  ;; converted to z.
  (let (($radexpand '$all))
    (if (mminusp x)
        ;; gamma(b)*(-x)^((1-b)/2)*bessel_j(b-1,2*sqrt(-x))
        (sratsimp (mul (power (neg x) (div (sub 1 b) 2))
                  (take '(%gamma) b)
                  (take '(%bessel_j)
                        (sub b 1) 
                        (mul 2 (power (neg x) '((rat simp) 1 2))))))
        ;; gamma(b)*(x)^((1-b)/2)*bessel_i(b-1,2*sqrt(x))        
        (sratsimp (mul (power x (div (sub 1 b) 2))
                  (take '(%gamma) b)
                  (take '(%bessel_i)
                        (sub b 1)
                        (mul 2 (power x '((rat simp) 1 2)))))))))

;; Kummer's transformation.  A&S 13.1.27
;;
;; M(a,b,z) = e^z*M(b-a,b,-z)
(defun kummer (arg-l1 arg-l2 arg)
  (mul (list '(mexpt) '$%e arg)
       (confl (list (sub (car arg-l2) (car arg-l1)))
	      arg-l2 (mul -1 arg))))

;; Return non-NIL if any element of the list L is zero.

(defun zerop-in-l (l)
  (some #'(lambda (x)
	    (and (numberp x) (zerop x)))
	l))

;; If the list L contains a negative integer, return the most positive
;; of the negative integers.  Otherwise return NIL.
(defun hyp-negp-in-l (l)
  (let ((max-neg nil))
    (dolist (x l)
      (when (and (integerp x) (minusp x))
	(if max-neg
	    (setf max-neg (max max-neg x))
	    (setf max-neg x))))
    max-neg))

;; Compute the intersection of L1 and L2, possibly destructively
;; modifying L2.  Preserves duplications in L1.
(defun zl-intersection (arg-l1 arg-l2)
  (cond ((null arg-l1) nil)
	((member (car arg-l1) arg-l2 :test #'equal)
	 (cons (car arg-l1)
	       (zl-intersection (cdr arg-l1)
				(delete (car arg-l1) arg-l2 :count 1 :test #'equal))))
	(t (zl-intersection (cdr arg-l1) arg-l2))))

;; Whittaker M function.  A&S 13.1.32 defines it as
;;
;; %m[k,u](z) = exp(-z/2)*z^(u+1/2)*M(1/2+u-k,1+2*u,z)
;;
;; where M is the confluent hypergeometric function.
(defun whitfun (k m arg)
  (list '(mqapply) (list '($%m array) k m) arg))

(defun simp1f2 (arg-l1 arg-l2 arg)
  "Simplify 1F2([a], [b,c], arg).  ARG-L1 is the list [a], and ARG-L2 is
  the list [b, c].  The dependent variable is the (special variable)
  VAR."
  (let ((a (car arg-l1)))
    (destructuring-bind (b c)
	arg-l2
      (cond
	((and (alike1 a 1//2)
	      (alike1 b 3//2)
	      (alike1 c 3//2))
	 ;; Sine integral, expintegral_si(z) = z*%f[1,2]([1/2],[3/2,3/2], -z^2/4)
	 ;; (See http://functions.wolfram.com/06.37.26.0001.01)
	 ;; Subst z = 2*sqrt(-y) into the above to get
	 ;;
	 ;;  expintegral_si(2*sqrt(-y)) = 2*%f[1,2]([1/2],[3/2,3/2], y)*sqrt(-y)
	 ;;
	 ;; Hence %f[1,2]([1/2],[3/2,3/2], y) = expintegral_si(2*sqrt(-y))/2/sqrt(-y)
	 (div (ftake '%expintegral_si (mul 2 (power (neg arg) 1//2)))
	      (mul 2 (power (neg arg) 1//2))))
	(t
	 (fpqform arg-l1 arg-l2 arg))))))

(defun simp2f2 (arg-l1 arg-l2 arg)
  (destructuring-bind (a1 a2)
      arg-l1
    (destructuring-bind (b1 b2)
	arg-l2
      (cond
	((and (= a1 1)
	      (= a2 1)
	      (= b1 2)
	      (= b2 2))
	 ;; Cosine integral
	 ;; expintegral_ci(z) = -z^2/4*%f[2,2]([1,1],[2,2], -z^2/4) + log(z) + %gamma
	 ;; (See http://functions.wolfram.com/06.38.26.0001.01)
	 ;;
	 ;; Subst z = 2*sqrt(-y) into the above to get
	 ;;
	 ;;   expintegral_ci(2*sqrt(-y)) =
	 ;;     %f[2,2]([1,1],[2,2],y)*y + log(2*sqrt(-y)) + %gamma
	 ;;
	 ;; Hence
	 ;;
	 ;;   %f[2,2]([1,1],[2,2],y) =
	 ;;     (expintegral_ci(2*sqrt(-y)) - log(2*sqrt(-y)) - %gamma)/y
	 ;;
	 ;; But see also http://functions.wolfram.com/06.35.26.0001.01
	 ;; which shows that expintegral_ei can be written in terms of
	 ;; %f[2,2]([1,1],[2,2],z) too.  Not sure how to choose
	 ;; between the two representations.
	 (div (sub (ftake '%expintegral_ci (mul 2 (power (neg arg) 1//2)))
		   (add (ftake '%log (mul 2 (power (neg arg) 1//2)))
			'$%gamma))
	      arg))
	(t
	 (fpqform arg-l1 arg-l2 arg))))))

(defvar $trace2f1 nil
  "Enables simple tracing of simp2f1 so you can see how it decides
  what approach to use to simplify hypergeometric functions")

(defun simp2f1 (arg-l1 arg-l2 arg)
  (prog (a b c lgf)
     (setq a (car arg-l1) b (cadr arg-l1) c (car arg-l2))
     
     (cond ((zerop1 arg)
            ;; F(a,b; c; 0) = 1
            (return (add arg 1))))
     
     (when $trace2f1
       (format t "Tracing SIMP2F1~%")
       (format t " Test a or b negative integer ...~%"))
     
     ;; Look if a or b is a symbolic negative integer. The routine 
     ;; 2f1polys handles this case.
     (cond ((and (maxima-integerp a) (member ($sign a) '($neg $nz)))
            (return (2f1polys arg-l1 arg-l2 a arg))))
     (cond ((and (maxima-integerp b) (member ($sign b) '($neg $nz)))
            (return (2f1polys (list b a) arg-l2 b arg))))
     
     (when $trace2f1
       (format t " Test F(1,1,2)...~%"))
     
     (cond ((and (alike1 a 1)
		 (alike1 b 1)
		 (alike1 c 2))
	    ;; F(1,1;2;z) = -log(1-z)/z, A&S 15.1.3
	    (when $trace2f1
	      (format t " Yes~%"))
	    (return (mul (inv (mul -1 arg))
	                 (take '(%log) (add 1 (mul -1 arg)))))))
     
     (when $trace2f1
       (format t " Test c = 1/2 or c = 3/2...~%"))
     
     (cond ((or (alike1 c '((rat simp) 3 2))
		(alike1 c '((rat simp) 1 2)))
	    ;; F(a,b; 3/2; z) or F(a,b;1/2;z)
	    (cond ((setq lgf (trig-log (list a b) (list c) arg))
		   (when $trace2f1
		     (format t " Yes: trig-log~%"))
	           (return lgf)))))
     
     (when $trace2f1
       (format t " Test |a-b|=1/2...~%"))
     
     (cond ((or (alike1 (sub a b) '((rat simp) 1 2))
                (alike1 (sub b a) '((rat simp) 1 2)))
	    ;; F(a,b;c;z) where |a-b|=1/2 
	    (cond ((setq lgf (hyp-cos a b c arg))
		   (when $trace2f1
		     (format t " Yes: hyp-cos~%"))
	           (return lgf)))))
     
     (when $trace2f1
       (format t " Test a,b are integers, c is a numerical integer...~%"))
     
     (cond ((and (maxima-integerp a)
		 (maxima-integerp b)
		 (hyp-integerp c))
	    ;; F(a,b;c;z) when a, and b are integers (or are declared
	    ;; to be integers) and c is a integral number.
	    (setf lgf (simpr2f1 (list a b) (list c) arg))
	    (unless (symbolp lgf) ; Should be more specific! (DK 01/2010)
	      (when $trace2f1
		(format t " Yes: simpr2f1~%"))
	      (return lgf))))
     
     (when $trace2f1
       (format t " Test a+b and c+1/2 are numerical integers...~%"))
     
     (cond ((and (hyp-integerp (add c (inv 2)))
		 (hyp-integerp (add a b)))
	    ;; F(a,b;c;z) where a+b is an integer and c+1/2 is an
	    ;; integer.
	    (when $trace2f1
	      (format t " Yes: step4~%"))
            (return (step4 a b c arg))))
     
     (when $trace2f1
       (format t " Test a-b+1/2 is a numerical integer...~%"))
     
     (cond ((hyp-integerp (add (sub a b) (inv 2)))
	    ;; F(a,b;c,z) where a-b+1/2 is an integer
	    (cond ((setq lgf (step7 a b c arg))
		   (unless (atom lgf)
		     (when $trace2f1
		       (format t " Yes: step7~%"))
		     (return lgf))))))
     
     #+nil
     (when (and (hyp-integerp (add c 1//2))
		(or (and (hyp-integerp (add a 1//2))
			 (hyp-integerp b))
		    (and (hyp-integerp (add b 1//2))
			 (hyp-integerp a))))
       (when $trace2f1
	 (format t " Test for atanh:  a+1/2, b, and c+1/2 are integers~%"))
       (return (hyp-atanh a b c arg)))
     
     (when (hyp-integerp (add c 1//2))
       (when $trace2f1
	 (format t " Test for atanh:  c+1/2 is an integer~%"))
       (cond ((and (hyp-integerp (add a 1//2))
		   (hyp-integerp b))
	      (when $trace2f1
		(format t "  atanh with integers a+1/2 and b ~%"))
	      (return (hyp-atanh a b c arg)))
	     ((and (hyp-integerp (add b 1//2))
		   (hyp-integerp a))
	      (when $trace2f1
		(format t "  atanh with integers a and b+1/2 ~%"))
	      (return (hyp-atanh b a c arg)))))
     
     (when $trace2f1
       (format t " Test for Legendre function...~%"))
     
     (cond ((setq lgf (legfun a b c arg))
	    (unless (atom lgf)
	      ;; LEGFUN returned something interesting, so we're done.
	      (when $trace2f1
		(format t " Yes: case 1~%"))
	      (return lgf))
	    ;; LEGFUN didn't return anything, so try it with the args
	    ;; reversed, since F(a,b;c;z) is F(b,a;c;z).
	    (setf lgf (legfun b a c arg))
	    (when lgf
	      (when $trace2f1
		(format t " Yes: case 2~%"))
	      (return lgf))))
     
     (when $trace2f1
       (format t "'simp2f1-will-continue-in~%"))
     (return  (fpqform arg-l1 arg-l2 arg))))

;; As best as I (rtoy) can tell, step7 is meant to handle an extension
;; of hyp-cos, which handles |a-b|=1/2 and either a+b-1/2 = c or
;; c=a+b+1/2.
;;
;; Based on the code, step7 wants a = s + m/n and c = 2*s+k/l.  For
;; hyp-cos, we want c-2*a to be a integer.  Or k/l-2*m/n is an
;; integer.
#+(or)
(progn
(defun step7 (a b c)
  (prog (l m n k mn kl sym sym1 r)
     ;; Write a = sym + mn, c = sym1 + kl
     (setq l (s+c a)
	   sym (cdras 'f l)
	   mn  (cdras 'c l)
	   l (s+c c)
	   syrm1 (cdras 'f l))
     ;; We only handle the case where 2*sym = sym1.
     (cond ((not (equal (mul sym 2) sym1))
	    (return nil)))
     (setq kl (cdras 'c l))
     ;; a-b+1/2 is an integer.
     (setq l (s+c b)
	   r (sub (add (inv 2) (cdras 'c l)) mn)
	   m ($num mn)
	   n ($denom mn)
	   k ($num kl)
	   l ($denom kl))
     ;; We have a = m*s+m/n, c = 2*m*s+k/l.
     (cond ((equal (* 2 l) n)
	    (cond ((hyp-integerp (/ (- k m) n))
		   (return (hyp-algv k l m n a b c))))))
     (cond ((hyp-integerp (/ k (* 2 l)))
	    (cond ((hyp-integerp (/ m n))
		   (return (hyp-algv k l m n a b c)))
		  (t (return nil))))
	   ((hyp-integerp (/ m n))
	    (return nil))
	   ((hyp-integerp (/ (- (* k n) (* 2 l m)) (* 2 l n)))
	    (return (hyp-algv k l m n a b c))))
     (return nil)))

(defun getxy (k l m n)
  (prog (x y)
     (setq y 0)
     loop
     (cond ((hyp-integerp (setq x (truncate (+ y
					       (truncate k l)
					       (* -2 (quot m n)))
					    2)))
	    (return (list x y))))
     (incf y 2)
     (go loop)))

(defun hyp-algv  (k l m n a b c)
  (prog (x y xy a-b w)
     (setq a-b (sub a b))
     (setq xy (getxy k l m n)
	   x (car xy)
	   y (cadr xy))
     (cond ((< x 0)(go out)))
     (cond ((< x y)
	    (cond ((< (add a-b x (inv 2)) 0)
		   (return (f88 x y a b c fun)))
		  (t (return (f87 x y a c fun)))))
	   (t
	    (cond ((< (add a-b x (inv 2)) 0)
		     (return (f90 x y a c fun)))
		    (t (return (f89 x y a c fun))))))
     out
     (setq w (* x -1))
     (cond ((< (- (add a-b (inv 2)) w) 0)
	    (return (f92 x y a c fun)))
	   (t (return (f91 x y a c fun))))))

(defun f87 (x y a c fun )
  (mul
   (inv (mul (factf c y)
	     (factf (sub (add c y) (add a x)) (- x y))
	     (factf (sub (add c y) (add a x (inv 2)))
		    (sub (add a x (inv 2)) (add a (inv 2))))))
   (power 'ell (sub 1 c))
   (power (sub 1 'ell)(sub (add y c) (add a (inv 2))))
   ($diff (mul (power 'ell (add a x))
	       (power (sub 1 'ell)(mul -1 a))
	       ($diff (mul (power 'ell (sub (add (inv 2) x) y))
			   ($diff (mul (power 'ell (sub (add c y) 1))
				       (power (sub 1 'ell)
					      (sub (add (inv 2)
							(mul 2 a)
							(* 2 x))
						   (add c y)))
				       fun)
				  'ell x))
		      'ell (- x y)))
	  'ell y)))

(defun f88 (x y a b c fun )
  (mul
   (inv (mul (factf c y)
	     (factf (sub (add c y) (add a x)) (- x y))
	     (factf (add a (inv 2) x)
		    (sub b (sub x (sub a (inv 2)))))))
   (power 'ell (sub 1 c))
   (power (sub 1 'ell)(sub (add y c) (add a (inv 2))))
   ($diff (mul (power 'ell (add a x))
	       (power (sub 1 'ell)(mul -1 a))
	       ($diff (mul (power 'ell (sub c (sub x (sub (inv 2) (mul a 2))))))
		      (power (sub 1 'ell) (sub (add a x b)(sub c y)))
		      ($diff (mul (power 'ell (sub b  1 ))
					    
				  fun)
			     'ell (sub b (sub a (sub x (inv 2)))))
		      'ell (- x y)))
	  'ell y)))
)

;; A new version of step7.
(defun step7 (a b c arg)
  ;; To get here, we know that a-b+1/2 is an integer.  To make further
  ;; progress, we want a+b-1/2-c to be an integer too.
  ;;
  ;; Let a-b+1/2 = p and a+b+1/2-c = q where p and q are (numerical)
  ;; integers.
  ;;
  ;; A&S 15.2.3 and 15.2.5 allows us to increase or decrease a.  Then
  ;; F(a,b;c;z) can be written in terms of F(a',b;c;z) where a' = a-p
  ;; and a'-b = a-p-b = 1/2.  Also, a'+b+1/2-c = a-p+b+1/2-c = q-p =
  ;; r, which is also an integer.
  ;;
  ;; A&S 15.2.4 and 15.2.6 allows us to increase or decrease c.  Thus,
  ;; we can write F(a',b;c;z) in terms of F(a',b;c',z) where c' =
  ;; c+r.  Now a'-b=1/2 and a'+b+1/2-c' = a-p+b+1/2-c-r =
  ;; a+b+1/2-c-p-r = q-p-(q-p)=0.
  ;;
  ;; Thus F(a',b;c';z) is exactly the form we want for hyp-cos.  In
  ;; fact, it's A&S 15.1.14: F(a,a+1/2,;1+2a;z) =
  ;; 2^(2*a)*(1+sqrt(1-z))^(-2*a).
  (let ((q (sub (add a b (inv 2))
		c)))
    (unless (hyp-integerp q)
      ;; Wrong form, so return NIL
      (return-from step7 nil))
    ;; Since F(a,b;c;z) = F(b,a;c;z), we need to figure out which form
    ;; to use.  The criterion will be the fewest number of derivatives
    ;; needed.
    (let* ((p1 (add (sub a b) (inv 2)))
	   (r1 (sub q p1))
	   (p2 (add (sub b a) (inv 2)))
	   (r2 (sub q p2)))
      (when $trace2f1
	(format t "step 7:~%")
	(format t "  q, p1, r1 = ~A ~A ~A~%" q p1 r1)
	(format t "     p2, r2 = ~A ~A~%" p2 r2))
      (cond ((<= (+ (abs p1) (abs r1))
		 (+ (abs p2) (abs r2)))
	     (step7-core a b c arg))
	    (t
	     (step7-core b a c arg))))))

(defun step7-core (a b c arg)
  (let* ((p (add (sub a b) (inv 2)))
	 (q (sub (add a b (inv 2))
		 c))
	 (r (sub q p))
	 (a-prime (sub a p))
	 (c-prime (add 1 (mul 2 a-prime))))
    ;; Ok, p and q are integers.  We can compute something.  There are
    ;; four cases to handle depending on the sign of p and r.
    ;;
    ;; We need to differentiate some hypergeometric forms, so use 'ell
    ;; as the variable.
    (let ((fun (hyp-cos a-prime (add a-prime 1//2) c-prime 'ell)))
      ;; fun is F(a',a'+1/2;2*a'+1;z), or NIL
      (when fun
	(when $trace2f1
	  (format t "step7-core~%")
	  (format t " a,b,c = ~A ~A ~A~%" a b c)
	  (format t " p,q,r = ~A ~A ~A~%" p q r)
	  (format t " a', c' = ~A ~A~%" a-prime c-prime)
	  (format t " F(a',a'+1/2; 1+2*a';z) =~%")
	  (maxima-display fun))
	;; Compute the result, and substitute the actual argument into
	;; result.
	(maxima-substitute arg 'ell
	       (cond ((>= p 0)
		      (cond ((>= r 0)
			     (step-7-pp a-prime b c-prime p r 'ell fun))
			    (t
			     (step-7-pm a-prime b c-prime p r 'ell fun))))
		     (t
		      (cond ((>= r 0)
			     (step-7-mp a-prime b c-prime p r 'ell fun))
			    (t
			     (step-7-mm a-prime b c-prime p r 'ell fun))))))))))
  
;; F(a,b;c;z) in terms of F(a',b;c';z)
;;
;; F(a'+p,b;c'-r;z) where p >= 0, r >= 0.
(defun step-7-pp (a b c p r z fun)
  ;; Apply A&S 15.2.4 and 15.2.3
  (let ((res (as-15.2.4 a b c r z fun)))
    (as-15.2.3 a b (sub c r) p z res)))

;; p >= 0, r < 0
;;
;; Let r' = -r
;; F(a'+p,b;c'-r;z) = F(a'+p,b;c'+r';z)
(defun step-7-pm (a b c p r z fun)
  ;; Apply A&S 15.2.6 and 15.2.3
  (let ((res (as-15.2.6 a b c (- r) z fun)))
    (as-15.2.3 a b (sub c r) p z res)))
;;
;; p < 0, r >= 0
;;
;; Let p' = -p
;; F(a'+p,b;c'-r;z) = F(a'-p',b;c'-r;z)
(defun step-7-mp (a b c p r z fun)
  ;; Apply A&S 15.2.4 and 15.2.5
  (let ((res (as-15.2.4 a b c r z fun)))
    (as-15.2.5 a b (sub c r) (- p) z res)))

;; p < 0 r < 0
;;
;; Let p' = - p, r' = -r
;;
;; F(a'+p,b;c'-r;z) = F(a'-p',b;c'+r';z)
(defun step-7-mm (a b c p r z fun)
  ;; Apply A&S 15.2.6 and A&S 15.2.5
  (let ((res (as-15.2.6 a b c (- r) z fun)))
    (as-15.2.5 a b (sub c r) (- p) z res)))

;; F(a,b;c;z) when a and b are integers (or declared to be integers)
;; and c is an integral number.
(defun simpr2f1 (arg-l1 arg-l2 arg)
  (destructuring-bind (a b)
      arg-l1
    (destructuring-bind (c)
	arg-l2
      (let ((inl1p (hyp-integerp a))
	    (inl1bp (hyp-integerp b))
	    (inl2p (hyp-integerp c)))
	(cond (inl2p
	       ;; c is an integer
	       (cond ((and inl1p inl1bp)
		      ;; a, b, c are (numerical) integers
		      (derivint a b c arg))
		     (inl1p
		      ;; a and c are integers
		      (geredno2 b a c arg))
		     (inl1bp
		      ;; b and c are integers.
		      (geredno2 a b c arg))
		     (t 'fail1)))
	      ;; Can't really do anything else if c is not an integer.
	      (inl1p
	       (cond (inl1bp
		      'd)
		     (t
		      'c)))
	      ((eq (caaar arg-l1) 'rat)
	       ;; How do we ever get here?
	       (cond (inl1bp
		      'c)
		     (t
		      'd)))
	      (t
	       'failg))))))

;; This isn't called from anywhere?
#+nil
(defun geredno1
    (arg-l1 arg-l2)
  (cond ((and (> (car arg-l2)(car arg-l1))
	      (> (car arg-l2)(cadr arg-l1)))
	 (geredf (car arg-l1) (cadr arg-l1) (car arg-l2) arg))
	(t (gered1 arg-l1 arg-l2 #'hgfsimp arg))))

(defun geredno2 (a b c arg)
  (cond ((> c b) (geredf b a c arg))
	(t (gered2 a b c arg))))

;; Consider F(1,1;2;z).  A&S 15.1.3 says this is equal to -log(1-z)/z.
;;
;; Apply A&S 15.2.2:
;;
;; diff(F(1,1;2;z),z,ell) = poch(1,ell)*poch(1,ell)/poch(2,ell)*F(1+ell,1+ell;2+ell;z)
;;
;; A&S 15.2.7 says:
;;
;; diff((1-z)^(m+ell)*F(1+ell;1+ell;2+ell;z),z,m)
;;    = (-1)^m*poch(1+ell,m)*poch(1,m)/poch(2+ell,m)*(1-z)^ell*F(1+ell+m,1+ell;2+ell+m;z)
;;
;; A&S 15.2.6 gives
;;
;; diff((1-z)^ell*F(1+ell+m,1+ell;2+ell+m;z),z,n)
;;    = poch(1,n)*poch(1+m,n)/poch(2+ell+m,n)*(1-z)^(ell-n)*F(1+ell+m,1+ell;2+ell+m+n;z)
;;
;; The derivation above assumes that ell, m, and n are all
;; non-negative integers.  Thus, F(a,b;c;z), where a, b, and c are
;; integers and a <= b <= c, can be written in terms of F(1,1;2;z).
;; The result also holds for b <= a <= c, of course.
;;
;; Also note that the last two differentiations can be combined into
;; one differention since the result of the first is in exactly the
;; form required for the second.  The code below does one
;; differentiation.
;;
;; So if a = 1+ell, b = 1+ell+m, and c = 2+ell+m+n, we have ell = a-1,
;; m = b - a, and n = c - ell - m - 2 = c - b - 1.

(defun derivint (a b c arg)
  (if (> a b)
      (derivint b a c arg)
      (let ((l (- a 1))
	    (m (- b a))
            (n (- c b 1))
            (psey (gensym))
            result)
         
        (setq result 
              (mul (power -1 m)
                   (factorial (+ n m l 1))
                   (inv (factorial n))
                   (inv (factorial l))
                   (inv (factorial (+ n m)))
                   (inv (factorial (+ m l)))
                   (power (sub 1 psey) (sub n l))
                   ($diff (mul (power (sub 1 psey) (+ m l))
                               ($diff (mul (power  psey  -1)
                                           -1
                                           (take '(%log) (sub 1 psey)))
                                      psey
                                      l))
                          psey
                          (+ n m))))
        (if (onep1 arg)
            ($limit result psey arg)
            (maxima-substitute arg psey result)))))

;; Handle F(a, b; c; z) for certain values of a, b, and c.  See the
;; comments below for these special values.
(defun hyp-cos (a b c z)
  (let ((a1 (div (sub (add a b) (div 1 2)) 2))
	(z1 (sub 1 z)))
    ;; a1 = (a+b-1/2)/2
    ;; z1 = 1-z
    (cond ((eql 0 ($ratsimp (sub (sub (add a b)
				      (div 1 2))
				 c)))
	   ;; a+b-1/2 = c
	   ;;
	   ;; A&S 15.1.14
	   ;;
	   ;; F(a,a+1/2;2*a;z)
	   ;;    = 2^(2*a-1)*(1-z)^(-1/2)*(1+sqrt(1-z))^(1-2*a)
	   ;;
	   ;; But if 1-2*a is a negative integer, let's rationalize the answer to give
	   ;;
	   ;; F(a,a+1/2;2*a;z)
	   ;;   = 2^(2*a-1)*(1-z)^(-1/2)*(1-sqrt(1-z))^(2*a-1)/z^(2*a-1)
	   (when $trace2f1
	     (format t "   Case a+b-1/2=c~%"))
	   (let ((2a-1 (sub (mul a1 2) 1)))
	     (cond ((and (integerp 2a-1) (plusp 2a-1))
		    ;; 2^(2*a-1)*(1-z)^(-1/2)*(1-sqrt(1-z))^(2*a-1)/z^(2*a-1)
		    (mul (power 2 2a-1)
			 (inv (power z1 1//2))
			 (power (sub 1 (power z1 1//2)) 2a-1)
			 (inv (power z 2a-1))))
		   (t
		    ;; 2^(2*a-1)*(1-z)^(-1/2)*(1+sqrt(1-z))^(1-2*a)
		    (mul (power 2 (sub (mul a1 2) 1))
			 (inv (power  z1 (div 1 2)))
			 (power (add 1
				     (power z1
					    (div 1
						 2)))
				(sub 1 (mul 2 a1))))))))
	  ((eql 0 ($ratsimp (sub (add 1 (mul 2 a1)) c)))
	   ;; c = 1+2*a1 = a+b+1/2
	   ;;
	   ;; A&S 15.1.13:
	   ;;
	   ;; F(a,1/2+a;1+2*a;z) = 2^(2*a)*(1+sqrt(1-z))^(-2*a)
	   ;;
	   ;; But if 2*a is a positive integer, let's rationalize the answer to give
	   ;;
	   ;; F(a,1/2+a;1+2*a;z) = 2^(2*a)*(1-sqrt(1-z))^(2*a)/z^(2*a)
	   (when $trace2f1
	     (format t "   Case c=1+2*a=a+b+1/2~%"))
	   (let ((2a (sub c 1)))
	     (cond ((and (integerp 2a) (plusp 2a))
		    ;; 2^(2*a)*(1-sqrt(1-z))^(2*a)/z^(2*a)
		    (mul (power 2 2a)
			 (power (sub 1 (power z1 1//2))
				2a)
			 (power z (mul -1 2a))))
		   (t
		    ;; 2^(2*a)*(1+sqrt(1-z))^(-2*a)
		    (mul (power 2 2a)
			 (power (add 1 (power z1 1//2))
				(mul -1 2a))))))))))

;; Is A a non-negative integer?
(defun nni (a)
  (cond ((hyp-integerp a)
	 (not (minusp a)))))


;;; The following code doesn't appear to be used at all.  Comment it all out for now.
#||
(defun degen2f1
    (a b c)
  (cond ((eq (quest (sub c b)) '$negative)
	 (cond ((eq (quest (sub c a)) '$negative)
		(gered1 (list a b)(list c) #'hgfsimp))
	       (t (gered2 a b c))))
	((eq (quest (sub c a)) '$negative)(gered2 b a c))
	(t (rest-degen a b c))))


(defun rest-degen
    (a b c)
  (prog(m n l)
     (cond ((nni (setq m (sub a 1)))
	    (return (rest-degen-1 a b c m))))
     (cond ((ni b)(return (rest-degen-2 a b c))))
     (cond ((and (nni (setq n (sub c 1)))
		 (nni (setq m (sub (sub a n) 1)))
		 (nni (setq l (sub b a)))
		 (eq (sub (sub c a) b)
		     (mul -1 (add m m n l 1))))
	    (return (gered1 (list a b)
			    (list c)
			    #'hgfsimp))))
     (return (hyp-deg b a c))))


(defun rest-degen-1
    (a b c m)
  (prog(n l)
     (cond ((and (ni b)
		 (ni (sub (sub c a) b))
		 (nni (sub (sub c a) 1)))
	    (return (deg299 a b c))))
     (cond ((and (nni (setq n (sub (sub c m) 2)))
		 (nni (setq l (sub b c)))
		 (equal (sub (sub c a) b)
			(mul -1 (add l m 1))))
	    (return (gered1 (list a b)
			    (list c)
			    #'hgfsimp))))
     (cond ((nni (setq l (sub (sub b m) 1)))
	    (return (rest-degen-1a a b c m l))))
     (return (hyp-deg b a c))))


(defun rest-degen-1a
    (a b c m l)
  (prog(n)
     (cond ((and (nni (setq n
			    (sub (sub (sub c m) l) 2)))
		 (equal (sub n m)(sub (sub c a) b)))
	    (return (deg2913 a b c))))
     (cond ((and (equal c (mul -1 n))
		 (equal (sub (sub c a) b)
			(mul -1 (add m m l n 2))))
	    (return (deg2918 a b c))))
     (return (hyp-deg b a c))))


(defun rest-degen-2
    (a b c)
  (prog(m l)
     (cond ((and (ni c)(ni (sub (sub c a) b)))
	    (return (rest-degen-2a a b c))))
     (cond ((and (nni (setq m (sub c 1)))
		 (nni (setq l (sub a c)))
		 (ni (sub (sub c a) b)))
	    (return (deg292 a b c))))
     (return (hyp-deg b a c))))


(defun rest-degen-2a
    (a b c)
  (prog()
     (cond ((nni (sub a c))
	    (return (gered1 (list a b)
			    (list c)
			    #'hgfsimp))))
     (cond ((nni (sub (sub c a) 1))
	    (return (deg2917 a b c))))
     (return (hyp-deg b a c))))

(defun quest
    (a)
  (cond ((numberp a)(checksigntm a))
	((equal (caar a) 'rat)(checksigntm a))
	(t nil)))

(defun ni(a)(not (hyp-integerp a)))


(defun hyp-deg
    (a b c)
  (prog()
     (cond (fldeg (setq fldeg nil)
		  (return (hgfsimp (list a b)
				   (list c)
				   var))))
     (setq fldeg t)
     (return (fpqform (list a b)(list c) var))))


(defun deg2913
    (a b c)
  (mul (power (mul -1 var)(mul -1 b))
       (hgfsimp (list (add b 1 (mul -1 c)) b)
		(list (add b 1 (mul -1 a)))
		(inv var))))


(defun deg2918
    (a b c)
  (mul (power var (sub 1 c))
       (power (sub 1 var)(add c (mul -1 a)(mul -1 b)))
       (hgfsimp (list (sub 1 a)(sub 1 b))
		(list (sub 2 c))
		var)))


(defun deg2917
    (a b c)
  (mul (power var (sub 1 c))
       (hgfsimp (list (add a 1 (mul -1 c))
		      (add b 1 (mul -1 c)))
		(list (sub 2 c))
		var)))


(defun deg299
    (a b c)
  (mul (power (mul -1 var)(mul -1 a))
       (hgfsimp (list a (add a 1 (mul -1 c)))
		(list (add a 1 (mul -1 b)))
		(inv var))))

||#


;; Is F(a, b; c; z) is Legendre function?
;;
;; Lemma 29 (see ref) says F(a, b; c; z) can be reduced to a Legendre
;; function if two of the numbers 1-c, +/-(a-b), and +/- (c-a-b) are
;; equal to each other or one of them equals +/- 1/2.
;;
;; This routine checks for each of the possibilities.
(defun legfun (a b c arg)
  (let ((1-c (sub 1 c))
	(a-b (sub a b))
	(c-a-b (sub (sub c a) b))
	(inv2 (inv 2)))
    (cond ((alike1 a-b inv2)
	   ;; a-b = 1/2
	   (when $trace2f1
	     (format t "Legendre a-b = 1/2~%"))
           (gered1 (list a b) (list c) #'legf24 arg))
          
	  ((alike1 a-b (mul -1 inv2))
	   ;; a-b = -1/2
	   ;;
	   ;; For example F(a,a+1/2;c;x)
	   (when $trace2f1
	     (format t "Legendre a-b = -1/2~%"))
	   (legf24 (list a b) (list c) arg))
          
	  ((alike1 c-a-b '((rat simp) 1 2))
	   ;; c-a-b = 1/2
	   ;; For example F(a,b;a+b+1/2;z)
	   (when $trace2f1
	     (format t "Legendre c-a-b = 1/2~%"))
	   (legf20 (list a b) (list c) arg))
          
          ((and (alike1 c-a-b '((rat simp) 3 2))
		(not (alike1 c 1))
		(not (alike1 a -1//2))
		(not (alike1 b -1//2)))
           ;; c-a-b = 3/2 e.g. F(a,b;a+b+3/2;z) Reduce to
           ;; F(a,b;a+b+1/2) and use A&S 15.2.6.  But if c = 1, we
           ;; don't want to reduce c to 0! Problem: The derivative of
           ;; assoc_legendre_p introduces a unit_step function and the
           ;; result looks very complicated. And this doesn't work if
           ;; a+1/2 or b+1/2 is zero, so skip that too.
           (when $trace2f1
             (format t "Legendre c-a-b = 3/2~%")
             (mformat t "   : a = ~A~%" a)
             (mformat t "   : b = ~A~%" b)
             (mformat t "   : c = ~A~%" c))
           (let ((psey (gensym)))
             (maxima-substitute
               *par* psey
               (mul (power (sub 1 psey) '((rat simp) 3 2))
                    (add a b '((rat simp) 1 2))
                    (inv (add b '((rat simp) 1 2)))
                    (inv (add a '((rat simp) 1 2)))
                    ($diff (mul (power (sub 1 psey) '((rat simp) -1 2))
                                (hgfsimp (list a b)
                                         (list (add a b '((rat simp) 1 2)))
                                         psey))
                           psey
                           1)))))
          
	  ((alike1 c-a-b '((rat simp) -1 2))
	   ;; c-a-b = -1/2, e.g. F(a,b; a+b-1/2; z)
	   ;; This case is reduce to F(a,b; a+b+1/2; z) with
	   ;;    F(a,b;c;z) = (1-z)^(c-a-b)*F(c-a,c-b;c;z)
	   (when $trace2f1
	     (format t "Legendre c-a-b = -1/2~%"))
	   (gered1 (list a b) (list c) #'legf20 arg))
          
	  ((alike1 1-c a-b)
	   ;; 1-c = a-b, F(a,b; b-a+1; z)
	   (when $trace2f1
	     (format t "Legendre 1-c = a-b~%"))
	   (gered1 (list a b) (list c) #'legf16 arg))
          
	  ((alike1 1-c (mul -1 a-b))
	   ;; 1-c = b-a, e.g. F(a,b; a-b+1; z)
	   (when $trace2f1
	     (format t "Legendre 1-c = b-a~%"))
	   (legf16 (list a b) (list c) arg))
          
	  ((alike1 1-c c-a-b)
	   ;; 1-c = c-a-b, e.g. F(a,b; (a+b+1)/2; z)
	   (when $trace2f1
	     (format t "Legendre 1-c = c-a-b~%"))
	   (gered1 (list a b) (list c) #'legf14 arg))
          
	  ((alike1 1-c (mul -1 c-a-b))
	   ;; 1-c = a+b-c
	   ;;
	   ;; For example F(a,1-a;c;x)
	   (when $trace2f1
	     (format t "Legendre 1-c = a+b-c~%"))
	   (legf14 (list a b) (list c) arg))
          
	  ((alike1 a-b (mul -1 c-a-b))
	   ;; a-b = a+b-c, e.g. F(a,b;2*b;z)
	   (when $trace2f1
	     (format t "Legendre a-b = a+b-c~%"))
	   (legf36 (list a b) (list c) arg))
          
	  ((or (alike1 1-c inv2)
	       (alike1 1-c (mul -1 inv2)))
	   ;; 1-c = 1/2 or 1-c = -1/2
	   ;; For example F(a,b;1/2;z) or F(a,b;3/2;z)
	   (when $trace2f1
	     (format t "Legendre |1-c| = 1/2~%"))
	   ;; At this point it does not make sense to call legpol. legpol can
	   ;; handle only cases with a negative integer in the first argument
	   ;; list. This has been tested already. Therefore we can not get
	   ;; a result from legpol. For this case a special algorithm is needed.
	   ;; At this time we return nil.
	   ;(legpol a b c)
	   nil)
          
	  ((alike1 a-b c-a-b)
	   ;; a-b = c-a-b
	   (when $trace2f1
	     (format t "Legendre a-b = c-a-b~%"))
	   'legendre-funct-to-be-discovered)
	  (t
	   nil))))

;;; The following legf<n> functions correspond to formulas in Higher
;;; Transcendental Functions.  See the chapter on Legendre functions,
;;; in particular the table on page 124ff,

;; Handle the case c-a-b = 1/2
;;
;; Formula 20:
;;
;; P(n,m,z) = 2^m*(z^2-1)^(-m/2)/gamma(1-m)*F(1/2+n/2-m/2, -n/2-m/2; 1-m; 1-z^2)
;;
;; See also A&S 15.4.12 and 15.4.13.
;;
;; Let a = 1/2+n/2-m/2, b = -n/2-m/2, c = 1-m.  Then, m = 1-c.  And we
;; have two equivalent expressions for n:
;;
;; n = c - 2*b - 1 or n = 2*a - c
;;
;; The code below chooses the first solution.  A&S chooses second.
;;
;; F(a,b;c;w) = 2^(c-1)*gamma(c)*(-w)^((1-c)/2)*P(c-2*b-1,1-c,sqrt(1-w))
;;
;;
(defun legf20 (arg-l1 arg-l2 arg)
  ;; F(a,b;a+b+1/2;x)
  (let* (($radexpand nil)
	 (b (cadr arg-l1))
	 (c (car arg-l2))
	 (a (sub (sub c b) '((rat simp) 1 2)))
	 (m (sub 1 c))
	 (n (mul -1 (add b b m))))
    ;; m = 1 - c
    ;; n = -(2*b+1-c) = c - 1 - 2*b
    ;; A&S 15.4.13
    ;;
    ;; F(a,b;a+b+1/2;x) = 2^(a+b-1/2)*gamma(a+b+1/2)*x^((1/2-a-b)/2)
    ;;                     *assoc_legendre_p(a-b-1/2,1/2-a-b,sqrt(1-x))
    ;; This formula is correct for all arguments x.
    (mul (power 2 (add a b '((rat simp) -1 2)))
	 (take '(%gamma) (add a b '((rat simp) 1 2)))
	 (power arg
		(div (sub '((rat simp) 1 2) (add a b))
		     2))
	 (legen n
		m
		(power (sub 1 arg) '((rat simp) 1 2))
		'$p))))

;; Handle the case a-b = -1/2.
;;
;; Formula 24:
;;
;; P(n,m,z) = 2^m*(z^2-1)^(-m/2)*z^(n+m)/gamma(1-m)*F(-n/2-m/2,1/2-n/2-m/2;1-m;1-1/z^2)
;;
;; See also A&S 15.4.10 and 15.4.11.
;;
;; Let a = -n/2-m/2, b = 1/2-n/2-m/2, c = 1-m.  Then m = 1-c.  Again,
;; we have 2 possible (equivalent) values for n:
;;
;; n = -(2*a + 1 - c) or n = c-2*b
;;
;; The code below chooses the first solution.
;;
;; F(a,b;c;w) = 2^(c-1)*w^(1/2-c/2)*(1-w)^(c/2-a-1/2)*P(c-2*a-1,1-c,1/sqrt(1-w))
;;
;; F(a,b;c;w) = 2^(c-1)*w^(1/2-c/2)*(1-w)^(c/2-b)*P(c-2*b,1-c,sqrt(1-w))
;;
;; Is there a mistake in 15.4.10 and 15.4.11?
;;
(defun legf24 (arg-l1 arg-l2 arg)
  (let* (($radexpand nil)
	 (a (car arg-l1))
	 (c (car arg-l2))
	 (m (sub 1 c))
;	 (n (mul -1 (add a a m))) ; This is not 2*a-c
         (n (sub (add a a) c))    ; but this.
	 (z (inv (power (sub 1 arg) (inv 2)))))
    ;; A&S 15.4.10, 15.4.11
    (cond ((eq (asksign arg) '$negative)
	   ;; A&S 15.4.11
	   ;;
	   ;; F(a,a+1/2;c;x) = 2^(c-1)*gamma(c)(-x)^(1/2-c/2)*(1-x)^(c/2-a-1/2)
	   ;;                   *assoc_legendre_p(2*a-c,1-c,1/sqrt(1-x))
	   (mul (inv (power 2 m))
		(gm (sub 1 m))
		(power (mul -1 arg) (div m 2))
		(power (sub 1 arg) (sub (div m -2) a))
		(legen n
		       m
		       z
		       '$p)))
	  (t
	   (mul (inv (power 2 m))
		(gm (sub 1 m))
		(power arg (div m 2))
		(power (sub 1 arg) (sub (div m -2) a))
		(legen n
		       m
		       z
		       '$p))))))

;; Handle 1-c = a-b
;;
;; Formula 16:
;;
;; P(n,m,z) = 2^(-n)*(z+1)^(m/2+n)*(z-1)^(-m/2)/gamma(1-m)*F(-n,-n-m;1-m;(z-1)/(z+1))
;;
;; See also A&S 15.4.14 and 15.4.15.
;;
;; Let a = -n, b = -n-m, c = 1-m.  Then m = 1-c.  We have 2 solutions
;; for n:
;;
;; n = -a or n = c-b-1.
;;
;; The code below chooses the first solution.
;;
;; F(a,b;c;w) = gamma(c)*w^(1/2-c/2)*(1-w)^(-a)*P(-a,1-c,(1+w)/(1-w));
;;
;; FIXME:  We don't correctly handle the branch cut here!
(defun legf16 (arg-l1 arg-l2 arg)
  (let* (($radexpand nil)
	 (a (car arg-l1))
	 (c (car arg-l2))
	 ;; m = 1-c = b-a
	 (m (sub 1 c))
	 ;; n = -b
	 ;; m = b - a, so b = a + m
	 (b (add a m))
	 (n (mul -1 b))
	 (z (div (add 1 arg)
		 (sub 1 arg))))
    (when $trace2f1
      (format t "a, c = ~A ~A~%" a c)
      (format t "b = ~A~%" b))
    ;; A&S 15.4.14, 15.4.15
    (cond ((eq (asksign arg) '$negative)
	   ;; A&S 15.4.15
	   ;;
	   ;; F(a,b;a-b+1,x) = gamma(a-b+1)*(1-x)^(-b)*(-x)^(b/2-a/2)
	   ;;                   * assoc_legendre_p(-b,b-a,(1+x)/(1-x))
	   ;;
	   ;; for x < 0
	   (mul (take '(%gamma) c)
		(power (sub 1 arg) (mul -1 b))
		(power (mul -1 arg) (div m 2))
		(legen n m z '$p)))
	  (t
	   (mul (take '(%gamma) c)
		(power (sub 1 arg) (mul -1 b))
		(power arg (div m 2))
		(legen n m z '$p))))))

;; Handle the case 1-c = a+b-c.
;;
;; See, for example, A&S 8.1.2 (which
;; might have a bug?) or
;; http://functions.wolfram.com/HypergeometricFunctions/LegendreP2General/26/01/02/
;;
;; Formula 14:
;;
;; P(n,m,z) = (z+1)^(m/2)*(z-1)^(-m/2)/gamma(1-m)*F(-n,1+n;1-m;(1-z)/2)
;;
;; See also A&S 8.1.2, 15.4.16, 15.4.17
;;
;; Let a=-n, b = 1+n, c = 1-m.  Then m = 1-c and n has 2 solutions:
;;
;; n = -a or n = b - 1.
;;
;; The code belows chooses the first solution.
;;
;; F(a,b;c;w) = gamma(c)*(-w)^(1/2-c/2)*(1-w)^(c/2-1/2)*P(-a,1-c,1-2*w)
(defun legf14 (arg-l1 arg-l2 arg)
  ;; Set $radexpand to NIL, because we don't want (-z)^x getting
  ;; expanded to (-1)^x*z^x because that's wrong for this.
  (let* (($radexpand nil)
	 (a (first arg-l1))
	 (b (second arg-l1))
	 (c (first arg-l2))
	 (m (sub 1 c))
	 (n (mul -1 a))
	 (z (sub 1 (mul 2 arg))))
    (when $trace2f1
      (format t "~&legf14~%"))
    ;; A&S 15.4.16, 15.4.17
    (cond ((not (alike1 (add a b) 1))
	   ;; I think 15.4.16 and 15.4.17 require the form
	   ;; F(a,1-a;c;x).  That is, a+b = 1.  If we don't have it
	   ;; exit now.
	   nil)
	  ((and (eq (asksign arg) '$positive)
		(eq (asksign (sub 1 arg)) '$positive))
	   (when $trace2f1
	     (format t " A&S 15.4.17~%"))
	   ;; A&S 15.4.17
	   ;;
	   ;; F(a,1-a;c;x) = gamma(c)*x^(1/2-c/2)*(1-x)^(c/2-1/2)*
	   ;;                 assoc_legendre_p(-a,1-c,1-2*x)
	   ;;
	   ;; for 0 < x < 1
	   (mul (gm c)
		(power arg (div (sub 1 c) 2))
		(power (sub 1 arg) (div (sub c 1) 2))
		(legen n m z '$p)))
	  (t
	   ;; A&S 15.4.16
	   ;;
	   ;; F(a,1-a;c;z) = gamma(c)*(-z)^(1/2-c/2)*(1-z)^(c/2-1/2)*
	   ;;                 assoc_legendre_p(-a,1-c,1-2*z)
	   (when $trace2f1
	     (format t " A&S 15.4.17~%"))
	   (mul (gm c)
		(power (mul -1 arg) (div (sub 1 c) 2))
		(power (sub 1 arg) (div (sub c 1) 2))
		(legen n m z '$p))))))

;; Handle a-b = a+b-c
;;
;; Formula 36:
;;
;; exp(-%i*m*%pi)*Q(n,m,z) =
;;     2^n*gamma(1+n)*gamma(1+n+m)*(z+1)^(m/2-n-1)*(z-1)^(-m/2)/gamma(2+2*n)
;;     * hgfred([1+n-m,1+n],[2+2*n],2/(1+z))
;;
;; Let a = 1+n-m, b = 1+n, c = 2+2*n.  then n = b-1 and m = b - a.
;; (There are other solutions.)
;;
;; F(a,b;c;z) = 2*gamma(2*b)/gamma(b)/gamma(2*b-a)*w^(-b)*(1-w)^((b-a)/2)
;;              *Q(b-1,b-a,2/w-1)*exp(-%i*%pi*(b-a))
;;
(defun legf36 (arg-l1 arg-l2 arg)
  (declare (ignore arg-l2))
  (let* ((a (car arg-l1))
	 (b (cadr arg-l1))
	 (n (sub b 1))
	 (m (sub b a))
	 ;;z (div (sub 2 arg) arg)
	 (z (sub (div 2 arg) 1)))
    (mul (inv (power 2 n))
	 (inv (gm (add 1 n)))
	 (inv (gm (add 1 n m)))
	 (inv (power (add z 1)
		     (add (div m 2)
			  (mul -1 n)
			  -1)))
	 (inv (power (sub z 1) (div m -2)))
	 (gm (add 2 n n))
	 (power '$%e (mul -1 '$%i m '$%pi))
	 (legen n m z '$q))))

(defun legen (n m x pq)
  ;; A&S 8.2.1: P(-n-1,m,z) = P(n,m,z)
  (let ((n (if (or (member ($sign n) '($neg $nz)) ; negative sign or
                   (mminusp n))                   ; negative form like -n-1
               (mul -1 (add 1 n))
               n)))
    (cond ((equal m 0)
           (list (if (eq pq '$q)
                     '($legendre_q simp)
                     '($legendre_p simp))
                 n x))
          (t
           (list (if (eq pq '$q) 
                     '($assoc_legendre_q simp)
                     '($assoc_legendre_p simp))
                 n m x)))))

(defun legpol-core (a b c arg)
  ;; I think for this to be correct, we need a to be a negative integer.
  (unless (and (eq '$yes (ask-integerp a))
	       (eq (asksign a) '$negative))
    (return-from legpol-core nil))
  (let* ((l (vfvp (div (add b a) 2) arg))
	 (v (cdr (assoc 'v l :test #'equal))))
    ;; v is (a+b)/2
    (cond
      ((and (alike1 v '((rat simp) 1 2))
	    (alike1 c 1))
       ;; A&S 22.5.49:
       ;; P(n,x) = F(-n,n+1;1;(1-x)/2)
       (legenpol (mul -1 a)
		 (sub 1 (mul 2 arg))))

      ((and (alike1 c '((rat simp) 1 2))
	    (alike1 (add b a) '((rat simp) 1 2)))
       ;; c = 1/2, a+b = 1/2
       ;;
       ;; A&S 22.5.52
       ;; P(2*n,x) = (-1)^n*(2*n)!/2^(2*n)/(n!)^2*F(-n,n+1/2;1/2;x^2)
       ;;
       ;; F(-n,n+1/2;1/2;x^2) = P(2*n,x)*(-1)^n*(n!)^2/(2*n)!*2^(2*n)
       ;;
       (let ((n (mul -1 a)))
	 (mul (power -1 n)
	      (power (gm (add n 1)) 2)
	      (inv (gm (add 1 (mul 2 n))))
	      (power 2 (mul 2 n))
	      (legenpol (mul 2 n)
			(power arg (div 1 2))))))

      ((and (alike1 c '((rat simp) 3 2))
	    (alike1 (add b a) '((rat simp) 3 2)))
       ;; c = 3/2, a+b = 3/2
       ;;
       ;; A&S 22.5.53
       ;; P(2*n+1,x) = (-1)^n*(2*n+1)!/2^(2*n)/(n!)^2*F(-n,n+3/2;3/2;x^2)*x
       ;;
       ;; F(-n,n+3/2;3/2;x^2) = P(2*n+1,x)*(-1)^n*(n!)^2/(2*n+1)!*2^(2*n)/x
       ;;
       (let ((n (mul -1 a)))
	 (mul (power -1 n)
	      (power (gm (add 1 n)) 2)
	      (inv (gm (add 2 (mul 2 n))))
	      (power 2 (mul 2 n))
	      (legenpol (add 1 (mul 2 n))
			(power arg (div 1 2)))
	      (inv (power arg (div 1 2))))))

      ((and (zerp (sub b a))
	    (zerp (sub c (add a b))))
       ;; a = b, c = a + b
       ;;
       ;; A&S 22.5.50
       ;; P(n,x) = binomial(2*n,n)*((x-1)/2)^n*F(-n,-n;-2*n;2/(1-x))
       ;;
       ;; F(-n,-n;-2*n;x) = P(n,1-2/x)/binomial(2*n,n)(-1/x)^(-n)
       (mul (power (gm (add 1 (mul -1 a))) 2)
	    (inv (gm (add 1 (mul -2 a))))
	    (power (mul -1 arg) (mul -1 a))
	    (legenpol (mul -1 a)
		      (add 1 (div -2 arg)))))
      ((and (alike1 (sub a b) '((rat simp) 1 2))
	    (alike1 (sub c (mul 2 b)) '((rat simp) 1 2)))
       ;; a - b = 1/2, c - 2*b = 1/2
       ;;
       ;; A&S 22.5.51
       ;; P(n,x) = binomial(2*n,n)*(x/2)^n*F(-n/2,(1-n)/2;1/2-n;1/x^2)
       ;;
       ;; F(-n/2,(1-n)/2;1/2-n,1/x^2) = P(n,x)/binomial(2*n,n)*(x/2)^(-n)
       (mul (power (gm (add 1 (mul -2 b))) 2)
	    (inv (gm (add 1 (mul -4 b))))
	    (power (mul 2 (power arg (div 1 2))) (mul -2 b))
	    (legenpol (mul -2 b)
		      (power arg (div -1 2)))))
      ((and (alike1 (sub b a) '((rat simp) 1 2))
	    (alike1 (sub c (mul 2 a)) '((rat simp) 1 2)))
       ;; b - a = 1/2, c + 2*a = 1/2
       ;;
       ;; A&S 22.5.51
       ;; P(n,x) = binomial(2*n,n)*(x/2)^n*F(-n/2,(1-n)/2;1/2-n;1/x^2)
       ;;
       ;; F(-n/2,(1-n)/2;1/2-n,1/x^2) = P(n,x)/binomial(2*n,n)*(x/2)^(-n)
       (mul (power (gm (add 1 (mul -2 a))) 2)
	    (inv (gm (add 1 (mul -4 a))))
	    (power (mul 2 (power arg (div 1 2))) (mul -2 a))
	    (legenpol (mul -2 a)
		      (power arg (div -1 2)))))
      (t 
       nil))))

;; This seems not be be called at all?  There is a commented-out call
;; in LEGFUN that says it doesn't make sense to call LEGPOL there.
#+nil
(defun legpol (a b c)
  ;; See if F(a,b;c;z) is a Legendre polynomial.  If not, try
  ;; F(b,a;c;z).
  (or (legpol-core a b c var)
      (legpol-core b a c var)))

;; See A&S 15.3.3:
;;
;; F(a,b;c;z) = (1-z)^(c-a-b)*F(c-a,c-b;c;z)
(defun gered1 (arg-l1 arg-l2 simpflg arg)
  (destructuring-bind (a b)
      arg-l1
    (destructuring-bind (c)
	arg-l2
      (mul (power (sub 1 arg)
		  (add c
		       (mul -1 a)
		       (mul -1 b)))
	   (funcall simpflg
		    (list (sub c a)
			  (sub c b))
		    arg-l2
	            arg)))))

;; See A&S 15.3.4
;;
;; F(a,b;c;z) = (1-z)^(-a)*F(a,c-b;c;z/(z-1))
(defun gered2 (a b c arg)
  (mul (power (sub 1 arg) (mul -1 a))
       (hgfsimp (list a (sub c b))
		(list c)
		(div arg (sub arg 1)))))

;; See A&S 15.3.9:
;;
;; F(a,b;c;z) = A*z^(-a)*F(a,a-c+1;a+b-c+1;1-1/z)
;;              + B*(1-z)^(c-a-b)*z^(a-c)*F(c-a,1-a;c-a-b+1,1-1/z)
;;
;; where A = gamma(c)*gamma(c-a-b)/gamma(c-a)/gamma(c-b)
;;       B = gamma(c)*gamma(a+b-c)/gamma(a)/gamma(b)

(defun geredf (a b c arg)
  (let (($gamma_expand t))
    (add (div (mul (take '(%gamma) c)
                   (take '(%gamma) (add c (mul -1 a) (mul -1 b)))
                   (power arg (mul -1 a))
                   ($hgfred `((mlist) ,a ,(add a 1 (mul -1 c)))
                            `((mlist) ,(add a b (mul -1 c) 1))
                            (sub 1 (div 1 arg))))
              (mul (take '(%gamma) (sub c a)) 
                   (take '(%gamma) (sub c b))))
         (div (mul (take '(%gamma) c)
                   (take '(%gamma) (add a b (mul -1 c)))
                   (power (sub 1 arg)
                          (add c (mul -1 a) (mul -1 b)))
                   (power arg (sub a c))
                   ($hgfred `((mlist) ,(sub c a) ,(sub 1 a))
                            `((mlist) ,(add c (mul -1 a) (mul -1 b) 1))
                            (sub 1 (div 1 arg))))
              (mul (take '(%gamma) a) (take '(%gamma) b))))))

(defun trig-log (arg-l1 arg-l2 arg)
  (cond ((equal (simplifya (car arg-l2) nil) '((rat simp) 3 2))
	 ;; c = 3/2
	 (when $trace2f1
	   (format t "  trig-log:  Test c=3/2~%"))
	 (trig-log-3 arg-l1 arg-l2 arg))
	((equal (simplifya (car arg-l2) nil) '((rat simp) 1 2))
	 ;; c = 1/2
	 (when $trace2f1
	   (format t "  trig-log:  Test c=1/2~%"))
	 (trig-log-1 arg-l1 arg-l2 arg))
	(t nil)))

(defun trig-log-3 (arg-l1 arg-l2 arg)
  (cond ((and (or (equal (car arg-l1) 1) (equal (cadr arg-l1) 1))
	      (or (equal (car arg-l1) (div 1 2))
		  (equal (cadr arg-l1) (div 1 2))))
	 ;; (a = 1 or b = 1) and (a = 1/2 or b = 1/2)
	 (when $trace2f1
	   (format t "   Case a or b is 1 and the other is 1/2~%"))
	 (trig-log-3-exec arg-l1 arg-l2 arg))
	((and (equal (car arg-l1) (cadr arg-l1))
	      (or (equal 1 (car arg-l1))
		  (equal (div 1 2) (car arg-l1))))
	 ;; a = b and (a = 1 or a = 1/2)
	 (when $trace2f1
	   (format t "   Case a=b and a is 1 or 1/2~%"))
	 (trig-log-3a-exec arg-l1 arg-l2 arg))
	((or (equal (add (car arg-l1) (cadr arg-l1)) 1)
	     (equal (add (car arg-l1) (cadr arg-l1)) 2))
	 ;; a + b = 1 or a + b = 2
	 (when $trace2f1
	   (format t "   Case a+b is 1 or 2~%"))
	 (trig-sin arg-l1 arg-l2 arg))
	((or (equal (sub (car arg-l1) (cadr arg-l1)) (div 1 2))
	     (equal (sub (cadr arg-l1) (car arg-l1)) (div 1 2)))
	 ;; a - b = 1/2 or b - a = 1/2
	 (when $trace2f1
	   (format t "   Case a-b=1/2 or b-a=1/2~%"))
	 (trig-3 arg-l1 arg-l2 arg))
	(t nil)))

(defun trig-3 (arg-l1 arg-l2 arg)
  (declare (ignore arg-l2))
  ;; A&S 15.1.10
  ;;
  ;; F(a,a+1/2,3/2,z^2) =
  ;; ((1+z)^(1-2*a) - (1-z)^(1-2*a))/2/z/(1-2*a)
  (let* (($radexpand '$all)
	 (a (sub 1
		 (sub (add (car arg-l1)
			   (cadr arg-l1))
		      (div 1 2))))
	 (z (power arg (div 1 2))))
    (mul (inv z)
	 (inv 2)
	 (inv a)
	 (sub (power (add 1 z) a)
	      (power (sub 1 z) a)))))

(defun trig-sin (arg-l1 arg-l2 arg)
  (declare (ignore arg-l2))
  ;; A&S 15.1.15, 15.1.16
  (destructuring-bind (a b)
      arg-l1
    ;; I think it's ok to convert sqrt(z^2) to z here, so $radexpand
    ;; is $all.
    (let (($radexpand '$all)
	  a1 z1)
      (cond ((equal (add a b) 1)
	     ;; A&S 15.1.15
	     ;;
	     ;; F(a,1-a;3/2;sin(z)^2) =
	     ;;
	     ;; sin((2*a-1)*z)/(2*a-1)/sin(z)
	     (mul (inv (mul (mul -1 (sub a b))
			    (msin (masin (msqrt arg)))))
		  (msin (mul (mul -1
				  (sub a b))
			     (masin (msqrt arg))))))
	    ((equal (add a b) 2)
	     ;; A&S 15.1.16
	     ;;
	     ;; F(a, 2-a; 3/2; sin(z)^2) =
	     ;;
	     ;; sin((2*a-2)*z)/(a-1)/sin(2*z)
	     (mul (msin (mul (setq z1
				   (masin (msqrt
					   arg)))
			     (setq a1
				   (mul -1
					(sub a
					     b)))))
		  (inv (mul a1
			    (msin z1)
			    (mcos z1)))))
	    (t
	     nil)))))


;;Generates atan if arg positive else log
(defun trig-log-3-exec (arg-l1 arg-l2 arg)
  (declare (ignore arg-l1 arg-l2))
  ;; See A&S 15.1.4 and 15.1.5
  ;;
  ;; F(a,b;3/2;z) where a = 1/2 and b = 1 (or vice versa).

  ;; I think it's ok to convert sqrt(z^2) to z here, so $radexpand is
  ;; $all.
  (let (($radexpand '$all))
    (cond ((equal (checksigntm arg) '$positive)
	   ;; A&S 15.1.4
	   ;;
	   ;; F(1/2,1;3/2,z^2) =
	   ;;
	   ;; log((1+z)/(1-z))/z/2
	   ;;
	   ;; This is the same as atanh(z)/z.  Should we return that
	   ;; instead?  This would make this match what hyp-atanh
	   ;; returns.
	   (let ((z (power arg (div 1 2))))
	     (mul (power z -1)
		  (inv 2)
		  (mlog (div (add 1 z)
			     (sub 1 z))))))
	  ((equal (checksigntm arg) '$negative)
	   ;; A&S 15.1.5
	   ;;
	   ;; F(1/2,1;3/2,z^2) =
	   ;; atan(z)/z
	   (let ((z (power (mul -1 arg)
			   (div 1 2))))
	     (mul (power z -1)
		  (matan z)))))))

(defun trig-log-3a-exec (arg-l1 arg-l2 arg)
  ;; See A&S 15.1.6 and 15.1.7
  ;;
  ;; F(a,b;3/2,z) where a = b and a = 1/2 or a = 1.

  ;; I think it's ok to convert sqrt(z^2) to z here, so $radexpand is
  ;; $all.
  (let ((a (first arg-l1))
	($radexpand '$all))
    (cond ((equal (checksigntm arg) '$positive)
	   ;; A&S 15.1.6
	   ;;
	   ;; F(1/2,1/2; 3/2; z^2) = sqrt(1-z^2)*F(1,1;3/2;z^2) =
	   ;; asin(z)/z
	   (let ((z (power arg (div 1 2))))
	     (if (equal a 1)
		 (div (trig-log-3a-exec (list (div 1 2) (div 1 2)) arg-l2 arg)
		      (power (sub 1 (power z 2)) (div 1 2)))
		 (div (masin z) z))))
	  ((equal (checksigntm arg) '$negative)
	   ;; A&S 15.1.7
	   ;;
	   ;; F(1/2,1/2; 3/2; -z^2) = sqrt(1+z^2)*F(1,1,3/2; -z^2) =
	   ;;log(z + sqrt(1+z^2))/z
	   (let* ((z (power (mul -1 arg)
			    (div 1 2)))
		  (1+z^2 (add 1 (power z 2))))
	     (if (equal a 1)
		 (div (trig-log-3a-exec (list (div 1 2) (div 1 2))
					arg-l2
                                        arg)
		      (power 1+z^2
			     (div 1 2)))
		 (div (mlog (add z (power 1+z^2
					  (div 1 2))))
		      z)))))))


(defun trig-log-1 (arg-l1 arg-l2 arg)	;; 2F1's with C = 1/2
  (declare (ignore arg-l2))
  ;; 15.1.17, 11, 18, 12, 9, and 19

  ;; I think it's ok to convert sqrt(z^2) to z here, so $radexpand is
  ;; $all.
  (let (($radexpand '$all)
	x z $exponentialize a b)
    (setq a (car arg-l1) b (cadr arg-l1))
    (cond ((=0 (m+t a b))
	   ;; F(-a,a;1/2,z)

	   (cond ((equal (checksigntm arg) '$positive)
		  ;; A&S 15.1.17:
		  ;; F(-a,a;1/2;sin(z)^2) = cos(2*a*z)
		  (trig-log-1-pos a arg))
		 ((equal (checksigntm arg) '$negative)
		  ;; A&X 15.1.11:
		  ;; F(-a,a;1/2;-z^2) = 1/2*((sqrt(1+z^2)+z)^(2*a)
		  ;;                         +(sqrt(1+z^2)-z)^(2*a))
		  ;;
		  (trig-log-1-neg a b arg))
		 (t ())))
	  ((equal (m+t a b) 1.)
	   ;; F(a,1-a;1/2,z)
	   (cond ((equal (checksigntm arg) '$positive)
		  ;; A&S 15.1.18:
		  ;; F(a,1-a;1/2;sin(z)^2) = cos((2*a-1)*z)/cos(z)
		  (m//t (mcos (m*t (m-t a b) (setq z (masin (msqrt arg)))))
			(mcos z)))
		 ((equal (checksigntm arg) '$negative)
		  ;; A&S 15.1.12
		  ;; F(a,1-a;1/2;-z^2) = 1/2*(1+z^2)^(-1/2)*
		  ;;                     {[(sqrt(1+z^2)+z]^(2*a-1)
		  ;;                       +[sqrt(1+z^2)-z]^(2*a-1)}
		  (m*t 1//2 (m//t (setq x (msqrt (m-t 1. arg))))
		       (m+t (m^t (m+t x (setq z (msqrt (m-t arg))))
				 (setq b (m-t a b)))
			    (m^t (m-t x z) b))))
		 (t ())))
	  ((=1//2 (hyp-mabs (m-t b a)))
	   ;; F(a, a+1/2; 1/2; z)
	   (cond ((equal (checksigntm arg) '$positive)
		  ;; A&S 15.1.9
		  ;; F(a,1/2+a;1/2;z^2) = ((1+z)^(-2*a)+(1-z)^(-2*a))/2
		  (m*t 1//2
		       (m+t (m^t (m1+t (setq z (msqrt arg)))
				 (setq b (m-t 1//2 (m+t a b))))
			    (m^t (m-t 1. z) b))))
		 ((equal (checksigntm arg) '$negative)
		  ;; A&S 15.1.19
		  ;; F(a,1/2+a;1/2;-tan(z)^2) = cos(z)^(2*a)*cos(2*a*z)
		  (m*t (m^t (mcos (setq z (matan (msqrt (m-t arg)))))
			    (setq b (m+t a b -1//2)))
		       (mcos (m*t b z))))
		 (t ())))
	  (t ()))))

(defun trig-log-1-pos (a z)
  ;; I think it's ok to convert sqrt(z^2) to z here, so $radexpand is
  ;; $all.
  (let (($radexpand '$all))
    (mcos (m*t 2. a (masin (msqrt z))))))

(defun trig-log-1-neg (a b v)
  ;; Look to see a is of the form m*s+c where m and c
  ;; are numbers.  If m is positive, swap a and b.
  ;; Basically we want F(-a,a;1/2;-z^2) =
  ;; F(a,-a;1/2;-z^2), as they should be.
  (let* (($radexpand '$all)
	 (match (m*s+c a))
	 (m (cdras 'm match))
	 (s (cdras 's match))
	 (b (if s
		(if (and m (eq (checksigntm m) '$positive))
		    a
		    b)
		(if (eq (checksigntm a) '$negative)
		    b
		    a)))
	 (x (msqrt (m-t 1. v)))
	 (z (msqrt (m-t v))))
    (m*t 1//2
	 (m+t (m^t (m+t x z)
		   (setq b (m*t 2. b)))
	      (m^t (m-t x z) b)))))
  
;; Pattern match for m*s+c where a is a number, x is symbolic, and c
;; is a number.
(defun m*s+c (exp)
  (m2 exp
      '((mplus) ((coeffpt) (m $numberp) (s nonnump))
	        ((coeffpp) (c $numberp)))))

;; List L contains two elements first the numerator parameter that
;;exceeds the denumerator one and is called "C", second
;;the difference of the two parameters which is called "M". 

#||
(defun diffintprop-gen-exec (l l1 l2) 
  (prog (c m poly constfact ) 
     (setq c (car l) 
	   m (cadr l) 
	   l1 (delete c l1 :count 1 :test #'equal) 
	   c (sub c m)
	   l2 (delete c l2 :count 1 :test equal) 
	   poly ($expand (constrpoly c m 'avgoustis)) 
	   constfact (createconstfact c m))
     (return (yanmult constfact
		      (diffintprop-exec poly l1 l2))))) 

(defun constrpoly (c m k) 
  (cond ((zerop m) 1.)
	(t (mul (add c k (1- m)) (constrpoly c (1- m) k))))) 

(defun createconstfact (c m) 
  (cond ((zerop m) 1.)
	(t (mul (inv (add c (1- m)))
		(createconstfact c (1- m)))))) 

(defun diffintprop-exec (poly l1 l2) 
  (distrdiffintprop (createcoefpowlist-exec poly) l1 l2)) 

(defun distrdiffintprop (l l1 l2) 
  (cond ((null l) 0.)
	(t (add (yanmult ($factor (cadar l))
			 (diffintprop (caar l) l1 l2))
		(distrdiffintprop (cdr l) l1 l2))))) 

(defun diffintprop (pow l1 l2) 
  (cond ((zerop pow) (hgfsimp l1 l2 var))
	((equal pow 1.)
	 (yanmult (mul (div (multpl l1) (multpl l2)) var)
		  (hgfsimp (incr1 l1) (incr1 l2) var)))
	(t (searchaddserieslist pow l1 l2)))) 

(defun searchaddserieslist (pow l1 l2) 
  (prog (series res) 
     (cond ((setq series (searchserieslistp serieslist pow))
	    (return (eval series))))
     (setq 
      serieslist
      (append
       serieslist
       (list
	(list
	 pow
	 (setq res
	       '(yanmult (mul (div (multpl l1) (multpl l2))
			  var)
		 (diffintproprecurse (1- pow)
		  (incr1 l1)
		  (incr1 l2))))))))
     (return (eval res)))) 

(defun diffintproprecurse (pow l1 l2) 
  (prog (poly) 
     (setq poly
	   ($expand (power (add 'avgoustis 1.) pow)))
     (return (diffintprop-exec poly l1 l2)))) 

(defun multpl (l) 
  (cond ((null l) 1.) (t (mul (car l) (multpl (cdr l)))))) 

(defun createcoefpowlist-exec (poly) 
  (prog (hp conster) 
     (setq conster (consterminit poly 'avgoustis) 
	   hp ($hipow poly 'avgoustis))
     (return (append (list (list 0. conster))
		     (createcoefpowlist poly hp))))) 

(defun createcoefpowlist (poly hp) 
  (cond ((equal hp 1.)
	 (list (list 1. ($coeff poly 'avgoustis))))
	(t (append (createcoefpowlist poly (1- hp))
		   (list (list hp
			       ($coeff poly
				       (power 'avgoustis
					      hp)))))))) 

(defun consterminit (fun var) 
  (cond ((eq (caar fun) 'mplus) (consterm (cdr fun) var))
	(t (cond ((freevar fun) fun) (t 0.))))) 

(defun searchserieslistp (serieslist pow) 
  (cond ((null serieslist) nil)
	((equal (caar serieslist) pow) (cadar serieslist))
	(t (searchserieslistp (cdr serieslist) pow)))) 

(defun yanmult (a b) 
  (cond ((eq (caar b) 'mplus) (yanmul a (cdr b)))
	(t (mul a b)))) 

(defun yanmul (a b) 
  (cond ((null b) 0.)
	(t (add (mul a (car b)) (yanmul a (cdr b)))))) 

||#

(defun freevarpar (exp)
  (cond ((freevar exp) (freepar exp))
	(t nil)))

(defun freevarpar2 (exp arg)
  (cond ((freevar2 exp arg)
         (freepar exp))
	(t nil)))

;; Why is this needed?
(setq *par* '$p)

(defun freepar (exp)
  (cond ((atom exp)
	 (not (eq exp *par*)))
	(t (and (freepar (car exp))
		(freepar (cdr exp))))))

;; Confluent hypergeometric function.
;;
;; F(a;c;z)
(defun confl (arg-l1 arg-l2 arg)
  (let* ((a (car arg-l1))
         (c (car arg-l2))
         (a-c (sub a c))
         n)
    (cond ((zerop1 arg)
           ;; F(a;c;0) = 1
           (add 1 arg))
          
          ((and (equal 1 c)
                (not (integerp a))          ; Do not handle an integer or
                (not (integerp (add a a)))) ; an half integral value
           ;; F(a;1;z) = laguerre(-a,z)
           (lagpol (neg a) 0 arg))
          
          ((and (maxima-integerp a)
                (member ($sign a) '($neg nz)))
           ;; F(-n; c; z) and n a positive integer
           (1f1polys (list c) a arg))
          
          ((alike1 c (add a a))
	   ;; F(a;2a;z)
	   ;; A&S 13.6.6
	   ;;
	   ;; F(n+1;2*n+1;2*z) =
	   ;; gamma(3/2+n)*exp(z)*(z/2)^(-n-1/2)*bessel_i(n+1/2,z).
	   ;;
	   ;; So
	   ;;
	   ;; F(n,2*n,z) =
	   ;; gamma(n+1/2)*exp(z/2)*(z/4)^(-n-3/2)*bessel_i(n-1/2,z/2);
	   ;;
	   ;; If n is a negative integer, we use laguerre polynomial.
	   (if (and (maxima-integerp a)
	            (eq (asksign a) '$negative))
	       ;; We have already checked a negative integer. This algorithm
	       ;; is now present in 1f1polys and at this place never called.
	       (let ((n (neg a)))
	         (mul (power -1  n)
	              (inv (take '(%binomial) (add n n) n))
	              (lagpol n (sub c 1) arg)))
	       (let ((z (div arg 2)))
		 (mul (power '$%e z)
		      (bestrig (add a '((rat simp) 1 2))
		               (div (mul z z) 4))))))
          
          ((and (integerp (setq n (sub (add a a) c)))
                (plusp n)
                (not (integerp a))
                (not (integerp (add a a))))
           ;; F(a,2*a-n,z) and a not an integer or a half integral value
           (when *debug-hyp*
             (format t "~&Case 1F1(a,2*a-n,x):")
             (format t "~&   ; a = ~A~%" a)
             (format t "~&   ; c = ~A~%" c)
             (format t "~&   : n = ~A~%" n))
           (sratsimp
             (mul (take '(%gamma) (sub a (add n '((rat simp) 1 2))))
                  (power (div arg 4)
                         (sub (add '((rat simp) 1 2) n) a))
                  (power '$%e (div arg 2))
                  (let ((index (gensym)))
                    (dosum
                      (mul (power -1 index)
                           (take '($pochhammer) (- n) index)
                           (take '($pochhammer) (add a a (* -2 n) -1) index)
                           (add a index (- n) '((rat simp) -1 2))
                           (inv (take '($pochhammer) (sub (add a a) n) index))
                           (inv (take '(mfactorial) index))
                           (take '(%bessel_i)
                                 (add a index (- n) '((rat simp) -1 2))
                                 (div arg 2)))
                     index 0 n t)))))
                
          ((and (integerp (setq n (sub c (add a a))))
                (plusp n)
                (not (integerp a))
                (not (integerp (add a a))))
           ;; F(a,2*a+n,z) and a not an integer or a half integral value
           (when *debug-hyp*
             (format t "~&Case 1F1(a,2*a+n,x):")
             (format t "~&   ; a = ~A~%" a)
             (format t "~&   ; c = ~A~%" c)
             (format t "~&   : n = ~A~%" n))
           (sratsimp
             (mul (take '(%gamma) (sub a '((rat simp) 1 2)))
                  (power (div arg 4)
                         (sub '((rat simp) 1 2) a))
                  (power '$%e (div arg 2))
                  (let ((index (gensym)))
                    (dosum
                      (mul (take '($pochhammer) (- n) index)
                           (take '($pochhammer) (add a a -1) index)
                           (add a index '((rat simp) -1 2))
                           (inv (take '($pochhammer) (add a a n) index))
                           (inv (take '(mfactorial) index))
                           (take '(%bessel_i)
                                 (add a index '((rat simp) -1 2))
                                 (div arg 2)))
                     index 0 n t)))))
          
          ((and (integerp (setq n (sub a '((rat simp) 1 2))))
                (>= n 0)
                (integerp c)
                (plusp c))
           (let ((m c)
                 ($simpsum t)
                 ($bessel_reduce t))
             (when *debug-hyp*
               (format t "~&Case 1F1(n+1/2,m,x):")
               (format t "~&   ; a = ~A~%" a)
               (format t "~&   ; c = ~A~%" c)
               (format t "~&   : n = ~A~%" n)
               (format t "~&   : m = ~A~%" m))
             (sratsimp
               (mul (power 2 (- 1 m))
                    (power '$%e (div arg 2))
                    (factorial (- m 1))
                    (factorial n)
                    (inv (take '($pochhammer) '((rat simp) 1 2) (- m 1)))
                    (inv (take '($pochhammer) '((rat simp) 1 2) n))
                    (let ((index1 (gensumindex)))
                      (dosum
                        (mul (power 2 (neg index1))
                             (power (neg arg) index1)
                             (inv (take '(mfactorial) index1))
                             (mfuncall '$gen_laguerre
                                       (sub n index1)
                                       (sub index1 '((rat simp) 1 2))
                                       (neg arg))
                             (let ((index2 (gensumindex)))
                               (dosum
                                 (mul (power -1 index2)
                                      (power 2 (neg index2))
                                      (take '(%binomial)
                                            (add index1 m -1)
                                            index2)
                                      (let ((index3 (gensumindex)))
                                        (dosum
                                          (mul (take '(%binomial) index2 index3)
                                               (take '(%bessel_i)
                                                     (sub index2 (mul 2 index3))
                                                     (div arg 2)))
                                         index3 0 index2 t)))
                                index2 0 (add index1 m -1) t)))
                       index1 0 n t))))))
      
          ((and (integerp (setq n (sub a '((rat simp) 1 2))))
                (< n 0)
                (integerp c)
                (plusp c))
           (let ((n (- n))
                 (m c)
                 ($simpsum t)
                 ($bessel_reduce t))
             (when *debug-hyp*
               (format t "~&Case 1F1(1/2-n,m,x):")
               (format t "~&   ; a = ~A~%" a)
               (format t "~&   ; c = ~A~%" c)
               (format t "~&   : n = ~A~%" n)
               (format t "~&   : m = ~A~%" m))
             (sratsimp
               (mul (power -1 n)
                    (power 2 (- 1 m))
                    (power '$%e (div arg 2))
                    (factorial (- m 1))
                    (inv (take '($pochhammer) '((rat simp) 1 2) (- m 1)))
                    (inv (take '($pochhammer) (sub m '((rat simp) 1 2)) n))
                    (let ((index1 (gensumindex)))
                      (dosum
                        (mul (power 2 (neg index1))
                             (power arg index1)
                             (take '(%binomial) n index1)
                             (take '($pochhammer) 
                                   (sub '((rat simp) 3 2) (+ m n))
                                   (sub n index1))
                             (let ((index2 (gensumindex)))
                               (dosum
                                 (mul (power '((rat simp) -1 2) index2)
                                      (take '(%binomial)
                                            (add index1 m -1)
                                            index2)
                                      (let ((index3 (gensumindex)))
                                        (dosum
                                          (mul (take '(%binomial) index2 index3)
                                               (take '(%bessel_i)
                                                     (sub index2 (mul 2 index3))
                                                     (div arg 2)))
                                          index3 0 index2 t)))
                                 index2 0 (add index1 m -1) t)))
                        index1 0 n t))))))
          
	  ((not (hyp-integerp a-c))
	   (cond ((hyp-integerp a)
		  (kummer arg-l1 arg-l2 arg))
		 ($prefer_whittaker
		  ;; A&S 15.1.32:
		  ;;
		  ;; %m[k,u](z) = exp(-z/2)*z^(u+1/2)*M(1/2+u-k,1+2*u,z)
		  ;;
		  ;; So
		  ;;
		  ;; M(a,c,z) = exp(z/2)*z^(-c/2)*%m[c/2-a,c/2-1/2](z)
		  ;;
		  ;; But if we apply Kummer's transformation, we can also
		  ;; derive the expression
		  ;;
		  ;; %m[k,u](z) = exp(z/2)*z^(u+1/2)*M(1/2+u+k,1+2*u,-z)
		  ;;
		  ;; or
		  ;;
		  ;; M(a,c,z) = exp(-z/2)*(-z)^(-c/2)*%m[a-c/2,c/2-1/2](-z)
		  ;;
		  ;; For Laplace transforms it might be more beneficial to
		  ;; return this second form instead.
		  (let* ((m (div (sub c 1) 2))
			 (k (add '((rat simp) 1 2) m (mul -1 a))))
		    (mul (power arg (mul -1 (add '((rat simp) 1 2) m)))
			 (power '$%e (div arg 2))
			 (whitfun k m arg))))
		 (t
		  (fpqform arg-l1 arg-l2 arg))))
	  ((minusp a-c)
	   (sratsimp (erfgammared a c arg)))
	  (t
	   (kummer arg-l1 arg-l2 arg)))))

;; A&S 13.6.19:
;; M(1/2,3/2,-z^2) =  sqrt(%pi)*erf(z)/2/sqrt(z)
;;
;; So M(1/2,3/2,z) = sqrt(%pi)*erf(sqrt(-z))/2/sqrt(-z)
;;                 = sqrt(%pi)*erf(%i*sqrt(z))/2/(%i*sqrt(z))
(defun hyprederf (x)
  (let ((x (mul '$%i (power x '((rat simp) 1 2 )))))
    (mul (power '$%pi '((rat simp) 1 2))
         '((rat simp) 1 2)
         (inv x)
         (take '(%erf) x))))

;; M(a,c,z), where a-c is a negative integer.
(defun erfgammared (a c z)
  (cond ((and (nump a) (nump c))
	 (erfgamnumred a c z))
	(t (gammareds a c z))))

;; I (rtoy) think this is what the function above is doing, but I'm
;; not sure.  Plus, I think it's wrong.
;;
;; For hgfred([n],[2+n],-z), the above returns
;;
;; 2*n*(n+1)*z^(-n-1)*(gamma_incomplete_lower(n,z)*z-gamma_incomplete_lower(n+1,z))
;;
;; But from A&S 13.4.3
;;
;; -M(n,2+n,z) - n*M(n+1,n+2,z) + (n+1)*M(n,n+1,z) = 0
;;
;; so M(n,2+n,z) = (n+1)*M(n,n+1,z)-n*M(n+1,n+2,z)
;;
;; And M(n,n+1,-z) = n*z^(-n)*gamma_incomplete_lower(n,z)
;;
;; This gives
;;
;; M(n,2+n,z) = (n+1)*n*z^(-n)*gamma_incomplete_lower(n,z) - n*(n+1)*z^(-n-1)*gamma_incomplete_lower(n+1,z)
;;            = n*(n+1)*z^(-n-1)*(gamma_incomplete_lower(n,z)*n-gamma_incomplete_lower(n+1,z))
;;
;; So the version above is off by a factor of 2.  But I think it's more than that.
;; Using A&S 13.4.3 again,
;;
;; M(n,n+3,-z) = [n*M(n+1,n+3,-z) - (n+2)*M(n,n+2,-z)]/(-2);
;;
;; The version above doesn't produce anything like this equation would
;; produce, given the value of M(n,n+2,-z) derived above.
(defun gammareds (a c z)
  ;; M(a,c,z) where a-c is a negative integer.
  (let ((diff (sub c a)))
    (cond ((eql diff 1)
	   ;; We have M(a,a+1,z).
	   (hypredincgm a z))
	  ((eql a 1)
	   ;; We have M(1,a,z)
	   ;; Apply Kummer's transformation to get the form M(a-1,a,z)
	   ;;
	   ;; (I don't think we ever get here, but just in case, we leave it.)
	   (kummer (list a) (list c) z))
	  (t
	   ;; We have M(a, a+n, z)
	   ;;
	   ;; A&S 13.4.3 says
	   ;; (1+a-b)*M(a,b,z) - a*M(a+1,b,z)+(b-1)*M(a,b-1,z) = 0
	   ;;
	   ;; So
	   ;;
	   ;; M(a,b,z) = [a*M(a+1,b,z) - (b-1)*M(a,b-1,z)]/(1+a-b);
	   ;;
	   ;; Thus, the difference between b and a is reduced, until
	   ;; b-a=1, which we handle above.
	   (mul (sub (mul a
			  (gammareds (add 1 a) c z))
		     (mul (sub c 1)
			  (gammareds a (sub c 1) z)))
		(inv (sub (add 1 a) c)))))))

;; A&S 6.5.12: 
;; gamma_incomplete_lower(a,x) = x^a/a*M(a,1+a,-x)
;;                  = x^a/a*exp(-x)*M(1,1+a,x)
;;
;; where gamma_incomplete_lower(a,x) is the lower incomplete gamma function.
;;
;; M(a,1+a,x) = a*(-x)^(-a)*gamma_incomplete_lower(a,-x)
(defun hypredincgm (a z)
  (let ((-z (mul -1 z)))
    (if (not $prefer_gamma_incomplete)
        (mul a
             (power -z (mul -1 a))
             (take '(%gamma_incomplete_lower) a -z))
        (mul a
             (power -z (mul -1 a))
             (sub (take '(%gamma) a)
                  (take '(%gamma_incomplete) a -z))))))

;; M(a,c,z), when a and c are numbers, and a-c is a negative integer
(defun erfgamnumred (a c z)
  (cond ((hyp-integerp (sub c '((rat simp) 1 2)))
         (erfred a c z))
	(t (gammareds a c z))))

;; M(a,c,z) when a and c are numbers and c-1/2 is an integer and a-c
;; is a negative integer.  Thus, we have M(p+1/2, q+1/2,z)
(defun erfred (a c z)
  (prog (n m)
     (setq n (sub a '((rat simp) 1 2))
           m (sub c '((rat simp) 3 2)))
     ;; a = n + 1/2
     ;; c = m + 3/2
     ;; a - c < 0 so n - m - 1 < 0
     (cond ((not (or (> n m) (minusp n)))
	    ;; 0 <= n <= m
	    (return (thno33 n m z)))
           ((and (minusp n) (minusp m))
            ;; n < 0 and m < 0
            (return (thno35 (mul -1 n) (mul -1 m) z)))
           ((and (minusp n) (plusp m))
            ;; n < 0 and m > 0
            (return (thno34 (mul -1 n) m z)))
           (t
            ;; n = 0 or m = 0
            (return (gammareds (add n '((rat simp) 1 2))
                               (add m '((rat simp) 3 2))
                               z))))))

;; Compute M(n+1/2, m+3/2, z) with 0 <= n <= m.
;;
;; I (rtoy) think this is what this routine is doing.  (I'm guessing
;; that thno33 means theorem number 33 from Yannis Avgoustis' thesis.)
;;
;; I don't have his thesis, but I see there are similar ways to derive
;; the result we want.
;;
;; Method 1:
;;   Use Kummer's transformation (A&S ) to get
;;
;;     M(n+1/2,m+3/2,z) = exp(z)*M(m-n+1,m+3/2,-z)
;;
;;   From A&S, we have
;;
;;     diff(M(1,n+3/2,z),z,m-n) = poch(1,m-n)/poch(n+3/2,m-n)*M(m-n+1,m+3/2,z)
;;
;;   Apply Kummer's transformation again:
;;
;;     M(1,n+3/2,z) = exp(z)*M(n+1/2,n+3/2,-z)
;;
;;   Apply the differentiation formula again:
;;
;;     diff(M(1/2,3/2,z),z,n) = poch(1/2,n)/poch(3/2,n)*M(n+1/2,n+3/2,z)
;;
;;   And we know that M(1/2,3/2,z) can be expressed in terms of erf.
;;
;; Method 2:
;;
;;   Since n <= m, apply the differentiation formula:
;;
;;     diff(M(1/2,m-n+3/2,z),z,n) = poch(1/2,n)/poch(m-n+3/2,n)*M(n+1/2,m+3/2,z)
;;
;;   Apply Kummer's transformation:
;;
;;     M(1/2,m-n+3/2,z) = exp(z)*M(m-n+1,m-n+3/2,z)
;;
;;   Apply the differentiation formula again:
;;
;;     diff(M(1,3/2,z),z,m-n) = poch(1,m-n)/poch(3/2,m-n)*M(m-n+1,m-n+3/2,z)
;;
;; I think this routine uses Method 2.
(defun thno33 (n m x)
  ;; M(n+1/2,m+3/2,z) = diff(M(1/2,m-n+3/2,z),z,n)*poch(m-n+3/2,n)/poch(1/2,n)
  ;; M(1/2,m-n+3/2,z) = exp(z)*M(m-n+1,m-n+3/2,-z)
  ;; M(m-n+1,m-n+3/2,z) = diff(M(1,3/2,z),z,m-n)*poch(3/2,m-n)/poch(1,m-n)
  ;; diff(M(1,3/2,z),z,m-n) = (-1)^(m-n)*diff(M(1,3/2,-z),z,m-n)
  ;; M(1,3/2,-z) = exp(-z)*M(1/2,3/2,z)
  (let* ((yannis (gensym))
         (m-n (sub m n))
	 ;; poch(m-n+3/2,n)/poch(1/2,n)
	 (factor1 (div (take '($pochhammer) (add m-n '((rat simp) 3 2)) n)
		       (take '($pochhammer) '((rat simp) 1 2) n)))
	 ;; poch(3/2,m-n)/poch(1,m-n)
	 (factor2 (div (take '($pochhammer) '((rat simp) 3 2) m-n)
		       (take '($pochhammer) 1 m-n)))
	 ;; M(1,3/2,-z) = exp(-z)*M(1/2,3/2,z)
	 (hgferf (mul (power '$%e (mul -1 yannis))
		      (hyprederf yannis)))
	 ;; diff(M(1,3/2,z),z,m-n)
	 (diff1 (meval (list '($diff) hgferf yannis m-n)))
	 ;; exp(z)*M(m-n+1,m-n+3/2,-z)
	 (kummer (mul (power '$%e yannis) diff1))
	 ;; diff(M(1/2,m-n+3/2,z),z,n)
	 (diff2 (meval (list '($diff) kummer yannis n))))
    ;; Multiply all the terms together.
    (sratsimp (mul (power -1 m-n)
                   factor1
                   factor2
                   (maxima-substitute x yannis diff2)))))

;; M(n+1/2,m+3/2,z), with n < 0 and m > 0
;;
;; Let's write it more explicitly as M(-n+1/2,m+3/2,z) with n > 0 and
;; m > 0.
;;
;; First, use Kummer's transformation to get
;;
;;    M(-n+1/2,m+3/2,z) = exp(z)*M(m+n+1,m+3/2,-z)
;;
;; We also have
;;
;;    diff(z^(n+m)*M(m+1,m+3/2,z),z,n) = poch(m+1,n)*z^m*M(m+n+1,m+3/2,z)
;;
;; And finally
;;
;;    diff(M(1,3/2,z),z,m) = poch(1,m)/poch(3/2,m)*M(m+1,m+3/2,z)
;;
;; Thus, we can compute M(-n+1/2,m+3/2,z) from M(1,3/2,z).
;;
;; The second formula above can be derived easily by multiplying the
;; series for M(m+1,m+3/2,z) by z^(n+m) and differentiating n times.

(defun thno34 (n m x)
  (let ((yannis (gensym)))
    (sratsimp
      (maxima-substitute 
        x
        yannis
        (mul (power -1 m)
             (div (mul (take '($pochhammer) '((rat simp) 3 2) m)
                       (power '$%e yannis))
                  (mul (take '($pochhammer) 1 m)
                       (take '($pochhammer) (1+ m) n)
                       (power yannis m)))
             (meval (list '($diff)
                          (mul (power yannis (+ m n))
                               (meval (list '($diff)
                                            (mul (power '$%e
                                                        (mul -1 yannis))
                                                 (hyprederf yannis))
                                            yannis
                                            m)))
                          yannis
                          n)))))))

;; M(n+1/2,m+3/2,z), with n < 0 and m < 0
;;
;; Write it more explicitly as M(-n+1/2,-m+3/2,z) with n > 0 and m >
;; 0.
;;
;; We know that
;;
;;    diff(sqrt(z)*M(-n+1/2,3/2,z),z,m) = poch(3/2-m,m)*M(-n+1/2,-m+3/2,z).
;;
;; Apply Kummer's transformation:
;;
;;    M(-n+1/2,3/2,z) = exp(z) * M(n+1,3/2,-z)
;;
;; Finally
;;
;;    diff(z^n*M(1,3/2,z),z,n) = n!*M(n+1,3/2,z)
;;
;; So we can express M(-n+1/2,-m+3/2,z) in terms of M(1,3/2,z).
;;
;; The first formula above follows from the more general formula
;;
;;    diff(z^(b-1)*M(a,b,z),z,n) = poch(b-n,n)*z^(b-n-1)*M(a,b-n,z)
;;
;; The last formula follows from the general result
;;
;;    diff(z^(a+n-1)*M(a,b,z),z,n) = poch(a,n)*z^(a-1)*M(a+n,b,z)
;;
;; Both of these are easily derived by using the series for M and
;; differentiating.

(defun thno35 (n m x)
  (let ((yannis (gensym)))
    (sratsimp
      (maxima-substitute 
        x
        yannis
        (mul (div (power yannis (sub m '((rat simp) 1 2)))
                  (mul (power -1 (* -1 m))
                       (take '($pochhammer) 1 n)
                       (take '($pochhammer) '((rat simp) -1 2) m)))
             (meval (list '($diff)
                          (mul (power yannis '((rat simp) 1 2))
                               (power '$%e yannis)
                               (meval (list '($diff)
                                            (mul (power '$%e
                                                        (mul -1 yannis))
                                                 (power yannis n)
                                                 (hyprederf yannis))
                                            yannis
                                            n)))
                          yannis
                          m)))))))

;; Pochhammer symbol. fctrl(a,n) = a*(a+1)*(a+2)*...*(a+n-1).
;;
;; N must be a positive integer!
;;
;; FIXME:  This appears to be identical to factf below.
(defun fctrl (a n)
  (cond ((zerop n)
	 1)
	((equal n 1)
	 a)
	(t
	 (mul (add a (1- n))
	      (fctrl a (1- n))))))

(setq *par* '$p)                           

(defun vfvp (exp arg)
  (m2 exp `(v freevarpar2 ,arg)))


(defun fpqform (arg-l1 arg-l2 arg)
  (list '(mqapply)
	(list '($%f simp array) (length arg-l1)(length arg-l2))
	(append (list '(mlist simp)) arg-l1)
	(append (list '(mlist simp)) arg-l2)
	arg))

;; Consider pFq([a_k]; [c_j]; z).  If a_k = c_j + m for some k and j
;; and m >= 0, we can express pFq in terms of (p-1)F(q-1).
;;
;; Here is a derivation for F(a,b;c;z), but it generalizes to the
;; generalized hypergeometric very easily.
;;
;; From A&s 15.2.3:
;;
;; diff(z^(a+n-1)*F(a,b;c;z), z, n) = poch(a,n)*z^(a-1)*F(a+n,b;c;z)
;;
;; F(a+n,b;c;z) = diff(z^(a+n-1)*F(a,b;c;z), z, n)/poch(a,n)/z^(a-1)
;;
;;
;; So this expresses F(a+n,b;c;z) in terms of F(a,b;c;z).  Let a = c +
;; n.  This therefore gives F(c+n,b;c;z) in terms of F(c,b;c;z) =
;; 1F0(b;;z), which we know.
;;
;; For simplicity, we will write F(z) for F(a,b;c;z).
;;
;; Now,
;;
;;                       n
;; diff(z^x*F(z),z,n) = sum binomial(n,k)*diff(z^x,z,n-k)*diff(F(z),z,k)
;;                      k=0
;;
;; But diff(z^x,z,n-k) = x*(x-1)*...*(x-n+k+1)*z^(x-n+k)
;;                     = poch(x-n+k+1,n-k)*z^(x-n+k)
;;
;; so
;; 
;; z^(-a+1)/poch(a,n)*diff(z^(a+n-1),z,n-k)
;;    = poch(a+n-1-n+k+1,n-k)/poch(a,n)*z^(a+n-1-n+k)*z^(-a+1)
;;    = poch(a+k,n-k)/poch(a,n)*z^k
;;    = z^k/poch(a,k)
;;
;; Combining these we have
;;
;;                 n
;; F(a+n,b;c;z) = sum z^k/poch(a,k)*binomial(n,k)*diff(F(a,b;c;z),z,k)
;;                k=0
;;
;; Since a = c, we have
;;
;;                 n
;; F(a+n,b;a;z) = sum z^k/poch(a,k)*binomial(n,k)*diff(F(a,b;a;z),z,k)
;;                k=0
;;
;; But F(a,b;a;z) = F(b;;z) and it's easy to see that A&S 15.2.2 can
;; be specialized to this case to give
;;
;; diff(F(b;;z),z,k) = poch(b,k)*F(b+k;;z)
;;
;; Finally, combining all of these, we have
;;
;;                 n
;; F(a+n,b;c;z) = sum z^k/poch(a,k)*binomial(n,k)*poch(b,k)*F(b+k;;z)
;;                k=0
;;
;; Thus, F(a+n,b;c;z) is expressed in terms of 1F0(b+k;;z), as desired.
(defun splitpfq (l arg-l1 arg-l2 arg)
  (destructuring-bind (a1 k)
      l
    (let* ((result 0)
	   (prodnum 1)
	   (proden 1)
	   (b1 (sub a1 k))
	   (prod-b 1)
	   (arg-l1 (delete a1 arg-l1 :count 1 :test #'equal))
	   (arg-l2 (delete b1 arg-l2 :count 1 :test #'equal)))
      (loop for count from 0 upto k
	 do
	   (when $trace2f1
	     (format t "splitpfg term:~%")
	     (maxima-display (mul (combin k count)
				  (div prodnum proden)
				  (inv prod-b)
				  (power arg count)))
	     (mtell "F(~:M, ~:M)~%" 
	            (cons '(mlist) arg-l1) 
	            (cons '(mlist) arg-l2)))
	 (setq result (add result
			   (mul (combin k count)
				(div prodnum proden)
				(inv prod-b)
				(power arg count)
				(hgfsimp arg-l1 arg-l2 arg))))
	 (setq prod-b (mul prod-b (add b1 count)))
	 (setq prodnum (mul prodnum (mull arg-l1))
	       proden (mul proden (mull arg-l2)))
	 (setq arg-l1 (incr1 arg-l1))
	 (setq arg-l2 (incr1 arg-l2)))
      result)))

;; binomial(k,count)
(defun combin (k count)
  (div (factorial k)
       (mul (factorial count)
	    (factorial (sub k count)))))


;; We have something like F(s+m,-s+n;c;z)
;; Rewrite it like F(a'+d,-a';c;z) where a'=s-n=-b and d=m+n.
;;
(defun algii (a b)
  (let* ((sym (cdras 'f (s+c a)))
	 (sign (cdras 'm (m2 sym '((mtimes) ((coefft) (m $numberp)) ((coefft) (s nonnump)))))))
    (when (and sign (minusp sign))
      (rotatef a b))
    (list nil (mul -1 b) (add a b))))


;;Algor. 2F1-RL from thesis:step 4:dispatch on a+m,-a+n,1/2+l cases
(defun step4 (a b c arg)
  ;; F(a,b;c;z) where a+b is an integer and c+1/2 is an integer.  If a
  ;; and b are not integers themselves, we can derive the result from
  ;; F(a1,-a1;1/2;z).  However, if a and b are integers, we can't use
  ;; that because F(a1,-a1;1/2;z) is a polynomial.  We need to derive
  ;; the result from F(1,1;3/2;z).
  (if (and (hyp-integerp a)
	   (hyp-integerp b))
      (step4-int a b c arg)
      (step4-a a b c arg)))

(defun step4-a (a b c arg)
  (let* ((alglist (algii a b))
	 (aprime (cadr alglist))
	 (m (caddr alglist))
	 (n (sub c (inv 2)))
	 ($ratsimpexpons $true)
	 ($ratprint $false))
    ;; At this point, we have F(a'+m,-a';1/2+n;z) where m and n are
    ;; integers.
    (cond ((hyp-integerp (add aprime (inv 2)))
	   ;; Ok.  We have a problem if aprime + 1/2 is an integer.
	   ;; We can't always use the algorithm below because we have
	   ;; F(1/2,-1/2;1/2;z) which is 1F0(-1/2;;z) so the
	   ;; derivation isn't quite right.  Also, sometimes we'll end
	   ;; up with a division by zero.
	   ;;
	   ;; Thus, We need to do something else.  So, use A&S 15.3.3
	   ;; to change the problem:
	   ;;
	   ;; F(a,b;c;z) = (1-z)^(c-a-b)*F(c-a, c-b; c; z)
	   ;;
	   ;; which is
	   ;;
	   ;; F('a+m,-a';1/2+n;z) = (1-z)^(1/2+n-m)*F(1/2+n-a'-m,1/2+n+a';1/2+n;z)
	   ;;
	   ;; Recall that a' + 1/2 is an integer.  Thus we have
	   ;; F(<int>,<int>,1/2+n;z), which we know how to handle in
	   ;; step4-int.
	   (gered1 (list a b) (list c) #'hgfsimp arg))
	  (t
	   (let ((newf 
		  (cond ((equal (checksigntm arg) '$positive)
			 (trig-log-1-pos aprime 'ell))
			((equal (checksigntm arg) '$negative)
			 (trig-log-1-neg (mul -1 aprime) aprime 'ell)))))
	     ;; Ok, this uses F(a,-a;1/2;z).  Since there are 2 possible
	     ;; representations (A&S 15.1.11 and 15.1.17), we check the sign
	     ;; of the arg (as done in trig-log-1) to select which form we
	     ;; want to use.  The original didn't and seemed to want to use
	     ;; the negative form.
	     ;;
	     ;; With this change, F(a,-a;3/2;z) matches what A&S 15.2.6 would
	     ;; produce starting from F(a,-a;1/2;z), assuming z < 0.
    
	     (subst arg 'ell
		    (algiii newf
			    m n aprime)))))))

;; F(a,b;c;z), where a and b are (positive) integers and c = 1/2+l.
;; This can be computed from F(1,1;3/2;z).
;;
;; Assume a < b, without loss of generality.
;;
;; F(m,n;3/2+L;z), m < n.
;;
;; We start from F(1,1;3/2;z).  Use A&S 15.2.3, differentiating m
;; times to get F(m,1;3/2;z).  Swap a and b to get F(m,1;3/2;z) =
;; F(1,m;3/2;z) and use A&S 15.2.3 again to get F(n,m;3/2;z) by
;; differentiating n times.  Finally, if L < 0, use A&S 15.2.4.
;; Otherwise use A&S 15.2.6.
;;
;; I (rtoy) can't think of any way to do this with less than 3
;; differentiations.
;;
;; Note that if d = (n-m)/2 is not an integer, we can write F(m,n;c;z)
;; as F(-d+u,d+u;c;z) where u = (n+m)/2.  In this case, we could use
;; step4-a to compute the result.


;; Transform F(a,b;c;z) to F(a+n,b;c;z), given F(a,b;c;z)
(defun as-15.2.3 (a bb cx n arg fun)
  (declare (ignore bb cx))
  (assert (>= n 0))
  ;; A&S 15.2.3:
  ;; F(a+n,b;c;z) = z^(1-a)/poch(a,n)*diff(z^(a+n-1)*fun,z,n)
  (mul (inv (factf a n))
       (power arg (sub 1 a))
       ($diff (mul (power arg (sub (add a n) 1))
		   fun)
	      arg n)))

;; Transform F(a,b;c;z) to F(a,b;c-n;z), given F(a,b;c;z)
(defun as-15.2.4 (axax bb c n arg fun)
  (declare (ignore axax bb))
  (assert (>= n 0))
  ;; A&S 15.2.4
  ;; F(a,b;c-n;z) = 1/poch(c-n,n)/z^(c-n-1)*diff(z^(c-1)*fun,z,n)
  (mul (inv (factf (sub c n) n))
       (inv (power arg (sub (sub c n) 1)))
       ($diff (mul (power arg (sub c 1))
		   fun)
	      arg n)))

;; Transform F(a,b;c;z) to F(a-n,b;c;z), given F(a,b;c;z)
(defun as-15.2.5 (a b c n arg fun)
  ;; A&S 15.2.5
  ;; F(a-n,b;c;z) = 1/poch(c-a,n)*z^(1+a-c)*(1-z)^(c+n-a-b)
  ;;                 *diff(z^(c-a+n-1)*(1-z)^(a+b-c)*F(a,b;c;z),z,n)
  (assert (>= n 0))
  (mul (inv (factf (sub c a) n))
       (power arg (sub (add a 1) c))
       (power (sub 1 arg)
	      (sub (add c n) (add a b)))
       ($diff (mul (power arg (sub (add c n)
				   (add a 1)))
		   (power (sub 1 arg)
			  (sub (add a b) c))
		   fun)
	      arg n)))

;; Transform F(a,b;c;z) to F(a,b;c+n;z), given F(a,b;c;z)
(defun as-15.2.6 (a b c n arg fun)
  ;; A&S 15.2.6
  ;; F(a,b;c+n;z) = poch(c,n)/poch(c-a,n)/poch(c-b,n)*(1-z)^(c+n-a-b)
  ;;                 *diff((1-z)^(a+b-c)*fun,z,n)
  (assert (>= n 0))
  (mul (factf c n)
       (inv (factf (sub c a) n))
       (inv (factf (sub c b) n))
       (inv (power (sub 1 arg) (sub (add a b)
				    (add c n))))
       ($diff (mul (power (sub 1 arg) (sub (add a b) c))
		   fun)
	      arg n)))

;; Transform F(a,b;c;z) to F(a+n, b; c+n; z)
(defun as-15.2.7 (a b c n arg fun)
  ;; A&S 15.2.7
  ;; F(a+n,b;c+n;z) = (-1)^n*poch(c,n)/poch(a,n)/poch(c-b,n)*(1-z)^(1-a)
  ;;                    *diff((1-z)^(a+n-1)*fun, z, n)
  (assert (>= n 0))
  (mul (power -1 n)
       (factf c n)
       (inv (factf a n))
       (inv (factf (sub c b) n))
       (power (sub 1 arg) (sub 1 a))
       ($diff (mul (power (sub 1 arg) (sub (add a n) 1))
		   fun)
	      arg n)))

;; Transform F(a,b;c;z) to F(a-n, b; c-n; z)
(defun as-15.2.8 (axax b c n arg fun)
  ;; A&S 15.2.8
  ;;  F(a-n,b;c-n;z) = 1/poch(c-n,n)/(z^(c-n-1)*(1-z)^(b-c))
  ;;                    *diff(z^(c-1)*(1-z^(b-c+n)*fun, z, n))
  (declare (ignore axax))
  (assert (>= n 0))
  (mul (inv (factf (sub c n) n))
       (inv (mul (power arg (sub (sub c n) 1))
		 (power (sub 1 arg) (sub b c))))
       ($diff (mul (power arg (sub c 1))
		   (power (sub 1 arg) (add (sub b c) n))
		   fun)
	      arg n)))

;; Transform F(a,b;c;z) to F(a+n,b+n;c+n;z)
(defun as-15.2.2 (a b c n arg fun)
  ;; A&S 15.2.2
  ;; F(a+n,b+n; c+n;z) = poch(c,n)/poch(a,n)/poch(b,n)
  ;;                      *diff(fun, z, n)
  (assert (>= n 0))
  (mul (factf c n)
       (inv (factf a n))
       (inv (factf b n))
       ($diff fun arg n)))

;; Transform F(a,b;c;z) to F(a-n,b-n;c-n;z)
(defun as-15.2.9 (a b c n arg fun)
  ;; A&S 15.2.9
  ;; F(a-n,b-n; c-n;z) = 1/poch(c-n,n)/(z^(c-n-1)*(1-z)^(a+b-c-n))
  ;;                      *diff(z^(c-1)*(1-z)^(a+b-c)*fun, z, n)
  (assert (>= n 0))
  (mul (inv (factf (sub c n) n))
       (inv (mul (power arg (sub (sub c n) 1))
		 (power (sub 1 arg) (sub (add a b)
					 (add c n)))))
       ($diff (mul (power arg (sub c 1))
		   (power (sub 1 arg) (sub (add a b) c))
		   fun)
	      arg n)))

(defun step4-int (a b c arg)
  (if (> a b)
      (step4-int b a c arg)
      (let* ((s (gensym (symbol-name '#:step4-arg-)))
	     (m (1- a))
	     (n (1- b))
	     (ell (sub c 3//2))
	     (res (cond ((eq (checksigntm arg) '$negative)
			 ;; F(1,1;3/2;z) =
			 ;; -%i*log(%i*sqrt(zn)+sqrt(1-zn))/(sqrt(1-zn)*sqrt(zn))
			 ;; for z < 0
			 (let ((root1-z (power (sub 1 s) (inv 2)))
			       (rootz (power s (inv 2))))
			   (mul -1 '$%i
				(mlog (add (mul '$%i rootz)
					   root1-z))
				(inv root1-z)
				(inv rootz))))
			(t
			 ;; F(1,1;3/2;z) = asin(sqrt(zp))/(sqrt(1-zp)*sqrt(zp))
			 ;; for z > 0
			 (let ((root1-z (power (sub 1 s) (inv 2)))
			       (rootz (power s (inv 2))))
			   (mul (masin rootz)
				(inv root1-z)
				(inv rootz)))))))
	;; Start with res = F(1,1;3/2;z).  Compute F(m,1;3/2;z)
	(setf res (as-15.2.3 1 1 3//2 m s res))
	;; We now have res = C*F(m,1;3/2;z).  Compute F(m,n;3/2;z)
	(setf res (as-15.2.3 1 a 3//2 n s res))
	;; We now have res = C*F(m,n;3/2;z).  Now compute F(m,n;3/2+ell;z):
	(subst arg s
	       (cond ((minusp ell)
		      (as-15.2.4 a b 3//2 (- ell) s res))
		     (t
		      (as-15.2.6 a b 3//2 ell s res)))))))

;;Pattern match for s(ymbolic) + c(onstant) in parameter
(defun s+c (exp)
  (m2 exp '((mplus) ((coeffpt)(f nonnump)) ((coeffpp)(c $numberp)))))

(defun nonnump (z)
  (cond ((not ($numberp z)) t)
	(t nil)))

;;Algor. III from thesis:determines which Differ. Formula to use
(defun algiii (fun m n aprime)
  (let ((mm (abs m))
	(nn (abs n)))
    (cond ((and (nni m) (nni n))
	   (cond ((< m n)
		  (f81 fun m n aprime))
		 (t
		  (f85 fun mm nn aprime))))
	  ((and (hyp-negp n) (hyp-negp m))
	   (cond ((> (abs m) (abs n))
		  (f86 fun mm nn aprime))
		 (t
		  (f82 fun mm nn aprime))))
	  ((and (hyp-negp m) (nni n))
	   (f83 fun mm nn aprime))
	  (t
	   (f84 fun mm nn aprime)))))

;; Factorial function:x*(x+1)*(x+2)...(x+n-1)
;;
;; FIXME:  This appears to be identical to fctrl above
(defun factf (x n)
  (cond ((zerop n) 1)
	(t (mul x (factf (add x 1) (sub n 1))))))

;;Formula  #85 from Yannis thesis:finds by differentiating F[2,1](a,b,c,z)
;; given F[2,1](a+m,b,c+n,z) where b=-a and c=1/2, n,m integers

;; Like F81, except m > n.
;;
;; F(a+m,-a;c+n;z), m > n, c = 1/2, m and n are non-negative integers
;;
;; A&S 15.2.3
;; diff(z^(a+m-n-1)*F(a,-a;1/2;z),z,m-n) = poch(a,m-n)*z^(a-1)*F(a+m-n,-a;1/2;z)
;;
;; A&S 15.2.7
;; diff((1-z)^(a+m-1)*F(a+m-n,-a;1/2;z),z,n)
;;     = (-1)^n*poch(a+m-n,n)*poch(1/2+a,n)/poch(1/2,n)*(1-z)^(a+m-n-1)
;;         * F(a+m,-a;1/2+n;z)
;;
(defun f85 (fun m n a)
  (mul (factf (inv 2) n)
       (inv (power -1 n))
       (inv (factf (sub (add a m)
			n)
		   n))
       (inv (factf (sub (inv 2)
			(mul a -1))
		   n))
       (inv (factf a (- m n)))
       (power (sub 1 'ell) (sub (sub (add 1 n) m) a))
       ($diff (mul (power (sub 1 'ell) (sub (add a m) 1))
		   (power 'ell (sub 1 a))
		   ($diff (mul (power 'ell (sub (add a m -1) n))
			       fun)
			  'ell (- m n)))
	      'ell n)))

;;Used to find negative things that are not integers,eg RAT's	
(defun hyp-negp (x)
  (cond ((equal (asksign x) '$negative)
	 t)
	(t nil)))

;; F(a,-a+m; c+n; z) where m,n are non-negative integers, m < n, c = 1/2.
;;
;; A&S 15.2.6
;; diff((1-z)^(a+b-c)*F(a,b;c;z),z,n)
;;    = poch(c-a,n)*poch(c-b,n)/poch(c,n)*(1-z)^(a+b-c-n)*F(a,b;c+n;z)
;;
;; A&S 15.2.7:
;; diff((1-z)^(a+m-1))*F(a,b;c;z),z,m)
;;    = (-1)^m*poch(a,m)*poch(c-b,m)/poch(c,m)*(1-z)^(a-1)*F(a+m,b;c+m;z)
;;
;; Rewrite F(a,-a+m; c+n;z) as F(-a+m, a; c+n; z).  Then apply 15.2.6
;; to F(-a,a;1/2;z), differentiating n-m times:
;;
;; diff((1-z)^(-1/2)*F(-a,a;1/2;z),z,n-m)
;;     = poch(1/2+a,n-m)*poch(1/2-a,n-m)/poch(1/2,n-m)*(1-z)^(-1/2-n+m)*F(-a,a;1/2+n-m;z)
;;
;; Multiply this result by (1-z)^(n-a-1/2) and apply 15.2.7, differentiating m times:
;;
;; diff((1-z)^(m-a-1)*F(-a,a;1/2+n-m;z),z,m)
;;     = (-1)^m*poch(-a,m)*poch(1/2+n-m-a,m)/poch(1/2+n-m)*(1-z)^(-a-1)*F(-a+m,a;1/2+n;z)
;;
;; Which gives F(-a+m,a;1/2+n;z), which is what we wanted.
(defun f81 (fun m n a)
  (mul (factf (add (inv 2) (- n m)) m)
       (factf (inv 2) (- n m))
       (inv (power -1 m))
       (inv (factf a m))
       (inv (factf (add (inv 2) n (sub a m)) m))
       (inv (factf (sub (inv 2) a) (- n m)))
       (inv (factf (add (inv 2) a) (- n m)))
       (power (sub 1 'ell) (sub 1 a))
       ($diff (mul (power (sub 1 'ell) (add a n (inv -2)))
		   ($diff (mul (power (sub 1 'ell) (inv -2))
			       fun)
			  'ell (- n m)))
	      'ell m)))

;; Like f86, but |n|>=|m|
;;
;; F(a-m,-a;1/2-n;z) where n >= m >0
;;
;; A&S 15.2.4
;; diff(z^(c-1)*F(a,b;c;z),z,n)
;;     = poch(c-n,n)*z^(c-n-1)*F(a;b;c-n;z)
;;
;; A&S 15.2.8:
;; diff(z^(c-1)*(1-z)^(b-c+n)*F(a,b;c;z),z,n)
;;     = poch(c-n,n)*z^(c-n-1)*(1-z)^(b-c)*F(a-n,b;c-n;z)
;;
;; For our problem:
;;
;; diff(z^(-1/2)*F(a,-a;1/2;z),z,n-m)
;;     = poch(1/2-n+m,n-m)*z^(m-n-1/2)*F(a,-a;1/2-n+m;z)
;;
;; diff(z^(m-n-1/2)*(1-z)^(n-a-1/2)*F(a,-a;1/2-n+m;z),z,m)
;;     = poch(1/2-n,m)*z^(-1/2-n)*(1-z)^(n-m-a-1/2)*F(a-m,-a;1/2-n;z)
;;
;; So
;;
;; G(z) = z^(m-n-1/2)*F(a,-a;1/2-n+m;z)
;;      = z^(n-m+1/2)/poch(1/2-n+m,n-m)*diff(z^(-1/2)*F(a,-a;1/2;z),z,n-m)
;;
;; F(a-m,-a;1/2-n;z)
;;     = z^(n+1/2)*(1-z)^(m+a-1/2-n)/poch(1/2-n,m)*diff((1-z)^(n-a-1/2)*G(z),z,m)
(defun f82 (fun m n a)
  (mul (inv (factf (sub (inv 2) n) m))
       (inv (factf (sub (add (inv 2) m) n) (- n m)))
       (power 'ell (add n (inv 2)))
       (power (sub 1 'ell) (sub (add m (inv 2) a) n))
       ($diff (mul (power (sub 1 'ell)
			  (sub (sub n a) (inv 2)))
		   ($diff (mul  (power 'ell (inv -2)) fun)
			  'ell
			  (- n m)))
	      'ell
	      m)))

;; F(a+m,-a;1/2+n;z) with m,n integers and m < 0, n >= 0
;;
;; Write this more clearly as F(a-m,-a;1/2+n;z), m > 0, n >= 0
;; or equivalently F(a-m,-a;c+n;z)
;;
;; A&S 15.2.6
;; diff((1-z)^(-1/2)*F(a,-a;1/2;z),z,n) 
;;     = poch((1/2+a,n)*poch(1/2-a,n)/poch(1/2,n)*(1-z)^(-1/2-n)
;;         * F(a,-a;1/2+n;z)
;;
;; A&S 15.2.5
;; diff(z^(n+m-a-1/2)*(1-z)^(-1/2-n)*F(a,-a;1/2+n;z),z,m)
;;     = poch(1/2+n-a,m)*z^(1/2+n-a-1)*(1-z)^(-1/2-n-m)*F(a-m,-a;1/2+n;z)
;;     = poch(1/2+n-a,m)*z^(n-a-1/2)*(1-z)^(-1/2-n-m)*F(a-m,-a;1/2+n;z)
;;
;; (1-z)^(-1/2-n)*F(a,-a;1/2+n;z)
;;     = poch(1/2,n)/poch(1/2-a,n)/poch(1/2+a,n)*diff((1-z)^(-1/2)*F(a,-a;1/2;z),z,n)
;;
;; F(a-m,-a;1/2+n;z)
;;     = (1-z)^(n+m+1/2)*z^(a-n+1/2)/poch(1/2+n-a,m)
;;        *diff(z^(n+m-a-1/2)*(1-z)^(-1/2-n)*F(a,-a;1/2+n;z),z,m)
(defun f83 (fun m n a)
  (mul (factf (inv 2) n)
       (inv (factf (sub (inv 2) a) n))
       (inv (factf (sub (add n (inv 2)) a) m))
       (inv (factf (add (inv 2) a) n))
       (power (sub 1 'ell) (add m n (inv 2)))
       (power 'ell (add (sub a n) (inv 2)))
       ($diff (mul (power 'ell (sub (sub (+ m n) a) (inv 2)))
		   ($diff (mul (power (sub 1 'ell)
				      (inv -2))
			       fun)
			  'ell
			  n))
	      'ell
	      m)))

;; The last case F(a+m,-a;c+n;z), m,n integers, m >= 0, n < 0
;;
;; F(a+m,-a;1/2-n;z)
;;
;; A&S 15.2.4:
;; diff(z^(c-1)*F(a,b;c;z),z,n) = poch(c-n,n)*z^(c-n-1)*F(a,b;c-n;z)
;;
;; A&S 15.2.3:
;; diff(z^(a+m-1)*F(a,b;c;z),z,m) = poch(a,n)*z^(a-1)*F(a+n,b;c;z)
;;
;; For our problem:
;;
;; diff(z^(-1/2)*F(a,-a;1/2;z),z,n) = poch(1/2-n,n)*z^(-n-1/2)*F(a,-a;1/2-n;z)
;;
;; diff(z^(a+m-1)*F(a,-a;1/2-n;z),z,m) = poch(a,m)*z^(a-1)*F(a+m,-a;1/2-n;z)
(defun f84 (fun m n a)
  (mul (inv (mul (factf a m)
		 (factf (sub (inv 2) n) n)))
       (power 'ell (sub 1 a))
       ($diff (mul (power 'ell (sub (add a m n) (inv 2)))
		   ($diff (mul (power 'ell (inv -2)) fun)
			  'ell
			  n))
	      'ell
	      m)))

;; Like f82, but |n|<|m|
;;
;; F(a-m,-a;1/2-n;z), 0 < n < m
;;
;; A&S 15.2.5
;; diff(z^(c-a+n-1)*(1-z)^(a+b-c)*F(a,b;c;z),z,n)
;;     = poch(c-a,n)*z^(c-a-1)*(1-z)^(a+b-c-n)*F(a-n,b;c;z)
;;
;; A&S 15.2.8:
;; diff(z^(c-1)*(1-z)^(b-c+n)*F(a,b;c;z),z,n)
;;     = poch(c-n,n)*z^(c-n-1)*(1-z)^(b-c)*F(a-n,b;c-n;z)
;;
;; For our problem:
;;
;; diff(z^(-a+m-n-1/2)*(1-z)^(-1/2)*F(a,-a;1/2;z),z,m-n)
;;     = poch(1/2-a,m-n)*z^(-a-1/2)*(1-z)^(-1/2-m+n)*F(a-m+n,-a;1/2;z)
;;
;; diff(z^(-1/2)*(1-z)^(-a-1/2+n)*F(a-m+n,-a;1/2;z),z,n)
;;     = poch(1/2-n,n)*z^(-n-1/2)*(1-z)^(-a-1/2)*F(a-m,-a;1/2-n;z)
;;
;; G(z) = z^(-a-1/2)*(1-z)^(-1/2-m+n)*F(a-m+n,-a;1/2;z)
;;      = 1/poch(1/2-a,m-n)*diff(z^(-a+m-n-1/2)*(1-z)^(-1/2)*F(a,-a;1/2;z),z,m-n)
;;
;; F(a-m,-a;1/2-n;z)
;;      = z^(n+1/2)*(1-z)^(a+1/2)/poch(1/2-n,n)
;;         *diff(z^(-1/2)*(1-z)^(-a-1/2+n)*F(a-m+n,-a;1/2;z),z,n)
;;      = z^(n+1/2)*(1-z)^(a+1/2)/poch(1/2-n,n)
;;         *diff(z^a*(1-z)^(m-a)*G(z),z,n)
;; 
(defun f86 (fun m n a)
  (mul (inv (mul (factf (sub (inv 2) n) n)
		 (factf (sub (inv 2) a) (- m n))))
       (power 'ell (add n (inv 2)))
       (power (sub 1 'ell) (add (inv 2) a))
       ($diff (mul (power 'ell a)
		   (power (sub 1 'ell) (sub m a))
		   ($diff (mul (power 'ell
				      (sub (sub (sub m n) (inv 2)) a))
			       (power (sub 1 'ell)
				      (inv -2))
			       fun)
			  'ell (- m n)))
	      'ell n)))

;; F(-1/2+n, 1+m; 1/2+l; z)
(defun hyp-atanh (a b c arg)
  ;; We start with F(-1/2,1;1/2;z) = 1-sqrt(z)*atanh(sqrt(z)).  We can
  ;; derive the remaining forms by differentiating this enough times.
  ;;
  ;; FIXME:  Do we need to assume z > 0?  We do that anyway, here.
  (let* ((s (gensym (symbol-name '#:hyp-atanh-)))
	 (n (add a 1//2))
	 (m (sub b 1))
	 (ell (sub c 1//2))
         (res (sub 1 (mul (power s '((rat simp) 1 2))
                          (take '(%atanh) (power s '((rat simp) 1 2))))))
	 (new-a -1//2)
	 (new-b 1)
	 (new-c 1//2))
    ;; The total number of derivates we compute is n + m + ell.  We
    ;; should do something to reduce the number of derivatives.
    #+nil
    (progn
      (format t "a ,b ,c   = ~a ~a ~a~%" a b c)
      (format t "n, m, ell = ~a ~a ~a~%" n m ell)
      (format t "init a b c = ~a ~a ~a~%" new-a new-b new-c))
    (cond ((alike1 (sub n ell) 0)
	   ;; n = ell so we can use A&S 15.2.7 or A&S 15.2.8
	   (cond ((plusp n)
		  (setf res (as-15.2.7 new-a new-b new-c n s res)))
		 (t
		  (setf res (as-15.2.8 new-a new-b new-c (- n) s res))))
	   (setf new-a (add new-a n))
	   (setf new-c (add new-c n)))
	  (t
	   ;; Adjust ell and then n.  (Does order matter?)
	   (cond ((plusp ell)
		  (setf res (as-15.2.6 new-a new-b new-c ell s res))
		  (setf new-c (add new-c ell)))
		 (t
		  (setf res (as-15.2.4 new-a new-b new-c (- ell) s res))
		  (setf new-c (add new-c ell))))
	   #+nil
	   (progn 
	     (maxima-display res)
	     (format t "new a b c = ~a ~a ~a~%" new-a new-b new-c))
	   (cond ((plusp n)
		  ;; A&S 15.2.3
		  (setf res (as-15.2.3 new-a new-b new-c n s res))
		  (setf new-a (add new-a n)))
		 (t
		  ;; A&S 15.2.5
		  (setf res (as-15.2.5 new-a new-b new-c (- n) s res))
		  (setf new-a (add new-a n))))))
    #+nil
    (progn
      (format t "new a b c = ~a ~a ~a~%" new-a new-b new-c)
      (maxima-display res))
    ;; Finally adjust m by swapping the a and b parameters, since the
    ;; hypergeometric function is symmetric in a and b.
    (cond ((plusp m)
	   (setf res (as-15.2.3 new-b new-a new-c m s res))
	   (setf new-b (add new-b m)))
	  (t
	   (setf res (as-15.2.5 new-b new-a new-c (- m) s res))
	   (setf new-b (add new-b m))))
    #+nil
    (progn
      (format t "new a b c = ~a ~a ~a~%" new-a new-b new-c)
      (maxima-display res))
    ;; Substitute the argument into the expression and simplify the result.
    (sratsimp (maxima-substitute arg s res))))
