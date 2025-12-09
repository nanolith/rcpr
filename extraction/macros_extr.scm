;;;;;; Extraction from Coq to regular (R5RS) scheme: Auxiliary macros

;; Because of fixed arity, we always use unary lambda
;; (lambdas (a b) c) ==> (lambda (a) (lambda (b) c))

(define-syntax lambdas 
  (syntax-rules ()
    ((lambdas () c) c)
    ((lambdas (a b ...) c) (lambda (a) (lambdas (b ...) c)))))

;; Hence all applications should be unary: ((f x) y)
;; to remove some parenthesis, we introduce a macro: (@ f x y) = ((f x) y)

(define-syntax @
  (syntax-rules  ()
    ((@ f) (f))
    ((@ f x) (f x))
    ((@ f x . l) (@ (f x) . l))))

;; (limited) encoding of pattern matching in the bigloo style
;; but without ? in the patterns:
;; Example: predecessor should be written
;;    (define (pred n)
;;       (match n
;;          ((O) '(O))
;;          ((S n) n)))

(define-syntax match
  (syntax-rules () 
    ((match c ((constr . args) u) clauses ...)
     (if (eq? (car c) 'constr) 
	 (apply (lambda args u) (cdr c))
	 (match c clauses ...)))
    ((match c) (error "match-failure"))))

;; NB: in the previous macro and in the extracted code we use 
;; the error function, which is not required by the r5rs standard.
;; Most of the Scheme implementations provide it nonetheless.
;; If yours doesn't, well ... any use of the error function will fail, 
;; which is precisely what should happen ;-)

;;;;;;;;; end of macros;;;;;;;


