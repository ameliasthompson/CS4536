#lang plai-typed
#|
Type checking for a simply-typed calculus: starter file
Dan Dougherty Febraury 2018
|#

(require (typed-in racket/sandbox
            [call-with-limits : (number boolean (-> 'a) -> 'a)]))

;; useful placeholder while developing
(define (undefined) (error 'undefined "") )

;; ------
;; Types
;; ------
(define-type Type
  [numT]
  [boolT]
  [nlistT]
  [funT (input : Type) (return : Type)])

;; Type Environments
(define-type-alias typeEnv (listof tBinding))
(define-type tBinding [tbind (name : symbol) (type : Type)])
(define mt-tenv empty)
(define extend-tenv cons)

;;
;; Parsing Types
;;
;; parse-type : s-expression ->  Type
(define (parse-type [t : s-expression]) : Type
  (cond [(s-exp-symbol? t)
         (case (s-exp->symbol t)
           [(number) (numT)]
           [(boolean) (boolT)]
           [(nlist) (nlistT)]
           [else (error 'parse-type
                        (string-append "parse error: unrecognized type name "
                                       (to-string t)))])]
        [(s-exp-list? t) ; must be a function type
         (let ([tl (s-exp->list t)])
           (if (= (length tl) 3)
               (let ([tin (parse-type (first tl))]
                     [tarrow (s-exp->symbol (second tl))]
                     [tout (parse-type (third tl))])
                 (if (eq? tarrow '->)
                     (funT tin tout)
                     (error 'parse-type
                            (string-append "parse error: Malformed type syntax "
                                           (to-string tl)))))
               (error 'parse-type  (string-append "parse error: Malformed type syntax "
                                                  (to-string tl)))))]
        [else (error 'parse-type  (string-append "parse error: Malformed type syntax "
                                                 (to-string t)))]))


;; ------
;; Expressions
;; ------

(define-type ExprS
  [numS (n : number)]
  [boolS (b : boolean)]
  [nemptyS]
  [plusS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [idS (i : symbol)]
  [appS (f : ExprS) (arg : ExprS)]
  [iszeroS (e : ExprS)]
  [bifS (c : ExprS) (t : ExprS) (e : ExprS)]
  [lamS (param : symbol) (paramtype : Type) (rettype : Type) (body : ExprS)]
  [recS (var : symbol) (val : ExprS) (body : ExprS)]
  [withS (var : symbol) (val : ExprS) (body : ExprS)]
  [nconsS (e : ExprS) (l : ExprS)]
  [nisEmptyS (e : ExprS)]
  [nfirstS (e : ExprS)]
  [nrestS (e : ExprS)]
  )

;; 
;; Parsing Exprsssions
;; 
;;  parse : s-expression -> ExprS
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) 
     (case (s-exp->symbol s)
       [(tru) (boolS true)]
       [(fls) (boolS false)]
       [(nempty) (nemptyS)]
       [else (idS (s-exp->symbol s))])]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (cond [(s-exp-symbol? (first sl)) ;; built-in construct or calling function through an identifier
              (case (s-exp->symbol (first sl))
                [(+) (plusS (parse (second sl)) (parse (third sl)))]
                [(*) (multS (parse (second sl)) (parse (third sl)))]
                [(-) (bminusS (parse (second sl)) (parse (third sl)))]
                [(iszero) (iszeroS (parse (second sl)))]
                [(bif) (bifS (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
                [(fun) (if (= (length sl) 5)
                           (let ([pspec (s-exp->list (second sl))])
                             (begin (unless (= (length pspec) 3)
                                      (error 'parse
                                             (string-append "parse error: bad parameter (expected 3 parts)"
                                                            (to-string pspec))))
                                    (unless (eq? ': (s-exp->symbol (third sl)))
                                      (error 'parse
                                             (string-append "parse error: missing : for output type "
                                                            (to-string sl))))
                                    (unless (eq? ': (s-exp->symbol (second pspec)))
                                      (error 'parse
                                             (string-append "parse error: expected : in "
                                                            (to-string pspec))))
                                    (let ([pname (s-exp->symbol (first pspec))]
                                          [ptype (parse-type (third pspec))])
                                      (lamS pname ptype
                                            (parse-type (fourth sl))
                                            (parse (fourth (rest sl)))))))
                           (error 'parse
                                  (string-append "parse error: bad lambda expression (expected 5 parts)"
                                                 (to-string s))))]
                [(with) (let ([bindings (s-exp->list (second sl))]
                              [body (third sl)])
                          (cond [(= 1 (length bindings))
                                 (let ([binding (s-exp->list (first bindings))])
                                   (withS (s-exp->symbol (first binding))
                                          (parse (second binding))
                                          (parse body)))]
                                [else (error 'parse "parse error: bad format in with bindings")]))]
                [(rec)  (let ([bindings (s-exp->list (second sl))]
                              [body (third sl)])
                          (cond [(= 1 (length bindings))
                                 (let ([binding (s-exp->list (first bindings))])
                                   (recS (s-exp->symbol (first binding))
                                          (parse (second binding))
                                          (parse body)))]
                                [else (error 'parse "parse error: bad format in with bindings")]))]
                [(ncons) (nconsS (parse (second sl)) (parse (third sl)))]
                [(nempty?) (nisEmptyS (parse (second sl)))]
                [(nfirst) (nfirstS (parse (second sl)))]
                [(nrest) (nrestS (parse (second sl)))]
                [else ;; must be a function application
                 (appS (idS (s-exp->symbol (first sl)))
                       (parse (second sl)))])]
             [else (appS (parse (first sl))
                         (parse (second sl)))]))]
    [else (error 'parse "parse error: unexpected syntax")]))

(define (with-err bindings)
  (string-append "parse error: with expects list containing one binding but got "
                 (to-string bindings)))
  
(define (type-error) (error 'type-of "type error"))

;; -------------
;; Type Checking 
;; -------------

;; typecheck takes an ExprS, since for this assignment we don't desugar
;;  type-of : ExprS x (listof tBinding) -> Type
(define (type-of [e : ExprS] [tenv : typeEnv]) : Type
  (type-case ExprS e
             [idS (i)
                  (lookup-type i tenv)]
             [appS (f arg)
                   (type-case Type (type-of f tenv)
                     [funT (i r) (if (same-type? i (type-of arg tenv))
                                     r
                                     [error 'type-of "type error: function input type does not match argument type"])]
                     [else (error 'type-of "type eror: appS f is not a function")])]
             [lamS (param paramtype rettype body)
                   (if (same-type? rettype (type-of body (extend-tenv (tbind param paramtype) tenv)))
                       [type-case Type (type-of body (extend-tenv (tbind param paramtype) tenv))
                         [funT (i r)
                               (if (and (same-type? (funT-input rettype) i)
                                        (same-type? (funT-return rettype) r))
                                   [funT paramtype rettype]
                                   [error 'type-of "type error: wrong type returned by inner function"])]
                         [else (funT paramtype rettype)]]
                       [error 'type-of "type error: function return type does not match body type"])]
             [withS (var val body)
                    (type-of body (extend-tenv (tbind var (type-of val tenv)) tenv))]
             [recS (fn val body)
                   (local
                     ([define fun-type (type-of val (extend-tenv (tbind fn (funT (lamS-paramtype val) (lamS-rettype val))) tenv))]
                      [define fun-bind (tbind fn fun-type)])
                     (type-of body (extend-tenv fun-bind tenv)))]
             [numS (n)
                   (numT) ]
             [boolS (b)
                    (boolT) ]
             [plusS (l r)
                    (if (and (numT? (type-of l tenv)) (numT? (type-of r tenv)))
                        [numT]
                        [error 'type-of "type error: sum not of type (numT numT)"])]
             [bminusS (l r)
                      (if (and (numT? (type-of l tenv)) (numT? (type-of r tenv)))
                        [numT]
                        [error 'type-of "type error: difference not of type (numT numT)"])]             
             [multS (l r)
                    (if (and (numT? (type-of l tenv)) (numT? (type-of r tenv)))
                        [numT]
                        [error 'type-of "type error: product not of type (numT numT)"])]
             [iszeroS (e)
                      (if (numT? (type-of e tenv))
                          [boolT]
                          [error 'type-of "type error: iszero not of type (numT)"])]
             [bifS (c t e)
                   (if (boolT? (type-of c tenv))
                       [if (same-type? (type-of t tenv) (type-of e tenv))
                           [type-of t tenv]
                           [error 'type-of "type error: bif results not of same type"]]
                       [error 'type-of "type error: bif conditional not of type (boolT)"])]
             [nemptyS ()
                      (nlistT)] 
             [nisEmptyS (e)
                        (if (nlistT? (type-of e tenv))
                            [boolT]
                            [error 'type-of "type error: nisEmptyS not of type (nlistT)"])]
             [nconsS (e l)
                     (if (and (numT? (type-of e tenv)) (nlistT? (type-of l tenv)))
                         [nlistT]
                         [error 'type-of "type error: nconsS not of type (numT nlistT)"])]
             [nfirstS (e)
                      (if (nlistT? (type-of e tenv))
                          [numT]
                          [error 'type-of "type error: nfirstS not of type (nlistT)"])]
             [nrestS (e)
                     (if (nlistT? (type-of e tenv))
                         [nlistT]
                         [error 'type-of "type error: nrestS not of type (nlistT)"])]
             ))

;;----------
;; Utilities
;; ---------


;; lookup a type name in the type environment
;; lookup-type : symbol x  (listof tBinding) -> Type
(define (lookup-type [name : symbol] [env : typeEnv])
  (cond [(empty? env) (error 'lookup-type (string-append "unbound identifier " (to-string name)))]
        [(cons? env) (if (eq? name (tbind-name (first env)))
                         (tbind-type (first env))
                         (lookup-type name (rest env)))]))

(define (same-type? [a : Type] [b : Type]) : boolean
  (or (and (numT? a) (numT? b))
      (and (boolT? a) (boolT? b))
      (and (nlistT? a) (nlistT? b))
      (and (funT? a) (funT? b))))

;; ----
;; API 
;; ----

;; have "type error" be a substring in all type errors raised by your code

;;  typecheck : s-expression -> Type
(define (typecheck sexp)
  (call-with-limits 
   10 #f
   (lambda () (type-of (parse sexp) mt-tenv))))


;; Some tests
;; atomic data and basic arithmetic tests 
(test (typecheck (number->s-exp 5)) (numT))
(test/exn (typecheck '(- fls (* 4 5))) "type error")
;; iszero test
(test (typecheck '(iszero 0)) (boolT))
;; if tests
(test (typecheck '(bif fls tru (bif tru fls tru))) (boolT))
(test/exn (typecheck '(bif 5 tru fls)) "type error")
;; lists tests
(test (typecheck (symbol->s-exp 'nempty)) (nlistT))
(test/exn (typecheck '(nrest (bif tru 3 2))) "type error")
;; with tests
(test (typecheck '(with ((n 4)) n)) (numT))
(test (typecheck '(with ((n 4))
                        (with ((n (iszero 5)))
                              (bif n 3 4)))) (numT))
;; incorrect return type when returning a function: dropped return type from inner function
(test/exn (typecheck '(fun (x : number) : (number -> boolean)
                        (fun (f : (number -> boolean)) : boolean
                          (f x))))
          "type error")
;; lists across if branches, returning a function
(test (typecheck '(with ((f (fun (n : number) : nlist
                              (bif (iszero n) nempty (ncons n nempty)))))
                        f))
      (funT (numT) (nlistT)))
;;;; nested scopes for same identifier name
(test (typecheck '(with ((f (fun (x : number) : nlist (ncons x nempty))))
                        (with ((x (iszero (+ 2 -2))))
                              (bif x (f 5) nempty)))) 
      (nlistT))
;; same identifier with different types in different scopes: types propagate from inner to outer scopes
(test (typecheck '(with ((x 3))
                        (with ((f (fun (y : number) : number (+ x y))))
                              (with ((x tru))
                                    (bif x x x)))))
          (boolT))
;; referencing closured var two levels down
(test (typecheck '(with ((n 0))
                        (with ((f (fun (x : nlist) : (number -> nlist)
                                    (fun (y : number) : nlist
                                      (ncons (+ y n) x)))))
                              (with ((n nempty))
                                    (f (ncons 12 n))))))
      (funT (numT) (nlistT)))
;;; type-checking recursive functions
(test (typecheck '(rec ((f (fun (n : number) : nlist
                                (bif (iszero n) nempty (ncons n (f (- n 1)))))))
                       (f 4)))
      (nlistT))
;;; doesn't HAVE to be recursive
(test (typecheck '(rec ((f (fun (x : number) : number  (+ x 1))))
                       ( f 2 )))
      (numT))    