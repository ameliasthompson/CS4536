#lang plai-typed
#| 
Language, parsing, desugaring, and interpreting for:
First-class functions
(multiple arguments)
|#

;; General utilities
;; -----------------

;; useful placeholder while developing
;; will match any type, for the purpose of compiling...
(define (undefined) (error 'undefined "") )

;; True if the two lists have *different* lengths
;; different-length? (listof 'a) -> (listof 'a) -> boolean
  (define (different-length? lst1 lst2) : boolean
  (not (= (length lst1) (length lst2))))

;; complaint when string-list has duplicates
;; multiple-names-error : symbol -> (listof string) -> void
(define (multiple-names-error tag string-list)
   ;; OLD, BUG
   ;; (error tag (string-append "name occurs multiple times: " string-list)))
  (error tag (string-append "name occurs multiple times: " (to-string string-list))))

;; complaint when lst lengths don't match
;; (ugh, string-append wants exactly two arguments)
;; length-mismatch-error : symbol -> (listof string) -> (listof string) -> void
(define (length-mismatch-error tag lst1 lst2)
  (error tag
         (string-append "string lengths don't match "
                        (string-append (to-string lst1) (to-string lst2))
                        )))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Language Definition, Parsing, (De-)Sugaring
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types
;; ------
;; the core language     
(define-type ExprC
  [numC (n : number)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [idC (i : symbol)]
  [appC (f : ExprC) (args : (listof ExprC))]
  [if0C (c : ExprC) (t : ExprC) (e : ExprC)]
  [lamC (args : (listof symbol)) (body : ExprC)]
  )

;; Sugared Syntax
(define-type ExprS
  [numS (n : number)]
  [plusS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [idS (i : symbol)]
  [appS (f : ExprS) (args : (listof ExprS))]
  [if0S (c : ExprS) (t : ExprS) (e : ExprS)]
  [lamS (args : (listof symbol)) (body : ExprS)]
  [withS (bindings : (listof Def)) (body : ExprS)]
  )

;; Definitions, as used in a with-form
(define-type Def
  [defS (name : symbol) (val : ExprS)])


;; desugar : ExprS -> ExprC
(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS (n) (numC n)]
    [plusS (l r) (plusC (desugar l)
                        (desugar r))]
    [multS (l r) (undefined)]
    [bminusS (l r)  (undefined)]
    [idS (i)  (idC i)]
    [lamS (args body) (lamC args (desugar body))]
    [appS (f args)  (undefined)] 
    [if0S (c t e) (if0C (desugar c)
                        (desugar t)
                        (desugar e))]
    [withS (bindings body) (undefined)]
    ))

;; Parsing
;; --------
     
;; parse : s-expression -> ExprS
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (cond [(s-exp-symbol? (first sl))
              ;; built-in construct or calling function through an identifier
              (case (s-exp->symbol (first sl))
                [(+) (plusS (parse (second sl)) (parse (third sl)))]
                [(*) (multS (parse (second sl)) (parse (third sl)))]
                [(-) (bminusS (parse (second sl)) (parse (third sl)))]
                [(if0) (if0S (parse (second sl)) (parse (third sl)) (parse (fourth sl)))]
                [(fun) (lamS (map s-exp->symbol (s-exp->list (second sl))) 
                                (parse (third sl)))]
                [(with) (withS (map (lambda (b) 
                                      (let ([bl (s-exp->list b)])
                                        (defS (s-exp->symbol (first bl)) (parse (second bl)))))
                                    (s-exp->list (second sl)))
                               (parse (third sl)))]
                [else ;; must be a function call using function name
                 (appS (idS (s-exp->symbol (first sl)))
                       (map parse (rest sl)))])]
             [(s-exp-list? (first sl)) ;; function call with complex expression in function position
              (appS (parse (first sl))
                    (map parse (rest sl)))]
             [(s-exp-number? (first sl))
              ;; type violation: using number as function (but fits grammar)
              (appS (parse (first sl)) (map parse (rest sl)))]
             [else (error 'parse "expected symbol or list after parenthesis")]))]
    [else (error 'parse "unexpected input format")]))


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreting
;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Types
;; -----

(define-type Value
  [numV (n : number)]
  [closV (params : (listof symbol)) (body : ExprC) (env : Env)])

;; Environments
(define-type Binding
  [bind (name : symbol) (val : Value)])
(define-type-alias Env (listof Binding))


;; Local Utilities
;; ---------------

;; mt-env : Env
(define mt-env empty)

;; extend-env : Binding -> Env -> Env
(define extend-env cons)

;; return first value bound to id in env, or raise error if id is not found
;; lookup : symbol  -> Env -> Value
(define (lookup [id : symbol] [env : Env]) : Value
  (cond [(empty? env) (error 'lookup (string-append "unbound identifier " (to-string id)))]
        [(cons? env) (if (symbol=? id (bind-name (first env)))
                         (bind-val (first env))
                         (lookup id (rest env)))]))

;; error unless names and vals have the same length
;; add-bindings : (listof symbol  -> listof Value -> Env -> Env
(define (add-bindings [names : (listof symbol)] [vals : (listof Value)] [env : Env]) : Env
  (cond [(empty? names) env]
        [(cons? names) (add-bindings (rest names) (rest vals)
                                     (extend-env (bind (first names) (first vals)) env))]))

;; operators on numVs
;; num+ : Value -> Value -> Value
(define (num+ [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (numV (+ (numV-n l) (numV-n r)))]
    [else
     (error 'num+ "type error: one argument was not a number")]))

;; num* : Value -> Value -> Value
(define (num* [l : Value] [r : Value]) : Value
  (cond
    [(and (numV? l) (numV? r))
     (numV (* (numV-n l) (numV-n r)))]
    [else
     (error 'num* "type error: one argument was not a number")]))

;; num0? : Value -> boolean
(define (num0? [v : Value]) : boolean
  (if (numV? v) 
      (zero? (numV-n v))
      (error 'num0? "type error: argument was not a number")))

;; helpers to check for duplicate names
(define (multiples? lst)
  (cond [(empty? lst) false]
        [(cons? lst) (or (member (first lst) (rest lst))
                         (multiples? (rest lst)))]))

;; Interpreter
;; ------------------------------------------------------------------------

;; interp : ExprC -> Env -> Value
(define (interp [a : ExprC] [env : Env]) : Value
  (type-case ExprC a
             [numC (n) (numV n)]
             [plusC (l r) (num+ (interp l env) (interp r env))]
             [multC (l r) (undefined) ]
             [idC (i)     (undefined) ]
             [if0C (c t e) (undefined) ]
             [lamC (params body) (undefined) ]
             [appC (f args) (apply f args env)]
             ))

;; apply : ExprC -> (listof ExprC) -> Env -> Value
(define (apply  [f : ExprC] [args : (listof ExprC) ] [env : Env]) : Value
  (undefined))


;; ------------------------------------------------------------------------
;; Running;  testing
;; --------------------------------

;; evaluates a program starting with a pre-populated environment
;; (this can be helpful in testing)

;; run/env : s-expression ->  Env -> Value
(define (run/env sexp env)
  (interp (desugar (parse sexp)) env))

;; evaluates a program in the empty environment

;; run : s-expression -> Value
(define (run sexp)
  (run/env sexp mt-env))


;; Some tests
(test (run '(+ (* 5 (+ 7 3)) 4)) (numV 54))
(test (run '(if0 (+ 2 2) 6 8)) (numV 8))
(test (run '(with ((f (fun (x) (* x 2)))) (f 5))) (numV 10))
(test/exn (run '(with ((x 5)) y)) "unbound")
(test/exn (run '((fun (x y x) 3) 4 4 4)) "multiple")
(test/exn (run '(3 4)) "type") 
(test/exn (run '(if0 (fun (x) 5) 3 4)) "type")
