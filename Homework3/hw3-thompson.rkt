#lang plai-typed
#| 
Starter file for:
Language, parsing, desugaring and interpretation for the language including
Mutation (multiple arguments)
|#

; Maximilian Thompson

;; useful placeholder while developing
(define (undefined) (error 'undefined "") )

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Types (and fundamental operators)
;;
;; Expressions
;;
; type used to capture a with-binding
(define-type DefS
  [defS (name : symbol) (val : ExprS)])

(define-type ExprC
  [numC (n : number)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)]
  [idC (i : symbol)]
  [appC (f : ExprC) (args : (listof ExprC))]
  [if0C (c : ExprC) (t : ExprC) (e : ExprC)]
  [lamC (args : (listof symbol)) (body : ExprC)]
  [boxC (arg : ExprC)]
  [unboxC (arg : ExprC)]
  [setboxC (b : ExprC) (v : ExprC)]
  [seqC (b1 : ExprC) (b2 : ExprC)]
  [setC (var : symbol) (arg : ExprC)]
  )

(define-type ExprS
  [numS (n : number)]
  [plusS (l : ExprS) (r : ExprS)]
  [bminusS (l : ExprS) (r : ExprS)]
  [multS (l : ExprS) (r : ExprS)]
  [idS (i : symbol)]
  [appS (f : ExprS) (args : (listof ExprS))]
  [if0S (c : ExprS) (t : ExprS) (e : ExprS)]
  [lamS (args : (listof symbol)) (body : ExprS)]
  [withS (bindings : (listof DefS)) (body : ExprS)]
  [boxS (arg : ExprS)]
  [unboxS (arg : ExprS)]
  [setboxS (b : ExprS) (v : ExprS)]
  [seqS (exprs : (listof ExprS))]
  [setS (var : symbol) (arg : ExprS)]
  )

;;
;; Values
;;
(define-type Value
  [numV (n : number)]
  [boxV (l : Location)]
  [closV (params : (listof symbol)) (body : ExprC) (env : Env)])

;; error-checking function for extracting the location of a box
(define (boxloc [v : Value]) : Location
  (if (boxV? v)
      (boxV-l v)
      (error 'boxloc "type error: argument was not a box")))

;;
;; Environments
;;
(define-type-alias Env (listof Binding))
(define-type Binding
  [bind (name : symbol) (loc : Location)])

;; mt-env : Env
(define mt-env empty)

;; extend-env : Binding x Env -> Env
(define extend-env cons)


;;
;; Stores
;;
(define-type-alias Store (listof Storage))
(define-type Storage
  [cell (location : Location) (val : Value)])
(define-type-alias Location number)

;; mt-store : Store
(define mt-store empty)

;; override-store : Storage x Store -> Store

;; Implemented in the text as cons, trusting that fetch will fetch the
;; "most recent" Storage with the given Location.  Fragile....
;;(define override-store cons)

;; A more robust implementation, not making assumptions about how
;; fetch will be implemented.
(define (override-store [c : Storage] [sto : Store]) : Store
  (if (member (cell-location c) (map cell-location sto))
      [map (lambda (i) (if (equal? (cell-location c) (cell-location i)) c i)) sto]
      [cons c sto]
      ))
           
;;
;; Results
;;
;; Interpreting an Expr returns this
(define-type Result
  [v*s (v : Value) (s : Store)])
;; Interpreting a list of Expr returns this
;; useful when evaluating a list of arguments to a function, for example
(define-type Results
  [vs*s (vs : (listof Value)) (s : Store)])


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parsing and desugaring

;; parse : s-expression -> ExprS
(define (parse [s : s-expression]) : ExprS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-symbol? s) (idS (s-exp->symbol s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (cond
         ;; built-in construct or calling function through an identifier
         [(s-exp-symbol? (first sl)) 
          (case (s-exp->symbol (first sl))
            ; [(+) (plusS (parse (second sl)) (parse (third sl)))]
            [(+) (parse-arith s)]
            [(*) (parse-arith s)]
            [(-) (parse-arith s)]
            [(if0) (if0S (parse (second sl))
                         (parse (third sl)) (parse (fourth sl)))]
            [(fun) (lamS (map s-exp->symbol (s-exp->list (second sl)))
                         (parse (third sl)))]
            [(with) (withS (map (lambda (b) 
                                  (let ([bl (s-exp->list b)])
                                    (defS (s-exp->symbol (first bl))
                                      (parse (second bl)))))
                                (s-exp->list (second sl)))
                           (parse (third sl)))]
            [(box) (boxS (parse (second sl)))]
            [(unbox) (unboxS (parse (second sl)))]
            [(setbox) (setboxS (parse (second sl))
                               (parse (third sl)))]
            [(seq) (seqS (map parse (rest sl)))]
            [(set) (setS (s-exp->symbol (second sl))
                         (parse (third sl)))]
            [else ;; must be a function application
             (appS (idS (s-exp->symbol (first sl)))
                   (map parse (rest sl)))])]
         [else ;; must be a function application
          (appS (parse (first sl))
                (map parse (rest sl)))]))]
    [else (error 'parse "unexpected syntax")]))

;; parse-arith : s-expression -> ExprS
;; ASSSUMES s satisfies s-exp-list? (call this from parse...)
;; CHECKS for having exactly two arguments
(define (parse-arith [s : s-expression]) : ExprS
   (let ([sl (s-exp->list s)])
     (cond
       [(not (= 3 (length sl)))
        (error 'parse-arith "wrong number of arguments")]
         ;; built-in construct or calling function through an identifier
         [(s-exp-symbol? (first sl)) 
          (case (s-exp->symbol (first sl))
            [(+) (plusS (parse (second sl)) (parse (third sl)))]
            [(*) (multS (parse (second sl)) (parse (third sl)))]
            [(-) (bminusS (parse (second sl)) (parse (third sl)))]
            [else (error 'parse-arith "not an arithmetic expression")]
            )])))

  
;; desugar : ExprS -> ExprC
(define (desugar [as : ExprS]) : ExprC
  (type-case ExprS as
    [numS (n) (numC n)]
    [plusS (l r) (plusC (desugar l)
                        (desugar r))]
    [multS (l r) (multC (desugar l)
                        (desugar r))]
    [bminusS (l r) (plusC (desugar l)
                          (multC (numC -1) (desugar r)))]
    [idS (i) (idC i)]
    [lamS (params body)
          (if (duplicates? params)
              (error 'desugar (string-append "binding name multiple times: "
                                             (to-string params)))
              (lamC params (desugar body)))]
    [appS (f args) (appC (desugar f) (map desugar args))]
    [if0S (c t e) (if0C (desugar c) (desugar t) (desugar e))]
    [withS (bindings body)
           (desugar (appS (lamS (map defS-name bindings) body)
                          (map defS-val bindings)))]
    [boxS (arg) (boxC (desugar arg))]
    [unboxS (arg) (unboxC (desugar arg))]
    [setboxS (arg val) (setboxC (desugar arg) (desugar val))]
    [seqS (exprs)
          (cond [(empty? exprs) (error 'desugar "empty seq not allowed")]
                [(= (length exprs) 1) (desugar (first exprs))]
                [else (seqC (desugar (first exprs)) (desugar (seqS (rest exprs))))])]  
    [setS (var arg) (setC var (desugar arg))]
    ))



;; General utilities
;; -----------------

;; True if the two lists have *different* lengths
(define (different-length? lst1 lst2) : boolean
  (not (= (length lst1) (length lst2))))

; helper to check for duplicate names
;; duplicates : (listof 'a) -> boolean
(define (duplicates? lst)
  (cond [(empty? lst) false]
        [(cons? lst) (or (member (first lst) (rest lst))
                         (duplicates? (rest lst)))]))

;; complaint when string-list has duplicates
(define (multiple-names-error tag string-list)
  (error tag (string-append "name occurs multiple times: " string-list)))

;; Local Utilities
;; ---------------

;; return first value bound to id in env, or raise error if id is not found
;; lookup : symbol x Env -> Location
  (define (lookup [id : symbol] [env : Env]) : Location
  (cond [(empty? env) (error 'lookup (string-append "unbound identifier " (to-string id)))]
        [(cons? env) (if (symbol=? id (bind-name (first env)))
                         (bind-loc (first env))
                         (lookup id (rest env)))]))

;; operators on numVs
;; ------------------

(define (num+ [l : Value] [r : Value]) : Value
  (if (numV? l)
      (if (numV? r)
          (numV (+ (numV-n l) (numV-n r)))
          (error 'num+ "type error: second argument was not a number"))
      (error 'num+ "type error: first argument was not a number")))

(define (num* [l : Value] [r : Value]) : Value
  (if (numV? l)
      (if (numV? r)
          (numV (* (numV-n l) (numV-n r)))
          (error 'num* "type error: second argument was not a number"))
      (error 'num* "type error: first argument was not a number")))

(define (num0? [v : Value]) : boolean
  (if (numV? v) 
      (zero? (numV-n v))
      (error 'num0? "type error: argument was not a number")))




;; Generating new numbers
;; and lists of numbers, and
;; new locations
;; -------------------

;; The let-lambda idiom together with mutation *in Racket*
;; lets us generate numbers as needed.

;; new-number-demo : -> number
;; each time this is called (with no arguments)
;; it returns the "next" number
(define new-number-demo
   (let ([n 0])
    (lambda ()
      (begin
        (set! n (+ 1 n))
        n ))))

;; Here we generate a list of k new numbers
(define new-number-list
  (let ([n 0])
    (lambda (k)
      (if (zero? k)
          empty
          (begin
            (set! n (+ 1 n))
            (cons n (new-number-list (- k 1)))
            )))))

;; In case we just need one new number
;; CRUCIALLY important that this uses the same state as new-number-list;
;; that's why we don't just use a separate function (like new-number-demo above)
(define (new-number) (first (new-number-list 1)))

;; new-loc :-> Location
(define new-loc new-number)
;; new-loc-list : -> (listof Location)
(define new-loc-list new-number-list)


;; fetch : Location x  Store -> Value
(define (fetch [loc : Location] [sto : Store]) : Value
  (cond [(empty? sto) (error 'fetch "Memory address out of bounds")]
        [(cons? sto) (if (= loc (cell-location (first sto)))
                         (cell-val (first sto))
                         (fetch loc (rest sto)))]))


;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The Interpreter

;; interp : ExprC  x Env x  Store -> Result
(define (interp [a : ExprC] [env : Env] [sto : Store]) : Result
    (type-case ExprC a
      [numC (n)            (v*s (numV n) sto)]
      [plusC (l r)         (v*s (num+ (v*s-v (interp l env sto)) (v*s-v (interp r env sto))) sto)]
      [multC (l r)         (v*s (num* (v*s-v (interp l env sto)) (v*s-v (interp r env sto))) sto)]
      [idC (i)             (v*s (fetch (lookup i env) sto) sto)]
      [lamC (params body)  (v*s (closV params body env) sto)]
      [appC (f a)          (apply f a env sto)]
      [if0C (c t e)        (v*s (if (num0? (v*s-v (interp c env sto))) (v*s-v (interp t env sto)) (v*s-v (interp e env sto))) sto)]
      [boxC (a)            (let ([n (new-loc)]) (v*s (numV n) (override-store (cell n (v*s-v (interp a env sto))) sto)))]
      [unboxC (a)          (v*s (fetch (numV-n (v*s-v (interp a env sto))) sto) sto)]
      [setboxC (b v)       (v*s (v*s-v (interp v env sto)) (override-store (cell (numV-n (v*s-v (interp b env sto))) (v*s-v (interp v env sto))) sto))]
      [seqC (b1 b2)        (interp b2 env (v*s-s (interp b1 env sto)))]
      [setC (var val)      (v*s (v*s-v (interp val env sto)) (override-store (cell (lookup var env) (v*s-v (interp val env sto))) sto))]
      ))


;; apply : ExprC x (listof ExprC) x Env x Sto -> Value
;; ASSUMES f evaluates to a closure, and that the closure passes the
;; checks in compute-closure
(define (apply  [f : ExprC] [args : (listof ExprC) ] [env : Env] [sto : Store] ) : Result
  (let* (
         (num-args        (length args))
         ;; eval the function
         (f-result        (compute-closure f env sto (length args)))
         (f-value         (v*s-v f-result))
         (f-store         (v*s-s f-result))
         ;; extract the closure fields
         (f-params        (closV-params f-value))
         (f-bdy           (closV-body f-value))
         (f-env           (closV-env f-value))
         
         ;; eval the arguments. 
         (args-results    (interp-list args env f-store))
         (args-values     (vs*s-vs args-results))
         (args-store      (vs*s-s args-results))
         ;; make a new environment and a new store
         (new-locs        (new-number-list (length f-params)))
         (new-env         (make-new-env f-env new-locs f-params))
         (new-store       (make-new-sto args-store new-locs args-values))
         )
   ;; go for it
    (interp f-bdy new-env new-store)
    ))

(define (make-new-env [env : Env] [locs : (listof Location)] [params : (listof symbol)]) : Env
  (if (empty? locs)
      env
      [make-new-env (extend-env (bind (first params) (first locs)) env) (rest locs) (rest params)]))

(define (make-new-sto [sto : Store] [locs : (listof Location)] [val : (listof Value)]) : Store
  (if (empty? locs)
      sto
      [make-new-sto (override-store (cell (first locs) (first val)) sto) (rest locs) (rest val)]))

;;
;; Interpreter Utilities
;; ----------------------
;; interp-list : (listof ExprC)  x Env x  Store -> (listof Value)
;; this evaluates left-to-right
;; all exprs evaluated in the same Environment
;; (but of course the Store is threaded)
(define (interp-list [exprs : (listof ExprC)] [env : Env] [sto : Store]) : Results
  (if (empty? exprs)
      [vs*s empty sto]
      [local
        (
         ;; Results of current expression
         [define res     (interp (first exprs) env sto)]
         [define res-val (v*s-v res)]
         [define res-sto (v*s-s res)]

         ;; Recursive results of the rest of the expressions
         [define all-res (interp-list (rest exprs) env res-sto)]
         [define all-val (vs*s-vs all-res)]
         [define all-sto (vs*s-s all-res)])

        ;; Taking the current result, prepending it to the rest of the results, and adding the final store
        (vs*s (cons res-val all-val) all-sto)]
  ))

;; compute-closure :  ExprC x Env x Store x number ->  Result
;; Evaluate the first argument w.r.t. the given environment and store
;; check that the result is a closure,
;; and that the number of parameters equals the final argument, 
;; and that there are no repeated parameters in that closure.

(define (compute-closure  [f : ExprC] [env : Env] [sto : Store] [n : number]) : Result
  ;; evaluate the function 
  (type-case Result (interp f env sto)
             [v*s (func-value s-f)
                  (cond
                     ;; if func-value not a closure we have a bug
                    [(not (closV? func-value))
                     (error 'compute-closure "given a non-closure")]
                    
                    [else ;; extract the parts of the closure
                     (let ((params (closV-params func-value))
                           (f-bdy  (closV-body func-value))
                           (f-env  (closV-env func-value)))
                       ;; check that the closure is appropriate for this application
                       (cond [(not (= (length params) n))
                              (error 'compute-closure "parameter and argument lengths don't match")]
                              ;; (length-mismatch-error 'compute-closure params n)]
                             [(duplicates? params)
                              (error 'compute-closure "duplicate parameters")]
                             
                             ;; ok, all is good
                             [else (v*s func-value s-f)]
                             ))])]))


                     
;; Putting it all together

;; a run-command just returning values
(define (run-v sexp)
     (v*s-v (interp (desugar (parse sexp)) mt-env mt-store)))

;; a run-command returning values and stores
(define (run sexp)
     (interp (desugar (parse sexp)) mt-env mt-store))

;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests
;;

;; override-store tests
(test (override-store (cell 4 (numV 45))
                      (list (cell 1 (numV 0)) (cell 9 (numV 0)) (cell 24 (numV 0))))
      (list (cell 4 (numV 45)) (cell 1 (numV 0)) (cell 9 (numV 0)) (cell 24 (numV 0))))
(test (override-store (cell 9 (numV 26))
                      (list (cell 4 (numV 45)) (cell 1 (numV 0)) (cell 9 (numV 0)) (cell 24 (numV 0))))
      (list (cell 4 (numV 45)) (cell 1 (numV 0)) (cell 9 (numV 26)) (cell 24 (numV 0))))

;; desugar (seqS)
(test (desugar (seqS (list (numS 1) (numS 2) (numS 3))))
      (seqC (numC 1) (seqC (numC 2) (numC 3))))
(test (desugar (seqS (list (numS 42))))
      (numC 42))
(test/exn (desugar (seqS (list))) "empty")

;; interp (boxC)
; This test is kind of bad and assumes the functionality of new-number
(test (interp (boxC (numC 1)) empty (list (cell 40 (numV 0)) (cell 50 (numV 0))))
      (v*s (numV 1) (list (cell 1 (numV 1)) (cell 40 (numV 0)) (cell 50 (numV 0)))))

;; interp (unboxC)
(test (interp (unboxC (numC 4)) empty (list (cell 4 (numV 1)) (cell 81 (numV 81))))
      (v*s (numV 1) (list (cell 4 (numV 1)) (cell 81 (numV 81)))))
(test/exn (interp (unboxC (numC 0)) empty (list (cell 4 (numV 1)) (cell 81 (numV 81))))
      "Memory")

;; interp (setboxC)
(test (interp (setboxC (numC 4) (numC 100)) empty (list (cell 3 (numV 15)) (cell 4 (numV 0))))
      (v*s (numV 100) (list (cell 3 (numV 15)) (cell 4 (numV 100)))))
(test (interp (setboxC (numC 10) (numC 50)) empty (list (cell 3 (numV 15)) (cell 4 (numV 0))))
      (v*s (numV 50) (list (cell 10 (numV 50)) (cell 3 (numV 15)) (cell 4 (numV 0)))))

;; interp (seqC)
(test (interp (seqC (numC 1) (seqC (numC 2) (numC 3))) empty (list (cell 1 (numV 42))))
      (v*s (numV 3) (list (cell 1 (numV 42)))))
      
;; interp (setC)
(test (interp (setC 'x (numC 4)) (list (bind 'x 4)) (list (cell 4 (numV 0))))
      (v*s (numV 4) (list (cell 4 (numV 4)))))
(test (interp (seqC (setC 'x (numC 4)) (setC 'x (numC 8))) (list (bind 'x 4)) (list (cell 4 (numV 0))))
      (v*s (numV 8) (list (cell 4 (numV 8)))))
(test (interp (seqC (setC 'x (numC 4)) (plusC (idC 'x) (numC 10))) (list (bind 'x 4)) (list (cell 4 (numV 0))))
      (v*s (numV 14) (list (cell 4 (numV 4)))))

;; interp-list
(test (interp-list (list (plusC (numC 2) (numC 2)) (setC 'x (numC 8)) (idC 'x)) (list (bind 'x 0)) (list (cell 0 (numV 0))))
                   (vs*s (list (numV 4) (numV 8) (numV 8)) (list (cell 0 (numV 8)))))
(test (interp-list empty (list (bind 'x 0)) (list (cell 0 (numV 0))))
      (vs*s empty (list (cell 0 (numV 0)))))

;; apply
; These are also fragile and assume the state of new-number
(test (apply (lamC (list 'b 'c) (plusC (plusC (idC 'a) (idC 'b)) (idC 'c))) (list (numC 2) (numC 2)) (list (bind 'a 400)) (list (cell 400 (numV 2))))
      (v*s (numV 6) (list (cell 3 (numV 2)) (cell 2 (numV 2)) (cell 400 (numV 2)))))
(test (apply (lamC (list 'b 'c) (plusC (plusC (setC 'a (plusC (idC 'b) (idC 'c))) (idC 'b)) (idC 'c))) (list (numC 2) (numC 2)) (list (bind 'a 400)) (list (cell 400 (numV 2))))
      (v*s (numV 8) (list (cell 5 (numV 2)) (cell 4 (numV 2)) (cell 400 (numV 2)))))
(test (interp (seqC (setboxC (numC 0) (lamC (list 'x 'y) (plusC (idC 'x) (idC 'y)))) (appC (idC 'f) (list (numC 2) (numC 2)))) (list (bind 'f 0)) (list (cell 0 (numV 0))))
      (v*s (numV 4) (list (cell 7 (numV 2)) (cell 6 (numV 2)) (cell 0 (closV (list 'x 'y) (plusC (idC 'x) (idC 'y)) (list (bind 'f 0)))))))

;; run
(test (run '(seq (setbox 0 (+ 2 2)) (setbox 0 (+ (unbox 0) 2)) (unbox 0)))
      (v*s (numV 6) (list (cell 0 (numV 6)))))
(test (run '(seq (+ 2 2)))
      (v*s (numV 4) empty))
; This one is fragile too
(test (run '(with ((a 2) (b 2) (f (fun (x y) (+ x y)))) (f a b)))
      (v*s (numV 4) (list (cell 12 (numV 2)) (cell 11 (numV 2)) (cell 10 (closV (list 'x 'y) (plusC (idC 'x) (idC 'y)) empty)) (cell 9 (numV 2)) (cell 8 (numV 2)))))
(test (run '(with ((a 2) (b 2) (f (fun (x y) (+ x y)))) (f a a)))
      (v*s (numV 4) (list (cell 17 (numV 2)) (cell 16 (numV 2)) (cell 15 (closV (list 'x 'y) (plusC (idC 'x) (idC 'y)) empty)) (cell 14 (numV 2)) (cell 13 (numV 2)))))
(test (run '(with ((x (box 12))) (unbox x)))
      (v*s (numV 12) (list (cell 19 (numV 18)) (cell 18 (numV 12)))))
(test (run '(with ((x (box 12))) (seq (setbox x 40) (unbox x))))
     (v*s (numV 40) (list (cell 21 (numV 20)) (cell 20 (numV 40)))))
(test/exn (run '(seq)) "empty seq")
(test/exn (run '(with () x)) "unbound")
(test/exn (run '(with ((a 2) (b 2) (f (fun (x y) (+ x y)))) (f a))) "lengths")
(test/exn (run '(with ((a 2) (b 2) (f (fun (x y) (+ x y)))) (f a b a))) "lengths")


;; Tests from HW2
(test (run '(+ (* 5 (+ 7 3)) 4)) (v*s (numV 54) empty))
(test (run '(+ (* 5 (- 7 3)) 4)) (v*s (numV 24) empty))
(test (run '(if0 (+ 2 2) 6 8)) (v*s (numV 8) empty))
(test (run '(if0 (- 2 2) 6 8)) (v*s (numV 6) empty))
(test (run '(with ((f (fun (x) (* x 2)))) (f 5)))
      (v*s (numV 10) (list (cell 29 (numV 5)) (cell 28 (closV (list 'x) (multC (idC 'x) (numC 2)) empty)))))
