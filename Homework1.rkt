#lang plai-typed

; Problem #1 (0.5 pts)
;
; Write a function sum which takes a list of numbers and produces
; the sum of the numbers in the list.

(define (sum [nums : (listof number)]) : number
  (cond [(empty? nums) 0]
        [else (+ (first nums) (sum (rest nums)))]))

(test (sum (list 1 2 3 4 5 6)) 21)
(test (sum empty) 0)
(test (sum (list -1 1 0)) 0)

; Problem #2 (0.5 pts)
;
; Write a function sum-inrange which takes a list of numbers and
; produces the sum of the numbers in the list whose value is between
; -2 and -5 (included).

(define (sum-inrange [nums : (listof number)]) : number
  (cond [(empty? nums) 0]
        [(and (>= (first nums) -5) (<= (first nums) -2))
         (+ (first nums) (sum-inrange (rest nums)))]
        [else (sum-inrange (rest nums))]))

(test (sum-inrange (list -2 -5 10)) -7)
(test (sum-inrange empty) 0)
(test (sum-inrange (list 1 2 3 4 5 6)) 0)

; Problem #3 (0.5 pts)
;
; Write a function startswith? which takes as input two strings and
; returns true if the first string begins with the second (you are
; encouraged to review Racket's string primitives at
; https://docs.racket-lang.org/reference/strings.html; many of them
; are available in plai-typed).

(define (startswith? [a : string] [b : string]) : boolean
  (cond [(>= (string-length a) (string-length b))
         (string=? (substring a 0 (string-length b)) b)]
        [else #f]))

(test (startswith? "Hello world!" "Hell") #t)
(test (startswith? "Hello world!" "lo w") #f)
(test (startswith? "Hell" "Hello world!") #f)

; Problem #4 (0.5 pts)
;
; Write a function replaceP which takes a list of strings and replaces
; every string starting with 'P' with 'none', keeping the other elements
; unchanged. For example:
;     (test (replaceP (list "Potatoes" "Tomatoes" "Dill")) (list "none" "Tomatoes" "Dill"))

(define (replaceP [strings : (listof string)]) : (listof string)
  (map (lambda ([str : string]) (cond [(char=? (string-ref str 0) #\P) "none"]
                                      [else str])) strings))

(test (replaceP (list "Potatoes" "Tomatoes" "Dill")) (list "none" "Tomatoes" "Dill"))
; 'P' and 'p' are not the same character:
(test (replaceP (list "Hello world!" "Pinhole camera" "pow")) (list "Hello world!" "none" "pow"))

; Problem #5 (0.5 pts)
;
; Write a function alternating which takes a list (any type of element)
; and returns a list containing every other element (i.e., only even-numbered
; elements). For example:
;     (test (alternating (list 1 2 3 4)) (list 2 4))
;     (test (alternating (list "hi" "there" "mom")) (list "there"))

(define (alternating objs)
  (alternating2 objs #f))

(define (alternating2 objs [alt : boolean])
  (cond [(empty? objs) empty]
        [alt (append (list (first objs)) (alternating2 (rest objs) #f))]
        [else (alternating2 (rest objs) #t)]))

(test (alternating (list 1 2 3 4)) (list 2 4))
(test (alternating (list "hi" "there" "mom")) (list "there"))

; Problem #6 (1 pt)
;
; Define a datatype called Scores, which contains a homework 1 score
; (non-negative number), a homework 2 score (non-negative number), a
; homework 3 score (non-negative number), and a "extra_points" field
; (a boolean). Use scores as the name of the constructor. The define-type
; does not need to enforce that the numbers are non-negative; use number
; and we will agree not to test outside that range.
;
; Then, define a datatype called Students with two variants: an undergrad
; has a name, grades (of type Scores), and a graduation year; a graduate
; has a name, grades (of type Scores), and a degree program ("MS" or "PhD").
; (undergrad and graduate should be the names of your constructors).
; Your define-type does not need to enforce the specific strings for the degree,
; just use the string type.

(define-type Scores
  [scores (hw1 : number) (hw2 : number) (hw3 : number) (extra_points : boolean)])

(define-type Students
  [undergrad (name : string) (grades : Scores) (gradYear : number)]
  [graduate (name : string) (grades : Scores) (program : string)])

; Problem #7 (1.5 pts)
;
; Write a function assign-points that takes a list of students and produces
; a list of students in which each student is assigned extra points
; (extra_points set to true) if the minimum score across all three homeworks
; is above 80.

(define (assign-points [studs : (listof Students)]) : (listof Students)
  (map (lambda ([i : Students]) (cond [(undergrad? i)
                                       (cond [(>= (min (min (scores-hw1 (undergrad-grades i)) (scores-hw2 (undergrad-grades i))) (scores-hw3 (undergrad-grades i))) 80)
                                              (undergrad (undergrad-name i) (scores (scores-hw1 (undergrad-grades i)) (scores-hw2 (undergrad-grades i)) (scores-hw3 (undergrad-grades i)) #t) (undergrad-gradYear i))]
                                             [else
                                              (undergrad (undergrad-name i) (scores (scores-hw1 (undergrad-grades i)) (scores-hw2 (undergrad-grades i)) (scores-hw3 (undergrad-grades i)) #f) (undergrad-gradYear i))])]
                                      [(graduate? i)
                                       (cond [(>= (min (min (scores-hw1 (graduate-grades i)) (scores-hw2 (graduate-grades i))) (scores-hw3 (graduate-grades i))) 80)
                                              (graduate (graduate-name i) (scores (scores-hw1 (graduate-grades i)) (scores-hw2 (graduate-grades i)) (scores-hw3 (graduate-grades i)) #t) (graduate-program i))]
                                             [else
                                              (graduate (graduate-name i) (scores (scores-hw1 (graduate-grades i)) (scores-hw2 (graduate-grades i)) (scores-hw3 (graduate-grades i)) #f) (graduate-program i))])])) studs))

(test (assign-points (list (undergrad "Ack" (scores 27 89 80 #f) 2020)
                           (graduate "Ack" (scores 27 90 98 #f) "PhD")
                           (undergrad "Ack" (scores 94 82 104 #f) 2020)))
      (list (undergrad "Ack" (scores 27 89 80 #f) 2020)
            (graduate "Ack" (scores 27 90 98 #f) "PhD")
            (undergrad "Ack" (scores 94 82 104 #t) 2020)))

; Problem #8 (1 pts)
;
; Write a function all-phd-haveextra? which consumes a list of students
; and produces a boolean indicating whether all phd students have
; achieved extra points (to be clear: assume the list has already been
; processed by assign-points).

(define (all-phd-haveextra? [studs : (listof Students)]) : boolean
  (cond [(empty? studs) #t]
        [else (cond
                [(and (graduate? (first studs)) (string=? (graduate-program (first studs)) "PhD"))
                 (and (scores-extra_points (graduate-grades (first studs))) (all-phd-haveextra? (rest studs)))]
                [else (all-phd-haveextra? (rest studs))])]))

(test (all-phd-haveextra? (assign-points (list (undergrad "Ack" (scores 27 89 80 #f) 2020)
                          (graduate "Ack" (scores 27 90 98 #f) "PhD")
                          (undergrad "Ack" (scores 94 82 104 #f) 2020))))
      #f)
(test (all-phd-haveextra? (assign-points (list (undergrad "Ack" (scores 27 89 80 #f) 2020)
                          (graduate "Ack" (scores 80 90 98 #f) "PhD")
                          (graduate "Ack" (scores 77 44 28 #f) "MS"))))
      #t)

; Problem #9 (2 pts)
;
; Write a function rainfall which takes a list of numbers representing
; daily rainfall readings. The list contains irrelevant values up to the
; first occurrence of the number -999. After that, the function should average
; all non-negative values encountered until the end of the list. Note that -999
; may never show up in the list. It may also show up multiple times, but all
; occurrences past the first one should be ignored

(define (rainfall [nums : (listof number)]) : number
  (rainfall2 nums #f))

(define (rainfall2 [nums : (listof number)] [sumnow? : boolean]) : number
  (cond [(empty? nums) 0]
        [sumnow? (/ (sum (filter (lambda (n) (>= n 0)) nums)) (length (filter (lambda (n) (>= n 0)) nums)))]
        [else (cond [(= (first nums) -999) (rainfall2 (rest nums) #t)]
                    [else (rainfall2 (rest nums) #f)])]))

(test (rainfall (list 4 -999 8 7 -999 3 -47))
      (/ (sum (filter (lambda (n) (>= n 0)) (list 8 7 3))) (length (filter (lambda (n) (>= n 0))(list 8 7 3)))))
(test (rainfall (list 8 0 123))
      0)



; Problem #10 (2 pts)
;
; An online clothing store applies discounts during checkout. A shopping cart
; is a list of the items being purchased. Each item has a name (a string like
; "shoes") and a price (a real number like 12.50). Write a function called
; checkout that consumes a shopping cart and produces the total cost of the
; cart after applying the following two discounts:
;     (i) if the cart contains at least $100 worth of hats, take 20% off the
;     cost of all hats (match only items whose exact name is "hat")
;
;     (ii) if the cart contains at least two shoes, take $10 off the total
;     of the cart (match only items whose exact name is "shoes")
;
; Each of these discounts applies to the total value of the cart before any
; discount is considered.
;
; Use the following datatype for shopping cart items:

(define-type CartItem
[item (name : string) (price : number)])

; As an example:
;     (test (checkout
;     (list (item "hat" 25) (item "bag" 50)
;     (item "hat" 85) (item "shoes" 15))) 153)
;
; Use the built-in Racket operator string=? to compare strings.

(define (checkout [items : (listof CartItem)]) : number
  (+
   (+
    (* (sum (map (lambda (i) (item-price i)) (filter (lambda (i) (string=? (item-name i) "hat")) items)))
       (cond [(>= (sum (map (lambda (i) (item-price i)) (filter (lambda (i) (string=? (item-name i) "hat")) items))) 100)
              0.8]
             [else 1]
             ))
    (+ (sum (map (lambda (i) (item-price i)) (filter (lambda (i) (string=? (item-name i) "shoes")) items)))
       (cond [(>= (length (filter (lambda (i) (string=? (item-name i) "shoes")) items)) 2)
              -10]
             [else 0]
             )))
   (sum (map (lambda (i) (item-price i)) (filter (lambda (i) (and (not (string=? (item-name i) "hat")) (not (string=? (item-name i) "shoes")))) items)))))

(test (checkout
       (list (item "hat" 25) (item "bag" 50)
             (item "hat" 85) (item "shoes" 15)))
      153)
(test (checkout
       (list (item "hat" 25) (item "bag" 50)
             (item "hat" 85) (item "shoes" 15) (item "shoes" 10)))
      153)
