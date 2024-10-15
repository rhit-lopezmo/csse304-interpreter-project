#lang racket

; only functions in racket/base can be used by default in macros
; this adds some other useful prodcedures

;Collaboration between Bryson Lee and Manuel Lopez. Talked to Buffalo in class about working together
(require (for-syntax racket/list)) 

(provide my-let null-let all-equal begin-unless range-cases ifelse let-destruct)

(define-syntax (my-let stx)
  (syntax-case stx ()
    [(my-let ((name value) ...) bodies ...)
     #'((lambda (name ...) bodies ...) value ...)]
    [(my-let funcName ((name value) ...) bodies ...)
     #'(letrec ([funcName (lambda (name ...) bodies ...)]) (funcName value ...))]))

(define-syntax (null-let stx)
   (syntax-case stx ()
     [(null-let (name ...) bodies ...)
      #'(let ((name null) ...) bodies ...)]))

(define-syntax (all-equal stx)
  (syntax-case stx ()
    [(all-equal exp1 exp2)
     #'(equal? exp1 exp2)]
    [(all-equal exp1 exp2 rest ...)
     #'(let* ([expVal1 exp1]
              [expVal2 exp2])
         (and (equal? expVal1 expVal2) (all-equal expVal2 rest ...)))]))

(define-syntax (begin-unless stx)
  (syntax-case stx ()
    [(begin-unless var)
     #'var]
    [(begin-unless var body1 bodies ...)
     #'(if (not var)
           (begin
             body1
             (begin-unless var bodies ...))
           var)]))
             
(define-syntax (range-cases stx)
  (syntax-case stx (< else)
    [(range-cases val (rand exp))
     #'exp]
    [(range-cases valExp (rand threshold exp) (rand2 ...) ...)
     #'(let ([val valExp])
         (if (rand val threshold)
             exp
             (range-cases val (rand2 ...) ...)))]))

(define-syntax (ifelse stx)
  (let* ([fullCode (syntax->datum stx)]
         [code (cddr fullCode)]
         [predicate? (cadr fullCode)]
         [else-pos (let loop ([code code] [pos 1])
                      (cond [(equal? 'else (car code))
                             pos]
                            [else (loop (cdr code) (+ pos 1))]))]
         [then-body (take code (- else-pos 1))]
         [else-body (drop code else-pos)]
         [begin-list (list 'begin)]
         [result (list 'if predicate? (append begin-list then-body) (append begin-list else-body))])
    (datum->syntax stx result)))
                       
(define-syntax (let-destruct stx)
  (syntax-case stx ()
    [(let-destruct _ ...) #''nyi]))
