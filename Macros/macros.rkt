#lang racket

; only functions in racket/base can be used by default in macros
; this adds some other useful prodcedures
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
    [(all-equal exp)
     #'exp]
    [(all-equal exp exp2 rest ...)
     #'(if (equal? exp exp2)
           (all-equal exp2 rest ...)
           #f)]))

(all-equal 1 1 1 1)

(define-syntax (begin-unless stx)
  (syntax-case stx ()
    [(begin-unless _ ...)
     #''nyi]))

             
(define-syntax (range-cases stx)
  (syntax-case stx (< else)
    [(range-cases _ ...) #''nyi]))   



(define-syntax (let-destruct stx)
  (syntax-case stx ()
    [(let-destruct _ ...) #''nyi]))

(define-syntax (ifelse stx)
  #'(error "nyi"))
