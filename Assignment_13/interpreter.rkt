#lang racket

(require "../chez-init.rkt")
(provide eval-one-exp)

;-------------------+
;                   |
;   sec:DATATYPES   |
;                   |
;-------------------+

; parsed expression.  You'll probably want to replace this 
; code with your expression datatype from A11b

(define-datatype expression expression?  
  [var-exp
   (id symbol?)]
  
  [lit-exp
   (data (or/c number? boolean? string? vector? null?))]
  
  [lambda-exp
   (bindings (listof symbol?))
   (body (listof expression?))]
  
  [lambda-exp-var
   (bindings (listof symbol?))
   (body (listof expression?))]

  [named-let-exp
   (name symbol?)
   (params (listof (list/c symbol? expression?)))
   (body (listof expression?))]

  [let-exp
   (params (listof (list/c symbol? expression?)))
   (body (listof expression?))]

  [let*-exp
   (params (listof (list/c symbol? expression?)))
   (body (listof expression?))]

  [letrec-exp
   (params (listof (list/c symbol? expression?)))
   (body expression?)]

  [if-exp
   (if-clause expression?)
   (body expression?)]

  [if-else-exp
   (if-clause expression?)
   (true-body expression?)
   (false-body expression?)]

  [set!-exp
   (var expression?)
   (body expression?)]
  
  [app-exp
   (rator expression?)
   (rand (listof expression?))])
	
;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals (list-of? scheme-value?))
   (env environment?)])


; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)])

  
;-------------------+
;                   |
;    sec:PARSER     |
;                   |
;-------------------+

; This is a parser for simple Scheme expressions, such as those in EOPL 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Helper procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

;Helper functions:
(define check-for-num
  (lambda (a)
    (cond
      [(null? a) #f]
      [(number? (car a)) #t]
      [else (check-for-num (cdr a))]
      )
    )
  )

(define check-proper-list
  (lambda (a)
    (cond
      [(null? a) #t]
      [(not (list? a)) #f]
      [(not (list? (car a))) #f]
      [else (check-proper-list (cdr a))]
      )
    )
  )

(define check-sub-lets
  (lambda (a)
    (cond
      [(not (equal? (length a) 2)) #f]
      [(number? (car a)) #f]
      [else #t]
      )
    )
  )

(define check-lets
  (lambda (a)
    (cond
      [(null? a) #t]
      [(not (check-sub-lets (car a))) #f]
      [else (check-lets (cdr a))]
      )
    )
  )

(define app?
  (lambda (exp)
    (cond [(null? exp) #f]
          [(not (list? exp)) #f]
          [(or (eqv? (car exp) 'lambda)
               (eqv? (car exp) 'let)
               (eqv? (car exp) 'letrec)
               (eqv? (car exp) 'let*)
               (eqv? (car exp) 'set!)
               (eqv? (car exp) 'if))
           #f]
          [else #t])))

; Again, you'll probably want to use your code from A11b

(define parse-exp         
  (lambda (datum)
    (cond
      [(null? datum) (lit-exp datum)]
      [(symbol? datum) (var-exp datum)]
      [(number? datum) (lit-exp datum)]
      [(boolean? datum) (lit-exp datum)]
      [(vector? datum) (lit-exp datum)]
      [(string? datum) (lit-exp datum)]
      [(not (list? datum)) (error 'parse-exp "Error: Improper list")]
      [(pair? datum)
       (cond
         ;Length 1
         [(and (equal? 1 (length datum)) (not (symbol? (car datum)))) (parse-exp (car datum))]

         ;Lambda (The error checking is a little messier for this one, mb)
         [(eqv? (car datum) 'lambda)
          (if (< (length datum) 3)
              (error 'parse-exp "Error: Missing lambda arguments")
              (if (symbol? (cadr datum))
                  (if (> (length datum) 3)
                      (lambda-exp-var (list (cadr datum))
                                  (map (lambda (x)
                                         (if (app? x)
                                             (app-exp (parse-exp (car x)) (map parse-exp (cdr x)))
                                             (parse-exp x)))
                                       (cddr datum)))
                      (lambda-exp-var (list (cadr datum))
                                      (map parse-exp (list (cddr datum)))))
                  (if (check-for-num (2nd datum))
                                     (error 'parse-exp "Error: Invalid lambda parameters")
                                     (lambda-exp (2nd datum)
                                                 (map (lambda (x)
                                                        (if (app? x)
                                                            (app-exp (parse-exp (car x)) (map parse-exp (cdr x)))
                                                            (parse-exp x)))
                                                      (cddr datum))))))]

         ;Named Let
         [(and (eqv? (car datum) 'let) (not (list? (cadr datum))))
          (cond
            [(not (check-proper-list (3rd datum))) (error 'parse-exp "Error: Improper let params")]
            [(not (list? (3rd datum))) (error 'parse-exp "Error: Let params not a list")]
            [(not (check-lets (3rd datum))) (error 'parse-exp "Error: let params invalid")]
            [else (let ([params (map (lambda (p) (list (car p) (parse-exp (cadr p)))) (caddr datum))])
                   (named-let-exp (cadr datum) params (map parse-exp (cdddr datum))))]
            )]

         ;Let
         [(eqv? (car datum) 'let)
          (cond
            [(not (check-proper-list (2nd datum))) (error 'parse-exp "Error: Improper let params")]
            [(not (list? (cadr datum))) (error 'parse-exp "Error: Let params not a list")]
            [(not (check-lets (2nd datum))) (error 'parse-exp "Error: let params invalid")]
            [(null? (cddr datum)) (error 'parse-exp "Error: no body provided")]
            [else (let ([params (map (lambda (p) (list (car p) (parse-exp (cadr p)))) (cadr datum))])
                   (let-exp params (map parse-exp (cddr datum))))]
            )]

         ;Let*
         [(eqv? (car datum) 'let*)
          (cond
            [(not (check-proper-list (2nd datum))) (error 'parse-exp "Error: Improper let params")]
            [(not (list? (cadr datum))) (error 'parse-exp "Error: Let params not a list")]
            [(not (check-lets (2nd datum))) (error 'parse-exp "Error: let params invalid")]
            [else (let ([params (map (lambda (p) (list (car p) (parse-exp (cadr p)))) (cadr datum))])
                    (let*-exp params (map parse-exp (cddr datum))))]
            )]

         ;LetRec
         [(eqv? (car datum) 'letrec)
          (cond
            [(not (check-proper-list (2nd datum))) (error 'parse-exp "Error: Improper let params")]
            [(not (list? (cadr datum))) (error 'parse-exp "Error: Let params not a list")]
            [(not (check-lets (2nd datum))) (error 'parse-exp "Error: let params invalid")]
            [(null? (cddr datum)) (error 'parse-exp "Error: no body provided")]
            [else (let ([params (map (lambda (p) (list (car p) (parse-exp (cadr p)))) (cadr datum))])
                    (letrec-exp params (parse-exp (caddr datum))))]
            )]

         ;If/If else
         [(eqv? (car datum) 'if)
          (cond
            [(equal? (length datum) 3) (if-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))]
            [(equal? (length datum) 4) (if-else-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)) (parse-exp (4th datum)))]
            [else (error 'parse-exp "Error: Invalid if expression length")]
            )]

         ;Set!
         [(eqv? (car datum) 'set!)
          (cond
            [(not (equal? (length datum) 3)) (error 'parse-exp "Error: Invalid set! length")]
            [else (set!-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))]
            )]
          

         ;Application
         [else (app-exp (parse-exp (1st datum))
                        (map parse-exp (cdr datum)))])]
      [else (error 'parse-exp "bad expression: ~s" datum)])))


;-------------------+
;                   |
; sec:ENVIRONMENTS  |
;                   |
;-------------------+


; Environment definitions for CSSE 304 Scheme interpreter.  
; Based on EoPL sections 2.2 and 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms vals env)))

(define list-find-position
  (lambda (sym los)
    (let loop ([los los] [pos 0])
      (cond [(null? los) #f]
            [(eq? sym (car los)) pos]
            [else (loop (cdr los) (add1 pos))]))))
	    
(define apply-env
  (lambda (env sym) 
    (cases environment env 
      [empty-env-record ()      
                        (error 'env "variable ~s not found." sym)]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env env sym)))])))


;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

; To be added in assignment 14.

;---------------------------------------+
;                                       |
; sec:CONTINUATION DATATYPE and APPLY-K |
;                                       |
;---------------------------------------+

; To be added in assignment 18a.


;-------------------+
;                   |
;  sec:INTERPRETER  |
;                   |
;-------------------+

; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form)
    ; later we may add things that are not expressions.
    (eval-exp form)))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
               (apply-env init-env id)]
      [app-exp (rator rands)
               (let ([proc-value (eval-exp rator)]
                     [args (eval-rands rands)])
                 (apply-proc proc-value args))]
      [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (rands)
    (map eval-exp rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      ; You will add other cases
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))

(define *prim-proc-names* '(+ - * add1 sub1 cons =))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
   *prim-proc-names*   ;  a value (not an expression) with an identifier.
   (map prim-proc      
        *prim-proc-names*)
   (empty-env)))

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (+ (1st args) (2nd args))]
      [(-) (- (1st args) (2nd args))]
      [(*) (* (1st args) (2nd args))]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [else (error 'apply-prim-proc 
                   "Bad primitive procedure name: ~s" 
                   prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (parse-exp x))))
