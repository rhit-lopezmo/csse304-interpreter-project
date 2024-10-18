#lang racket

(require "../chez-init.rkt")
(provide eval-one-exp)
(provide add-macro-interpreter)

(define add-macro-interpreter (lambda x (error "nyi")))
(provide quasiquote-enabled?)
(define quasiquote-enabled?
         (lambda () (error "nyi"))) ; make this return 'yes if you're trying quasiquote

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

  [quote-exp
   (body (or/c symbol? (listof symbol?) list? string? vector? null?))]

  [closure-exp
   (params (listof symbol?))
   (body (listof expression?))
   (stored-env environment?)]
  
  [app-exp
   (rator expression?)
   (rand (listof expression?))]

  [cond-exp
   (test expression?)
   (bodies (listof expression?))]

  [cond-block
   (exps (listof expression?))
   ]
  )
	
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
   (name symbol?)]
  [lambda-proc
   (closure expression?)])



  
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

         ; Lambda App
         [(and (equal? 1 (length datum)) (list? (car datum)) (equal? 'lambda (caar datum)))
          (app-exp (parse-exp (car datum)) '())]
         
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

         ;Cond
         [(eqv? (car datum) 'cond)
          (cond-block (map (lambda (condExp)
                 (cond-exp (parse-exp (first condExp)) (map parse-exp (cdr condExp))))
                 (cdr datum)))]

         ;Quote
         [(eqv? (car datum) 'quote)
          (quote-exp (cadr datum))]
          
         ;Application
         [else
          (app-exp (parse-exp (1st datum))
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
                        (apply-env-global init-env sym)]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env env sym)))])))
(define apply-env-global
  (lambda (env sym) 
    (cases environment env 
      [empty-env-record ()      
                        (error 'env "variable ~s not found." sym)]
      [extended-env-record (syms vals env)
                           (let ((pos (list-find-position sym syms)))
                             (if (number? pos)
                                 (list-ref vals pos)
                                 (apply-env-global env sym)))])))


;-----------------------+
;                       |
;  sec:SYNTAX EXPANSION |
;                       |
;-----------------------+

(define syntax-expand
    (lambda (exp)
        (cases expression exp
            [var-exp (symbol) exp] ;; do nothing
            [lit-exp (literal) exp] ;; do nothing
            [cond-exp (test bodies)
                      (if-else-exp test
                          (last bodies)
                          (lit-exp #f))]
            [cond-block (exps)
                        (let ([result (syntax-expand (car exps))])
                          (if-else-exp result
                              result
                              (syntax-expand (cdr exps))))]
          [else (display "todo")])))

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
    (top-level-eval (parse-exp form))))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (env exp)
    (cases expression exp
      [quote-exp (body) body]
      [if-exp (if-clause body)
              (when (eval-exp env if-clause)
                (eval-exp env body))]
      [if-else-exp (if-clause true-body false-body)
              (if (eval-exp env if-clause)
                  (eval-exp env true-body)
                  (eval-exp env false-body))]
      [let-exp (params bodies) ;Change this to be consistent with ours
               (let* ([init-vals (eval-rands env (map (lambda (x) (second x)) params))]
                      [new-env (extend-env
                                (map (lambda (x) (first x)) params)
                                init-vals
                                env)])
                      (last (eval-rands new-env bodies)))]
      [lit-exp (datum) datum]
      [closure-exp (params body stored-env)
                   (let* ([init-vals (map (lambda (y) (apply-env env y)) params)]
                          [new-env (extend-env params init-vals stored-env)])
                     (last (eval-rands new-env body)))]
                
      [lambda-exp (bindings body) (lambda-proc (closure-exp bindings body env))]
      [lambda-exp-var (bindings body) (lambda-proc (closure-exp bindings body env))]
      [var-exp (id)
               (apply-env env id)]
      [app-exp (rator rands)
               (cond [(equal? (car rator) 'lambda-exp)
                      (let* ([closure (cadr (eval-exp env rator))]
                             [init-vals (eval-rands env rands)])
                        (let-values ([(closure-params closure-body stored-env) (closure-fields closure)])
                          (let ([new-env (extend-env closure-params init-vals stored-env)])
                            (last (eval-rands new-env closure-body)))))]
                     [(equal? (car rator) 'lambda-exp-var)
                      (let* ([closure (cadr (eval-exp env rator))]
                             [init-vals (eval-rands env rands)])
                        (let-values ([(closure-params closure-body stored-env) (closure-fields closure)])
                          (let ([new-env (extend-env closure-params (list init-vals) stored-env)])
                            (last (eval-rands new-env closure-body)))))]
                     [else (let ([proc-value (eval-exp env rator)]
                             [args (eval-rands env rands)])
                         (apply-proc proc-value args))]
               )]
      [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))

(define closure-fields
  (lambda (closure)
    (cases expression closure
      [closure-exp (params body stored-env)
               (values params body stored-env)]
      [else (error "don't do this")])))
      

; evaluate the list of operands, putting results into a list

(define eval-rands
  (lambda (env rands)
    (map (lambda (exp) (eval-exp env exp)) rands)))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val proc-value
      [prim-proc (op) (apply-prim-proc op args)]
      [lambda-proc (closure) (let-values ([(closure-params closure-body stored-env) (closure-fields closure)])
                               (eval-exp (extend-env closure-params args stored-env) closure))]
      ; You will add other cases
      ;Add lambda here!
      [else (error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                   proc-value)])))

(define *prim-proc-names* '(+ - * add1 sub1 cons = quote / list->vector vector->list vector?
                              number? symbol? caar cadr cadar list? eq? equal? null? procedure?
                              >= not zero? car cdr length list pair? vector vector-set!
                              vector-ref display newline cr < map apply))

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
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [(list->vector) (list->vector (first args))]
      [(vector->list) (vector->list (first args))] 
      [(vector?) (vector? (first args))]
      [(number?) (number? (first args))]
      [(symbol?) (symbol? (first args))] 
      [(caar) (caar (first args))] 
      [(cadr) (cadr (first args))] 
      [(cadar) (cadar (first args))] 
      [(list?) (list? (first args))]
      [(eq?) (if (eq? (first args) (second args)) #t #f)]
      [(equal?) (if (equal? (first args) (second args)) #t #f)] 
      [(null?) (null? (first args))] 
      [(>=) (if (>= (first args) (second args)) #t #f)]
      [(<) (if (< (first args) (second args)) #t #f)]
      [(not) (not (first args))] 
      [(zero?) (if (equal? (car args) 0) #t #f)] 
      [(car) (car (first args))]
      [(cdr) (cdr (first args))]
      [(length) (length (first args))] 
      [(list) (apply list args)]
      [(procedure?) (if (list? args)
                        (if (list? (first args))
                            (or (procedure? (first args)) (proc-val? (first args)))
                            (or (procedure? args) (proc-val? args)))
                        (procedure? args))]
      [(pair?) (pair? (first args))]
      [(vector) (apply vector args)]
      [(vector-set!) (vector-set! (first args) (second args) (third args))]
      [(vector-ref) (vector-ref (first args) (second args))]
      [(display) (apply display args)]
      [(newline) (newline)]
      [(quote) (first args)]
      [(map) (map (lambda (x) (apply-proc (first args) x)) (second args))]
      [(apply) (apply (lambda (x) (apply-proc (first args) x)) (cdr args))]
      [(cr) (letrec ([make-easy (lambda (str proc)
                               (cond
                                 [(null? str) proc]
                                 [(equal? (car str) #\a) (make-easy (cdr str) (cons car proc))]
                                 [(equal? (car str) #\d) (make-easy (cdr str) (cons cdr proc))]))])
              ((apply compose (reverse (make-easy (string->list (first args)) '()))) (second args)))]
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
   (lambda (exp) 
       (top-level-eval (syntax-expand (parse-exp exp)))))
