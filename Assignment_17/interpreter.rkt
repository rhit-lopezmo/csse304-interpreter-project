#lang racket

(require "../chez-init.rkt")
(provide eval-one-exp y2 advanced-letrec)
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
   (bindings (or/c (listof symbol?) symbol?))
   (body (or/c (listof expression?) expression?))]
  
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
   (rator (or/c (listof expression?) expression?))
   (rand (or/c (listof expression?) expression? list?))]

  [cond-exp
   (firstTest (or/c expression? null?))
   (firstBodies (or/c (listof expression?) null?))
   (restExps (or/c (listof expression?) null? expression?))]

  [or-exp
   (val (or/c (listof expression?) expression?))
   (rest (or/c (listof expression?) expression? null?))]
  
  [and-exp
   (val (or/c (listof expression?) expression?))
   (rest (or/c (listof expression?) expression? null?))]

  #| [map-exp
      (proc expression?)
   (args (listof expression?))] |#

  [begin-exp
    (exps (listof expression?))]
  )
	
;; environment type definitions

(define scheme-value?
  (lambda (x) #t))
  
(define-datatype environment environment?
  [empty-env-record]
  [extended-env-record
   (syms (list-of? symbol?))
   (vals vector?)
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
          [(equal? 'app (car exp)) #t]
          [else #f])))

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
                  (if (> (length datum) 3) ; lambda-exp-var
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
                                     (lambda-exp (2nd datum) ; lambda-exp
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

         ;Let/Named
         [(eqv? (car datum) 'let)
          (if (list? (cadr datum))
              (cond
                [(not (check-proper-list (2nd datum))) (error 'parse-exp "Error: Improper let params")]
                [(not (list? (cadr datum))) (error 'parse-exp "Error: Let params not a list")]
                [(not (check-lets (2nd datum))) (error 'parse-exp "Error: let params invalid")]
                [(null? (cddr datum)) (error 'parse-exp "Error: no body provided")]
                [else (let ([params (map (lambda (p) (list (car p) (parse-exp (cadr p)))) (cadr datum))])
                        (let-exp params (map parse-exp (cddr datum))))])
              
              (let ([params (map (lambda (p) (list (car p) (parse-exp (cadr p)))) (caddr datum))])
                        (named-let-exp (cadr datum) params (map parse-exp (cdddr datum)))))
          ]

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
          (let* ([exps (cdr datum)]
                 [firstTest (caar exps)]
                 [firstBodies (cdar exps)]
                 [restExps (cdr exps)])
            (if (null? restExps)
                (cond-exp (parse-exp firstTest)
                          (map parse-exp firstBodies)
                          '())
                (cond-exp (parse-exp firstTest)
                          (map parse-exp firstBodies)
                          (parse-exp (cons 'cond restExps)))))]
         
         ;Quote
         [(eqv? (car datum) 'quote)
          (quote-exp (cadr datum))]

         ; Map
         #| [(eqv? (car datum) 'map)
             (let*  ([proc (parse-exp (cadr datum))]
                     [args (cddr datum)])
            (app-exp (var-exp 'list) (map (lambda (x) (app-exp proc (parse-exp x))) args)))] |#

         ;Or
         [(eqv? (car datum) 'or)
          (let* ([exps (cdr datum)])
            (if (null? exps)
                (or-exp (lit-exp '()) (lit-exp '()))
                (or-exp (parse-exp (car exps)) (parse-exp (cons 'or (cdr exps))))))]

         ;And
         [(eqv? (car datum) 'and)
          (let* ([exps (cdr datum)])
            (if (null? exps)
                (and-exp (lit-exp '()) (lit-exp '()))
                (and-exp (parse-exp (car exps)) (parse-exp (cons 'or (cdr exps))))))]

         ;Begin
         [(eqv? (car datum) 'begin)
          (begin-exp (map parse-exp (cdr datum)))]
          
         ;Application
         [else
          (app-exp (parse-exp (1st datum))
                   (map parse-exp (cdr datum)))])]
      [else (error 'parse-exp "bad expression: ~s" datum)])))

;(require racket/trace)
;(trace parse-exp)

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
    (if (vector? vals)
         (extended-env-record syms vals env)
         (extended-env-record syms (list->vector vals) env))))
   

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
                                 (vector-ref vals pos)
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
      (if (null? exp) '()
        (cases expression exp
          [var-exp (symbol) exp] ;; do nothing
          [lit-exp (literal) exp] ;; do nothing
          [cond-exp (firstTest firstBodies restExps)
                    (if (null? restExps)
                        (if-exp firstTest (car firstBodies))
                        (if-else-exp (syntax-expand firstTest) (car firstBodies) (syntax-expand restExps)))]
          [begin-exp (exps)
                     (app-exp (lambda-exp '() (map syntax-expand exps)) '())]
          [or-exp (val rest)
                  (if (equal? val '(lit-exp ())) (lit-exp #f)
                  (let* ([expanded-val (syntax-expand val)])
                  (if (null? rest)
                      (if-else-exp expanded-val expanded-val (lit-exp #f))
                      (if-else-exp expanded-val expanded-val (syntax-expand rest)))))]
          [and-exp (val rest)
                  (if (equal? val '(lit-exp ())) (lit-exp #t)
                  (let* ([expanded-val (syntax-expand val)])
                  (if (null? rest)
                      expanded-val
                      (if-else-exp expanded-val (syntax-expand rest) (lit-exp #f)))))]
          [let-exp (params body)
                   (app-exp (lambda-exp (map (lambda (x) (first x)) params) (map syntax-expand body)) (map syntax-expand (map (lambda (x) (second x)) params)))]
          [let*-exp (params body)
                    (if (null? (cdr params))
                        (syntax-expand (let-exp params body))
                    (syntax-expand (let-exp (list (first params)) (list (syntax-expand (let*-exp (cdr params) body))))))]
          [named-let-exp (name params body)
                         (let* ([bindings (map (lambda (x) (car x)) params)]
                                [vals (map (lambda (x) (syntax-expand (cadr x))) params)]
                                [expanded-body (map syntax-expand body)]
                                [letrec-params (list (list name (lambda-exp bindings expanded-body)))]
                                [letrec-body (app-exp (var-exp name) vals)])
                           (letrec-exp letrec-params letrec-body))]
          [app-exp (rator rands)
                   (app-exp (syntax-expand rator) (map syntax-expand rands))]
          [if-exp (if-clause body)
                  (if-exp (syntax-expand if-clause) (syntax-expand body))]
          [if-else-exp (if-clause true-body false-body)
                  (if-else-exp (syntax-expand if-clause) (syntax-expand true-body) (syntax-expand false-body))]
          [lambda-exp (bindings body)
                      (lambda-exp bindings (map syntax-expand body))]
          [letrec-exp (params body)
                      (letrec-exp (map (lambda (x) (list (car x) (car (map syntax-expand (cdr x)))))
                                       params)
                                  (syntax-expand body))]
          [else
           ;(display "no case found, returning exp\n")
           exp]))))

;(require racket/trace)
;(trace parse-exp)

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
    (eval-exp init-env form)))

(define set-env-vals!
  (lambda (pos currParams valsVec env) 
    (cond [(> pos (- (vector-length valsVec) 1)) (void)]
          [else
           (vector-set! valsVec pos (eval-exp env (cadar currParams)))
           (set-env-vals! (+ pos 1) (cdr currParams) valsVec env)])))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (env exp)
    (cases expression exp
      [quote-exp (body) body]
      [if-exp (if-clause body)
              (let* ([test if-clause])
              (when (eval-exp env if-clause)
                (eval-exp env body)))]
      [if-else-exp (if-clause true-body false-body)
                   (if (equal? if-clause true-body)
                       (let ([test (eval-exp env if-clause)])
                         (if test
                             test
                             (eval-exp env false-body)))
                       (let ([test (eval-exp env if-clause)])
                         (if test
                             (eval-exp env true-body)
                             (eval-exp env false-body)))
                       )]
      [letrec-exp (params bodies)
                  (let* ([valsVec (make-vector (length params))]
                         [new-env (extend-env
                                   (map (lambda (x) (first x)) params)
                                   valsVec
                                   env)]
                         [newVals (eval-rands new-env (map (lambda (x) (second x)) params))])
                    (set-env-vals! 0 params valsVec new-env)
                    (eval-exp new-env bodies))]
                    
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
                              vector-ref display newline cr < map apply begin else > append eqv?
                              quotient list-tail))

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
      [(eqv?) (eqv? (first args) (second args))]
      [(null?) (null? (first args))] 
      [(>=) (if (>= (first args) (second args)) #t #f)]
      [(<) (if (< (first args) (second args)) #t #f)]
      [(>) (if (> (first args) (second args)) #t #f)]
      [(not) (not (first args))] 
      [(zero?) (if (equal? (car args) 0) #t #f)] 
      [(car) (car (first args))]
      [(cdr) (cdr (first args))]
      [(length) (length (first args))] 
      [(list) (apply list args)]
      [(append) (apply append args)]
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
      [(map) (map (lambda (x) (apply-proc (first args) (list x))) (second args))]
      [(apply) (apply (lambda (x) (apply-proc (first args) x)) (cdr args))]
      [(quotient) (quotient (first args) (second args))]
      [(list-tail) (list-tail (first args) (second args))]
      [(begin) (eval (append (list 'begin) args))]
      [(else) (eval (append (list 'begin) args))]
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

(define my-*p
  (lambda (self)
    (lambda (num times)
      (if (zero? times)
          0
          (+ num (self num (sub1 times)))))))

; The Y Combinator: A function that takes a function
; and returns a recursive version of that function

(define yp
  (lambda (self)
    (lambda (f)
      (f (lambda params
         (apply ((self self) f) params)))
    )))

(define y
  (yp yp))

(define my-*
  (y my-*p))



(define-syntax (basic-letrec stx)
   (syntax-case stx ()
     [(basic-letrec prod-name prod-body letrec-body)
      #'(let ((prod-name (y (lambda (prod-name) prod-body))))
          letrec-body)]))

#| (basic-letrec my-*2 (lambda (num times)
                         (if (zero? times)
                             0
                             (+ num (my-*2 num (sub1 times)))))
              (my-*2 3 4)) |#

(define my-odd?
  (lambda (my-odd? my-even?)
    (lambda (num)
      (if (zero? num)
          #f
          (my-even? (sub1 num))))))
                      
(define my-even?
  (lambda (my-odd? my-even?)
    (lambda (num)
      (if (zero? num)
          #t
          (my-odd? (sub1 num))))))

(define y2
  (lambda (which f1 f2)
    (nyi)))

(define-syntax (advanced-letrec stx)
  (syntax-case stx ()
    [(advanced-letrec ((fun-name fun-body)...) letrec-body)
     #'(error "nyi")]))

(define eval-one-exp
   (lambda (exp) 
       (top-level-eval (syntax-expand (parse-exp exp)))))

(require racket/trace)
;(trace syntax-expand)

(define-syntax nyi
  (syntax-rules ()
    ([_]
     [error "nyi"])))