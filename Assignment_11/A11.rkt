#lang racket

(require "../chez-init.rkt")
(provide bintree-to-list bintree-add leaf-node interior-node parse-exp unparse-exp)


(define-datatype bintree bintree?
  (leaf-node
   (datum number?))
  (interior-node
   (key symbol?)
   (left-tree bintree?)
   (right-tree bintree?)))

; I've provide this one as a sample to you.
; It's used by the testcases though  so don't mess with it.
(define bintree-to-list
  (lambda (bt)
    (cases bintree bt
      [interior-node (value left right)
                (list value
                      (bintree-to-list left)
                      (bintree-to-list right))]
      [leaf-node (datum)
                 datum])))
                
; Here's the one you need to solve
(define bintree-add
  (lambda (bt num)
    (cases bintree bt
      [interior-node (value left right)
                     (interior-node value
                                    (bintree-add left num)
                                    (bintree-add right num))]
      [leaf-node (datum)
                 (leaf-node (+ datum num))])))

; This is a parser for simple Scheme expressions, 
; such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

(define-datatype expression expression?
  [var-exp
   (id symbol?)]
  
  [lit-exp
   (data (or/c number? boolean? string? vector?))]
  
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

; Procedures to make the parser a little bit saner.
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

(define parse-exp         
  (lambda (datum)
    (cond
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

(define unparse-exp
  (lambda (exp)
    (cases expression exp
      
      [var-exp (id)
               id]
      
      [lit-exp (data)
               data]
      
      [lambda-exp (bindings body)
                  (append (list 'lambda bindings) (map unparse-exp body))]
      
      [lambda-exp-var (bindings body)
                      (append (list 'lambda (car bindings)) (map unparse-exp body))]
      
      [named-let-exp (name params body)
                     (append (list 'let
                                   name
                                   (map (lambda (curr-pair) (list (car curr-pair) (unparse-exp (cadr curr-pair)))) params))
                             (car (map unparse-exp body)))]
      
      [let-exp (params body)
               (append (list 'let
                             (map (lambda (curr-pair) (list (car curr-pair) (unparse-exp (cadr curr-pair)))) params))
                       (map unparse-exp body))]
      
      [let*-exp (params body)
                (append (list 'let*
                              (map (lambda (curr-pair) (list (car curr-pair) (unparse-exp (cadr curr-pair)))) params))
                        (map unparse-exp body))]
      
      [letrec-exp (params body)
                  (append (list 'letrec
                                (map (lambda (curr-pair) (list (car curr-pair) (unparse-exp (cadr curr-pair)))) params))
                          (map unparse-exp (list body)))]
      
      [if-exp (if-clause body)
              (list 'if (unparse-exp if-clause) (unparse-exp body))]
      
      [if-else-exp (if-clause true-body false-body)
                   (list 'if (unparse-exp if-clause) (unparse-exp true-body) (unparse-exp false-body))]
      
      [set!-exp (var body)
                (list 'set! (unparse-exp var) (unparse-exp body))]
      
      [app-exp (rator rand)
               (append (list (unparse-exp rator)) (map unparse-exp rand))])))

; An auxiliary procedure that could be helpful.
(define var-exp?
  (lambda (x)
    (cases expression x
      [var-exp (id) #t]
      [else #f])))

;;--------  Used by the testing mechanism   ------------------

(define-syntax nyi
  (syntax-rules ()
    ([_]
     [error "nyi"])))
