(#%require "define-datatype.scm")
(#%require "sllgen.scm")

(#%require racket/file)

;; ----------------------------------------------------------------------
;; Lexer specification
;; ----------------------------------------------------------------------

(define let-scanner-spec
  '((white-sp (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier (letter (arbno (or letter digit))) symbol)
    (number (digit (arbno digit)) number)
    (equals ("=") string)
    (minus ("-") string)
    (lparen ("(") string)
    (rparen (")") string)
    (comma (",") string)
    (let ("let") string)
    (letrec ("letrec") string)
    (in ("in") string)
    (if ("if") string)
    (then ("then") string)
    (else ("else") string)
    (zero? ("zero?") string)
    (less? ("less?") string)
    (more? ("more?") string)
    (cons ("cons") string)
    (car ("car") string)
    (cdr ("cdr") string)
    (cadr ("cadr") string)
    (cddr ("cddr") string)
    (caddr ("caddr") string)
    (cdddr ("cdddr") string)
    (emptylist ("emptylist") string)
    (list ("list") string)
    (proc ("proc") string)
    ))

;; ----------------------------------------------------------------------
;; Parser specification
;; ----------------------------------------------------------------------

(define let-grammar-spec
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)
    (expression
     ("zero?" "(" expression ")")
     zero?-exp)
    (expression
     ("less?" "(" expression "," expression ")")
     less?-exp)
    (expression
     ("more?" "(" expression "," expression ")")
     more?-exp)
    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)
    (expression (identifier) var-exp)
    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)
    (expression
     ("letrec" identifier "(" identifier ")" "=" expression "in" expression)
     letrec-exp)
    (expression
     ("(" expression expression (arbno expression) ")")
     app-exp)
    (expression
     ("cons" "(" expression "," expression ")")
     cons-exp)
    (expression
     ("car" "(" expression ")")
     car-exp)
    (expression
     ("cdr" "(" expression ")")
     cdr-exp)
    (expression
     ("cadr" "(" expression ")")
     cadr-exp)
    (expression
     ("cddr" "(" expression ")")
     cddr-exp)
    (expression
     ("caddr" "(" expression ")")
     caddr-exp)
    (expression
     ("cdddr" "(" expression ")")
     cdddr-exp)
    (expression
     ("emptylist")
     emptylist-exp)
    (expression
     ("null?" "(" expression ")")
     null?-exp)
    (expression
     ("list" "(" (separated-list expression ",") ")" )
     list-exp)
    (expression
     ("proc" "(" identifier (arbno identifier) ")" expression)
     proc-exp)    
    ))

;; ----------------------------------------------------------------------
;; Use sllgen to generate lexer and parser 
;; sllgen functions come from sllgen.scm 
;; ----------------------------------------------------------------------

(define parser
  (sllgen:make-string-parser let-scanner-spec let-grammar-spec))

(sllgen:make-define-datatypes let-scanner-spec let-grammar-spec)

;; ----------------------------------------------------------------------
;; expval data type - expressed values
;; ----------------------------------------------------------------------

(define pair-or-nil?
  (lambda (v)
    (or (pair? v) (null? v))))

(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (list-val
   (list pair-or-nil?))
  (proc-val
   (proc proc?)))

(define expval->num
    (lambda (v)
      (cases expval v
        (num-val (num) num)
        (else (expval-extractor-error 'num v)))))

(define expval->bool
    (lambda (v)
      (cases expval v
        (bool-val (bool) bool)
        (else (expval-extractor-error 'bool v)))))

(define expval->pair
  (lambda (v)
    (cases expval v
           (list-val (car cdr)
                     (cons car cdr))
           (else (expval-extractor-error 'pair v)))))

(define expval->list
  (lambda (v)
    (cases expval v
      (list-val (lst) (expval->schemeval (list-val lst)))
      (else (expval-extractor-error 'list v)))))

(define expval-null?
  (lambda (v)
    (cases expval v
           (emptylist-val () (bool-val #t))
           (else (bool-val #f)))))

(define expval->proc
  (lambda (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (expval-extractor-error 'proc v)))))

(define expval-extractor-error
    (lambda (variant value)
      (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                   variant value)))

;; ----------------------------------------------------------------------
;; env data type - environment mapping variables to values
;; ----------------------------------------------------------------------

(define-datatype env env?
  (empty-env)
  (extend-env (var symbol?) (val expval?) (env env?))
  (letrec-extend-env (procname symbol?) (param symbol?) (procbody expression?) (saved-env env?))
  )

(define apply-env
  (lambda (var e)
    (cases env e
      (empty-env ()
        (eopl:error 'apply-env "Undefined variable: ~s" var))
      (extend-env (e-var e-val e-env)
        (if (eq? var e-var)
            e-val
            (apply-env var e-env)))
      (letrec-extend-env (procname param procbody saved-env)
        (if (eq? var procname)
            (proc-val (a-proc param procbody e))
            (apply-env var saved-env)))
      )))

;; ----------------------------------------------------------------------
;; continuation data type
;; ----------------------------------------------------------------------

(define-datatype continuation continuation?
  ;; End of the computation: a "final answer" has been computed!
  (end-cont)
  ;; Continuation for the zero? predicate: receives the value
  ;; of the subexpression which we want to test.
  (zero1-cont (saved-cont continuation?))
  ;; Continuation for if: receives the (boolean) value of the condition
  ;; of the if.
  (if-test-cont (exp2 expression?)
                (exp3 expression?)
                (saved-env env?)
                (saved-cont continuation?))
  ;; Continuation for the difference ("-") operator.
  ;; Receives the value of the left-hand operand.
  (diff1-cont (exp2 expression?)
              (saved-env env?)
              (saved-cont continuation?))
  ;; Continuation for the difference ("-") operator.
  ;; Receives the value of the right-hand operand.
  (diff2-cont (left-operand expval?)
              (saved-cont continuation?))
  ;; Continuation for the less? operator.
  ;; Receives the value of the left-hand operand.
  (less1-cont (exp2 expression?)
              (saved-env env?)
              (saved-cont continuation?))
  ;; Continuation for the less? operator.
  ;; Receives the value of the right-hand operand.
  (less2-cont (left-operand expval?)
              (saved-cont continuation?))
  ;; Continuation for the more? operator.
  ;; Receives the value of the left-hand operand.
  (more1-cont (exp2 expression?)
              (saved-env env?)
              (saved-cont continuation?))
  ;; Continuation for the more? operator.
  ;; Receives the value of the right-hand operand.
  (more2-cont (left-operand expval?)
              (saved-cont continuation?))
  ;; Continuation for let.
  ;; Receives the value to which we want to bind the variable
  ;; introduced by the let.
  (let-cont (var symbol?)
            (body-exp expression?)
            (saved-env env?)
            (saved-cont continuation?))
  ;; Continuation for procedure application.
  ;; Receives the (procedure) value of the operand of the
  ;; procedure application.
  (rator-cont ;(rand-exp expression?)
              (rand-exp-list list?)
              (saved-env env?)
              (saved-cont continuation?))
  ;; Continuation for procedure application.
  ;; Receives the value of *one of* the operands of the procedure application.
  (rand-cont (procval expval?)
             (remaining-rand-exp-list list?)
             (evaluated-arg-list list?)
             (saved-env env?)
             (saved-cont continuation?))

  (cons-cont (exp2 expression?)
             (saved-env env?)
             (saved-cont continuation?))

  (cons-cont2 (val1 expval?)
              (saved-cont continuation?))

  (car-cont (saved-cont continuation?))

  (cdr-cont (saved-cont continuation?))

  (cadr-cont (saved-cont continuation?))

  (cddr-cont (saved-cont continuation?))

  (caddr-cont (saved-cont continuation?))

  (cdddr-cont (saved-cont continuation?))

  (null?-cont (saved-cont continuation?))

  (list-cont (args (list-of expression?))
             (saved-env env?)
             (saved-cont continuation?))

  (list-cont-else (args (list-of expression?))
                  (prev-args list?)
                  (saved-env env?)
                  (saved-cont continuation?))
  )

(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont ()
        (begin 
               val))
      (zero1-cont (saved-cont)
                  (apply-cont saved-cont (bool-val (zero? (expval->num val)))))
      (if-test-cont (exp2 exp3 saved-env saved-cont)
                    (if (expval->bool val)
                        (value-of/k exp2 saved-env saved-cont)
                        (value-of/k exp3 saved-env saved-cont)))
      (diff1-cont (exp2 saved-env saved-cont)
                  (value-of/k exp2 saved-env (diff2-cont val saved-cont)))
      (diff2-cont (left-operand saved-cont)
                  (apply-cont saved-cont (num-val (- (expval->num left-operand)
                                                     (expval->num val)))))
      (less1-cont (exp2 saved-env saved-cont)
                  (value-of/k exp2 saved-env (less2-cont val saved-cont)))
      (less2-cont (left-operand saved-cont)
                  (apply-cont saved-cont (bool-val (< (expval->num left-operand)
                                                      (expval->num val)))))
      (more1-cont (exp2 saved-env saved-cont)
                  (value-of/k exp2 saved-env (more2-cont val saved-cont)))
      (more2-cont (left-operand saved-cont)
                  (apply-cont saved-cont (bool-val (> (expval->num left-operand)
                                                      (expval->num val)))))
      (let-cont (var body-exp saved-env saved-cont)
                (value-of/k body-exp (extend-env var val saved-env) saved-cont))
      (rator-cont (rand-exp-list saved-env saved-cont)
                  (value-of/k (car rand-exp-list) saved-env (rand-cont val
                                                                       (cdr rand-exp-list)
                                                                       '()
                                                                       saved-env
                                                                       saved-cont)))
      (rand-cont (procval remaining-rand-exp-list evaluated-arg-list saved-env saved-cont)
         (if (null? remaining-rand-exp-list)
             ;; bind all proc parameters to the evaluated arguments
             (cases proc (expval->proc procval)
               (a-proc (param body-exp closure-env) ;; TODO: param should be param-list
                 (let* ((param-list (list param))  ;; TODO: eventually procedures will have multiple parameters
                        (arg-list (append evaluated-arg-list (list val)))
                        (call-env (create-call-env param-list arg-list closure-env)))
                   (value-of/k body-exp call-env saved-cont))))
             ;; there are more operand (i.e., argument) expressions to be evaluated
             (value-of/k (car remaining-rand-exp-list) saved-env (rand-cont procval
                                                                            (cdr remaining-rand-exp-list)
                                                                            (append evaluated-arg-list (list val))
                                                                            saved-env
                                                                            saved-cont))))

      (cons-cont (exp2 saved-env saved-cont)
                 (value-of/k exp2 saved-env
                             (cons-cont2 val saved-cont)))

      (cons-cont2 (val1 saved-cont)
                  (apply-cont saved-cont
                              (list-val (list val1 val))))

      (car-cont (saved-cont)
                (apply-cont saved-cont
                            (car (expval->list val))))

      (cdr-cont (saved-cont)
                (apply-cont saved-cont
                            (cdr (expval->list val))))

      (cadr-cont (saved-cont)
                (apply-cont saved-cont
                            (cadr (expval->list val))))

      (cddr-cont (saved-cont)
                (apply-cont saved-cont
                            (cddr (expval->list val))))

      (caddr-cont (saved-cont)
                (apply-cont saved-cont
                            (caddr (expval->list val))))

      (cdddr-cont (saved-cont)
                (apply-cont saved-cont
                            (cdddr (expval->list val))))
      
      (null?-cont (saved-cont)
                  (apply-cont saved-cont
                              (expval-null? val)))
      
      (list-cont (args saved-env saved-cont)
                 (if (null? args)
                     (apply-cont saved-cont
                                 (list-val val (emptylist-val)))
                     (value-of/k (car args)
                                 saved-env
                                 (list-cont-else (cdr args)
                                                 (list val)
                                                 saved-env saved-cont))))

      (list-cont-else (args prev-args saved-env saved-cont)
                      (if (null? args)
                          (apply-cont saved-cont
                                      (list-val (append prev-args (list val))))
                          (value-of/k (car args)
                                      saved-env
                                      (list-cont-else
                                       (cdr args)
                                       (append prev-args (list val))
                                       saved-env
                                       saved-cont))))
      )))

(define create-call-env
  (lambda (param-list arg-list env)
    (if (null? param-list)
        env
        (create-call-env (cdr param-list)
                         (cdr arg-list)
                         (extend-env (car param-list) (car arg-list) env)))))

;; ----------------------------------------------------------------------
;; proc data type - represents a procedure
;; ----------------------------------------------------------------------

(define-datatype proc proc?
  (a-proc (param symbol?)
          (body expression?)
          (saved-env env?)))

;; ----------------------------------------------------------------------
;; The interpreter (CPS)
;; ----------------------------------------------------------------------



(define value-of-program
  (lambda (p env)
    (cases program p
      (a-program (exp)
       (value-of/k exp env (end-cont))))))

(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      (const-exp (num) (apply-cont cont (num-val num)))
      (var-exp (var) (apply-cont cont (apply-env var env)))
      (proc-exp (param more-params body-exp)
                (apply-cont cont
                            (proc-val (a-proc param body-exp env))))
      (zero?-exp (exp1) (value-of/k exp1 env (zero1-cont cont)))
      (letrec-exp (procname param procbody-exp body-exp)
                  (value-of/k body-exp (letrec-extend-env procname param procbody-exp env) cont))
      (if-exp (exp1 exp2 exp3) (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
      (diff-exp (exp1 exp2)
                (value-of/k exp1 env (diff1-cont exp2 env cont)))
      (let-exp (var val-exp body-exp)
               (value-of/k val-exp env (let-cont var body-exp env cont)))
      (app-exp (rator-exp rand-exp more-rand-exps)
               (value-of/k rator-exp env (rator-cont (list rand-exp) env cont)))
      (less?-exp (exp1 exp2)
                 (value-of/k exp1 env (less1-cont exp2 env cont)))
      (more?-exp (exp1 exp2)
                 (value-of/k exp1 env (more1-cont exp2 env cont)))
      (cons-exp (exp1 exp2)
                (value-of/k exp1 env
                            (cons-cont exp2 env cont)))
      (car-exp (exp)
               (value-of/k exp env (car-cont cont)))
      (cdr-exp (exp)
               (value-of/k exp env (cdr-cont cont)))
      (cadr-exp (exp)
               (value-of/k exp env (cadr-cont cont)))
      (cddr-exp (exp)
               (value-of/k exp env (cddr-cont cont)))
      (caddr-exp (exp)
               (value-of/k exp env (caddr-cont cont)))
      (cdddr-exp (exp)
               (value-of/k exp env (cdddr-cont cont)))
      (null?-exp (exp)
                 (value-of/k exp env (null?-cont cont)))    
      (emptylist-exp ()
                          (apply-cont cont (emptylist-val)))
      (list-exp (args)
		     (if (null? args)
			 (apply-cont cont (emptylist-val))
			 (value-of/k (car args)
				     env
				     (list-cont (cdr args) env cont))))
    )))

;(define value-of
;  (lambda (exp env)
;    (cases expression exp
;      (const-exp (num) (num-val num))
;      (diff-exp (exp1 exp2)
;                (let ((val1 (expval->num (value-of exp1 env)))
;                      (val2 (expval->num (value-of exp2 env))))
;                  (num-val (- val1 val2))))
;      (zero?-exp (subexp)
;                 (bool-val (= (expval->num (value-of subexp env)) 0)))
;      (less?-exp (subexp subexp2)
;                 (bool-val (< (expval->num (value-of subexp env)) (expval->num (value-of subexp2 env)))))
;      (if-exp (exp1 exp2 exp3)
;              (let ((b (expval->bool (value-of exp1 env))))
;                (if b
;                    (value-of exp2 env)
;                    (value-of exp3 env))))
;      (var-exp (var) (apply-env var env))
;      (let-exp (var valexp subexp)
;               (let ((value (value-of valexp env)))
;                 (value-of subexp (extend-env var value env))))
;      (letrec-exp (procname param procbody body)
;         (value-of body (letrec-extend-env procname param procbody env)))
;      (proc-exp (param body) (proc-val (a-proc param body env)))
;      (app-exp (fn arg) (apply-procedure fn arg env))
;      )))

;(define apply-procedure
;  (lambda (fn arg env)
;    (let ((fnval (value-of fn env))
;          (argval (value-of arg env)))
;      (cases expval fnval
;        (proc-val (called-proc)
;           (cases proc called-proc
;             (a-proc (param body saved-env)
;               (let ((call-env (extend-env param argval saved-env) ))
;                 (value-of body call-env)))))
;        (else (eopl:error 'value-of "Application of non-procedure"))))))

;; ----------------------------------------------------------------------
;; Testing
;; ----------------------------------------------------------------------

(define expval->schemeval
  (lambda (result)
    (cases expval result
      (num-val (n) n)
      (bool-val (b) b)
      (list-val (lst)
                (if (null? lst)
                    lst
                    (cons (expval->schemeval (car lst)) (expval->schemeval (list-val (cdr lst))))))
      (proc-val (p) p))))
    
(define test-prog
  (lambda (filename)
    (let* ((prog (parser (file->string filename)))
            (result (value-of-program prog (empty-env))))
      (if (expval? result)
          (expval->schemeval result)
          result))))

(define run
  (lambda (string)
    (let* ((prog (parser string))
           (result (value-of-program prog (empty-env))))
      (if (expval? result)
          (expval->schemeval result)
          result))))
     