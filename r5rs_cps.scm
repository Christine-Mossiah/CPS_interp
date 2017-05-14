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
     ("proc" "(" identifier (arbno identifier) ")" expression)
     proc-exp)
    (expression
     ("(" expression expression (arbno expression) ")")
     app-exp)
    ))

;; ----------------------------------------------------------------------
;; Use sllgen to generate lexer and parser from the corresponding
;; specifications.
;; ----------------------------------------------------------------------

(define lexer
  (sllgen:make-string-scanner let-scanner-spec let-grammar-spec))

(define parser
  (sllgen:make-string-parser let-scanner-spec let-grammar-spec))

(sllgen:make-define-datatypes let-scanner-spec let-grammar-spec)

;; ----------------------------------------------------------------------
;; expval data type - expressed values
;; ----------------------------------------------------------------------


(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
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
  )

(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont ()
        (begin (eopl:printf "End of computation.~%")
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
;; The interpreter
;; ----------------------------------------------------------------------

(define value-of-program
  (lambda (p env)
    (cases program p
      (a-program (exp)
       (value-of/k exp env (end-cont))))))

(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      (const-exp (n) (apply-cont cont (num-val n)))
      (var-exp (var) (apply-cont cont (apply-env var env)))
      (proc-exp (param more-params body-exp)
                (apply-cont cont (proc-val (a-proc param body-exp env))))
      (zero?-exp (subexp) (value-of/k subexp env (zero1-cont cont)))
      (letrec-exp (procname param procbody-exp body-exp)
                  (value-of/k body-exp (letrec-extend-env procname param procbody-exp env) cont))
      (if-exp (exp1 exp2 exp3) (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
      (diff-exp (exp1 exp2)
                (value-of/k exp1 env (diff1-cont exp2 env cont)))
      (let-exp (var val-exp body-exp)
               (value-of/k val-exp env (let-cont var body-exp env cont)))
      (app-exp (rator-exp rand-exp more-rand-exps);; TODO: send all rand exps to rator-cont
               (value-of/k rator-exp env (rator-cont (list rand-exp) env cont)))
      (less?-exp (exp1 exp2)
                 (value-of/k exp1 env (less1-cont exp2 env cont)))
      )
    ))

;(define value-of
;  (lambda (exp env)
;    (cases expression exp
;      (const-exp (n) (num-val n))
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
      (proc-val (p) p))))
    

(define test-proc
  (lambda (filename)
    (let* ((prog (parser (file->string filename)))
            (result (value-of-program prog (empty-env))))
      (expval->schemeval result))))

(define exec
  (lambda (progtext)
    (let* ((prog (parser progtext))
           (result (value-of-program prog (empty-env))))
      (expval->schemeval result))))

