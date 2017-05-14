;; define-datatype.scm 
#lang r5rs
(#%provide (all-defined)) 

(define eopl:printf
  (lambda (format . args)
    (let ((len (string-length format)))
      (let loop ((i 0) (args args))
        (let ((output
               (lambda (fn)
                 (fn (car args))
                 (loop  (+ i 2) (cdr args))))
              (outputc
               (lambda (fn)
                 (fn)
                 (loop (+ i 2) args))))
          (if (>= i len) #t
              (let ((c (string-ref format i)))
                (if (char=? c #\~)
                    (case (string-ref format (+ i 1))
                      ((#\s) (output write))
                      ((#\a) (output display))
                      ((#\c) (output write-char))
                      ((#\% #\n) (outputc newline))
                      ((#\~) (outputc (lambda () (write-char #\~))))
                      (else
                       (write
                        "error in eopl:printf: unknown format character ")
                       (write-char  (string-ref format (+ i 1)))
                       (write-char #\newline)
                       (eopl:error-stop)))
                    (begin
                      (display c)
                      (loop (+ i 1) args))))))))))

(define eopl:pretty-print
  (lambda (x)
    (write x)
    (newline)))

(define sllgen:pretty-print          eopl:pretty-print)
(define define-datatype:pretty-print eopl:pretty-print)

(define eopl:error
  (lambda (who format . data)
    ;; print the message
    (eopl:printf "Error reported by ~s:~%" who)
    (apply eopl:printf (cons format data))
    (newline)
    (eopl:error-stop)))

(define eopl:error-stop "eopl:error-stop is purposely undefined")

(define define-datatype:report-error eopl:error)

(define define-datatype:reset-registries 'ignored)
(define define-datatype:is-a-type? 'ignored)
(define define-datatype:datatype-checker&registry-updater 'ignored)
(define define-datatype:case-checker 'ignored)

(let ((define-datatype:type-registry '())
      (define-datatype:variant-registry '()))  

  (set! define-datatype:reset-registries
    (lambda ()
      (set! define-datatype:type-registry '())
      (set! define-datatype:variant-registry '())
      #t))

  (set! define-datatype:is-a-type?
    (lambda (type-name)
      (memq type-name define-datatype:type-registry)))

  (set! define-datatype:datatype-checker&registry-updater
    (letrec ((set?
               (lambda (s)
                 (if (null? s) #t
                   (and (not (memq (car s) (cdr s))) (set? (cdr s)))))))
      (lambda (Type-name Variants)
        (if (not (symbol? Type-name))
          (define-datatype:report-error 'define-datatype
            "~nThe data type name ~s is not an identifier."
            Type-name))
        (for-each
          (lambda (variant)
            (if (not (symbol? (car variant)))
              (define-datatype:report-error 'define-datatype
                (string-append
                  "(While defining the ~a datatype)~n"
                  "  The variant-name ~s is not an identifier.")
                Type-name (car variant))))
          Variants)
        (let ((variant-names (map car Variants)))
          (if (not (set? variant-names))
            (define-datatype:report-error 'define-datatype
              (string-append
                "(While defining the ~a datatype)~n"
                "  Some of the variant-names are repeated: ~s.")
              Type-name variant-names))
          (for-each
            (lambda (v)
              (cond  
                ((assq v define-datatype:variant-registry) =>
                 (lambda (pair)
                   (if (not (eq? (cdr pair) Type-name))
                     (define-datatype:report-error 'define-datatype
                       (string-append
                         "(While defining the ~a data type)~n"
                         "  The variant-name ~s has already been~n"
                         "  used as a variant name in ~s.")
                       Type-name v (cdr pair)))))))
            variant-names)
          (cond 
            ((assq Type-name define-datatype:variant-registry) =>
             (lambda (pair)
               (define-datatype:report-error 'define-datatype
                 (string-append
                   "(While defining the ~a data type)~n"
                   "  The type name ~s has already been~n"
                   "  used as a variant name ~s in the~n"
                   "  data type ~s.")
                 Type-name Type-name (car pair) (cdr pair))))
            ((memq Type-name variant-names)
             (define-datatype:report-error 'define-datatype
               (string-append
                 "(While defining the ~a data type)~n"
                 "  Variant name is the same as the data type name.")
               Type-name)))
          (for-each
            (lambda (variant-name)
              (cond
                ((memq variant-name define-datatype:type-registry)
                 (define-datatype:report-error 'define-datatype
                   (string-append
                     "(While defining the ~a data type)~n"
                     "  The variant name ~s has already been~n"
                     "  used as a type name.")
                   Type-name variant-name))))
            variant-names)
          (set! define-datatype:variant-registry
            (append
              (map (lambda (v) (cons v Type-name)) variant-names)
              define-datatype:variant-registry))
          (cond 
            ((memq Type-name define-datatype:type-registry) =>
             (lambda (pair)
               (set-car! pair Type-name)))
            (else
              (set! define-datatype:type-registry
                (cons Type-name define-datatype:type-registry))))))))
  
  (set! define-datatype:case-checker
    (let ((remq-or-false
            (lambda (sym ls)
              (call-with-current-continuation
                (lambda (k)
                  (let f ((ls ls))
                    (cond ((null? ls) (k #f))
                      ((eq? (car ls) sym) (cdr ls))
                      (else (cons (car ls) (f (cdr ls)))))))))))
      (lambda (Type-value Type-name Expression clauses)
        (if (eq? Type-name Expression)
          (begin
            (define-datatype:pretty-print
              (cons 'cases
                (cons Type-name
                  (cons Expression clauses))))
            (define-datatype:report-error 'cases
              (string-append
                "The data type ~s should not be the same~n"
                "  as a lexical variable.")
              Type-name))
          (let ((variant-table (cdr Type-value)))
            (let f ((clauses* clauses)
                    (unused-variants (map car variant-table)))
              (if (null? clauses*)
                (if (not (null? unused-variants))
                  (begin
                    (define-datatype:pretty-print
                      (cons 'cases
                        (cons Type-name
                          (cons Expression clauses*))))
                    (define-datatype:report-error 'cases "Missing variant clauses for ~s."
                      unused-variants)))
                (let* ((head-clause (car clauses*))
                       (tail-clauses (cdr clauses*))
                       (purported-variant (car head-clause)))
                  (if (eq? purported-variant Expression)
                    (begin
                      (define-datatype:pretty-print
                        (cons 'cases
                          (cons Type-name
                            (cons Expression clauses))))
                      (define-datatype:report-error 'cases
                        (string-append
                          "The variant name ~s should not be the same~n"
                          "  as a lexical variable.")
                        Expression))
                    (cond
                      ((and (null? tail-clauses) (eq? purported-variant 'else)))                        
                      ((assq purported-variant variant-table)
                       =>
                       (lambda (p)
                         (let ((fields (cdr p))
                               (purported-fields (cadr head-clause))
                               (new-unused-variants-or-false
                                 (remq-or-false
                                   purported-variant
                                   unused-variants)))
                           (if (not (=
                                      (length fields)
                                      (length purported-fields)))
                             (begin
                               (define-datatype:pretty-print
                                 (cons 'cases
                                   (cons Type-name
                                     (cons Expression clauses))))
                               (define-datatype:report-error 'cases "Bad fields in ~s." head-clause)))
                           (if (not new-unused-variants-or-false)
                             (begin
                               (define-datatype:pretty-print
                                 (cons 'cases
                                   (cons Type-name
                                     (cons Expression clauses))))
                               (define-datatype:report-error 'cases "Duplicate variant clause: ~s."
                                 head-clause)))
                           (f tail-clauses new-unused-variants-or-false))))
                      (else
                        (define-datatype:pretty-print
                          (cons 'cases
                            (cons Type-name
                              (cons Expression clauses))))
                        (define-datatype:report-error 'cases
                          "Bad clause: ~s."
                          head-clause)))))))))))))

(define-syntax isa
  (syntax-rules ()
    ((_)
     (define-datatype:report-error 'isa "isa expects 1 argument, not 0."))
    ((_ type-name)
     (if (symbol? 'type-name)
       (lambda args
         (if (null? args)
           (define-datatype:report-error 'isa "(isa ~s) expects 1 argument, not 0." 'type-name)
           (if (null? (cdr args))
             (let ((variant (car args)))
               (let ((type-info type-name)) 
                 (if (and (pair? type-info) (list? (car type-info)))
                   (and (pair? variant)
                     (memq (car variant) (car type-info)) #t)
                   (define-datatype:report-error 'isa
                     (string-append
                       "(isa ~s) did not get a data type bound to an~n"
                       "  appropriate structure: ~s.~n"
                       "  This tends to happen when the type name is~n"
                       "  bound to a lexical variable.")
                     'type-name type-info))))
             (define-datatype:report-error 'isa
               (string-append
                 "(isa ~s) expects 1 argument, not ~s.~n"
                 "  With argument list = ~s.")
               'type-name (length args) args))))
       (define-datatype:report-error 'isa "Type name is not a symbol: ~s." 'type-name)))
    ((_  type-name other ...)
     (define-datatype:report-error 'isa "(isa ~s) expects 1 argument, not ~s with ~s."
       'type-name (add1 (length '(other ...)))
       (cons 'isa '(type-name other ...))))))

(define-syntax define-datatype
  (syntax-rules ()
    ((_ Type-name)
     (define-datatype:report-error 'define-datatype
       (string-append
         "~n  There are no variants: ~n  ~s.")
       '(define-datatype Type-name)))
    ((_ Type-name Type-name?
       (Variant-name (Field-name Pred?) ...)
       ...)
     (begin
       (define ignored
               (define-datatype:datatype-checker&registry-updater
               'Type-name 
               '((Variant-name (Field-name Pred?) ...)
                 ...)))
       (define Type-name
         (cons '(Variant-name ...)
           '((Variant-name Field-name ...) ...)))
       (define Type-name?
         (if (symbol? 'Type-name)
           (lambda args
             (if (null? args)
               (define-datatype:report-error 'Type-name? "expects 1 argument, not 0.")
               (if (null? (cdr args))
                 (let ((variant (car args)))
                   (let ((type-info Type-name)) 
                     (if (and (pair? type-info) (list? (car type-info)))
                       (and (pair? variant)
                         (memq (car variant) (car type-info)) #t)
                       (define-datatype:report-error 'Type-name?
                         (string-append
                           "did not get a data type bound to an~n"
                           "  appropriate structure: ~s.~n"
                           "  This tends to happen when the type name is~n"
                           "  bound to a lexical variable.")
                         'type-name type-info))))
                 (define-datatype:report-error 'Type-name?
                   (string-append
                     "expects 1 argument, not ~s.~n"
                     "  With argument list = ~s.")
                    (length args) args))))
           (define-datatype:report-error 'Type-name "Type name is not a symbol: ~s." 'type-name)))
       (define Variant-name
         (let ((expected-length (length '(Field-name ...)))
               (field-names '(Field-name ...))
               (pred-names '(Pred? ...))
               (preds (list (lambda (x) (Pred? x)) ...)))
           (lambda args
             (if (not (= (length args) expected-length))
               (define-datatype:report-error 'Variant-name
                 (string-append
                   "Expected ~s arguments but got ~s arguments."
                   "~n  Fields are: ~s ~n  Args are: ~s.")
                 expected-length (length args) '(Field-name ...) args))
             (for-each
               (lambda (a f p pname)
                 (if (not (p a))
                   (define-datatype:report-error 'Variant-name "~n Bad ~a field (~s ~s) => #f."
                     f pname a)))
               args
               field-names
               preds
               pred-names)
             (cons 'Variant-name args))))
       ...))))
 
(define-syntax cases
  (syntax-rules ()
    ((_ Type-name Expression . Clauses)
     (let ((type-predicate? (isa Type-name)))
       (define-datatype:case-checker
         Type-name
         'Type-name
         'Expression
         'Clauses)
       (let ((x Expression))
         (if (type-predicate? x)
           (define-datatype:case-helper x . Clauses)
           (begin
             (define-datatype:pretty-print
               (cons 'cases
                 (cons 'Type-name
                   (cons 'Expression 'Clauses))))
             (define-datatype:report-error 'cases
               "~n  Not a ~a variant: ~s." 'Type-name x))))))))

(define-syntax define-datatype:case-helper
  (syntax-rules (else)
    ((_ Variant (else Body0 Body1 ...))
     (begin Body0 Body1 ...))
    ((_ Variant (Purported-variant-name (Purported-field-name ...)
                  Body0 Body1 ...))
     (apply (lambda (Purported-field-name ...) Body0 Body1 ...)
       (cdr Variant)))
    ((_ Variant (Purported-variant-name (Purported-field-name ...)
                  Body0 Body1 ...)
       Clause ...)
     (if (eq? (car Variant) 'Purported-variant-name)
         (apply (lambda (Purported-field-name ...) Body0 Body1 ...)
           (cdr Variant))
         (define-datatype:case-helper Variant Clause ...)))))

(define always?
  (lambda (x) #t))

(define list-of
  (lambda (pred . l)
    (let ((all-preds (cons pred l)))
      (lambda (obj)
        (let loop ((obj obj) (preds '()))
          (or 
            (and (null? obj) (null? preds))
            (if (null? preds)
                (loop obj all-preds)
                (and (pair? obj)
                     ((car preds) (car obj))
                     (loop (cdr obj) (cdr preds))))))))))


(define-datatype btree btree?
  (empty-btree)
  (btree-node (left btree?) (key integer?) (right btree?)))

(define sort-intlist
  (letrec ((flatten-btree
             (lambda (bt acc)
               (cases btree bt
                 (empty-btree () acc)
                 (btree-node (left key right)
                   (flatten-btree left
                     (cons key
                       (flatten-btree right acc)))))))
           (insert-list
             (lambda (ls bt)
               (if (null? ls) bt
                   (insert-list (cdr ls) (insert (car ls) bt)))))
           (insert
             (lambda (n bt)
               (cases btree bt
                 (empty-btree ()
                   (btree-node (empty-btree) n (empty-btree)))
                 (btree-node (left key right)
                   (cond
                     ((equal? n key) bt)
                     ((< n key)
                      (btree-node (insert n left) key right))
                     (else
                       (btree-node left key (insert n right)))))))))
    (lambda (ls)
      (flatten-btree (insert-list ls (empty-btree)) '()))))

(define define-datatype:test0
  '(sort-intlist '(8 6 7 5 3 0 9)))

(define-datatype lyst lyst?
  (nil)
  (pair
    (head always?)
    (tail lyst?)))

(define list->lyst
  (lambda (ls)
    (if (null? ls)
        (nil)
        (pair (car ls) (list->lyst (cdr ls))))))

(define lyst->list                      ; this tests hygiene
  (lambda (pr)
    (cases lyst pr
      (nil () '())
      (pair (head tail)
        (cons head (lyst->list tail))))))

(define define-datatype:test1
  '(lyst->list (list->lyst '(this is a weird form of identity))))

(define lyst-nil?                       ; this tests else-ability
  (lambda (pr)
    (cases lyst pr
      (nil () #t)
      (else #f))))

(define define-datatype:test2
  '(list (lyst-nil? (nil)) (lyst-nil? (pair 3 (nil)))))

(define define-datatype:test3
  '(begin
     (define-datatype alist alist?
       (anil)
       (apair (head always?) (tail blist?)))
     (define-datatype blist blist?
       (bnil)
       (bpair (head always?) (tail alist?)))
     (apair 5 (bpair 4 (anil)))))

(define define-datatype:test4
  '(begin
     (define-datatype fff fff?
       (wu)
       (bu (fff fff?)))
     (let ((fff 3))
       (fff? (bu (wu))))))


(define define-datatype:err0            ; wrong # args to a constructor
  '(pair))

(define define-datatype:err1            ; wrong type args to a constructor
  '(pair 3 4))

(define define-datatype:err2            ; unlisted variant in cases
  '(cases lyst (nil)
     (nil () 3)))

(define define-datatype:err3            ; wrong type argument to case
  '(cases lyst 5
     (pair (x y) 3)
     (nil () 8)))

(define define-datatype:err4            ; wrong # fields in cases
  '(cases lyst (nil)
     (pair (y z) 4)
     (nil (x) 3)
     (else 5)))

(define define-datatype:err5            ; misspelled variant in cases
  '(cases lyst (nil)
     (ppair (y z) 4)
     (nil () 8)
     (else 5)))

(define define-datatype:err10           ; non-symbol used for variant name
  '(define-datatype x x?
     ((r) (a b))))

(define define-datatype:err11           ; duplicate variant names
  '(define-datatype x x?
     (r (zoo goo?))
     (r (foo goo?))
     (s (joo goo?))))

(define define-datatype:err14           ; only type name
  '(define-datatype a a?))

(define define-datatype:err18           ; duplicate variant clauses
  '(cases lyst (nil)
     (nil () 3)
     (nil () 4)))

(define define-datatype:err19           ; repeated variant name.
  '(begin
     (define-datatype www www?
       (foo (man www?)))
     (define-datatype zzz zzz?
       (foo (harry zzz?)))))

(define define-datatype:err20           ; isa's symbol arg is not a type name
  '(begin
     (define-datatype uu uu?
       (goo (man number?)))
     (define-datatype:pretty-print (uu? (goo 5)))
     (uuu? (goo 6))))

(define define-datatype:err21           ; Too many args to uuuu?
  '(begin
     (define-datatype uuuu uuuu?
       (gu)
       (zu (foo uuuu?)))
     (uuuu? (zu (zu (gu))) 5)))

(define define-datatype:err22           ; Too few args to isa
  '(begin
     (define-datatype uuuu uuuu?
       (gu)
       (zu (foo uuuu?)))
     ( (zu (zu (gu)))?)))

(define define-datatype:err23           ; Too many args to isa
  '(begin
     (define-datatype uuuu uuuu?
       (gu)
       (zu (foo uuuu?)))
     (uuuu? (zu (zu (gu))))))

(define define-datatype:err24           ; type name cannot be chosen
  '(begin                               ; from existing variant name
     (define-datatype uuuu uuuu?
       (gu)
       (zu (foo uuuu?)))
     (define-datatype gu gu?
       (hood))
     (uuuu? (zu (zu (gu))))))

(define define-datatype:err25           ; type name and constructor name
  '(begin                               ; cannot be the same.
     (define-datatype uuuu uuuu?
       (gu)
       (uuuu (foo uuuu?)))
     (uuuu? (zu (zu (gu))))))

(define define-datatype:err26           ; variantr name cannot be chosen
  '(begin                               ; from existing type name
     (define-datatype uuuu uuuu?
       (gu)
       (uuuu^ (foo uuuu?)))
     (define-datatype gru gru?
       (uuuu))
     (uuuu? (zu (zu (gu))))))



;; wdc: what is this 5 ?
(define define-datatype:err27           ; isa's arg is not a symbol.
  '(begin                               
     (define-datatype uuuu uuuu?
       (gu)
       (uuuu^ (foo uuuu?)))
     (5 (zu (zu (gu))))))



(define define-datatype:err28           ; 1st & 2nd arg of cases should not
  '(begin                               ; be the same.
     (define-datatype uuuu** uuuu**?
       (gud)
       (uuuu^^ (foo uuuu**?)))
     (let ((uuuu** (uuuu^^ (uuuu^^ (gud)))))
       (cases uuuu** uuuu**
         (gud () "Hello")
         (uuuu^^ (foo) "Goodbye")))))

(define define-datatype:err29           ; 2nd arg of cases should not
  '(begin                               ; be the same as any variant name.
     (define-datatype uuuu** uuuu**?
       (gud)
       (uuuu^^ (foo uuuu**?)))
     (let ((uuuu^^ (uuuu^^ (uuuu^^ (gud)))))
       (cases uuuu** uuuu^^
         (gud () "Hello")
         (uuuu^^ (foo) "Goodbye")))))

(define do-all-tests
  (let ((tests (list
                 define-datatype:test0
                 define-datatype:test1
                 define-datatype:test2
                 define-datatype:test3
                 define-datatype:test4  
                 define-datatype:err0
                 define-datatype:err1
                 define-datatype:err2
                 define-datatype:err3
                 define-datatype:err4
                 define-datatype:err5
                 define-datatype:err10
                 define-datatype:err11 
                 define-datatype:err14 
                 define-datatype:err18
                 define-datatype:err19
                 define-datatype:err21
                 define-datatype:err23 
                 define-datatype:err24
                 define-datatype:err25
                 define-datatype:err26
                 define-datatype:err28
                 define-datatype:err29))) 
    (lambda (chezer)
      (for-each chezer tests))))

(define define-datatype:tester
  (lambda (example)
    (display "------------------------------")
    (newline)
    (sllgen:pretty-print example)
    (display "-->")
    (newline)
    (call-with-current-continuation
     (lambda (k)
       (let ((alpha (lambda () (k #f))))
         (let ((swap (lambda ()
                     (let ((temp eopl:error-stop))
                       (set! eopl:error-stop alpha)
                       (set! alpha temp)))))
           (dynamic-wind
             swap
             (lambda () 
               (write (eval example (interaction-environment)))
               (newline)
               #t)
             swap)))))))

(define define-datatype:test-all
  (lambda ()
    (do-all-tests define-datatype:tester)
    (define-datatype:reset-registries)))


